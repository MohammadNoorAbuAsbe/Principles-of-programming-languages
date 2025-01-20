export const MISSING_KEY = '___MISSING_KEY___'
export const MISSING_TABLE_SERVICE = '___MISSING_TABLE_SERVICE___'

export type Table<T> = Readonly<Record<string, Readonly<T>>>

export type TableService<T> = {
    get(key: string): Promise<T>;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
}

// Q 2.1 (a)
export function makeTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>): TableService<T> {
    // optional initialization code
    return {
        get(key: string): Promise<T> {
            
            return sync().then((data) => {
                if(key in data){
                    return Promise.resolve(data[key]);
                }
                else{
                    return Promise.reject(MISSING_KEY);
                }
            }).catch(err => Promise.reject(MISSING_KEY))
        },
        set(key: string, val: T): Promise<void> {
            return sync().then((data) => {
                let temp = {} as Record<string, Readonly<T>>;
                let flag = false;
                Object.keys(data).forEach(element => {
                    if(element === key){
                        flag = true;
                        temp[element]= val;
                    }
                    else{
                        temp[element]= data[element];
                    }
                });
                if(!flag){
                    temp[key]= val;
                }
                return sync(temp).then(res => Promise.resolve())
                
                
            })
        },
        delete(key: string): Promise<void> {
            return sync().then((data) => {
                let temp = {} as Record<string, Readonly<T>>;
                let flag = false;
                Object.keys(data).forEach(element => {
                    if(element != key){
                        temp[element]= data[element];
                    }
                    else{
                        flag = true;
                    }
                }); 
                if(flag){
                    return sync(temp).then(res => Promise.resolve())
                    
                }
                else{
                    return Promise.reject(MISSING_KEY);
                }   
            }).catch(err => Promise.reject(MISSING_KEY))
            
        }
    }
}

// Q 2.1 (b)
export function getAll<T>(store: TableService<T>, keys: string[]): Promise<T[]> {
    const promisedKeys = keys.map(key => store.get(key));
    return Promise.all(promisedKeys);
}


// Q 2.2
export type Reference = { table: string, key: string }

export type TableServiceTable = Table<TableService<object>>

export function isReference<T>(obj: T | Reference): obj is Reference {
    return typeof obj === 'object' && 'table' in obj
}

export async function constructObjectFromTables(tables: TableServiceTable, ref: Reference) {
    async function deref(ref: Reference) {
        let temp = new Map();
        const tab =  tables[ref.table];
        if(tab != null){const k = await tab.get(ref.key);
            for (const [key, value] of Object.entries(k)) {
                isReference(value)? temp.set(key,await deref(value)):temp.set(key,value)
            }
            return Object.fromEntries(temp);
        }
        else{
            return Promise.reject(MISSING_TABLE_SERVICE);
        }
        

    }

    return deref(ref)
}

// Q 2.3

export function lazyProduct<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    return function* () {
        for(const n of g1()){
            for(const m of g2())
            yield [n,m];
        }
    }
}

export function lazyZip<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    return function* () {
        const g = g2();
        for(const n of g1()){
            yield [n,g.next().value];
        }
    }
}

// Q 2.4
export type ReactiveTableService<T> = {
    get(key: string): T;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
    subscribe(observer: (table: Table<T>) => void): void
}

export async function makeReactiveTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>, optimistic: boolean): Promise<ReactiveTableService<T>> {
    // optional initialization code
    const observers:((table: Table<T>) => void)[] = [];
    let _table: Table<T> = await sync()

    const handleMutation = async (newTable: Table<T>) => {
        _table = await sync(newTable);
    }
    return {
        get(key: string): T {
            if (key in _table) {
                return _table[key]
            } else {
                throw MISSING_KEY
            }
        },
        set(key: string, val: T): Promise<void> {
            let temp = {} as Record<string, Readonly<T>>;
            let flag = false;
            Object.keys(_table).forEach(element => {
                if(element === key){
                    flag = true;
                    temp[element]= val;
                }
                else{
                    temp[element]= _table[element];
                }
            });
            if(!flag){
                temp[key]= val;
            }
            if(optimistic){
                observers.forEach(observer => {
                    observer(temp);
                })
                return handleMutation(temp).catch(err => {
                    observers.forEach(observer => {
                        observer(_table);
                    })
                    return Promise.reject(err);
                }
                    
                    )
            }
            else{
                return handleMutation(temp).then(() => observers.forEach(observer => {
                    observer(temp);
                }));
            }
                
        },
        delete(key: string): Promise<void> {
            let temp = {} as Record<string, Readonly<T>>;
            let flag = false;
            Object.keys(_table).forEach(element => {
                if(element != key){
                    temp[element]= _table[element];
                }
                else{
                    flag = true;
                }
            }); 
            if(flag){
                if(optimistic){
                    observers.forEach(observer => {
                        observer(temp);
                    })
                    return handleMutation(temp).catch(err => {
                        observers.forEach(observer => {
                            observer(_table);
                        })
                        return Promise.reject(err);
                    }
                        
                        )
                }
                else{
                    return handleMutation(temp).then(() => observers.forEach(observer => {
                        observer(temp);
                    }));
                }
                
            }
            else{
                return Promise.reject(MISSING_KEY);
            } 
                
        },

        subscribe(observer: (table: Table<T>) => void): void {
            observers.push(observer);
        }
    }
}