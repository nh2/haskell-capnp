import Capnp.Addressbook.Pure

import Data.Capnp (defaultLimit, getValue)

main = do
    value <- getValue defaultLimit
    print (value :: AddressBook)
