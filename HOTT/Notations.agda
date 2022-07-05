-- This file doesn't compile.  It's just here to record all the
-- syntaxes and their fixities and relative precedence, so we can try
-- to keep them consistent.  Any changes should be made simultaneously
-- here and in the actual code files.

infix 60 _₀ _₁ -- Id
infix 60 _₀₀ _₀₁ _₀₂ _₁₀ _₁₁ _₁₂ _₂₀ _₂₁ -- Square/Base

infixl 50 _↑ _↓ _⇑ -- Copy/Base *
infixl 50 _∷_ -- Telescope

infixl 40 _⊙_ -- Arrow/Base
infixl 40 _∙_ -- Pi/Base
infix 40 _⊘_ _⊘ᵉ_ -- Telescope
infixr 40 _⊚_ _⊚ᵉ_ -- Telescope

infixr 35 _•ᶠ_ _•ʰ_ -- Rewrite
infixr 35 _•_       -- Groupoids

infix 30 _＝_ -- Refl
infixr 30 _⇒_ Π -- Pi/Base
infixl 30 _▸_ _▹_ -- Telescope
infixr 30 _,_ Σ -- Sigma/Base
infixr 30 _×_ -- Prod/Base, Sigma/Base
infixr 30 _⇛_ -- Arrow/Base

infix 20 Λ⇨ Λ⇨ᵉ -- Telescope
infixr 20 ƛ⇛ -- Arrow/Base
infixr 20 ƛ⇒ -- Pi/Base

infix 10 _≡_ _≡ᵉ_ -- Rewrite
