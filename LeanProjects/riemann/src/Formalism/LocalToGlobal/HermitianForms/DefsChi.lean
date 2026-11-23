import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Forms

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {gp : Fin 2 → ℕ}

structure CharacterCompatible (G : GLoc F E σ gp) (m : ℕ) : Prop where

  dist : ∀ i v h a b, a < m → b < m → G.chiB i v h a = G.chiB i v h b → a = b

  same : ∀ i v h v' h' a (n : ℤ), a < m → G.chiB i v h a (n : kv F v) = G.chiB i v' h' a (n : kv F v')

  pow : ∀ i, ∃ om : MulChar (ZMod (gp i)) ℂ, orderOf om = gp i - 1 ∧
    ∀ v h a (n : ℤ), a < m → G.chiB i v h a (n : kv F v) = (om ^ (2 * (a + 1))) (n : ZMod (gp i))

end Formalism.L2.Forms

end
