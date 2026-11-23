import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev Ix (Dw : Datum H) : Type := Option (Σ τ : E →+* ℂ, Fin (Dw.mult τ))

def ex (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Ix Dw → ℕ
  | none => n
  | some x => a (x.1, x.2)

theorem ex_add (Dw : Datum H) (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) :
    ex Dw (a + a') (n + n') = ex Dw a n + ex Dw a' n' := by
  funext i; cases i <;> rfl

def Dom (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop := (∀ τ, Antitone fun i => a (τ, i)) ∧ Even n

variable {l : Level H} (c : Coeff l)

instance : NumberField c.F where
  to_charZero := inferInstance
  to_finiteDimensional := c.fin

def embF (τ : E →+* ℂ) : E →+* c.F := τ.codRestrict c.F (c.conj τ)

def embK (τ : E →+* ℂ) : 𝓞 E →+* c.F := (embF c τ).comp (algebraMap (𝓞 E) E)

theorem embK_coe (τ : E →+* ℂ) (a : 𝓞 E) : ((embK c τ a : c.F) : ℂ) = τ (a : E) := rfl

end Formalism.L2.Pj
