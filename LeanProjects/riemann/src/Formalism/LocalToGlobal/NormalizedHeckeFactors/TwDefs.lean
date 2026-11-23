import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions
open scoped NNReal

namespace Formalism.L2.TwC

section rings

variable (l : ℕ) [Fact l.Prime]

def intOf (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : Subring (PadicAlgCl l) :=
  K.toSubalgebra.toSubring ⊓ (PadicAlgCl.valued l).v.integer

def clC (F : IntermediateField ℚ_[l] (PadicAlgCl l)) : Subring ℂ_[l] :=
  (F.toSubalgebra.toSubring.map (algebraMap (PadicAlgCl l) ℂ_[l])).topologicalClosure ⊓
    (PadicComplexInt l).toSubring

def Kt (K₀ L : Loc.FinExt l) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  K₀.1 ⊔ L.1 ⊔ Loc.MaximalUnramifiedExtension l

def muK (k : ℕ) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] {x | x ^ (l ^ k) = 1}

end rings

section places

theorem placesOver_finite' (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have hp' : ((p : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hI : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hp'
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  show v.asIdeal ∣ Ideal.span {((p : ℕ) : 𝓞 E)}
  rw [Ideal.dvd_span_singleton]
  exact hv

def pDC {R : Ranks} (H : Host R) (l : ℕ) : Finset (HeightOneSpectrum (𝓞 H.E)) :=
  (placesOver_finite' H.E (if l = H.pde then H.pde' else H.pde)
    (by split_ifs <;> first | exact H.pde'_prime.ne_zero | exact H.pde_prime.ne_zero)).toFinset

theorem coe_pDC {R : Ranks} (H : Host R) (l : ℕ) :
    (pDC H l : Set (HeightOneSpectrum (𝓞 H.E))) = placesOver H.E (if l = H.pde then H.pde' else H.pde) := by
  first
    | exact Set.Finite.coe_toFinset _
    | (simp [pDC]; done)

end places

end Formalism.L2.TwC
