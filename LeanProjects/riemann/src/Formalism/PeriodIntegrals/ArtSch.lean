import Mathlib

namespace PI.ArtSch

open scoped NNReal

noncomputable section

section
variable (l : ℕ) [Fact l.Prime]

theorem OC_l_not_unit : ¬ IsUnit ((l : ℕ) : PadicComplexInt l) := by
  have key : Valued.v ((l : ℕ) : ℂ_[l]) = ‖((l : ℕ) : ℚ_[l])‖₊ := by
    have e1 : ((l : ℕ) : ℂ_[l]) = (((l : ℕ) : PadicAlgCl l) : ℂ_[l]) := by
      first
        | exact (map_natCast (UniformSpace.Completion.coeRingHom : PadicAlgCl l →+* ℂ_[l]) l).symm
        | norm_cast
        | simp
    rw [e1, Valued.valuedCompletion_apply, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l))]
    apply NNReal.eq
    exact PadicAlgCl.norm_extends l _
  rw [(PadicComplexInt.integers l).isUnit_iff_valuation_eq_one, map_natCast, key]
  intro h
  have h2 : ‖((l : ℕ) : ℚ_[l])‖ = 1 := by
    have h3 := congrArg NNReal.toReal h
    simpa using h3
  exact absurd h2 (ne_of_lt Padic.norm_p_lt_one)

instance factOC : Fact (¬ IsUnit ((l : ℕ) : PadicComplexInt l)) := ⟨OC_l_not_unit l⟩

abbrev OC : Type := ↥(PadicComplexInt l)

abbrev OCb : Type := PreTilt (OC l) l

instance domOCb : IsDomain (OCb l) :=
  PreTilt.isDomain (PadicComplex l) (PadicComplex.valued l).v (OC l) (PadicComplexInt.integers l) l

abbrev Cb : Type := FractionRing (OCb l)

instance charCb : CharP (Cb l) l := charP_of_injective_algebraMap' (OCb l) l

abbrev WCb : Type := WittVector l (Cb l)

abbrev valb : Valuation (OCb l) ℝ≥0 :=
  PreTilt.val (PadicComplex l) (PadicComplex.valued l).v (OC l) (PadicComplexInt.integers l) l

end

def Main : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (x : WCb l), ∃ y : WCb l, WittVector.map (frobenius (Cb l) l) y - y = x

def WittLift : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] [CharP k p], (∀ a : k, ∃ y : k, y ^ p - y = a) →
    ∀ x : WittVector p k, ∃ y : WittVector p k, WittVector.map (frobenius k p) y - y = x

def TiltAS : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (a : Cb l), ∃ y : Cb l, y ^ l - y = a

def RootModP : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c b : ModP (OC l) l), ∃ z : ModP (OC l) l, z ^ l - c * z - b = 0

def TiltDiv : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (x y : OCb l), valb l x ≤ valb l y → y ∣ x

def TiltSmall : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : OCb l), valb l e < 1 → ∃ w : OCb l, w ^ l - w = e

def TiltGlue : Prop := RootModP → TiltDiv → TiltSmall → TiltAS

theorem main_of (hW : WittLift) (hT : TiltAS) : Main := by
  intro l _ x
  exact hW l (Cb l) (hT l) x

end

end PI.ArtSch
