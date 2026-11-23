import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.QZDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Brauer

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

def IsPairClass (a : (kbarT p K).V) (χ : charGrp (GK p K)) (c : Br p K) : Prop :=
  ∃ (t : GK p K → ℚ) (m : (Fin 2 → GK p K) → ℤ) (z : (kbarT p K).coch.X 2) (hz : (kbarT p K).coch.d 2 z = 0),
    IsLocallyConstant t ∧ (∀ g, (QuotientAddGroup.mk (t g) : QZ) = χ.1 (Additive.ofMul g)) ∧
    (∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) ∧ (∀ g, z.1 g = m g • a) ∧
    c = (kbarT p K).coch.cls 2 z hz

open Classical in

def pairBr (a : Kˣ) (χ : charGrp (GK p K)) : Br p K :=
  if h : ∃ c, IsPairClass p K (ofK p K (Additive.ofMul a)) χ c then h.choose else 0

def pairK (a : Kˣ) (χ : charGrp (GK p K)) : QZ := invBr p K (pairBr p K a χ)

variable {p K L} in

def resChar (h : K ≤ L) : charGrp (GK p K) →+ charGrp (GK p L) where
  toFun χ := ⟨χ.1.comp (MonoidHom.toAdditive (resGK h)),
    (show IsLocallyConstant fun g : GK p K => χ.1 (Additive.ofMul g) from χ.2).comp_continuous
      (resGK_continuous h)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def TrivOn (χ : charGrp (GK p K)) : Prop := ∀ g ∈ subG p K L, χ.1 (Additive.ofMul g) = 0

def IsRecip (a : Kˣ) (g : GK p K) : Prop :=
  ∀ χ : charGrp (GK p K), TrivOn p K L χ → χ.1 (Additive.ofMul g) = pairK p K a χ

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
