import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CardNuGZmod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.HaarIdx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GOfPrime

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm

theorem card_conj {G : Type} [Group G] (H : Subgroup G) (c : G) :
    Nat.card (H.map (MulAut.conj c).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj c).injective

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def LevelReductionImage (p : TypX X) : Prop :=
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ρ₀ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)), Function.Surjective ρ₀ ∧
      (∀ x : K, ρ₀ x = 1 ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ A : Subgroup K, Subtype.val '' (A : Set K) = KppX X hb p ∧ ρ₀.ker ≤ A ∧
        ∃ c, A.map ρ₀ = (nuG (ZMod (gOf p)) D.R.rS D.R.k).map (MulAut.conj c).toMonoidHom

def ParabolicReductionImage (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ρ₀ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)), Function.Surjective ρ₀ ∧
      (∀ x : K, ρ₀ x = 1 ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ B : Subgroup K, Subtype.val '' (B : Set K) = KnatX X u p ∧ ρ₀.ker ≤ B ∧
        ∃ c, B.map ρ₀ = (sG (ZMod (gOf p)) D.R.rS D.R.k).map (MulAut.conj c).toMonoidHom

theorem stImA_of (p : TypX X) (h : LevelReductionImage X hb p) : StImA X hb p := by
  obtain ⟨K₀, hK₀, ρ₀, hρ₀, hker₀, A, hA, hkA, c, hc⟩ := h
  intro K hK ρ hρ hker
  have hKK : K = K₀ := SetLike.coe_injective (hK.trans hK₀.symm)
  subst hKK
  have hkers : ρ.ker = ρ₀.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker, hker₀]
  have hkA' : ρ.ker ≤ A := hkers.le.trans hkA
  refine ⟨A, hA, hkA', ?_⟩
  have hq : ∀ f : ↥K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)),
      Nat.card (A.map f) = Nat.card (↥A ⧸ (f.comp A.subtype).ker) := by
    intro f
    have hr : A.map f = (f.comp A.subtype).range := by
      first
      | rw [MonoidHom.range_comp, Subgroup.range_subtype]
      | rw [MonoidHom.range_comp, Subgroup.subtype_range]
    rw [hr]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.comp A.subtype)).toEquiv.symm
  have hk2 : (ρ.comp A.subtype).ker = (ρ₀.comp A.subtype).ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, hker, hker₀]
  rw [hq ρ, hk2, ← hq ρ₀, hc, card_conj]
  haveI : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  first
  | exact card_nuG (ZMod (gOf p)) D.R.rS D.R.k
  | (rw [card_nuG]; unfold nnC ukC; rfl)
  | (rw [card_nuG]; unfold nnC ukC)

theorem stImB_of (u : D.what₂.Word) (p : TypX X) (h : ParabolicReductionImage X u p) : StImB X u p := by
  obtain ⟨K₀, hK₀, ρ₀, hρ₀, hker₀, A, hA, hkA, c, hc⟩ := h
  intro K hK ρ hρ hker
  have hKK : K = K₀ := SetLike.coe_injective (hK.trans hK₀.symm)
  subst hKK
  have hkers : ρ.ker = ρ₀.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker, hker₀]
  have hkA' : ρ.ker ≤ A := hkers.le.trans hkA
  refine ⟨A, hA, hkA', ?_⟩
  have hq : ∀ f : ↥K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)),
      Nat.card (A.map f) = Nat.card (↥A ⧸ (f.comp A.subtype).ker) := by
    intro f
    have hr : A.map f = (f.comp A.subtype).range := by
      first
      | rw [MonoidHom.range_comp, Subgroup.range_subtype]
      | rw [MonoidHom.range_comp, Subgroup.subtype_range]
    rw [hr]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.comp A.subtype)).toEquiv.symm
  have hk2 : (ρ.comp A.subtype).ker = (ρ₀.comp A.subtype).ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, hker, hker₀]
  rw [hq ρ, hk2, ← hq ρ₀, hc, card_conj]
  haveI : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  first
  | exact card_sG (ZMod (gOf p)) D.R.rS D.R.k
  | (rw [card_sG]; unfold glkC nnC; rfl)
  | (rw [card_sG]; unfold glkC nnC)

end MassDataIdxSteps
