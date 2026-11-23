import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenLevelGroupFiniteAdelic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.TransSum

def conjMeet {Γ : Type*} [Group Γ] (K : Subgroup Γ) (γ : Γ) : Subgroup Γ :=
  K ⊓ K.comap (MulAut.conj γ⁻¹).toMonoidHom

theorem mem_conjMeet {Γ : Type*} [Group Γ] {K : Subgroup Γ} {γ x : Γ} :
    x ∈ conjMeet K γ ↔ x ∈ K ∧ γ⁻¹ * x * γ ∈ K := by
  simp [conjMeet, Subgroup.mem_inf, Subgroup.mem_comap, MulAut.conj_apply]

theorem exists_sum_inv {Γ : Type*} [Group Γ] (K : Subgroup Γ) (γ : Γ)
    [hf : ((conjMeet K γ).subgroupOf K).FiniteIndex] :
    ∃ C : Finset Γ, C.Nonempty ∧ (∀ δ ∈ C, ∃ k ∈ K, δ = k * γ) ∧
      ∀ F : Γ → ℂ, (∀ k ∈ K, ∀ g, F (g * k) = F g) → ∀ k ∈ K, ∀ g,
        ∑ δ ∈ C, F (g * k * δ) = ∑ δ ∈ C, F (g * δ) := by
  classical
  set H := (conjMeet K γ).subgroupOf K
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let r : K ⧸ H → Γ := fun q => ((Quotient.out q : K) : Γ) * γ
  have hr : Function.Injective r := by
    intro q₁ q₂ h
    have h' : (Quotient.out q₁ : K) = Quotient.out q₂ := Subtype.ext (mul_right_cancel h)
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂, h']
  refine ⟨Finset.univ.image r, ?_, ?_, ?_⟩
  · exact Finset.image_nonempty.2 ⟨(QuotientGroup.mk 1 : K ⧸ H), Finset.mem_univ _⟩
  · intro δ hδ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hδ
    exact ⟨_, (Quotient.out q).2, rfl⟩
  · intro F hF k hk g
    rw [Finset.sum_image (fun a _ b _ h => hr h), Finset.sum_image (fun a _ b _ h => hr h)]
    let kk : K := ⟨k, hk⟩

    have key : ∀ q : K ⧸ H, F (g * k * r q) = F (g * r (kk • q)) := by
      intro q
      have hq : (QuotientGroup.mk (Quotient.out (kk • q)) : K ⧸ H) = QuotientGroup.mk (kk * Quotient.out q) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have hm := QuotientGroup.eq.1 hq
      rw [Subgroup.mem_subgroupOf, mem_conjMeet] at hm
      have e : g * k * r q = g * r (kk • q) * (γ⁻¹ * ((((Quotient.out (kk • q))⁻¹ * (kk * Quotient.out q) : K) : Γ)) * γ) := by
        simp only [r, Subgroup.coe_mul, Subgroup.coe_inv, kk]
        group
      rw [e, hF _ hm.2]

    rw [Finset.sum_congr rfl fun q _ => key q]
    exact Fintype.sum_equiv (MulAction.toPerm kk) _ _ (fun q => rfl)

end GlobalTheory.TransSum

namespace GlobalTheory.TransSum

theorem heckeOn_doubleCoset_mem_wall : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}, LevProd R i → ∀ (γ : GA D (Wc D i)), γ ∈ GfC (Wc D i) → ∃ C : Finset (GA D (Wc D i)), C.Nonempty ∧ (∀ δ ∈ C, ∃ k ∈ levW R i, δ = k * γ) ∧ ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hP γ hγ
  have topgrp := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (Wc D i).gram
  haveI : CompactSpace (levW R i) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.ParahoricCompact.isCompact_levG _ _ _)
  have hU := GlobalTheory.LevelOpen.isOpen_levG (Wc D i) (R.βW i) (R.datWp i R.triv)
  have hopen : IsOpen (((conjMeet (levW R i) γ).subgroupOf (levW R i) : Subgroup (levW R i)) : Set (levW R i)) := by
    let φ : levW R i → GfC (Wc D i) := fun x =>
      ⟨γ⁻¹ * (x : GA D (Wc D i)) * γ, mul_mem (mul_mem (inv_mem hγ) (hP.1 x.2)) hγ⟩
    have hφ : Continuous φ := by
      refine Continuous.subtype_mk ?_ _
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const
    have e : (((conjMeet (levW R i) γ).subgroupOf (levW R i) : Subgroup (levW R i)) : Set (levW R i)) =
        φ ⁻¹' {g : GfC (Wc D i) | (g : GA D (Wc D i)) ∈ levG _ (R.βW i) (R.datWp i R.triv)} := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_conjMeet, Set.mem_preimage, Set.mem_setOf_eq, φ]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [e]
    exact hU.preimage hφ
  haveI : Finite (levW R i ⧸ (conjMeet (levW R i) γ).subgroupOf (levW R i)) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  haveI : ((conjMeet (levW R i) γ).subgroupOf (levW R i)).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨C, hne, hC, hsum⟩ := exists_sum_inv (levW R i) γ
  refine ⟨C, hne, hC, fun Tm hT => ?_⟩
  have hCf : ∀ a ∈ C, a ∈ GfC (Wc D i) := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := hC a ha
    exact mul_mem (hP.1 hk) hγ
  unfold RealDat.Wall at hT ⊢
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  refine GlobalTheory.HeckeParts.isMultMap_heckeOn hT hCf fun v k hk g => ?_
  have h1 : levChi _ (R.βW i) (R.datWp i R.triv) k = 1 := hP.2.1 k hk
  rw [h1, one_mul, heckeLin_apply, heckeLin_apply]
  exact hsum (Tm v) (fun k' hk' g' => by rw [hT.lev v k' hk' g', hP.2.1 k' hk', one_mul]) k hk g

end GlobalTheory.TransSum

end
