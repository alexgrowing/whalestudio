import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometry
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCompletionMapsDualLattices
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDefiniteSelfDualOfBaseFramePosDef
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.GramFrame

theorem hform_add_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (x u v : n → A) : Formalism.UG.hform τ J x (u + v) = Formalism.UG.hform τ J x u + Formalism.UG.hform τ J x v := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (a : A) (x y : n → A) : Formalism.UG.hform τ J x (a • y) = a * Formalism.UG.hform τ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_zero_right {A : Type} [CommRing A] {n : Type} [Fintype n] (τ : A →+* A)
    (J : Matrix n n A) (x : n → A) : Formalism.UG.hform τ J x 0 = 0 := by
  simp [Formalism.UG.hform]

variable {D : D7}

theorem sigR_inclE (x : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) x) =
      Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (D.sp.cm.sig x) := by
  simp [Formalism.UG.sigR, Formalism.UG.inclE]

theorem inclE_int (b : 𝓞 D.host.E) :
    Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (algebraMap (𝓞 D.host.E) D.host.E b) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨_, b, rfl⟩, rfl⟩)

theorem hform_inclE {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
      (J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)))
      (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (x i))
      (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (y i)) =
    Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) J x y) := by
  simp only [Formalism.UG.hform, map_sum, map_mul, sigR_inclE, Matrix.map_apply]
  rfl

theorem pair_hatL {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (h : ∀ x ∈ Λ, ∀ y ∈ Λ, Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) J x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (x y : Fin n → Formalism.IndefR.Lev.EAf D) (hx : x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    Formalism.UG.hform (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
      (J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) x y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x0, hx0, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y0, hy0, rfl⟩ := hy
      rw [hform_inclE]
      obtain ⟨b, hb⟩ := h x0 hx0 y0 hy0
      rw [← hb]
      exact inclE_int b
    | zero => rw [hform_zero_right]; exact zero_mem _
    | add a b _ _ ha hb => rw [hform_add_right]; exact add_mem ha hb
    | smul s a _ ha => rw [Subring.smul_def, hform_smul_right]; exact mul_mem s.2 ha
  | zero => rw [Formalism.UG.P.csDual_hform_zero_left]; exact zero_mem _
  | add a b _ _ ha hb => rw [Formalism.UG.P.csDual_hform_add_left]; exact add_mem ha hb
  | smul s a _ ha =>
    rw [Subring.smul_def, Formalism.UG.P.csDual_hform_smul_left]
    exact mul_mem (GlobalTheory.LevSplit.sigR_int s.2) ha

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prV_hform' {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    Formalism.UG.prV (E := E) v (Formalism.UG.hform (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F))
      (J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) x y) =
    Formalism.UG.hform (Formalism.UG.sigR σ (v.adicCompletion F))
      (J.map (Formalism.UG.inclE (F := F) (v.adicCompletion F)))
      (fun i => Formalism.UG.prV (E := E) v (x i)) (fun i => Formalism.UG.prV (E := E) v (y i)) := by
  have hs : ∀ z, Formalism.UG.prV (E := E) v (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) z) =
      Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.prV (E := E) v z) :=
    fun z => RingHom.congr_fun (Formalism.UG.P.afsplit_prV_comp_sigR σ v) z
  simp only [Formalism.UG.hform, map_sum, map_mul, hs, Matrix.map_apply]
  rfl

theorem inv_int {n : ℕ} (σ : E →ₐ[F] E)
    (hσ : ∀ s ∈ Formalism.L2.Herm.intAf F E, Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) s ∈ Formalism.L2.Herm.intAf F E)
    (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hlat : Submodule.IsLattice E Λ) (hfr : Formalism.L2.DIV.IsFrame β Λ)
    (hd : Formalism.L2.Forms.dualL (σ : E →+* E) J Λ ≤ Λ)
    (G' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hG' : Formalism.UG.cT (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) β.val *
      J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) * β.val * G' = 1) :
    ∀ i j, G' i j ∈ Formalism.L2.Herm.intAf F E := by
  intro i j
  have key : ∀ x ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      Formalism.UG.hform (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F))
        (J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) x
        (β.val *ᵥ (G' *ᵥ Pi.single j 1)) ∈ Formalism.L2.Herm.intAf F E := by
    intro x hx
    have ha := (hfr x).1 hx
    have e : x = β.val *ᵥ ((β⁻¹).val *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e, GlobalTheory.DualCompletion.hform_mulVec_left]
    have e2 : (Formalism.UG.cT (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) β.val *
        J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) *ᵥ (β.val *ᵥ (G' *ᵥ Pi.single j 1)) =
        Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hG', Matrix.one_mulVec]
    rw [e2]
    refine Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hσ _ (ha k)) ?_
    rw [Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (fun k => Formalism.UG.prV (E := E) v ((β.val *ᵥ (G' *ᵥ Pi.single j 1)) k)) ∈
        Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E)
            (v.adicCompletionIntegers F).toSubring) Λ := by
    intro v
    have hm := (GlobalTheory.DualCompletion.mem_latS_dualL σ J hJ v Λ hlat
      (fun k => Formalism.UG.prV (E := E) v ((β.val *ᵥ (G' *ᵥ Pi.single j 1)) k))).2
    refine Submodule.span_mono (Set.image_mono hd) (hm fun u hu => ?_)
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨x0, hx0, rfl⟩ := hu
      have h3 := key _ (Submodule.subset_span ⟨x0, hx0, rfl⟩)
      have h4 := Formalism.UG.P.afsplit_prV_int (E := E) v _ h3
      rw [prV_hform'] at h4
      exact h4
    | zero => rw [Formalism.UG.P.csDual_hform_zero_left]; exact zero_mem _
    | add a b _ _ ha hb => rw [Formalism.UG.P.csDual_hform_add_left]; exact add_mem ha hb
    | smul s a _ ha =>
      rw [Subring.smul_def, Formalism.UG.P.csDual_hform_smul_left]
      exact mul_mem (Formalism.L2.G.RelativeIndexFlags.sigR_mem v σ s.2) ha
  have hc : β.val *ᵥ (G' *ᵥ Pi.single j 1) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
    Formalism.L2.Geo.Def.PN.latS_of_loc Λ hlat.span_eq_top _ hloc
  have h5 := (hfr _).1 hc i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
    Matrix.mulVec_single_one] at h5
  exact h5

end General

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

theorem gram_entry {A : Type} [CommRing A] {n : ℕ} (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    (Formalism.UG.cT τ B * J * B) i j = Formalism.UG.hform τ J (B *ᵥ Pi.single i 1) (B *ᵥ Pi.single j 1) := by
  rw [GlobalTheory.DualCompletion.hform_col, map_one, one_mul, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

end GlobalTheory.GramFrame
