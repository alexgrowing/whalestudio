import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.LiftHilbertModel

open Formalism.IndefR.Mult GlobalTheory.HilbertLevels

theorem hasPeterssonInner_smul_measure' {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) {T T' : MMap M} {c : ℂ} {a : ℝ} (ha : 0 ≤ a) (h : IsMultIP M μ 𝓕 T T' c) :
    IsMultIP M (ENNReal.ofReal a • μ) 𝓕 T T' ((a : ℂ) * c) := by
  intro v v'
  obtain ⟨h1, h2⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn at h1 ⊢
    rw [Measure.restrict_smul]
    exact h1.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, h2, ENNReal.toReal_ofReal ha, Complex.real_smul, mul_assoc]

theorem ipM_smul_measure {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) {T T' : MMap M} {a : ℝ} (ha : 0 ≤ a) (hne : ∀ τ, ∃ w : M.sm τ, w ≠ 0)
    (h : ∃ c, IsMultIP M μ 𝓕 T T' c) :
    ipM M (ENNReal.ofReal a • μ) 𝓕 T T' = (a : ℂ) * ipM M μ 𝓕 T T' := by
  choose w hw using hne
  have hv0 : ∏ τ, ⟪(w τ : M.H τ), (w τ : M.H τ)⟫_ℂ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 fun h => hw τ (Submodule.coe_eq_zero.1 h)
  have h1 := hasPeterssonInner_smul_measure' M μ 𝓕 ha (ipM_spec M μ 𝓕 T T' h)
  exact hasPeterssonInner_unique M _ 𝓕 T T' w hv0 (ipM_spec M _ 𝓕 T T' ⟨_, h1⟩) h1

theorem mult_mono {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : Formalism.IndefR.Datum.InfFam D) (M : DSModel V S) {J J' : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : Mult θ M J χ ≤ Mult θ M J' χ' :=
  Submodule.span_mono fun _ hX =>
    ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem wat_le_wall (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (P : LevelP R.Pg D.R.r ℂ) : R.Wat i σ P ≤ R.Wall i σ :=
  le_trans inf_le_left (mult_mono R.θ (R.MW i σ) (levS_mono fun x hx =>
    lev_datY_triv D.R.r D.R.t 0 (r_le_rank_Wc i) R.Pg ∅ P (fun _ _ => 1) (fun _ => 1) x hx))

theorem model_facts (hI : Inputs D) (hM : R.IsModels) (y : Hd R) (i : Fin D.R.m) :
    Function.Injective (R.HW i (sg0 D A)).e ∧
      R.Wat i (sg0 D A) (R.levL F false (sg0 D A)) ≤ LinearMap.range (R.HW i (sg0 D A)).e ∧
      ∀ u v, (y.L F).ipWc i (PiTensorProduct.lift ((R.HW i (sg0 D A)).e u)) (PiTensorProduct.lift ((R.HW i (sg0 D A)).e v)) =
        (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  obtain ⟨h1, h2, h3⟩ := hM.HW i (sg0 D A)
  refine ⟨h1, h2 ▸ wat_le_wall R i _ _, fun u v => ?_⟩
  have h0 := hM.νW i
  have hu : (R.HW i (sg0 D A)).e u ∈ R.Wall i (sg0 D A) := h2 ▸ LinearMap.mem_range_self _ u
  have hv : (R.HW i (sg0 D A)).e v ∈ R.Wall i (sg0 D A) := h2 ▸ LinearMap.mem_range_self _ v
  have hs := ipM_smul_measure (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) (inv_pos.2 (nP_pos F false)).le
    (hI.sm _ _ _) (hI.schur _ (D.sp.W_sig _) _ R.θ _ _ _ _ _ hM.inf h0.1.1 h0.2 _ hu _ hv)
  have e : (y.L F).ipWc i (PiTensorProduct.lift ((R.HW i (sg0 D A)).e u)) (PiTensorProduct.lift ((R.HW i (sg0 D A)).e v)) =
      (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) *
        ipMT (R.MW i (sg0 D A)) (ENNReal.ofReal (RealDat.nP F false)⁻¹ • R.νW i) (R.fdW i)
          (PiTensorProduct.lift ((R.HW i (sg0 D A)).e u)) (PiTensorProduct.lift ((R.HW i (sg0 D A)).e v)) := rfl
  rw [e, h3, ipMT, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hs, ipAt, mul_left_comm]

end

theorem hilbert_model_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m), Function.Injective (R.toRealDat.HW i (sg0 D A3.A)).e ∧ R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) ≤ LinearMap.range (R.toRealDat.HW i (sg0 D A3.A)).e ∧ ∀ u v, (y.L F.lv2).ipWc i (PiTensorProduct.lift ((R.toRealDat.HW i (sg0 D A3.A)).e u)) (PiTensorProduct.lift ((R.toRealDat.HW i (sg0 D A3.A)).e v)) = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ hI hP _ y i
  exact model_facts R.toRealDat F.lv2 hI hP.char.base.models y i

end GlobalTheory.LiftHilbertModel

end
