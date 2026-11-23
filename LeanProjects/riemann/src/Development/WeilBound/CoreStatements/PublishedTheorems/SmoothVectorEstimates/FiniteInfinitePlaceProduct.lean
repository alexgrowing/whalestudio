import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdInfMulFinPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousInfIdele
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.GlobalFields.Adele.WeakApproxUnits

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace FiniteInfinitePlaceProduct

open Neutral.B1

variable {L : Type} [Field L] [NumberField L]

theorem loc_eq_one_of_val {ν : HChar L} {v : HeightOneSpectrum (𝓞 L)} (hu : ν.UnrAt v) (hv : ν.val v = 1)
    (x : (v.adicCompletion L)ˣ) : ν.loc v x = 1 := by
  set π := atFin v (unif v) with hπ
  have hπv : Valued.v (π : v.adicCompletion L) = WithZero.exp (-1) := unif_spec v
  have hπ1 : ν.loc v π = 1 := by rw [HChar.val_eq ν hu π (unif_spec v)]; exact hv
  have hx0 : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  set n := WithZero.log (Valued.v (x : v.adicCompletion L))
  have hxv : Valued.v (x : v.adicCompletion L) = WithZero.exp n := (WithZero.exp_log hx0).symm
  have hy : IsUnitAt v (x * π ^ n) := by
    show Valued.v ((x * π ^ n : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1
    rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hπv, hxv,
      ← WithZero.exp_zsmul, ← WithZero.exp_add, smul_eq_mul]
    simp
  have h2 := hu _ hy
  rw [map_mul, map_zpow, hπ1, _root_.one_zpow, mul_one] at h2
  exact h2

theorem inf_eq_prod (ν : HChar L) (k : Lˣ) :
    ν.inf k = ∏ w ∈ (Finset.univ : Finset (InfinitePlace L)), ν.locInf w (atInf w k) := by
  simp only [HChar.inf, HChar.locInf, infDiag, MonoidHom.comp_apply, MonoidHom.finset_prod_apply, map_prod]

set_option maxHeartbeats 400000 in

theorem eq_one (ν : HChar L) (h : ∀ᶠ w in cofinite, ν.val w = 1) : ν = 1 := by
  classical
  have hνc : Continuous (ν : Ideles L →* ℂˣ) := ν.2.1
  have hfin := (GlobalTheory.Mem.UnrAe.finite_ramified ν).union (Filter.eventually_cofinite.mp h)
  set S := hfin.toFinset with hSdef
  have hS : ∀ v ∉ S, ν.UnrAt v ∧ ν.val v = 1 := by
    intro v hv
    simpa [S, not_or] using hv
  have hgood : ∀ v ∉ S, ∀ x, ν.loc v x = 1 := fun v hv x =>
    loc_eq_one_of_val (hS v hv).1 (hS v hv).2 x
  have hprod : ∀ k : Lˣ, ν.inf k * ∏ v ∈ S, ν.locK v k = 1 := by
    intro k
    have h0 : (ν.inf k * ∏ v ∈ S, ν.locK v k) *
        ∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), ν.val v ^ GlobalTheory.Mem.Chr.ordF v k = 1 :=
      GlobalTheory.Mem.Chr.CharModel.productRule (ν : GlobalTheory.Mem.Chr.HChar L) S (fun v hv => (hS v hv).1) k
    have hf : ∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), ν.val v ^ GlobalTheory.Mem.Chr.ordF v k = 1 := by
      apply finprod_eq_one_of_forall_eq_one
      intro v
      rw [finprod_eq_if]
      by_cases hv : v ∈ S
      · rw [if_neg (not_not.mpr hv)]
      · rw [if_pos hv, (hS v hv).2, _root_.one_zpow]
    rw [hf, mul_one] at h0
    exact h0
  have key : ∀ p : ((v : S) → (v.1.adicCompletion L)ˣ) ×
      ((w : (Finset.univ : Finset (InfinitePlace L))) → (w.1.Completion)ˣ),
      (∏ v : S, ν.loc v.1 (p.1 v)) *
        ∏ w : (Finset.univ : Finset (InfinitePlace L)), ν.locInf w.1 (p.2 w) = 1 := by
    have hc : Continuous fun p : ((v : S) → (v.1.adicCompletion L)ˣ) ×
        ((w : (Finset.univ : Finset (InfinitePlace L))) → (w.1.Completion)ˣ) =>
        (∏ v : S, ν.loc v.1 (p.1 v)) *
          ∏ w : (Finset.univ : Finset (InfinitePlace L)), ν.locInf w.1 (p.2 w) := by
      apply Continuous.mul
      · apply continuous_finset_prod
        intro v _
        exact (hνc.comp (GlobalTheory.Mem.Chr.Determ.continuous_localIdele v.1)).comp
          ((continuous_apply v).comp continuous_fst)
      · apply continuous_finset_prod
        intro w _
        exact (hνc.comp (GlobalTheory.InfTypeLocal.continuous_infIdele L w.1)).comp
          ((continuous_apply w).comp continuous_snd)
    have hd := GroundTheory.Global.denseRange_units_prod_pi S (Finset.univ : Finset (InfinitePlace L))
    intro p
    refine hd.induction_on p (isClosed_eq hc continuous_const) (fun k => ?_)
    beta_reduce
    have e1 : (∏ v : S, ν.loc v.1 (Units.map ↑(algebraMap L (v.1.adicCompletion L)) k)) =
        ∏ v ∈ S, ν.locK v k := Finset.prod_coe_sort S (fun v => ν.locK v k)
    have e2 : (∏ w : (Finset.univ : Finset (InfinitePlace L)),
        ν.locInf w.1 (Units.map ↑(algebraMap L w.1.Completion) k)) = ν.inf k := by
      rw [inf_eq_prod]
      exact Finset.prod_coe_sort _ (fun w => ν.locInf w (atInf w k))
    exact (congrArg₂ (· * ·) e1 e2).trans (by rw [mul_comm]; exact hprod k)
  have hlocS : ∀ v ∈ S, ∀ x, ν.loc v x = 1 := by
    intro v hv x
    have h0 := key (Pi.mulSingle ⟨v, hv⟩ x, 1)
    dsimp only at h0
    rw [Fintype.prod_eq_single ⟨v, hv⟩ (fun v' hne => by rw [Pi.mulSingle_eq_of_ne hne, map_one]),
      Pi.mulSingle_eq_same] at h0
    simpa using h0
  have hinf : ∀ w x, ν.locInf w x = 1 := by
    intro w x
    have h0 := key (1, Pi.mulSingle ⟨w, Finset.mem_univ w⟩ x)
    dsimp only at h0
    rw [Fintype.prod_eq_single (⟨w, Finset.mem_univ w⟩ : (Finset.univ : Finset (InfinitePlace L)))
      (fun w' hne => by rw [Pi.mulSingle_eq_of_ne hne, map_one]), Pi.mulSingle_eq_same] at h0
    simpa using h0
  have hall := GlobalTheory.Mem.Chr.Determ.eq_one_of_components (ψ := (ν : Ideles L →* ℂˣ)) hνc
    (fun v k => by
      by_cases hv : v ∈ S
      · exact hlocS v hv _
      · exact hgood v hv _)
    (fun k => by
      have h0 := inf_eq_prod ν k
      rw [Finset.prod_eq_one (fun w _ => hinf w _)] at h0
      exact h0)
  exact Subtype.ext (MonoidHom.ext fun a => by rw [hall a]; rfl)

end FiniteInfinitePlaceProduct

theorem finite_infinite_product_eq_one : HeckeCharacterRigidity := by
  intro E _ _ _ ω ω' h
  have h1 := FiniteInfinitePlaceProduct.eq_one (ω * ω'⁻¹) (h.mono fun w hw => by
    rw [HChar.val_mul, HChar.val_inv, hw, mul_inv_cancel])
  exact mul_inv_eq_one.1 h1

end PositivityTheory.jumpWindows

end
