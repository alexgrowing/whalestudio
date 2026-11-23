import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesUnitOfReadInjScaleRootConjRootCoordRange
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarMulSelfOfPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjFormsRescale
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Formalism.LocalToGlobal.Columns.CoefModAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientSpaceEndomorphismScalarSchurStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesAllOfCommutesRationalUnitaryPointsStatement

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefRoot

theorem coef_root : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
    {A : FamIn D.what₂.LL G Pl0 T m} {cR : Bridge.CoefDat D D.sp.X'} {cL : ∀ i : Fin m, Bridge.CoefDat D (D.sp.V ((i : ℕ) + 1))}
    {lR : ∀ t, Bridge.LevEnv D D.sp.X' (A.ok t × ℕ)} {lL : ∀ (i : Fin m) t, Bridge.LevEnv D (D.sp.V ((i : ℕ) + 1)) (A.ok t × ℕ)}
    (B : Bridge.FamReal D A cR cL lR lL) (pl : Pl0 → Pl D.host.E) (S : Set (Pl D.host.E)) (Qt : T → Finset (Pl D.host.E))
    (tauL : D.what₂.Tau → (D.host.E →+* D.what₂.LL)) (lamR : D.what₂.Tau → DomWeight D.sp.X'.rank)
    (lamL : ∀ i : Fin m, D.what₂.Tau → DomWeight (D.sp.V ((i : ℕ) + 1)).rank)
    (gramR gramR' : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R c0R' : VV D.what₂.LL lamR →ₛₗ[D.what₂.embLL] cR.W)
    (c0L c0L' : ∀ i : Fin m, VV D.what₂.LL (lamL i) →ₛₗ[D.what₂.embLL] (cL i).W),
    Bridge.FamTie B pl S Qt tauL lamR lamL gramR c0R c0L → Bridge.FamTie B pl S Qt tauL lamR lamL gramR' c0R' c0L' →
    ∀ i : Fin m, ∃ a : D.what₂.LL, (∃ k : ℕ, k ≠ 0 ∧ a ^ k = 1) ∧ ∀ F, c0L' i F = D.what₂.embLL a • c0L i F := by
  intro D G _ _ Pl0 T m A cR cL lR lL B pl S Qt tauL lamR lamL gramR gramR' c0R c0R' c0L c0L' h h' i
  rcases subsingleton_or_nontrivial (VV D.what₂.LL (lamL i)) with hs | hs
  · exact ⟨1, ⟨1, one_ne_zero, one_pow _⟩, fun F => by rw [Subsingleton.elim F 0, map_zero, map_zero, smul_zero]⟩
  obtain ⟨e, hrat, hco, hpa, hnab, -⟩ := h.coefL i A.μ0
  obtain ⟨e₂, hrat₂, hco₂, hpa₂, hnab₂, -⟩ := h'.coefL i A.μ0
  let g : Module.End D.what₂.LL (VV D.what₂.LL (lamL i)) := (e₂.symm.trans e).toLinearMap
  have hcg : ∀ v, c0L' i v = c0L i (g v) := fun v => by
    have h1 := hco₂ (e₂.symm v)
    rw [e₂.apply_symm_apply] at h1
    rw [← h1, hco]
    rfl
  have hinj : Function.Injective (c0L i) :=
    GlobalTheory.GalLift.rescale_inj (bVV D.what₂.LL (lamL i)) D.what₂.embLL (c0L i) (h.mapL i).2.1
  have hcomm : ∀ (γ : GQ (D.sp.V ((i : ℕ) + 1))) (γE : GL (Fin (D.sp.V ((i : ℕ) + 1)).rank) D.host.E),
      Bridge.IsRatMat _ γ γE → ∀ v, g (rhoVr tauL (lamL i) γE v) = rhoVr tauL (lamL i) γE (g v) := by
    intro γ γE hγ v
    apply hinj
    rw [← hcg, (h'.mapL i).1 γ γE hγ, hcg, (h.mapL i).1 γ γE hγ]
  obtain ⟨a, ha⟩ := GlobalTheory.T.coefficientSpace_endomorphism_scalar_schur D.what₂.LL (lamL i) g (GlobalTheory.T.commutes_all_of_commutes_rationalUnitaryPoints D _ tauL h.tauL_ok (lamL i) g hcomm)
  have hea : ∀ x, e x = a • e₂ x := fun x => by
    have h1 := ha (e₂ x)
    simpa [g] using h1
  haveI := e.toEquiv.nontrivial
  obtain ⟨i0⟩ := (A.MtCSD i A.μ0).bV.index_nonempty
  have hx0 := (A.MtCSD i A.μ0).bV.ne_zero i0
  have hy0 : e₂ ((A.MtCSD i A.μ0).bV i0) ≠ 0 := fun h0 => hx0 (e₂.injective (h0.trans (map_zero e₂).symm))
  have hm : a ∈ Formalism.DivisionValues.cmMax D.what₂.LL :=
    GlobalTheory.CoefUniq.mem_of_coords _ (bVV D.what₂.LL (lamL i)) a hy0 (fun k => hea _ ▸ hrat i0 k) (hrat₂ i0)
  have hst : star a * a = 1 := by
    have hinj' := GlobalTheory.GalLift.rescale_inj _ D.what₂.embLL _ (B.L i A.μ0).pres.coef_li
    have hp0 := GlobalTheory.CoefUniq.pair_ne_zero D.what₂.embLL _ hinj' _ (B.L i A.μ0).pres.coef_pair hx0
    refine GlobalTheory.CoefUniq.star_mul_self_of_pair _ a ((hpa₂ _ _).trans_ne hp0) ?_
    rw [← hea, hpa, hpa₂]
  have hi : IsIntegral ℤ a := by
    obtain ⟨cl, -⟩ := ((B.L i A.μ0).pres.reps 1).exists
    have hL := nabAtr_isLattice tauL (lamL i) _
      (GlobalTheory.RepsCompare.isLattice_hLat (D.sp.V ((i : ℕ) + 1)) ((B.L i A.μ0).pres.y cl))
    refine GlobalTheory.CoefUniq.isIntegral_of_keeps _ (fun h0 => ?_) hL.fg a (fun n hn => ?_)
    · have h1 := hL.span_eq_top
      rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at h1
      exact bot_ne_top h1
    · rw [← hnab₂ cl] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      rw [← hnab cl]
      exact ⟨m, hm, hea m⟩
  obtain ⟨n, hn, han⟩ := GlobalTheory.CoefUniq.pow_eq_one_of_cmMax hm hst hi
  exact ⟨a, ⟨n, hn, han⟩, fun F => by rw [hcg, ha, LinearMap.map_smulₛₗ]⟩

end GlobalTheory.CoefRoot
