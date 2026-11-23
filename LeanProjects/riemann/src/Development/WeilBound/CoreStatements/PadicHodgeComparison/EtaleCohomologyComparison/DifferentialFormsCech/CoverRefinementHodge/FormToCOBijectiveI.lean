import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.BridgeLApply
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechFormsAddSmulStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsToCechBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsToCechSmulStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.FormCochPullPf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PfPull

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om.Nt2F

open CrystallineSemistableComparison.Om.Glob CrystallineSemistableComparison.Om.Cech CrystallineSemistableComparison.Om.Nt2

def bridgeI (hB : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_bijective _)) (hS : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_smul _))
    {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Pb.Cov q) (a j : ℕ) :
    (formCos q U.U a).cx.H j ≃ₗ[K] CO q U.U a j :=
  LinearEquiv.ofBijective
    { toFun := formToCO q U.U a j
      map_add' := map_add _
      map_smul' := hS q U.U a j }
    (hB q U.U (cov_aff U) a j)

theorem bridgeI_apply (hB : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_bijective _)) (hS : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_smul _))
    {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Pb.Cov q) (a j : ℕ)
    (y : (formCos q U.U a).cx.H j) : bridgeI hB hS q U a j y = formToCO q U.U a j y := rfl

def lerayI (hA : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOmAdd_smul _)) {K : Type} [Field K] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (U : Pb.Cov q) (a j : ℕ) : CO q U.U a j ≃ₗ[K] HodgeC q a j :=
  (cechOmAdd q U.U U.cover (cov_aff U) a j).toLinearEquiv (hA q U.U U.cover (cov_aff U) a j)

theorem lerayI_apply (hA : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOmAdd_smul _)) {K : Type} [Field K] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (U : Pb.Cov q) (a j : ℕ) (y : CO q U.U a j) :
    lerayI hA q U a j y = cechOmAdd q U.U U.cover (cov_aff U) a j y := rfl

def isoI (hG : type_of% (@CrystallineSemistableComparison.Om.Glob.glob_iso _)) (hB : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_bijective _))
    (hS : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_smul _)) (hA : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOmAdd_smul _))
    {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Pb.Cov q)
    (a j : ℕ) : HT.Hdg q a (a + j) ≃ₗ[K] HodgeC q a j :=
  ((Classical.choose (hG K) q U a j).trans (bridgeI hB hS q U a j)).trans (lerayI hA q U a j)

set_option maxHeartbeats 2000000 in

theorem isoI_nat (hG : type_of% (@CrystallineSemistableComparison.Om.Glob.glob_iso _)) (hB : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_bijective _))
    (hS : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_smul _)) (hA : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOmAdd_smul _))
    (hP : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOm_pull _)) (hC : type_of% (@CrystallineSemistableComparison.Om.Cech.formCoch_pull _))
    {K : Type} [Field K] [CharZero K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [Smooth p] (u : X ⟶ Y) (hu : u ≫ p = q) (U : Pb.Cov q) (W : Pb.Cov p)
    (τ : U.ι → W.ι) (hτ : ∀ α, U.U α ≤ u ⁻¹ᵁ W.U (τ α)) (a j : ℕ) (x : HT.Hdg p a (a + j)) :
    isoI hG hB hS hA q U a j (HT.pullH u hu a (a + j) x) = pullC u hu a j (isoI hG hB hS hA p W a j x) := by
  have hτ' : ∀ n (i : Fin (n + 1) → U.ι), Pb.capO U.U i ≤ u ⁻¹ᵁ Pb.capO W.U (τ ∘ i) :=
    fun n i => capO_pre u U.U W.U τ hτ i
  obtain ⟨c, hc, rfl⟩ : ∃ (c : (formCos p W.U a).X j) (h0 : (formCos p W.U a).cx.d j c = 0),
      (Classical.choose (hG K) p W a j).symm ((formCos p W.U a).cx.cls c h0) = x := by
    obtain ⟨⟨c, h0⟩, hx⟩ := Submodule.Quotient.mk_surjective _ (Classical.choose (hG K) p W a j x)
    exact ⟨c, h0, by rw [LinearEquiv.symm_apply_eq]; exact hx⟩
  set c' : (formCos q U.U a).X j := fun i => formRes q (hτ' j i) a (formPull hu (Pb.capO W.U (τ ∘ i)) a (c (τ ∘ i)))
    with hc'
  have hd : (formCos q U.U a).cx.d j c' = fun i =>
      formRes q (hτ' (j + 1) i) a (formPull hu (Pb.capO W.U (τ ∘ i)) a ((formCos p W.U a).cx.d j c (τ ∘ i))) := by
    funext i
    change (Cos.d (formCos q U.U a) j c') i =
      formRes q (hτ' (j + 1) i) a (formPull hu (Pb.capO W.U (τ ∘ i)) a (Cos.d (formCos p W.U a) j c (τ ∘ i)))
    let evU : (formCos q U.U a).X (j + 1) →+ OmU q (Pb.capO U.U i) a :=
      { toFun := fun f => f i, map_zero' := rfl, map_add' := fun _ _ => rfl }
    let evW : (formCos p W.U a).X (j + 1) →+ OmU p (Pb.capO W.U (τ ∘ i)) a :=
      { toFun := fun f => f (τ ∘ i), map_zero' := rfl, map_add' := fun _ _ => rfl }
    change evU (Cos.d (formCos q U.U a) j c') =
      formRes q (hτ' (j + 1) i) a (formPull hu (Pb.capO W.U (τ ∘ i)) a (evW (Cos.d (formCos p W.U a) j c)))
    rw [Cos.d_apply, Cos.d_apply, map_sum, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, map_zsmul, map_zsmul, map_zsmul]
    congr 1
    change formRes q (Pb.capO_comp U.U i k.succAbove) a (formRes q (hτ' j (i ∘ k.succAbove)) a
        (formPull hu (Pb.capO W.U (τ ∘ (i ∘ k.succAbove))) a (c (τ ∘ (i ∘ k.succAbove))))) =
      formRes q (hτ' (j + 1) i) a (formPull hu (Pb.capO W.U (τ ∘ i)) a
        (formRes p (Pb.capO_comp W.U (τ ∘ i) k.succAbove) a (c ((τ ∘ i) ∘ k.succAbove))))
    rw [← formRes_formPull, formRes_formRes, formRes_formRes]
    rfl
  have h1 : (formCos q U.U a).cx.d j c' = 0 := by
    rw [hd]
    funext i
    have h0 : (formCos p W.U a).cx.d j c (τ ∘ i) = 0 := congrFun hc (τ ∘ i)
    refine (congrArg (fun y => formRes q (hτ' (j + 1) i) a (formPull hu (Pb.capO W.U (τ ∘ i)) a y)) h0).trans ?_
    change formRes q (hτ' (j + 1) i) a (formPull hu (Pb.capO W.U (τ ∘ i)) a 0) = 0
    exact (congrArg (formRes q (hτ' (j + 1) i) a) (map_zero _)).trans (map_zero _)
  have key := Classical.choose_spec (hG K) q p u hu U W τ hτ' a j c hc h1
  have hb : bridgeI hB hS q U a j ((formCos q U.U a).cx.cls c' h1) =
      cechPull hu W.U U.U τ hτ a j (bridgeI hB hS p W a j ((formCos p W.U a).cx.cls c hc)) := by
    rw [bridgeI_apply, bridgeI_apply, formToCO_cls, formToCO_cls]
    exact (cls_eq (hC hu W.U U.U τ hτ (fun i => hτ' _ i) a j c).symm _ _).trans
      (cechPullH_cls u.base (GlobalTheory.toAbSheafPush (omegaPull hu a)).hom W.U U.U τ hτ (formCoch p W.U a j c) _).symm
  simp only [isoI, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [key, LinearEquiv.apply_symm_apply, hb, lerayI_apply, lerayI_apply]
  exact hP q p u hu W.U W.cover (cov_aff W) U.U U.cover (cov_aff U) τ hτ a j _

theorem hdg_iso_of_ing (hG : type_of% (@CrystallineSemistableComparison.Om.Glob.glob_iso _)) (hB : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_bijective _))
    (hS : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_smul _)) (hA : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOmAdd_smul _))
    (hP : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOm_pull _)) (hC : type_of% (@CrystallineSemistableComparison.Om.Cech.formCoch_pull _))
    (hR : CovRefine) (hH : PullHId) (hCi : PullCId) : type_of% (@CrystallineSemistableComparison.Om.hdg_iso _) := by
  intro K _ _
  refine ⟨fun {X} q _ _ a j => isoI hG hB hS hA q (covX q) a j, ?_⟩
  intro X Y q p _ _ _ _ u hu a j x
  dsimp only
  obtain ⟨U', hU'⟩ := hR q (fun k : (covX q).ι × (covX p).ι => (covX q).U k.1 ⊓ u ⁻¹ᵁ (covX p).U k.2) (by
    refine eq_top_iff.2 fun z _ => ?_
    have hz : z ∈ (⨆ α, (covX q).U α) := by rw [(covX q).cover]; trivial
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    have hy : u.base z ∈ (⨆ β, (covX p).U β) := by rw [(covX p).cover]; trivial
    obtain ⟨β, hβ⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(α, β), ⟨hα, hβ⟩⟩)
  choose k hk using hU'
  have hid : 𝟙 X ≫ q = q := Category.id_comp q
  have e1 : ∀ z : HT.Hdg q a (a + j), isoI hG hB hS hA q U' a j z = isoI hG hB hS hA q (covX q) a j z := by
    intro z
    have := isoI_nat hG hB hS hA hP hC q q (𝟙 X) hid U' (covX q) (fun α => (k α).1) (fun α y hy => ((hk α) hy).1) a j z
    rwa [hH, hCi] at this
  rw [← e1]
  exact isoI_nat hG hB hS hA hP hC q p u hu U' (covX p) (fun α => (k α).2) (fun α => (hk α).trans inf_le_right) a j x

theorem formToCO_bijective_i : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_bijective _) := GlobalTheory.T.forms_to_cech_bijective
theorem formToCO_smul_i : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_smul _) := GlobalTheory.T.forms_to_cech_smul
theorem cechOmAdd_smul_i : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOmAdd_smul _) := GlobalTheory.T.cech_forms_add_smul
theorem formCoch_pull_i : type_of% (@CrystallineSemistableComparison.Om.Cech.formCoch_pull _) := CrystallineSemistableComparison.Om.Cech.formCoch_pull_pf

end CrystallineSemistableComparison.Om.Nt2F
