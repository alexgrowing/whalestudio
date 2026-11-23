import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.CoefInv

open GlobalTheory.SplitScalar GlobalTheory.HeisOrtho

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def coef (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f : WO S T → ℂ)
    (w : WO S T) : ℂ := ∫ x in 𝓕, heisO ψ S T w f x * star (f x) ∂μ

theorem coef_right (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) {f : WO S T → ℂ} {u : WO S T}
    (hu : heisO ψ S T u f = f) (w : WO S T) :
    coef ψ S T μ 𝓕 f w = ψ (symplOH S T w u) * coef ψ S T μ 𝓕 f (w + u) := by
  have h := heisO_heisO ψ S T w u f
  rw [hu] at h
  unfold coef
  rw [h, ← integral_const_mul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem coef_left (hψ : IsCharAF D.host.F ψ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {u : WO S T}
    (hu : heisO ψ S T u f = f) (w : WO S T) :
    coef ψ S T μ 𝓕 f w = ψ (symplOH S T u w) * coef ψ S T μ 𝓕 f (w + u) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have key := setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕
    (fun x => heisO ψ S T w f x * star (f x)) (by
      intro γ hγ x
      have h0 := mul_conj_of_norm_one (hψ.2.1 (-(symplOH S T γ x)))
      have h1 := heisO_quasi hf w γ hγ x
      have h2 := heisO_quasi hf 0 γ hγ x
      rw [heisO_zero] at h2
      show heisO ψ S T w f (γ + x) * (starRingEnd ℂ) (f (γ + x)) = _
      rw [h1, h2, map_mul, mul_mul_mul_comm, h0, one_mul]
      rfl) u
  unfold coef
  rw [← key, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h0 := mul_conj_of_norm_one (hψ.2.1 (symplOH S T x u))
  have h1 : ψ (symplOH S T x u) * heisO ψ S T w f (x + u) = ψ (symplOH S T u w) * heisO ψ S T (u + w) f x :=
    congrFun (heisO_heisO ψ S T u w f) x
  have h2 : ψ (symplOH S T x u) * f (x + u) = f x := congrFun hu x
  show heisO ψ S T w f (x + u) * (starRingEnd ℂ) (f (x + u)) =
    ψ (symplOH S T u w) * (heisO ψ S T (w + u) f x * (starRingEnd ℂ) (f x))
  rw [← h2, add_comm w u, ← mul_assoc, ← h1, map_mul, mul_mul_mul_comm, h0, one_mul]

theorem char_eq_one (hψ : IsCharAF D.host.F ψ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {u : WO S T}
    (hu : heisO ψ S T u f = f) {w : WO S T} (hw : coef ψ S T μ 𝓕 f w ≠ 0) : ψ (symplO S T w u) = 1 := by
  have h1 := coef_right μ 𝓕 hu w
  have h2 := coef_left hψ hμ h𝓕 hf hu w
  have h3 : coef ψ S T μ 𝓕 f (w + u) ≠ 0 := fun h => hw (by rw [h1, h, mul_zero])
  have h4 := mul_right_cancel₀ h3 (h1.symm.trans h2)
  rw [← symplOH_add_self, AddChar.map_add_eq_mul]
  nth_rewrite 2 [h4]
  rw [← AddChar.map_add_eq_mul, symplOH_skew S T w u, add_neg_cancel, AddChar.map_zero_eq_one]

theorem nsmul_cancel {m n : ℕ} {N : ℕ} (hN : 0 < N) {x y : Mx D m n} (h : N • x = N • y) : x = y := by
  have hu : IsUnit (N : AE D) := by
    have h1 : IsUnit (N : D.host.F) := (Nat.cast_ne_zero.2 hN.ne').isUnit
    have h2 := (h1.map (algebraMap D.host.F (AF D.host.F))).map (algebraMap (AF D.host.F) (AE D))
    rwa [map_natCast, map_natCast] at h2
  refine Matrix.ext fun i j => hu.mul_left_cancel ?_
  have h3 : N • x i j = N • y i j := congrFun (congrFun h i) j
  rwa [nsmul_eq_mul, nsmul_eq_mul] at h3

theorem symplO_nsmul (N : ℕ) (x y : WO S T) : symplO S T (N • x) y = symplO S T x (N • y) := by
  have h := symplO_smul S T (N : AE D) x y
  rwa [map_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul] at h

theorem real_part (w : WO S T) : (realIdem D • w).map (finPart D) = 0 := by
  funext i j
  show finPart D (realIdem D * w i j) = 0
  rw [RingHom.map_mul, finPart_realIdem, zero_mul]

theorem fin_part (w : WO S T) : (w - realIdem D • w).map (infPart D) = 0 := by
  funext i j
  show infPart D (w i j - realIdem D * w i j) = 0
  rw [RingHom.map_sub, RingHom.map_mul, infPart_realIdem, one_mul, sub_self]

theorem actO_real {g : GA D S} {h : GA D T} (hg : g ∈ GfC S) (hh : h ∈ GfC T) {u : WO S T}
    (hu : u.map (finPart D) = 0) : actO S T g h u = u := by
  have h1 : (Formalism.L2.Theta.mt T h).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hh)
  have h2 : (Formalism.L2.Theta.mt S g⁻¹).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 (inv_mem hg))
  have h3 : (actO S T g h u).map (infPart D) = u.map (infPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, h1, h2, Matrix.one_mul, Matrix.mul_one]
  have h4 : (actO S T g h u).map (finPart D) = u.map (finPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]
  exact Matrix.ext fun i j => adele_ext (congrFun (congrFun h3 i) j) (congrFun (congrFun h4 i) j)

theorem eventually_mod (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (N : ℕ) (hN : 0 < N) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1, ∀ x ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 x = x + N • l := by
  obtain ⟨G, hG, hGl, hgen⟩ := GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT
  have h := (Filter.eventually_all_finite hG).2 fun u hu =>
    GlobalTheory.LatNhds.eventually_move S T ΛS ΛT hS hT u (latO_fin (hGl u hu)) N hN
  filter_upwards [h] with p hp
  intro w hw
  have key := hgen (((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    fun _ => True).map (nsmulAddMonoidHom N)).comap (GlobalTheory.LatLevel.actHom S T p.1 p.2 - AddMonoidHom.id _))
    (fun α hα u hu => ?_) w hw
  · obtain ⟨l, hl, e⟩ := key
    refine ⟨l, hl, ?_⟩
    have e' : N • l = actO S T p.1 p.2 w - w := e
    rw [e', add_sub_cancel]
  · obtain ⟨l, hl, e⟩ := hp u hu
    refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • l,
      GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩) _ hl, ?_⟩
    show N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • l) =
      actO S T p.1 p.2 (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u) -
        algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u
    rw [GlobalTheory.LatNhds.actO_smul, e, smul_add, add_sub_cancel_left, smul_comm]

theorem eventually_coef_of_ne (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : ∀ᶠ p : GA D S × GA D T in 𝓝 1, p.1 ∈ GfC S → p.2 ∈ GfC T → ∀ w,
      coef ψ S T μ 𝓕 f w ≠ 0 → coef ψ S T μ 𝓕 f (actO S T p.1 p.2 w) = coef ψ S T μ 𝓕 f w := by
  have hS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨N, hN, hNU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T _ _ hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T _ _ hS hT)).1 U hU
  have hfix := fun u hu => hUf _ (hNU u hu) (latO_fin (AddSubgroup.nsmul_mem _ hu N))
  filter_upwards [eventually_mod _ _ hS hT (N * (2 * N)) (by positivity)] with p hp hg hh w hw
  have hfin : (N • (w - realIdem D • w)).map (infPart D) = 0 := by
    rw [GlobalTheory.LatNhds.fin_iff, smul_comm, GlobalTheory.LatNhds.fin_iff.1 (fin_part w), nsmul_zero]
  have hmem := GlobalTheory.LatVac.mem_of_char hψ hS hT hfin fun u hu => by
    rw [symplO_nsmul, symplO_sub_left, symplO_real_fin S T (real_part w) (latO_fin (AddSubgroup.nsmul_mem _ hu N)),
      sub_zero]
    exact char_eq_one hψ.1 hμ h𝓕 hf (hfix u hu) hw
  obtain ⟨l, hl, e⟩ := hp _ hmem
  have e1 : actO S T p.1 p.2 (w - realIdem D • w) = (w - realIdem D • w) + (2 * N) • l := by
    refine nsmul_cancel hN ?_
    rw [nsmul_add, ← mul_nsmul', ← e]
    exact (map_nsmul (GlobalTheory.LatLevel.actHom S T p.1 p.2) N _).symm
  have e2 : actO S T p.1 p.2 w = w + N • (l + l) := by
    have h := GlobalTheory.LatNhds.actO_add p.1 p.2 (realIdem D • w) (w - realIdem D • w)
    rw [e1, actO_real hg hh (real_part w), ← add_assoc, add_sub_cancel] at h
    rw [h, ← two_nsmul, ← mul_nsmul]
  have h1 := coef_right μ 𝓕 (hfix _ (AddSubgroup.add_mem _ hl hl)) w
  rw [nsmul_add, symplOH_add_right, symplOH_add_self, char_eq_one hψ.1 hμ h𝓕 hf (hfix l hl) hw, one_mul,
    ← nsmul_add] at h1
  rw [e2, ← h1]

theorem eventually_coef_actO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ᶠ p : GA D S × GA D T in 𝓝 1, p.1 ∈ GfC S → p.2 ∈ GfC T → ∀ w, ∫ x in 𝓕, heisO ψ S T (actO S T p.1 p.2 w) f x * star (f x) ∂μ = ∫ x in 𝓕, heisO ψ S T w f x * star (f x) ∂μ := by
  intro D ψ hψ S T μ 𝓕 hμ h𝓕 f hf
  have h1 := eventually_coef_of_ne hψ hμ h𝓕 hf
  haveI : ∀ V : HSp D, IsTopologicalGroup (GA D V) := fun V => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have ht : Filter.Tendsto (fun p : GA D S × GA D T => p⁻¹) (𝓝 1) (𝓝 1) := by
    have := (continuous_inv (G := GA D S × GA D T)).tendsto 1
    rwa [inv_one] at this
  filter_upwards [h1, ht.eventually h1] with p hp hp' hg hh w
  show coef ψ S T μ 𝓕 f (actO S T p.1 p.2 w) = coef ψ S T μ 𝓕 f w
  by_cases hw : coef ψ S T μ 𝓕 f w = 0
  · by_contra hne
    have h2 := hp' (inv_mem hg) (inv_mem hh) _ (hw ▸ hne)
    have h3 := GlobalTheory.AdelicLatMove.actO_actO_inv S T p.1⁻¹ p.2⁻¹ w
    rw [inv_inv, inv_inv] at h3
    exact hne (h2.symm.trans (congrArg _ h3))
  · exact hp hg hh w hw

end GlobalTheory.Mem.CoefInv

end
