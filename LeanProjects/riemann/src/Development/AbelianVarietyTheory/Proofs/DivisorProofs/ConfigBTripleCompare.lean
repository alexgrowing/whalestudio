import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticTraceBasisExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenStabilizerIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleStabilizerStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeDecay

open GlobalTheory.HeisSchA GlobalTheory.XTermDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem I_smul {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (c : ℂ) (Φ : Fn F n d)
    (h : UA σ W.J) : M.I om (c • Φ) h = c * M.I om Φ h := by
  simp only [Model.I, theta, thetaSum, map_smul, Pi.smul_apply, smul_eq_mul, tsum_mul_left, integral_const_mul]

theorem tendsto_smul_zero {κ : Type} [Fintype κ] (f : ℕ → SInf F κ)
    (hf : ∀ p : Seminorm ℂ (SInf F κ), Continuous p → ∃ C : ℝ, ∀ t, p (f t) ≤ C) :
    Tendsto (fun k : ℕ => (((1 / ((k : ℝ) + 1) : ℝ) : ℂ)) • f k) atTop (𝓝 0) := by
  rw [(schwartz_withSeminorms ℂ _ ℂ).tendsto_nhds]
  intro i ε hε
  obtain ⟨C, hC⟩ := hf _ ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm i)
  have h1 : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) * C) atTop (𝓝 (0 * C)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mul_const C
  rw [zero_mul] at h1
  filter_upwards [h1.eventually (gt_mem_nhds hε)] with k hk
  rw [sub_zero, map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine lt_of_le_of_lt ?_ hk
  gcongr
  exact hC k

theorem bounded_I (hS : SoCont) {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') {T : Type} (Ψ : T → Fn F n d)
    (hΨ : ∀ t, Ψ t ∈ schA F (Fin n × Fin d)) (hSo : ∀ t, Ψ t ∈ M.So B.ψ B.τ₁)
    (hb : ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), ∃ C : ℝ, ∀ t, ‖l (Ψ t)‖ ≤ C) (h : UA σ W.J) :
    ∃ C : ℝ, ∀ t, ‖M.I om (Ψ t) h‖ ≤ C := by
  obtain ⟨m, g, f, hg, hdec, hf⟩ := exists_decomp Ψ hΨ hb
  by_contra hcon
  push Not at hcon
  choose t ht using fun k : ℕ => hcon ((k : ℝ) + 1)
  have hu : ∀ k : ℕ, ∑ j, pureA F ((((1 / ((k : ℝ) + 1) : ℝ) : ℂ)) • f j (t k) : SInf F _) (g j) =
      (((1 / ((k : ℝ) + 1) : ℝ) : ℂ)) • Ψ (t k) := fun k => by
    rw [hdec, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => funext fun x => ?_
    exact mul_assoc _ _ _
  have h0 : ∑ j, pureA F (0 : SInf F (Fin n × Fin d)) (g j) = (0 : ℂ) • (0 : Fn F n d) := by
    rw [smul_zero]
    exact Finset.sum_eq_zero fun j _ => funext fun x => zero_mul _
  have hlim := hS F E σ B n d X W M χX χW om r s r' s' hP m g (fun _ => 0)
    (fun k j => (((1 / ((k : ℝ) + 1) : ℝ) : ℂ)) • f j (t k))
    (fun j => ⟨hg j, tendsto_smul_zero (fun k => f j (t k)) fun p hp => (hf j p hp).imp fun C hC k => hC _⟩)
    (fun k => by rw [hu]; exact Submodule.smul_mem _ _ (hSo _))
    (by rw [h0]; exact Submodule.smul_mem _ _ (Submodule.zero_mem _)) h
  simp only [hu, h0, I_smul, zero_mul] at hlim
  obtain ⟨k, hk⟩ := (hlim.norm.eventually (gt_mem_nhds (show ‖(0 : ℂ)‖ < 1 by simp))).exists
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), one_div,
    inv_mul_lt_iff₀ (by positivity), mul_one] at hk
  exact lt_asymm hk (ht k)

def oneS : SInf F Empty where
  toFun _ := 1
  smooth' := contDiff_const
  decay' k n := ⟨_, fun x => le_of_eq (by rw [show x = 0 from funext fun i => i.elim])⟩

theorem form_decay {κ ι T : Type} [Fintype κ] [Fintype ι] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (S U : ι → (κ → AF F) × (κ → AF F)) (hSU : ∀ i j, (S j).1 ⬝ᵥ (U i).2 - (U i).1 ⬝ᵥ (S j).2 = if i = j then 1 else 0)
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ (adeleClass F).adm κ)
    (hinv : ∀ i (a : AF F), ∀ Φ ∈ schA F κ, l (schr ψ (a • U i) Φ) = l Φ)
    (Ψ : T → (κ → AF F) → ℂ) (hΨ : ∀ t, Ψ t ∈ schA F κ) (hb : ∀ l ∈ (adeleClass F).adm κ, ∃ C : ℝ, ∀ t, ‖l (Ψ t)‖ ≤ C)
    {Ω : Set (ι → Af F)} (hΩ : IsCompact Ω) (N : ℕ) :
    ∃ C : ℝ, ∀ t (x : ι → AF F), (fun i => (x i).2) ∈ Ω →
      ‖l (schr ψ (∑ i, x i • S i) (Ψ t))‖ ≤ C * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖) ^ (-(N : ℝ)) := by
  obtain ⟨m, g, f, hg, hdec, hf⟩ := exists_decomp Ψ hΨ hb
  choose C hC using fun j => slice_decay ψ hψ S U hSU (l.smulRight (⇑(oneS (F := F))))
    (fun g hg => by
      obtain ⟨L, hL⟩ := hl g hg
      exact ⟨L.smulRight oneS, fun f => by rw [LinearMap.smulRight_apply, hL]; rfl⟩)
    (fun i a Φ hΦ => by rw [LinearMap.smulRight_apply, LinearMap.smulRight_apply, hinv i a Φ hΦ])
    (hg j) (f j) (hf j) hΩ (schwartzSeminormFamily ℂ _ ℂ (0, 0)) ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm _) N
  refine ⟨∑ j, C j, fun t x hx => ?_⟩
  rw [hdec t, Finset.sum_mul]
  change ‖l (schrL ψ _ _)‖ ≤ _
  rw [map_sum, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  obtain ⟨f₁, h1, h2⟩ := hC j t x hx
  refine le_trans ?_ h2
  have h3 := congrFun h1 0
  have h4 := SchwartzMap.norm_le_seminorm ℂ f₁ 0
  rw [h3] at h4
  refine le_trans (le_of_eq ?_) h4
  change _ = ‖_ * (1 : ℂ)‖
  rw [mul_one]
  rfl

theorem dualPair {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (x y : Fin n → E) (x' y' : Fin d → E)
    (h1 : form σ J y x = 1) (h2 : form σ J' x' y' = 1) : ∃ t : Fin (Module.finrank F E) → E, ∀ i j,
      symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')
        (inclR (F := F) (AF F) (σ (Module.finBasis F E j)) • Matrix.vecMulVec (incV F y) (incV F x'))
        (inclR (F := F) (AF F) (t i) • Matrix.vecMulVec (incV F x) (incV F y')) = if i = j then 1 else 0 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let s : E ≃ₐ[F] E := AlgEquiv.ofBijective σ σ.bijective
  let bb := (Module.finBasis F E).map s.toLinearEquiv
  let b' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) bb
  refine ⟨fun i => s.symm (-b' i), fun i j => ?_⟩
  have hσt : σ (s.symm (-b' i)) = -b' i := s.apply_symm_apply _
  rw [GlobalTheory.ArchDualPair.lhs_eq, GlobalTheory.ArchDualPair.lhs_eq, symp, GlobalTheory.ArchDualPair.hTens_incM,
    GlobalTheory.ArchDualPair.hTens_vecMulVec', GlobalTheory.ArchDualPair.form_smul, hσt, h1, h2,
    show (-1 : AE F E) = inclR (F := F) (AF F) (-1) by simp, ← map_mul, GlobalTheory.ArchDualPair.trace_inclR']
  have ht : Algebra.trace F E (-1 * (σ (Module.finBasis F E j) * -b' i * 1 * 1)) = Algebra.traceForm F E (b' i) (bb j) := by
    rw [Algebra.traceForm_apply, show bb j = σ (Module.finBasis F E j) from rfl]; congr 1; ring
  rw [ht, LinearMap.BilinForm.apply_dualBasis_left]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]

theorem form_swap_herm (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (x y : Fin n → E) : form σ J y x = σ (form σ J x y) := by
  have hσ : ∀ z, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem cone_decay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h, ∀ N : ℕ, ∃ C : ℝ, ∀ (k : K) (l : (AE F E)ˣ),
      ‖G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) 1‖ ≤
        C * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K hK X om om' om₁ om₁' hT hT₁ Φ' hΦ' h N
  obtain ⟨K', μK, μ, hK', hKc, hμK, hμ⟩ := GlobalTheory.T.theta_stabilizer_exists hKP.base F E σ B _ G.V' _ _ hT.base hT.geo.hV'
  obtain rfl : K = K' := Subgroup.ext fun g => (hK g).trans (hK' g).symm
  obtain ⟨U, hU, hsupp⟩ := GlobalTheory.T.config_B_triple_stabilizer hKP F E σ B a b G G₁ H H' hC e' he K hK X om om' om₁ om₁' hT hT₁ Φ' hΦ' h
  have hSo := GlobalTheory.T.config_b_eigen_stabilizer_integral hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h
  have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om' := hT.weil'
  have hΦA : Φ' ∈ schA F _ := by
    refine Submodule.span_le.mpr ?_ hΦ'.1
    rintro _ ⟨f, -, φ, hφ, hvac, rfl⟩
    exact GlobalTheory.BigNZ.Fam.mem hT.geo.hM' ⟨hφ, hvac⟩ f
  have hmem : ∀ k : K, om' (k.1, h) Φ' ∈ schA F _ := fun k => hw.isUSplitting.pres (k.1, h) Φ' hΦA
  have hbd : ∀ l ∈ (adeleClass F).adm (Fin (b + 2) × Fin (a + (b + 2))), ∃ C : ℝ, ∀ k : K, ‖l (om' (k.1, h) Φ')‖ ≤ C :=
    fun l hl => by
      have hc := (hw.2.2 l hl Φ' hΦA).comp
        (continuous_id.prodMk continuous_const : Continuous fun g : UA σ G.V'.J => (g, h))
      obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hc.continuousOn
      exact ⟨C, fun k => hC k.1 k.2⟩
  obtain ⟨t, ht⟩ := dualPair (σ := σ) G.V'.J G.W.J H.x H.y H'.x H'.y (by
    rw [form_swap_herm hT.base.cm hT.geo.hV'.herm, hC.hH.xy, map_one]) hC.hH'.xy
  let S := fun j => G.M'.co.e (inclR (F := F) (AF F) (σ (Module.finBasis F E j)) • Matrix.vecMulVec (incV F H.y) (incV F H'.x))
  let U' := fun i => G.M'.co.e (inclR (F := F) (AF F) (t i) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
  have hS : ∀ l : (AE F E)ˣ, G.M'.co.e (shiftB σ H H' l) = ∑ i, GlobalTheory.XTermMaj.crd F E (l : AE F E) i • S i := fun l => by
    simp only [S, ← map_smul, ← map_sum, ← smul_assoc, ← Finset.sum_smul]
    congr 2
    rw [shiftB]
    congr 1
    refine (congrArg (cA σ) ((Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun (l : AE F E)).symm).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.TensorProduct.basis_apply]
    rfl
  let w : (AE F E)ˣ → ℝ := fun l => 1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖
  have hw0 : ∀ l, 0 < w l := fun l => by positivity
  let T := K × {l : (AE F E)ˣ // (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U}
  obtain ⟨C, hCb⟩ := bounded_I (GlobalTheory.T.schwartz_orbit_continuous hKP) (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).2
    (fun p : T => ((w p.2.1 ^ (N : ℝ) : ℝ) : ℂ) • e' (G.M'.co.rho B.ψ (shiftB σ H H' p.2.1) (om' (p.1.1, h) Φ')))
    (fun p => Submodule.smul_mem _ _ (he.maps _ (schr_mem_schA B.ψ hT.base.std _ _ (hmem p.1))))
    (fun p => Submodule.smul_mem _ _ (hSo p.1 p.2.1)) (fun l hl => by
      obtain ⟨C, hC⟩ := form_decay B.ψ hT.base.std S U' (fun i j => by rw [← G.M'.co.form]; convert ht i j) (l ∘ₗ e')
        (GlobalTheory.EvAdm.comp_mem_adm F E σ B _ _ _ _ _ _ _ _ _ _ _ _ _ e' hT.geo.hM' hT₁.geo.hM' he l hl) (fun i c Ψ hΨ => by
          have := he.inv (Matrix.vecMulVec (incV F H.x) (c • inclR (F := F) (AF F) (t i) • incV F H'.y)) (Or.inl ⟨_, rfl⟩) Ψ hΨ
          rw [Matrix.vecMulVec_smul, Matrix.vecMulVec_smul, Darboux.rho, map_smul] at this
          exact congrArg l this) _ hmem hbd hU N
      refine ⟨C, fun p => ?_⟩
      have h1 := hC p.1 _ p.2.2
      rw [← hS] at h1
      have h2 := Real.rpow_pos_of_pos (hw0 p.2.1) (N : ℝ)
      rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg h2.le, ← le_div_iff₀' h2, div_eq_mul_inv,
        ← Real.rpow_neg (hw0 _).le]
      exact h1) 1
  refine ⟨|C|, fun k l => ?_⟩
  have h2 := Real.rpow_pos_of_pos (hw0 l) (N : ℝ)
  have h3 := Real.rpow_pos_of_pos (hw0 l) (-(N : ℝ))
  by_cases hl : (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U
  · have h1 := (hCb (k, ⟨l, hl⟩)).trans (le_abs_self C)
    rw [I_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg h2.le, ← le_div_iff₀' h2, div_eq_mul_inv,
      ← Real.rpow_neg (hw0 _).le] at h1
    exact h1
  · rw [hsupp k l hl, norm_zero]
    exact mul_nonneg (abs_nonneg _) h3.le

end GlobalTheory.ConeDecay

end
