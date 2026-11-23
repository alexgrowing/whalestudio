import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticTraceBasisExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenStabilizerIntegralStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFamilyBoundedUniformlyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationBCompactSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarStabilizerPeriodCaseBSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentBoundedHeightReduction
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.ConeCTFin

section Step

open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Decay

open GlobalTheory.HeisSchA GlobalTheory.XTermDecay

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

end Decay

theorem absE_pos (l : (AE F E)ˣ) : 0 < (absE F E l : ℝ) := by
  have h1 : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h2 : absE F E l ≠ 0 := fun h0 => by simp [h0] at h1
  exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr h2)

variable {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b} {H : Plane E (b + 2) b}
  {H' : Plane E (a + (b + 2)) (a + b)} {e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)} {X : Chars F E}
  {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {om₁ : Rep σ G₁.V G₁.W} {om₁' : Rep σ G₁.V' G₁.W}

open GlobalTheory.XTermDecay GlobalTheory.HeisSchA in

theorem theta_bound (hKP : KP) (hC : CfgB B G G₁ H H') (he : IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e')
    (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁') {K : Subgroup (UA σ G.V'.J)} (hK : IsStab B K)
    {Φ' : Fn F (b + 2) (a + (b + 2))} (hΦ' : Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)
    (hΦA : Φ' ∈ schA F (Fin (b + 2) × Fin (a + (b + 2)))) {C' : Set (UA σ G.W.J)} (hC' : IsCompact C') :
    ∃ (k : ℕ) (U : Set (Fin (Module.finrank F E) → Af F)), IsCompact U ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ (κ : K), ∀ κ' ∈ C',
      ∀ (l : (AE F E)ˣ) g₀ h₁,
      ENNReal.ofReal ‖theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (κ.1, κ') Φ'))) g₀ h₁‖ ≤
        ENNReal.ofReal (C * (ht h₁ : ℝ) ^ k) * GlobalTheory.XTermMaj.maj F E N U (l : AE F E) := by
  obtain ⟨K', μK, μ, hK', hKc, hμK, hμ⟩ := GlobalTheory.T.theta_stabilizer_exists hKP.base F E σ B _ G.V' _ _ hT.base hT.geo.hV'
  obtain rfl : K = K' := Subgroup.ext fun g => (hK g).trans (hK' g).symm
  obtain ⟨U, hU, hsupp⟩ := GlobalTheory.T.configuration_b_compact_support F E σ B a b G G₁ H H' hC e' he X om om' hT Φ' hΦA _ (hKc.prod hC')
  have hSo := GlobalTheory.T.config_b_eigen_stabilizer_integral hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ'
  have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om' := hT.weil'
  have hmem : ∀ p : K × C', om' (p.1.1, p.2.1) Φ' ∈ schA F _ := fun p => hw.isUSplitting.pres _ Φ' hΦA
  have hbd : ∀ l ∈ (adeleClass F).adm (Fin (b + 2) × Fin (a + (b + 2))), ∃ C : ℝ, ∀ p : K × C',
      ‖l (om' (p.1.1, p.2.1) Φ')‖ ≤ C := fun l hl => by
    obtain ⟨C, hC⟩ := (hKc.prod hC').exists_bound_of_continuousOn (hw.2.2 l hl Φ' hΦA).continuousOn
    exact ⟨C, fun p => hC _ ⟨p.1.2, p.2.2⟩⟩
  obtain ⟨t, ht'⟩ := dualPair (σ := σ) G.V'.J G.W.J H.x H.y H'.x H'.y (by
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
  let T := (K × C') × {l : (AE F E)ˣ // (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U}
  have hdec : ∀ N : ℕ, ∀ l ∈ (adeleClass F).adm (Fin b × Fin (a + b)), ∃ C : ℝ, ∀ p : T,
      w p.2.1 ^ (N : ℝ) * ‖l (e' (G.M'.co.rho B.ψ (shiftB σ H H' p.2.1) (om' (p.1.1.1, p.1.2.1) Φ')))‖ ≤ C := fun N l hl => by
    obtain ⟨C, hC⟩ := form_decay B.ψ hT.base.std S U' (fun i j => by rw [← G.M'.co.form]; convert ht' i j) (l ∘ₗ e')
      (GlobalTheory.EvAdm.comp_mem_adm F E σ B _ _ _ _ _ _ _ _ _ _ _ _ _ e' hT.geo.hM' hT₁.geo.hM' he l hl) (fun i c Ψ hΨ => by
        have := he.inv (Matrix.vecMulVec (incV F H.x) (c • inclR (F := F) (AF F) (t i) • incV F H'.y)) (Or.inl ⟨_, rfl⟩) Ψ hΨ
        rw [Matrix.vecMulVec_smul, Matrix.vecMulVec_smul, Darboux.rho, map_smul] at this
        exact congrArg l this) _ hmem hbd hU N
    refine ⟨C, fun p => ?_⟩
    have h1 := hC p.1 _ p.2.2
    rw [← hS] at h1
    have h2 := Real.rpow_pos_of_pos (hw0 p.2.1) (N : ℝ)
    rw [← le_div_iff₀' h2, div_eq_mul_inv, ← Real.rpow_neg (hw0 _).le]
    exact h1
  obtain ⟨k, hk⟩ := GlobalTheory.T.schwartz_family_bounded_uniformly hKP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).2 T
    (fun p => e' (G.M'.co.rho B.ψ (shiftB σ H H' p.2.1) (om' (p.1.1.1, p.1.2.1) Φ'))) (fun p => hSo _ p.1.1 p.2.1)
    (fun l hl => by simpa using hdec 0 l hl)
  refine ⟨k, U, hU, fun N => ?_⟩
  obtain ⟨C, hCb⟩ := hk (fun p => w p.2.1 ^ (N : ℝ)) (fun p => (Real.rpow_pos_of_pos (hw0 _) _).le) (hdec N)
  refine ⟨C, fun κ κ' hκ' l g₀ h₁ => ?_⟩
  by_cases hl : (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U
  · have h1 := hCb ((κ, ⟨κ', hκ'⟩), ⟨l, hl⟩) g₀ h₁
    have h2 := Real.rpow_pos_of_pos (hw0 l) (N : ℝ)
    rw [← le_div_iff₀' h2, div_eq_mul_inv, ← Real.rpow_neg (hw0 _).le] at h1
    rw [GlobalTheory.XTermMaj.maj, Set.indicator_of_mem hl, ← ENNReal.ofReal_mul' (Real.rpow_nonneg (hw0 l).le _)]
    exact ENNReal.ofReal_le_ofReal h1
  · rw [hsupp (κ.1, κ') ⟨κ.2, hκ'⟩ l hl]
    simp [theta, thetaSum]

end Step

section Maj

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def archSize (x : AE F E) : ℝ := ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E x i).1 v‖

def finCrd (x : AE F E) : Fin (Module.finrank F E) → Af F := fun i => (GlobalTheory.XTermMaj.crd F E x i).2

theorem continuous_crd : Continuous (GlobalTheory.XTermMaj.crd F E) := by
  unfold GlobalTheory.XTermMaj.crd
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun.toLinearMap

theorem continuous_archSize : Continuous (archSize F E) := by
  unfold archSize
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun v _ => ?_
  exact ((continuous_apply v).comp (continuous_fst.comp ((continuous_apply i).comp (continuous_crd F E)))).norm

theorem continuous_finCrd : Continuous (finCrd F E) :=
  continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_crd F E))

theorem archSize_nonneg (x : AE F E) : 0 ≤ archSize F E x := by unfold archSize; positivity

theorem maj_toReal (N : ℕ) (U : Set (Fin (Module.finrank F E) → Af F)) (x : AE F E) :
    (GlobalTheory.XTermMaj.maj F E N U x).toReal = {y | finCrd F E y ∈ U}.indicator (fun y => (1 + archSize F E y) ^ (-(N : ℝ))) x := by
  unfold GlobalTheory.XTermMaj.maj
  by_cases h : finCrd F E x ∈ U
  · rw [Set.indicator_of_mem (by exact h), Set.indicator_of_mem (show x ∈ {y | finCrd F E y ∈ U} from h),
      ENNReal.toReal_ofReal]
    · rfl
    · apply Real.rpow_nonneg
      have := archSize_nonneg F E x
      exact le_trans zero_le_one (le_add_of_nonneg_right this)
  · rw [Set.indicator_of_notMem (by exact h), Set.indicator_of_notMem (show x ∉ {y | finCrd F E y ∈ U} from h)]
    rfl

theorem measurable_maj (N : ℕ) {U : Set (Fin (Module.finrank F E) → Af F)} (hU : IsCompact U) :
    Measurable fun l : (AE F E)ˣ => (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal := by
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  simp_rw [maj_toReal]
  have hc : Continuous fun l : (AE F E)ˣ => (l : AE F E) := Units.continuous_val
  have hS : MeasurableSet {l : (AE F E)ˣ | finCrd F E (l : AE F E) ∈ U} :=
    (hU.isClosed.preimage ((continuous_finCrd F E).comp hc)).measurableSet
  have hne : ∀ l : (AE F E)ˣ, 1 + archSize F E (l : AE F E) ≠ 0 ∨ 0 ≤ -(N : ℝ) := fun l =>
    Or.inl (ne_of_gt (by have := archSize_nonneg F E (l : AE F E); linarith))
  have hf : Measurable fun l : (AE F E)ˣ => (1 + archSize F E (l : AE F E)) ^ (-(N : ℝ)) :=
    ((continuous_const.add ((continuous_archSize F E).comp hc)).rpow_const hne).measurable
  have heq : (fun l : (AE F E)ˣ => {y | finCrd F E y ∈ U}.indicator (fun y => (1 + archSize F E y) ^ (-(N : ℝ))) (l : AE F E)) =
      {l : (AE F E)ˣ | finCrd F E (l : AE F E) ∈ U}.indicator (fun l => (1 + archSize F E (l : AE F E)) ^ (-(N : ℝ))) := by
    rfl
  rw [heq]
  exact hf.indicator hS

end Maj

theorem integrable_maj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (μ : Measure (AE F E)ˣ) [μ.IsHaarMeasure] {U : Set (Fin (Module.finrank F E) → Af F)} (hU : IsCompact U) {s : ℝ}
    (hs : 1 < s) : ∃ N : ℕ, Integrable
      (fun l : (AE F E)ˣ => (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal * (absE F E l : ℝ) ^ s) μ := by
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  obtain ⟨N, k, L, C', hk, hb⟩ := GlobalTheory.TateConv.bound F E hs hU
  have hpow : Continuous fun l : (AE F E)ˣ => (absE F E l : ℝ) ^ s :=
    (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE).rpow_const fun _ => Or.inr (by linarith)
  refine ⟨N, ((measurable_maj F E N hU).mul hpow.measurable).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun l => ?_) (GlobalTheory.TateConv.lintegral_bound_lt_top F E μ hs hk L C')
  refine le_trans ?_ (hb l)
  rw [Real.enorm_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)),
    ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  gcongr
  exact ENNReal.ofReal_toReal_le

theorem hasFiniteIntegral_cone : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' →
    ∀ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ →
    ∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → ∀ (g : UA σ G.W.J) (h : UA σ G₁.W.J) (μ' : Measure (unip σ G₁.W H₂)) (𝓕 : Set (unip σ G₁.W H₂)), μ'.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ G₁.W.J).subgroupOf (unip σ G₁.W H₂)) 𝓕 μ' → μ' 𝓕 = 1 →
      HasFiniteIntegral (fun p : unip σ G₁.W H₂ × (K × (AE F E)ˣ) => G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' p.2.2) (om' (p.2.1.1, g) Φ'))) (p.1.1 * h) * (X.ν p.2.2 : ℂ) * ((absE F E p.2.2 : ℝ) : ℂ) ^ (s + ((a : ℂ) + 1) / 2)) ((μ'.restrict 𝓕).prod (μK.prod μ)) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' V V' W₁' hT₂ e W₂ H₂
    i₀ i₁ hH₂
  refine ⟨1, fun s hs g h μ' 𝓕 _ _ h𝓕 => ?_⟩
  obtain ⟨_, _, _⟩ := GlobalTheory.OuterFin.ideles_lcsc F E
  haveI : SigmaCompactSpace (AE F E)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SFinite μ := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts μ)
  obtain ⟨K', -, -, hK', hKc, -, -⟩ := GlobalTheory.T.theta_stabilizer_exists hKP.base F E σ B _ G.V' _ _ hT.base hT.geo.hV'
  obtain rfl : K = K' := Subgroup.ext fun g => (hK g).trans (hK' g).symm
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  haveI : IsFiniteMeasure μK := CompactSpace.isFiniteMeasure
  haveI : IsFiniteMeasure (μ'.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [h𝓕]; exact ENNReal.one_ne_top)
  haveI : IsFiniteMeasure (G₁.M'.μ.restrict G₁.M'.dom) := isFiniteMeasure_restrict.2
    (GlobalTheory.ThKContSmall.measure_dom_lt_top hKP.siegelSetUnitary hT₁.base hT₁.geo.hV' hT₁.geo.hM').ne
  have hS := IsUWeilPair.isUSplitting hT.weil'
  have hΦA : Φ' ∈ schA F _ := by
    refine Submodule.span_le.mpr ?_ hΦ'.1
    rintro _ ⟨f, -, φ, hφ, hvac, rfl⟩
    exact GlobalTheory.BigNZ.Fam.mem hT.geo.hM' ⟨hφ, hvac⟩ f
  have hsch : ∀ (l : (AE F E)ˣ) Ψ, Ψ ∈ schA F _ → e' (G.M'.co.rho B.ψ (shiftB σ H H' l) Ψ) ∈ schA F _ := fun l Ψ hΨ =>
    he.maps _ (GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std _ _ hΨ)
  have hrat := fun Ψ hΨ => (((GlobalTheory.T.theta_basic_properties hKP.base) F E σ B _ _ _ _ _ _ _ _ _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).2).1 Ψ hΨ).2.1
  obtain ⟨R, hR⟩ := GlobalTheory.UnipCompact.exists_bounded_translate F E σ B _ _ _ W₂ H₂ _ _ _ _ hT₂.base hT₂.geo.hW hH₂
  obtain ⟨k, U, hU, hθ⟩ := theta_bound hKP hC he hT hT₁ hK hΦ' hΦA (isCompact_singleton (x := g))
  have hre : (s + ((a : ℂ) + 1) / 2).re = s.re + ((a : ℝ) + 1) / 2 := by
    rw [show ((a : ℂ) + 1) / 2 = ((((a : ℝ) + 1) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.add_re, Complex.ofReal_re]
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  obtain ⟨N, hN⟩ := integrable_maj F E μ hU (s := s.re + ((a : ℝ) + 1) / 2) (by linarith)
  obtain ⟨C, hCθ⟩ := hθ N
  refine GlobalTheory.OuterFin.hasFiniteIntegral_of_bound _ _ _ _ _
    (hN.const_mul (|C| * ((R : ℝ) * ht h) ^ k * (G₁.M'.μ.restrict G₁.M'.dom).real Set.univ)) ?_
  rintro ⟨u, κ, l⟩
  obtain ⟨γ, hγ, hγR⟩ := hR u.1 u.2
  let γ₁ : UA σ G₁.W.J := γ
  have hγ₁ : γ₁ ∈ ratU σ G₁.W.J := hγ.1
  have hγR₁ : ht (γ₁ * u.1) ≤ R := hγR
  have hht : (ht (γ₁ * (u.1 * h)) : ℝ) ≤ (R : ℝ) * ht h := by
    rw [← mul_assoc]
    exact_mod_cast (heightGL_mul_le F (γ₁ * u.1).1 h.1).trans (mul_le_mul_left hγR₁ _)
  have hmaj : GlobalTheory.XTermMaj.maj F E N U (l : AE F E) ≠ ⊤ := by
    unfold GlobalTheory.XTermMaj.maj
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (Set.indicator_le_self _ _ _)
  have hbd : ∀ g₀, ‖theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (κ.1, g) Φ'))) g₀ (u.1 * h)‖ ≤
      |C| * ((R : ℝ) * ht h) ^ k * (GlobalTheory.XTermMaj.maj F E N U (l : AE F E)).toReal := fun g₀ => by
    have e1 := hrat _ (hsch l _ (hS.pres (κ.1, g) _ hΦA)) 1 (one_mem _) γ₁ hγ₁ g₀ (u.1 * h)
    rw [one_mul] at e1
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmaj) (hCθ κ g rfl l g₀ (γ₁ * (u.1 * h)))
    rw [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_ofReal', e1] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right (max_le ?_ (by positivity)) ENNReal.toReal_nonneg)
    calc _ ≤ |C| * (ht (γ₁ * (u.1 * h)) : ℝ) ^ k := by gcongr; exact le_abs_self C
      _ ≤ _ := by gcongr
  have hI := norm_integral_le_of_norm_le_const (μ := G₁.M'.μ.restrict G₁.M'.dom) (Eventually.of_forall hbd)
  rw [norm_mul, norm_mul, Circle.norm_coe, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (absE_pos l), hre,
    ← mul_assoc]
  refine mul_le_mul_of_nonneg_right (hI.trans (le_of_eq ?_)) (Real.rpow_nonneg (NNReal.coe_nonneg _) _)
  ring

end GlobalTheory.ConeCTFin

end
