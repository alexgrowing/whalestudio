import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

noncomputable section

namespace GlobalTheory.ThK.Check

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem incM_one : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem isEv_id (B : Base F E) (M : Model σ X W) : IsEv B M M 1 1 ∅ LinearMap.id where
  maps := fun _ h => h
  Heisenberg₂ := fun z Φ _ => by simp [incM_one]
  inv := fun _ h => h.elim
  loc := ⟨ContinuousLinearMap.id _ _, fun _ => LinearMap.id, by
    classical
    intro h
    let b : ContDiffBump (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
    have hs : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) := b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
    have h1 := congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) => T (hs.toSchwartzMap hc) 0) h
    have h2 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
    simp [h2] at h1,
    fun v => ⟨rfl, Submodule.map_id _⟩, fun _ _ _ _ => rfl⟩

theorem isLevi_one (H' : Plane E d d₁) : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' 1 1 1 := by
  simp [IsLevi, mat]

theorem shiftA_levi (H : Plane E n n₁) (H' : Plane E d d₁) {t : (AE F E)ˣ} {h₁ : UA σ W₁.J} {m : UA σ W.J}
    (h : IsLevi H' t h₁ m) (l : (AE F E)ˣ) : shiftA H H' l * (mat m)ᵀ = cA σ (t⁻¹).1 • shiftA H H' l := by
  rw [shiftA, Matrix.smul_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, h.2.1, smul_comm]
  congr 1
  ext i j
  simp [Matrix.vecMulVec_apply, mul_left_comm]

theorem shiftB_levi (H : Plane E n n₁) (H' : Plane E d d₁) {t : (AE F E)ˣ} {h₁ : UA σ W₁.J} {m : UA σ W.J}
    (h : IsLevi H' t h₁ m) (l : (AE F E)ˣ) : shiftB σ H H' l * (mat m)ᵀ = t.1 • shiftB σ H H' l := by
  rw [shiftB, Matrix.smul_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, h.1, smul_comm]
  congr 1
  ext i j
  simp [Matrix.vecMulVec_apply, mul_left_comm]

theorem isCT_const (H' : Plane E d d₁) (c : ℂ) : IsCT (σ := σ) (W := W) H' (fun _ => c) fun _ => c := by
  intro μ 𝓕 _ _ h1 h
  rw [integral_const, Measure.real, Measure.restrict_apply_univ, h1, ENNReal.toReal_one, one_smul]

theorem hasLaw_const (H' : Plane E d d₁) (c : ℂ) : HasLaw (σ := σ) (W := W) W₁ H' 1 0 fun _ => c := by
  intro t m _ h
  simp

theorem eq_zero_of_hasLaw (H' : Plane E d d₁) {χ χ' : Chr F E} {z z' : ℝ} (hz : z ≠ z') {T : UA σ W.J → ℂ}
    (h : HasLaw W₁ H' χ z T) (h' : HasLaw W₁ H' χ' z' T) {t : (AE F E)ˣ} {m : UA σ W.J} (hm : IsLevi (W₁ := W₁) H' t 1 m)
    (h0 : 0 < (absE F E t : ℝ)) (ht : (absE F E t : ℝ) ≠ 1) : T = 0 := by
  funext g
  by_contra hg
  have e := congrArg norm (mul_right_cancel₀ hg ((h t m hm g).symm.trans (h' t m hm g)))
  simp only [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos h0 _)] at e
  exact hz ((Real.rpow_right_inj h0 ht).1 e)

example (a a' : ℝ) : (1 - a) / 2 + (a + a' - 1) / 2 = a' / 2 ∧ (1 - a') / 2 + (a + a' - 1) / 2 = a / 2 := by
  constructor <;> ring

def intLat (E : Type) [Field E] [NumberField E] (n : ℕ) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.pi Set.univ fun _ => ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E)

variable (F) in

def hyp (ε : E) : Spc F E 2 := ⟨!![0, 1; ε, 0], intLat E 2, fun _ => !![0, 1; 1, 0], fun _ => 1⟩

variable (F E) in

def pt : Spc F E 0 := ⟨1, ⊤, fun _ => 1, fun _ => 1⟩

variable (E) in

def pl : Plane E 2 0 := ⟨![1, 0], ![0, 1], 0, 1⟩

theorem pl_adapted (B : Base F E) (ε : E) : (pl E).IsAdapted σ B (hyp F ε) (pt F E) 0 1 where
  rank := rfl
  xx := by simp [form, pl, hyp, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  yy := by simp [form, pl, hyp, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  xy := by simp [form, pl, hyp, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  orth := fun u => by simp [form, pl]
  gram := Subsingleton.elim _ _
  low := fun u => by simp [pl, pt]
  split := fun z hz => by
    refine ⟨z 0, z 1, 0, ?_, ?_, trivial, ?_⟩
    · intro i _
      fin_cases i
      · simpa [pl] using hz 0 trivial
      · simp [pl]
    · intro i _
      fin_cases i
      · simp [pl]
      · simpa [pl] using hz 1 trivial
    · funext i
      fin_cases i <;> simp [pl]
  ideal := fun s => by
    constructor
    · intro h i _
      fin_cases i
      · simpa [pl] using h
      · simp [pl]
    · intro h
      simpa [pl] using h 0 trivial
  cartan := fun w => ⟨Subsingleton.elim _ _, 1, one_ne_zero, by
    funext i
    fin_cases i <;> simp [pl, hyp, Matrix.mulVec, dotProduct, Fin.sum_univ_two]⟩
  bas := fun v i => by
    refine ⟨fun h r => ?_, fun h r => ?_, fun j => j.elim0⟩ <;> fin_cases i <;> fin_cases r <;> simp_all [pl, hyp]

theorem nonempty_model (h2 : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (h1 : ∀ i j, σ (X.J j i) = X.J i j)
    (h5 : ∀ i j, σ (W.J j i) = -W.J i j) (h1' : X.J.det ≠ 0) (h5' : W.J.det ≠ 0) : Nonempty (Model σ X W) := by
  obtain ⟨co, -⟩ := GlobalTheory.RatDarboux.exists_darboux (AF F) h2 σ hσ h1 h5 h1' h5'
  exact ⟨⟨co, fun _ => 0, 0, ∅⟩⟩

theorem exists_cfg (h2 : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (B : Base F E) :
    (∃ (G : Geo σ 0 (0 + 2)) (G₁ : Geo σ 0 0) (H : Plane E (0 + 2) 0) (H' : Plane E (0 + (0 + 2)) (0 + 0)), CfgB B G G₁ H H') ∧
    ∃ (G : Geo σ (0 + 2) 0) (G₁ : Geo σ 0 0) (H : Plane E (0 + 2) 0) (H' : Plane E (0 + 2 + 0) (0 + 0)), CfgA B G G₁ H H' := by
  have a1 : ∀ i j, σ ((hyp F (1 : E)).J j i) = (hyp F (1 : E)).J i j := fun i j => by
    fin_cases i <;> fin_cases j <;> simp [hyp]
  have a2 : ∀ i j, σ ((hyp F (-1 : E)).J j i) = -(hyp F (-1 : E)).J i j := fun i j => by
    fin_cases i <;> fin_cases j <;> simp [hyp]
  have d1 : (hyp F (1 : E)).J.det ≠ 0 := by simp [hyp, Matrix.det_fin_two]
  have d2 : (hyp F (-1 : E)).J.det ≠ 0 := by simp [hyp, Matrix.det_fin_two]
  have d0 : (pt F E).J.det ≠ 0 := by simp
  obtain ⟨M⟩ := nonempty_model h2 hσ a1 a2 d1 d2
  obtain ⟨M₀⟩ := nonempty_model (X := pt F E) h2 hσ (fun i => i.elim0) a2 d0 d2
  obtain ⟨M₁⟩ := nonempty_model (X := pt F E) (W := pt F E) h2 hσ (fun i => i.elim0) (fun i => i.elim0) d0 d0
  exact ⟨⟨⟨0, 1, pt F E, hyp F 1, hyp F (-1), M₀, M⟩, ⟨0, 0, pt F E, pt F E, pt F E, M₁, M₁⟩, pl E, pl E,
      rfl, rfl, rfl, pl_adapted B _, pl_adapted B _⟩,
    ⟨1, 0, hyp F 1, pt F E, hyp F (-1), M, M₀⟩, ⟨0, 0, pt F E, pt F E, pt F E, M₁, M₁⟩, pl E, pl E,
      rfl, rfl, rfl, rfl, pl_adapted B _, pl_adapted B _⟩

theorem resEta_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {a b m : ℕ} (h : ResEtaPow K χ a) (h' : ResEtaPow K χ' b)
    (hm : m = a + b) : ResEtaPow K (χ / χ') m := fun x => by
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x, hm]
  split_ifs
  · simp
  · rcases neg_one_pow_eq_or ℂ b with e | e <;> simp [pow_add, e, div_neg]

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]⟩

theorem isPair_of_isTriple {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {Y : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (h : IsTriple B G Y om om') :
    IsPair B G.M Y.β (Y.β / Y.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) ∧
      IsPair B G.M' Y.α (Y.α / Y.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
      resEta_div h.chars.resβ h.chars.resα rfl, h.weil⟩,
    h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
      resEta_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem conv_range {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} (h : G.IsGood B) : a + a' + 2 * min (a - G.p) G.p < 2 * a := by
  have := h.eBig
  omega

theorem intInd_mem_SB {κ : Type} [Fintype κ] (v : HeightOneSpectrum (𝓞 F)) :
    Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1 ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  have hU : {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} =
      Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x; simp
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_integer _
  have hC : IsClosed (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isClosed_integer _
  have hK : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  rw [hU]
  have hUo : IsOpen (Set.pi Set.univ (fun _ : κ => (v.adicCompletionIntegers F : Set (Fv F v)))) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => hO)
  have hUc : IsClosed (Set.pi Set.univ (fun _ : κ => (v.adicCompletionIntegers F : Set (Fv F v)))) :=
    isClosed_set_pi (fun _ _ => hC)
  have hUk : IsCompact (Set.pi Set.univ (fun _ : κ => (v.adicCompletionIntegers F : Set (Fv F v)))) :=
    isCompact_univ_pi (fun _ => hK)
  generalize Set.pi Set.univ (fun _ : κ => (v.adicCompletionIntegers F : Set (Fv F v))) = U at hUo hUc hUk ⊢
  refine ⟨IsLocallyConstant.iff_isOpen_fiber.2 fun y => ?_, ?_⟩
  · by_cases h1 : (1 : ℂ) = y
    · have : U.indicator 1 ⁻¹' {y} = U := by
        ext x
        by_cases hx : x ∈ U <;> simp [hx, ← h1]
      rw [this]; exact hUo
    · by_cases h0 : (0 : ℂ) = y
      · have : U.indicator 1 ⁻¹' {y} = Uᶜ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx, ← h0]
        rw [this]; exact hUc.isOpen_compl
      · have : U.indicator 1 ⁻¹' {y} = ∅ := by
          ext x
          by_cases hx : x ∈ U <;> simp [hx] <;> assumption
        rw [this]; exact isOpen_empty
  · exact hUk.of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal Set.support_indicator_subset hUc)

open scoped Classical in

def oneS (κ : Type) [Fintype κ] [IsEmpty κ] : SInf F κ :=
  HasCompactSupport.toSchwartzMap (f := fun _ => (1 : ℂ)) (HasCompactSupport.of_compactSpace _) contDiff_const

def evOrigin (R κ κ' : Type) [Zero R] : ((κ → R) → ℂ) →ₗ[ℂ] ((κ' → R) → ℂ) where
  toFun Φ := fun _ => Φ 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem const_mem_SB {R κ : Type} [TopologicalSpace R] [IsEmpty κ] (φ : (κ → R) → ℂ) : φ ∈ SB (κ → R) :=
  ⟨IsLocallyConstant.of_discrete _, HasCompactSupport.of_compactSpace _⟩

open scoped Classical in

theorem isEv_origin (B : Base F E) {n₁ d₁ : ℕ} [IsEmpty (Fin n₁ × Fin d₁)] {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (M : Model σ X W)
    (M₁ : Model σ X₁ W₁) (hv : ∀ v, M₁.vac v = fun _ => M.vac v 0) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (hI : ∀ u ∈ I, (M.co.e u).1 = 0) :
    IsEv B M M₁ ι ι' I (evOrigin (AF F) _ _) where
  maps := fun Φ _ => by
    refine Submodule.subset_span ⟨Φ 0 • oneS (F := F) _, fun _ => 1, const_mem_SB _, ?_⟩
    funext x
    simp [pureA, evOrigin, oneS]
  Heisenberg₂ := fun z Φ _ => by
    have hz : z = 0 := by
      ext i j
      exact isEmptyElim (i, j)
    subst hz
    funext x
    simp [Darboux.rho, schr, evOrigin]
  inv := fun u hu Φ _ => by
    funext x
    simp [Darboux.rho, schr, evOrigin, hI u hu]
  loc := by
    refine ⟨((BoundedContinuousFunction.evalCLM ℂ (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F)).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)).smulRight (oneS _), fun v => evOrigin _ _ _, ?_,
      fun v => ⟨(hv v).symm, ?_⟩, fun f φ _ _ => ?_⟩
    · intro h
      let b : ContDiffBump (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
      have hs : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) := b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
      have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
      have h1 := congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁) => T (hs.toSchwartzMap hc) 0) h
      have h2 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
      simp [h2, oneS] at h1
    · refine le_antisymm ?_ fun φ _ => ⟨φ 0 • _, Submodule.smul_mem _ _ (intInd_mem_SB v), ?_⟩
      · rintro _ ⟨φ, -, rfl⟩
        exact const_mem_SB _
      · funext x
        rw [Subsingleton.elim x 0]
        simp [evOrigin, Set.indicator, zero_mem]
    · funext x
      have e1 : (fun i : Fin n × Fin d => evI F ((0 : Fin n × Fin d → AF F) i)) = 0 :=
        funext fun _ => map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      have e2 : ∀ v, (fun i : Fin n × Fin d => evFin F v ((0 : Fin n × Fin d → AF F) i)) = 0 := fun v => funext fun _ => map_zero _
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, evOrigin, LinearMap.coe_mk, AddHom.coe_mk, e1, e2]
      simp [oneS]

theorem isStab_unique (B : Base F E) {K K' : Subgroup (UA σ X.J)} (h : IsStab B K) (h' : IsStab B K') : K = K' :=
  Subgroup.ext fun g => (h g).trans (h' g).symm

theorem split2_unique {a a' : ℕ} (ha : a ≠ a') {W : Spc F E (a + a')} {H' : Plane E (a + a') d₁} {Y : Chars F E}
    {f fa fb ga gb : UA σ W.J → ℂ} (h : Split2 W₁ H' Y f fa fb) (h' : Split2 W₁ H' Y f ga gb)
    (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ) (h1 : μ 𝓕 = 1)
    {t : (AE F E)ˣ} {m : UA σ W.J} (hm : IsLevi (W₁ := W₁) H' t 1 m) (h0 : 0 < (absE F E t : ℝ)) (ht : (absE F E t : ℝ) ≠ 1) :
    fa = ga ∧ fb = gb := by
  have e : fa + fb = ga + gb := funext fun g => (h.1 μ 𝓕 hμ h𝓕 h1 g).trans (h'.1 μ 𝓕 hμ h𝓕 h1 g).symm
  have e' : fa - ga = gb - fb := by linear_combination e
  have la : HasLaw W₁ H' Y.α ((a' : ℝ) / 2) (fa - ga) := fun t m hm g => by
    rw [Pi.sub_apply, Pi.sub_apply, h.2.1 t m hm g, h'.2.1 t m hm g]; ring
  have lb : HasLaw W₁ H' Y.β ((a : ℝ) / 2) (fa - ga) := fun t m hm g => by
    rw [e', Pi.sub_apply, Pi.sub_apply, h.2.2 t m hm g, h'.2.2 t m hm g]; ring
  have hz : ((a' : ℝ) / 2) ≠ (a : ℝ) / 2 := fun k => ha (by exact_mod_cast (by linarith : (a : ℝ) = a'))
  have z := eq_zero_of_hasLaw H' hz la lb hm h0 ht
  exact ⟨sub_eq_zero.1 z, (sub_eq_zero.1 (e' ▸ z)).symm⟩

example {a a' : ℕ} (h : a' < a) (he : Even (a + a')) :
    (a : ℝ) / 2 - (((a - a') / 2 : ℕ) : ℝ) = a' / 2 ∧ ((a' : ℝ) - 2) / 2 + (((a - a') / 2 + 1 : ℕ) : ℝ) = a / 2 := by
  obtain ⟨k, hk⟩ := he
  have e : a = a' + 2 * ((a - a') / 2) := by omega
  generalize (a - a') / 2 = x at e
  subst e
  push_cast
  constructor <;> ring

example (Y : Chars F E) (t s : (AE F E)ˣ) (h : Y.ν s = (Y.ν t)⁻¹) : Y.β t * (Y.ν s)⁻¹ = Y.α t ∧ Y.α t * Y.ν s = Y.β t := by
  rw [h, Chars.ν, MonoidHom.div_apply]
  constructor <;> simp

end GlobalTheory.ThK.Check

end
