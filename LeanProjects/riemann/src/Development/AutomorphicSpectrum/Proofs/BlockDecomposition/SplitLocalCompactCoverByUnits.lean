import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetSplitPlaceLatticeIntersection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormEqInv

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.CoverS

section Split

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU NumberField IsDedekindDomain
open scoped TensorProduct NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} {M : ℕ}

def comp (τ : E →ₐ[F] Fv F v) (X : Fin 1 → Fin M → Fv F v ⊗[F] E) : Fin 1 → Fin M → Fv F v :=
  fun p k => splitProj τ (X p k)

theorem continuous_comp (τ : E →ₐ[F] Fv F v) : Continuous (comp (M := M) τ) :=
  continuous_pi fun p => continuous_pi fun k =>
    (continuous_splitProj τ).comp ((continuous_apply k).comp (continuous_apply p))

def glue (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (Y Z : Fin 1 → Fin M → Fv F v) :
    Fin 1 → Fin M → Fv F v ⊗[F] E :=
  fun p k => (splitAlgEquiv h τ).symm (Y p k, Z p k)

theorem continuous_glue (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    Continuous fun W : (Fin 1 → Fin M → Fv F v) × (Fin 1 → Fin M → Fv F v) => glue h τ W.1 W.2 :=
  continuous_pi fun p => continuous_pi fun k => (continuous_splitAlgEquiv_symm h τ).comp (by fun_prop)

theorem comp_glue_left (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (Y Z : Fin 1 → Fin M → Fv F v) :
    comp τ (glue h τ Y Z) = Y := by
  funext p k
  simp [comp, glue]

theorem comp_glue_right (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (Y Z : Fin 1 → Fin M → Fv F v) :
    comp (τ.comp σ) (glue h τ Y Z) = Z := by
  funext p k
  simp [comp, glue]

theorem glue_comp (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (X : Fin 1 → Fin M → Fv F v ⊗[F] E) :
    glue h τ (comp τ X) (comp (τ.comp σ) X) = X := by
  funext p k
  exact split_ext h τ (by simp [comp, glue]) (by simp [comp, glue])

def unitVecs (σ : E →ₐ[F] E) (τ : E →ₐ[F] Fv F v) : Set (Fin 1 → Fin M → Fv F v ⊗[F] E) :=
  {X | ‖comp τ X‖ = 1 ∧ ‖comp (τ.comp σ) X‖ = 1}

theorem isOpen_unitVecs (τ : E →ₐ[F] Fv F v) : IsOpen (unitVecs (M := M) σ τ) := by
  have hS : IsOpen {Y : Fin 1 → Fin M → Fv F v | ‖Y‖ = 1} := by
    have := IsUltrametricDist.isOpen_sphere (0 : Fin 1 → Fin M → Fv F v) (r := 1) one_ne_zero
    have e : {Y : Fin 1 → Fin M → Fv F v | ‖Y‖ = 1} = Metric.sphere 0 1 := Set.ext fun Y => by simp
    rw [e]
    exact this
  exact (hS.preimage (continuous_comp τ)).inter (hS.preimage (continuous_comp (τ.comp σ)))

theorem isCompact_unitVecs (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) : IsCompact (unitVecs (M := M) σ τ) := by
  haveI : ProperSpace (Fv F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  have hS : IsCompact (Metric.sphere (0 : Fin 1 → Fin M → Fv F v) 1) := isCompact_sphere _ _
  have := (hS.prod hS).image (continuous_glue h τ)
  convert this using 1
  ext X
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(comp τ X, comp (τ.comp σ) X), ⟨by simpa using h1, by simpa using h2⟩, glue_comp h τ X⟩
  · rintro ⟨⟨Y, Z⟩, ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [comp_glue_left]; simpa using h1
    · rw [comp_glue_right]; simpa using h2

theorem comp_ne_zero_of_free (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v)
    {X : Fin 1 → Fin M → Fv F v ⊗[F] E} (hX : LinearIndependent (Fv F v ⊗[F] E) X) : comp τ X ≠ 0 := by
  intro h0
  have h1 := Fintype.linearIndependent_iff.1 hX (fun _ => splitIdem h τ) (by
    funext k
    have e : splitProj τ (X 0 k) = 0 := congrFun (congrFun h0 0) k
    simpa using (splitProj_eq_zero_iff h τ _).1 e) 0
  simpa using congrArg (splitProj τ) h1

theorem proj_eq_zero_of_smul (ρ : E →ₐ[F] Fv F v) {X : Fin 1 → Fin M → Fv F v ⊗[F] E}
    {c : Fv F v ⊗[F] E} (hc : ∀ k, c * X 0 k = 0) (hρ : comp ρ X ≠ 0) : splitProj ρ c = 0 := by
  by_contra hne
  refine hρ ?_
  funext p k
  obtain rfl : p = 0 := Subsingleton.elim _ _
  have := congrArg (splitProj ρ) (hc k)
  rw [map_mul, map_zero] at this
  exact (mul_eq_zero.1 this).resolve_left hne

theorem free_of_comp_ne_zero (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v)
    {X : Fin 1 → Fin M → Fv F v ⊗[F] E} (h1 : comp τ X ≠ 0) (h2 : comp (τ.comp σ) X ≠ 0) :
    LinearIndependent (Fv F v ⊗[F] E) X := by
  refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have hc : ∀ k, g 0 * X 0 k = 0 := fun k => by simpa using congrFun hg k
  exact split_ext h τ (by simpa using proj_eq_zero_of_smul τ hc h1)
    (by simpa using proj_eq_zero_of_smul (τ.comp σ) hc h2)

theorem unitVecs_subset_free (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    unitVecs (M := M) σ τ ⊆ {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
  rintro X ⟨h1, h2⟩
  refine free_of_comp_ne_zero h τ (fun e => ?_) (fun e => ?_)
  · rw [e, norm_zero] at h1; exact zero_ne_one h1
  · rw [e, norm_zero] at h2; exact zero_ne_one h2

theorem exists_entry_norm (hM : 0 < M) (Y : Fin 1 → Fin M → Fv F v) : ∃ p k, ‖Y p k‖ = ‖Y‖ := by
  haveI : Nonempty (Fin M) := Fin.pos_iff_nonempty.1 hM
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun b => ‖Y b‖₊)
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun b => ‖Y p b‖₊)
  refine ⟨p, k, ?_⟩
  have e1 : ‖Y‖₊ = ‖Y p‖₊ := by rw [Pi.nnnorm_def]; exact hp
  have e2 : ‖Y p‖₊ = ‖Y p k‖₊ := by rw [Pi.nnnorm_def]; exact hk
  exact congrArg NNReal.toReal (e1.trans e2).symm

theorem exists_scale {ϖ : Fv F v} (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (hM : 0 < M)
    {Y : Fin 1 → Fin M → Fv F v} (hY : Y ≠ 0) :
    ∃ (j : ℤ) (Y' : Fin 1 → Fin M → Fv F v), ‖Y'‖ = 1 ∧ ‖Y‖ = ‖ϖ‖ ^ j ∧ ∀ p k, Y p k = ϖ ^ j * Y' p k := by
  have hq := GlobalTheory.NormFvFacts.absNorm_gt_one F v
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by positivity
  have hϖ0 : ϖ ≠ 0 := fun e => by
    rw [e, norm_zero] at hϖ
    exact inv_ne_zero hq0 hϖ.symm
  obtain ⟨p, k, hpk⟩ := exists_entry_norm hM Y
  have ha : Y p k ≠ 0 := fun e => hY (norm_eq_zero.1 (by rw [← hpk, e, norm_zero]))
  obtain ⟨m, hm⟩ := GlobalTheory.NormFvFacts.norm_eq_zpow F v (Y p k) ha
  refine ⟨-m, ϖ ^ m • Y, ?_, ?_, fun p k => ?_⟩
  · rw [norm_smul, norm_zpow, hϖ, ← hpk, hm, inv_zpow, inv_mul_cancel₀ (zpow_ne_zero _ hq0)]
  · rw [← hpk, hm, hϖ, zpow_neg, inv_zpow, inv_inv]
  · simp only [Pi.smul_apply, smul_eq_mul, zpow_neg]
    rw [inv_mul_cancel_left₀ (zpow_ne_zero _ hϖ0)]

def mkU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (a b : (Fv F v)ˣ) : (Fv F v ⊗[F] E)ˣ where
  val := (splitAlgEquiv h τ).symm ((a : Fv F v), (b : Fv F v))
  inv := (splitAlgEquiv h τ).symm (((a⁻¹ : (Fv F v)ˣ) : Fv F v), ((b⁻¹ : (Fv F v)ˣ) : Fv F v))
  val_inv := by
    rw [← map_mul, Prod.mk_mul_mk, Units.mul_inv, Units.mul_inv, Prod.mk_one_one, map_one]
  inv_val := by
    rw [← map_mul, Prod.mk_mul_mk, Units.inv_mul, Units.inv_mul, Prod.mk_one_one, map_one]

theorem splitProj_mkU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (a b : (Fv F v)ˣ) :
    splitProj τ (mkU h τ a b : Fv F v ⊗[F] E) = a := splitProj_symm h τ _

theorem splitProj_comp_mkU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (a b : (Fv F v)ˣ) :
    splitProj (τ.comp σ) (mkU h τ a b : Fv F v ⊗[F] E) = b := splitProj_comp_symm h τ _

theorem nnnorm_norm_mkU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (a b : (Fv F v)ˣ) :
    ‖Algebra.norm (Fv F v) (mkU h τ a b : Fv F v ⊗[F] E)‖₊ = ‖(a : Fv F v)‖₊ * ‖(b : Fv F v)‖₊ := by
  rw [GlobalTheory.SplitInterDet.norm_eq_split h τ, splitProj_mkU, splitProj_comp_mkU, nnnorm_mul]

theorem summable_pow {t : ℝ≥0} (ht0 : t ≠ 0) (ht : t < 1) (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    Summable fun i : ℕ × ℕ => (t ^ ((i.1 : ℤ) - k) * t ^ ((i.2 : ℤ) - k)) ^ n := by
  rw [← NNReal.summable_coe]
  have h0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht0
  have h1 : (t : ℝ) < 1 := by exact_mod_cast ht
  have hp : 0 ≤ (t : ℝ) := t.2
  have g : Summable fun a : ℕ => ((t : ℝ) ^ (-(k : ℤ))) ^ n * ((t : ℝ) ^ n) ^ a :=
    (summable_geometric_of_lt_one (by positivity) (pow_lt_one₀ hp h1 hn)).mul_left _
  have hg : 0 ≤ fun a : ℕ => ((t : ℝ) ^ (-(k : ℤ))) ^ n * ((t : ℝ) ^ n) ^ a := fun a => by
    show 0 ≤ ((t : ℝ) ^ (-(k : ℤ))) ^ n * ((t : ℝ) ^ n) ^ a
    positivity
  refine (Summable.mul_of_nonneg g g hg hg).congr fun i => ?_
  have e : ∀ a : ℕ, (t : ℝ) ^ ((a : ℤ) - k) = (t : ℝ) ^ a * (t : ℝ) ^ (-(k : ℤ)) := fun a => by
    rw [sub_eq_add_neg, zpow_add₀ h0, zpow_natCast]
  simp only [NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_zpow]
  rw [e, e]
  ring

theorem neg_lt_of_norm_lt {ϖ : Fv F v} (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) {x : ℝ} {j : ℤ} {k : ℕ}
    (e : x = ‖ϖ‖ ^ j) (hx : x < (Ideal.absNorm v.asIdeal : ℝ) ^ k) : -(k : ℤ) < j := by
  have hq := GlobalTheory.NormFvFacts.absNorm_gt_one F v
  rw [e, hϖ, inv_zpow', ← zpow_natCast] at hx
  have := (zpow_lt_zpow_iff_right₀ hq).1 hx
  omega

theorem cover (h : IsCMExt F E σ) (hM : 2 ≤ M) (τ : E →ₐ[F] Fv F v)
    {A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)} (hA : IsCompact A) :
    ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (u : ι → (Fv F v ⊗[F] E)ˣ),
      IsCompact P ∧ IsOpen P ∧ P ⊆ {X | LinearIndependent (Fv F v ⊗[F] E) X} ∧
      Summable (fun i => ‖Algebra.norm (Fv F v) (u i : Fv F v ⊗[F] E)‖₊ ^ (M - 1)) ∧
      A ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X} ⊆
        ⋃ i, (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) =>
          (u i : Fv F v ⊗[F] E) * X p k) '' P := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.NormFvFacts.exists_norm_eq_inv F v
  have hq := GlobalTheory.NormFvFacts.absNorm_gt_one F v
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by positivity
  have hϖ0 : ϖ ≠ 0 := fun e => by
    rw [e, norm_zero] at hϖ
    exact inv_ne_zero hq0 hϖ.symm
  have hlt : ‖ϖ‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, hϖ, NNReal.coe_one]
    exact inv_lt_one_of_one_lt₀ hq
  obtain ⟨C1, hC1⟩ := hA.exists_bound_of_continuousOn (continuous_comp (M := M) τ).continuousOn
  obtain ⟨C2, hC2⟩ := hA.exists_bound_of_continuousOn (continuous_comp (M := M) (τ.comp σ)).continuousOn
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (max C1 C2) hq
  let w : (Fv F v)ˣ := Units.mk0 ϖ hϖ0
  refine ⟨ℕ × ℕ, inferInstance, unitVecs σ τ, fun i => mkU h τ (w ^ ((i.1 : ℤ) - k)) (w ^ ((i.2 : ℤ) - k)),
    isCompact_unitVecs h τ, isOpen_unitVecs τ, unitVecs_subset_free h τ, ?_, ?_⟩
  · refine (summable_pow (nnnorm_ne_zero_iff.2 hϖ0) hlt k (n := M - 1) (by omega)).congr fun i => ?_
    rw [nnnorm_norm_mkU]
    simp [w, Units.val_zpow_eq_zpow_val, nnnorm_zpow]
  · rintro X ⟨hXA, hXf⟩
    obtain ⟨j1, Y1, n1, e1, f1⟩ := exists_scale hϖ (by omega) (comp_ne_zero_of_free h τ hXf)
    obtain ⟨j2, Y2, n2, e2, f2⟩ := exists_scale hϖ (by omega) (comp_ne_zero_of_free h (τ.comp σ) hXf)
    have b1 := neg_lt_of_norm_lt hϖ e1 ((hC1 X hXA).trans_lt ((le_max_left _ _).trans_lt hk))
    have b2 := neg_lt_of_norm_lt hϖ e2 ((hC2 X hXA).trans_lt ((le_max_right _ _).trans_lt hk))
    have c1 : (((j1 + k).toNat : ℤ) - k) = j1 := by omega
    have c2 : (((j2 + k).toNat : ℤ) - k) = j2 := by omega
    refine Set.mem_iUnion.2 ⟨((j1 + k).toNat, (j2 + k).toNat), glue h τ Y1 Y2, ⟨?_, ?_⟩, ?_⟩
    · rw [comp_glue_left]; exact n1
    · rw [comp_glue_right]; exact n2
    · funext p m
      refine split_ext h τ ?_ ?_
      · have := congrFun (congrFun (comp_glue_left h τ Y1 Y2) p) m
        simp only [map_mul, splitProj_mkU, c1]
        refine Eq.trans ?_ (f1 p m).symm
        rw [← this]
        simp [w, comp, Units.val_zpow_eq_zpow_val]
      · have := congrFun (congrFun (comp_glue_right (σ := σ) h τ Y1 Y2) p) m
        simp only [map_mul, splitProj_comp_mkU, c2]
        refine Eq.trans ?_ (f2 p m).symm
        rw [← this]
        simp [w, comp, Units.val_zpow_eq_zpow_val]

end Split

section Main

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem exists_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 2 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] Fv F v), ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (u : ι → (Fv F v ⊗[F] E)ˣ), IsCompact P ∧ IsOpen P ∧ P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Summable (fun i => ‖Algebra.norm (Fv F v) (u i : Fv F v ⊗[F] E)‖₊ ^ (M - 1)) ∧ A ∩ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ i, (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u i : Fv F v ⊗[F] E) * X p k) '' P := by
  intro F E _ _ _ _ _ σ hE M hM v τ A hA
  exact cover hE hM τ hA

end Main

end GlobalTheory.CompanionTheory.WeilSiegel.Free.CoverS
