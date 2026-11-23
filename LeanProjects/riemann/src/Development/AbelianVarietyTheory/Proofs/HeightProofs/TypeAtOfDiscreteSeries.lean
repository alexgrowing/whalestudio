import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.BlattnerShiftsSignedParameters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAndHasSumKAvg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactAverageKFiniteFiniteRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverageStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactFiniteApproxIdentityStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RankOneOperatorMemOfTranslationAverageClosedStatement

noncomputable section

namespace GlobalTheory.SeriesToClosure

section Model

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)} {S : List (List (Mx n))} {v v' : ℕ → H} {ℓ : ℕ → (H →ₗ[ℂ] ℂ)} {C : ℕ → ℝ}
  {f f' : Mx n → ℂ}

theorem sob_add (hσ : IsURepOn (UJset ε) σ) (hS : Words (lieSet ε) S) {x y : H} (hx : Sm ε σ x) (hy : Sm ε σ y) :
    sobNorm σ S (x + y) ≤ sobNorm σ S x + sobNorm σ S y := by
  induction S with
  | nil => simp [sobNorm]
  | cons l S ih =>
    have h1 := ih fun l' h => hS l' (List.mem_cons_of_mem _ h)
    have h2 := norm_add_le (Dw σ l x) (Dw σ l y)
    rw [← Dw_add hσ (hS l List.mem_cons_self) hx hy] at h2
    simp only [sobNorm, List.map_cons, List.sum_cons] at h1 ⊢
    linarith

theorem sob_smul (hσ : IsURepOn (UJset ε) σ) (hS : Words (lieSet ε) S) (c : ℂ) {x : H} (hx : Sm ε σ x) :
    sobNorm σ S (c • x) = ‖c‖ * sobNorm σ S x := by
  induction S with
  | nil => simp [sobNorm]
  | cons l S ih =>
    have h1 := ih fun l' h => hS l' (List.mem_cons_of_mem _ h)
    have h2 := norm_smul c (Dw σ l x)
    rw [← Dw_smul hσ (hS l List.mem_cons_self) c hx] at h2
    simp only [sobNorm, List.map_cons, List.sum_cons] at h1 ⊢
    rw [h1, mul_add]
    exact congrArg (· + _) h2

theorem sob_sum (hσ : IsURepOn (UJset ε) σ) (hS : Words (lieSet ε) S) {ι : Type} (s : Finset ι) (z : ι → ℂ) {a : ι → H}
    (ha : ∀ j, Sm ε σ (a j)) : sobNorm σ S (∑ j ∈ s, z j • a j) ≤ ∑ j ∈ s, ‖z j‖ * sobNorm σ S (a j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := sob_smul hσ hS 0 (x := 0) (smooth (Jm ε) σ).zero_mem
    simp only [zero_smul, norm_zero, zero_mul] at this
    simp [this]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← sob_smul hσ hS _ (ha j)]
    exact (sob_add hσ hS ((smooth (Jm ε) σ).smul_mem _ (ha j))
      ((smooth (Jm ε) σ).sum_mem fun j _ => (smooth (Jm ε) σ).smul_mem _ (ha j))).trans (by linarith)

abbrev Expn (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) := IsExpnAll (lieSet ε) (UJset ε) σ

theorem Expn.mk' (h : Expn ε σ S v ℓ C f) (hS : Words (lieSet ε) S) (h1 : ∀ i, Sm ε σ (v' i))
    (h2 : ∀ S', Words (lieSet ε) S' → Summable fun i => C i * sobNorm σ S' (v' i))
    (h3 : ∀ g ∈ UJset ε, HasSum (fun i => ℓ i (σ g (v' i))) (f' g)) : Expn ε σ S v' ℓ C f' :=
  ⟨⟨h1, h.1.2.1, h.1.2.2.1, h2 S hS, h3⟩, h2⟩

theorem Expn.translate (hσ : IsURepOn (UJset ε) σ) (h : Expn ε σ S v ℓ C f) (hS : Words (lieSet ε) S) {g : Mx n}
    (hg : g ∈ UJset ε) (hf : ∀ y ∈ UJset ε, f' y = f (y * g)) : Expn ε σ S (fun i => σ g (v i)) ℓ C f' := by
  refine h.mk' hS (fun i => Sm.translate hσ (h.1.1 i) hg) (fun S' hS' => ?_) fun y hy => ?_
  · simp only [fun i => sobNorm_translate hσ hg (h.1.1 i) hS']
    refine h.2 _ fun l hl X hX => ?_
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact conj_mem_lie (isUnit_Jm ε) hg (hS' l' hl' Y hY)
  · simp only [← sigma_mul hσ hy hg, hf y hy]
    exact h.1.2.2.2.2 _ (mul_mem_UJ hy hg)

theorem Expn.add (hσ : IsURepOn (UJset ε) σ) (h : Expn ε σ S v ℓ C f) (h' : Expn ε σ S v' ℓ C f')
    (hS : Words (lieSet ε) S) : Expn ε σ S (fun i => v i + v' i) ℓ C fun y => f y + f' y := by
  refine h.mk' hS (fun i => (smooth (Jm ε) σ).add_mem (h.1.1 i) (h'.1.1 i)) (fun S' hS' => ?_) fun y hy => ?_
  · refine Summable.of_nonneg_of_le (fun i => mul_nonneg (h.1.2.1 i) (sobNorm_nonneg _ _ _)) (fun i => ?_)
      ((h.2 S' hS').add (h'.2 S' hS'))
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (sob_add hσ hS' (h.1.1 i) (h'.1.1 i)) (h.1.2.1 i)
  · simp only [map_add]
    exact (h.1.2.2.2.2 y hy).add (h'.1.2.2.2.2 y hy)

theorem Expn.smul (hσ : IsURepOn (UJset ε) σ) (h : Expn ε σ S v ℓ C f) (hS : Words (lieSet ε) S) (c : ℂ) :
    Expn ε σ S (fun i => c • v i) ℓ C fun y => c * f y := by
  refine h.mk' hS (fun i => (smooth (Jm ε) σ).smul_mem c (h.1.1 i)) (fun S' hS' => ?_) fun y hy => ?_
  · simp only [fun i => sob_smul hσ hS' c (h.1.1 i), mul_left_comm _ ‖c‖]
    exact (h.2 S' hS').mul_left _
  · simp only [map_smul, smul_eq_mul]
    exact (h.1.2.2.2.2 y hy).mul_left c

theorem Expn.summable_norm (h : Expn ε σ S v ℓ C f) : Summable fun i => C i * ‖v i‖ := by
  simpa [sobNorm] using h.2 [[]] (by simp [Words])

theorem Expn.term_le (h : Expn ε σ S v ℓ C f) (c : H) {u : H} (hu : Sm ε σ u) (i : ℕ) :
    ‖⟪c, v i⟫_ℂ * ℓ i u‖ ≤ ‖c‖ * (C i * ‖v i‖) * sobNorm σ S u := by
  rw [norm_mul]
  exact (mul_le_mul (norm_inner_le_norm c (v i)) (h.1.2.2.1 i u hu) (norm_nonneg _) (by positivity)).trans
    (le_of_eq (by ring))

theorem Expn.summable_term (h : Expn ε σ S v ℓ C f) (c : H) {u : H} (hu : Sm ε σ u) :
    Summable fun i => ⟪c, v i⟫_ℂ * ℓ i u :=
  Summable.of_norm_bounded ((h.summable_norm.mul_left _).mul_right _) (h.term_le c hu)

theorem Expn.sobFun (h : Expn ε σ S v ℓ C f) (hS : Words (lieSet ε) S) (c : H) :
    SobFun ε σ fun u => ∑' i, ⟪c, v i⟫_ℂ * ℓ i u := by
  refine ⟨fun x y hx hy => ?_, fun z x _ => ?_, S, ∑' i, ‖c‖ * (C i * ‖v i‖), hS, fun w hw => ?_⟩
  · simp only [map_add, mul_add]
    exact (h.summable_term c hx).tsum_add (h.summable_term c hy)
  · simp only [map_smul, smul_eq_mul, mul_left_comm _ z]
    exact tsum_mul_left
  · exact tsum_of_norm_bounded ((h.summable_norm.mul_left _).hasSum.mul_right _) (h.term_le c hw)

variable [CompleteSpace H]

theorem Expn.avg (hσ : Std ε σ) (h : Expn ε σ S v ℓ C f) (hS : Words (lieSet ε) S)
    (hc : Ctrl (lieSet ε) (UJset ε) σ S) {e : KG ε → ℂ} (he : KFinFun ε e) :
    Expn ε σ S (fun i => kAvg ε σ e (v i)) ℓ C fun y => ∫ k, e k * f (y * toMK k) ∂(muK ε) := by
  obtain ⟨m, a, c, -, ha, -, hQ⟩ := kAvg_finite_rank n ε H σ hσ e he
  have ha' := fun j => hσ.2.2.1 _ (ha j)
  have hs : ∀ w, Sm ε σ (kAvg ε σ e w) := fun w => by
    rw [hQ]
    exact (smooth (Jm ε) σ).sum_mem fun j _ => (smooth (Jm ε) σ).smul_mem _ (ha' j)
  refine h.mk' hS (fun i => hs _) (fun S' hS' => ?_)
    ((GlobalTheory.ExpansionAverage.continuousOn_and_hasSum_kAvg n ε H σ hσ S v ℓ C f hS hc h.1).2 e
      (by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1) hs)
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (h.1.2.1 i) (sobNorm_nonneg _ _ _)) (fun i => ?_)
    (h.summable_norm.mul_right (∑ j, ‖c j‖ * sobNorm σ S' (a j)))
  rw [mul_assoc, hQ]
  refine mul_le_mul_of_nonneg_left ((sob_sum hσ.1 hS' _ _ ha').trans ?_) (h.1.2.1 i)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => (mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _)
    (sobNorm_nonneg _ _ _)).trans (le_of_eq (by ring))

omit [CompleteSpace H] in
theorem mem_kFin_iff {u : H} : u ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ ↔ IsKFin ε σ u := by
  refine ⟨fun h => ?_, fun ⟨W, h1, h2, h3⟩ => (le_sSup (a := W) ⟨h1, h3⟩ : W ≤ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) h2⟩
  exact (sSup_le fun W hW w hw => ⟨W, hW.1, hw, hW.2⟩ : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ ≤ kfin ε σ) h

end Model

section Adelic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.REAL MeasureTheory Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin V.rank → Bool)
  (σ : Mx V.rank → (H →L[ℂ] H)) (P : Mx V.rank)

def res (φ : GA D V → ℂ) (x : GA D V) : Mx V.rank → ℂ := fun y => φ (x * atTau θ V τ (P⁻¹ * y * P))

def avg (e : KG ε → ℂ) (φ : GA D V → ℂ) : GA D V → ℂ :=
  fun x => ∫ k, e k * φ (x * atTau θ V τ (P⁻¹ * toMK k * P)) ∂(muK ε)

def Moves (T : H → H) (φ ψ : GA D V → ℂ) : Prop :=
  ∀ x S v ℓ C, Words (lieSet ε) S → Ctrl (lieSet ε) (UJset ε) σ S → Expn ε σ S v ℓ C (res θ V τ P φ x) →
    Expn ε σ S (fun i => T (v i)) ℓ C (res θ V τ P ψ x)

def Acts (T : H → H) : Prop :=
  ∀ φ, IsAutFunSm θ V φ → ∃ ψ, IsAutFunSm θ V ψ ∧ Moves θ V τ ε σ P T φ ψ

variable {θ V τ ε σ P}

theorem at_mul (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ) {a b : Mx V.rank}
    (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) :
    atTau θ V τ (P⁻¹ * (a * b) * P) = atTau θ V τ (P⁻¹ * a * P) * atTau θ V τ (P⁻¹ * b * P) := by
  rw [GrowthAtPlace.conj_mul hP, atTau_mul hθ V τ (conj_inv_mem hP hJ ha) (conj_inv_mem hP hJ hb)]

theorem res_conj (hP : IsUnit P) (φ : GA D V → ℂ) (x : GA D V) (g : Mx V.rank) :
    res θ V τ P φ x (P * g * P⁻¹) = φ (x * atTau θ V τ g) := by
  have h : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hP)
  have e : P⁻¹ * (P * g * P⁻¹) * P = g := by
    calc _ = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [h, one_mul, mul_one]
  rw [res, e]

theorem res_one (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (φ : GA D V → ℂ) (x : GA D V) :
    res θ V τ P φ x 1 = φ x := by
  rw [res, mul_one, Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hP), atTau_one hθ, mul_one]

theorem continuous_conjK : Continuous fun k : KG ε => P⁻¹ * toMK k * P :=
  (continuous_const.matrix_mul (continuous_toMK ε)).matrix_mul continuous_const

variable [CompleteSpace H]

theorem moves_avg (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ) (hσ : Std ε σ)
    {e : KG ε → ℂ} (he : KFinFun ε e) (φ : GA D V → ℂ) :
    Moves θ V τ ε σ P (kAvg ε σ e) φ (avg θ V τ ε P e φ) := by
  intro x S v ℓ C hS hc h
  have h1 := h.avg hσ hS hc he
  refine h1.mk' hS h1.1.1 h1.2 fun y hy => ?_
  have h2 := h1.1.2.2.2.2 y hy
  simp only [res, avg, at_mul hθ hP hJ hy (K_le_UJ (toMK_mem_K _)), ← mul_assoc x] at h2 ⊢
  exact h2

theorem exists_rank_one (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ) (hσ : Std ε σ)
    {e : KG ε → ℂ} (he : KFinFun ε e) :
    ∃ (m : ℕ) (a c : Fin m → H), (∀ j, IsKFin ε σ (a j)) ∧ (∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j) ∧
      ∀ j u, IsKFin ε σ u → Acts θ V τ ε σ P fun w => ⟪c j, w⟫_ℂ • u := by
  have hsmul : ∀ (c : ℂ) (T : H → H), Acts θ V τ ε σ P T → Acts θ V τ ε σ P fun w => c • T w := fun c T hT φ hφ => by
    obtain ⟨ψ, h1, h2⟩ := hT φ hφ
    exact ⟨c • ψ, isAutFunSm_smul c h1, fun x S v ℓ C hS hc h => (h2 x S v ℓ C hS hc h).smul hσ.1 hS c⟩
  have htr : ∀ g ∈ UJset ε, Acts θ V τ ε σ P (σ g) := fun g hg φ hφ =>
    ⟨_, GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V φ hφ τ _ (conj_inv_mem hP hJ hg),
      fun x S v ℓ C hS _ h => h.translate hσ.1 hS hg fun y hy => by
        simp only [res, rTr, at_mul hθ hP hJ hy hg, mul_assoc x]⟩
  refine GlobalTheory.T.rankOneOperator_mem_of_translation_average_closed _ ε H σ hσ (Acts θ V τ ε σ P) htr (fun T T' hT hT' => ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩) hsmul
    (fun e he φ hφ => ⟨_, GlobalTheory.T.isSmoothAutomorphicFunction_compactFamily_average D θ hθ V τ (KG ε) (muK ε) _ continuous_conjK
      (fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))) e
      (by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1) φ hφ, moves_avg hθ hP hJ hσ he φ⟩) ?_ e he
  · obtain ⟨ψ, h1, h2⟩ := hT φ hφ
    obtain ⟨ψ', h1', h2'⟩ := hT' φ hφ
    exact ⟨ψ + ψ', isAutFunSm_add h1 h1', fun x S v ℓ C hS hc h =>
      (h2 x S v ℓ C hS hc h).add hσ.1 (h2' x S v ℓ C hS hc h) hS⟩
  · obtain ⟨ψ', h1', h2'⟩ := hT' φ hφ
    obtain ⟨ψ, h1, h2⟩ := hT ψ' h1'
    exact ⟨ψ, h1, fun x S v ℓ C hS hc h => h2 x S _ ℓ C hS hc (h2' x S v ℓ C hS hc h)⟩
  · simpa using hsmul 0 _ (htr 1 (one_mem_UJ ε))

theorem exists_gkMap (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ) (hσ : Std ε σ)
    {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) {S : GA D V → List (List (Mx V.rank))} {v : GA D V → ℕ → H}
    {ℓ : GA D V → ℕ → (H →ₗ[ℂ] ℂ)} {C : GA D V → ℕ → ℝ} (hS : ∀ x, Words (lieSet ε) (S x))
    (hc : ∀ x, Ctrl (lieSet ε) (UJset ε) σ (S x)) (h : ∀ x, Expn ε σ (S x) (v x) (ℓ x) (C x) (res θ V τ P φ x))
    {c : H} (hA : ∀ u, IsKFin ε σ u → Acts θ V τ ε σ P fun w => ⟪c, w⟫_ℂ • u) :
    ∃ T : kFin ε σ →ₗ[ℂ] (GA D V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T ∧
      ∀ u x, T u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u := by
  have hb := fun x => (h x).sobFun (hS x) c
  have hsm : ∀ u : kFin ε σ, Sm ε σ u := fun u => hσ.2.2.1 _ (mem_kFin_iff.1 u.2)
  let T : kFin ε σ →ₗ[ℂ] (GA D V → ℂ) :=
    { toFun := fun u x => ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u
      map_add' := fun a b => funext fun x => (hb x).1 _ _ (hsm a) (hsm b)
      map_smul' := fun z a => funext fun x => (hb x).2.1 z _ (hsm a) }
  have key : ∀ u : kFin ε σ, IsAutFunSm θ V (T u) ∧
      ∀ x, ∀ y ∈ UJset ε, res θ V τ P (T u) x y = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i (σ y u) := fun u => by
    obtain ⟨ψ, h1, h2⟩ := hA u (mem_kFin_iff.1 u.2) φ hφ
    have h3 : ∀ x, ∀ y ∈ UJset ε, res θ V τ P ψ x y = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i (σ y u) := fun x y hy => by
      have := (h2 x _ _ _ _ (hS x) (hc x) (h x)).1.2.2.2.2 y hy
      simp only [map_smul, smul_eq_mul] at this
      exact this.tsum_eq.symm
    have e : T u = ψ := funext fun x => by
      have := h3 x 1 (one_mem_UJ ε)
      rw [res_one hθ hP, sigma_one hσ.1] at this
      exact this.symm
    rw [e]
    exact ⟨h1, h3⟩
  refine ⟨T, ⟨fun u => (key u).1, fun g _ hg a b hab => funext fun x => ?_, fun X hX a b hab => funext fun x => ?_⟩,
    fun _ _ => rfl⟩
  · rw [rTr, ← res_conj hP (T a) x g, (key a).2 x _ (K_le_UJ hg), ← hab]
    rfl
  · have hd := (isUnit_iff_isUnit_det _).1 hP
    have hY : P * X * P⁻¹ ∈ lieSet ε := by
      refine Transport.conj_lie (G := gramAt D V τ) (Matrix.nonsing_inv_mul _ hd) ?_ hX
      rw [← hJ]
      calc _ = (P * P⁻¹)ᴴ * Jm ε * (P * P⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp
    simp only [← Transport.exp_smul_conj hP] at hab
    have e : (b : H) = dRep σ (P * X * P⁻¹) a := hab.deriv.symm
    have h1 := (hσ.hasDerivAt_sobFun (hb x) (hsm a) hY).deriv
    rw [← e] at h1
    refine h1.symm.trans ?_
    unfold Rder oneP
    congr 1
    funext t
    rw [← res_conj hP (T a) x, ← Transport.exp_smul_conj hP, (key a).2 x _ (exp_mem_UJ hY t)]

end Adelic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.REAL MeasureTheory GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes in
open scoped InnerProductSpace in

theorem hasTypeAt_of_isTypeAt : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau) (S : SPar) (φ : GA D V → ℂ),
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.DiscreteSeriesUpqUnique → GlobalTheory.Published.HarishChandraModules →
    GlobalTheory.Published.CasselmanWallach → IsInfFam (D := D) θ → V.SigOK →
    GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 S → IsAutFunSm θ V φ →
    IsTypeAt θ V τ S φ → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S φ := by
  intro D θ V τ S φ _ _ hHC _ hθ _ hS hφ ⟨H, i1, i2, σ, lam, ε, P, hE, hD, hP, hJ, hx⟩ K hK δ hδ
  haveI : CompleteSpace H := hD.1
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hσ : Std ε σ := std_of_isDS hHC hD
  have hlam : Formalism.QuantumDeterminants.IsHCParam lam := by
    obtain ⟨l, e, h1, h2, -⟩ := hS
    rwa [(GlobalTheory.SignedParTest.isEnum_unique hE h1).1]
  have hx' : ∀ x, HasTypeAll (lieSet ε) (UJset ε) σ (res θ V τ P φ x) := fun x =>
    hasTypeAll_transport _ H H _ σ (gramAt D V τ) (Jm ε) P (isUnit_gram hP hJ) hP hJ (LinearIsometryEquiv.refl ℂ H)
      (fun _ _ _ => rfl) (fun g => φ (x * atTau θ V τ g)) (hasTypeAll_iff.2 (hx x))
  choose W hW hc v ℓ C h using hx'
  have hk : Continuous fun k : KG ε => atTau θ V τ (P⁻¹ * toMK k * P) :=
    (continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
      fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  obtain ⟨e, he, hap⟩ := GlobalTheory.T.exists_compactFinite_approxIdentity _ ε (GA D V) (fun x k => φ (x * atTau θ V τ (P⁻¹ * toMK k * P)))
    (hφ.cont.comp (continuous_fst.mul (hk.comp continuous_snd))) K hK δ hδ
  obtain ⟨m, a, c, ha, hQ, hA⟩ := exists_rank_one hθ hP hJ hσ he
  choose T hT hTv using fun j => exists_gkMap hθ hP hJ hσ hφ hW hc h (hA j)
  refine ⟨∑ j, T j ⟨a j, mem_kFin_iff.2 (ha j)⟩, Submodule.sum_mem _ fun j _ =>
    (le_sSup (a := LinearMap.range (T j)) ⟨H, _, _, σ, lam, ε, P, T j, hE, hlam, hD, hP, hJ, hT j, rfl⟩ :
      _ ≤ finPartOfType θ V τ S) ⟨_, rfl⟩, fun x hxK => ?_⟩
  have h1 := (moves_avg hθ hP hJ hσ he φ x _ _ _ _ (hW x) (hc x) (h x)).1.2.2.2.2 1 (one_mem_UJ ε)
  simp only [res_one hθ hP, sigma_one hσ.1, hQ, map_sum, map_smul, smul_eq_mul] at h1
  have h2 := h1.unique (hasSum_sum fun j _ => (Expn.summable_term (h x) (c j) (hσ.2.2.1 _ (ha j))).hasSum)
  have h3 := hap x hxK
  have h4 : φ (x * atTau θ V τ (P⁻¹ * toMK (1 : KG ε) * P)) = φ x := res_one hθ hP φ x
  simp only [Finset.sum_apply, hTv]
  rw [← h2, ← h4]
  exact h3

end GlobalTheory.SeriesToClosure

end
