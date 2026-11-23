import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneConstantTermGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneJacobianIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLineDerivativeCommutatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteFunctionsCompactBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneStabilizerActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetLineDecompositionStatement
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.CuspTransfer.Growth

open GlobalTheory.SiegelSet GlobalTheory.UAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isSm_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) {f : ι → GAd σ J → ℂ} (hf : ∀ i, IsSm σ J (f i)) :
    IsSm σ J (∑ i ∈ s, c i • f i) :=
  (GlobalTheory.LeviHC.SmG σ J).sum_mem fun i _ => (GlobalTheory.LeviHC.SmG σ J).smul_mem _ (hf i)

theorem foldr_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) {f : ι → GAd σ J → ℂ} (hf : ∀ i, IsSm σ J (f i))
    {l : List (ℝ → GAd σ J)} (hl : ∀ γ ∈ l, IsRealLine σ J γ) :
    l.foldr lineDer (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • l.foldr lineDer (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using foldr_smul l 0 (0 : GAd σ J → ℂ)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, foldr_add hl (isSm_smul _ (hf i)) (isSm_sum s c hf), ih, foldr_smul]

theorem line_hom (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    γ 0 = 1 ∧ (∀ s t, γ (s + t) = γ s * γ t) ∧ ∀ t, γ t ∈ infPts σ J := by
  obtain ⟨w, τ, Z, -, hy⟩ := hγ
  choose y e1 e2 using hy
  have inj := GlobalTheory.LeviHC.LineLie.archMat_injective (J := J) h τ
  refine ⟨?_, fun s t => ?_, fun t => ?_⟩
  · rw [e1, show y 0 = 1 from inj (by rw [e2, zero_smul, NormedSpace.exp_zero, map_one]), map_one]
  · rw [e1, e1, e1, ← map_mul, show y (s + t) = y s * y t from inj (by
      rw [map_mul, e2, e2, e2, add_smul, Matrix.exp_add_of_commute]
      exact ((Commute.refl Z).smul_left s).smul_right t)]
  · rw [e1]; exact mem_infPts.2 (projFin_embArch _ _ _ _)

theorem differentiableAt_of_hom {e : ℝ → ℂ} (hc : Continuous e) (h0 : e 0 = 1) (hm : ∀ s t, e (s + t) = e s * e t) :
    DifferentiableAt ℝ e 0 := by
  obtain ⟨Y, hY⟩ := GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter (n := Unit) (fun t => Matrix.diagonal fun _ => e t)
    (Continuous.matrix_diagonal (continuous_pi fun _ => hc)) (by simp [h0]) (fun s t => by simp [hm])
  have e1 : e = fun t : ℝ => Complex.exp (t * Y () ()) := funext fun t => by
    have h1 : t • Y = Matrix.diagonal fun _ => (t : ℂ) * Y () () := by ext ⟨⟩ ⟨⟩; simp
    have h2 := congrFun (congrFun (hY t) ()) ()
    rw [h1, Matrix.exp_diagonal] at h2
    simpa [Pi.exp_def, Complex.exp_eq_exp_ℂ] using h2
  rw [e1]
  fun_prop

theorem abstract_bound (h : IsCMExt F E σ) (hJ : IsHermND σ J) (P K : Subgroup (GAd σ J)) (S : Set (GAd σ J))
    (hS : ∀ k ∈ S, ∀ k' ∈ K, k * k' ∈ S) (w : P → ℝ) (U : (P → ℂ) → Prop) (A : (GAd σ J → ℂ) → Prop)
    (U1 : ∀ φ, U φ → ∃ C : ℝ, ∀ p, ‖φ p‖ ≤ C * w p)
    (U2 : ∀ φ, U φ → ∀ β, IsRealLine σ J β → ∀ hβ : ∀ s, β s ∈ P, ∃ φ', U φ' ∧ ∀ p,
      HasDerivAt (fun s => φ (p * ⟨β s, hβ s⟩)) (φ' p) 0)
    (A1 : ∀ a, A a → ∃ C : ℝ, ∀ k ∈ S, ‖a k‖ ≤ C)
    (A2 : ∀ a, A a → ∀ ζ, IsRealLine σ J ζ → (∀ s, ζ s ∈ K) → ∃ a', A a' ∧ ∀ k ∈ S,
      HasDerivAt (fun s => a (k * ζ s)) (a' k) 0)
    (hdec : ∀ γ : ℝ → GAd σ J, IsRealLine σ J γ →
      ∃ (e e' : ℕ) (β : Fin e → ℝ → GAd σ J) (ζ : Fin e' → ℝ → GAd σ J) (C : ℝ),
        (∀ j, IsRealLine σ J (β j) ∧ ∀ s, β j s ∈ P) ∧ (∀ j, IsRealLine σ J (ζ j) ∧ ∀ s, ζ j s ∈ K) ∧
        ∀ k ∈ S, ∃ (c : Fin e → ℂ) (c' : Fin e' → ℂ), (∀ j, ‖c j‖ ≤ C) ∧ (∀ j, ‖c' j‖ ≤ C) ∧
          ∀ f, IsSm σ J f → lineDer γ f =
            ∑ j, c j • lineDer (fun s => k⁻¹ * β j s * k) f + ∑ j, c' j • lineDer (ζ j) f)
    (d : ℕ) : ∀ (m : ℕ) (Φ : GAd σ J → ℂ), IsSm σ J Φ →
      (∃ (φ : Fin d → P → ℂ) (a : Fin d → GAd σ J → ℂ), (∀ i, U (φ i)) ∧ (∀ i, A (a i)) ∧
        ∀ p : P, ∀ k ∈ S, Φ (p * k) = ∑ i, φ i p * a i k) →
      ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → l.length = m →
      ∀ lP : List (ℝ → GAd σ J), (∀ β ∈ lP, IsRealLine σ J β ∧ ∀ s, β s ∈ P) →
      ∃ C : ℝ, ∀ p : P, ∀ k ∈ S,
        ‖(lP.map fun β s => k⁻¹ * β s * k).foldr lineDer (l.foldr lineDer Φ) (p * k)‖ ≤ C * w p := by
  have hconj : ∀ (lP : List (ℝ → GAd σ J)), (∀ β ∈ lP, IsRealLine σ J β ∧ ∀ s, β s ∈ P) → ∀ k,
      ∀ γ ∈ lP.map fun β s => k⁻¹ * β s * k, IsRealLine σ J γ := fun lP hlP k γ hγ => by
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hγ
    exact GlobalTheory.ThK.DescB.GenGrowth.isRealLine_conj h (hlP β hβ).1 k
  intro m
  induction m with
  | zero =>
    rintro Φ - ⟨φ, a, hφ, ha, e⟩ l - hl lP hlP
    obtain rfl := List.length_eq_zero_iff.1 hl
    have key : ∃ φ' : Fin d → P → ℂ, (∀ i, U (φ' i)) ∧ ∀ p : P, ∀ k ∈ S,
        (lP.map fun β s => k⁻¹ * β s * k).foldr lineDer Φ (p * k) = ∑ i, φ' i p * a i k := by
      induction lP with
      | nil => exact ⟨φ, hφ, e⟩
      | cons β lP ih =>
        obtain ⟨φ', h1, h2⟩ := ih fun γ hγ => hlP γ (List.mem_cons_of_mem _ hγ)
        obtain ⟨hβ, hβP⟩ := hlP β List.mem_cons_self
        choose φ'' h3 h4 using fun i => U2 _ (h1 i) β hβ hβP
        refine ⟨φ'', h3, fun p k hk => ?_⟩
        rw [List.map_cons, List.foldr_cons, lineDer]
        have e2 : (fun s => (lP.map fun β s => k⁻¹ * β s * k).foldr lineDer Φ (p * k * (k⁻¹ * β s * k))) =
            fun s => ∑ i, φ' i (p * ⟨β s, hβP s⟩) * a i k := funext fun s => by
          rw [← h2 _ k hk]; simp [mul_assoc]
        rw [e2]
        exact (HasDerivAt.fun_sum fun i _ => (h4 i p).mul_const (a i k)).deriv
    obtain ⟨φ', h1, h2⟩ := key
    choose C hC using fun i => U1 _ (h1 i)
    choose B hB using fun i => A1 _ (ha i)
    refine ⟨∑ i, C i * B i, fun p k hk => ?_⟩
    rw [List.foldr_nil, h2 p k hk, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, mul_right_comm]
    exact mul_le_mul (hC i p) (hB i k hk) (norm_nonneg _) ((norm_nonneg _).trans (hC i p))
  | succ m ih =>
    rintro Φ hΦ hcl l hl hlen lP hlP
    obtain ⟨γ, l, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    have hl' : ∀ γ ∈ l, IsRealLine σ J γ := fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
    have hlen' : l.length = m := by simpa using hlen
    have hK : ∀ ζ, IsRealLine σ J ζ → (∀ s, ζ s ∈ K) → ∀ l₂ l₁ : List (ℝ → GAd σ J), (∀ γ ∈ l₁, IsRealLine σ J γ) →
        (∀ γ ∈ l₂, IsRealLine σ J γ) → l₁.length + l₂.length = m → ∃ C : ℝ, ∀ p : P, ∀ k ∈ S,
          ‖(lP.map fun β s => k⁻¹ * β s * k).foldr lineDer (l₁.foldr lineDer (lineDer ζ (l₂.foldr lineDer Φ))) (p * k)‖ ≤
            C * w p := by
      intro ζ hζ hζK l₂
      induction l₂ with
      | nil =>
        intro l₁ h1 _ h3
        obtain ⟨φ, a, hφ, ha, e⟩ := hcl
        choose a' h4 h5 using fun i => A2 _ (ha i) ζ hζ hζK
        refine ih _ (isSm_lineDer hΦ hζ) ⟨φ, a', hφ, h4, fun p k hk => ?_⟩ l₁ h1 (by simpa using h3) lP hlP
        have e2 : (fun s => Φ (p * k * ζ s)) = fun s => ∑ i, φ i p * a i (k * ζ s) := funext fun s => by
          rw [mul_assoc, e p _ (hS k hk _ (hζK s))]
        rw [lineDer, e2]
        exact (HasDerivAt.fun_sum fun i _ => (h5 i k hk).const_mul (φ i p)).deriv
      | cons δ l₂ ih₂ =>
        intro l₁ h1 h2 h3
        have hδ := h2 δ List.mem_cons_self
        have h2' : ∀ γ ∈ l₂, IsRealLine σ J γ := fun γ hγ => h2 γ (List.mem_cons_of_mem _ hγ)
        obtain ⟨ε, hε, hbr⟩ := GlobalTheory.T.siegel_line_derivative_commutator F E σ h n J hJ ζ δ hζ hδ
        obtain ⟨C₁, hC₁⟩ := ih₂ (l₁ ++ [δ]) (by
          intro γ hγ
          rcases List.mem_append.1 hγ with h | h
          · exact h1 γ h
          · rw [List.mem_singleton.1 h]; exact hδ) h2' (by simp at h3 ⊢; omega)
        obtain ⟨C₂, hC₂⟩ := ih Φ hΦ hcl (l₁ ++ ε :: l₂) (by
          intro γ hγ
          rcases List.mem_append.1 hγ with h | h
          · exact h1 γ h
          · rcases List.mem_cons.1 h with h | h
            · rw [h]; exact hε
            · exact h2' γ h) (by simpa using h3) lP hlP
        refine ⟨C₁ + C₂, fun p k hk => ?_⟩
        have hR := isSm_foldr h2' hΦ
        have s1 := isSm_lineDer (isSm_lineDer hR hζ) hδ
        have s2 := isSm_lineDer hR hε
        rw [List.foldr_cons, hbr _ hR, foldr_add h1 s1 s2, foldr_add (hconj lP hlP k) (isSm_foldr h1 s1) (isSm_foldr h1 s2),
          add_mul]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using hC₁ p k hk
        · simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using hC₂ p k hk
    obtain ⟨e, e', β, ζ, C, hβ, hζ, hd⟩ := hdec γ (hl γ List.mem_cons_self)
    choose C₁ hC₁ using fun j => ih Φ hΦ hcl l hl' hlen' (lP ++ [β j]) (by
      intro γ hγ
      rcases List.mem_append.1 hγ with h | h
      · exact hlP γ h
      · rw [List.mem_singleton.1 h]; exact hβ j)
    choose C₂ hC₂ using fun j => hK (ζ j) (hζ j).1 (hζ j).2 l [] (by simp) hl' (by simpa using hlen')
    refine ⟨∑ j, C * C₁ j + ∑ j, C * C₂ j, fun p k hk => ?_⟩
    obtain ⟨c, c', hc, hc', hcc⟩ := hd k hk
    have hR := isSm_foldr hl' hΦ
    have s1 : ∀ j, IsSm σ J (lineDer (fun s => k⁻¹ * β j s * k) (l.foldr lineDer Φ)) := fun j =>
      isSm_lineDer hR (GlobalTheory.ThK.DescB.GenGrowth.isRealLine_conj h (hβ j).1 k)
    have s2 : ∀ j, IsSm σ J (lineDer (ζ j) (l.foldr lineDer Φ)) := fun j => isSm_lineDer hR (hζ j).1
    rw [List.foldr_cons, hcc _ hR, foldr_add (hconj lP hlP k) (isSm_sum _ _ s1) (isSm_sum _ _ s2),
      foldr_sum _ _ s1 (hconj lP hlP k), foldr_sum _ _ s2 (hconj lP hlP k), add_mul, Finset.sum_mul, Finset.sum_mul,
      Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)))
    · rw [Pi.smul_apply, norm_smul, mul_assoc]
      refine mul_le_mul (hc j) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hc j))
      simpa only [List.map_append, List.map_cons, List.map_nil, List.foldr_append, List.foldr_cons, List.foldr_nil]
        using hC₁ j p k hk
    · rw [Pi.smul_apply, norm_smul, mul_assoc]
      exact mul_le_mul (hc' j) (hC₂ j p k hk) (norm_nonneg _) ((norm_nonneg _).trans (hc' j))

theorem datum_deriv (h : IsCMExt F E σ) {n₁ : ℕ} {J₁ : Matrix (Fin n₁) (Fin n₁) E} {P : Subgroup (GAd σ J)}
    (π : P →* GAd σ J₁) (hπ : Continuous π) (hπi : ∀ p : P, p.1 ∈ infPts σ J → π p ∈ infPts σ J₁)
    (η : P → ℂ) (hη : Continuous η) (hη1 : η 1 = 1) (hηm : ∀ p q, η (p * q) = η p * η q) (w : GAd σ J₁ → ℝ)
    {f : GAd σ J₁ → ℂ} (hf : IsSm σ J₁ f)
    (hg : ∀ l : List (ℝ → GAd σ J₁), (∀ γ ∈ l, IsRealLine σ J₁ γ) → ∃ C : ℝ, ∀ y, ‖l.foldr lineDer f y‖ ≤ C * w y)
    {β : ℝ → GAd σ J} (hβ : IsRealLine σ J β) (hP : ∀ s, β s ∈ P) :
    ∃ f' : GAd σ J₁ → ℂ, IsSm σ J₁ f' ∧
      (∀ l : List (ℝ → GAd σ J₁), (∀ γ ∈ l, IsRealLine σ J₁ γ) → ∃ C : ℝ, ∀ y, ‖l.foldr lineDer f' y‖ ≤ C * w y) ∧
      ∀ p : P, HasDerivAt (fun s => η (p * ⟨β s, hP s⟩) * f (π (p * ⟨β s, hP s⟩))) (η p * f' (π p)) 0 := by
  obtain ⟨b0, bm, bi⟩ := line_hom h hβ
  let b : ℝ → P := fun s => ⟨β s, hP s⟩
  have hb : Continuous b := (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J β hβ).subtype_mk _
  have c0 : b 0 = 1 := Subtype.ext b0
  have cm : ∀ s t, b (s + t) = b s * b t := fun s t => Subtype.ext (bm s t)
  obtain ⟨r, δ, hδ, hd⟩ := GlobalTheory.LineDerSum.exists_lines_of_infPts h J₁ (fun s => π (b s)) (hπ.comp hb)
    (by rw [c0, map_one]) (fun s t => by rw [cm, map_mul]) fun t => hπi _ (bi t)
  have he := (differentiableAt_of_hom (e := fun s => η (b s)) (hη.comp hb) (by rw [c0, hη1])
    fun s t => by rw [cm, hηm]).hasDerivAt
  set c := deriv (fun s => η (b s)) 0
  have s1 : ∀ i, IsSm σ J₁ (lineDer (δ i) f) := fun i => isSm_lineDer hf (hδ i)
  refine ⟨c • f + ∑ i, (1 : ℂ) • lineDer (δ i) f, isSm_add (isSm_smul _ hf) (isSm_sum _ _ s1), fun l hl => ?_, fun p => ?_⟩
  · obtain ⟨C, hC⟩ := hg l hl
    choose D hD using fun i => hg (l ++ [δ i]) (by
      intro γ hγ
      rcases List.mem_append.1 hγ with h | h
      · exact hl γ h
      · rw [List.mem_singleton.1 h]; exact hδ i)
    refine ⟨‖c‖ * C + ∑ i, D i, fun y => ?_⟩
    rw [foldr_add hl (isSm_smul _ hf) (isSm_sum _ _ s1), foldr_smul, foldr_sum _ _ s1 hl, add_mul, Finset.sum_mul,
      Pi.add_apply, Finset.sum_apply]
    refine (norm_add_le _ _).trans (add_le_add ?_ ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)))
    · rw [Pi.smul_apply, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)
    · simpa only [one_smul, List.foldr_append, List.foldr_cons, List.foldr_nil] using hD i y
  · have h1 := (he.mul (hd f hf (π p))).const_mul (η p)
    have e1 : (fun s => η (p * ⟨β s, hP s⟩) * f (π (p * ⟨β s, hP s⟩))) =
        fun s => η p * ((fun s => η (b s)) * fun s => f (π p * π (b s))) s := funext fun s => by
      simp only [hηm, map_mul, Pi.mul_apply, mul_assoc, b]
    rw [e1]
    refine h1.congr_deriv ?_
    simp only [c0, hη1, map_one, mul_one, one_mul, one_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]

theorem growth_of_ind : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ χ : Chr F E, (∀ t : Eˣ, χ (Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom t) = 1) → Continuous (fun t : (AE F E)ˣ => (χ t : ℂ)) →
      ∀ K₁ : Subgroup (GAd σ (c₀ • W₁.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W₁.J.map σ) K₁ →
      ∀ K' : Subgroup (GAd σ (c₀ • W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W.J.map σ) K' →
      ∀ (Kc : Set (GAd σ (c₀ • W.J.map σ))) (d : ℕ) (ψs : Fin d → GAd σ (c₀ • W₁.J.map σ) → ℂ) (a : Fin d → GAd σ (c₀ • W.J.map σ) → ℂ) (Ψ : GAd σ (c₀ • W.J.map σ) → ℂ),
      GlobalTheory.ThK.CuspTransfer.IsInd hσ W W₁ H hc₀ X' M χ Kc ψs a Ψ →
      (∀ i, GlobalTheory.StdPar.IsCuspOn σ (c₀ • W₁.J.map σ) Xf Yf S' K₁ (ψs i)) →
      (IsCompact Kc ∧ (1 : GAd σ (c₀ • W.J.map σ)) ∈ Kc ∧ ∀ k ∈ Kc, ∀ k' ∈ K', k * k' ∈ Kc) → (∀ i, ContinuousOn (a i) Kc) → (∀ i, ∀ k ∈ Kc, ∀ (e : ℕ) (γ : Fin e → ℝ → GAd σ (c₀ • W.J.map σ)), (∀ j, GlobalTheory.SiegelSet.IsRealLine σ (c₀ • W.J.map σ) (γ j)) → (∀ j s, γ j s ∈ K') →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin e → ℝ => a i (k * (List.ofFn fun j => γ j (t j)).prod)) → (∃ (e : ℕ) (b : Fin e → GAd σ (c₀ • W.J.map σ) → ℂ), (∀ j, ContinuousOn (b j) Kc) ∧ (∀ i, ∃ c : Fin e → ℂ, ∀ k ∈ Kc, a i k = ∑ j, c j * b j k) ∧
        ∀ j, ∀ k' ∈ K', ∃ c : Fin e → ℂ, ∀ k ∈ Kc, b j (k * k') = ∑ l, c l * b l k) → ∃ N : ℕ, ∀ l : List (ℝ → GAd σ (c₀ • W.J.map σ)), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine σ (c₀ • W.J.map σ) γ) →
      ∃ C : ℝ, ∀ g, ‖l.foldr GlobalTheory.SiegelSet.lineDer Ψ g‖ ≤ C * (height σ (c₀ • W.J.map σ) g : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ hCM hσ n n₁ W W₁ H hJ hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M hMc hM hMr r Xf Yf hWf X' Y' hW' hx0 hy0 hsucc
    S' χ hχ hχc K₁ hK₁ K' hK' Kc d ψs a Ψ hI hψs c1 c3 c4 c5
  have hsm := GlobalTheory.T.skew_plane_jacobian_identity F E σ hCM hσ n n₁ W W₁ H hJ hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M hMc hM hMr r Xf Yf hWf X' Y' hW'
    hx0 hy0 hsucc S' χ hχ hχc K₁ hK₁ K' hK' Kc d ψs a Ψ hI hψs c1 c3 c4
  obtain ⟨P, π, T, hP, hdec, hmem, hπ, hT, A, hA, hmat⟩ := GlobalTheory.T.skew_plane_stabilizer_action F E σ hCM hσ n n₁ W W₁ H hJ hn hxx hyy hxy hι hJ₁ c₀ hc₀
    hN₁ hN M hM r X' Y' hW' hx0
  obtain ⟨e, b, hb, hab, hbb⟩ := c5
  choose N hNg using fun i => (hψs i).1.growth
  have hx : hE σ (c₀ • W.J.map σ) H.x H.x = 0 := by
    have h1 := congrFun (congrFun hW'.xx 0) 0
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hx0, Finset.sum_mul] at h1
    rw [Finset.sum_comm] at h1
    exact h1
  have hπi : ∀ p : P, p.1 ∈ infPts σ _ → π p ∈ infPts σ _ := fun p hp => mem_infPts_iff_forall.2 fun v => by
    have h1 : (matHom _ σ _ p.1).1.map (compFin F E v) = 1 := congrArg (fun z => z.1.1) (mem_infPts_iff_forall.1 hp v)
    refine Subtype.ext (Units.ext ?_)
    show (matHom _ σ _ (π p)).1.map (compFin F E v) = 1
    rw [hmat, Matrix.map_mul, Matrix.map_mul, h1, Matrix.mul_one, ← Matrix.map_mul, adMat, adMat, ← Matrix.map_mul, hA,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨K₀, hK₀⟩ := GlobalTheory.EmbHeight.exists_heightGL_aff_le F 0 (adMat F A) (adMat F H.ι)
  have hht : ∀ p : P, height σ _ (π p) ≤ K₀ * height σ _ p.1 := fun p =>
    hK₀ _ _ (by rw [zero_add]; exact hmat p) (by rw [zero_add, ← map_inv, ← map_inv, ← map_inv]; exact hmat p⁻¹)
  obtain ⟨B, hB⟩ := height_bddAbove_of_isCompact σ _ c1.1
  let N₀ := Finset.univ.sup N
  let w : GAd σ (c₀ • W₁.J.map σ) → ℝ := fun y => (height σ _ y : ℝ) ^ N₀
  let η : P → ℂ := fun p => (χ (T p) : ℂ)
  refine ⟨N₀, fun l hl => ?_⟩
  obtain ⟨C, hC⟩ := abstract_bound hCM hN P K' Kc c1.2.2 (fun p => w (π p))
    (fun φ => ∃ f, IsSm σ _ f ∧ (∀ l : List (ℝ → GAd σ (c₀ • W₁.J.map σ)), (∀ γ ∈ l, IsRealLine σ _ γ) →
      ∃ C : ℝ, ∀ y, ‖l.foldr lineDer f y‖ ≤ C * w y) ∧ φ = fun p => η p * f (π p))
    (fun a' => ∃ i, ∃ l : List (ℝ → GAd σ (c₀ • W.J.map σ)), (∀ ζ ∈ l, IsRealLine σ _ ζ ∧ ∀ s, ζ s ∈ K') ∧
      a' = l.foldr lineDer (a i))
    (by
      rintro _ ⟨f, -, hf, rfl⟩
      obtain ⟨C, hC⟩ := hf [] (by simp)
      exact ⟨C, fun p => by simpa only [η, norm_mul, Circle.norm_coe, one_mul, List.foldr_nil] using hC (π p)⟩)
    (by
      rintro _ ⟨f, hf, hg, rfl⟩ β hβ hβP
      obtain ⟨f', h1, h2, h3⟩ := datum_deriv hCM π hπ hπi η (hχc.comp hT) (by simp [η]) (fun p q => by simp [η]) w hf hg hβ hβP
      exact ⟨_, ⟨f', h1, h2, rfl⟩, h3⟩)
    (by
      rintro _ ⟨i, l, hl, rfl⟩
      exact (GlobalTheory.T.k_finite_functions_compact_bound F E σ hCM n _ K' Kc c1.1 c1.2.2 e b hb hbb (a i) (hab i) (c4 i) l hl).1)
    (by
      rintro _ ⟨i, l, hl, rfl⟩ ζ hζ hζK
      refine ⟨_, ⟨i, ζ :: l, fun γ hγ => ?_, rfl⟩, fun k hk =>
        ((GlobalTheory.T.k_finite_functions_compact_bound F E σ hCM n _ K' Kc c1.1 c1.2.2 e b hb hbb (a i) (hab i) (c4 i) l hl).2 ζ hζ hζK k hk).hasDerivAt⟩
      rcases List.mem_cons.1 hγ with h | h
      · rw [h]; exact ⟨hζ, hζK⟩
      · exact hl γ h)
    (fun γ hγ => by
      obtain ⟨e, e', β, ζ, C, h1, h2, h3⟩ := GlobalTheory.T.siegel_set_line_decomposition F E σ hCM n _ hN H.x hx K' hK' Kc c1.1 γ hγ
      exact ⟨e, e', β, ζ, C, fun j => ⟨(h1 j).1, fun s => (hP _).2 ((h1 j).2 s)⟩, h2, h3⟩)
    d l.length Ψ hsm
    ⟨fun i p => η p * ψs i (π p), a, fun i => ⟨ψs i, (hψs i).1.smooth, fun l hl => by
        obtain ⟨C, hC⟩ := hNg i l hl
        refine ⟨max C 0, fun y => (hC y).trans ?_⟩
        have h1 : (1 : ℝ) ≤ height σ _ y := by exact_mod_cast one_le_height σ _ y
        exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ h1 (Finset.le_sup (f := N) (Finset.mem_univ i)))
          (by positivity) (le_max_right _ _), rfl⟩,
      fun i => ⟨i, [], by simp, rfl⟩, fun p k hk => by
        obtain ⟨u, hu, m, hm, hp⟩ := hdec p
        rw [hp, hI.2 u hu _ m _ k hk hm, Finset.mul_sum]
        simp only [η, mul_assoc]⟩
    l hl rfl [] (by simp)
  refine ⟨max C 0 * ((K₀ : ℝ) * B) ^ N₀, fun g => ?_⟩
  obtain ⟨u, hu, t, m, y, k, hk, hm, rfl⟩ := hI.1 g
  let p : P := ⟨_, hmem u hu t m y hm⟩
  change ‖l.foldr lineDer Ψ (p.1 * k)‖ ≤ _ * (height σ _ (p.1 * k) : ℝ) ^ N₀
  have h1 : height σ _ (π p) ≤ K₀ * B * height σ _ (p.1 * k) := by
    have h2 := height_mul_le σ _ (p.1 * k) k⁻¹
    rw [mul_inv_cancel_right, height_inv] at h2
    refine (hht p).trans ?_
    rw [mul_assoc, mul_comm B]
    exact mul_le_mul' le_rfl (h2.trans (mul_le_mul' le_rfl (hB k hk)))
  have h3 : (height σ _ (π p) : ℝ) ≤ (K₀ : ℝ) * B * height σ _ (p.1 * k) := by exact_mod_cast h1
  refine (hC p k hk).trans ?_
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by positivity) h3 _) (by positivity) (le_max_right _ _)

end GlobalTheory.ThK.CuspTransfer.Growth

end
