import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TupMemLatT
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.CovTrans

theorem zOm_smul_eq_q {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module (Om l) X] [Module ℚ_[l] X]
    [IsScalarTower ℚ_[l] (Om l) X] (c : ℤ_[l]) (x : X) : zOm l c • x = ((c : ℚ_[l])) • x := by
  show (algebraMap ℚ_[l] (Om l) (algebraMap ℤ_[l] ℚ_[l] c)) • x = _
  rw [algebraMap_smul]
  rfl

theorem coord_inj {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module (Om l) X] [Module ℚ_[l] X]
    [IsScalarTower ℚ_[l] (Om l) X] {n : ℕ} {v : Fin n → X} (hv : LinearIndependent ℚ_[l] v) {u u' : Fin n → ℤ_[l]}
    (h : ∑ i, zOm l (u i) • v i = ∑ i, zOm l (u' i) • v i) : u = u' := by
  simp only [zOm_smul_eq_q] at h
  have := Fintype.linearIndependent_iff.mp hv (fun i => (u i : ℚ_[l]) - u' i)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self])
  funext i
  have h2 := this i
  rw [sub_eq_zero] at h2
  exact Subtype.ext h2

theorem dsum {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module (Om l) X] {p q : ℕ} (α : Fin p → ℤ_[l])
    (β : Fin p → Fin q → ℤ_[l]) (w : Fin q → X) :
    ∑ s, zOm l (α s) • ∑ i, zOm l (β s i) • w i = ∑ i, zOm l (∑ s, β s i * α s) • w i := by
  simp only [Finset.smul_sum, smul_smul, map_sum, map_mul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
  rw [mul_comm]

theorem transition : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (d : ℕ) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)), LinearIndependent ℚ_[l] b → ∀ (m m' : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (ρs' : Fin m' → (Γ →* GL (Fin a) (Om l))) (ι : Fin m → Fin m'), (∀ k, ρs' (ι k) = ρs k) → ∀ (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (t' : Fin m' → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, t' (ι k) = t k) → ∀ (M M' : ℕ), M ≤ M' → ∀ (d₁ d₂ : ℕ) (ρ₁ : Γ →* GL (Fin d₁) ℤ_[l]) (ρ₂ : Γ →* GL (Fin d₂) ℤ_[l]) (bb₁ : Fin d₁ → Fin m → Matrix (Fin a) (Fin a) (Om l)) (bb₂ : Fin d₂ → Fin m' → Matrix (Fin a) (Fin a) (Om l)) (e₁ : Fin d₁ → ℤ_[l]) (e₂ : Fin d₂ → ℤ_[l]), LinearIndependent ℚ_[l] bb₁ → (∀ k, Reads ρ₁ (ρs k) (fun s => bb₁ s k) e₁) → (∀ k, Reads ρ₂ (ρs' k) (fun s => bb₂ s k) e₂) → (∀ s, bb₂ s ∈ GlobalTheory.TraceConjugationCover.latT ρs' t' M') → (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d₁ → ℤ_[l], x = ∑ s, zOm l (z s) • bb₁ s) → ∀ (P₁ : Matrix (Fin d) (Fin d₁) ℤ_[l]) (P₂ : Matrix (Fin d) (Fin d₂) ℤ_[l]) (n N₁ N₂ : ℕ), n ≤ N₁ → n ≤ N₂ → GlobalTheory.TraceConjugationCover.Carries r b ρs t M bb₁ P₁ N₁ → GlobalTheory.TraceConjugationCover.Carries r b ρs' t' M' bb₂ P₂ N₂ → ∃ f : Matrix (Fin d₁) (Fin d₂) ℤ_[l], (∀ g, f * ((ρ₂ g : GL (Fin d₂) ℤ_[l]) : Matrix (Fin d₂) (Fin d₂) ℤ_[l]) = ((ρ₁ g : GL (Fin d₁) ℤ_[l]) : Matrix (Fin d₁) (Fin d₁) ℤ_[l]) * f) ∧ ∀ i j, (l : ℤ_[l]) ^ n ∣ (P₁ * f - P₂) i j := by
  intro l _ Γ _ a r d b hb m m' ρs ρs' ι hι t t' ht M M' hM d₁ d₂ ρ₁ ρ₂ bb₁ bb₂ e₁ e₂ hbb₁ hR₁ hR₂ hmem₂ hcoord
    P₁ P₂ n N₁ N₂ hn₁ hn₂ hC₁ hC₂
  have hsm : ∀ {k : Fin m} (c : Om l) (w : Matrix (Fin a) (Fin a) (Om l)),
      (Pi.single k (c • w) : Fin m → Matrix (Fin a) (Fin a) (Om l)) = c • Pi.single k w := by
    intro k c w
    funext k₀
    by_cases h : k₀ = k
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hπL : ∀ y ∈ GlobalTheory.TraceConjugationCover.latL t' M', y ∘ ι ∈ GlobalTheory.TraceConjugationCover.latL t M := by
    intro y hy
    have hle : Submodule.map (LinearMap.funLeft ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) ι) (GlobalTheory.TraceConjugationCover.latL t' M') ≤
        GlobalTheory.TraceConjugationCover.latL t M := by
      rw [GlobalTheory.TraceConjugationCover.latL, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [Set.mem_iUnion, Set.mem_image] at hx
      obtain ⟨k', v, hv, rfl⟩ := hx
      change (Pi.single k' ((l : Om l) ^ M' • v)) ∘ ι ∈ _
      rw [← Finset.univ_sum_single (Pi.single k' ((l : Om l) ^ M' • v) ∘ ι)]
      refine Submodule.sum_mem _ fun k _ => ?_
      by_cases hk : ι k = k'
      · subst hk
        simp only [Function.comp_apply, Pi.single_eq_same]
        have hv' : v ∈ t k := by rw [← ht k]; exact hv
        have e1 : ((l : Om l) ^ M' • v) = zOm l ((l : ℤ_[l]) ^ (M' - M)) • ((l : Om l) ^ M • v) := by
          rw [map_pow, map_natCast, smul_smul, ← pow_add, Nat.sub_add_cancel hM]
        rw [e1, hsm, GlobalTheory.TraceConjugationCover.zOm_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_iUnion.mpr ⟨k, v, hv', rfl⟩))
      · simp [Pi.single_eq_of_ne hk]
    exact hle ⟨y, hy, rfl⟩
  have hdec : ∀ j, ∃ (F : Γ →₀ ℤ_[l]) (y : Fin m' → Matrix (Fin a) (Fin a) (Om l)), y ∈ GlobalTheory.TraceConjugationCover.latL t' M' ∧
      bb₂ j = (F.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs' g) + y := by
    intro j
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (hmem₂ j)
    obtain ⟨F, hF⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hx
    refine ⟨F, y, hy, ?_⟩
    rw [← hxy, ← hF]
    simp only [GlobalTheory.TraceConjugationCover.zOm_smul]
  choose F y hy hbb using hdec
  have hπF : ∀ (G : Γ →₀ ℤ_[l]), (G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs' g) ∘ ι =
      G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g := by
    intro G
    funext k
    simp [Finsupp.sum, Finset.sum_apply, GlobalTheory.TraceConjugationCover.tup, hι]
  have hπbb : ∀ j, bb₂ j ∘ ι = ((F j).sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) + y j ∘ ι := by
    intro j
    rw [hbb j, ← hπF]
    rfl
  have hmemT : ∀ j, bb₂ j ∘ ι ∈ GlobalTheory.TraceConjugationCover.latT ρs t M := by
    intro j
    rw [hπbb j]
    refine Submodule.add_mem_sup ?_ (hπL _ (hy j))
    simp only [GlobalTheory.TraceConjugationCover.zOm_smul]
    exact Submodule.finsuppSum_mem _ _ _ _ (fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩))
  choose z hz using fun j => hcoord _ (hmemT j)
  have hcol : ∀ j k, bb₂ j (ι k) = ∑ s, zOm l (z j s) • bb₁ s k := by
    intro j k
    have := congrFun (hz j) k
    simpa [Finset.sum_apply] using this
  refine ⟨Matrix.of fun s j => z j s, ?_, ?_⟩
  · intro g
    ext i j
    have hA : ∀ k, (ρs k g).val * bb₂ j (ι k) =
        ∑ i, zOm l (((ρ₁ g).val * Matrix.of fun s j => z j s) i j) • bb₁ i k := by
      intro k
      have e := fun s => (hR₁ k).equi g s
      try simp only at e
      rw [hcol, Finset.mul_sum]
      simp_rw [Matrix.mul_smul, e]
      rw [dsum]
      simp [Matrix.mul_apply]
    have hB : ∀ k, (ρs k g).val * bb₂ j (ι k) =
        ∑ i, zOm l (((Matrix.of fun s j => z j s) * (ρ₂ g).val) i j) • bb₁ i k := by
      intro k
      rw [← hι k]
      have e := (hR₂ (ι k)).equi g j
      try simp only at e
      rw [e]
      simp_rw [hcol]
      rw [dsum]
      simp [Matrix.mul_apply]
    have key : (fun i => ((Matrix.of fun s j => z j s) * (ρ₂ g).val) i j) =
        fun i => ((ρ₁ g).val * Matrix.of fun s j => z j s) i j := by
      apply GlobalTheory.CovTrans.coord_inj hbb₁
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [← hB k, hA k]
    exact congrFun key i
  · intro i j
    have hsingle : ∑ s, zOm l ((Pi.single j 1 : Fin d₂ → ℤ_[l]) s) • bb₂ s = bb₂ j := by
      simp [Pi.single_apply]
    obtain ⟨w₂, hw₂⟩ := hC₂ (Pi.single j 1) (F j) (y j) (hy j) (by rw [hsingle]; exact hbb j)
    obtain ⟨w₁, hw₁⟩ := hC₁ (fun s => z j s) (F j) (y j ∘ ι) (hπL _ (hy j)) (by rw [← hz j, hπbb j])
    have hP₂ : P₂ *ᵥ Pi.single j 1 = fun i => P₂ i j := by
      funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hP₁ : P₁ *ᵥ (fun s => z j s) = fun i => (P₁ * Matrix.of fun s j => z j s) i j := by
      funext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [hP₂] at hw₂
    rw [hP₁] at hw₁
    have key : (fun i => (P₁ * Matrix.of fun s j => z j s) i j - P₂ i j) =
        fun i => (l : ℤ_[l]) ^ n * ((l : ℤ_[l]) ^ (N₁ - n) * w₁ i - (l : ℤ_[l]) ^ (N₂ - n) * w₂ i) := by
      apply GlobalTheory.CovTrans.coord_inj hb
      have hs : ∑ i, zOm l ((P₁ * Matrix.of fun s j => z j s) i j - P₂ i j) • b i =
          ∑ i, zOm l ((P₁ * Matrix.of fun s j => z j s) i j) • b i - ∑ i, zOm l (P₂ i j) • b i := by
        simp only [map_sub, sub_smul, Finset.sum_sub_distrib]
      rw [hs, hw₁, hw₂, add_sub_add_left_eq_sub]
      have e1 : (l : Om l) ^ N₁ = (l : Om l) ^ n * (l : Om l) ^ (N₁ - n) := by rw [← pow_add, Nat.add_sub_cancel' hn₁]
      have e2 : (l : Om l) ^ N₂ = (l : Om l) ^ n * (l : Om l) ^ (N₂ - n) := by rw [← pow_add, Nat.add_sub_cancel' hn₂]
      rw [e1, e2]
      simp only [Finset.smul_sum, smul_smul, map_mul, map_sub, map_pow, map_natCast, mul_sub, sub_smul,
        Finset.sum_sub_distrib, mul_assoc]
    have := congrFun key i
    rw [Matrix.sub_apply, this]
    exact Dvd.intro _ rfl

end GlobalTheory.CovTrans
