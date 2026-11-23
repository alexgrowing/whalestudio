import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviCentreFiniteUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotIsConstTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.Published.LeviCentreModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (F) in

def big (δ : E) : Spc F E 3 := ⟨!![0, 0, 1; 0, δ, 0; -1, 0, 0], ⊥, fun _ => 1, fun _ => 1⟩

variable (F) in

def small (δ : E) : Spc F E 1 := ⟨!![δ], ⊥, fun _ => 1, fun _ => 1⟩

variable (E) in

def pl : Plane E 3 1 := ⟨![1, 0, 0], ![0, 0, 1], !![0; 1; 0], 1⟩

def detA {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J →* AE F E :=
  Matrix.detMonoidHom.comp ((Units.coeHom _).comp (Subgroup.subtype _))

theorem detA_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) : detA J g = (mat g).det := rfl

theorem detA_unip (δ : E) : ∀ u ∈ unip σ (big F δ) (pl E), detA (big F δ).J u = 1 := by
  refine fun u hu => (Subgroup.closure_le (detA (σ := σ) (big F δ).J).ker).2 ?_ hu
  rintro u ⟨h1, h2⟩
  obtain ⟨a, h2⟩ := h2 ![1]
  have a0 := congrFun h1 0
  have a1 := congrFun h1 1
  have a2 := congrFun h1 2
  have b1 := congrFun h2 1
  have b2 := congrFun h2 2
  have c := congrFun (congrFun (show (mat u)ᵀ * incM F (big F δ).J * (mat u).map (cA σ) = incM F (big F δ).J from u.2) 2) 0
  change (mat u).det = 1
  generalize mat u = M at a0 a1 a2 b1 b2 c ⊢
  simp [pl, incV, incM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at a0 a1 a2 b1 b2
  simp [big, incM, Matrix.mul_apply, Fin.sum_univ_three, a0, a1, a2] at c
  rw [Matrix.det_fin_three]
  simp [a0, a1, a2, b1, b2, c]

theorem detA_levi (δ : E) (h₁ : UA σ (small F δ).J) (m : UA σ (big F δ).J)
    (hm : IsLevi (W₁ := small F δ) (pl E) 1 h₁ m) : detA (big F δ).J m = mat h₁ 0 0 := by
  obtain ⟨h1, h2, h3⟩ := hm
  have a0 := congrFun h1 0
  have a1 := congrFun h1 1
  have a2 := congrFun h1 2
  have b0 := congrFun h2 0
  have b1 := congrFun h2 1
  have b2 := congrFun h2 2
  have c1 := congrFun (congrFun h3 1) 0
  have c2 := congrFun (congrFun h3 2) 0
  simp [pl, incV, incM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.mul_apply] at a0 a1 a2 b0 b1 b2 c1 c2
  rw [detA_apply, Matrix.det_fin_three]
  simp [a0, a1, a2, b0, b1, b2, c1, c2]

theorem arch_entry {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F} (τ : EmbOver E w) (g : GAd σ J) (i j : Fin n) :
    GlobalTheory.Orb.archMat σ J τ (projArch σ J w g) i j = piInf τ (g.1.1 i j) := rfl

theorem exists_inhabitant (hσ : IsCMExt F E σ) {δ : E} (h0 : δ ≠ 0) (hδ : σ δ = -δ) :
    ∃ (Y : Spc F E 3) (Y₁ : Spc F E 1) (H : Plane E 3 1) (ψ : UA σ Y.J → ℂ) (c : E) (h : UA σ Y.J) (g : UA σ Y₁.J → ℂ)
      (φ₁ : GAd σ (c • Y₁.J.map σ) → ℂ),
      (∀ i j, σ (Y.J j i) = -Y.J i j) ∧ form σ Y.J H.x H.x = 0 ∧ form σ Y.J H.y H.y = 0 ∧ form σ Y.J H.x H.y = 1 ∧
      (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) ∧ H.ιᵀ * Y.J * H.ι.map σ = Y₁.J ∧ Y.J.det ≠ 0 ∧
      Y₁.J.det ≠ 0 ∧ (∀ u ∈ unip σ Y H, ∀ x, ψ (u * x) = ψ x) ∧ c ≠ 0 ∧ IsHermND σ (c • Y.J.map σ) ∧
      IsHermND σ (c • Y₁.J.map σ) ∧
      (∀ φ : GAd σ (c • Y.J.map σ) → ℂ, (∀ (g : UA σ Y.J) (g' : GAd σ (c • Y.J.map σ)), g.1 = g'.1 → φ g' = ψ g) →
        GlobalTheory.UAut.IsSm σ (c • Y.J.map σ) φ ∧
          FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, GlobalTheory.UAut.IsCentral σ (c • Y.J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ})) ∧
      (∀ h₁ m, IsLevi (W₁ := Y₁) H 1 h₁ m → g h₁ = ψ (m * h)) ∧
      (∀ (g₁ : UA σ Y₁.J) (g' : GAd σ (c • Y₁.J.map σ)), g₁.1 = g'.1 → φ₁ g' = g g₁) ∧ ∃ a, φ₁ a ≠ φ₁ 1 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  refine ⟨big F δ, small F δ, pl E, fun g => piInf τ (detA _ g), δ, 1, fun g => piInf τ (mat g 0 0),
    fun g => piInf τ (g.1.1 0 0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h0, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [big, hδ]
  · simp [form, big, pl, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [form, big, pl, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [form, big, pl, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · intro u; simp [form, big, pl, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ext i j; fin_cases i; fin_cases j; simp [big, small, pl, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [big, Matrix.det_fin_three, h0]
  · simp [small, h0]
  · intro u hu x; simp only [map_mul, detA_unip δ u hu, one_mul]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [big, hδ]
  · simp [big, Matrix.det_fin_three, h0, hδ]
  · intro i j; fin_cases i; fin_cases j; simp [small, hδ]
  · simp [small, h0, hδ]
  · intro φ hφ
    obtain rfl : φ = fun g' => piInf τ (g'.1.1.det) := funext fun g' => by
      obtain ⟨g, hg⟩ := GlobalTheory.ThK.SmoothLev.exists_val_eq σ _ hσ h0 g'
      rw [hφ g g' hg]
      exact congrArg (fun x : GL (Fin 3) (AE F E) => piInf τ x.1.det) hg
    constructor
    · intro k γ hγ g
      have e := fun i j => GlobalTheory.UAut.Model.isSm_entry (J := δ • (big F δ).J.map σ) hσ τ i j k γ hγ g
      simp only [arch_entry] at e
      simp only [Matrix.det_fin_three, map_add, map_sub, map_mul]
      fun_prop
    · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ
        {fun g' : GAd σ (δ • (big F δ).J.map σ) => piInf τ (g'.1.1.det)}) (Submodule.span_le.2 ?_)
      rintro _ ⟨z, -, rfl⟩
      choose c hc using GlobalTheory.UAut.Model.foldr_char (φ := fun g' : GAd σ (δ • (big F δ).J.map σ) => piInf τ (g'.1.1.det))
        fun g h => by rw [← map_mul, ← Matrix.det_mul]; rfl
      exact Submodule.mem_span_singleton.2 ⟨z.sum fun l a => a * c l, funext fun g => by
        simp [GlobalTheory.UAut.dop, hc, Finsupp.sum, Finset.sum_mul, mul_assoc]⟩
  · intro h₁ m hm; simp only [mul_one, detA_levi δ h₁ m hm]
  · intro g₁ g' e; simp only [mat, e]
  · refine ⟨⟨-1, show _ * _ * _ = _ by
      ext i j; fin_cases i; fin_cases j; simp [Formalism.UG.cT, Matrix.mul_apply]⟩, ?_⟩
    change piInf τ ((-1 : Matrix (Fin 1) (Fin 1) _) 0 0) ≠ piInf τ ((1 : Matrix (Fin 1) (Fin 1) _) 0 0)
    simp only [Matrix.neg_apply, Matrix.one_apply_eq, map_neg, map_one]
    norm_num

open Matrix GlobalTheory.LeviUnitary in

theorem exists_levi (hcm : IsCMExt F E σ) {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    (hsk : ∀ i j, σ (W.J j i) = -W.J i j)
    (horth : ∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 ∧ form σ W.J (H'.ι *ᵥ u) H'.y = 0)
    (hgram : H'.ιᵀ * W.J * H'.ι.map σ = W₁.J) (hd : W₁.J.det ≠ 0) (h₁ : UA σ W₁.J) :
    ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' 1 h₁ m := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hdet : IsUnit W₁.J.det := hd.isUnit
  obtain ⟨π, p1, p2, p3, p4, p5⟩ : ∃ π : Matrix (Fin d₁) (Fin d) E, π * H'.ι = 1 ∧ W.J * H'.ι.map σ = πᵀ * W₁.J ∧
      H'.ιᵀ * W.J = W₁.J * π.map σ ∧ π *ᵥ H'.x = 0 ∧ π *ᵥ H'.y = 0 := by
    have mm : ∀ {k l : ℕ} (A : Matrix (Fin k) (Fin l) E), (A.map σ).map σ = A := fun A => by
      ext i j; exact hσ _
    have mul : ∀ {k l p : ℕ} (A : Matrix (Fin k) (Fin l) E) (A' : Matrix (Fin l) (Fin p) E),
        (A * A').map σ = A.map σ * A'.map σ := fun A A' => Matrix.map_mul (f := σ.toRingHom)
    have sk : W.J.map σ = -W.Jᵀ := by ext i j; exact hsk j i
    have sk₁ : W₁.J.map σ = -W₁.Jᵀ := by
      rw [← hgram, mul, mul, mm, sk, transpose_mul, transpose_mul, transpose_transpose]
      simp [Matrix.mul_assoc, Matrix.transpose_map]
    set P : Matrix (Fin d₁) (Fin d) E := W₁.J⁻¹ * (H'.ιᵀ * W.J) with hP
    have h2 : H'.ιᵀ * W.J = W₁.J * P := by rw [hP, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
    have hz : ∀ z : Fin d → E, (∀ u, form σ W.J (H'.ι *ᵥ u) z = 0) → P.map σ *ᵥ z = 0 := by
      intro z hz
      have e1 : (H'.ιᵀ * W.J) *ᵥ (fun i => σ (z i)) = 0 := by
        funext j
        have := hz (Pi.single j 1)
        rw [form, mulVec_single_one] at this
        rw [← mulVec_mulVec]
        exact this
      have e2 : P *ᵥ (fun i => σ (z i)) = 0 := by rw [hP, ← mulVec_mulVec, e1, mulVec_zero]
      funext j
      have := congrArg σ (congrFun e2 j)
      simpa [mulVec, dotProduct, map_sum, map_mul, hσ] using this
    refine ⟨P.map σ, ?_, ?_, by rw [mm, h2], hz _ fun u => (horth u).1, hz _ fun u => (horth u).2⟩
    · have : P * H'.ι.map σ = 1 := by rw [hP, Matrix.mul_assoc, hgram, Matrix.nonsing_inv_mul _ hdet]
      rw [← mm H'.ι, ← mul, this]
      exact Matrix.map_one _ (map_zero σ) (map_one σ)
    · have := congrArg (fun A => (Matrix.map A σ)ᵀ) h2
      simp only [mul, sk, sk₁, transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg,
        neg_inj] at this
      exact this
  have q1 : incM F π * incM F H'.ι = 1 := by
    rw [← incM_mul, p1]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have q2 : incM F W.J * (incM F H'.ι).map (cA σ).toRingHom = (incM F π)ᵀ * incM F W₁.J := by
    rw [incM_conj, ← incM_mul, p2, incM_mul]; rfl
  have q3 : (incM F H'.ι)ᵀ * incM F W.J = incM F W₁.J * (incM F π).map (cA σ).toRingHom := by
    rw [incM_conj, ← incM_mul, ← p3, incM_mul]; rfl
  have hfix : ∀ z, π *ᵥ z = 0 → (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) *ᵥ incV F z = incV F z := by
    intro z hz
    have h0 : incV F (0 : Fin d₁ → E) = 0 := by funext i; exact map_zero _
    rw [add_mulVec, one_mulVec, ← mulVec_mulVec, incM_mulVec, hz, h0, mulVec_zero, add_zero]
  refine ⟨⟨⟨1 + incM F H'.ι * (mat h₁ - 1) * incM F π, 1 + incM F H'.ι * ((h₁.1⁻¹).1 - 1) * incM F π, ?_, ?_⟩, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [ext_mul q1, mat, Units.mul_inv]; simp
  · rw [ext_mul q1, mat, Units.inv_mul]; simp
  · exact ext_unitary (cA σ).toRingHom q1 q2 q3 h₁.2
  · rw [Units.val_one, one_smul]; exact hfix _ p4
  · rw [inv_one, Units.val_one, map_one, one_smul]; exact hfix _ p5
  · show (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) * incM F H'.ι = _
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, q1, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]

theorem exists_anti (hσ : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  have hs := GlobalTheory.SiegelSet.sigma_sigma hσ
  haveI := hσ.2.1
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_contra hcon
  push Not at hcon
  have : ∀ x, σ x = x := fun x => by
    by_contra hx
    exact hcon (x - σ x) (sub_ne_zero.2 (Ne.symm hx)) (by rw [map_sub, hs]; ring)
  exact IsTotallyComplex.complexEmbedding_not_isReal τ
    (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
      have := hσ.2.2.2 τ x
      rw [‹∀ x, σ x = x› x] at this
      simpa using this.symm))

example (hσ : IsCMExt F E σ) {δ : E} (hJ : IsHermND σ (δ • (small F δ).J.map σ)) :
    ∃ φ₁ : GAd σ (δ • (small F δ).J.map σ) → ℂ, GlobalTheory.UAut.IsSm σ _ φ₁ ∧ ¬ FiniteDimensional ℂ (Submodule.span ℂ
      {u | ∃ z, GlobalTheory.UAut.IsCentral σ (δ • (small F δ).J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ₁}) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  exact ⟨_, GlobalTheory.UAut.Model.not_zfin_exp hσ hJ τ 0⟩

end GlobalTheory.Published.LeviCentreModel

end
