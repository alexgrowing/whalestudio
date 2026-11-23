import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtDataPfA

namespace ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem sum_castLE_eq {n : ℕ} (h : n ≤ r) (g : Fin r → ℝ) :
    ∑ a : Fin n, g (Fin.castLE h a) = ∑ b ∈ Finset.univ.filter (fun b : Fin r => (b : ℕ) < n), g b := by
  classical
  refine Finset.sum_bij (fun a _ => Fin.castLE h a) (fun a _ => by simp) (fun a _ b _ hab => Fin.castLE_injective h hab)
    (fun b hb => ⟨⟨b, by simpa using hb⟩, Finset.mem_univ _, Fin.ext rfl⟩) (fun a _ => rfl)

theorem sum_shift_eq {n m : ℕ} (hn : n ≤ r) (hm : m = r - n) (g : Fin r → ℝ) (f : Fin m → Fin r)
    (hf : ∀ a, (f a : ℕ) = n + a) :
    ∑ a : Fin m, g (f a) = ∑ b ∈ Finset.univ.filter (fun b : Fin r => ¬ (b : ℕ) < n), g b := by
  classical
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := congrArg Fin.val hab
    rw [hf, hf] at h1
    exact Fin.ext (by omega)
  refine Finset.sum_bij (fun a _ => f a) (fun a _ => by simp [hf]) (fun a _ b _ hab => hinj hab)
    (fun b hb => ?_) (fun a _ => rfl)
  have hb' : ¬ (b : ℕ) < n := by simpa using hb
  refine ⟨⟨b - n, by have := b.isLt; omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
  rw [hf]
  simp only
  omega

theorem conj_conj_X (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
  star_star φ

theorem cols_linInd (X : Data E r) (x : Frame X.Ψ r) (A : TorusAt X x) (τ : X.Ψ) :
    LinearIndependent ℂ (X.colP x τ) := by
  have h := A.e_flag τ r le_rfl
  have h1 : (fun a : Fin r => A.e τ (Fin.castLE le_rfl a)) = A.e τ := funext fun a => rfl
  have h2 : (fun a : Fin r => col (mat x τ) (Fin.castLE le_rfl a)) = fun a => col (mat x τ) a :=
    funext fun a => rfl
  rw [h1, h2, e_span X τ (A.e τ) (A.e_orth τ)] at h
  have hcols : LinearIndependent ℂ (fun a : Fin r => col (mat x τ) a) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank h.le (by simp)
  exact hcols.comp _ (Fin.castLE_injective X.p0_le)

theorem norm_sq_eq (X : Data E r) (x : Frame X.Ψ r) (A : TorusAt X x) (v : Fin r → E) :
    ‖A.φ v‖ ^ 2 = ∑ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 v) := by
  classical
  have hc : ∀ τ : X.Ψ, 0 ≤ X.c τ := fun τ => by unfold Data.c; positivity
  have hmaj : ∀ τ : X.Ψ, X.maj x τ (Data.emb τ.1 v) =
      ∑ b : Fin r, ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ b)‖ ^ 2 := fun τ =>
    maj_eq_sum X τ (A.e τ) (A.e_orth τ) x (A.e_flag τ X.p0 X.p0_le) (cols_linInd X x A τ) _
  let F : (E →+* ℂ) → ℝ := fun σ => ∑ a : Fin (A.T.dim σ), ‖A.φ v ⟨σ, a⟩‖ ^ 2
  have hpos : ∀ τ : X.Ψ, F τ.1 = X.c τ * ∑ b ∈ Finset.univ.filter (fun b : Fin r => (b : ℕ) < X.p0),
      ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ b)‖ ^ 2 := by
    intro τ
    have hle : A.T.dim τ.1 ≤ r := by rw [A.dim_pos τ]; exact X.p0_le
    have e1 : ∀ a : Fin (A.T.dim τ.1), ‖A.φ v ⟨τ.1, a⟩‖ ^ 2 =
        X.c τ * ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ (Fin.castLE hle a))‖ ^ 2 := by
      intro a
      rw [A.coord_pos τ a v, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (hc τ)]
    show ∑ a : Fin (A.T.dim τ.1), ‖A.φ v ⟨τ.1, a⟩‖ ^ 2 = _
    rw [Finset.sum_congr rfl fun a _ => e1 a, ← Finset.mul_sum,
      sum_castLE_eq hle (fun b => ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ b)‖ ^ 2), A.dim_pos τ]
  have hneg : ∀ τ : X.Ψ, F (ComplexEmbedding.conjugate τ.1) =
      X.c τ * ∑ b ∈ Finset.univ.filter (fun b : Fin r => ¬ (b : ℕ) < X.p0),
        ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ b)‖ ^ 2 := by
    intro τ
    have hlt : ∀ a : Fin (A.T.dim (ComplexEmbedding.conjugate τ.1)), X.p0 + a.1 < r := by
      intro a
      have h1 : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (A.dim_neg τ)
      have := X.p0_le
      omega
    have e1 : ∀ a : Fin (A.T.dim (ComplexEmbedding.conjugate τ.1)),
        ‖A.φ v ⟨ComplexEmbedding.conjugate τ.1, a⟩‖ ^ 2 =
          X.c τ * ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ ⟨X.p0 + a.1, hlt a⟩)‖ ^ 2 := by
      intro a
      rw [A.coord_neg τ a v, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (hc τ), Complex.norm_conj, norm_neg]
    show ∑ a : Fin (A.T.dim (ComplexEmbedding.conjugate τ.1)),
      ‖A.φ v ⟨ComplexEmbedding.conjugate τ.1, a⟩‖ ^ 2 = _
    rw [Finset.sum_congr rfl fun a _ => e1 a, ← Finset.mul_sum]
    congr 1
    exact sum_shift_eq X.p0_le (A.dim_neg τ) (fun b => ‖hermC τ.1 X.Gm (Data.emb τ.1 v) (A.e τ b)‖ ^ 2)
      (fun a => ⟨X.p0 + a.1, hlt a⟩) (fun a => rfl)
  have hsplit : ∑ σ, F σ = ∑ τ : X.Ψ, (F τ.1 + F (ComplexEmbedding.conjugate τ.1)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun σ => σ ∈ X.Ψ)]
    have hfilt : Finset.univ.filter (fun σ => σ ∈ X.Ψ) = X.Ψ := by ext; simp
    have hcomp : ∑ σ ∈ Finset.univ.filter (fun σ => σ ∉ X.Ψ), F σ =
        ∑ τ ∈ X.Ψ, F (ComplexEmbedding.conjugate τ) := by
      refine Finset.sum_nbij' (fun σ => ComplexEmbedding.conjugate σ)
        (fun τ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
      · intro σ hσ
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        rw [X.cmType, conj_conj_X]
        exact hσ
      · intro τ hτ
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
        exact (X.cmType τ).mp hτ
      · intro σ _; exact conj_conj_X σ
      · intro τ _; exact conj_conj_X τ
      · intro σ _; rw [conj_conj_X]
    rw [hfilt, hcomp, ← Finset.sum_add_distrib,
      ← Finset.sum_coe_sort X.Ψ (fun σ => F σ + F (ComplexEmbedding.conjugate σ))]
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]
  show ∑ σ, F σ = _
  rw [hsplit]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [hpos τ, hneg τ, hmaj τ, ← mul_add, Finset.sum_filter_add_sum_filter_not]

theorem torusAtIs_holds : TorusAtIsStatement := by
  intro E _ _ _ r X x A
  exact ⟨A.φ, A.sg, A.sg_pm, A.lat, A.act_eq, fun v _ => norm_sq_eq X x A v, A.im_eq⟩

end ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
