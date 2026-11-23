import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColsDef
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftSubstitutionCoeffDivisible

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

variable {p f : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p f) O]

def renV {ι ι' : Type} {k k' : ℕ} (e : ι → ι') (hk : k = k') : ι × Fin k → ι' × Fin k' :=
  fun v => (e v.1, Fin.cast hk v.2)

theorem renV_injective {ι ι' : Type} {k k' : ℕ} (e : ι → ι') (he : Function.Injective e) (hk : k = k') :
    Function.Injective (renV e hk) := by
  intro a b h
  simp only [renV, Prod.mk.injEq] at h
  exact Prod.ext (he h.1) (Fin.cast_injective hk h.2)

theorem sigMat_congr_pos {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) (s s' : ℤ)
    (h : s % (f : ℤ) = s' % (f : ℤ)) : sigMat p f O g s = sigMat p f O g s' := by
  simp only [sigMat, sigPow, h]

theorem liftSubst_rename (w : O) (r : ℕ) {ι ι' : Type} (LL : LiftLetters ι) (LL' : LiftLetters ι') (e : ι → ι')
    (hvec : ∀ i, LL'.vec (e i) = LL.vec i) (hpos : ∀ i, LL'.pos (e i) % (f : ℤ) = LL.pos i % (f : ℤ))
    {k k' : ℕ} (hk : k = k') (g : Matrix (Fin k') (Fin k') (WF p f)) (F : MvPolynomial (ι × Fin k) (KK O)) :
    liftSubst p f O w r LL' g (rename (renV e hk) F) =
      rename (renV e hk) (liftSubst p f O w r LL (g.submatrix (Fin.cast hk) (Fin.cast hk)) F) := by
  subst hk
  have hsub : g.submatrix (Fin.cast (rfl : k = k)) (Fin.cast rfl) = g := by
    ext a b
    simp
  rw [hsub]
  have key : (liftSubst p f O w r LL' g).comp (rename (renV e (rfl : k = k))) =
      (rename (renV e (rfl : k = k))).comp (liftSubst p f O w r LL g) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, a⟩
    simp only [AlgHom.comp_apply, rename_X, liftSubst, aeval_X, renV, Fin.cast_eq_self, hvec]
    rw [sigMat_congr_pos g _ _ (hpos i)]
    split_ifs <;> simp [map_sum, map_mul, rename_X, rename_C, apply_ite, renV, Fin.cast_eq_self]
  exact AlgHom.congr_fun key F

theorem isGLW_submatrix_cast {k k' : ℕ} (hk : k = k') (g : Matrix (Fin k') (Fin k') (WF p f)) (hg : IsGLW g) :
    IsGLW (g.submatrix (Fin.cast hk) (Fin.cast hk)) := by
  unfold IsGLW at hg ⊢
  rw [show (Fin.cast hk : Fin k → Fin k') = finCongr hk from rfl, Matrix.det_submatrix_equiv_self]
  exact hg

theorem one_submatrix_cast {k k' : ℕ} (hk : k = k') :
    (1 : Matrix (Fin k') (Fin k') (WF p f)).submatrix (Fin.cast hk) (Fin.cast hk) = 1 := by
  ext a b
  simp [Matrix.one_apply]

private theorem coeff_rename_mem_multiple_of_coeff {σ τ : Type} (φ : σ → τ) (a : O) (P : MvPolynomial σ (KK O))
    (h : ∀ m, ∃ c : O, P.coeff m = algebraMap O (KK O) (a * c)) :
    ∀ m, ∃ c : O, (rename φ P).coeff m = algebraMap O (KK O) (a * c) := by
  classical
  have hP : rename φ P = ∑ u ∈ P.support, monomial (u.mapDomain φ) (P.coeff u) := by
    conv_lhs => rw [P.as_sum]
    simp only [map_sum, rename_monomial]
  rw [hP]
  refine Finset.sum_induction _
    (fun Q : MvPolynomial τ (KK O) => ∀ m, ∃ c : O, Q.coeff m = algebraMap O (KK O) (a * c)) ?_ ?_ ?_
  · intro Q R hQ hR m
    obtain ⟨c1, h1⟩ := hQ m
    obtain ⟨c2, h2⟩ := hR m
    exact ⟨c1 + c2, by rw [coeff_add, h1, h2, mul_add, map_add]⟩
  · intro m
    exact ⟨0, by simp⟩
  · intro u _ m
    rw [coeff_monomial]
    split_ifs
    · exact h u
    · exact ⟨0, by simp⟩

private theorem coeff_mem_multiple_of_rename_injective {σ τ : Type} (φ : σ → τ) (hφ : Function.Injective φ) (a : O)
    (P : MvPolynomial σ (KK O))
    (h : ∀ m, ∃ c : O, (rename φ P).coeff m = algebraMap O (KK O) (a * c)) :
    ∀ m, ∃ c : O, P.coeff m = algebraMap O (KK O) (a * c) := by
  intro m
  obtain ⟨c, hc⟩ := h (m.mapDomain φ)
  rw [coeff_rename_mapDomain φ hφ] at hc
  exact ⟨c, hc⟩

theorem inWj_rename_iff {σ τ : Type} (φ : σ → τ) (hφ : Function.Injective φ) (w : O)
    (P : MvPolynomial σ (KK O)) (j : ℕ) : InWj w (rename φ P) j ↔ InWj w P j :=
  ⟨coeff_mem_multiple_of_rename_injective φ hφ _ P, coeff_rename_mem_multiple_of_coeff φ _ P⟩

theorem inWj_rename {σ τ : Type} (φ : σ → τ) (w : O) (P : MvPolynomial σ (KK O)) (j : ℕ)
    (h : InWj w P j) : InWj w (rename φ P) j :=
  coeff_rename_mem_multiple_of_coeff φ _ P h

theorem inA_rename {σ τ : Type} (φ : σ → τ) (P : MvPolynomial σ (KK O)) (h : InA P) : InA (rename φ P) := by
  have e : ∀ {ρ : Type} (Q : MvPolynomial ρ (KK O)),
      InA Q ↔ ∀ m, ∃ c : O, Q.coeff m = algebraMap O (KK O) (1 * c) := by
    intro ρ Q
    simp only [one_mul]
    rfl
  rw [e] at h ⊢
  exact coeff_rename_mem_multiple_of_coeff φ _ P h

theorem inWjRg_rename (w : O) (r : ℕ) {ι ι' : Type} (LL : LiftLetters ι) (LL' : LiftLetters ι') (e : ι → ι')
    (he : Function.Injective e) (hvec : ∀ i, LL'.vec (e i) = LL.vec i)
    (hpos : ∀ i, LL'.pos (e i) % (f : ℤ) = LL.pos i % (f : ℤ)) {k k' : ℕ} (hk : k = k')
    (g : Matrix (Fin k') (Fin k') (WF p f)) (F : MvPolynomial (ι × Fin k) (KK O)) (j : ℕ) :
    InWjRg p f O w r LL' g (rename (renV e hk) F) j ↔
      InWjRg p f O w r LL (g.submatrix (Fin.cast hk) (Fin.cast hk)) F j := by
  unfold InWjRg
  rw [liftSubst_rename w r LL LL' e hvec hpos hk g F]
  exact inWj_rename_iff _ (renV_injective e he hk) _ _ _

open Classical in
theorem mem_Pol_rename {R : Type} [CommRing R] {ι ι' : Type} [Fintype ι] {k k' : ℕ} (e : ι → ι')
    (he : Function.Injective e) (hk : k = k') (d : ι → ℕ) (F : MvPolynomial (ι × Fin k) R) (hF : F ∈ Pol R k d) :
    rename (renV e hk) F ∈ Pol R k' (fun l => ∑ i : ι, if e i = l then d i else 0) := by
  subst hk
  unfold Pol at hF ⊢
  rw [MvPolynomial.mem_restrictSupport_iff] at hF ⊢
  rw [MvPolynomial.support_rename_of_injective (renV_injective e he rfl)]
  intro m hm
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hm
  obtain ⟨u, hu, rfl⟩ := hm
  have hud := hF hu
  intro l
  unfold multideg
  by_cases hl : ∃ i, e i = l
  · obtain ⟨i, rfl⟩ := hl
    have h1 : ∀ c, (Finsupp.mapDomain (renV e rfl) u) (e i, c) = u (i, c) := by
      intro c
      have h2 := Finsupp.mapDomain_apply (renV_injective e he rfl) u (i, c)
      simpa [renV] using h2
    simp only [h1]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (fun h => hj (he h))]) (by simp), if_pos rfl]
    exact hud i
  · push_neg at hl
    have h0 : ∀ c, (Finsupp.mapDomain (renV e rfl) u) (l, c) = 0 := by
      intro c
      apply Finsupp.mapDomain_notin_range
      rintro ⟨v, hv⟩
      exact hl v.1 (congrArg Prod.fst hv)
    simp [h0, hl]

end Formalism.MainNotions.ColumnSystems.Pf.GenusGluing
