import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section Good

variable {O : Type} [CommRing O] [IsDomain O] {σ : Type}

def goodSub (w : O) (δ : (σ →₀ ℕ) → ℕ) (h0 : δ 0 = 0) (hadd : ∀ a b, δ (a + b) = δ a + δ b) :
    Subalgebra O (MvPolynomial σ (KK O)) where
  carrier := {P | ∀ m, ∃ a : O, P.coeff m = algebraMap O (KK O) (w ^ δ m * a)}
  mul_mem' := by
    intro P Q hP hQ m
    classical
    rw [coeff_mul]
    choose a ha using hP
    choose b hb using hQ
    refine ⟨∑ x ∈ antidiagonal m, a x.1 * b x.2, ?_⟩
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [ha, hb, ← map_mul]
    congr 1
    rw [← (mem_antidiagonal.mp hx), hadd, pow_add]; ring
  add_mem' := by
    intro P Q hP hQ m
    obtain ⟨a, ha⟩ := hP m; obtain ⟨b, hb⟩ := hQ m
    exact ⟨a + b, by rw [coeff_add, ha, hb, ← map_add]; congr 1; ring⟩
  algebraMap_mem' := by
    intro c m
    classical
    rw [MvPolynomial.algebraMap_apply, coeff_C]
    by_cases h : 0 = m
    · subst h; exact ⟨c, by simp [h0]⟩
    · exact ⟨0, by simp [h]⟩

lemma mem_goodSub {w : O} {δ : (σ →₀ ℕ) → ℕ} {h0 : δ 0 = 0} {hadd : ∀ a b, δ (a + b) = δ a + δ b}
    {P : MvPolynomial σ (KK O)} :
    P ∈ goodSub w δ h0 hadd ↔ ∀ m, ∃ a : O, P.coeff m = algebraMap O (KK O) (w ^ δ m * a) := by
  exact Iff.rfl

lemma C_mem_sub (Sg : Subalgebra O (MvPolynomial σ (KK O))) (c : O) :
    (C (algebraMap O (KK O) c) : MvPolynomial σ (KK O)) ∈ Sg := by
  have := Sg.algebraMap_mem c
  rwa [MvPolynomial.algebraMap_apply] at this

lemma X_mem_goodSub {w : O} {δ : (σ →₀ ℕ) → ℕ} {h0 : δ 0 = 0} {hadd : ∀ a b, δ (a + b) = δ a + δ b}
    (v : σ) (hv : δ (Finsupp.single v 1) = 0) : (X v : MvPolynomial σ (KK O)) ∈ goodSub w δ h0 hadd := by
  rw [mem_goodSub]
  intro m
  classical
  rw [MvPolynomial.coeff_X']
  by_cases h : Finsupp.single v 1 = m
  · subst h
    exact ⟨1, by simp [hv]⟩
  · exact ⟨0, by simp [h]⟩

lemma wX_mem_goodSub {w : O} {δ : (σ →₀ ℕ) → ℕ} {h0 : δ 0 = 0} {hadd : ∀ a b, δ (a + b) = δ a + δ b}
    (v : σ) (hv : δ (Finsupp.single v 1) = 1) :
    (C (algebraMap O (KK O) w) * X v : MvPolynomial σ (KK O)) ∈ goodSub w δ h0 hadd := by
  rw [mem_goodSub]
  intro m
  classical
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
  by_cases h : Finsupp.single v 1 = m
  · subst h
    exact ⟨1, by simp [hv]⟩
  · exact ⟨0, by simp [h]⟩

lemma aeval_mem_sub {τ : Type} (Sg : Subalgebra O (MvPolynomial τ (KK O))) (φ : σ → MvPolynomial τ (KK O))
    (hφ : ∀ v, φ v ∈ Sg) (F : MvPolynomial σ (KK O)) (hF : InA F) :
    (aeval φ : MvPolynomial σ (KK O) →ₐ[KK O] MvPolynomial τ (KK O)) F ∈ Sg := by
  classical
  rw [F.as_sum, map_sum]
  refine Subalgebra.sum_mem _ (fun m _ => ?_)
  rw [MvPolynomial.aeval_monomial]
  obtain ⟨c, hc⟩ := hF m
  rw [hc, MvPolynomial.algebraMap_eq]
  refine Subalgebra.mul_mem _ (C_mem_sub Sg c) ?_
  exact Subalgebra.prod_mem _ (fun i _ => Subalgebra.pow_mem _ (hφ i) _)

end Good

section Sig

variable (p f : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p f) O] {k : ℕ}

def psiO (s : ℤ) : WF p f →+* O := (algebraMap (WF p f) O).comp (sigPow p f s)

lemma sigMat_apply (g : Matrix (Fin k) (Fin k) (WF p f)) (s : ℤ) (a b : Fin k) :
    sigMat p f O g s a b = algebraMap O (KK O) (psiO p f O s (g a b)) := rfl

lemma sigMat_eq_map (g : Matrix (Fin k) (Fin k) (WF p f)) (s : ℤ) :
    sigMat p f O g s = g.map ((algebraMap O (KK O)).comp (psiO p f O s)) := by
  exact Matrix.ext fun a b => rfl

lemma sigMat_mul (g h : Matrix (Fin k) (Fin k) (WF p f)) (s : ℤ) :
    sigMat p f O (g * h) s = sigMat p f O g s * sigMat p f O h s := by
  simp only [sigMat_eq_map, Matrix.map_mul]

lemma sigMat_one (s : ℤ) : sigMat p f O (1 : Matrix (Fin k) (Fin k) (WF p f)) s = 1 := by
  rw [sigMat_eq_map]
  exact Matrix.map_one _ (map_zero _) (map_one _)

lemma sigMat_inv (g : Matrix (Fin k) (Fin k) (WF p f)) (hg : IsGLW g) (s : ℤ) :
    (sigMat p f O g s)⁻¹ = sigMat p f O g⁻¹ s := by
  rw [sigMat_eq_map, sigMat_eq_map]
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul g hg]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end Sig

section PartB

variable (p f : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF p f) O] {k : ℕ}

private lemma degUS_eq_sum_ite {ι : Type} (LL : LiftLetters ι) (r : ℕ) (m : ι × Fin k →₀ ℕ) :
    degUS LL r m = m.sum (fun v n =>
      if (LL.vec v.1 = true ∧ r ≤ v.2.val) ∨ (LL.vec v.1 = false ∧ v.2.val < r) then n else 0) := rfl

lemma degUS_zero {ι : Type} (LL : LiftLetters ι) (r : ℕ) : degUS (k := k) LL r 0 = 0 := by
  rw [degUS_eq_sum_ite, Finsupp.sum_zero_index]

lemma degUS_add {ι : Type} (LL : LiftLetters ι) (r : ℕ) (a b : ι × Fin k →₀ ℕ) :
    degUS LL r (a + b) = degUS LL r a + degUS LL r b := by
  rw [degUS_eq_sum_ite, degUS_eq_sum_ite, degUS_eq_sum_ite]
  apply Finsupp.sum_add_index'
  · intro v
    split_ifs <;> rfl
  · intro v b1 b2
    split_ifs <;> simp

lemma degUS_single {ι : Type} (LL : LiftLetters ι) (r : ℕ) (v : ι × Fin k) :
    degUS LL r (Finsupp.single v 1) =
      if (LL.vec v.1 = true ∧ r ≤ v.2.val) ∨ (LL.vec v.1 = false ∧ v.2.val < r) then 1 else 0 := by
  rw [degUS_eq_sum_ite, Finsupp.sum_single_index]
  all_goals (split_ifs <;> rfl)

def usSub {ι : Type} (w : O) (LL : LiftLetters ι) (r : ℕ) : Subalgebra O (MvPolynomial (ι × Fin k) (KK O)) :=
  goodSub w (degUS LL r) (degUS_zero LL r) (degUS_add LL r)

lemma liftSubst_X_mem {ι : Type} (w : O) (LL : LiftLetters ι) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p f))
    (hg : IsGLW g) (v : ι × Fin k) : liftSubst p f O w r LL g (X v) ∈ usSub O w LL r := by
  simp only [liftSubst, MvPolynomial.aeval_X]
  by_cases hv : LL.vec v.1 = true
  · rw [if_pos hv]
    refine Subalgebra.sum_mem _ (fun b _ => Subalgebra.mul_mem _ ?_ ?_)
    · by_cases hb : r ≤ b.val
      · rw [if_pos hb]
        exact wX_mem_goodSub (v.1, b) (by rw [degUS_single]; simp [hv, hb])
      · rw [if_neg hb]
        exact X_mem_goodSub (v.1, b) (by rw [degUS_single]; simp [hv, hb])
    · rw [sigMat_inv p f O g hg, sigMat_apply]
      exact C_mem_sub _ _
  · rw [if_neg hv]
    have hv' : LL.vec v.1 = false := by simpa using hv
    refine Subalgebra.sum_mem _ (fun b _ => Subalgebra.mul_mem _ ?_ ?_)
    · by_cases hb : b.val < r
      · rw [if_pos hb]
        exact wX_mem_goodSub (v.1, b) (by rw [degUS_single]; simp [hv', hb])
      · rw [if_neg hb]
        exact X_mem_goodSub (v.1, b) (by rw [degUS_single]; simp [hv', hb])
    · rw [sigMat_apply]
      exact C_mem_sub _ _

theorem lift_substitution_coeff_divisible {ι : Type} (w : O) (LL : LiftLetters ι) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p f))
    (hg : IsGLW g) (F : MvPolynomial (ι × Fin k) (KK O)) (hF : InA F) (m : ι × Fin k →₀ ℕ) :
    ∃ a : O, (liftSubst p f O w r LL g F).coeff m = algebraMap O (KK O) (w ^ degUS LL r m * a) := by
  have hmem : liftSubst p f O w r LL g F ∈ usSub O w LL r := by
    refine aeval_mem_sub (usSub O w LL r) _ (fun v => ?_) F hF
    have := liftSubst_X_mem p f O w LL r g hg v
    simp only [liftSubst, MvPolynomial.aeval_X] at this
    exact this
  exact mem_goodSub.mp hmem m

end PartB

section PartA

variable (p f : ℕ) [Fact p.Prime] {k : ℕ}

lemma plane_block (r : ℕ) (g g' : Matrix (Fin k) (Fin k) (WF p f)) (hg' : IsGLW g')
    (h : ratPlane p f r g ≤ ratPlane p f r g') (b c : Fin k) (hb : b.val < r) (hc : r ≤ c.val) :
    WittVector.constantCoeff ((g⁻¹ * g') b c) = 0 := by
  let ℓ : (Fin k → GaloisField p f) →ₗ[GaloisField p f] GaloisField p f :=
    { toFun := fun x => ∑ j, x j * WittVector.constantCoeff (g' j c)
      map_add' := fun x y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hspan : ratPlane p f r g' ≤ LinearMap.ker ℓ := by
    rw [ratPlane, Submodule.span_le]
    rintro x ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    show ∑ j, WittVector.constantCoeff (g'⁻¹ i j) * WittVector.constantCoeff (g' j c) = 0
    have hic : i ≠ c := by
      intro hh
      have := congrArg Fin.val hh
      omega
    have e : ∑ j, WittVector.constantCoeff (g'⁻¹ i j) * WittVector.constantCoeff (g' j c) =
        WittVector.constantCoeff ((g'⁻¹ * g') i c) := by
      rw [Matrix.mul_apply, map_sum]
      simp only [map_mul]
    rw [e, Matrix.nonsing_inv_mul g' hg', Matrix.one_apply_ne hic, map_zero]
  have hv : (fun j => WittVector.constantCoeff (g⁻¹ b j)) ∈ ratPlane p f r g :=
    Submodule.subset_span ⟨b, hb, rfl⟩
  have h2 : ℓ (fun j => WittVector.constantCoeff (g⁻¹ b j)) = 0 := hspan (h hv)
  have e : WittVector.constantCoeff ((g⁻¹ * g') b c) =
      ∑ j, WittVector.constantCoeff (g⁻¹ b j) * WittVector.constantCoeff (g' j c) := by
    rw [Matrix.mul_apply, map_sum]
    simp only [map_mul]
  rw [e]
  exact h2

lemma p_dvd_of_cc (x : WF p f) (h : WittVector.constantCoeff x = 0) : ∃ y : WF p f, x = (p : WF p f) * y := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, mul_zero]⟩
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul x hx
  cases m with
  | zero =>
    exfalso
    apply hb
    have h' : WittVector.constantCoeff b = 0 := by simpa using h
    exact h'
  | succ m => exact ⟨(p : WF p f) ^ m * b, by ring⟩

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF p f) O]

lemma w_dvd_psi (S : UniformizedDVR p O) (s : ℤ) (x : WF p f) (h : WittVector.constantCoeff x = 0) :
    ∃ e : O, psiO p f O s x = S.w * e := by
  obtain ⟨y, rfl⟩ := p_dvd_of_cc p f x h
  have hp : S.w ∣ (p : O) := by
    have := S.p_mem
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer S.w).mp S.w_irr, Ideal.mem_span_singleton] at this
    exact this
  obtain ⟨t, ht⟩ := hp
  refine ⟨t * psiO p f O s y, ?_⟩
  rw [map_mul, map_natCast, ht, mul_assoc]

open Classical in

def dW {ι : Type} (w : O) (LL : LiftLetters ι) (r : ℕ) (l : ι) (b : Fin k) : O :=
  if (LL.vec l = true ∧ r ≤ b.val) ∨ (LL.vec l = false ∧ b.val < r) then w else 1

def NO {ι : Type} (LL : LiftLetters ι) (g g' : Matrix (Fin k) (Fin k) (WF p f)) (l : ι) (c b : Fin k) : O :=
  if LL.vec l then psiO p f O (LL.pos l) ((g'⁻¹ * g) c b) else psiO p f O (LL.pos l) ((g⁻¹ * g') b c)

lemma exists_A {ι : Type} (S : UniformizedDVR p O) (LL : LiftLetters ι) (r : ℕ)
    (g g' : Matrix (Fin k) (Fin k) (WF p f)) (hg : IsGLW g) (hg' : IsGLW g')
    (h : ratPlane p f r g = ratPlane p f r g') (l : ι) (c b : Fin k) :
    ∃ A : O, dW O S.w LL r l b * A = dW O S.w LL r l c * NO p f O LL g g' l c b := by
  unfold dW
  by_cases hb : (LL.vec l = true ∧ r ≤ b.val) ∨ (LL.vec l = false ∧ b.val < r)
  · rw [if_pos hb]
    by_cases hc : (LL.vec l = true ∧ r ≤ c.val) ∨ (LL.vec l = false ∧ c.val < r)
    · rw [if_pos hc]
      exact ⟨_, rfl⟩
    · rw [if_neg hc, one_mul]
      unfold NO
      by_cases hv : LL.vec l = true
      · have hbr : r ≤ b.val := by simpa [hv] using hb
        have hcr : c.val < r := by
          have := hc
          simp [hv] at this
          omega
        rw [if_pos hv]
        obtain ⟨e, he⟩ := w_dvd_psi p f O S (LL.pos l) _ (plane_block p f r g' g hg h.ge c b hcr hbr)
        exact ⟨e, he.symm⟩
      · have hv' : LL.vec l = false := by simpa using hv
        have hbr : b.val < r := by simpa [hv'] using hb
        have hcr : r ≤ c.val := by
          have := hc
          simp [hv'] at this
          omega
        rw [if_neg hv]
        obtain ⟨e, he⟩ := w_dvd_psi p f O S (LL.pos l) _ (plane_block p f r g g' hg' h.le b c hbr hcr)
        exact ⟨e, he.symm⟩
  · rw [if_neg hb]
    exact ⟨_, one_mul _⟩

def Theta {ι : Type} (A : ι → Fin k → Fin k → O) :
    MvPolynomial (ι × Fin k) (KK O) →ₐ[KK O] MvPolynomial (ι × Fin k) (KK O) :=
  aeval fun v => ∑ c : Fin k, X (v.1, c) * C (algebraMap O (KK O) (A v.1 c v.2))

lemma Theta_X {ι : Type} (A : ι → Fin k → Fin k → O) (l : ι) (b : Fin k) :
    Theta O A (X (l, b)) = ∑ c : Fin k, X (l, c) * C (algebraMap O (KK O) (A l c b)) := by
  simp only [Theta, MvPolynomial.aeval_X]

lemma Theta_C {ι : Type} (A : ι → Fin k → Fin k → O) (x : KK O) :
    Theta (ι := ι) O A (C x) = C x := by
  simp only [Theta, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

lemma liftSubst_X_vec {ι : Type} (w : O) (LL : LiftLetters ι) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p f))
    (hg : IsGLW g) (l : ι) (a : Fin k) (hv : LL.vec l = true) :
    liftSubst p f O w r LL g (X (l, a)) =
      ∑ b : Fin k, C (algebraMap O (KK O) (dW O w LL r l b)) * X (l, b) * C (sigMat p f O g⁻¹ (LL.pos l) b a) := by
  simp only [liftSubst, MvPolynomial.aeval_X]
  rw [if_pos hv, sigMat_inv p f O g hg]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  unfold dW
  by_cases hb : r ≤ b.val
  · rw [if_pos hb, if_pos (Or.inl ⟨hv, hb⟩)]
  · have hc : ¬ ((LL.vec l = true ∧ r ≤ b.val) ∨ (LL.vec l = false ∧ b.val < r)) := by
      rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact hb h
      · rw [hv] at h
        cases h
    rw [if_neg hb, if_neg hc, map_one, map_one, one_mul]

lemma liftSubst_X_cov {ι : Type} (w : O) (LL : LiftLetters ι) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p f))
    (l : ι) (a : Fin k) (hv : LL.vec l = false) :
    liftSubst p f O w r LL g (X (l, a)) =
      ∑ b : Fin k, C (algebraMap O (KK O) (dW O w LL r l b)) * X (l, b) * C (sigMat p f O g (LL.pos l) a b) := by
  simp only [liftSubst, MvPolynomial.aeval_X]
  have hv2 : ¬ (LL.vec l = true) := by simp [hv]
  rw [if_neg hv2]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  unfold dW
  by_cases hb : b.val < r
  · rw [if_pos hb, if_pos (Or.inr ⟨hv, hb⟩)]
  · have hc : ¬ ((LL.vec l = true ∧ r ≤ b.val) ∨ (LL.vec l = false ∧ b.val < r)) := by
      rintro (⟨h, _⟩ | ⟨_, h⟩)
      · rw [hv] at h
        cases h
      · exact hb h
    rw [if_neg hb, if_neg hc, map_one, map_one, one_mul]

lemma Theta_comp {ι : Type} (w : O) (LL : LiftLetters ι) (r : ℕ)
    (g g' : Matrix (Fin k) (Fin k) (WF p f)) (hg : IsGLW g) (hg' : IsGLW g') (A : ι → Fin k → Fin k → O)
    (hA : ∀ l c b, dW O w LL r l b * A l c b = dW O w LL r l c * NO p f O LL g g' l c b) :
    (Theta O A).comp (liftSubst p f O w r LL g) = liftSubst p f O w r LL g' := by
  apply MvPolynomial.algHom_ext
  rintro ⟨l, a⟩
  rw [AlgHom.comp_apply]
  by_cases hv : LL.vec l = true
  · rw [liftSubst_X_vec p f O w LL r g hg l a hv, liftSubst_X_vec p f O w LL r g' hg' l a hv]
    simp only [map_sum, map_mul, Theta_C, Theta_X, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hNO : ∀ b, NO p f O LL g g' l c b = psiO p f O (LL.pos l) ((g'⁻¹ * g) c b) := by
      intro b
      unfold NO
      rw [if_pos hv]
    have hterm : ∀ b, C (algebraMap O (KK O) (dW O w LL r l b)) * (X (l, c) * C (algebraMap O (KK O) (A l c b))) *
          C (sigMat p f O g⁻¹ (LL.pos l) b a) =
        X (l, c) * C (algebraMap O (KK O) (dW O w LL r l c) * sigMat p f O (g'⁻¹ * g) (LL.pos l) c b *
          sigMat p f O g⁻¹ (LL.pos l) b a) := by
      intro b
      have h1 := congrArg (fun x => (C (algebraMap O (KK O) x) : MvPolynomial (ι × Fin k) (KK O))) (hA l c b)
      simp only [map_mul, hNO] at h1
      rw [sigMat_apply p f O (g'⁻¹ * g)]
      simp only [map_mul]
      linear_combination (X (l, c) * C (sigMat p f O g⁻¹ (LL.pos l) b a)) * h1
    simp only [hterm]
    rw [← Finset.mul_sum, ← map_sum]
    have hsum : ∑ b, algebraMap O (KK O) (dW O w LL r l c) * sigMat p f O (g'⁻¹ * g) (LL.pos l) c b *
        sigMat p f O g⁻¹ (LL.pos l) b a = algebraMap O (KK O) (dW O w LL r l c) * sigMat p f O g'⁻¹ (LL.pos l) c a := by
      simp only [mul_assoc]
      rw [← Finset.mul_sum, ← Matrix.mul_apply, ← sigMat_mul, mul_assoc, Matrix.mul_nonsing_inv g hg, mul_one]
    rw [hsum, map_mul]
    ring
  · have hv' : LL.vec l = false := by simpa using hv
    rw [liftSubst_X_cov p f O w LL r g l a hv', liftSubst_X_cov p f O w LL r g' l a hv']
    simp only [map_sum, map_mul, Theta_C, Theta_X, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hNO : ∀ b, NO p f O LL g g' l c b = psiO p f O (LL.pos l) ((g⁻¹ * g') b c) := by
      intro b
      unfold NO
      rw [if_neg hv]
    have hterm : ∀ b, C (algebraMap O (KK O) (dW O w LL r l b)) * (X (l, c) * C (algebraMap O (KK O) (A l c b))) *
          C (sigMat p f O g (LL.pos l) a b) =
        X (l, c) * C (algebraMap O (KK O) (dW O w LL r l c) * sigMat p f O g (LL.pos l) a b *
          sigMat p f O (g⁻¹ * g') (LL.pos l) b c) := by
      intro b
      have h1 := congrArg (fun x => (C (algebraMap O (KK O) x) : MvPolynomial (ι × Fin k) (KK O))) (hA l c b)
      simp only [map_mul, hNO] at h1
      rw [sigMat_apply p f O (g⁻¹ * g')]
      simp only [map_mul]
      linear_combination (X (l, c) * C (sigMat p f O g (LL.pos l) a b)) * h1
    simp only [hterm]
    rw [← Finset.mul_sum, ← map_sum]
    have hsum : ∑ b, algebraMap O (KK O) (dW O w LL r l c) * sigMat p f O g (LL.pos l) a b *
        sigMat p f O (g⁻¹ * g') (LL.pos l) b c = algebraMap O (KK O) (dW O w LL r l c) * sigMat p f O g' (LL.pos l) a c := by
      simp only [mul_assoc]
      rw [← Finset.mul_sum, ← Matrix.mul_apply, ← sigMat_mul, ← mul_assoc, Matrix.mul_nonsing_inv g hg, one_mul]
    rw [hsum, map_mul]
    ring

lemma InWj_zero_iff {σ : Type} (w : O) (P : MvPolynomial σ (KK O)) : InWj w P 0 ↔ InA P := by
  simp only [InWj, InA, pow_zero, one_mul]

def intSub (σ : Type) : Subalgebra O (MvPolynomial σ (KK O)) :=
  goodSub (1 : O) (fun _ => 0) rfl (fun _ _ => rfl)

lemma mem_intSub {σ : Type} (P : MvPolynomial σ (KK O)) : P ∈ intSub O σ ↔ InA P := by
  unfold intSub InA
  rw [mem_goodSub]
  simp only [pow_zero, one_mul]

lemma Theta_int {ι : Type} (A : ι → Fin k → Fin k → O) (P : MvPolynomial (ι × Fin k) (KK O)) (hP : InA P) :
    InA (Theta O A P) := by
  rw [← mem_intSub]
  refine aeval_mem_sub (intSub O _) _ (fun v => ?_) P hP
  refine Subalgebra.sum_mem _ (fun c _ => Subalgebra.mul_mem _ ?_ (C_mem_sub _ _))
  exact X_mem_goodSub _ (by rfl)

theorem lift_region_plane_invariant {ι : Type} (S : UniformizedDVR p O) (LL : LiftLetters ι) (r : ℕ)
    (g g' : Matrix (Fin k) (Fin k) (WF p f)) (hg : IsGLW g) (hg' : IsGLW g')
    (h : ratPlane p f r g = ratPlane p f r g') (F : MvPolynomial (ι × Fin k) (KK O))
    (hF : InWjRg p f O S.w r LL g F 0) : InWjRg p f O S.w r LL g' F 0 := by
  unfold InWjRg at hF ⊢
  rw [InWj_zero_iff] at hF ⊢
  choose A hA using exists_A p f O S LL r g g' hg hg' h
  rw [← Theta_comp p f O S.w LL r g g' hg hg' A hA, AlgHom.comp_apply]
  exact Theta_int O A _ hF

end PartA

theorem coefficientDependence (D : Formalism.BasicNotions.D7) : CoefficientDependence D := by
  unfold CoefficientDependence
  intro p f _ O _ _ _ _ S _ _ r K ι LL g g' hg hg'
  exact ⟨fun h F => ⟨lift_region_plane_invariant p f O S LL r g g' hg hg' h F, lift_region_plane_invariant p f O S LL r g' g hg' hg h.symm F⟩,
    fun F hF m => lift_substitution_coeff_divisible p f O S.w LL r g hg F hF m⟩

end Formalism.MainNotions.LemmaBAlt
