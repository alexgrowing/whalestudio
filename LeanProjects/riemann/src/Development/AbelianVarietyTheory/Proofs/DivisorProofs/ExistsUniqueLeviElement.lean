import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.PlaneLeviExt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma cA_incl (σ : E →ₐ[F] E) (e : E) :
    cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

lemma incM_mul {l m n : Type} [Fintype m] (A : Matrix l m E) (B : Matrix m n E) :
    incM F (A * B) = incM F A * incM F B := by
  unfold incM; exact Matrix.map_mul (f := inclR (F := F) (AF F))

lemma incM_transpose {m n : Type} (A : Matrix m n E) : incM F Aᵀ = (incM F A)ᵀ := rfl

lemma cA_incM (σ : E →ₐ[F] E) {m n : Type} (A : Matrix m n E) :
    (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j; simp [incM, cA_incl]

lemma form_swap (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

lemma entry (σ : E →ₐ[F] E) {n p q : Type} [Fintype n] (J : Matrix n n E) (A : Matrix n p E) (B : Matrix n q E) (k : p) (l : q) :
    (Aᵀ * J * B.map σ) k l = (fun i => A i k) ⬝ᵥ J *ᵥ fun i => σ (B i l) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

lemma not_line {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E) (u : Fin n → E)
    (hu : ∀ a : E, a • u ∈ L) : u = 0 := by
  by_contra h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  have hfg : (L.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) i)).FG := hL.fg.map _
  have htop : L.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) i) = ⊤ := by
    refine eq_top_iff.mpr fun z _ => ?_
    refine ⟨(z / u i) • u, hu _, ?_⟩
    simp [div_mul_cancel₀ _ hi]
  rw [htop] at hfg
  have : Module.Finite (𝓞 E) E := ⟨hfg⟩
  have : Algebra.IsIntegral (𝓞 E) E := Algebra.IsIntegral.of_finite _ _
  exact NumberField.RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective (𝓞 E) E) (Field.toIsField E))

section Plane
variable {d d₁ : ℕ}

def twoCols (H' : Plane E d d₁) : Matrix (Fin d) (Fin 2) E := Matrix.of fun i k => ![H'.x i, H'.y i] k

def frame (H' : Plane E d d₁) : Matrix (Fin d) (Fin d₁ ⊕ Fin 2) E := Matrix.fromCols H'.ι (twoCols H')

def hyp : Matrix (Fin 2) (Fin 2) E := !![0, 1; -1, 0]

lemma gram_frame (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {W : Spc F E d} {W₁ : Spc F E d₁}
    {H' : Plane E d d₁} {i₀ i₁ r' s' : ℕ} (hW : W.IsSkew σ B r' s') (hA : H'.IsAdapted σ B W W₁ i₀ i₁) :
    (frame H')ᵀ * W.J * (frame H').map σ = Matrix.fromBlocks W₁.J 0 0 hyp := by
  have hcol : ∀ k, (fun i => H'.ι i k) = H'.ι *ᵥ Pi.single k 1 := fun k => by
    ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have ho : ∀ l, form σ W.J (H'.ι.col l) H'.x = 0 ∧ form σ W.J (H'.ι.col l) H'.y = 0 := fun l => by
    have hc : H'.ι.col l = H'.ι *ᵥ Pi.single l 1 := hcol l
    rw [hc]; exact hA.orth _
  have hxy : form σ W.J H'.y H'.x = -1 := by
    rw [form_swap σ hσ W.J hW.skew, hA.xy, map_one]
  ext a b
  rw [entry]
  change form σ W.J _ _ = _
  rcases a with k | k <;> rcases b with l | l
  · rw [← hA.gram, Matrix.fromBlocks_apply₁₁, entry]; rfl
  · fin_cases l
    · simp only [frame, twoCols, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, Matrix.of_apply]; exact (ho k).1
    · simp only [frame, twoCols, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, Matrix.of_apply]; exact (ho k).2
  · fin_cases k
    · simp [frame, twoCols, hcol]
      rw [form_swap σ hσ W.J hW.skew]; simp [(ho l).1]
    · simp [frame, twoCols, hcol]
      rw [form_swap σ hσ W.J hW.skew]; simp [(ho l).2]
  · fin_cases k <;> fin_cases l
    · simpa [frame, twoCols, hyp] using hA.xx
    · simpa [frame, twoCols, hyp] using hA.xy
    · simpa [frame, twoCols, hyp] using hxy
    · simpa [frame, twoCols, hyp] using hA.yy

lemma frame_mulVec_eq_zero (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {W : Spc F E d}
    {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ r' s' r₁ s₁ : ℕ} (hW : W.IsSkew σ B r' s')
    (hW₁ : W₁.IsSkew σ B r₁ s₁) (hA : H'.IsAdapted σ B W W₁ i₀ i₁) (v : Fin d₁ ⊕ Fin 2 → E)
    (hv : frame H' *ᵥ v = 0) : v = 0 := by
  have hg := gram_frame σ hσ B hW hA
  have h0 : v ᵥ* Matrix.fromBlocks W₁.J 0 0 hyp = 0 := by
    rw [← hg, Matrix.mul_assoc, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hv, Matrix.zero_vecMul]
  have h1 : v (Sum.inr 0) = 0 ∧ v (Sum.inr 1) = 0 := by
    have a := congrFun h0 (Sum.inr 0)
    have b := congrFun h0 (Sum.inr 1)
    simp [Matrix.vecMul_fromBlocks, hyp, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at a b
    exact ⟨b, a⟩
  have h2 : (fun k : Fin 2 => v (Sum.inr k)) = 0 := by
    ext k; fin_cases k
    · exact h1.1
    · exact h1.2
  have hu : H'.ι *ᵥ (fun k => v (Sum.inl k)) = 0 := by
    have : frame H' *ᵥ v = H'.ι *ᵥ (fun k => v (Sum.inl k)) + twoCols H' *ᵥ (fun k => v (Sum.inr k)) := by
      rw [frame, Matrix.fromCols_mulVec]; rfl
    rw [this, h2, Matrix.mulVec_zero, add_zero] at hv
    exact hv
  have hu0 := not_line W₁.L hW₁.lat (fun k => v (Sum.inl k)) fun a =>
    (hA.low _).mpr (by rw [Matrix.mulVec_smul, hu, smul_zero]; exact zero_mem _)
  ext (k | k)
  · exact congrFun hu0 k
  · exact congrFun h2 k

def num (hd : d = d₁ + 2) : Fin d₁ ⊕ Fin 2 ≃ Fin d := finSumFinEquiv.trans (finCongr hd.symm)

def sq (hd : d = d₁ + 2) (H' : Plane E d d₁) : Matrix (Fin d) (Fin d) E := (frame H').submatrix id (num hd).symm

def coframe (hd : d = d₁ + 2) (H' : Plane E d d₁) : Matrix (Fin d₁ ⊕ Fin 2) (Fin d) E :=
  (sq hd H')⁻¹.submatrix (num hd) id

lemma isUnit_sq (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {W : Spc F E d}
    {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ r' s' r₁ s₁ : ℕ} (hW : W.IsSkew σ B r' s')
    (hW₁ : W₁.IsSkew σ B r₁ s₁) (hA : H'.IsAdapted σ B W W₁ i₀ i₁) : IsUnit (sq hA.rank H') := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro a b hab
  have h0 : sq hA.rank H' *ᵥ (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
  rw [sq, Matrix.submatrix_mulVec_equiv] at h0
  have h1 := frame_mulVec_eq_zero σ hσ B hW hW₁ hA _ (by simpa using h0)
  have h2 : a - b = 0 := by
    ext i
    have := congrFun h1 ((num hA.rank).symm i)
    simpa using this
  exact sub_eq_zero.mp h2

lemma frame_eq (hd : d = d₁ + 2) (H' : Plane E d d₁) : frame H' = (sq hd H').submatrix id (num hd) := by
  ext i j; simp [sq]

lemma frame_mul_coframe (hd : d = d₁ + 2) (H' : Plane E d d₁) (hu : IsUnit (sq hd H')) :
    frame H' * coframe hd H' = 1 := by
  rw [frame_eq hd, coframe, Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]
  simp

lemma coframe_mul_frame (hd : d = d₁ + 2) (H' : Plane E d d₁) (hu : IsUnit (sq hd H')) :
    coframe hd H' * frame H' = 1 := by
  rw [frame_eq hd, coframe, show (sq hd H').submatrix id (num hd) = (sq hd H').submatrix (Equiv.refl _) (num hd) from rfl,
    show (sq hd H')⁻¹.submatrix (num hd) id = (sq hd H')⁻¹.submatrix (num hd) (Equiv.refl _) from rfl,
    Matrix.submatrix_mul_equiv, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]
  exact Matrix.submatrix_one_equiv _

end Plane

section Adelic
variable {d d₁ : ℕ}

def blk (g : Matrix (Fin d₁) (Fin d₁) (AE F E)) : Matrix (Fin d₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E) :=
  Matrix.fromBlocks g 0 0 1

lemma blk_mul (g g' : Matrix (Fin d₁) (Fin d₁) (AE F E)) : blk g * blk g' = blk (g * g') := by
  simp [blk, Matrix.fromBlocks_multiply]

lemma blk_one : blk (1 : Matrix (Fin d₁) (Fin d₁) (AE F E)) = 1 := Matrix.fromBlocks_one

def leviM (hd : d = d₁ + 2) (H' : Plane E d d₁) (g : Matrix (Fin d₁) (Fin d₁) (AE F E)) :
    Matrix (Fin d) (Fin d) (AE F E) :=
  incM F (frame H') * blk g * incM F (coframe hd H')

variable {hd : d = d₁ + 2} {H' : Plane E d d₁}

lemma incM_one {n : Type} [Fintype n] [DecidableEq n] : incM F (1 : Matrix n n E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

lemma S_T (hu : IsUnit (sq hd H')) : incM F (frame H') * incM F (coframe hd H') = 1 := by
  rw [← incM_mul, frame_mul_coframe hd H' hu, incM_one]

lemma T_S (hu : IsUnit (sq hd H')) : incM F (coframe hd H') * incM F (frame H') = 1 := by
  rw [← incM_mul, coframe_mul_frame hd H' hu, incM_one]

lemma leviM_mul (hu : IsUnit (sq hd H')) (g g' : Matrix (Fin d₁) (Fin d₁) (AE F E)) :
    leviM (F := F) hd H' g * leviM hd H' g' = leviM hd H' (g * g') := by
  simp only [leviM, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (coframe hd H')), T_S hu, Matrix.one_mul, ← Matrix.mul_assoc (blk g), blk_mul]

lemma leviM_one (hu : IsUnit (sq hd H')) : leviM (F := F) hd H' 1 = 1 := by
  rw [leviM, blk_one, Matrix.mul_one, S_T hu]

lemma leviM_frame (hu : IsUnit (sq hd H')) (g : Matrix (Fin d₁) (Fin d₁) (AE F E)) :
    leviM hd H' g * incM F (frame H') = incM F (frame H') * blk g := by
  rw [leviM, Matrix.mul_assoc, T_S hu, Matrix.mul_one]

lemma incM_frame : incM F (frame H') = Matrix.fromCols (incM F H'.ι) (incM F (twoCols H')) := by
  ext i (j | j) <;> rfl

lemma levi_cols (m : Matrix (Fin d) (Fin d) (AE F E)) (g : Matrix (Fin d₁) (Fin d₁) (AE F E)) :
    m * incM F (frame H') = incM F (frame H') * blk g ↔
      (m *ᵥ incV F H'.x = incV F H'.x ∧ m *ᵥ incV F H'.y = incV F H'.y) ∧ m * incM F H'.ι = incM F H'.ι * g := by
  rw [incM_frame, Matrix.mul_fromCols, blk, Matrix.fromCols_mul_fromBlocks]
  simp only [Matrix.mul_zero, add_zero, Matrix.mul_one, zero_add]
  rw [Matrix.fromCols_inj.eq_iff]
  have : m * incM F (twoCols H') = incM F (twoCols H') ↔
      (m *ᵥ incV F H'.x = incV F H'.x ∧ m *ᵥ incV F H'.y = incV F H'.y) := by
    constructor
    · intro h
      exact ⟨funext fun i => congrFun (congrFun h i) 0, funext fun i => congrFun (congrFun h i) 1⟩
    · rintro ⟨h1, h2⟩
      ext i k
      fin_cases k
      · exact congrFun h1 i
      · exact congrFun h2 i
  rw [this, and_comm]

lemma leviM_unitary (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {W : Spc F E d}
    {W₁ : Spc F E d₁} {i₀ i₁ r' s' : ℕ} (hW : W.IsSkew σ B r' s') (hA : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hu : IsUnit (sq hd H')) (g : Matrix (Fin d₁) (Fin d₁) (AE F E))
    (hg : gᵀ * incM F W₁.J * g.map (cA σ) = incM F W₁.J) :
    (leviM hd H' g)ᵀ * incM F W.J * (leviM hd H' g).map (cA σ) = incM F W.J := by
  have hmap : ∀ {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) (Y : Matrix b c (AE F E)),
      (X * Y).map (cA σ) = X.map (cA σ) * Y.map (cA σ) := fun X Y => Matrix.map_mul (f := (cA σ).toRingHom)
  have hG : (incM F (frame H'))ᵀ * incM F W.J * (incM F (frame H')).map (cA σ) =
      incM F (Matrix.fromBlocks W₁.J 0 0 hyp) := by
    rw [← gram_frame σ hσ B hW hA, incM_mul, incM_mul, incM_transpose, cA_incM]
  have hJ : incM F W.J = (incM F (coframe hd H'))ᵀ * incM F (Matrix.fromBlocks W₁.J 0 0 hyp) *
      (incM F (coframe hd H')).map (cA σ) := by
    have h1 : (incM F (frame H') * incM F (coframe hd H'))ᵀ * incM F W.J *
        (incM F (frame H') * incM F (coframe hd H')).map (cA σ) = incM F W.J := by
      rw [S_T hu, Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
    calc incM F W.J = (incM F (frame H') * incM F (coframe hd H'))ᵀ * incM F W.J *
          (incM F (frame H') * incM F (coframe hd H')).map (cA σ) := h1.symm
      _ = (incM F (coframe hd H'))ᵀ * ((incM F (frame H'))ᵀ * incM F W.J * (incM F (frame H')).map (cA σ)) *
          (incM F (coframe hd H')).map (cA σ) := by
        rw [Matrix.transpose_mul, hmap]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hG]
  have hB : (blk g)ᵀ * incM F (Matrix.fromBlocks W₁.J 0 0 hyp) * (blk g).map (cA σ) =
      incM F (Matrix.fromBlocks W₁.J 0 0 hyp) := by
    have e1 : incM F (Matrix.fromBlocks W₁.J 0 0 hyp) = Matrix.fromBlocks (incM F W₁.J) 0 0 (incM F hyp) := by
      simp [incM, Matrix.fromBlocks_map]
    have e2 : (blk g).map (cA σ) = Matrix.fromBlocks (g.map (cA σ)) 0 0 1 := by
      rw [blk, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _),
        Matrix.map_one _ (map_zero _) (map_one _)]
    rw [e1, e2, blk, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [hg]
  calc (leviM hd H' g)ᵀ * incM F W.J * (leviM hd H' g).map (cA σ)
      = (incM F (coframe hd H'))ᵀ * ((blk g)ᵀ * ((incM F (frame H'))ᵀ * incM F W.J *
          (incM F (frame H')).map (cA σ)) * (blk g).map (cA σ)) * (incM F (coframe hd H')).map (cA σ) := by
        simp only [leviM, Matrix.transpose_mul, hmap, Matrix.mul_assoc]
    _ = incM F W.J := by rw [hG, hB, ← hJ]

end Adelic

theorem levi_existsUnique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁)
    (i₀ i₁ r' s' r₁ s₁ : ℕ), (∀ z : E, σ (σ z) = z) → W.IsSkew σ B r' s' → W₁.IsSkew σ B r₁ s₁ →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ h₁ : UA σ W₁.J, ∃ m : UA σ W.J, IsLevi H' 1 h₁ m ∧
      ∀ m' : UA σ W.J, IsLevi H' 1 h₁ m' → m' = m := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r' s' r₁ s₁ hσ hW hW₁ hA h₁
  have hu := isUnit_sq σ hσ B hW hW₁ hA
  have hinv : mat h₁ * mat h₁⁻¹ = 1 := by
    show ((h₁.1 * (h₁⁻¹).1 : GL (Fin d₁) (AE F E)) : Matrix (Fin d₁) (Fin d₁) (AE F E)) = 1
    rw [← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hinv' : mat h₁⁻¹ * mat h₁ = 1 := by
    show (((h₁⁻¹).1 * h₁.1 : GL (Fin d₁) (AE F E)) : Matrix (Fin d₁) (Fin d₁) (AE F E)) = 1
    rw [← Subgroup.coe_mul, inv_mul_cancel]; rfl
  let mU : GL (Fin d) (AE F E) := ⟨leviM hA.rank H' (mat h₁), leviM hA.rank H' (mat h₁⁻¹),
    by rw [leviM_mul hu, hinv, leviM_one hu], by rw [leviM_mul hu, hinv', leviM_one hu]⟩
  have hmem : mU ∈ UG (cA σ) (incM F W.J) := leviM_unitary σ hσ B hW hA hu (mat h₁) h₁.2
  have hc := (levi_cols (leviM hA.rank H' (mat h₁)) (mat h₁)).mp (leviM_frame hu (mat h₁))
  refine ⟨⟨mU, hmem⟩, ⟨by simp only [Units.val_one, one_smul]; exact hc.1.1,
    by simp only [inv_one, Units.val_one, map_one, one_smul]; exact hc.1.2, hc.2⟩, fun m' hm' => ?_⟩
  have h1 : mat m' * incM F (frame H') = incM F (frame H') * blk (mat h₁) :=
    (levi_cols _ _).mpr ⟨⟨by simpa using hm'.1, by simpa using hm'.2.1⟩, hm'.2.2⟩
  have h2 : mat m' = leviM hA.rank H' (mat h₁) := by
    calc mat m' = mat m' * (incM F (frame H') * incM F (coframe hA.rank H')) := by rw [S_T hu, Matrix.mul_one]
      _ = leviM hA.rank H' (mat h₁) := by rw [← Matrix.mul_assoc, h1]; rfl
  exact Subtype.ext (Units.ext h2)

end GlobalTheory.PlaneLeviExt
