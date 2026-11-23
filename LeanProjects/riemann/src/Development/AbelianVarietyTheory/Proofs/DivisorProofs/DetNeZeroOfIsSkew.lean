import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.TorusCentre

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_zero_of_isSkew {B : Base F E} {d₁ : ℕ} {W₁ : Spc F E d₁} {r s : ℕ} (h : W₁.IsSkew σ B r s) :
    W₁.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, A, hA⟩ := h.sig w
  set φ := (B.emb w).1
  let e : Fin r ⊕ Fin s ≃ Fin d₁ := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin d₁) (Fin d₁) ℂ := A.submatrix id e.symm
  have h2 : A'ᵀ * (Complex.I • W₁.J.map φ) * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply]
  have hD : ((Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  rw [← h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_smul] at hD
  intro h0
  apply hD
  have : (W₁.J.map φ).det = φ W₁.J.det := by
    simp [RingHom.map_det]
  rw [this, h0]
  simp

theorem sigma_sigma (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem form_swap (hσ : ∀ x, σ (σ x) = x) {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (a b : Fin d → E) : form σ J b a = -σ (form σ J a b) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem mulVec_dot {m n : Type} [Fintype m] [Fintype n] {R : Type} [CommRing R] (A : Matrix m n R) (u : n → R) (w : m → R) :
    (A *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Aᵀ *ᵥ w) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

section Adapted

variable {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} {i₀ i₁ : ℕ}

theorem orth_alt (hH : H.IsAdapted σ B W W₁ i₀ i₁) : H.ιᵀ *ᵥ (W.J *ᵥ fun i => σ (H.x i)) = 0 := by
  ext l
  have := (hH.orth (Pi.single l 1)).1
  rw [form, mulVec_dot, single_dotProduct, one_mul] at this
  simpa using this

theorem orth_y (hH : H.IsAdapted σ B W W₁ i₀ i₁) : H.ιᵀ *ᵥ (W.J *ᵥ fun i => σ (H.y i)) = 0 := by
  ext l
  have := (hH.orth (Pi.single l 1)).2
  rw [form, mulVec_dot, single_dotProduct, one_mul] at this
  simpa using this

theorem form_single (a : Fin d → E) (l : Fin d₁) :
    form σ W.J a (H.ι *ᵥ Pi.single l 1) = (a ᵥ* (W.J * H.ι.map σ)) l := by
  have : (fun i => σ ((H.ι *ᵥ Pi.single l 1) i)) = H.ι.map σ *ᵥ Pi.single l 1 := by
    ext i; simp [Matrix.mulVec_single]
  rw [form, this, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, dotProduct_single, mul_one]

theorem vecMul_J_map_eq_zero_of_isAdapted (hσ : ∀ x, σ (σ x) = x) (hW : ∀ i j, σ (W.J j i) = -W.J i j) (hH : H.IsAdapted σ B W W₁ i₀ i₁) :
    H.x ᵥ* (W.J * H.ι.map σ) = 0 := by
  ext l
  rw [← form_single, form_swap hσ hW, (hH.orth _).1, map_zero, neg_zero, Pi.zero_apply]

theorem orth_y' (hσ : ∀ x, σ (σ x) = x) (hW : ∀ i j, σ (W.J j i) = -W.J i j) (hH : H.IsAdapted σ B W W₁ i₀ i₁) :
    H.y ᵥ* (W.J * H.ι.map σ) = 0 := by
  ext l
  rw [← form_single, form_swap hσ hW, (hH.orth _).2, map_zero, neg_zero, Pi.zero_apply]

theorem form_yx (hσ : ∀ x, σ (σ x) = x) (hW : ∀ i j, σ (W.J j i) = -W.J i j) (hH : H.IsAdapted σ B W W₁ i₀ i₁) :
    form σ W.J H.y H.x = -1 := by
  rw [form_swap hσ hW, hH.xy, map_one]

end Adapted

section Gen

variable {R : Type} [CommRing R] (c : R →+* R) {d d₁ : ℕ} {J : Matrix (Fin d) (Fin d) R} {I : Matrix (Fin d) (Fin d₁) R}
  {J₁ : Matrix (Fin d₁) (Fin d₁) R} {X Y : Fin d → R}

theorem map_mulVec_fun (u : Fin d₁ → R) : (fun i => c ((I *ᵥ u) i)) = I.map c *ᵥ fun i => c (u i) := by
  ext i; exact RingHom.map_mulVec c I u i

theorem dotProduct_J_c_eq_neg_of_pairing (h3x : Iᵀ *ᵥ (J *ᵥ fun i => c (X i)) = 0) (hxx : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0)
    (hyx : Y ⬝ᵥ J *ᵥ (fun i => c (X i)) = -1) (u : Fin d₁ → R) (a b : R) :
    (I *ᵥ u + a • X + b • Y) ⬝ᵥ J *ᵥ (fun i => c (X i)) = -b := by
  rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, mulVec_dot, h3x, hxx, hyx]
  simp

theorem pair_y (h3y : Iᵀ *ᵥ (J *ᵥ fun i => c (Y i)) = 0) (hxy : X ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 1)
    (hyy : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0) (u : Fin d₁ → R) (a b : R) :
    (I *ᵥ u + a • X + b • Y) ⬝ᵥ J *ᵥ (fun i => c (Y i)) = a := by
  rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, mulVec_dot, h3y, hxy, hyy]
  simp

theorem pair_ι (h1 : Iᵀ * J * I.map c = J₁) (h4x : X ᵥ* (J * I.map c) = 0) (h4y : Y ᵥ* (J * I.map c) = 0)
    (u : Fin d₁ → R) (a b : R) (u' : Fin d₁ → R) :
    (I *ᵥ u + a • X + b • Y) ⬝ᵥ J *ᵥ (fun i => c ((I *ᵥ u') i)) = (u ᵥ* J₁) ⬝ᵥ fun i => c (u' i) := by
  rw [map_mulVec_fun, Matrix.mulVec_mulVec, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
    Matrix.dotProduct_mulVec X, Matrix.dotProduct_mulVec Y, h4x, h4y, mulVec_dot, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, h1, Matrix.dotProduct_mulVec]
  simp

theorem eq_zero_of_pair (hJ : IsUnit J₁.det) (u : Fin d₁ → R) (h : ∀ u' : Fin d₁ → R, (u ᵥ* J₁) ⬝ᵥ (fun i => c (u' i)) = 0) :
    u = 0 := by
  have h0 : u ᵥ* J₁ = 0 := by
    ext l
    have := h (Pi.single l 1)
    have e : (fun i => c ((Pi.single l (1 : R) : Fin d₁ → R) i)) = Pi.single l 1 := by
      ext i; by_cases hi : i = l
      · subst hi; simp
      · simp [Pi.single_apply, hi]
    rw [e, dotProduct_single, mul_one] at this
    simpa using this
  have : u = (u ᵥ* J₁) ᵥ* J₁⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJ, Matrix.vecMul_one]
  rw [this, h0, Matrix.zero_vecMul]

end Gen

section Transfer

theorem cA_inclR (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem cA_incV {d : ℕ} (v : Fin d → E) : (fun i => (cA σ).toRingHom (incV F v i)) = incV F (fun i => σ (v i)) := by
  ext i; simp [incV, cA_inclR]

theorem incM_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) (v : Fin n → E) : incM F A *ᵥ incV F v = incV F (A *ᵥ v) := by
  ext i; exact (RingHom.map_mulVec (inclR (F := F) (AF F)) A v i).symm

theorem incV_dot {n : ℕ} (a b : Fin n → E) : incV F a ⬝ᵥ incV F b = inclR (F := F) (AF F) (a ⬝ᵥ b) :=
  (RingHom.map_dotProduct (inclR (F := F) (AF F)) a b).symm

theorem incV_vecMul {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) (v : Fin m → E) : incV F v ᵥ* incM F A = incV F (v ᵥ* A) := by
  ext i; exact (RingHom.map_vecMul (inclR (F := F) (AF F)) A v i).symm

theorem incM_mul {m n p : ℕ} (A : Matrix (Fin m) (Fin n) E) (C : Matrix (Fin n) (Fin p) E) :
    incM F (A * C) = incM F A * incM F C := Matrix.map_mul

theorem incM_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) : incM F Aᵀ = (incM F A)ᵀ := rfl

theorem incM_cA {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) : (incM F A).map (cA σ).toRingHom = incM F (A.map σ) := by
  ext i j; simp [incM, cA_inclR]

theorem incV_zero {n : ℕ} : incV F (0 : Fin n → E) = 0 := by ext i; simp [incV]

theorem incV_form {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (a b : Fin d → E) :
    incV F a ⬝ᵥ incM F J *ᵥ (fun i => (cA σ).toRingHom (incV F b i)) = inclR (F := F) (AF F) (form σ J a b) := by
  rw [cA_incV, incM_mulVec, incV_dot, form]

end Transfer

section Decomp

variable {R : Type} [CommRing R] {d d₁ : ℕ} {I : Matrix (Fin d) (Fin d₁) R} {X Y : Fin d → R}

theorem decomp_all (h : ∀ i, ∃ (u : Fin d₁ → R) (a b : R), (Pi.single i 1 : Fin d → R) = I *ᵥ u + a • X + b • Y)
    (v : Fin d → R) : ∃ (u : Fin d₁ → R) (a b : R), v = I *ᵥ u + a • X + b • Y := by
  choose u a b hu using h
  refine ⟨∑ i, v i • u i, ∑ i, v i * a i, ∑ i, v i * b i, ?_⟩
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin d → R) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  refine hv.trans ?_
  simp_rw [hu, smul_add, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_add_distrib, Finset.sum_smul, smul_smul]

theorem mat_ext_of_decomp (h : ∀ v : Fin d → R, ∃ (u : Fin d₁ → R) (a b : R), v = I *ᵥ u + a • X + b • Y)
    {A C : Matrix (Fin d) (Fin d) R} (hι : ∀ u, A *ᵥ (I *ᵥ u) = C *ᵥ (I *ᵥ u)) (hx : A *ᵥ X = C *ᵥ X)
    (hy : A *ᵥ Y = C *ᵥ Y) : A = C := by
  have hv : ∀ v, A *ᵥ v = C *ᵥ v := by
    intro v
    obtain ⟨u, a, b, rfl⟩ := h v
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hι, hx, hy]
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

end Decomp

section Span

variable {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} {i₀ i₁ : ℕ}

theorem inj_E (hσ : ∀ x, σ (σ x) = x) (hW : ∀ i j, σ (W.J j i) = -W.J i j) (hH : H.IsAdapted σ B W W₁ i₀ i₁)
    (hJ₁ : W₁.J.det ≠ 0) (u : Fin d₁ → E) (a b : E) (h0 : H.ι *ᵥ u + a • H.x + b • H.y = 0) :
    u = 0 ∧ a = 0 ∧ b = 0 := by
  let c : E →+* E := σ.toRingHom
  have hb := dotProduct_J_c_eq_neg_of_pairing c (I := H.ι) (J := W.J) (X := H.x) (Y := H.y) (orth_alt hH) hH.xx (form_yx hσ hW hH) u a b
  have ha := pair_y c (I := H.ι) (J := W.J) (X := H.x) (Y := H.y) (orth_y hH) hH.xy hH.yy u a b
  have hu := pair_ι c (I := H.ι) (J := W.J) (X := H.x) (Y := H.y) hH.gram (vecMul_J_map_eq_zero_of_isAdapted hσ hW hH) (orth_y' hσ hW hH) u a b
  rw [h0, zero_dotProduct] at hb ha
  simp only [h0, zero_dotProduct] at hu
  refine ⟨eq_zero_of_pair c (isUnit_iff_ne_zero.2 hJ₁) u fun u' => (hu u').symm, ha.symm, ?_⟩
  exact neg_eq_zero.1 hb.symm

theorem span_E (hσ : ∀ x, σ (σ x) = x) (hW : ∀ i j, σ (W.J j i) = -W.J i j) (hH : H.IsAdapted σ B W W₁ i₀ i₁)
    (hJ₁ : W₁.J.det ≠ 0) (w : Fin d → E) : ∃ (u : Fin d₁ → E) (a b : E), w = H.ι *ᵥ u + a • H.x + b • H.y := by
  let L : ((Fin d₁ → E) × E × E) →ₗ[E] (Fin d → E) :=
    (Matrix.mulVecLin H.ι).coprod ((LinearMap.id.smulRight H.x).coprod (LinearMap.id.smulRight H.y))
  have hL : ∀ p, L p = H.ι *ᵥ p.1 + p.2.1 • H.x + p.2.2 • H.y := by
    intro p; simp [L, add_assoc]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hL] at hp
    obtain ⟨h1, h2, h3⟩ := inj_E hσ hW hH hJ₁ _ _ _ hp
    exact Prod.ext h1 (Prod.ext h2 h3)
  have hdim : Module.finrank E ((Fin d₁ → E) × E × E) = Module.finrank E (Fin d → E) := by
    simp [Module.finrank_prod, hH.rank]
  obtain ⟨p, hp⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj w
  exact ⟨p.1, p.2.1, p.2.2, by rw [← hp, hL]⟩

theorem span_A (hσ : ∀ x, σ (σ x) = x) (hW : ∀ i j, σ (W.J j i) = -W.J i j) (hH : H.IsAdapted σ B W W₁ i₀ i₁)
    (hJ₁ : W₁.J.det ≠ 0) (v : Fin d → AE F E) :
    ∃ (u : Fin d₁ → AE F E) (a b : AE F E), v = incM F H.ι *ᵥ u + a • incV F H.x + b • incV F H.y := by
  refine decomp_all (fun i => ?_) v
  obtain ⟨u, a, b, hw⟩ := span_E hσ hW hH hJ₁ (Pi.single i 1)
  refine ⟨incV F u, inclR (F := F) (AF F) a, inclR (F := F) (AF F) b, ?_⟩
  have e1 : (Pi.single i 1 : Fin d → AE F E) = incV F (Pi.single i 1) := by
    ext j; by_cases hj : j = i
    · subst hj; simp [incV]
    · simp [incV, Pi.single_apply, hj]
  rw [e1, hw, incM_mulVec]
  ext j; simp [incV]

end Span

section Group

variable {d : ℕ} {J : Matrix (Fin d) (Fin d) E}

theorem mat_mul (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : UA σ J) = 1 := rfl

theorem mat_pow (g : UA σ J) (N : ℕ) : mat (g ^ N) = mat g ^ N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [pow_succ, mat_mul, ih, pow_succ]

theorem mat_inj {g h : UA σ J} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

theorem unitary_pair (g : UA σ J) (a b : Fin d → AE F E) :
    (mat g *ᵥ a) ⬝ᵥ incM F J *ᵥ (fun i => (cA σ).toRingHom ((mat g *ᵥ b) i)) =
      a ⬝ᵥ incM F J *ᵥ (fun i => (cA σ).toRingHom (b i)) := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ).toRingHom = incM F J := g.2
  rw [map_mulVec_fun, mulVec_dot, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

end Group

section Step

variable {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} {i₀ i₁ : ℕ}

theorem fixes_y (hσ : ∀ x, σ (σ x) = x) (hW : ∀ i j, σ (W.J j i) = -W.J i j) (hH : H.IsAdapted σ B W W₁ i₀ i₁)
    (hJ₁ : W₁.J.det ≠ 0) (q : UA σ W.J) (hqx : mat q *ᵥ incV F H.x = incV F H.x)
    (hqι : ∀ z, mat q *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) :
    ∃ β : AE F E, mat q *ᵥ incV F H.y = incV F H.y + β • incV F H.x := by
  let c : AE F E →+* AE F E := (cA σ).toRingHom
  obtain ⟨u, a, b, hv⟩ := span_A hσ hW hH hJ₁ (mat q *ᵥ incV F H.y - incV F H.y)
  have h3x : (incM F H.ι)ᵀ *ᵥ (incM F W.J *ᵥ fun i => c (incV F H.x i)) = 0 := by
    rw [cA_incV, incM_mulVec, ← incM_transpose, incM_mulVec, orth_alt hH, incV_zero]
  have hxx : incV F H.x ⬝ᵥ incM F W.J *ᵥ (fun i => c (incV F H.x i)) = 0 := by
    rw [incV_form, hH.xx, map_zero]
  have hyx : incV F H.y ⬝ᵥ incM F W.J *ᵥ (fun i => c (incV F H.x i)) = -1 := by
    rw [incV_form, form_yx hσ hW hH, map_neg, map_one]
  have h1 : (incM F H.ι)ᵀ * incM F W.J * (incM F H.ι).map c = incM F W₁.J := by
    rw [incM_cA, ← incM_transpose, ← incM_mul, ← incM_mul, hH.gram]
  have h4x : incV F H.x ᵥ* (incM F W.J * (incM F H.ι).map c) = 0 := by
    rw [incM_cA, ← incM_mul, incV_vecMul, vecMul_J_map_eq_zero_of_isAdapted hσ hW hH, incV_zero]
  have h4y : incV F H.y ᵥ* (incM F W.J * (incM F H.ι).map c) = 0 := by
    rw [incM_cA, ← incM_mul, incV_vecMul, orth_y' hσ hW hH, incV_zero]
  have hb := dotProduct_J_c_eq_neg_of_pairing c h3x hxx hyx u a b
  have hu := pair_ι c h1 h4x h4y u a b
  rw [← hv, sub_dotProduct] at hb
  conv at hb => lhs; lhs; rw [← hqx]
  rw [unitary_pair, sub_self] at hb
  have hu' : ∀ u' : Fin d₁ → AE F E, (u ᵥ* incM F W₁.J) ⬝ᵥ (fun i => c (u' i)) = 0 := by
    intro u'
    rw [← hu u', ← hv, sub_dotProduct]
    conv => lhs; lhs; rw [← hqι u']
    rw [unitary_pair, sub_self]
  have hdet : IsUnit (incM F W₁.J).det := by
    have : (incM F W₁.J).det = inclR (F := F) (AF F) W₁.J.det := (RingHom.map_det _ _).symm
    rw [this]
    exact (isUnit_iff_ne_zero.2 hJ₁).map _
  have hu0 := eq_zero_of_pair c hdet u hu'
  have hb0 : b = 0 := neg_eq_zero.1 hb.symm
  refine ⟨a, ?_⟩
  rw [hu0, hb0, Matrix.mulVec_zero, zero_add, zero_smul, add_zero] at hv
  rw [← hv]; abel

end Step

section Pow

variable {R : Type} [CommRing R] {d : ℕ}

theorem pow_fix (Q : Matrix (Fin d) (Fin d) R) (v : Fin d → R) (h : Q *ᵥ v = v) (N : ℕ) : Q ^ N *ᵥ v = v := by
  induction N with
  | zero => simp
  | succ N ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, ih]

theorem pow_shear (Q : Matrix (Fin d) (Fin d) R) (X Y : Fin d → R) (β : R) (hx : Q *ᵥ X = X) (hy : Q *ᵥ Y = Y + β • X)
    (N : ℕ) : Q ^ N *ᵥ Y = Y + ((N : R) * β) • X := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_add, Matrix.mulVec_smul, ih, pow_fix Q X hx]
    push_cast
    rw [add_mul, one_mul, add_smul, add_assoc]

end Pow

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ (q : UA σ W.J), mat q *ᵥ incV F H'.x = incV F H'.x → (∀ z, mat q *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z) →
      ∀ (k : ℕ) (t : (AE F E)ˣ), 0 < k → t.1 = (k : AE F E) → ∀ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m → m * q * m⁻¹ = q ^ (k * k) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ q hqx hqι k t hk ht m hm
  have hσ := sigma_sigma hP.base.cm
  have hW := hP.skew.skew
  have hJ₁ := det_ne_zero_of_isSkew hP₁.skew
  obtain ⟨β, hβ⟩ := fixes_y hσ hW hH hJ₁ q hqx hqι
  obtain ⟨hmx, hmy, hmι⟩ := hm
  rw [mat_one, Matrix.mul_one] at hmι
  have hMι : ∀ u, mat m *ᵥ (incM F H'.ι *ᵥ u) = incM F H'.ι *ᵥ u := by
    intro u; rw [Matrix.mulVec_mulVec, hmι]
  have hs : cA σ (t⁻¹).1 * (k : AE F E) = 1 := by
    rw [← map_natCast (cA σ) k, ← map_mul, ← ht, Units.inv_mul, map_one]
  suffices hq : m * q = q ^ (k * k) * m by rw [hq, mul_inv_cancel_right]
  apply mat_inj
  rw [mat_mul, mat_mul, mat_pow]
  refine mat_ext_of_decomp (span_A hσ hW hH hJ₁) ?_ ?_ ?_
  · intro u
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hqι, hMι, pow_fix _ _ (hqι u)]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hqx, hmx, Matrix.mulVec_smul, pow_fix _ _ hqx]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hβ, Matrix.mulVec_add, Matrix.mulVec_smul, hmx, hmy,
      Matrix.mulVec_smul, pow_shear _ _ _ β hqx hβ, ht]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    linear_combination (-(β * (k : AE F E) * incV F H'.x i)) * hs

end GlobalTheory.ThK.TorusCentre
