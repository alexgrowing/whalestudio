import Development.WeilBound.ThetaLifts.TowerModels.PlaneForm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists

noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem frame_inv {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hn : r + s = n) {A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ}
    (hA : Aᵀ * M * A.map star = Matrix.fromBlocks 1 0 0 (-1)) :
    ∃ B : Matrix (Fin r ⊕ Fin s) (Fin n) ℂ, B * A = 1 ∧ A * B = 1 := by
  have h1 : Aᵀ * (M * (A.map star * (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ))) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, Matrix.fromBlocks_multiply]
    simp
  have h2 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hn])).1 h1
  refine ⟨(M * (A.map star * (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ)))ᵀ, ?_, ?_⟩
  · have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  · have := congrArg Matrix.transpose h2
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨e, A, hA⟩ := h
  have h1 : Aᵀ * (M * (A.map star * (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ))) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, Matrix.fromBlocks_multiply]
    simp
  have h2 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [e])).1 h1
  rw [Matrix.mul_assoc] at h2
  exact (Matrix.isUnit_det_of_right_inverse h2).ne_zero

theorem gram_vec {m k : Type} [Fintype m] [Fintype k] (M : Matrix m m ℂ) (A : Matrix m k ℂ) (u v : k → ℂ) :
    (A *ᵥ u) ⬝ᵥ M *ᵥ star (A *ᵥ v) = u ⬝ᵥ (Aᵀ * M * A.map star) *ᵥ star v := by
  have e1 : star (A *ᵥ v) = A.map star *ᵥ star v := by
    funext i; simp [Matrix.mulVec, dotProduct]
  simp only [e1, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem cartan_of_frame {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hn : r + s = n)
    {A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ} (hA : Aᵀ * M * A.map star = Matrix.fromBlocks 1 0 0 (-1)) :
    ∃ θ, IsCartan M θ ∧ θ * A = A * (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) := by
  obtain ⟨B, hBA, hAB⟩ := frame_inv hn hA
  set J : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hJ
  have hJJ : J * J = 1 := by rw [hJ, Matrix.fromBlocks_multiply]; simp
  have hJt : Jᵀ = J := by rw [hJ, Matrix.fromBlocks_transpose]; simp
  have hJs : J.map star = J := by
    ext (a | a) (b | b) <;> simp [hJ, Matrix.one_apply, apply_ite]
  have hθA : A * J * B * A = A * J := by rw [Matrix.mul_assoc, hBA, Matrix.mul_one]
  have ms : ∀ {a b c : Type} [Fintype b] (X : Matrix a b ℂ) (Y : Matrix b c ℂ),
      (X * Y).map star = X.map star * Y.map star := fun X Y => Matrix.map_mul (f := starRingEnd ℂ)
  refine ⟨A * J * B, ⟨?_, ?_, fun x hx => ?_⟩, hθA⟩
  · calc A * J * B * (A * J * B) = A * (J * (B * A) * J) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBA, Matrix.mul_one, hJJ, Matrix.mul_one, hAB]
  · calc (A * J * B)ᵀ * M * (A * J * B).map star = Bᵀ * (J * (Aᵀ * M * A.map star) * J) * B.map star := by
          simp only [Matrix.transpose_mul, ms, hJt, hJs, Matrix.mul_assoc]
      _ = Bᵀ * (Aᵀ * M * A.map star) * B.map star := by rw [hA, hJJ, Matrix.one_mul]
      _ = (A * B)ᵀ * M * (A * B).map star := by simp only [Matrix.transpose_mul, ms, Matrix.mul_assoc]
      _ = M := by
          rw [hAB, Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (star_zero _) (star_one _), Matrix.mul_one]
  · obtain ⟨u, rfl⟩ : ∃ u, x = A *ᵥ u := ⟨B *ᵥ x, by rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]⟩
    have hu : u ≠ 0 := by rintro rfl; simp at hx
    rw [Matrix.mulVec_mulVec, hθA, ← Matrix.mulVec_mulVec, gram_vec, hA, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hJt, Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec]
    open scoped ComplexOrder in
    exact (Complex.pos_iff.1 (Matrix.dotProduct_self_star_pos_iff.2 hu)).1

theorem hasSig_unique {n r s p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (h' : HasSig M p q) :
    r = p ∧ s = q := by
  obtain ⟨e, A, hA⟩ := h
  obtain ⟨e', A', hA'⟩ := h'
  have k : ∀ {r s : ℕ} (A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ), (A.map star)ᴴ = Aᵀ := fun A => by ext a b; simp
  have h1 := Formalism.UG.P.sig_dim M (A.map star) (by rw [k]; exact hA) (A'.map star) (by rw [k]; exact hA')
  have h2 := Formalism.UG.P.sig_dim M (A'.map star) (by rw [k]; exact hA') (A.map star) (by rw [k]; exact hA)
  rw [Fintype.card_fin] at h1 h2
  omega

theorem hasSig_exists {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (hdet : M.det ≠ 0) : ∃ p q, HasSig M p q := by
  obtain ⟨p, q, h⟩ := Formalism.UG.P.signature_exists _ M (by rw [Formalism.UG.IsHerm, Formalism.UG.P.cT_conj_eq, hM]) hdet.isUnit
  obtain ⟨e, Q, hQ⟩ := Formalism.UG.P.sig_data M p q h
  refine ⟨p, q, by simpa using e.symm, Q.map star, ?_⟩
  have : (Q.map star).map star = Q := by ext a b; simp
  rw [this]
  exact hQ

theorem herm_swap {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (u v : Fin n → ℂ) :
    v ⬝ᵥ M *ᵥ star u = star (u ⬝ᵥ M *ᵥ star v) := by
  have hM' : ∀ i j, star (M i j) = M j i := fun i j => by rw [← Matrix.conjTranspose_apply, hM]
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, hM', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem real_plane {n n₁ : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (X Y : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) {r s : ℕ} (hn : n = n₁ + 2) (hM : Mᴴ = M)
    (hXX : X ⬝ᵥ M *ᵥ star X = 0) (hYY : Y ⬝ᵥ M *ᵥ star Y = 0) (hXY : X ⬝ᵥ M *ᵥ star Y = 1)
    (hιX : ιᵀ *ᵥ (M *ᵥ star X) = 0) (hιY : ιᵀ *ᵥ (M *ᵥ star Y) = 0) (hP : P * ι = 1) (hsig : HasSig M r s) :
    HasSig (ιᵀ * M * ι.map star) (r - 1) (s - 1) ∧ ∃ θ θ₁, IsCartan M θ ∧ IsCartan (ιᵀ * M * ι.map star) θ₁ ∧
      θ * ι = ι * θ₁ ∧ Y = (2 : ℂ) • θ *ᵥ X := by
  classical
  have hYX : Y ⬝ᵥ M *ᵥ star X = 1 := by rw [herm_swap hM, hXY, star_one]
  have oX : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 := fun u => by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hιX, zero_dotProduct]
  have oY : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0 := fun u => by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hιY, zero_dotProduct]
  have oX' : ∀ u, X ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := fun u => by rw [herm_swap hM, oX, star_zero]
  have oY' : ∀ u, Y ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := fun u => by rw [herm_swap hM, oY, star_zero]
  have hinj : ∀ u, ι *ᵥ u = 0 → u = 0 := fun u hu => by
    have := congrArg (P *ᵥ ·) hu
    simpa [Matrix.mulVec_mulVec, hP] using this
  have hspan : ∀ Z : Fin n → ℂ, ∃ (a : ℂ) (u : Fin n₁ → ℂ) (b : ℂ), a • X + ι *ᵥ u + b • Y = Z := by
    let f : (ℂ × ℂ) × (Fin n₁ → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
      ((LinearMap.toSpanSingleton ℂ _ X).coprod (LinearMap.toSpanSingleton ℂ _ Y)).coprod ι.mulVecLin
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨⟨a, b⟩, u⟩ h0
      have h0' : a • X + b • Y + ι *ᵥ u = 0 := h0
      have ha : a = 0 := by
        have := congrArg (· ⬝ᵥ M *ᵥ star Y) h0'
        simpa [add_dotProduct, smul_dotProduct, hXY, hYY, oY] using this
      have hb : b = 0 := by
        have := congrArg (· ⬝ᵥ M *ᵥ star X) h0'
        simpa [add_dotProduct, smul_dotProduct, hXX, hYX, oX] using this
      subst ha hb
      rw [hinj u (by simpa using h0')]
      rfl
    intro Z
    obtain ⟨⟨⟨a, b⟩, u⟩, hZ⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f)
      (by simp [hn]; omega)).1 hf Z
    exact ⟨a, u, b, by rw [← hZ, add_right_comm]; rfl⟩
  set M₁ := ιᵀ * M * ι.map star with hM₁
  have hM₁h : M₁ᴴ = M₁ := by
    have e1 : (ι.map star)ᴴ = ιᵀ := by ext a b; simp
    have e2 : ιᵀᴴ = ι.map star := by ext a b; simp
    rw [hM₁, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, e1, e2, hM, Matrix.mul_assoc]
  have hdet₁ : M₁.det ≠ 0 := fun h0 => by
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 : M *ᵥ star (ι *ᵥ star v) = 0 := by
      funext k
      obtain ⟨a, u, b, hZ⟩ := hspan (Pi.single k 1)
      have : (a • X + ι *ᵥ u + b • Y) ⬝ᵥ M *ᵥ star (ι *ᵥ star v) = 0 := by
        rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, oX', oY', gram_vec, star_star, ← hM₁, hMv]
        simp
      rw [hZ] at this
      simpa using this
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero (det_ne_zero_of_hasSig hsig) h1
    exact hv (star_eq_zero.1 (hinj _ (star_eq_zero.1 h2)))
  obtain ⟨p, q, hpq, A₁, hA₁⟩ := hasSig_exists hM₁h hdet₁
  let c : Fin (p + 1) ⊕ Fin (q + 1) → Fin n → ℂ :=
    Sum.elim (Fin.cons (X + (1 / 2 : ℂ) • Y) fun a => ι *ᵥ A₁ *ᵥ Pi.single (Sum.inl a) 1)
      (Fin.cons (X - (1 / 2 : ℂ) • Y) fun a => ι *ᵥ A₁ *ᵥ Pi.single (Sum.inr a) 1)
  obtain ⟨A, hcol⟩ : ∃ A : Matrix (Fin n) (Fin (p + 1) ⊕ Fin (q + 1)) ℂ, ∀ k, A *ᵥ Pi.single k 1 = c k :=
    ⟨(Matrix.of c)ᵀ, fun k => by funext i; simp⟩
  have ent : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℂ) (a b : κ),
      Pi.single a 1 ⬝ᵥ G *ᵥ star (Pi.single b (1 : ℂ) : κ → ℂ) = G a b := fun G a b => by
    rw [← Pi.single_star]; simp
  have g1 : ∀ a b, (ι *ᵥ A₁ *ᵥ Pi.single a 1) ⬝ᵥ M *ᵥ star (ι *ᵥ A₁ *ᵥ Pi.single b 1) =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) a b := fun a b => by
    rw [gram_vec, gram_vec, ← hM₁, hA₁, ent]
  have hA : Aᵀ * M * A.map star = Matrix.fromBlocks 1 0 0 (-1) := by
    ext a b
    rw [← ent (Aᵀ * M * A.map star), ← gram_vec, hcol, hcol]
    rcases a with a | a <;> rcases b with b | b <;> refine Fin.cases ?_ (fun a => ?_) a <;>
      refine Fin.cases ?_ (fun b => ?_) b <;>
      simp only [c, Sum.elim_inl, Sum.elim_inr, Fin.cons_zero, Fin.cons_succ, g1, add_dotProduct, sub_dotProduct,
        smul_dotProduct, star_add, star_sub, star_smul, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul,
        dotProduct_add, dotProduct_sub, dotProduct_smul, oX, oY, oX', oY', hXX, hYY, hXY, hYX] <;>
      simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm] <;> norm_num
  have hn' : p + 1 + (q + 1) = n := by omega
  obtain ⟨rfl, rfl⟩ := hasSig_unique hsig ⟨hn', A, hA⟩
  obtain ⟨θ, hθ, hθA⟩ := cartan_of_frame hn' hA
  obtain ⟨θ₁, hθ₁, hθA₁⟩ := cartan_of_frame hpq hA₁
  obtain ⟨B₁, -, hAB₁⟩ := frame_inv hpq hA₁
  have jl : ∀ {r s : ℕ} (a : Fin r), (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) *ᵥ
      Pi.single (Sum.inl a) 1 = Pi.single (Sum.inl a) 1 := fun a => by
    funext k; rcases k with k | k <;> simp [Matrix.one_apply, Pi.single_apply]
  have jr : ∀ {r s : ℕ} (a : Fin s), (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) *ᵥ
      Pi.single (Sum.inr a) 1 = -Pi.single (Sum.inr a) 1 := fun a => by
    funext k; rcases k with k | k <;> simp [Matrix.one_apply, Pi.single_apply]
  have tl : ∀ a, θ *ᵥ c (Sum.inl a) = c (Sum.inl a) := fun a => by
    rw [← hcol, Matrix.mulVec_mulVec, hθA, ← Matrix.mulVec_mulVec, jl]
  have tr : ∀ a, θ *ᵥ c (Sum.inr a) = -c (Sum.inr a) := fun a => by
    rw [← hcol, Matrix.mulVec_mulVec, hθA, ← Matrix.mulVec_mulVec, jr, Matrix.mulVec_neg]
  refine ⟨⟨hpq, A₁, hA₁⟩, θ, θ₁, hθ, hθ₁, ?_, ?_⟩
  · have : θ * ι * A₁ = ι * θ₁ * A₁ := by
      rw [Matrix.mul_assoc ι, hθA₁]
      refine Matrix.ext_of_mulVec_single fun k => ?_
      simp only [← Matrix.mulVec_mulVec]
      rcases k with k | k
      · rw [jl]; exact tl k.succ
      · rw [jr, Matrix.mulVec_neg, Matrix.mulVec_neg]; exact tr k.succ
    rw [← Matrix.mul_one (θ * ι), ← hAB₁, ← Matrix.mul_assoc, this, Matrix.mul_assoc, hAB₁, Matrix.mul_one]
  · have a1 : θ *ᵥ (X + (1 / 2 : ℂ) • Y) = X + (1 / 2 : ℂ) • Y := tl 0
    have a2 : θ *ᵥ (X - (1 / 2 : ℂ) • Y) = -(X - (1 / 2 : ℂ) • Y) := tr 0
    rw [Matrix.mulVec_add] at a1
    rw [Matrix.mulVec_sub] at a2
    funext i
    have b1 := congrFun a1 i
    have b2 := congrFun a2 i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at b1 b2 ⊢
    linear_combination -b1 - b2

end PositivityTheory.ThKG.Tow.Pln

end
