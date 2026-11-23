import Development.WeilBound.ThetaLifts.LeviDeterminants.EvModel

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt

section Alg

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) {α β : Type} [Fintype α] [Fintype β]

def DR (J : Matrix α α S) (z : Matrix α (β ⊕ Fin 2) S) : α → S := fun i => -∑ k, J i k * c (z k (.inr 0))

def DL (J : Matrix β β S) (z : Matrix (α ⊕ Fin 2) β S) : β → S := fun j => ∑ l, J j l * c (z (.inr 0) l)

theorem splitR (hc : ∀ z, c (c z) = z) {J : Matrix α α S} (hJ : ∀ i j, c (J j i) = 1 * J i j) (J' : Matrix β β S)
    (z z' : Matrix α (β ⊕ Fin 2) S) : hTens c J (Matrix.fromBlocks J' 0 0 !![0, 1; -1, 0]) z z' =
      (fun i => z i (.inr 1)) ⬝ᵥ DR c J z' - c ((fun i => z' i (.inr 1)) ⬝ᵥ DR c J z) +
        hTens c J J' (z.submatrix id .inl) (z'.submatrix id .inl) := by
  have e : ∀ z z' : Matrix α (β ⊕ Fin 2) S, (fun i => z i (.inr 1)) ⬝ᵥ DR c J z' =
      -∑ i, ∑ k, z i (.inr 1) * J i k * c (z' k (.inr 0)) := fun z z' => by
    simp only [dotProduct, DR, mul_neg, Finset.mul_sum, mul_assoc, Finset.sum_neg_distrib]
  rw [hTens_plane_right, e, e, map_neg, conj_pair c hc hJ]
  ring

theorem splitL (hc : ∀ z, c (c z) = z) (J : Matrix α α S) {J' : Matrix β β S} (hJ : ∀ i j, c (J' j i) = -1 * J' i j)
    (z z' : Matrix (α ⊕ Fin 2) β S) : hTens c (Matrix.fromBlocks J 0 0 !![0, 1; 1, 0]) J' z z' =
      z (.inr 1) ⬝ᵥ DL c J' z' - c (z' (.inr 1) ⬝ᵥ DL c J' z) + hTens c J J' (z.submatrix .inl id) (z'.submatrix .inl id) := by
  have e : ∀ z z' : Matrix (α ⊕ Fin 2) β S, z (.inr 1) ⬝ᵥ DL c J' z' =
      ∑ i, ∑ k, z (.inr 1) i * J' i k * c (z' (.inr 0) k) := fun z z' => by
    simp only [dotProduct, DL, Finset.mul_sum, mul_assoc]
  rw [hTens_plane_left, e, e, conj_pair c hc hJ]
  ring

theorem gram_herm (hc : ∀ z, c (c z) = z) {J : Matrix α α S} {η : S} (hJ : ∀ i j, c (J j i) = η * J i j) (A : Matrix α β S)
    (i j : β) : c ((Aᵀ * J * A.map c) j i) = η * (Aᵀ * J * A.map c) i j := by
  have e : ∀ i j, (Aᵀ * J * A.map c) i j = ∑ a, ∑ b, A a i * J a b * c (A b j) := fun i j => by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [e, e, conj_pair c hc hJ]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}

theorem incM_one' {α : Type} [DecidableEq α] : incM F (1 : Matrix α α E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem inc_herm {α : Type} {J : Matrix α α E} {η : ℤ} (hJ : ∀ i j, σ (J j i) = η * J i j) (i j : α) :
    cA σ (incM F J j i) = η * incM F J i j := by
  show cA σ (inclR (F := F) (AF F) _) = _ * inclR (F := F) (AF F) _
  rw [GlobalTheory.VacIndic.cA_inclR, hJ, map_mul, map_intCast]

structure FrOK (σ : E →ₐ[F] E) {m m₁ : ℕ} (Y : Spc F E m) (Y₁ : Spc F E m₁) (H : Plane E m m₁) (η : ℤ)
    (Q : Matrix (Fin m₁ ⊕ Fin 2) (Fin m) E) : Prop where
  pq : incM F (frame H) * incM F Q = 1
  gram : (incM F (frame H))ᵀ * incM F Y.J * (incM F (frame H)).map (cA σ) =
    Matrix.fromBlocks (incM F Y₁.J) 0 0 !![0, 1; (η : AE F E), 0]
  herm : ∀ i j, cA σ (incM F Y.J j i) = η * incM F Y.J i j
  herm₁ : ∀ i j, cA σ (incM F Y₁.J j i) = η * incM F Y₁.J i j
  qx : incM F Q *ᵥ incV F H.x = Pi.single (.inr 0) 1
  qy : incM F Q *ᵥ incV F H.y = Pi.single (.inr 1) 1
  qi : incM F Q * incM F H.ι = Matrix.fromRows 1 0
  low : ∀ u ∈ Y.L, Q.submatrix .inl id *ᵥ u ∈ Y₁.L
  msk : ∀ c s t : ℤ, ∃ A : Matrix (Fin m) (Fin m) E, (∀ u ∈ Y.L, A *ᵥ u ∈ Y.L) ∧
    incM F Q * incM F A = mask (AE F E) m₁ c s t * incM F Q

theorem exists_frOK (hB : B.IsGood σ) {m m₁ i₀ i₁ : ℕ} {Y : Spc F E m} {Y₁ : Spc F E m₁} {H : Plane E m m₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hL : Y.L.IsLattice E) {η : ℤ} (hη : η * η = 1)
    (hJ : ∀ i j, σ (Y.J j i) = η * Y.J i j) : ∃ Q, FrOK σ Y Y₁ H η Q := by
  obtain ⟨Q, hPQ, hQP, hQ⟩ := exists_frame_inv hH hL
  have hA : incM F Q * incM F (frame H) = 1 := by rw [← incM_mul, hQP, incM_one']
  refine ⟨Q, by rw [← incM_mul, hPQ, incM_one'], ?_, inc_herm hJ, inc_herm fun i j => ?_, ?_, ?_, ?_,
    fun u hu => (hQ u hu).1, fun c s t => ⟨_, mask_mem hH hQ c s t, ?_⟩⟩
  · have h := congrArg (incM F) (frame_gram hB hH (η := η) (by exact_mod_cast congrArg (Int.cast : ℤ → E) hη) hJ)
    rw [incM_mul, incM_mul] at h
    refine Eq.trans ?_ (h.trans ?_)
    · rfl
    · ext (i | i) (j | j)
      · rfl
      · simp [incM]
      · simp [incM]
      · fin_cases i <;> fin_cases j <;> simp [incM]
  · rw [← hH.gram]
    exact gram_herm σ (conj_conj hB) hJ _ _ _
  · funext i
    have := congrFun (congrFun hA i) (.inr 0)
    rw [Matrix.one_apply, ← Pi.single_apply (Sum.inr 0) (1 : AE F E) i] at this
    exact this
  · funext i
    have := congrFun (congrFun hA i) (.inr 1)
    rw [Matrix.one_apply, ← Pi.single_apply (Sum.inr 1) (1 : AE F E) i] at this
    exact this
  · ext i j
    refine (congrFun (congrFun hA i) (.inl j)).trans ?_
    rcases i with i | i <;> simp [Matrix.one_apply]
  · rw [incM_mul, incM_mul, incM_mask, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, Matrix.one_mul]

theorem frOK_herm (hB : B.IsGood σ) {m m₁ i₀ i₁ r s : ℕ} {Y : Spc F E m} {Y₁ : Spc F E m₁} {H : Plane E m m₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hY : Y.IsHerm σ B r s) : ∃ Q, FrOK σ Y Y₁ H 1 Q :=
  exists_frOK hB hH hY.lat rfl fun i j => by simp [hY.herm]

theorem frOK_skew (hB : B.IsGood σ) {m m₁ i₀ i₁ r s : ℕ} {Y : Spc F E m} {Y₁ : Spc F E m₁} {H : Plane E m m₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hY : Y.IsSkew σ B r s) : ∃ Q, FrOK σ Y Y₁ H (-1) Q :=
  exists_frOK hB hH hY.lat rfl fun i j => by simp [hY.skew]

theorem hTens_fr {α β α' β' : Type} [Fintype α] [Fintype β] [Fintype α'] [Fintype β'] [DecidableEq α] [DecidableEq β]
    (J : Matrix α α (AE F E)) (J' : Matrix β β (AE F E)) {P : Matrix α α' (AE F E)} {Q : Matrix α' α (AE F E)} (h : P * Q = 1)
    {P' : Matrix β β' (AE F E)} {Q' : Matrix β' β (AE F E)} (h' : P' * Q' = 1) (z z' : Matrix α β (AE F E)) :
    hTens (cA σ) J J' z z' = hTens (cA σ) (Pᵀ * J * P.map (cA σ)) (P'ᵀ * J' * P'.map (cA σ)) (Q * z * Q'ᵀ) (Q * z' * Q'ᵀ) := by
  have e : ∀ z : Matrix α β (AE F E), P * (Q * z * Q'ᵀ) * P'ᵀ = z := fun z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, h',
      Matrix.transpose_one, Matrix.mul_one]
  rw [← hTens_mul, e, e]

theorem w_vec {α β α' β' S : Type} [CommRing S] [Fintype α] [Fintype β] (Q : Matrix α' α S) (Q' : Matrix β' β S) (x : α → S)
    (y : β → S) : Q * Matrix.vecMulVec x y * Q'ᵀ = Matrix.vecMulVec (Q *ᵥ x) (Q' *ᵥ y) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

theorem w_mul {α β α' β' a b S : Type} [CommRing S] [Fintype α] [Fintype β] [Fintype a] [Fintype b] (Q : Matrix α' α S)
    (Q' : Matrix β' β S) (A : Matrix α a S) (A' : Matrix β b S) (z : Matrix a b S) :
    Q * (A * z * A'ᵀ) * Q'ᵀ = Q * A * z * (Q' * A')ᵀ := by
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem w_msk {α β α' β' S : Type} [CommRing S] [Fintype α] [Fintype β] [Fintype α'] [Fintype β'] {Q : Matrix α' α S}
    {Q' : Matrix β' β S} {A : Matrix α α S} {A' : Matrix β β S} {m : Matrix α' α' S} {m' : Matrix β' β' S}
    (h : Q * A = m * Q) (h' : Q' * A' = m' * Q')
    (z : Matrix α β S) : Q * (A * z * A'ᵀ) * Q'ᵀ = m * (Q * z * Q'ᵀ) * m'ᵀ := by
  rw [w_mul, h, h']
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem w_inc {α β α' β' : Type} [Fintype α] [Fintype β] (Q : Matrix α' α E) (Q' : Matrix β' β E) (x : Matrix α β E) :
    incM F Q * incM F x * (incM F Q')ᵀ = incM F (Q * x * Q'ᵀ) := by
  rw [incM_mul, incM_mul]
  rfl

theorem DR_inc {α β : Type} [Fintype α] (J : Matrix α α E) (x : Matrix α (β ⊕ Fin 2) E) :
    DR (cA σ) (incM F J) (incM F x) = fun k => inclR (F := F) (AF F) (DR σ J x k) := by
  funext k
  simp only [DR, map_neg, map_sum, map_mul]
  rfl

theorem DL_inc {α β : Type} [Fintype β] (J : Matrix β β E) (x : Matrix (α ⊕ Fin 2) β E) :
    DL (cA σ) (incM F J) (incM F x) = fun k => inclR (F := F) (AF F) (DL σ J x k) := by
  funext k
  simp only [DL, map_sum, map_mul]
  rfl

end PositivityTheory.ThKF0
