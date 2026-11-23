import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraFrobeniusReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLnStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesCentralIdempotentLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelMulOfConstituentStatement

noncomputable section

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.Opp

theorem eq_zero_of_idem {G : Type} [Group G] [Fintype G] (E : MonoidAlgebra ℂ G) (h : E * E = E)
    (h1 : E.coeff 1 = 0) : E = 0 := by
  haveI : Module.Finite ℂ (MonoidAlgebra ℂ G) := Module.Finite.of_basis (MonoidAlgebra.basis G ℂ)
  haveI : Module.Free ℂ (MonoidAlgebra ℂ G) := Module.Free.of_basis (MonoidAlgebra.basis G ℂ)
  have hi : IsIdempotentElem (LinearMap.mulLeft ℂ E) := by
    refine LinearMap.ext fun x => ?_
    simp [← mul_assoc, h]
  have ht : LinearMap.trace ℂ _ (LinearMap.mulLeft ℂ E) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    have : (MonoidAlgebra.basis G ℂ) x = MonoidAlgebra.single x 1 := by simp
    rw [this]
    show (E * MonoidAlgebra.single x 1).coeff x = 0
    rw [MonoidAlgebra.coeff_mul_single_apply]
    simp [h1]
  have h0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hi ht
  simpa using LinearMap.congr_fun h0 1

theorem tr_single {G : Type} [Group G] [Fintype G] (x : G) (c : ℂ) (χ : G → ℂ) :
    tr (MonoidAlgebra.single x c) χ = c * χ x := by
  simp [tr, Finsupp.single_apply]

theorem tr_sum {G ι : Type} [Group G] [Fintype G] (s : Finset ι) (a : ι → MonoidAlgebra ℂ G) (χ : G → ℂ) :
    tr (∑ i ∈ s, a i) χ = ∑ i ∈ s, tr (a i) χ := by
  simp only [tr]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul]
  simp

variable {g : ℕ} [Fact g.Prime] {k l n : ℕ}

def par (σ : Fin k ⊕ Fin l ≃ Fin n) (x : Gn g k) (B : Matrix (Fin k) (Fin l) (ZMod g)) (y : Gn g l) : Gn g n where
  val := Matrix.reindex σ σ (Matrix.fromBlocks (x : Mt g k) B 0 (y : Mt g l))
  inv := Matrix.reindex σ σ (Matrix.fromBlocks ((x⁻¹ : Gn g k) : Mt g k)
    (-(((x⁻¹ : Gn g k) : Mt g k) * B * ((y⁻¹ : Gn g l) : Mt g l))) 0 ((y⁻¹ : Gn g l) : Mt g l))
  val_inv := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [← Matrix.mul_assoc]
  inv_val := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc]

theorem par_val (σ : Fin k ⊕ Fin l ≃ Fin n) (x : Gn g k) (B : Matrix (Fin k) (Fin l) (ZMod g)) (y : Gn g l) :
    ((par σ x B y : Gn g n) : Mt g n) = Matrix.reindex σ σ (Matrix.fromBlocks (x : Mt g k) B 0 (y : Mt g l)) := rfl

theorem par_apply (σ : Fin k ⊕ Fin l ≃ Fin n) (x : Gn g k) (B : Matrix (Fin k) (Fin l) (ZMod g)) (y : Gn g l)
    (i j : Fin k ⊕ Fin l) : ((par σ x B y : Gn g n) : Mt g n) (σ i) (σ j) =
      Matrix.fromBlocks (x : Mt g k) B 0 (y : Mt g l) i j := by
  simp [par_val]

theorem par_mul (σ : Fin k ⊕ Fin l ≃ Fin n) (x x' : Gn g k) (B B' : Matrix (Fin k) (Fin l) (ZMod g))
    (y y' : Gn g l) : par σ x B y * par σ x' B' y' =
      par σ (x * x') ((x : Mt g k) * B' + B * (y' : Mt g l)) (y * y') := by
  apply Units.ext
  simp only [Units.val_mul, par_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem par_one (σ : Fin k ⊕ Fin l ≃ Fin n) : par σ (1 : Gn g k) 0 1 = 1 := by
  apply Units.ext
  simp [par_val]

def inA (σ : Fin k ⊕ Fin l ≃ Fin n) : Gn g k →* Gn g n where
  toFun x := par σ x 0 1
  map_one' := par_one σ
  map_mul' x x' := by simp [par_mul]

def inB (σ : Fin k ⊕ Fin l ≃ Fin n) : Gn g l →* Gn g n where
  toFun y := par σ 1 0 y
  map_one' := par_one σ
  map_mul' x x' := by simp [par_mul]

theorem par_swap (σ : Fin k ⊕ Fin l ≃ Fin n) (x : Gn g k) (y : Gn g l) :
    par ((Equiv.sumComm _ _).trans σ) y 0 x = par σ x 0 y := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := σ.surjective i
  obtain ⟨j, rfl⟩ := σ.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [par_val]

theorem inA_swap (σ : Fin k ⊕ Fin l ≃ Fin n) : inA (g := g) ((Equiv.sumComm _ _).trans σ) = inB σ :=
  MonoidHom.ext fun _ => par_swap σ _ _

theorem inB_swap (σ : Fin k ⊕ Fin l ≃ Fin n) : inB (g := g) ((Equiv.sumComm _ _).trans σ) = inA σ :=
  MonoidHom.ext fun _ => par_swap σ _ _

theorem sum_mul_left {A : Type} [AddCommMonoid A] (x : Gn g k) (F : Matrix (Fin k) (Fin l) (ZMod g) → A) :
    ∑ B : Matrix (Fin k) (Fin l) (ZMod g), F ((x : Mt g k) * B) = ∑ B, F B := by
  refine Fintype.sum_bijective (fun B : Matrix (Fin k) (Fin l) (ZMod g) => (x : Mt g k) * B) ?_ _ _ fun _ => rfl
  refine Finite.injective_iff_bijective.1 fun B B' h => ?_
  have := congrArg (fun C : Matrix (Fin k) (Fin l) (ZMod g) => ((x⁻¹ : Gn g k) : Mt g k) * C) h
  simpa [← Matrix.mul_assoc] using this

theorem sum_mul_right {A : Type} [AddCommMonoid A] (y : Gn g l) (F : Matrix (Fin k) (Fin l) (ZMod g) → A) :
    ∑ B : Matrix (Fin k) (Fin l) (ZMod g), F (B * (y : Mt g l)) = ∑ B, F B := by
  refine Fintype.sum_bijective (fun B : Matrix (Fin k) (Fin l) (ZMod g) => B * (y : Mt g l)) ?_ _ _ fun _ => rfl
  refine Finite.injective_iff_bijective.1 fun B B' h => ?_
  have := congrArg (fun C : Matrix (Fin k) (Fin l) (ZMod g) => C * ((y⁻¹ : Gn g l) : Mt g l)) h
  simpa [Matrix.mul_assoc] using this

def eN (g : ℕ) [Fact g.Prime] (σ : Fin k ⊕ Fin l ≃ Fin n) : MonoidAlgebra ℂ (Gn g n) :=
  ∑ B : Matrix (Fin k) (Fin l) (ZMod g), MonoidAlgebra.single (par σ 1 B 1) ((g : ℂ) ^ (k * l))⁻¹

theorem card_mat : (Fintype.card (Matrix (Fin k) (Fin l) (ZMod g)) : ℂ) = (g : ℂ) ^ (k * l) := by
  rw [← Fintype.card_congr (Matrix.of : (Fin k → Fin l → ZMod g) ≃ _), Fintype.card_fun, Fintype.card_fun]
  simp [← pow_mul, mul_comm]

theorem gpow_ne : (g : ℂ) ^ (k * l) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero)

theorem eN_idem (σ : Fin k ⊕ Fin l ≃ Fin n) : eN g σ * eN g σ = eN g σ := by
  unfold eN
  rw [Finset.sum_mul_sum]
  simp only [MonoidAlgebra.single_mul_single, par_mul, Units.val_one, Matrix.one_mul, Matrix.mul_one, mul_one]
  have : ∀ B : Matrix (Fin k) (Fin l) (ZMod g), ∑ B', MonoidAlgebra.single (par σ 1 (B' + B) 1)
      (((g : ℂ) ^ (k * l))⁻¹ * ((g : ℂ) ^ (k * l))⁻¹) = ∑ B', MonoidAlgebra.single (par σ (1 : Gn g k) B' 1)
      (((g : ℂ) ^ (k * l))⁻¹ * ((g : ℂ) ^ (k * l))⁻¹) := fun B =>
    Fintype.sum_equiv (Equiv.addRight B) _ _ fun _ => rfl
  simp only [this]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, card_mat, Finset.smul_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [MonoidAlgebra.smul_single, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ gpow_ne, one_mul]

theorem eN_comm (σ : Fin k ⊕ Fin l ≃ Fin n) (x : Gn g k) (y : Gn g l) (c : ℂ) :
    Commute (eN g σ) (MonoidAlgebra.single (par σ x 0 y) c) := by
  unfold eN Commute SemiconjBy
  rw [Finset.sum_mul, Finset.mul_sum]
  simp only [MonoidAlgebra.single_mul_single, par_mul, Units.val_one, Matrix.mul_zero, Matrix.zero_mul, mul_one,
    one_mul, zero_add, add_zero]
  rw [sum_mul_right y (fun B => MonoidAlgebra.single (par σ x B y) (((g : ℂ) ^ (k * l))⁻¹ * c)),
    sum_mul_left x (fun B => MonoidAlgebra.single (par σ x B y) (c * ((g : ℂ) ^ (k * l))⁻¹)), mul_comm c]

theorem par_conj (σ σ' : Fin k ⊕ Fin l ≃ Fin n) : ∃ p : Gn g n, ∀ x B y, par σ x B y = p * par σ' x B y * p⁻¹ := by
  let τ : Fin n ≃ Fin n := σ'.symm.trans σ
  refine ⟨⟨τ.symm.toPEquiv.toMatrix, τ.toPEquiv.toMatrix, ?_, ?_⟩, fun x B y => ?_⟩
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp
  · apply Units.ext
    simp only [Units.val_mul, Units.inv_mk, par_val]
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simp [τ]

theorem res_std (χ : Gn g (k + l) → ℂ) (x : Gn g k) (y : Gn g l) :
    res k l χ x y = ((g : ℂ) ^ (k * l))⁻¹ * ∑ B, χ (par finSumFinEquiv x B y) := by
  unfold res
  congr 1
  rw [← Finset.sum_filter]
  symm
  have e1 : ∀ (M : Mt g (k + l)) (i j : Fin k), tl k M i j = M (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j)) := by
    intro M i j
    have hi := i.2
    have hj := j.2
    rw [tl, entN, dif_pos ⟨by omega, by omega⟩]
    rfl
  have e2 : ∀ (M : Mt g (k + l)) (i j : Fin l), br k l M i j = M (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j)) := by
    intro M i j
    have hi := i.2
    have hj := j.2
    rw [br, entN, dif_pos ⟨by omega, by omega⟩]
    rfl
  refine Finset.sum_bij (fun B _ => par finSumFinEquiv x B y) (fun B _ => ?_) (fun B _ B' _ h => ?_)
    (fun z hz => ?_) (fun _ _ => rfl)
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun i j hj hi => ?_, ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
      rw [par_apply]
      rcases i with i | i
      · have := i.2
        simp at hi
        omega
      rcases j with j | j
      · simp
      · simp at hj
    · ext i j
      rw [e1, par_apply]; simp
    · ext i j
      rw [e2, par_apply]; simp
  · ext i j
    have := congrArg (fun z : Gn g (k + l) => (z : Mt g (k + l)) (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j))) h
    simpa only [par_apply, Matrix.fromBlocks_apply₁₂] using this
  · rw [Finset.mem_filter] at hz
    obtain ⟨-, h0, h1, h2⟩ := hz
    refine ⟨Matrix.of fun i j => (z : Mt g (k + l)) (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j)),
      Finset.mem_univ _, ?_⟩
    apply Units.ext
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [par_apply]
    rcases i with i | i <;> rcases j with j | j
    · rw [← e1 (z : Mt g (k + l)) i j, h1]; simp
    · simp
    · rw [h0 _ _ (by simp) (by simp)]; simp
    · rw [← e2 (z : Mt g (k + l)) i j, h2]; simp

theorem res_eq (σ : Fin k ⊕ Fin l ≃ Fin n) (χ : Gn g n → ℂ) (hχ : IsClass χ) (x : Gn g k) (y : Gn g l) :
    res k l χ x y = ((g : ℂ) ^ (k * l))⁻¹ * ∑ B, χ (par σ x B y) := by
  have hn : n = k + l := by simpa using (Fintype.card_congr σ).symm
  subst hn
  obtain ⟨p, hp⟩ := par_conj (g := g) σ finSumFinEquiv
  rw [res_std]
  simp only [hp, hχ _ p]

open MonoidAlgebra in
theorem map_zOf {G H : Type} [Group G] [Fintype G] [Group H] (i : G →* H) (α : G → ℂ) :
    mapDomainAlgHom ℂ ℂ i (zOf α) = ∑ x, single (i x) (α 1 / (Fintype.card G : ℂ) * α x⁻¹) := by
  simp [zOf, map_sum]

open MonoidAlgebra in
theorem commute_map {G H : Type} [Group G] [Group H] (i : G →* H) (e : MonoidAlgebra ℂ H)
    (h : ∀ x c, Commute e (single (i x) c)) (a : MonoidAlgebra ℂ G) : Commute e (mapDomainAlgHom ℂ ℂ i a) := by
  induction a using MonoidAlgebra.induction_on with
  | of m => simpa using h m 1
  | add x y hx hy => rw [map_add]; exact hx.add_right hy
  | smul r x hx => rw [map_smul]; exact hx.smul_right r

open MonoidAlgebra in
theorem commute_AB (σ : Fin k ⊕ Fin l ≃ Fin n) (a : MonoidAlgebra ℂ (Gn g k)) (b : MonoidAlgebra ℂ (Gn g l)) :
    Commute (mapDomainAlgHom ℂ ℂ (inA σ) a) (mapDomainAlgHom ℂ ℂ (inB σ) b) := by
  refine commute_map _ _ (fun y c => ?_) b
  refine (commute_map _ _ (fun x d => ?_) a).symm
  unfold Commute SemiconjBy
  simp [single_mul_single, inA, inB, par_mul, mul_comm]

theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, -, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

open MonoidAlgebra in
theorem irr_vanish (σ : Fin k ⊕ Fin l ≃ Fin n) (χ : Gn g n → ℂ) (α : Gn g k → ℂ) (β : Gn g l → ℂ)
    (hχ : IsIrr χ) (hα : IsIrr α) (hβ : IsIrr β) (h : ip χ (hc k l α β n) = 0) :
    eN g σ * mapDomainAlgHom ℂ ℂ (inA σ) (zOf α) * mapDomainAlgHom ℂ ℂ (inB σ) (zOf β) * zOf χ = 0 := by
  have hn : n = k + l := by simpa using (Fintype.card_congr σ).symm
  have cA : Commute (eN g σ) (mapDomainAlgHom ℂ ℂ (inA σ) (zOf α)) :=
    commute_map (inA σ) (eN g σ) (fun x c => eN_comm σ x 1 c) _
  have cB : Commute (eN g σ) (mapDomainAlgHom ℂ ℂ (inB σ) (zOf β)) :=
    commute_map (inB σ) (eN g σ) (fun x c => eN_comm σ 1 x c) _
  have iz : ∀ {G : Type} [Group G] [Fintype G] (χ : G → ℂ), IsIrr χ → IsIdempotentElem (zOf χ) := by
    intro G _ _ χ h
    simpa [IsIdempotentElem] using (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G χ χ h h).1
  have hi : IsIdempotentElem
      (eN g σ * mapDomainAlgHom ℂ ℂ (inA σ) (zOf α) * mapDomainAlgHom ℂ ℂ (inB σ) (zOf β) * zOf χ) := by
    refine IsIdempotentElem.mul_of_commute (((GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ χ χ hχ hχ).2.1 _).symm) ?_ (iz χ hχ)
    refine IsIdempotentElem.mul_of_commute (cB.mul_left (commute_AB σ _ _)) ?_ ((iz β hβ).map _)
    exact IsIdempotentElem.mul_of_commute cA (eN_idem σ) ((iz α hα).map _)
  refine eq_zero_of_idem _ hi ?_
  rw [(GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree _ _ χ).2.2]
  refine mul_eq_zero_of_right _ ?_
  rw [hc, GlobalTheory.T.harishChandra_frobenius_reciprocity g k l n hn χ _ (isClass_of_isIrr hχ), ip, mul_eq_zero] at h
  have h' := h.resolve_left (inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero))
  rw [Fintype.sum_prod_type] at h'
  rw [map_zOf, map_zOf, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum, tr_sum]
  simp only [Finset.mul_sum, tr_sum]
  have key : ∀ x y c d, tr (eN g σ * (single (inA σ x) c * single (inB σ y) d)) χ = c * d * res k l χ x y := by
    intro x y c d
    rw [res_eq σ χ (isClass_of_isIrr hχ), eN, Finset.sum_mul, tr_sum,
      ← sum_mul_right y (fun B => χ (par σ x B y)), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    simp only [single_mul_single, tr_single, inA, inB, MonoidHom.coe_mk, OneHom.coe_mk, par_mul]
    simp
    ring
  simp only [key]
  have := congrArg (fun t => α 1 / (Fintype.card (Gn g k) : ℂ) * (β 1 / (Fintype.card (Gn g l) : ℂ)) * t) h'
  simp only [Finset.mul_sum, mul_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [Prod.fst_inv, Prod.snd_inv]
  ring

open MonoidAlgebra in
theorem ser_vanish (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) (σ : Fin k ⊕ Fin l ≃ Fin n)
    (f f₁ f₂ : (ZMod g)[X]) (hf : f ≠ f₁ * f₂) :
    eN g σ * mapDomainAlgHom ℂ ℂ (inA σ) (eSerC L k f₁) * mapDomainAlgHom ℂ ℂ (inB σ) (eSerC L l f₂) *
      eSerC L n f = 0 := by
  have hn : n = k + l := by simpa using (Fintype.card_congr σ).symm
  refine finsum_mem_induction (fun a => eN g σ * mapDomainAlgHom ℂ ℂ (inA σ) a *
    mapDomainAlgHom ℂ ℂ (inB σ) (eSerC L l f₂) * eSerC L n f = 0) (by simp) ?_ ?_
  · intro x y hx hy
    simp only [map_add, mul_add, add_mul, hx, hy, add_zero]
  rintro α ⟨hα, hα'⟩
  refine finsum_mem_induction (fun b => eN g σ * mapDomainAlgHom ℂ ℂ (inA σ) (zOf α) *
    mapDomainAlgHom ℂ ℂ (inB σ) b * eSerC L n f = 0) (by simp) ?_ ?_
  · intro x y hx hy
    simp only [map_add, mul_add, add_mul, hx, hy, add_zero]
  rintro β ⟨hβ, hβ'⟩
  refine finsum_mem_induction (fun c => eN g σ * mapDomainAlgHom ℂ ℂ (inA σ) (zOf α) *
    mapDomainAlgHom ℂ ℂ (inB σ) (zOf β) * c = 0) (by simp) ?_ ?_
  · intro x y hx hy
    simp only [mul_add, hx, hy, add_zero]
  rintro χ ⟨hχ, hχ'⟩
  refine irr_vanish σ χ α β hχ hα hβ ?_
  by_contra hne
  exact hf (((GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn g L h5 hG n).1 χ hχ).unique hχ'
    (GlobalTheory.T.harishChandraSeriesLabel_mul_of_constituent g L k l n χ α β f₁ f₂ hn hχ hα hβ hα' hβ' hne))

open MonoidAlgebra in
theorem ser_vanish' (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) (σ : Fin k ⊕ Fin l ≃ Fin n)
    (f f₁ f₂ : (ZMod g)[X]) (hf : f ≠ f₁ * f₂) :
    eSerC L n f * mapDomainAlgHom ℂ ℂ (inB σ) (eSerC L l f₂) * mapDomainAlgHom ℂ ℂ (inA σ) (eSerC L k f₁) *
      eN g σ = 0 := by
  have cA : Commute (eN g σ) (mapDomainAlgHom ℂ ℂ (inA σ) (eSerC L k f₁)) :=
    commute_map (inA σ) (eN g σ) (fun x c => eN_comm σ x 1 c) _
  have cB : Commute (eN g σ) (mapDomainAlgHom ℂ ℂ (inB σ) (eSerC L l f₂)) :=
    commute_map (inB σ) (eN g σ) (fun x c => eN_comm σ 1 x c) _
  rw [mul_assoc, mul_assoc, (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.1, ← mul_assoc, ← (commute_AB σ _ _).eq,
    ← (cA.mul_right cB).eq, ← mul_assoc]
  exact ser_vanish L h5 hG σ f f₁ f₂ hf

open MonoidAlgebra in
theorem comp_alg {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W)
    (i : G →* H) (a : MonoidAlgebra ℂ G) :
    Representation.asAlgebraHom (ρ.comp i : Representation ℂ G W) a = ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ i a) := by
  induction a using MonoidAlgebra.induction_on with
  | of m => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul r x hx => simp only [map_smul, hx]

theorem equiv_alg {G W W' : Type} [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ G W) (ρ' : Representation ℂ G W') (T : W →ₗ[ℂ] W') (h : ∀ m, T ∘ₗ ρ m = ρ' m ∘ₗ T)
    (a : MonoidAlgebra ℂ G) (w : W) : T (ρ.asAlgebraHom a w) = ρ'.asAlgebraHom a (T w) := by
  induction a using MonoidAlgebra.induction_on with
  | of m => simpa using LinearMap.congr_fun (h m) w
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | smul r x hx => simp only [map_smul, LinearMap.smul_apply, hx]

theorem eN_left {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Fin k ⊕ Fin l ≃ Fin n) (ρ : Representation ℂ (Gn g n) W) (T : W →ₗ[ℂ] W')
    (h : ∀ B, T ∘ₗ ρ (par σ 1 B 1) = T) (w : W) : T (ρ.asAlgebraHom (eN g σ) w) = T w := by
  have h' : ∀ B, T (ρ (par σ 1 B 1) w) = T w := fun B => LinearMap.congr_fun (h B) w
  simp only [eN, map_sum, Representation.asAlgebraHom_single, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, h']
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, card_mat, smul_smul, mul_inv_cancel₀ gpow_ne,
    one_smul]

theorem eN_right {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Fin k ⊕ Fin l ≃ Fin n) (ρ : Representation ℂ (Gn g n) W) (w : W)
    (h : ∀ B, ρ (par σ 1 B 1) w = w) : ρ.asAlgebraHom (eN g σ) w = w := by
  simp only [eN, map_sum, Representation.asAlgebraHom_single, LinearMap.sum_apply, LinearMap.smul_apply, h]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, card_mat, smul_smul, mul_inv_cancel₀ gpow_ne,
    one_smul]

theorem exists_split (a : Fin n → ℤ) (hn : 0 < n) : ∃ (k l : ℕ) (σ : Fin k ⊕ Fin l ≃ Fin n) (M : ℤ), k < n ∧
    (∀ i, a (σ (.inl i)) < M) ∧ ∀ j, a (σ (.inr j)) = M := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ a ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine ⟨_, _, (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans
    (Equiv.sumCompl fun i => a i < a i₀), a i₀, ?_, fun i => ?_, fun j => ?_⟩
  · simpa using Fintype.card_subtype_lt (p := fun i => a i < a i₀) (x := i₀) (lt_irrefl _)
  · exact ((Fintype.equivFin {i // a i < a i₀}).symm i).2
  · exact le_antisymm (hi₀ _ (Finset.mem_univ _)) (not_lt.1 ((Fintype.equivFin {i // ¬ a i < a i₀}).symm j).2)

open MonoidAlgebra in
theorem step (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) (σ : Fin k ⊕ Fin l ≃ Fin n) {W W' : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (Gn g n) W)
    (ρ' : Representation ℂ (Gn g n) W') (T : W →ₗ[ℂ] W')
    (hN : ∀ w, T (ρ.asAlgebraHom (eN g σ) w) = T w)
    (hN' : ∀ w, ρ'.asAlgebraHom (eN g ((Equiv.sumComm _ _).trans σ)) (T w) = T w)
    (hB : ∀ b w, T (ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inB σ) b) w) =
      ρ'.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inB σ) b) (T w))
    (hA : ∀ f f', f ≠ f' → ∀ w, ρ'.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inA σ) (eSerC L k f'))
      (T (ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inA σ) (eSerC L k f)) w)) = 0)
    (f f' : (ZMod g)[X]) (hf : f ≠ f') (w : W) :
    ρ'.asAlgebraHom (eSerC L n f') (T (ρ.asAlgebraHom (eSerC L n f) w)) = 0 := by
  obtain ⟨S₁, -, h₁⟩ := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG k).2.2.2.2
  obtain ⟨S₂, -, h₂⟩ := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG l).2.2.2.2
  have e₁ : ∀ v : W, v = ∑ f₁ ∈ S₁, ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inA σ) (eSerC L k f₁)) v := by
    intro v
    rw [← LinearMap.sum_apply, ← map_sum, ← map_sum, h₁, map_one, map_one, Module.End.one_apply]
  have e₂ : ∀ v : W, v = ∑ f₂ ∈ S₂, ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inB σ) (eSerC L l f₂)) v := by
    intro v
    rw [← LinearMap.sum_apply, ← map_sum, ← map_sum, h₂, map_one, map_one, Module.End.one_apply]
  have e₃ : ∀ v : W', v = ∑ f₁ ∈ S₁, ρ'.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inA σ) (eSerC L k f₁)) v := by
    intro v
    rw [← LinearMap.sum_apply, ← map_sum, ← map_sum, h₁, map_one, map_one, Module.End.one_apply]
  rw [e₂ (ρ.asAlgebraHom (eSerC L n f) w), map_sum, map_sum]
  refine Finset.sum_eq_zero fun f₂ _ => ?_
  rw [e₁ (ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inB σ) (eSerC L l f₂)) _), map_sum, map_sum]
  refine Finset.sum_eq_zero fun f₁ _ => ?_
  by_cases h12 : f = f₁ * f₂
  swap
  · rw [← hN, ← Module.End.mul_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      ← map_mul, ser_vanish L h5 hG σ f f₁ f₂ h12]
    simp
  rw [e₃ (T _), map_sum]
  refine Finset.sum_eq_zero fun f₃ _ => ?_
  by_cases h13 : f₁ = f₃
  swap
  · rw [hA f₁ f₃ h13, map_zero]
  subst h13
  have hc : ∀ v, ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inA σ) (eSerC L k f₁))
      (ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inB σ) (eSerC L l f₂)) v) =
      ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inB σ) (eSerC L l f₂))
      (ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inA σ) (eSerC L k f₁)) v) := by
    intro v
    rw [← Module.End.mul_apply, ← map_mul, (commute_AB σ _ _).eq, map_mul, Module.End.mul_apply]
  have hv := ser_vanish' L h5 hG ((Equiv.sumComm _ _).trans σ) f' f₂ f₁ (by rw [mul_comm, ← h12]; exact hf.symm)
  rw [inA_swap, inB_swap] at hv
  rw [hc, hB, ← hN', ← Module.End.mul_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    ← map_mul, hv]
  simp

theorem vanish (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) {W W' : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (T : W →ₗ[ℂ] W') (n : ℕ) :
    ∀ (ρ : Representation ℂ (Gn g n) W) (ρ' : Representation ℂ (Gn g n) W') (a : Fin n → ℤ),
    (∀ u : Gn g n, (∀ i j, ¬ a i < a j → (u : Mt g n) i j = (1 : Mt g n) i j) → T ∘ₗ ρ u = T) →
    (∀ u : Gn g n, (∀ i j, ¬ a j < a i → (u : Mt g n) i j = (1 : Mt g n) i j) → ρ' u ∘ₗ T = T) →
    (∀ m : Gn g n, (∀ i j, a i ≠ a j → (m : Mt g n) i j = 0) → T ∘ₗ ρ m = ρ' m ∘ₗ T) →
    ∀ f f' : (ZMod g)[X], f ≠ f' → ∀ w, ρ'.asAlgebraHom (eSerC L n f') (T (ρ.asAlgebraHom (eSerC L n f) w)) = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ρ ρ' a hU hU' hM f f' hf w
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [equiv_alg ρ ρ' T (fun m => hM m fun i => i.elim0), ← Module.End.mul_apply, ← map_mul,
      (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG 0).2.2.1 f' f hf.symm]
    simp
  obtain ⟨k, l, σ, M, hk, h₁, h₂⟩ := exists_split a hn
  have one : ∀ i j, (1 : Mt g n) (σ i) (σ j) = Matrix.fromBlocks (1 : Mt g k) 0 0 (1 : Mt g l) i j := by
    intro i j
    simp [Matrix.one_apply]
  refine step L h5 hG σ ρ ρ' T (eN_left σ ρ T fun B => hU _ fun i j hij => ?_)
    (fun w => eN_right _ ρ' _ fun B => LinearMap.congr_fun (hU' _ fun i j hij => ?_) w) (fun b w => ?_)
    (fun f f' hf w => ?_) f f' hf w
  · obtain ⟨i, rfl⟩ := σ.surjective i
    obtain ⟨j, rfl⟩ := σ.surjective j
    rw [par_apply, one]
    rcases i with i | i <;> rcases j with j | j
    · simp
    · exact absurd (h₂ j ▸ h₁ i) hij
    · simp
    · simp
  · obtain ⟨i, rfl⟩ := σ.surjective i
    obtain ⟨j, rfl⟩ := σ.surjective j
    rw [one]
    rcases i with i | i <;> rcases j with j | j
    · simp [par_val]
    · simp [par_val]
    · exact absurd (h₂ i ▸ h₁ j) hij
    · simp [par_val]
  · rw [← comp_alg, ← comp_alg]
    refine equiv_alg _ _ T (fun m => hM (par σ 1 0 m) fun i j hij => ?_) b w
    obtain ⟨i, rfl⟩ := σ.surjective i
    obtain ⟨j, rfl⟩ := σ.surjective j
    rw [par_apply]
    rcases i with i | i <;> rcases j with j | j
    · have : i ≠ j := fun h => hij (by rw [h])
      simp [Matrix.one_apply_ne this]
    · simp
    · simp
    · exact absurd ((h₂ i).trans (h₂ j).symm) hij
  · rw [← comp_alg, ← comp_alg]
    refine ih k hk _ _ (fun i => a (σ (.inl i))) (fun u hu => hU (par σ u 0 1) fun i j hij => ?_)
      (fun u hu => hU' (par σ u 0 1) fun i j hij => ?_) (fun u hu => hM (par σ u 0 1) fun i j hij => ?_) f f' hf w
    · obtain ⟨i, rfl⟩ := σ.surjective i
      obtain ⟨j, rfl⟩ := σ.surjective j
      rw [par_apply, one]
      rcases i with i | i <;> rcases j with j | j
      · simpa using hu i j hij
      all_goals simp
    · obtain ⟨i, rfl⟩ := σ.surjective i
      obtain ⟨j, rfl⟩ := σ.surjective j
      rw [par_apply, one]
      rcases i with i | i <;> rcases j with j | j
      · simpa using hu i j hij
      all_goals simp
    · obtain ⟨i, rfl⟩ := σ.surjective i
      obtain ⟨j, rfl⟩ := σ.surjective j
      rw [par_apply]
      rcases i with i | i <;> rcases j with j | j
      · simpa using hu i j hij
      · simp
      · simp
      · exact absurd ((h₂ i).trans (h₂ j).symm) hij

theorem label_eq_of_opposite : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (n : ℕ) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (Gn g n) W) (ρ' : Representation ℂ (Gn g n) W') (T : W →ₗ[ℂ] W') (a : Fin n → ℤ) (f f' : (ZMod g)[X]), (∀ u : Gn g n, (∀ i j, ¬ a i < a j → (u : Mt g n) i j = (1 : Mt g n) i j) → T ∘ₗ ρ u = T) → (∀ u : Gn g n, (∀ i j, ¬ a j < a i → (u : Mt g n) i j = (1 : Mt g n) i j) → ρ' u ∘ₗ T = T) → (∀ m : Gn g n, (∀ i j, a i ≠ a j → (m : Mt g n) i j = 0) → T ∘ₗ ρ m = ρ' m ∘ₗ T) → (∀ w, ρ.asAlgebraHom (eSerC L n f) w = w) → (∀ w', ρ'.asAlgebraHom (eSerC L n f') w' = w') → T ≠ 0 → f = f' := by
  intro g _ L h5 hG n W W' _ _ _ _ ρ ρ' T a f f' hU hU' hM h h' hT
  by_contra hf
  refine hT (LinearMap.ext fun w => ?_)
  have := vanish L h5 hG T n ρ ρ' a hU hU' hM f f' hf w
  rwa [h, h'] at this

end GlobalTheory.GLq.Opp
