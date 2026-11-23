import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LieFilt

theorem det_eq_one_of_blockUni {ι : Type} [Fintype ι] [DecidableEq ι] (bl : ι → ℕ) {R : Type} [CommRing R]
    {N : Matrix ι ι R} (hN : BlockUni bl N) : N.det = 1 := by
  have hT : N.BlockTriangular bl := by
    intro i j hij
    have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    rw [hN i j (lt_asymm hij)]
    simp [Matrix.one_apply, hne]
  rw [hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have h1 : N.toSquareBlock bl a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    have hij : ¬ bl i < bl j := by
      omega
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    rw [hN i j hij]
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [h1, Matrix.det_one]

theorem minor_mul_blockUni {κ : Type} [Fintype κ] (bl : κ → ℕ) {g : ℕ} {R : Type} [CommRing R]
    (w : κ ≃ Fin g) (k : ℕ) (P : Matrix (Fin g) κ R) {N : Matrix κ κ R} (hN : BlockUni bl N) :
    minor bl w k (P * N) = minor bl w k P := by
  unfold minor
  have hmul : ((P * N).submatrix w id).toSquareBlockProp (fun z => bl z < k) =
      (P.submatrix w id).toSquareBlockProp (fun z => bl z < k) * N.toSquareBlockProp (fun z => bl z < k) := by
    ext ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Matrix.toSquareBlockProp_def, Matrix.of_apply, Matrix.submatrix_apply, Matrix.mul_apply, id]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun z => bl z < k)]
    have h0 : ∑ z : {z // ¬ bl z < k}, P (w a) z * N z b = 0 := by
      refine Finset.sum_eq_zero fun z _ => ?_
      have hzb : ¬ bl z < bl b := by have := z.2; omega
      have hne : (z : κ) ≠ b := fun h => z.2 (h ▸ hb)
      rw [hN _ _ hzb]
      simp [Matrix.one_apply, hne]
    rw [h0, add_zero]
  have hdet : (N.toSquareBlockProp (fun z => bl z < k)).det = 1 := by
    have hbu : BlockUni (fun z : {z // bl z < k} => bl z) (N.toSquareBlockProp (fun z => bl z < k)) := by
      intro z z' h
      simp only [Matrix.toSquareBlockProp_def, Matrix.of_apply]
      rw [hN _ _ h]
      simp [Matrix.one_apply, Subtype.ext_iff]
    exact det_eq_one_of_blockUni _ hbu
  rw [hmul]
  rw [Matrix.det_mul]
  rw [hdet, mul_one]

theorem norm_det_le_one_of_ultra {K : Type} [NormedField K] [IsUltrametricDist K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι K) (hM : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one _ _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => hM _ _)

theorem norm_eq_one_of_mul {K : Type} [NormedField K] {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (h : 1 ≤ ‖a‖ * ‖b‖) : ‖b‖ = 1 := by
  have := norm_nonneg a
  have := norm_nonneg b
  nlinarith

theorem exists_perm_lower_minor {K : Type} [NormedField K] [IsUltrametricDist K] : ∀ (n : ℕ)
    (M : Matrix (Fin n) (Fin n) K), (∀ i j, ‖M i j‖ ≤ 1) → ‖M.det‖ = 1 →
    ∃ σ : Equiv.Perm (Fin n), ∀ p : Fin n → Prop, (∀ a b, b ≤ a → p a → p b) →
      ‖((M.submatrix σ id).toSquareBlockProp p).det‖ = 1 := by
  intro n
  induction n with
  | zero =>
    intro M _ _
    refine ⟨1, fun p _ => ?_⟩
    haveI : IsEmpty {a : Fin 0 // p a} := ⟨fun x => Fin.elim0 x.1⟩
    simp [Matrix.det_isEmpty]
  | succ n ih =>
    intro M hM hdet
    have hexp := Matrix.det_succ_column M (Fin.last n)
    obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty Finset.univ_nonempty
      (fun i : Fin (n+1) => (-1) ^ ((i : ℕ) + (Fin.last n : ℕ)) * M i (Fin.last n) *
        (M.submatrix i.succAbove (Fin.last n).succAbove).det)
    rw [← hexp, hdet] at hi
    set M' : Matrix (Fin n) (Fin n) K := M.submatrix i.succAbove Fin.castSucc with hM'
    have hM'int : ∀ a b, ‖M' a b‖ ≤ 1 := fun a b => hM _ _
    have hdet' : ‖M'.det‖ = 1 := by
      rw [Fin.succAbove_last] at hi
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at hi
      exact norm_eq_one_of_mul (hM _ _) (norm_det_le_one_of_ultra _ hM'int) hi
    obtain ⟨σ', hσ'⟩ := ih M' hM'int hdet'
    let f : Fin (n+1) → Fin (n+1) := Fin.lastCases i (fun j => i.succAbove (σ' j))
    have hf_last : f (Fin.last n) = i := Fin.lastCases_last
    have hf_cs : ∀ j, f j.castSucc = i.succAbove (σ' j) := fun j => Fin.lastCases_castSucc j
    have hinj : Function.Injective f := by
      intro x y h
      induction x using Fin.lastCases with
      | last =>
        induction y using Fin.lastCases with
        | last => rfl
        | cast b => rw [hf_last, hf_cs] at h; exact absurd h.symm (Fin.succAbove_ne _ _)
      | cast a =>
        induction y using Fin.lastCases with
        | last => rw [hf_last, hf_cs] at h; exact absurd h (Fin.succAbove_ne _ _)
        | cast b =>
          rw [hf_cs, hf_cs] at h
          rw [σ'.injective (Fin.succAbove_right_injective h)]
    let σ : Equiv.Perm (Fin (n+1)) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
    have hσ : ∀ j, σ j = f j := fun j => rfl
    refine ⟨σ, fun p hp => ?_⟩
    by_cases hl : p (Fin.last n)
    · have hall : ∀ j, p j := fun j => hp _ _ (Fin.le_last j) hl
      have hsub : (M.submatrix σ id).toSquareBlockProp p =
          (M.submatrix σ id).submatrix (Equiv.subtypeUnivEquiv hall) (Equiv.subtypeUnivEquiv hall) := rfl
      rw [hsub, Matrix.det_submatrix_equiv_self, Matrix.det_permute]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, hdet]
    · have hcs : ∀ y : {a : Fin (n+1) // p a}, (y : Fin (n+1)) ≠ Fin.last n := fun y h => hl (h ▸ y.2)
      let φ : {j : Fin n // p j.castSucc} ≃ {a : Fin (n+1) // p a} :=
        { toFun := fun x => ⟨x.1.castSucc, x.2⟩
          invFun := fun y => ⟨(y : Fin (n+1)).castPred (hcs y), by simpa using y.2⟩
          left_inv := fun x => by ext; simp
          right_inv := fun y => by ext; simp }
      have hsub : ((M.submatrix σ id).toSquareBlockProp p).submatrix φ φ =
          (M'.submatrix σ' id).toSquareBlockProp (fun j => p j.castSucc) := by
        ext a b
        simp [φ, Matrix.toSquareBlockProp_def, hσ, hf_cs, M']
      rw [← Matrix.det_submatrix_equiv_self φ, hsub]
      exact hσ' _ fun a b hab h => hp _ _ (Fin.castSucc_le_castSucc_iff.mpr hab) h

theorem intAdapted_minor {K : Type} [NormedField K] [IsUltrametricDist K] {κ : Type} [Fintype κ] (bl : κ → ℕ) {g : ℕ}
    (P : Matrix (Fin g) κ K) (hP : IntAdapted bl P) :
    (∀ (w : κ ≃ Fin g) (k : ℕ), ‖minor bl w k P‖ ≤ 1) ∧ ∃ w : κ ≃ Fin g, ∀ k : ℕ, ‖minor bl w k P‖ = 1 := by
  obtain ⟨N, C', hN, hint, hC, h1, h2⟩ := hP
  have hmin : ∀ w k, minor bl w k P = minor bl w k (P * N) := fun w k => (minor_mul_blockUni bl w k P hN).symm
  refine ⟨fun w k => ?_, ?_⟩
  · rw [hmin]
    unfold minor
    exact norm_det_le_one_of_ultra _ fun a b => by
      simp only [Matrix.toSquareBlockProp_def, Matrix.of_apply, Matrix.submatrix_apply, id]
      exact hint _ _
  · have hcard : Fintype.card κ = g := by
      have e : (κ → K) ≃ₗ[K] (Fin g → K) := LinearEquiv.ofLinear (Matrix.mulVecLin (P * N)) (Matrix.mulVecLin C')
        (by rw [← Matrix.mulVecLin_mul, h1, Matrix.mulVecLin_one])
        (by rw [← Matrix.mulVecLin_mul, h2, Matrix.mulVecLin_one])
      have := e.finrank_eq
      simpa using this
    let e0 : κ ≃ Fin g := Fintype.equivFinOfCardEq hcard
    let fs : Fin g → ℕ := fun j => bl (e0.symm j)
    let e : κ ≃ Fin g := e0.trans (Tuple.sort fs).symm
    have hmono : Monotone (fun j => bl (e.symm j)) := by
      intro a b hab
      have := Tuple.monotone_sort fs hab
      simpa [e, fs] using this
    let A := P * N
    let M : Matrix (Fin g) (Fin g) K := A.submatrix id e.symm
    have hMint : ∀ a b, ‖M a b‖ ≤ 1 := fun a b => hint _ _
    have hMC : M * C'.submatrix e.symm id = 1 := by
      rw [show M = A.submatrix id e.symm from rfl, Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_id_id]
    have hdetM : ‖M.det‖ = 1 := by
      have h := congrArg (fun X => ‖Matrix.det X‖) hMC
      simp only [Matrix.det_mul, Matrix.det_one, norm_mul, norm_one] at h
      have hM1 := norm_det_le_one_of_ultra M hMint
      have hC1 := norm_det_le_one_of_ultra (C'.submatrix e.symm id) fun a b => hC _ _
      exact norm_eq_one_of_mul hC1 hM1 (by rw [mul_comm, h])
    obtain ⟨σ, hσ⟩ := exists_perm_lower_minor g M hMint hdetM
    refine ⟨e.trans σ, fun k => ?_⟩
    rw [hmin]
    let q : Fin g → Prop := fun j => bl (e.symm j) < k
    have hq : ∀ a b, b ≤ a → q a → q b := fun a b hab h => lt_of_le_of_lt (hmono hab) h
    let φ : {z // bl z < k} ≃ {j // q j} := e.subtypeEquiv fun z => by simp [q]
    have hsub : ((M.submatrix σ id).toSquareBlockProp q).submatrix φ φ =
        ((P * N).submatrix (e.trans σ) id).toSquareBlockProp (fun z => bl z < k) := by
      ext a b
      simp [φ, M, A, Matrix.toSquareBlockProp_def]
    unfold minor
    rw [← hsub, Matrix.det_submatrix_equiv_self]
    convert hσ q hq

end GlobalTheory.LieFilt
