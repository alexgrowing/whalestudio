import Mathlib
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnrM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsNrm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem.LamMul

section Blocks

variable {S : Type*} [CommRing S] {r c : ℕ}

theorem det_eq_of_lower_zero (M : Matrix (Fin (r + c)) (Fin (r + c)) S)
    (h : M.submatrix (Fin.natAdd r) (Fin.castAdd c) = 0) :
    M.det = (M.submatrix (Fin.castAdd c) (Fin.castAdd c)).det * (M.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
  have e : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (M.submatrix (Fin.castAdd c) (Fin.castAdd c)) (M.submatrix (Fin.castAdd c) (Fin.natAdd r)) 0
        (M.submatrix (Fin.natAdd r) (Fin.natAdd r)) := by
    rw [← h]
    ext (i | i) (j | j) <;> simp
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, e, Matrix.det_fromBlocks_zero₂₁]

theorem mul_dd_of_lower_zero (M N : Matrix (Fin (r + c)) (Fin (r + c)) S)
    (h : M.submatrix (Fin.natAdd r) (Fin.castAdd c) = 0) :
    (M * N).submatrix (Fin.natAdd r) (Fin.natAdd r) =
      M.submatrix (Fin.natAdd r) (Fin.natAdd r) * N.submatrix (Fin.natAdd r) (Fin.natAdd r) := by
  ext i j
  have h0 : ∀ a, M (Fin.natAdd r i) (Fin.castAdd c a) = 0 := fun a => congrFun (congrFun h i) a
  simp [Matrix.mul_apply, Fin.sum_univ_add, h0]

theorem dd_mod (I : Ideal S) (K K' : Matrix (Fin (r + c)) (Fin (r + c)) S)
    (hK : ∀ i j, K (Fin.natAdd r i) (Fin.castAdd c j) ∈ I) (hK' : ∀ i j, K' (Fin.natAdd r i) (Fin.castAdd c j) ∈ I)
    (hu : IsUnit K.det) (hu' : IsUnit K'.det) :
    IsUnit (Ideal.Quotient.mk I (K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) ∧
    IsUnit (Ideal.Quotient.mk I (K'.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) ∧
    ((K * K').submatrix (Fin.natAdd r) (Fin.natAdd r)).det -
      (K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det * (K'.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ∈ I := by
  have key : ∀ X : Matrix (Fin (r + c)) (Fin (r + c)) S, (∀ i j, X (Fin.natAdd r i) (Fin.castAdd c j) ∈ I) →
      ((Ideal.Quotient.mk I).mapMatrix X).submatrix (Fin.natAdd r) (Fin.castAdd c) = 0 := by
    intro X hX
    ext i j
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hX i j
  have sub : ∀ X : Matrix (Fin (r + c)) (Fin (r + c)) S, Ideal.Quotient.mk I (X.submatrix (Fin.natAdd r) (Fin.natAdd r)).det =
      (((Ideal.Quotient.mk I).mapMatrix X).submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    intro X
    rw [RingHom.map_det]
    rfl
  have unit : ∀ X : Matrix (Fin (r + c)) (Fin (r + c)) S, (∀ i j, X (Fin.natAdd r i) (Fin.castAdd c j) ∈ I) →
      IsUnit X.det → IsUnit (Ideal.Quotient.mk I (X.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) := by
    intro X hX hu
    have h1 : IsUnit ((Ideal.Quotient.mk I).mapMatrix X).det := by
      rw [← RingHom.map_det]
      exact hu.map _
    rw [det_eq_of_lower_zero _ (key X hX)] at h1
    rw [sub]
    exact isUnit_of_mul_isUnit_right h1
  refine ⟨unit K hK hu, unit K' hK' hu', ?_⟩
  rw [← Ideal.Quotient.eq, map_mul, sub, sub, sub, map_mul,
    mul_dd_of_lower_zero _ _ (key K hK), Matrix.det_mul]

end Blocks

section Val

variable {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ) (O : Subring F) (ε : Γ)

def redI (hO : ∀ x ∈ O, v x ≤ 1) : Ideal O where
  carrier := {a | v (a : F) ≤ ε}
  add_mem' {a b} ha hb := by
    show v ((a : F) + b) ≤ ε
    exact (v.map_add _ _).trans (max_le ha hb)
  zero_mem' := by
    show v ((0 : O) : F) ≤ ε
    simp
  smul_mem' a b hb := by
    show v ((a : F) * b) ≤ ε
    rw [map_mul]
    exact (mul_le_of_le_one_left' (hO _ a.2)).trans hb

variable {v O ε}

theorem val_eq_one_of_isUnit (hO : ∀ x ∈ O, v x ≤ 1) (hε : ε < 1) (a : O)
    (h : IsUnit (Ideal.Quotient.mk (redI v O ε hO) a)) : v (a : F) = 1 := by
  obtain ⟨b, hb⟩ := h.exists_right_inv
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have h1 : a * b - 1 ∈ redI v O ε hO := by
    apply Ideal.Quotient.eq.1
    simpa using hb
  have h2 : v ((a : F) * b - 1) ≤ ε := by
    have h1' : v (((a * b - 1 : O)) : F) ≤ ε := h1
    simpa using h1'
  have h3 : v ((a : F) * b) = 1 := by
    have e : (a : F) * b = ((a : F) * b - 1) + 1 := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    · simp
    · simpa using h2.trans_lt hε
  rw [map_mul] at h3
  refine le_antisymm (hO _ a.2) ?_
  rw [← h3]
  exact mul_le_of_le_one_right' (hO _ b.2)

omit [LinearOrderedCommGroupWithZero Γ] in

theorem exists_lift {n : ℕ} {k : GL (Fin n) F} (hk : k ∈ GLint O n) :
    ∃ K : Matrix (Fin n) (Fin n) O, (k : Matrix (Fin n) (Fin n) F) = K.map O.subtype ∧ IsUnit K.det := by
  let K : Matrix (Fin n) (Fin n) O := fun i j => ⟨(k : Matrix (Fin n) (Fin n) F) i j, hk.1 i j⟩
  let K' : Matrix (Fin n) (Fin n) O := fun i j => ⟨((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j, hk.2 i j⟩
  have e : (k : Matrix (Fin n) (Fin n) F) = K.map O.subtype := by ext i j; rfl
  have e' : ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = K'.map O.subtype := by ext i j; rfl
  refine ⟨K, e, Matrix.isUnit_det_of_right_inverse (B := K') ?_⟩
  apply Matrix.map_injective (f := O.subtype) Subtype.val_injective
  show (K * K').map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
  rw [Matrix.map_mul, ← e, ← e', ← Units.val_mul, mul_inv_cancel, Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

omit [LinearOrderedCommGroupWithZero Γ] in
theorem det_dd_map {r c : ℕ} (K : Matrix (Fin (r + c)) (Fin (r + c)) O) :
    (bDD (K.map O.subtype)).det = (((K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : O) : F) := by
  show _ = O.subtype _
  rw [RingHom.map_det]
  rfl

theorem dd_val (hO : ∀ x ∈ O, v x ≤ 1) (hε : ε < 1) {r c : ℕ} {k k' : GL (Fin (r + c)) F}
    (hk : k ∈ GLint O (r + c)) (hk' : k' ∈ GLint O (r + c))
    (hd : ∀ i j, v ((k : Matrix (Fin (r + c)) (Fin (r + c)) F) (Fin.natAdd r i) (Fin.castAdd c j)) ≤ ε)
    (hd' : ∀ i j, v ((k' : Matrix (Fin (r + c)) (Fin (r + c)) F) (Fin.natAdd r i) (Fin.castAdd c j)) ≤ ε) :
    v (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    v (bDD (k' : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    v ((bDD ((k * k' : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)).det -
      (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * (bDD (k' : Matrix (Fin (r + c)) (Fin (r + c)) F)).det) ≤ ε := by
  obtain ⟨K, e, hu⟩ := exists_lift hk
  obtain ⟨K', e', hu'⟩ := exists_lift hk'
  have hK : ∀ i j, K (Fin.natAdd r i) (Fin.castAdd c j) ∈ redI v O ε hO := fun i j => by
    have := hd i j
    rw [e] at this
    exact this
  have hK' : ∀ i j, K' (Fin.natAdd r i) (Fin.castAdd c j) ∈ redI v O ε hO := fun i j => by
    have := hd' i j
    rw [e'] at this
    exact this
  obtain ⟨h1, h2, h3⟩ := dd_mod (redI v O ε hO) K K' hK hK' hu hu'
  have em : ((k * k' : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = (K * K').map O.subtype := by
    rw [Units.val_mul, e, e', Matrix.map_mul]
  rw [em, e, e', det_dd_map, det_dd_map, det_dd_map]
  refine ⟨val_eq_one_of_isUnit hO hε _ h1, val_eq_one_of_isUnit hO hε _ h2, ?_⟩
  have h3' : v (((((K * K').submatrix (Fin.natAdd r) (Fin.natAdd r)).det -
      (K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det * (K'.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : O)) : F) ≤ ε := h3
  simpa using h3'

end Val

section Main

theorem lamJ_mul : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (δ : (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) (P.adicCompletion L)), k ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → k' ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → lamJ δ (k * k') = lamJ δ k * lamJ δ k' := by
  intro L _ _ P δ hδ r c k k' hk hk'
  have hO : ∀ x ∈ OP P, Valued.v x ≤ 1 := fun x hx => hx
  have hε : (WithZero.exp (-1 : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπ : Valued.v (piP P : P.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec P
  have small : ∀ {g : GL (Fin (r + c)) (P.adicCompletion L)}, g ∈ parJ (OP P) (piP P : P.adicCompletion L) r c →
      ∀ i j, Valued.v ((g : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) (Fin.natAdd r i) (Fin.castAdd c j)) ≤
        WithZero.exp (-1 : ℤ) := by
    intro g hg i j
    obtain ⟨o, ho, e⟩ := hg.2 i j
    have e' : (g : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) (Fin.natAdd r i) (Fin.castAdd c j) =
        (piP P : P.adicCompletion L) * o := e
    rw [e', map_mul, hπ]
    exact mul_le_of_le_one_right' (hO _ ho)
  obtain ⟨ha, hb, hxy⟩ := dd_val hO hε hk.1 hk'.1 (small hk) (small hk')
  unfold lamJ
  set a := (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det with hadef
  set b := (bDD (k' : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det with hbdef
  set x := (bDD ((k * k' : GL (Fin (r + c)) (P.adicCompletion L)) : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det with hxdef
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hab : Valued.v (a * b) = 1 := by rw [map_mul, ha, hb, one_mul]
  have hx : Valued.v x = 1 := by
    have e : x = (x - a * b) + a * b := by ring
    rw [e, Valuation.map_add_eq_of_lt_right, hab]
    rw [hab]
    exact hxy.trans_lt hε
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  have tame := hδ.tame (Units.mk0 x hx0 * (Units.mk0 a ha0 * Units.mk0 b hb0)⁻¹) (by
    show Valued.v _ = 1
    simp [hx, ha, hb]) (by
    have e : x * (a * b)⁻¹ - 1 = (x - a * b) * (a * b)⁻¹ := by field_simp
    simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
    rw [e, map_mul, map_inv₀, hab, inv_one, mul_one]
    exact hxy)
  rw [map_mul, map_inv, mul_inv_eq_one, map_mul] at tame
  simp only [chi0, dif_neg hx0, dif_neg ha0, dif_neg hb0, tame, Units.val_mul]

end Main

end GlobalTheory.Mem.LamMul
