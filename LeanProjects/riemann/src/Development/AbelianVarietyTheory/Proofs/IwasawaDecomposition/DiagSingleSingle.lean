import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NegOneNormFromCmFieldFiniteAdelesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasSignatureDiagonalSgn

noncomputable section

namespace GlobalTheory.Mem.DiagSp

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField IsDedekindDomain
open scoped TensorProduct

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def cut (N p : ℕ) : Fin N → Bool := fun i => decide (p ≤ (i : ℕ))

theorem card_cut_false (N p : ℕ) (h : p ≤ N) :
    (Finset.univ.filter fun i => cut N p i = false).card = p := by
  have : (Finset.univ.filter fun i => cut N p i = false) =
      (Finset.univ.filter fun i : Fin N => (i : ℕ) < p) := by
    ext i; simp [cut]
  rw [this, Fin.card_filter_val_lt]
  omega

theorem card_cut_true (N p : ℕ) (h : p ≤ N) :
    (Finset.univ.filter fun i => cut N p i = true).card = N - p := by
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (fun i => cut N p i = false)
  rw [card_cut_false N p h, Finset.card_univ, Fintype.card_fin] at h1
  have : (Finset.univ.filter fun i => cut N p i = true) =
      (Finset.univ.filter fun i => ¬ cut N p i = false) := by
    ext i; simp
  rw [this]
  omega

def signSpace (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) (neg : Fin N → Bool) :
    HSpace E :=
  stdSpace hstar N neg (Finset.univ.filter fun i => neg i = false).card
    (Finset.univ.filter fun i => neg i = true).card

theorem signSpace_sigOK (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ)
    (neg : Fin N → Bool) : (signSpace hstar N neg).SigOK :=
  GlobalTheory.stdSpace_sigOK_count E hstar N neg

theorem signSpace_cut_sig (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N p : ℕ)
    (h : p ≤ N) (τ : E →+* ℂ) : (signSpace hstar N (cut N p)).sig τ = (p, N - p) :=
  Prod.ext (card_cut_false N p h) (card_cut_true N p h)

def extTo (n N : ℕ) : (Fin n → E) →ₗ[E] (Fin N → E) where
  toFun x := fun i => if h : (i : ℕ) < n then x ⟨i, h⟩ else 0
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem extTo_of_le (n N : ℕ) (x : Fin n → E) (i : Fin N) (h : n ≤ (i : ℕ)) : extTo n N x i = 0 := by
  simp [extTo, not_lt.2 h]

theorem extTo_castLE (n N : ℕ) (hn : n ≤ N) (x : Fin n → E) (i : Fin n) :
    extTo n N x (Fin.castLE hn i) = x i := by
  simp [extTo]

theorem extTo_isom (n N : ℕ) (hn : n ≤ N) (neg : Fin n → Bool) (neg' : Fin N → Bool)
    (hneg : ∀ i, neg' (Fin.castLE hn i) = neg i) (x y : Fin n → E) :
    diagForm N neg' (extTo n N x) (extTo n N y) = diagForm n neg x y := by
  rw [diagForm_apply, diagForm_apply]
  symm
  refine Finset.sum_of_injOn (Fin.castLE hn) (Fin.castLE_injective hn).injOn
    (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro i _ hi
    have : n ≤ (i : ℕ) := by
      by_contra hlt
      exact hi ⟨⟨i, not_le.1 hlt⟩, by simp, Fin.ext rfl⟩
    rw [extTo_of_le n N y i this, mul_zero]
  · intro i _
    rw [extTo_castLE, extTo_castLE, hneg]

theorem diag_single_single (N : ℕ) (neg : Fin N → Bool) (i j : Fin N) (a b : E) :
    diagForm N neg (Pi.single i a) (Pi.single j b) =
      if (i : ℕ) = j then star a * sgn (neg i) * b else 0 := by
  rw [diagForm_single_left]
  by_cases h : i = j
  · subst h; simp
  · have h' : ¬ (i : ℕ) = j := fun e => h (Fin.ext e)
    simp [h, h']

theorem diag_ext_single (n N : ℕ) (neg : Fin N → Bool) (x : Fin n → E) (j : Fin N) (b : E)
    (h : n ≤ (j : ℕ)) : diagForm N neg (extTo n N x) (Pi.single j b) = 0 := by
  rw [diagForm_single_right, extTo_of_le n N x j h]
  simp

theorem ortho_sign (N : ℕ) (b : Bool) : Formalism.HermitianLatticesTheory.IsOrthoLattice
    (if b then -(diagForm (E := E) N (fun _ => b)) else diagForm (E := E) N (fun _ => b)) (stdLat N) N := by
  refine ⟨Pi.basisFun E (Fin N), (Pi.basisFun E (Fin N)).linearIndependent,
    (Pi.basisFun E (Fin N)).span_eq, rfl, fun i j => ?_⟩
  rw [Pi.basisFun_apply, Pi.basisFun_apply]
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [diagForm_single]
    simp [sgn]
  · simp only [if_true, LinearMap.neg_apply]
    rw [diagForm_single]
    split_ifs <;> simp [sgn]

theorem sign_congr {A : Type} [CommRing A] (σ : A →+* A) (ι : E →+* A) (y : A) (hy : σ y * y = -1)
    (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) (s t : Fin N → Bool) :
    ∃ g : GL (Fin N) A, Formalism.UG.cT σ (g : Matrix (Fin N) (Fin N) A) *
      Matrix.map (m := Fin N) (n := Fin N) (signSpace hstar N s).gram ι * (g : Matrix (Fin N) (Fin N) A) =
      Matrix.map (m := Fin N) (n := Fin N) (signSpace hstar N t).gram ι := by
  have hyu : y * (-(σ y)) = 1 := by rw [mul_neg, mul_comm, hy, neg_neg]
  have hg : ∀ s : Fin N → Bool, Matrix.map (m := Fin N) (n := Fin N) (signSpace hstar N s).gram ι =
      Matrix.diagonal fun i : Fin N => (sgn (s i) : A) := by
    intro s
    ext i j
    refine (congrArg ι (stdSpace_gram_apply hstar N s _ _ i j)).trans ?_
    change ι (if i = j then (sgn (s i) : E) else 0) = if i = j then (sgn (s i) : A) else 0
    by_cases h : i = j <;> simp [h, map_sgn]
  refine ⟨diagUnit (fun i => if s i = t i then 1 else y) (fun i => if s i = t i then 1 else -(σ y))
    (fun i => by split_ifs <;> simp [hyu]), ?_⟩
  rw [hg, hg, diagUnit_val]
  refine diag_congr σ _ _ _ fun i => ?_
  cases hs : s i <;> cases ht : t i <;> simp [sgn, hy]

end General

section Ranks

variable (R : Ranks)

def pY (j : ℕ) : ℕ := R.rankY j - (R.m - j) / 2

theorem rankY_zero : R.rankY 0 = R.k + 2 * R.rS + 1 := by
  obtain ⟨c, hc⟩ := R.m_even
  have := R.two_le_m
  simp only [Ranks.rankY, Ranks.r, Ranks.rS]
  omega

theorem pY_zero : pY R 0 = R.k + R.rS := by
  obtain ⟨c, hc⟩ := R.m_even
  have := R.two_le_m
  simp only [pY, Ranks.rankY, Ranks.r, Ranks.rS]
  omega

theorem N_zero : R.N 0 = R.k := by simp [Ranks.N]

theorem N_le_pY (j : ℕ) (hj : j < R.m) : R.N j ≤ pY R j := by
  simp only [pY, Ranks.rankY, Ranks.r, Ranks.N, mul_add]
  omega

theorem N_top : R.N R.m = R.rankY R.m + 1 := by
  have := R.two_le_m
  simp only [Ranks.rankY, Ranks.r, Ranks.N, mul_add]
  omega

theorem sub_pY (j : ℕ) : R.rankY j - pY R j = (R.m - j) / 2 := by
  have := R.m_add_three_le_k
  simp only [pY, Ranks.rankY, Ranks.r]
  omega

def idxP (i : Fin R.rS) : Fin (R.rankY 0) := ⟨R.k + i, by have := rankY_zero R; omega⟩

def idxM (i : Fin R.rS) : Fin (R.rankY 0) := ⟨R.k + R.rS + i, by have := rankY_zero R; omega⟩

def idxZ : Fin (R.rankY 0) := ⟨R.k + 2 * R.rS, by have := rankY_zero R; omega⟩

theorem cut_idxP (i : Fin R.rS) : cut _ (pY R 0) (idxP R i) = false := by
  simp [cut, idxP, pY_zero]

theorem cut_idxM (i : Fin R.rS) : cut _ (pY R 0) (idxM R i) = true := by
  simp [cut, idxM, pY_zero]

theorem cut_idxZ : cut _ (pY R 0) (idxZ R) = true := by
  simp only [cut, idxZ, pY_zero, decide_eq_true_eq]; omega

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def hypVec (a b : E) (i : Fin R.rS) : Fin (R.rankY 0) → E :=
  Pi.single (idxP R i) a + Pi.single (idxM R i) b

theorem hypVec_hypVec (a b c d : E) (i j : Fin R.rS) :
    diagForm _ (cut _ (pY R 0)) (hypVec R a b i) (hypVec R c d j) =
      if i = j then star a * c - star b * d else 0 := by
  simp only [hypVec, map_add, LinearMap.add_apply, diag_single_single, cut_idxP, cut_idxM]
  have hi := i.isLt
  have hj := j.isLt
  have e1 : ¬ ((idxP R i : ℕ) = idxM R j) := by simp only [idxP, idxM]; omega
  have e2 : ¬ ((idxM R i : ℕ) = idxP R j) := by simp only [idxP, idxM]; omega
  rw [if_neg e1, if_neg e2]
  by_cases h : i = j
  · subst h
    simp [sgn, sub_eq_add_neg]
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    have e3 : ¬ ((idxP R i : ℕ) = idxP R j) := by simp only [idxP]; omega
    have e4 : ¬ ((idxM R i : ℕ) = idxM R j) := by simp only [idxM]; omega
    rw [if_neg e3, if_neg e4, if_neg h]
    simp

theorem ext_hypVec (x : Fin (R.N 0) → E) (a b : E) (i : Fin R.rS) :
    diagForm _ (cut _ (pY R 0)) (extTo (R.N 0) (R.rankY 0) x) (hypVec R a b i) = 0 := by
  rw [hypVec, map_add, diag_ext_single, diag_ext_single, add_zero]
  · simp only [idxM, N_zero]; omega
  · simp only [idxP, N_zero]; omega

theorem z_hypVec (c a b : E) (i : Fin R.rS) :
    diagForm _ (cut _ (pY R 0)) (Pi.single (idxZ R) c) (hypVec R a b i) = 0 := by
  have hi := i.isLt
  rw [hypVec, map_add, diag_single_single, diag_single_single, if_neg, if_neg, add_zero]
  · simp only [idxM, idxZ]; omega
  · simp only [idxP, idxZ]; omega

end Ranks

section Main

variable (R : Ranks) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (vn : ℕ → Bool)

def spY (j : ℕ) : HSpace E := signSpace star_isIntegral (R.rankY j) (cut _ (pY R j))

def spW (j : ℕ) : HSpace E := signSpace star_isIntegral (R.rankY 0) (cut _ (R.k + j - 1))

theorem spY_sig (j : ℕ) (τ : E →+* ℂ) : (spY (E := E) R j).sig τ = sigYD R j := by
  rw [spY, signSpace_cut_sig _ _ (pY R _) (Nat.sub_le _ _), sub_pY]
  rfl

def spacesStd : Spaces R F E where
  cm := cm
  T := T
  T_prime := hT
  X := fun j => posSpace star_isIntegral (R.N j)
  X_sig := fun j => posSpace_sigOK _ _
  X_rank := fun _ _ => rfl
  X_def := fun _ _ _ => Or.inl rfl
  X' := posSpace star_isIntegral (R.rankY R.m)
  X'_sig := posSpace_sigOK _ _
  X'_rank := rfl
  iX' := extTo (R.rankY R.m) (R.N R.m)
  iX'_isom := fun x y => extTo_isom _ _ (by rw [N_top]; omega) (fun _ => false) (fun _ => false)
    (fun _ => rfl) x y
  z := Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) 1
  z_anis := by
    refine ne_of_eq_of_ne (diag_single_single _ (fun _ => false) _ _ 1 1) ?_
    simp [sgn]
  z_orth := fun x => diag_ext_single _ _ (fun _ => false) x _ 1 le_rfl
  Y := spY R
  Y_sig := fun _ => signSpace_sigOK _ _ _
  Y_rank := fun _ _ => rfl
  iXY := fun j => extTo (R.N j) (R.rankY j)
  iXY_isom := fun j hj x y => extTo_isom _ _ ((N_le_pY R j hj).trans (Nat.sub_le _ _))
    (fun _ => false) (cut _ (pY R j)) (fun i => by
      have := N_le_pY R j hj
      have := i.isLt
      simp only [cut, Fin.val_castLE, decide_eq_false_iff_not]
      omega) x y
  eYm := LinearEquiv.refl E (Fin (R.rankY R.m) → E)
  eYm_isom := fun x y => by
    have : cut (R.rankY R.m) (pY R R.m) = fun _ => false := by
      funext i
      have := i.isLt
      simp only [cut, pY, decide_eq_false_iff_not, Nat.sub_self, Nat.zero_div, Nat.sub_zero]
      exact not_le.2 this
    change diagForm _ (cut (R.rankY R.m) (pY R R.m)) x y = diagForm _ (fun _ => false) x y
    rw [this]
  zm := Pi.single (idxZ R) pz
  zm_norm := by
    refine (diag_single_single _ (cut _ (pY R 0)) _ _ pz pz).trans ?_
    rw [if_pos rfl, cut_idxZ, ← hpz]
    simp [sgn]
  zm_orth := fun x => diag_ext_single _ _ (cut _ (pY R 0)) x _ pz (by simp only [idxZ, N_zero]; omega)
  hypE := hypVec R 1 1
  hypF := hypVec R (1 / 2) (-(1 / 2))
  hyp_ee := fun i j => (hypVec_hypVec R _ _ _ _ i j).trans (by simp)
  hyp_ff := fun i j => (hypVec_hypVec R _ _ _ _ i j).trans (by simp)
  hyp_ef := fun i j => (hypVec_hypVec R _ _ _ _ i j).trans (by
    split_ifs
    · rw [star_one]; norm_num
    · rfl)
  hyp_orthX := fun i x => ⟨ext_hypVec R x _ _ i, ext_hypVec R x _ _ i⟩
  hyp_orthz := fun i => ⟨z_hypVec R _ _ _ i, z_hypVec R _ _ _ i⟩
  baseSpace_signature_eq := fun τ => by
    rw [spY, signSpace_cut_sig _ _ (pY R _) (Nat.sub_le _ _)]
    have h1 := pY_zero R
    have h2 := rankY_zero R
    refine Prod.ext h1 ?_
    change R.rankY 0 - pY R 0 = R.rS + 1
    omega
  W := spW R
  W_sig := fun _ => signSpace_sigOK _ _ _
  W_rank := fun _ _ _ => by
    change R.rankY 0 = R.r
    simp [Ranks.rankY]
  W_sigval := fun j h1 h2 τ => by
    have h : R.rankY 0 = R.k + R.m - 1 := by simp [Ranks.rankY, Ranks.r]
    rw [spW, signSpace_cut_sig _ _ _ (by omega)]
    refine Prod.ext rfl ?_
    change R.rankY 0 - (R.k + j - 1) = R.m - j
    omega
  baseSpace_isometric_graded := fun j _ _ => by
    obtain ⟨y, hy⟩ := GlobalTheory.T.neg_one_norm_from_cmField_finiteAdeles F E cm
    obtain ⟨g, hg⟩ := sign_congr (Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F))
      (Formalism.UG.inclE (FiniteAdeleRing (𝓞 F) F)) y hy star_isIntegral (R.rankY 0) (cut _ (pY R 0))
      (cut _ (R.k + j - 1))
    exact ⟨Equiv.refl _, g, hg⟩
  V := fun j => signSpace star_isIntegral R.nV (fun _ => vn j)
  V_sig := fun _ => signSpace_sigOK _ _ _
  V_rank := fun _ _ _ => rfl
  Vneg := vn
  V_std := fun j _ _ => ortho_sign R.nV (vn j)

end Main

end GlobalTheory.Mem.DiagSp

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

theorem GlobalTheory.Mem.exists_spaces : ∀ (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T) (vn : ℕ → Bool), ∃ S : Spaces R F E, S.T = T ∧ (∀ j, j ≤ R.m → ∀ τ : E →+* ℂ, (S.Y j).sig τ = sigYD R j) ∧ S.Vneg = vn ∧ ∃ hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x), ∀ j, S.X j = Formalism.BasicNotions.Examples₂.posSpace hstar (R.N j) := by
  intro R F E _ _ _ _ _ _ cm T hT pz hpz vn
  exact ⟨DiagSp.spacesStd R cm T hT pz hpz vn, rfl, fun j _ τ => DiagSp.spY_sig R j τ, rfl,
    Formalism.BasicNotions.Examples₂.star_isIntegral, fun _ => rfl⟩

end
