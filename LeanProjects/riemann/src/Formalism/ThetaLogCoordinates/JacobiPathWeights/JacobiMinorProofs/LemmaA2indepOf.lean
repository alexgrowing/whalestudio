import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.IndexWeightsDominance
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ActFormContract
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.PathProductHighestWeight
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.IsWeightedHomogeneousZeroStripPathWord

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace A3ev

def Cols {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (N : ℕ) (F : Finset ℤ) : Prop :=
  ∀ c ∉ F,
    (∀ (R : Type) [CommRing R] (Xr : ℕ → Fin n → R), pathWord isVec μ c Xr N = oneF) ∧
    ∀ I : ℤ → Finset (Fin n), IsIndex (μ N) I → I c = ∅

theorem exists_cols {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) : ∃ F : Finset ℤ, Cols isVec μ N F := by
  have hfin : (⋃ i ∈ Set.Iio N, {c : ℤ | colHeight (μ (i + 1)) c ≠ colHeight (μ i) c}).Finite :=
    Set.Finite.biUnion (Set.finite_Iio N) fun i hi => Paths.path_finite hp hi
  refine ⟨hfin.toFinset, fun c hc => ?_⟩
  have hun : ∀ i < N, colHeight (μ (i + 1)) c = colHeight (μ i) c := by
    intro i hi
    by_contra hne
    exact hc (hfin.mem_toFinset.2 (Set.mem_biUnion (show i ∈ Set.Iio N from hi) hne))
  refine ⟨fun R _ Xr => (Paths.pathWord_unchanged isVec μ c Xr N hun).1, fun I hI => ?_⟩
  have b := (Paths.pathWord_unchanged isVec μ c (fun _ _ => (0 : ℤ)) N hun).2
  have hcard := hI c
  rw [b, hp.1, Paths.colHeight_zero] at hcard
  apply Finset.card_eq_zero.1
  rw [hcard]; split_ifs <;> simp

theorem psi_eq_prod (R : Type) [CommRing R] {n N : ℕ} {isVec : ℕ → Bool} {μ : ℕ → Fin n → ℤ}
    {F : Finset ℤ} (hF : Cols isVec μ N F) {I : ℤ → Finset (Fin n)} (hI : IsIndex (μ N) I) :
    psiPath R isVec μ N I =
      ∏ c ∈ F, pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c) := by
  unfold psiPath
  refine finprod_eq_prod_of_mulSupport_subset _ fun c hc => ?_
  by_contra hn
  apply hc
  show pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c) = 1
  rw [(hF c hn).1, (hF c hn).2 I hI]
  simp [oneF]

theorem minorF_empty {R : Type*} [CommRing R] {n : ℕ} (m : Matrix (Fin n) (Fin n) R) :
    minorF m ∅ ∅ = 1 := by
  rw [minorF_eq m (d := 0) rfl rfl]
  exact Matrix.det_isEmpty

theorem brk_eq_prod {L : Type} [CommRing L] {n N : ℕ} {isVec : ℕ → Bool} {μ : ℕ → Fin n → ℤ}
    {F : Finset ℤ} (hF : Cols isVec μ N F) (g gi : Matrix (Fin n) (Fin n) L)
    {I : ℤ → Finset (Fin n)} (hI : IsIndex (μ N) I) :
    brk g gi (μ N) I =
      ∏ c ∈ F, minorF (if 1 ≤ c then g else gi.transpose) (canIdx (μ N) c) (I c) := by
  unfold brk
  refine finprod_eq_prod_of_mulSupport_subset _ fun c hc => ?_
  by_contra hn
  apply hc
  show minorF (if 1 ≤ c then g else gi.transpose) (canIdx (μ N) c) (I c) = 1
  rw [(hF c hn).2 I hI, (hF c hn).2 _ (A1hw.isIndex_can _)]
  exact minorF_empty _

def invT {A : Type*} [CommRing A] {n : ℕ} (G : (Matrix (Fin n) (Fin n) A)ˣ) :
    (Matrix (Fin n) (Fin n) A)ˣ where
  val := (↑G⁻¹ : Matrix (Fin n) (Fin n) A).transpose
  inv := (↑G : Matrix (Fin n) (Fin n) A).transpose
  val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

theorem col_act {L : Type} [CommRing L] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (g : (Matrix (Fin n) (Fin n) L)ˣ) (N : ℕ) (J : Finset (Fin n)) :
    actAll isVec (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L)
        (pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) L)) N J) =
      ∑ I' : Finset (Fin n),
        pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) L)) N I' *
          C (minorF (if 1 ≤ c then (↑g : Matrix (Fin n) (Fin n) L)
            else (↑g⁻¹ : Matrix (Fin n) (Fin n) L).transpose) I' J) := by
  have h1 := A1hw.map_pathWord
    ((actAll isVec (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L) :
      MvPolynomial (ℕ × Fin n) L →ₐ[L] MvPolynomial (ℕ × Fin n) L) :
      MvPolynomial (ℕ × Fin n) L →+* MvPolynomial (ℕ × Fin n) L)
    isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) L)) N J
  rw [RingHom.coe_coe] at h1
  rw [h1]
  have hX : ∀ i, (fun a => actAll isVec (↑g : Matrix (Fin n) (Fin n) L)
      (↑g⁻¹ : Matrix (Fin n) (Fin n) L) (X (i, a) : MvPolynomial (ℕ × Fin n) L)) =
      if isVec i then Matrix.vecMul (fun b => (X (i, b) : MvPolynomial (ℕ × Fin n) L))
          ((↑g : Matrix (Fin n) (Fin n) L).map C)
        else Matrix.vecMul (fun b => (X (i, b) : MvPolynomial (ℕ × Fin n) L))
          ((↑g⁻¹ : Matrix (Fin n) (Fin n) L).map C).transpose := by
    intro i
    funext a
    unfold actAll
    rw [aeval_X]
    split_ifs <;> rfl
  let G : (Matrix (Fin n) (Fin n) (MvPolynomial (ℕ × Fin n) L))ˣ :=
    Units.map ((C : L →+* MvPolynomial (ℕ × Fin n) L).mapMatrix (m := Fin n)).toMonoidHom g
  have hG : (↑G : Matrix (Fin n) (Fin n) (MvPolynomial (ℕ × Fin n) L)) =
      (↑g : Matrix (Fin n) (Fin n) L).map C := rfl
  have hGi : (↑G⁻¹ : Matrix (Fin n) (Fin n) (MvPolynomial (ℕ × Fin n) L)) =
      (↑g⁻¹ : Matrix (Fin n) (Fin n) L).map C := rfl
  by_cases hc : 1 ≤ c
  · have := A1hw.act_pathWord actFormWedge actFormContract isVec μ c
      (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) L))
      (fun i a => actAll isVec (↑g : Matrix (Fin n) (Fin n) L)
        (↑g⁻¹ : Matrix (Fin n) (Fin n) L) (X (i, a) : MvPolynomial (ℕ × Fin n) L)) G
      (fun i hi => by
        have hv : isVec i = true := by simpa [hc] using hi
        rw [hX i, if_pos hv, hG])
      (fun i hi => by
        have hv : ¬ isVec i = true := by simpa [hc] using hi
        rw [hX i, if_neg hv, hGi]) N
    rw [this]
    unfold actF
    refine Finset.sum_congr rfl fun I' _ => ?_
    rw [if_pos hc, hG, minorMap]
  · have := A1hw.act_pathWord actFormWedge actFormContract isVec μ c
      (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) L))
      (fun i a => actAll isVec (↑g : Matrix (Fin n) (Fin n) L)
        (↑g⁻¹ : Matrix (Fin n) (Fin n) L) (X (i, a) : MvPolynomial (ℕ × Fin n) L)) (invT G)
      (fun i hi => by
        have hv : ¬ isVec i = true := by simpa [hc] using hi
        rw [hX i, if_neg hv]
        rfl)
      (fun i hi => by
        have hv : isVec i = true := by simpa [hc] using hi
        rw [hX i, if_pos hv]
        show _ = Matrix.vecMul _ ((↑G : Matrix (Fin n) (Fin n) (MvPolynomial (ℕ × Fin n) L)).transpose).transpose
        rw [Matrix.transpose_transpose, hG]) N
    rw [this]
    unfold actF
    refine Finset.sum_congr rfl fun I' _ => ?_
    rw [if_neg hc, minorMap]
    rfl

def extF {n : ℕ} (F : Finset ℤ) (p : ∀ c ∈ F, Finset (Fin n)) : ℤ → Finset (Fin n) :=
  fun c => if h : c ∈ F then p c h else ∅

def term {L : Type} [CommRing L] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (N : ℕ)
    (F : Finset ℤ) (g gi : Matrix (Fin n) (Fin n) L) (I I' : ℤ → Finset (Fin n)) :
    MvPolynomial (ℕ × Fin n) L :=
  (∏ c ∈ F, pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) L)) N (I' c)) *
    C (∏ c ∈ F, minorF (if 1 ≤ c then g else gi.transpose) (I' c) (I c))

theorem act_psi {L : Type} [CommRing L] {n N : ℕ} {isVec : ℕ → Bool} {μ : ℕ → Fin n → ℤ}
    {F : Finset ℤ} (hF : Cols isVec μ N F) (g : (Matrix (Fin n) (Fin n) L)ˣ)
    {I : ℤ → Finset (Fin n)} (hI : IsIndex (μ N) I) :
    actAll isVec (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L)
        (psiPath L isVec μ N I) =
      ∑ p ∈ F.pi (fun _ => (univ : Finset (Finset (Fin n)))),
        term isVec μ N F (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L) I
          (extF F p) := by
  rw [psi_eq_prod L hF hI, map_prod]
  simp_rw [col_act]
  rw [Finset.prod_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold term
  rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_attach F]
  refine Finset.prod_congr rfl fun x _ => ?_
  simp [extF, x.2]

theorem term_cases {L : Type} [CommRing L] {n N : ℕ} {isVec : ℕ → Bool} {μ : ℕ → Fin n → ℤ}
    {F : Finset ℤ} (hF : Cols isVec μ N F) (g gi : Matrix (Fin n) (Fin n) L)
    {I : ℤ → Finset (Fin n)} (hI : IsIndex (μ N) I) (I' : ℤ → Finset (Fin n))
    (h0 : ∀ c ∉ F, I' c = ∅) :
    IsIndex (μ N) I' ∨ term isVec μ N F g gi I I' = 0 := by
  by_cases h : ∀ c ∈ F, (I' c).card = (I c).card
  · left
    intro c
    by_cases hc : c ∈ F
    · rw [h c hc]; exact hI c
    · rw [h0 c hc, ← (hF c hc).2 I hI]; exact hI c
  · right
    push Not at h
    obtain ⟨c, hc, hne⟩ := h
    have : ∏ c ∈ F, minorF (if 1 ≤ c then g else gi.transpose) (I' c) (I c) = 0 :=
      Finset.prod_eq_zero hc (minorF_ne _ (Ne.symm hne))
    unfold term
    rw [this, map_zero, mul_zero]

theorem term_hom (hW : PsiWeight) {L : Type} [CommRing L] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ}
    {μ : ℕ → Fin n → ℤ} (hp : IsPath n isVec B μ N)
    {F : Finset ℤ} (hF : Cols isVec μ N F) (g gi : Matrix (Fin n) (Fin n) L)
    (I : ℤ → Finset (Fin n)) {I' : ℤ → Finset (Fin n)} (hI' : IsIndex (μ N) I') :
    IsWeightedHomogeneous (torusW isVec) (term isVec μ N F g gi I I') (idxWeight I') := by
  unfold term
  rw [← psi_eq_prod L hF hI', mul_comm]
  exact (hW L n N isVec B μ I' hp hI').C_mul _

theorem idxWeight_can {n : ℕ} {μ : Fin n → ℤ} (h : Antitone μ) : idxWeight (canIdx μ) = μ := by
  funext m
  unfold idxWeight
  have h1 : {c : ℤ | 1 ≤ c ∧ m ∈ canIdx μ c} = ↑(Finset.Icc 1 (μ m)) := by
    ext c
    rw [Finset.mem_coe, Finset.mem_Icc]
    constructor
    · rintro ⟨a, b⟩
      rw [A1hw.mem_can h, if_pos a] at b
      exact ⟨a, b⟩
    · rintro ⟨a, b⟩
      refine ⟨a, ?_⟩
      rw [A1hw.mem_can h, if_pos a]
      exact b
  have h2 : {c : ℤ | c ≤ 0 ∧ m ∈ canIdx μ c} = ↑(Finset.Ioc (μ m) 0) := by
    ext c
    rw [Finset.mem_coe, Finset.mem_Ioc]
    constructor
    · rintro ⟨a, b⟩
      rw [A1hw.mem_can h, if_neg (by omega)] at b
      exact ⟨b, a⟩
    · rintro ⟨a, b⟩
      refine ⟨b, ?_⟩
      rw [A1hw.mem_can h, if_neg (by omega)]
      exact a
  rw [h1, h2, Set.ncard_coe_finset, Set.ncard_coe_finset, Int.card_Icc, Int.card_Ioc]
  omega

end A3ev

open A3ev in
theorem factEV_of : IndexWeightsDominance → PsiWeight → FactEV := by
  intro hT hW L _ n N isVec B μ I g hp hI
  obtain ⟨F, hF⟩ := exists_cols hp
  have hanti : Antitone (μ N) := hp.2.1 N le_rfl
  have key : ∀ (ν : Fin n → ℤ) (p : ∀ c ∈ F, Finset (Fin n)),
      weightedHomogeneousComponent (torusW isVec) ν
        (term isVec μ N F (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L) I
          (extF F p)) ≠ 0 →
      IsIndex (μ N) (extF F p) ∧ idxWeight (extF F p) = ν := by
    intro ν p hne
    rcases term_cases hF (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L) hI
      (extF F p) (fun c hc => dif_neg hc) with h | h
    · refine ⟨h, ?_⟩
      by_contra hν
      exact hne ((term_hom hW hp hF _ _ I h).weightedHomogeneousComponent_ne ν (Ne.symm hν))
    · rw [h, map_zero] at hne
      exact absurd rfl hne
  rw [act_psi hF g hI]
  constructor
  · intro ν hne
    rw [map_sum] at hne
    obtain ⟨p, _, hp'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨h1, h2⟩ := key ν p hp'
    rw [← h2]
    exact (hT n (μ N) _ hanti h1).1
  · rw [map_sum, Finset.sum_eq_single (fun c _ => canIdx (μ N) c)]
    · have hcan : extF F (fun c _ => canIdx (μ N) c) = canIdx (μ N) := by
        funext c
        unfold extF
        split_ifs with h
        · rfl
        · exact ((hF c h).2 _ (A1hw.isIndex_can _)).symm
      rw [hcan]
      have hh := term_hom hW hp hF (↑g : Matrix (Fin n) (Fin n) L)
        (↑g⁻¹ : Matrix (Fin n) (Fin n) L) I (A1hw.isIndex_can (μ N))
      rw [idxWeight_can hanti] at hh
      rw [hh.weightedHomogeneousComponent_same]
      unfold term
      rw [← psi_eq_prod L hF (A1hw.isIndex_can _), ← brk_eq_prod hF _ _ hI, mul_comm]
    · intro p _ hpne
      by_contra hne
      obtain ⟨h1, h2⟩ := key _ p hne
      apply hpne
      have h3 := (hT n (μ N) _ hanti h1).2 h2
      funext c hc
      have h4 := congrFun h3 c
      unfold extF at h4
      rw [dif_pos hc] at h4
      exact h4
    · intro h
      exact absurd (Finset.mem_pi.2 fun _ _ => Finset.mem_univ _) h

namespace A3ev

def psum {n : ℕ} (ν : Fin n → ℤ) (j : ℕ) : ℤ := ∑ m ∈ univ.filter (fun m : Fin n => m.val < j), ν m

theorem psum_succ {n : ℕ} (ν : Fin n → ℤ) (m : Fin n) : psum ν (m.val + 1) = psum ν m.val + ν m := by
  unfold psum
  have : univ.filter (fun m' : Fin n => m'.val < m.val + 1) =
      insert m (univ.filter (fun m' : Fin n => m'.val < m.val)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp), add_comm]

theorem eq_of_psum {n : ℕ} {ν μ : Fin n → ℤ} (h : ∀ j ≤ n, psum ν j = psum μ j) : ν = μ := by
  funext m
  have h1 := psum_succ ν m
  have h2 := psum_succ μ m
  rw [h _ m.2, h _ m.2.le] at h1
  linarith

def height {n : ℕ} (ν : Fin n → ℤ) : ℤ := ∑ j ∈ range (n + 1), psum ν j

theorem domLe_eq {n : ℕ} {μ ν : Fin n → ℤ} (h : DomLe μ ν) (hh : height ν ≤ height μ) : ν = μ := by
  have hle : ∀ j, psum μ j ≤ psum ν j := h.2
  have heq : ∀ j ∈ range (n + 1), psum μ j = psum ν j :=
    (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).1
      (le_antisymm (Finset.sum_le_sum fun j _ => hle j) hh)
  exact eq_of_psum fun j hj => (heq j (Finset.mem_range.2 (by omega))).symm

theorem genMat_det_ne (k : Type*) [Field k] (n : ℕ) : (genMat k n).det ≠ 0 := by
  have : genMat k n = (algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).mapMatrix
      (Matrix.mvPolynomialX (Fin n) (Fin n) k) := by
    ext a b
    simp [genMat, Matrix.mvPolynomialX]
  rw [this, ← RingHom.map_det]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    (Matrix.det_mvPolynomialX_ne_zero (Fin n) k)

def genU (k : Type*) [Field k] (n : ℕ) : (Matrix (Fin n) (Fin n) (GenField k n))ˣ where
  val := genMat k n
  inv := (genMat k n)⁻¹
  val_inv := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (genMat_det_ne k n))
  inv_val := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (genMat_det_ne k n))

theorem ev_gen (hEV : FactEV) (k : Type) [Field k] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ}
    {μ : ℕ → Fin n → ℤ} {I : ℤ → Finset (Fin n)} (hp : IsPath n isVec B μ N)
    (hI : IsIndex (μ N) I) :
    (∀ ν : Fin n → ℤ,
      weightedHomogeneousComponent (torusW isVec) ν
        (actAll isVec (genMat k n) (genMat k n)⁻¹ (psiPath (GenField k n) isVec μ N I)) ≠ 0 →
      DomLe ν (μ N)) ∧
    weightedHomogeneousComponent (torusW isVec) (μ N)
        (actAll isVec (genMat k n) (genMat k n)⁻¹ (psiPath (GenField k n) isVec μ N I)) =
      C (brk (genMat k n) (genMat k n)⁻¹ (μ N) I) *
        psiPath (GenField k n) isVec μ N (canIdx (μ N)) :=
  hEV (GenField k n) n N isVec B μ I (genU k n) hp hI

theorem map_psi {k L : Type} [CommRing k] [CommRing L] (φ : k →+* L) {n N : ℕ} {isVec : ℕ → Bool}
    {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ} {I : ℤ → Finset (Fin n)} (hp : IsPath n isVec B μ N)
    (hI : IsIndex (μ N) I) :
    MvPolynomial.map φ (psiPath k isVec μ N I) = psiPath L isVec μ N I := by
  obtain ⟨F, hF⟩ := exists_cols hp
  rw [psi_eq_prod k hF hI, psi_eq_prod L hF hI, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [A1hw.map_pathWord]
  simp only [map_X]

def evC (k : Type) [Field k] (n : ℕ) (isVec : ℕ → Bool) (ν : Fin n → ℤ) :
    MvPolynomial (ℕ × Fin n) k →ₗ[k] MvPolynomial (ℕ × Fin n) (GenField k n) :=
  ((weightedHomogeneousComponent (R := GenField k n) (torusW isVec) ν).restrictScalars k) ∘ₗ
    ((actAll isVec (genMat k n) (genMat k n)⁻¹).toLinearMap.restrictScalars k) ∘ₗ
      (mapAlgHom (σ := ℕ × Fin n) (Algebra.ofId k (GenField k n))).toLinearMap

theorem evC_psi (k : Type) [Field k] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ}
    {μ : ℕ → Fin n → ℤ} {I : ℤ → Finset (Fin n)} (ν : Fin n → ℤ) (hp : IsPath n isVec B μ N)
    (hI : IsIndex (μ N) I) :
    evC k n isVec ν (psiPath k isVec μ N I) =
      weightedHomogeneousComponent (torusW isVec) ν
        (actAll isVec (genMat k n) (genMat k n)⁻¹ (psiPath (GenField k n) isVec μ N I)) := by
  rw [← map_psi (algebraMap k (GenField k n)) hp hI]
  rfl

def fam (k : Type) [Field k] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} (x : PathIdx n N isVec B) :
    MvPolynomial (ℕ × Fin n) (GenField k n) :=
  brk (genMat k n) (genMat k n)⁻¹ (x.1.1 N) x.1.2 •
    psiPath (GenField k n) isVec x.1.1 N (canIdx (x.1.1 N))

theorem fam_li (hBrk : FactBrk) (k : Type) [Field k] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ)
    (μ₀ : Fin n → ℤ) (hanti : Antitone μ₀) :
    LinearIndepOn k (fam k (n := n) (N := N) (isVec := isVec) (B := B)) {x | x.1.1 N = μ₀} := by
  have hprod := linearIndependent_smul (hBrk k n μ₀ hanti)
    (pathProductLinearIndependent (GenField k n) n N isVec B μ₀)
  let φ : {x : PathIdx n N isVec B // x.1.1 N = μ₀} →
      {I : ℤ → Finset (Fin n) // IsStd μ₀ I} ×
        {μ : ℕ → Fin n → ℤ // IsPath n isVec B μ N ∧ μ N = μ₀ ∧ ∀ i, N < i → μ i = 0} :=
    fun x => (⟨x.1.1.2, by have := x.1.2.2.2; rw [x.2] at this; exact this⟩,
      ⟨x.1.1.1, x.1.2.1, x.2, x.1.2.2.1⟩)
  have hφ : Function.Injective φ := by
    intro x y h
    have h1 := congrArg (fun p => p.1.1) h
    have h2 := congrArg (fun p => p.2.1) h
    exact Subtype.ext (Subtype.ext (Prod.ext h2 h1))
  have hc := hprod.comp φ hφ
  show LinearIndependent k (fun x : {x : PathIdx n N isVec B // x.1.1 N = μ₀} => fam k x.1)
  convert hc using 1
  funext x
  have hx : x.1.1.1 N = μ₀ := x.2
  show fam k x.1 = _
  unfold fam
  rw [hx]
  rfl

end A3ev

open A3ev in
theorem lemmaA2indep_of : FactEV → FactBrk → LemmaA2indep := by
  intro hEV hBrk k _ n N isVec B
  classical
  rw [linearIndependent_iff']
  intro s a hsum
  by_contra hcon
  push Not at hcon
  obtain ⟨x₁, hx₁s, hx₁⟩ := hcon
  have hT : (s.filter fun x => a x ≠ 0).Nonempty := ⟨x₁, Finset.mem_filter.2 ⟨hx₁s, hx₁⟩⟩
  obtain ⟨x₀, hx₀, hmax⟩ := Finset.exists_max_image _
    (fun x : PathIdx n N isVec B => height (x.1.1 N)) hT
  rw [Finset.mem_filter] at hx₀
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, x₀.1.1 N = μ₀ := ⟨_, rfl⟩
  have hanti : Antitone μ₀ := hμ₀ ▸ x₀.2.1.2.1 N le_rfl
  have h1 := congrArg (evC k n isVec μ₀) hsum
  rw [map_sum, map_zero] at h1
  simp_rw [map_smul] at h1
  have h2 : ∑ x ∈ s.filter (fun x => x.1.1 N = μ₀), a x • fam k x = 0 := by
    have h3 := Finset.sum_filter_of_ne (s := s)
      (p := fun x : PathIdx n N isVec B => x.1.1 N = μ₀)
      (f := fun x => a x • evC k n isVec μ₀ (psiPath k isVec x.1.1 N x.1.2)) ?_
    · rw [← h1, ← h3]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_filter] at hx
      rw [evC_psi k μ₀ x.2.1 x.2.2.2.1, ← hx.2, (ev_gen hEV k x.2.1 x.2.2.2.1).2]
      unfold fam
      rw [smul_eq_C_mul]
    · intro x hx hne
      have ha : a x ≠ 0 := fun h => hne (by rw [h, zero_smul])
      have he : evC k n isVec μ₀ (psiPath k isVec x.1.1 N x.1.2) ≠ 0 :=
        fun h => hne (by rw [h, smul_zero])
      rw [evC_psi k μ₀ x.2.1 x.2.2.2.1] at he
      have hd : DomLe μ₀ (x.1.1 N) := (ev_gen hEV k x.2.1 x.2.2.2.1).1 μ₀ he
      refine domLe_eq hd ?_
      rw [← hμ₀]
      exact hmax x (Finset.mem_filter.2 ⟨hx, ha⟩)
  exact hx₀.2 (linearIndepOn_iff'.1 (fam_li hBrk k n N isVec B μ₀ hanti) _ a
    (fun x hx => (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2) h2 x₀
    (Finset.mem_filter.2 ⟨hx₀.1, hμ₀⟩))

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
