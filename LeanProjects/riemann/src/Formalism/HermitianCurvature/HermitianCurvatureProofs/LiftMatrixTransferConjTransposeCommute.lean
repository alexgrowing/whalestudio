import Formalism.HermitianCurvature.StatementWd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EntryCommuteTransposedRMatrix
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarCommuteTransposedRMatrixEntry

namespace Formalism.FourierDecayAlt.P.Wd8

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

section Abstract

variable {R ι : Type} [Monoid R]

theorem exch_list (X : R) (f g : ι → R) (L : List ι)
    (h1 : ∀ σ ∈ L, X * f σ * g σ = g σ * f σ * X)
    (h2 : L.Pairwise fun σ τ => Commute (f τ) (g σ) ∧ Commute (f σ) (g τ)) :
    X * (L.map f).prod * (L.map g).prod = (L.map g).prod * (L.map f).prod * X := by
  induction L with
  | nil => simp
  | cons σ L ih =>
    have hp := List.pairwise_cons.mp h2
    have hF : Commute (L.map f).prod (g σ) :=
      Commute.list_prod_left _ _ (by
        intro t ht
        obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
        exact (hp.1 τ hτ).1)
    have hG : Commute (f σ) (L.map g).prod :=
      Commute.list_prod_right _ _ (by
        intro t ht
        obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
        exact (hp.1 τ hτ).2)
    have ih' := ih (fun τ hτ => h1 τ (List.mem_cons.mpr (Or.inr hτ))) hp.2
    have e1 := h1 σ (List.mem_cons.mpr (Or.inl rfl))
    have key : X * (f σ * (L.map f).prod) * (g σ * (L.map g).prod)
        = g σ * (L.map g).prod * (f σ * (L.map f).prod) * X := by
      calc X * (f σ * (L.map f).prod) * (g σ * (L.map g).prod)
          = X * f σ * ((L.map f).prod * g σ) * (L.map g).prod := by simp only [mul_assoc]
        _ = X * f σ * (g σ * (L.map f).prod) * (L.map g).prod := by rw [hF.eq]
        _ = X * f σ * g σ * ((L.map f).prod * (L.map g).prod) := by simp only [mul_assoc]
        _ = g σ * f σ * X * ((L.map f).prod * (L.map g).prod) := by rw [e1]
        _ = g σ * f σ * (X * (L.map f).prod * (L.map g).prod) := by simp only [mul_assoc]
        _ = g σ * f σ * ((L.map g).prod * (L.map f).prod * X) := by rw [ih']
        _ = g σ * (f σ * (L.map g).prod) * (L.map f).prod * X := by simp only [mul_assoc]
        _ = g σ * ((L.map g).prod * f σ) * (L.map f).prod * X := by rw [hG.eq]
        _ = g σ * (L.map g).prod * (f σ * (L.map f).prod) * X := by simp only [mul_assoc]
    simpa only [List.map_cons, List.prod_cons] using key

theorem exch_list_rev (X : R) (f g : ι → R) (L : List ι)
    (h1 : ∀ σ ∈ L, f σ * X * g σ = g σ * X * f σ)
    (h2 : L.Pairwise fun σ τ => Commute (f τ) (g σ) ∧ Commute (f σ) (g τ)) :
    (L.reverse.map f).prod * X * (L.map g).prod = (L.map g).prod * X * (L.reverse.map f).prod := by
  induction L with
  | nil => simp
  | cons σ L ih =>
    have hp := List.pairwise_cons.mp h2
    have hF : Commute (L.reverse.map f).prod (g σ) :=
      Commute.list_prod_left _ _ (by
        intro t ht
        obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
        exact (hp.1 τ (List.mem_reverse.mp hτ)).1)
    have hG : Commute (f σ) (L.map g).prod :=
      Commute.list_prod_right _ _ (by
        intro t ht
        obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
        exact (hp.1 τ hτ).2)
    have ih' := ih (fun τ hτ => h1 τ (List.mem_cons.mpr (Or.inr hτ))) hp.2
    have e1 := h1 σ (List.mem_cons.mpr (Or.inl rfl))
    have key : (L.reverse.map f).prod * f σ * X * (g σ * (L.map g).prod)
        = g σ * (L.map g).prod * X * ((L.reverse.map f).prod * f σ) := by
      calc (L.reverse.map f).prod * f σ * X * (g σ * (L.map g).prod)
          = (L.reverse.map f).prod * (f σ * X * g σ) * (L.map g).prod := by simp only [mul_assoc]
        _ = (L.reverse.map f).prod * (g σ * X * f σ) * (L.map g).prod := by rw [e1]
        _ = (L.reverse.map f).prod * g σ * X * f σ * (L.map g).prod := by simp only [mul_assoc]
        _ = g σ * (L.reverse.map f).prod * X * f σ * (L.map g).prod := by rw [hF.eq]
        _ = g σ * (L.reverse.map f).prod * X * (f σ * (L.map g).prod) := by simp only [mul_assoc]
        _ = g σ * (L.reverse.map f).prod * X * ((L.map g).prod * f σ) := by rw [hG.eq]
        _ = g σ * ((L.reverse.map f).prod * X * (L.map g).prod) * f σ := by simp only [mul_assoc]
        _ = g σ * ((L.map g).prod * X * (L.reverse.map f).prod) * f σ := by rw [ih']
        _ = g σ * (L.map g).prod * X * ((L.reverse.map f).prod * f σ) := by simp only [mul_assoc]
    simpa [List.reverse_cons, mul_assoc] using key

theorem prod_mul_list (x y : ι → R) (L : List ι)
    (h2 : L.Pairwise fun σ τ => Commute (y σ) (x τ)) :
    (L.map fun σ => x σ * y σ).prod = (L.map x).prod * (L.map y).prod := by
  induction L with
  | nil => simp
  | cons σ L ih =>
    have hp := List.pairwise_cons.mp h2
    have hC : Commute (y σ) (L.map x).prod :=
      Commute.list_prod_right _ _ (by
        intro t ht
        obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
        exact hp.1 τ hτ)
    have key : x σ * y σ * ((L.map x).prod * (L.map y).prod)
        = x σ * (L.map x).prod * (y σ * (L.map y).prod) := by
      calc x σ * y σ * ((L.map x).prod * (L.map y).prod)
          = x σ * (y σ * (L.map x).prod) * (L.map y).prod := by simp only [mul_assoc]
        _ = x σ * ((L.map x).prod * y σ) * (L.map y).prod := by rw [hC.eq]
        _ = x σ * (L.map x).prod * (y σ * (L.map y).prod) := by simp only [mul_assoc]
    simpa only [List.map_cons, List.prod_cons, ih hp.2, mul_assoc] using key

end Abstract

section Basic

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem io_mul_apply (x : A) (b : SlopeTestRemainingChoices S A) (z z' : Ix S) : ((io x : SlopeTestRemainingChoices S A) * b) z z' = x * b z z' := by
  simp [io, Matrix.scalar_apply, Matrix.diagonal_mul]

theorem mul_io_apply (x : A) (b : SlopeTestRemainingChoices S A) (z z' : Ix S) : (b * (io x : SlopeTestRemainingChoices S A)) z z' = b z z' * x := by
  simp [io, Matrix.scalar_apply, Matrix.mul_diagonal]

theorem io_add (x y : A) : (io (x + y) : SlopeTestRemainingChoices S A) = io x + io y := by simp [io]

theorem io_mul (x y : A) : (io (x * y) : SlopeTestRemainingChoices S A) = io x * io y := by simp [io]

theorem io_neg (x : A) : (io (-x) : SlopeTestRemainingChoices S A) = -io x := by simp [io]

theorem io_zero : (io (0 : A) : SlopeTestRemainingChoices S A) = 0 := by simp [io]

theorem io_one : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := by simp [io]

theorem lift_reduction_mul (M N : M2 A) : (lift0 (M * N) : M2 (SlopeTestRemainingChoices S A)) = lift0 M * lift0 N := by
  refine Matrix.ext fun i j => ?_
  simp only [lift0, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, io_add, io_mul]

theorem liftMatrix_one : (lift0 (1 : M2 A) : M2 (SlopeTestRemainingChoices S A)) = 1 := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j <;> simp [lift0, Matrix.one_apply, h, io_one, io_zero]

theorem liftMatrix_list_prod (L : List (M2 A)) :
    (lift0 L.prod : M2 (SlopeTestRemainingChoices S A)) = (L.map lift0).prod := by
  induction L with
  | nil => simp [liftMatrix_one]
  | cons M L ih => simp [lift_reduction_mul, ih]

theorem diagScalar_mul (a b : SlopeTestRemainingChoices S A) : d0 (a * b) = d0 a * d0 b := by
  simp [d0]

theorem d0_one : d0 (1 : SlopeTestRemainingChoices S A) = 1 := by
  simp [d0]

theorem diagScalar_list_prod (L : List (SlopeTestRemainingChoices S A)) : d0 L.prod = (L.map d0).prod := by
  induction L with
  | nil => simp [d0_one]
  | cons M L ih => simp [diagScalar_mul, ih]

theorem mul_diagScalar_apply (M : M2 (SlopeTestRemainingChoices S A)) (b : SlopeTestRemainingChoices S A) (i j : Fin 2) : (M * d0 b) i j = M i j * b := by
  simp [d0, Matrix.mul_diagonal]

theorem diagScalar_mul_apply (M : M2 (SlopeTestRemainingChoices S A)) (b : SlopeTestRemainingChoices S A) (i j : Fin 2) : (d0 b * M) i j = b * M i j := by
  simp [d0, Matrix.diagonal_mul]

theorem liftMatrix_commute_diagScalar (M : M2 A) (b : SlopeTestRemainingChoices S A) (h : ∀ i j, Commute (io (M i j)) b) :
    Commute (lift0 M) (d0 b) := by
  show lift0 M * d0 b = d0 b * lift0 M
  refine Matrix.ext fun i j => ?_
  rw [mul_diagScalar_apply, diagScalar_mul_apply]
  exact (h i j).eq

theorem io_comm_eU (x : A) (a : S) (i j : Fin 2) : Commute (io x) (eU a i j : SlopeTestRemainingChoices S A) := by
  show (io x : SlopeTestRemainingChoices S A) * eU a i j = eU a i j * io x
  refine Matrix.ext fun z z' => ?_
  rw [io_mul_apply, mul_io_apply]
  simp only [eU, Matrix.of_apply]
  split_ifs <;> simp

theorem io_comm_io {x y : A} (h : Commute x y) : Commute (io x : SlopeTestRemainingChoices S A) (io y) := by
  exact h.map (Matrix.scalar (Ix S))

theorem io_algebraMap_comm (k : K) (b : SlopeTestRemainingChoices S A) : Commute (io (algebraMap K A k)) b := by
  show (io (algebraMap K A k) : SlopeTestRemainingChoices S A) * b = b * io (algebraMap K A k)
  refine Matrix.ext fun z z' => ?_
  rw [io_mul_apply, mul_io_apply]
  exact Algebra.commutes k (b z z')

theorem io_comm_ins (x : A) (a : S) (M : M2 A) (h : ∀ i j, Commute x (M i j)) :
    Commute (io x) (ins a (lift0 M) : SlopeTestRemainingChoices S A) := by
  unfold ins
  refine Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
  exact (io_comm_eU x a i j).mul_right (io_comm_io (h i j))

def CC (τ : Site A) (b : SlopeTestRemainingChoices S A) : Prop := ∀ x ∈ ops τ, Commute (io x) b

theorem mem_ops_p (τ : Site A) : τ.p ∈ ops τ := by simp [ops, hol]
theorem mem_ops_c (τ : Site A) : τ.c ∈ ops τ := by simp [ops, hol]
theorem mem_ops_ci (τ : Site A) : τ.ci ∈ ops τ := by simp [ops, hol]
theorem mem_ops_sp (τ : Site A) : star τ.p ∈ ops τ := by simp [ops, hol]
theorem mem_ops_sc (τ : Site A) : star τ.c ∈ ops τ := by simp [ops, hol]
theorem mem_ops_sci (τ : Site A) : star τ.ci ∈ ops τ := by simp [ops, hol]

theorem comm_Ts {R : Type} [Ring R] (φ : A →+* R) (hφ : ∀ (k : K) (r : R), Commute (φ (algebraMap K A k)) r)
    (τ : Site A) (b : R) (h : ∀ x ∈ ops τ, Commute (φ x) b) (Y : K) (i j : Fin 2) :
    Commute (φ (Ts τ Y i j)) b := by
  have hp := h _ (mem_ops_p τ)
  have hc := h _ (mem_ops_c τ)
  have hci := h _ (mem_ops_ci τ)
  have hY := hφ Y b
  fin_cases i <;> fin_cases j <;> simp [Ts, Tm, hc, hci] <;> exact hY.add_left hp

theorem comm_Ts_star {R : Type} [Ring R] (φ : A →+* R)
    (hφ : ∀ (k : K) (r : R), Commute (φ (algebraMap K A k)) r)
    (τ : Site A) (b : R) (h : ∀ x ∈ ops τ, Commute (φ x) b) (Y : K) (i j : Fin 2) :
    Commute (φ (star (Ts τ Y i j))) b := by
  have hp := h _ (mem_ops_sp τ)
  have hc := h _ (mem_ops_sc τ)
  have hci := h _ (mem_ops_sci τ)
  have hY : Commute (φ (star (algebraMap K A Y))) b := by
    rw [← algebraMap_star_comm]
    exact hφ _ b
  fin_cases i <;> fin_cases j <;> simp [Ts, Tm, hc, hci] <;>
    first | exact hY.add_left hp | exact (hφ (star Y) b).add_left hp

end Basic

section Sites

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem io_comm_vlet (σ : Site A) (x : A) (h : ∀ y ∈ ops σ, Commute y x) (l : Letter K S) :
    Commute (io x) (vlet σ l : SlopeTestRemainingChoices S A) := by
  unfold vlet
  apply io_comm_ins
  intro i j
  have hφ : ∀ (k : K) (r : A), Commute ((RingHom.id A) (algebraMap K A k)) r :=
    fun k r => Algebra.commutes k r
  by_cases hl : l.plus = true
  · rw [if_pos hl]
    exact (comm_Ts (RingHom.id A) hφ σ x h l.pt i j).symm
  · rw [if_neg hl]
    exact (comm_Ts_star (RingHom.id A) hφ σ x h l.pt i j).symm

theorem io_comm_bT (σ : Site A) (x : A) (h : ∀ y ∈ ops σ, Commute y x) (w : List (Letter K S)) :
    Commute (io x) (bT σ w : SlopeTestRemainingChoices S A) := by
  induction w with
  | nil =>
    simp only [bT]
    exact Commute.one_right _
  | cons l w ih =>
    simp only [bT]
    exact (io_comm_vlet σ x h l).mul_right ih

theorem cc_vlet {σ τ : Site A} (h : SitesCommute σ τ) (l : Letter K S) :
    CC τ (vlet σ l : SlopeTestRemainingChoices S A) := fun x hx => io_comm_vlet σ x (fun y hy => h y hy x hx) l

theorem cc_bT {σ τ : Site A} (h : SitesCommute σ τ) (w : List (Letter K S)) :
    CC τ (bT σ w : SlopeTestRemainingChoices S A) := fun x hx => io_comm_bT σ x (fun y hy => h y hy x hx) w

theorem sitesCommute_symm {σ τ : Site A} (h : SitesCommute σ τ) : SitesCommute τ σ := fun x hx y hy => (h y hy x hx).symm

theorem liftMatrix_transfer_commute_diagScalar {τ : Site A} {b : SlopeTestRemainingChoices S A} (h : CC τ b) (Y : K) :
    Commute (lift0 (Ts τ Y)) (d0 b) := by
  have hφ : ∀ (k : K) (r : SlopeTestRemainingChoices S A),
      Commute ((Matrix.scalar (Ix S) : A →+* SlopeTestRemainingChoices S A) (algebraMap K A k)) r :=
    fun k r => io_algebraMap_comm k r
  have h' : ∀ x ∈ ops τ, Commute ((Matrix.scalar (Ix S) : A →+* SlopeTestRemainingChoices S A) x) b := h
  exact liftMatrix_commute_diagScalar _ _ fun i j => comm_Ts _ hφ τ b h' Y i j

theorem liftMatrix_transfer_conjTranspose_commute {τ : Site A} {b : SlopeTestRemainingChoices S A} (h : CC τ b) (Y : K) :
    Commute (lift0 (Ts τ Y)ᴴ) (d0 b) := by
  have hφ : ∀ (k : K) (r : SlopeTestRemainingChoices S A),
      Commute ((Matrix.scalar (Ix S) : A →+* SlopeTestRemainingChoices S A) (algebraMap K A k)) r :=
    fun k r => io_algebraMap_comm k r
  have h' : ∀ x ∈ ops τ, Commute ((Matrix.scalar (Ix S) : A →+* SlopeTestRemainingChoices S A) x) b := h
  exact liftMatrix_commute_diagScalar _ _ fun i j => comm_Ts_star _ hφ τ b h' Y j i

theorem exchA_mat (sites : List (Site A)) (w : List (Letter K S)) (Y : K)
    (h1 : ∀ σ ∈ sites, Xp w Y * lift0 (Ts σ Y) * d0 (bT σ w) = d0 (bT σ w) * lift0 (Ts σ Y) * Xp w Y)
    (h2 : sites.Pairwise SitesCommute) :
    Xp w Y * lift0 (sites.map fun σ => Ts σ Y).prod * d0 (sites.map fun σ => bT σ w).prod =
      d0 (sites.map fun σ => bT σ w).prod * lift0 (sites.map fun σ => Ts σ Y).prod * Xp w Y := by
  have e := exch_list (Xp w Y) (fun σ => lift0 (Ts σ Y)) (fun σ => d0 (bT σ w)) sites h1
    (h2.imp fun {σ τ} hst =>
      ⟨liftMatrix_transfer_commute_diagScalar (cc_bT hst w) Y, liftMatrix_transfer_commute_diagScalar (cc_bT (sitesCommute_symm hst) w) Y⟩)
  rw [liftMatrix_list_prod, diagScalar_list_prod, List.map_map, List.map_map]
  exact e

private theorem lift0_conjT_prod_lemma (L : List (Site A)) (Y : K) :
    (lift0 ((L.map fun σ => Ts σ Y).prod)ᴴ : M2 (SlopeTestRemainingChoices S A)) =
      (L.reverse.map fun σ => lift0 (Ts σ Y)ᴴ).prod := by
  induction L with
  | nil => simp [liftMatrix_one]
  | cons σ L ih =>
    rw [List.map_cons, List.prod_cons, Matrix.conjTranspose_mul, lift_reduction_mul, ih,
      List.reverse_cons, List.map_append, List.prod_append]
    simp

theorem exchB_mat (sites : List (Site A)) (w : List (Letter K S)) (Y : K)
    (h1 : ∀ σ ∈ sites,
      lift0 (Ts σ Y)ᴴ * Xm w Y * d0 (bT σ w) = d0 (bT σ w) * Xm w Y * lift0 (Ts σ Y)ᴴ)
    (h2 : sites.Pairwise SitesCommute) :
    lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * Xm w Y * d0 (sites.map fun σ => bT σ w).prod =
      d0 (sites.map fun σ => bT σ w).prod * Xm w Y * lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ := by
  have e := exch_list_rev (Xm w Y) (fun σ => (lift0 (Ts σ Y)ᴴ : M2 (SlopeTestRemainingChoices S A)))
    (fun σ => d0 (bT σ w)) sites h1 (h2.imp fun {σ τ} hst =>
      ⟨liftMatrix_transfer_conjTranspose_commute (cc_bT hst w) Y, liftMatrix_transfer_conjTranspose_commute (cc_bT (sitesCommute_symm hst) w) Y⟩)
  rw [lift0_conjT_prod_lemma, diagScalar_list_prod, List.map_map]
  exact e

theorem mul_col_fix (B C : SlopeTestRemainingChoices S A) (z : Ix S) (h : ∀ z', C z' e1 = if z' = e1 then 1 else 0) :
    (B * C) z e1 = B z e1 := by
  rw [Matrix.mul_apply]
  simp [h]

theorem mul_col_zero (B C : SlopeTestRemainingChoices S A) (z : Ix S) (h : ∀ z', C z' e1 = 0) : (B * C) z e1 = 0 := by
  rw [Matrix.mul_apply]
  simp [h]

theorem sum_col_fix (B C : Fin 2 → SlopeTestRemainingChoices S A) (z : Ix S)
    (h : ∀ (k : Fin 2) (z' : Ix S), C k z' e1 = if k = 0 ∧ z' = e1 then 1 else 0) :
    (∑ k, B k * C k) z e1 = B 0 z e1 := by
  rw [Matrix.sum_apply, Fin.sum_univ_two,
    mul_col_fix (B 0) (C 0) z (fun z' => by simp [h]),
    mul_col_zero (B 1) (C 1) z (fun z' => by simp [h]), add_zero]

theorem exchVecA_of (hE1 : ExchangePlusFactor) (hfix : XpFix) : ExchVecA := by
  intro K A S _ _ _ _ _ _ _ _ QQ sites w Y hOK hw hreg k z
  have hM := exchA_mat sites w Y (fun σ hσ => hE1 K A S σ w Y (hOK.1 σ hσ).1 hw) hOK.2
  have hfx := hfix K A S w Y hw.1 hreg
  have hL : (Xp w Y * lift0 (sites.map fun σ => Ts σ Y).prod * d0 (sites.map fun σ => bT σ w).prod :
      M2 (SlopeTestRemainingChoices S A)) k 0 z e1 =
      ∑ l, ∑ z', (Xp w Y k l : SlopeTestRemainingChoices S A) z z' * (v0 sites Y l * uw sites w z') := by
    rw [mul_diagScalar_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.sum_apply, lift0, Matrix.map_apply, mul_io_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc, v0, uw]
  have hR : (d0 (sites.map fun σ => bT σ w).prod * lift0 (sites.map fun σ => Ts σ Y).prod * Xp w Y :
      M2 (SlopeTestRemainingChoices S A)) k 0 z e1 = uw sites w z * v0 sites Y k := by
    rw [Matrix.mul_apply]
    simp only [diagScalar_mul_apply, lift0, Matrix.map_apply]
    rw [sum_col_fix (fun j => (sites.map fun σ => bT σ w).prod * io ((sites.map fun σ => Ts σ Y).prod k j))
      (fun j => Xp w Y j 0) z hfx]
    simp only [mul_io_apply, v0, uw]
  exact hL.symm.trans ((congrArg (fun M : M2 (SlopeTestRemainingChoices S A) => M k 0 z e1) hM).trans hR)

theorem sum_row_fix (U : SlopeTestRemainingChoices S A) (C : Fin 2 → SlopeTestRemainingChoices S A) (x : Fin 2 → A) (z : Ix S)
    (h : ∀ (k : Fin 2) (z' : Ix S), C k z' e1 = if k = 0 ∧ z' = e1 then 1 else 0) :
    (∑ k, U * C k * io (x k) : SlopeTestRemainingChoices S A) z e1 = U z e1 * x 0 := by
  rw [Matrix.sum_apply, Fin.sum_univ_two, mul_io_apply, mul_io_apply,
    mul_col_fix U (C 0) z (fun z' => by simp [h]), mul_col_zero U (C 1) z (fun z' => by simp [h])]
  simp

theorem exchVecB_of (hE2 : ExchangeMinusFactorStar) (hfix : XmFix) : ExchVecB := by
  intro K A S _ _ _ _ _ _ _ _ QQ sites w Y hOK hw hreg hY l z
  have hM := exchB_mat sites w Y (fun σ hσ => hE2 K A S σ w Y (hOK.1 σ hσ).1 hw hY) hOK.2
  have hfx := hfix K A S w Y hw.1 hreg
  have hL : (lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * Xm w Y * d0 (sites.map fun σ => bT σ w).prod :
      M2 (SlopeTestRemainingChoices S A)) 0 l z e1 =
      ∑ k, ∑ z', star (v0 sites Y k) * (Xm w Y k l : SlopeTestRemainingChoices S A) z z' * uw sites w z' := by
    rw [mul_diagScalar_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.sum_apply, lift0, Matrix.map_apply, Matrix.conjTranspose_apply, io_mul_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [v0, uw]
  have hR : (d0 (sites.map fun σ => bT σ w).prod * Xm w Y * lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ :
      M2 (SlopeTestRemainingChoices S A)) 0 l z e1 = uw sites w z * star (v0 sites Y l) := by
    rw [Matrix.mul_apply]
    simp only [diagScalar_mul_apply, lift0, Matrix.map_apply, Matrix.conjTranspose_apply]
    rw [sum_row_fix _ (fun j => Xm w Y 0 j) (fun j => star ((sites.map fun σ => Ts σ Y).prod l j)) z hfx]
    simp only [v0, uw]
  exact hL.symm.trans ((congrArg (fun M : M2 (SlopeTestRemainingChoices S A) => M 0 l z e1) hM).trans hR)

theorem QQ_comm (QQ : K → M2 A) (sites : List (Site A)) (w : List (Letter K S)) (Y : K)
    (h : ∀ σ ∈ sites, QQCommutes QQ σ) :
    Commute (lift0 (QQ Y)) (d0 (sites.map fun σ => bT σ w).prod) := by
  refine liftMatrix_commute_diagScalar _ _ fun i j => Commute.list_prod_right _ _ fun b hb => ?_
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hb
  exact io_comm_bT σ _ (fun y hy => (h σ hσ Y i j y hy).symm) w

theorem cw_mat (X X' Q V VH U : M2 (SlopeTestRemainingChoices S A)) (hA : X' * V * U = U * V * X')
    (hB : VH * X * U = U * X * VH) (hQ : Commute Q U) :
    VH * (X * Q * X') * V * U = U * X * (VH * Q * V) * X' := by
  calc VH * (X * Q * X') * V * U = VH * X * Q * (X' * V * U) := by simp only [mul_assoc]
    _ = VH * X * Q * (U * V * X') := by rw [hA]
    _ = VH * X * (Q * U) * V * X' := by simp only [mul_assoc]
    _ = VH * X * (U * Q) * V * X' := by rw [hQ.eq]
    _ = VH * X * U * Q * V * X' := by simp only [mul_assoc]
    _ = U * X * VH * Q * V * X' := by rw [hB]
    _ = U * X * (VH * Q * V) * X' := by simp only [mul_assoc]

theorem cwEigen_of (hE1 : ExchangePlusFactor) (hE2 : ExchangeMinusFactorStar) (hfixp : XpFix) (hfixm : XmFix) (hT : TTFactor) :
    CwEigen := by
  intro K A S _ _ _ _ _ _ _ _ QQ sites w Y hOK hw hreg hY z
  have hA := exchA_mat sites w Y (fun σ hσ => hE1 K A S σ w Y (hOK.1 σ hσ).1 hw) hOK.2
  have hB := exchB_mat sites w Y (fun σ hσ => hE2 K A S σ w Y (hOK.1 σ hσ).1 hw hY) hOK.2
  have hQ := QQ_comm QQ sites w Y (fun σ hσ => (hOK.1 σ hσ).2)
  have hM := cw_mat _ _ _ _ _ _ hA hB hQ
  rw [← hT K A S QQ w Y] at hM
  have hfp := hfixp K A S w Y hw.1 hreg
  have hfm := hfixm K A S w Y hw.1 hreg
  have hCw : (lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * TTw QQ w Y * lift0 (sites.map fun σ => Ts σ Y).prod : M2 (SlopeTestRemainingChoices S A)) 0 0 = Cw QQ sites w Y := by
    simp only [Matrix.mul_apply, Finset.sum_mul, lift0, Matrix.map_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_comm]
    rfl
  have hL : (lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * TTw QQ w Y * lift0 (sites.map fun σ => Ts σ Y).prod * d0 (sites.map fun σ => bT σ w).prod : M2 (SlopeTestRemainingChoices S A)) 0 0 z e1 =
      ∑ z', Cw QQ sites w Y z z' * uw sites w z' := by
    rw [mul_diagScalar_apply, hCw, Matrix.mul_apply]
    rfl
  have hR : ∀ n, ((lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * lift0 (QQ Y) * lift0 (sites.map fun σ => Ts σ Y).prod) : M2 (SlopeTestRemainingChoices S A)) n 0 = io (∑ k, ∑ l, star ((sites.map fun σ => Ts σ Y).prod k n) * QQ Y k l * (sites.map fun σ => Ts σ Y).prod l 0) := by
    intro n
    simp only [Matrix.mul_apply, Fin.sum_univ_two, lift0, Matrix.map_apply, Matrix.conjTranspose_apply,
      io_add, io_mul, add_mul]
    abel
  have hRow : (d0 (sites.map fun σ => bT σ w).prod * Xm w Y * (lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * lift0 (QQ Y) * lift0 (sites.map fun σ => Ts σ Y).prod) : M2 (SlopeTestRemainingChoices S A)) 0 0 =
      ∑ n, (sites.map fun σ => bT σ w).prod * Xm w Y 0 n * io (∑ k, ∑ l, star ((sites.map fun σ => Ts σ Y).prod k n) * QQ Y k l * (sites.map fun σ => Ts σ Y).prod l 0) := by
    rw [Matrix.mul_apply]
    simp only [diagScalar_mul_apply, hR]
  have hRhs : (d0 (sites.map fun σ => bT σ w).prod * Xm w Y * (lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * lift0 (QQ Y) * lift0 (sites.map fun σ => Ts σ Y).prod) * Xp w Y : M2 (SlopeTestRemainingChoices S A)) 0 0 z e1 =
      uw sites w z * C0 QQ sites Y := by
    rw [Matrix.mul_apply]
    refine (sum_col_fix (fun m => (d0 (sites.map fun σ => bT σ w).prod * Xm w Y * (lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * lift0 (QQ Y) * lift0 (sites.map fun σ => Ts σ Y).prod) : M2 (SlopeTestRemainingChoices S A)) 0 m)
      (fun m => Xp w Y m 0) z hfp).trans ?_
    show (d0 (sites.map fun σ => bT σ w).prod * Xm w Y * (lift0 ((sites.map fun σ => Ts σ Y).prod)ᴴ * lift0 (QQ Y) * lift0 (sites.map fun σ => Ts σ Y).prod) : M2 (SlopeTestRemainingChoices S A)) 0 0 z e1 = _
    rw [hRow]
    exact sum_row_fix (sites.map fun σ => bT σ w).prod (fun n => Xm w Y 0 n) (fun n => ∑ k, ∑ l, star ((sites.map fun σ => Ts σ Y).prod k n) * QQ Y k l * (sites.map fun σ => Ts σ Y).prod l 0) z hfm
  exact hL.symm.trans ((congrArg (fun M : M2 (SlopeTestRemainingChoices S A) => M 0 0 z e1) hM).trans hRhs)

end Sites

section Product

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem eU_apply (a : S) (i j : Fin 2) (x y : Ix S) :
    (eU a i j : SlopeTestRemainingChoices S A) x y = if x a = i ∧ y = Function.update x a j then 1 else 0 := by
  simp only [eU, Matrix.of_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, funext fun b => ?_⟩
    by_cases hb : b = a
    · rw [hb]
      simp [h2]
    · simp [Function.update_apply, hb, h3 b hb]
  · rintro ⟨h1, rfl⟩
    exact ⟨h1, by simp, fun b hb => by simp [Function.update_apply, hb]⟩

theorem eU_mul_apply (a : S) (i j : Fin 2) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    ((eU a i j : SlopeTestRemainingChoices S A) * B) x y = if x a = i then B (Function.update x a j) y else 0 := by
  rw [Matrix.mul_apply]
  simp only [eU_apply]
  by_cases h : x a = i <;> simp [h]

theorem eU_comm_of_ne {a c : S} (hc : c ≠ a) (i j k l : Fin 2) :
    Commute (eU c i j : SlopeTestRemainingChoices S A) (eU a k l) := by
  show (eU c i j : SlopeTestRemainingChoices S A) * eU a k l = eU a k l * eU c i j
  refine Matrix.ext fun x y => ?_
  rw [eU_mul_apply, eU_mul_apply, eU_apply, eU_apply, Function.update_comm hc]
  by_cases h1 : x c = i <;> by_cases h2 : x a = k <;>
    simp [Function.update_apply, hc, Ne.symm hc, h1, h2]

theorem ins_lift0_mul_apply (a : S) (M : M2 A) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    ((ins a (lift0 M) : SlopeTestRemainingChoices S A) * B) x y = ∑ j, M (x a) j * B (Function.update x a j) y := by
  unfold ins
  simp only [Finset.sum_mul, Matrix.sum_apply, mul_assoc, eU_mul_apply, lift0, Matrix.map_apply,
    io_mul_apply]
  rw [Finset.sum_comm]
  simp

theorem free_vlet (σ : Site A) (l : Letter K S) {a : S} (ha : a ≠ l.intersection_update_fsHerm_neg_one) (i j : Fin 2) :
    Commute (eU a i j : SlopeTestRemainingChoices S A) (vlet σ l) := by
  unfold vlet ins
  refine Commute.sum_right _ _ _ fun k _ => Commute.sum_right _ _ _ fun m _ => ?_
  exact (eU_comm_of_ne ha i j k m).mul_right
    (io_comm_eU ((if l.plus then Ts σ l.pt else (Ts σ l.pt).map star) k m) a i j).symm

theorem free_bT (σ : Site A) (w : List (Letter K S)) {a : S} (ha : a ∉ w.map Letter.intersection_update_fsHerm_neg_one)
    (i j : Fin 2) : Commute (eU a i j : SlopeTestRemainingChoices S A) (bT σ w) := by
  induction w with
  | nil =>
    simp only [bT]
    exact Commute.one_right _
  | cons l w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at ha
    simp only [bT]
    exact (free_vlet σ l ha.1 i j).mul_right (ih ha.2)

def lm (l : Letter K S) (σ : Site A) : M2 A := if l.plus then Ts σ l.pt else (Ts σ l.pt).map star

private theorem ent_comm_lemma (σ : Site A) (l : Letter K S) (x : A)
    (h : ∀ y ∈ ops σ, Commute y x) (i j : Fin 2) :
    Commute ((if l.plus then Ts σ l.pt else (Ts σ l.pt).map star) i j) x := by
  have hφ : ∀ (k : K) (r : A), Commute ((RingHom.id A) (algebraMap K A k)) r :=
    fun k r => Algebra.commutes k r
  by_cases hl : l.plus = true
  · rw [if_pos hl]
    exact comm_Ts (RingHom.id A) hφ σ x h l.pt i j
  · rw [if_neg hl]
    exact comm_Ts_star (RingHom.id A) hφ σ x h l.pt i j

private theorem vlet_comm_lemma {σ τ : Site A} (h : SitesCommute σ τ) (l' l : Letter K S)
    (hne : l'.intersection_update_fsHerm_neg_one ≠ l.intersection_update_fsHerm_neg_one) : Commute (vlet σ l' : SlopeTestRemainingChoices S A) (vlet τ l) := by
  unfold vlet ins
  refine Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ =>
    Commute.sum_right _ _ _ fun p _ => Commute.sum_right _ _ _ fun q _ => ?_
  have hN : ∀ x ∈ ops σ, Commute x ((if l.plus then Ts τ l.pt else (Ts τ l.pt).map star) p q) :=
    fun x hx => (ent_comm_lemma τ l x (fun y hy => (h x hx y hy).symm) p q).symm
  have hMN := ent_comm_lemma σ l' _ hN i j
  exact ((eU_comm_of_ne hne i j p q).mul_right
      (io_comm_eU ((if l.plus then Ts τ l.pt else (Ts τ l.pt).map star) p q) l'.intersection_update_fsHerm_neg_one i j).symm).mul_left
    ((io_comm_eU ((if l'.plus then Ts σ l'.pt else (Ts σ l'.pt).map star) i j) l.intersection_update_fsHerm_neg_one p q).mul_right
      (io_comm_io hMN))

theorem bT_comm_vlet {σ τ : Site A} (h : SitesCommute σ τ) (w : List (Letter K S)) (l : Letter K S)
    (ha : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one) : Commute (bT σ w : SlopeTestRemainingChoices S A) (vlet τ l) := by
  induction w with
  | nil =>
    simp only [bT]
    exact Commute.one_left _
  | cons l' w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at ha
    simp only [bT]
    exact (vlet_comm_lemma h l' l (Ne.symm ha.1)).mul_left (ih ha.2)

theorem vlet_prod_mul_apply (sites : List (Site A)) (l : Letter K S) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    ((sites.map fun σ => (vlet σ l : SlopeTestRemainingChoices S A)).prod * B) x y =
      ∑ j, (sites.map (lm l)).prod (x l.intersection_update_fsHerm_neg_one) j * B (Function.update x l.intersection_update_fsHerm_neg_one j) y := by
  induction sites generalizing x with
  | nil => simp [Matrix.one_apply]
  | cons σ sites ih =>
    have hu : ∀ j : Fin 2, Function.update x l.intersection_update_fsHerm_neg_one j l.intersection_update_fsHerm_neg_one = j := fun j => by simp
    have hu2 : ∀ j j' : Fin 2, Function.update (Function.update x l.intersection_update_fsHerm_neg_one j) l.intersection_update_fsHerm_neg_one j' =
        Function.update x l.intersection_update_fsHerm_neg_one j' := fun j j' => by simp
    have hv : (vlet σ l : SlopeTestRemainingChoices S A) = ins l.intersection_update_fsHerm_neg_one (lift0 (lm l σ)) := rfl
    simp only [List.map_cons, List.prod_cons, mul_assoc]
    rw [hv, ins_lift0_mul_apply]
    simp only [ih, hu, hu2, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]

private theorem prod_one_lemma (L : List (Site A)) :
    (L.map fun σ => (bT σ ([] : List (Letter K S)) : SlopeTestRemainingChoices S A)).prod = 1 := by
  induction L with
  | nil => simp
  | cons σ L ih =>
    rw [List.map_cons, List.prod_cons, ih, mul_one] <;> simp only [bT]

theorem word_product_formula_general (sites : List (Site A)) (w : List (Letter K S))
    (hs : sites.Pairwise SitesCommute) (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (z : Ix S) :
    uw sites w z =
      if ∀ c, c ∉ w.map Letter.intersection_update_fsHerm_neg_one → z c = 0 then
        (w.map fun l => (sites.map (lm l)).prod (z l.intersection_update_fsHerm_neg_one) 0).prod
      else 0 := by
  induction w generalizing z with
  | nil =>
    unfold uw
    rw [prod_one_lemma]
    by_cases hz : ∀ c, z c = 0
    · have hz' : z = e1 := funext hz
      subst hz'
      simp [e1]
    · have hz' : z ≠ e1 := fun h => hz fun c => by simp [h, e1]
      simp [Matrix.one_apply, hz', hz]
  | cons l w' ih =>
    have hnd : l.intersection_update_fsHerm_neg_one ∉ w'.map Letter.intersection_update_fsHerm_neg_one ∧ (w'.map Letter.intersection_update_fsHerm_neg_one).Nodup := by
      simpa using hw
    have ih' : ∀ z', uw sites w' z' = if ∀ c, c ∉ w'.map Letter.intersection_update_fsHerm_neg_one → z' c = 0 then
        (w'.map fun l => (sites.map (lm l)).prod (z' l.intersection_update_fsHerm_neg_one) 0).prod else 0 := fun z' => by
      first | exact ih hnd.2 z' | exact ih z' hnd.2
    have hne : ∀ l' ∈ w', l'.intersection_update_fsHerm_neg_one ≠ l.intersection_update_fsHerm_neg_one := fun l' hl' h =>
      hnd.1 (List.mem_map.mpr ⟨l', hl', h⟩)
    have hsplit : (sites.map fun σ => (bT σ (l :: w') : SlopeTestRemainingChoices S A)).prod =
        (sites.map fun σ => (vlet σ l : SlopeTestRemainingChoices S A)).prod * (sites.map fun σ => (bT σ w' : SlopeTestRemainingChoices S A)).prod :=
      prod_mul_list (fun σ => (vlet σ l : SlopeTestRemainingChoices S A)) (fun σ => bT σ w') sites
        (hs.imp fun {σ τ} hst => bT_comm_vlet hst w' l hnd.1)
    have hexp : uw sites (l :: w') z = ∑ j, (sites.map (lm l)).prod (z l.intersection_update_fsHerm_neg_one) j *
        uw sites w' (Function.update z l.intersection_update_fsHerm_neg_one j) := by
      unfold uw
      rw [hsplit, vlet_prod_mul_apply]
    have hval : ∀ j, (w'.map fun l' => (sites.map (lm l')).prod (Function.update z l.intersection_update_fsHerm_neg_one j l'.intersection_update_fsHerm_neg_one) 0).prod =
        (w'.map fun l' => (sites.map (lm l')).prod (z l'.intersection_update_fsHerm_neg_one) 0).prod := fun j => by
      congr 1
      refine List.map_congr_left fun l' hl' => ?_
      rw [Function.update_apply, if_neg (hne l' hl')]
    have hc1 : ¬ ∀ c, c ∉ w'.map Letter.intersection_update_fsHerm_neg_one → Function.update z l.intersection_update_fsHerm_neg_one 1 c = 0 := fun h => by
      have h1 := h l.intersection_update_fsHerm_neg_one hnd.1
      simp at h1
    have hc0 : (∀ c, c ∉ w'.map Letter.intersection_update_fsHerm_neg_one → Function.update z l.intersection_update_fsHerm_neg_one 0 c = 0) ↔
        ∀ c, c ∉ (l :: w').map Letter.intersection_update_fsHerm_neg_one → z c = 0 := by
      constructor
      · intro h c hc
        simp only [List.map_cons, List.mem_cons, not_or] at hc
        have h1 := h c hc.2
        rwa [Function.update_apply, if_neg hc.1] at h1
      · intro h c hc
        rw [Function.update_apply]
        by_cases hca : c = l.intersection_update_fsHerm_neg_one
        · rw [if_pos hca]
        · rw [if_neg hca]
          exact h c (by simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨hca, hc⟩)
    rw [hexp, Fin.sum_univ_two, ih', ih', if_neg hc1, mul_zero, add_zero, hval]
    by_cases hP : ∀ c, c ∉ (l :: w').map Letter.intersection_update_fsHerm_neg_one → z c = 0
    · rw [if_pos (hc0.mpr hP), if_pos hP, List.map_cons, List.prod_cons]
    · rw [if_neg (fun h => hP (hc0.mp h)), if_neg hP, mul_zero]

theorem uwProduct : UwProduct := by
  intro K A S _ _ _ _ _ _ _ _ QQ sites w hOK hw z
  rw [word_product_formula_general sites w hOK.2 hw.1 z]
  by_cases hc : ∀ c, c ∉ w.map Letter.intersection_update_fsHerm_neg_one → z c = 0
  · rw [if_pos hc, if_pos hc]
    congr 1
    refine List.map_congr_left fun l _ => ?_
    by_cases h : l.plus = true
    · have e : lm l = fun σ : Site A => Ts σ l.pt := funext fun σ => if_pos h
      rw [e, if_pos h]
      rfl
    · have e : lm l = fun σ : Site A => (Ts σ l.pt).map star := funext fun σ => if_neg h
      rw [e, if_neg h]
  · rw [if_neg hc, if_neg hc]

end Product

theorem tTFactor : TTFactor := by
  intro K A S _ _ _ _ _ _ _ _ QQ w Y
  induction w with
  | nil => simp [TTw, Xm, Xp]
  | cons l w ih =>
    by_cases h : l.plus = true
    · simp [TTw, Xm, Xp, h, ih, mul_assoc]
    · simp [TTw, Xm, Xp, h, ih, mul_assoc]

end Formalism.FourierDecayAlt.P.Wd8

theorem Formalism.FourierDecayAlt.P.exchange_vector_positive : Formalism.FourierDecayAlt.Wd.ExchVecA := Formalism.FourierDecayAlt.P.Wd8.exchVecA_of Formalism.FourierDecayAlt.P.exchange_plus_factor Formalism.FourierDecayAlt.P.positive_word_fixed

theorem Formalism.FourierDecayAlt.P.exchange_vector_negative : Formalism.FourierDecayAlt.Wd.ExchVecB := Formalism.FourierDecayAlt.P.Wd8.exchVecB_of Formalism.FourierDecayAlt.P.exchange_second_case Formalism.FourierDecayAlt.P.negative_word_fixed

theorem Formalism.FourierDecayAlt.P.conjugate_word_eigen : Formalism.FourierDecayAlt.Wd.CwEigen := Formalism.FourierDecayAlt.P.Wd8.cwEigen_of Formalism.FourierDecayAlt.P.exchange_plus_factor Formalism.FourierDecayAlt.P.exchange_second_case
  Formalism.FourierDecayAlt.P.positive_word_fixed Formalism.FourierDecayAlt.P.negative_word_fixed Formalism.FourierDecayAlt.P.Wd8.tTFactor

theorem Formalism.FourierDecayAlt.P.word_product_formula : Formalism.FourierDecayAlt.Wd.UwProduct := Formalism.FourierDecayAlt.P.Wd8.uwProduct
