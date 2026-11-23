import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceBound
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceUmg

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} {n r s : ℕ}

namespace Dat

variable (b : Blo S r) (d : Dat S s)

def z0 : Fin (cons b d).len := (0 : Fin (d.len + 1))

def sc (j : Fin d.len) : Fin (cons b d).len := (j.succ : Fin (d.len + 1))

theorem sc_ne (j : Fin d.len) : sc b d j ≠ z0 b d := Fin.succ_ne_zero j

theorem sc_inj {j l : Fin d.len} : sc b d j = sc b d l ↔ j = l := Fin.succ_inj

theorem sc_cases {P : Fin (cons b d).len → Prop} (h0 : P (z0 b d)) (h1 : ∀ j, P (sc b d j)) (l : Fin (cons b d).len) : P l :=
  Fin.cases (n := d.len) (motive := P) h0 h1 l

theorem prod_cons {M : Type} [CommMonoid M] (f : Fin (cons b d).len → M) : ∏ l, f l = f (z0 b d) * ∏ j, f (sc b d j) :=
  Fin.prod_univ_succ (n := d.len) f

theorem idx_left (i : Fin r) : (cons b d).idx (Fin.castAdd s i) = z0 b d :=
  Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i

theorem idx_right (i : Fin s) : (cons b d).idx (Fin.natAdd r i) = sc b d (d.idx i) :=
  Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i

theorem sat_zero : (cons b d).sat (z0 b d) = b.sat := rfl

theorem sat_succ (j : Fin d.len) : (cons b d).sat (sc b d j) = d.sat j := rfl

theorem sum_zero {M : Type} [AddCommMonoid M] (f : Fin (r + s) → M) :
    ∑ i ∈ Finset.univ.filter (fun i => (cons b d).idx i = z0 b d), f i = ∑ i : Fin r, f (Fin.castAdd s i) := by
  rw [Finset.sum_filter, Fin.sum_univ_add]
  rw [Finset.sum_congr rfl fun i _ => if_pos (idx_left b d i), Finset.sum_eq_zero fun i _ => if_neg ?_, add_zero]
  rw [idx_right]
  exact sc_ne b d _

theorem sum_succ {M : Type} [AddCommMonoid M] (f : Fin (r + s) → M) (j : Fin d.len) :
    ∑ i ∈ Finset.univ.filter (fun i => (cons b d).idx i = sc b d j), f i =
      ∑ i ∈ Finset.univ.filter (fun i => d.idx i = j), f (Fin.natAdd r i) := by
  rw [Finset.sum_filter, Fin.sum_univ_add, Finset.sum_filter, Finset.sum_eq_zero fun i _ => if_neg ?_, zero_add]
  · refine Finset.sum_congr rfl fun i _ => if_congr ?_ rfl rfl
    rw [idx_right]
    exact sc_inj b d
  · rw [idx_left]
    exact (sc_ne b d _).symm

theorem size_zero : (cons b d).size (z0 b d) = r := by
  rw [size, Finset.card_eq_sum_ones, sum_zero]
  simp

theorem size_succ (j : Fin d.len) : (cons b d).size (sc b d j) = d.size j := by
  rw [size, size, Finset.card_eq_sum_ones, sum_succ, Finset.card_eq_sum_ones]

theorem sum_size {n : ℕ} (d : Dat S n) : ∑ j, d.size j = n := by
  have h := Finset.card_eq_sum_card_fiberwise (f := d.idx) (s := Finset.univ) (t := Finset.univ) fun _ _ => Finset.mem_univ _
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h.symm

private theorem sum_Iio_succ {m : ℕ} (f : Fin (m + 1) → ℝ) (j : Fin m) :
    ∑ l ∈ Finset.Iio j.succ, f l = f 0 + ∑ l ∈ Finset.Iio j, f l.succ := by
  rw [← Finset.filter_gt_eq_Iio, ← Finset.filter_gt_eq_Iio, Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
  simp

private theorem sum_Ioi_succ {m : ℕ} (f : Fin (m + 1) → ℝ) (j : Fin m) :
    ∑ l ∈ Finset.Ioi j.succ, f l = ∑ l ∈ Finset.Ioi j, f l.succ := by
  rw [← Finset.filter_lt_eq_Ioi, ← Finset.filter_lt_eq_Ioi, Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succ]
  simp

private theorem sum_Ioi_zero {m : ℕ} (f : Fin (m + 1) → ℝ) : ∑ l ∈ Finset.Ioi 0, f l = ∑ l : Fin m, f l.succ := by
  rw [← Finset.filter_lt_eq_Ioi, Finset.sum_filter, Fin.sum_univ_succ]
  simp

theorem rho_zero : (cons b d).rho (z0 b d) = -(s : ℝ) / 2 := by
  have h1 : ∑ l ∈ Finset.Ioi (z0 b d), ((cons b d).size l : ℝ) = ∑ l, ((cons b d).size (sc b d l) : ℝ) :=
    sum_Ioi_zero (m := d.len) fun l => ((cons b d).size l : ℝ)
  have h2 : ∑ l ∈ Finset.Iio (z0 b d), ((cons b d).size l : ℝ) = 0 :=
    Finset.sum_eq_zero fun l hl => absurd (Finset.mem_Iio.1 hl) (Fin.not_lt_zero (n := d.len + 1) l)
  simp only [size_succ] at h1
  rw [← Nat.cast_sum _ d.size, sum_size] at h1
  exact (congrArg₂ (fun x y : ℝ => (x - y) / 2) h2 h1).trans (by rw [zero_sub])

theorem rho_succ (j : Fin d.len) : (cons b d).rho (sc b d j) = d.rho j + (r : ℝ) / 2 := by
  have h1 : ∑ l ∈ Finset.Ioi (sc b d j), ((cons b d).size l : ℝ) = ∑ l ∈ Finset.Ioi j, ((cons b d).size (sc b d l) : ℝ) :=
    sum_Ioi_succ (m := d.len) (fun l => ((cons b d).size l : ℝ)) j
  have h2 : ∑ l ∈ Finset.Iio (sc b d j), ((cons b d).size l : ℝ) =
      ((cons b d).size (z0 b d) : ℝ) + ∑ l ∈ Finset.Iio j, ((cons b d).size (sc b d l) : ℝ) :=
    sum_Iio_succ (m := d.len) (fun l => ((cons b d).size l : ℝ)) j
  simp only [size_succ, size_zero] at h1 h2
  exact (congrArg₂ (fun x y : ℝ => (x - y) / 2) h2 h1).trans (by rw [rho]; ring)

theorem J_zero : (cons b d).J (z0 b d) = j1 E r s := by
  rw [J, size_zero, j1]
  exact congrArg _ (Finset.sum_congr rfl fun τ _ => sum_zero b d _)

theorem J_succ (j : Fin d.len) : (cons b d).J (sc b d j) =
    ((d.size j * Module.finrank ℚ E : ℕ) : ℂ)⁻¹ • ∑ τ : E →+* ℂ, ∑ i ∈ Finset.univ.filter fun i => d.idx i = j,
      Eop τ (Fin.natAdd r i) (Fin.natAdd r i) := by
  rw [J, size_succ]
  exact congrArg _ (Finset.sum_congr rfl fun τ _ => sum_succ b d _ j)

private theorem lev_diag {R : Type} [CommRing R] (x : Fin (r + s) → Rˣ) :
    diagUnits (r + s) x = lev R r s (diagUnits r fun i => x (Fin.castAdd s i), diagUnits s fun i => x (Fin.natAdd r i)) := by
  refine Units.ext ?_
  rw [lev, GlobalTheory.SmGL.val_emb₂]
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [GlobalTheory.SmGL.stdSum, Matrix.diagonal_apply, Fin.ext_iff] <;> omega

private theorem posIdele_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x = y) :
    posIdele (K := E) x hx = posIdele y hy := by subst h; rfl

theorem tr_cons (v : Fin (cons b d).len → ℝ) :
    (cons b d).tr v = lev (Ad E) r s (zt E r (v (z0 b d)), d.tr fun j => v (sc b d j)) := by
  refine (lev_diag _).trans (congrArg _ (Prod.ext (congrArg (diagUnits r) (funext fun i => ?_))
    (congrArg (diagUnits s) (funext fun i => ?_))))
  · refine posIdele_eq _ (Real.rpow_pos_of_pos (Real.exp_pos _) _) ?_
    rw [idx_left, size_zero, ← Real.exp_mul, Nat.cast_mul, div_eq_mul_inv]
  · refine posIdele_eq _ _ ?_
    rw [idx_right, size_succ]

theorem comp_cons (φ : GA E (r + s) → ℂ) (t : Fin (cons b d).len → ℝ) :
    (cons b d).comp φ t = d.comp (slice b.f.1 (t (z0 b d)) φ) fun j => t (sc b d j) := rfl

end Dat

theorem Umg.add {φ ψ : Sm E n} (h : Umg φ) (h' : Umg ψ) : Umg (φ + ψ) := ((umgOps E n).2 φ h).2.1 ψ h'

theorem Umg.smul {φ : Sm E n} (h : Umg φ) (c : ℂ) : Umg (c • φ) := ((umgOps E n).2 φ h).2.2.1 c

theorem Umg.uc {φ : Sm E n} (h : Umg φ) (u : UC E n) : Umg (uC E n u φ) := ((umgOps E n).2 φ h).2.2.2.1 u

theorem Umg.tr {φ : Sm E n} (h : Umg φ) (g : GA E n) : Umg (rt E n g φ) := ((umgOps E n).2 φ h).2.2.2.2.1 g

theorem Umg.hk {φ : Sm E n} (h : Umg φ) (w : Pl E) (j : ℕ) : Umg (hk n w j φ) := ((umgOps E n).2 φ h).2.2.2.2.2 w j

theorem Umg.sub {φ ψ : Sm E n} (h : Umg φ) (h' : Umg ψ) : Umg (φ - ψ) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ]
  exact h.add (h'.smul _)

theorem Umg.sum {ι : Type} {A : Finset ι} {φ : ι → Sm E n} (h : ∀ i ∈ A, Umg (φ i)) : Umg (∑ i ∈ A, φ i) :=
  Finset.sum_induction φ Umg (fun _ _ => Umg.add) (umgOps E n).1 h

theorem Umg.bound {φ : Sm E n} (h : Umg φ) : ∃ (N : ℕ) (B : ℝ), ∀ g, ‖φ.1 g‖ ≤ B * AutomorphicForm.height g ^ N := by
  obtain ⟨N, hN⟩ := h.growth
  obtain ⟨B, hB⟩ := hN 1
  exact ⟨N, B, by simpa using hB⟩

def Lnk (b : Blo S r) (X : Module.End ℂ (Sm E (r + s))) (Y : Module.End ℂ (Sm E s)) : Prop :=
  ∀ (t : ℝ) (φ : Sm E (r + s)) (ψ : Sm E s), Umg φ → ψ.1 = slice b.f.1 t φ.1 → Umg (X φ) ∧ (Y ψ).1 = slice b.f.1 t (X φ).1

variable {b : Blo S r}

theorem slice_lin (b : Blo S r) (t : ℝ) {φ ψ : Sm E (r + s)} (c : ℂ) (h : Umg φ) (h' : Umg ψ) :
    slice b.f.1 t (c • φ + ψ).1 = c • slice b.f.1 t φ.1 + slice b.f.1 t ψ.1 :=
  funext fun m => (sliceBound E S r s b).2 φ ψ c h h' t m

theorem slice_zero (b : Blo S r) (t : ℝ) : slice b.f.1 t (0 : Sm E (r + s)).1 = 0 := by
  have h := slice_lin b t (-1) (umgOps E (r + s)).1 (umgOps E (r + s)).1
  rwa [smul_zero, add_zero, neg_one_smul, neg_add_cancel] at h

theorem slice_add (b : Blo S r) (t : ℝ) {φ ψ : Sm E (r + s)} (h : Umg φ) (h' : Umg ψ) :
    slice b.f.1 t (φ + ψ).1 = slice b.f.1 t φ.1 + slice b.f.1 t ψ.1 := by
  have := slice_lin b t 1 h h'
  rwa [one_smul, one_smul] at this

theorem slice_smul (b : Blo S r) (t : ℝ) {φ : Sm E (r + s)} (c : ℂ) (h : Umg φ) :
    slice b.f.1 t (c • φ).1 = c • slice b.f.1 t φ.1 := by
  have := slice_lin b t c h (umgOps E (r + s)).1
  rwa [add_zero, slice_zero, add_zero] at this

namespace Lnk

variable {X X' : Module.End ℂ (Sm E (r + s))} {Y Y' : Module.End ℂ (Sm E s)}

theorem one : Lnk (s := s) b 1 1 := fun _ _ _ h e => ⟨h, e⟩

theorem zero : Lnk (s := s) b 0 0 := fun t _ _ _ _ => ⟨(umgOps E (r + s)).1, (slice_zero b t).symm⟩

theorem mul (h : Lnk b X Y) (h' : Lnk b X' Y') : Lnk b (X * X') (Y * Y') := fun t φ ψ hφ e =>
  h t _ _ (h' t φ ψ hφ e).1 (h' t φ ψ hφ e).2

theorem add (h : Lnk b X Y) (h' : Lnk b X' Y') : Lnk b (X + X') (Y + Y') := fun t φ ψ hφ e =>
  ⟨(h t φ ψ hφ e).1.add (h' t φ ψ hφ e).1, by
    rw [LinearMap.add_apply, LinearMap.add_apply, slice_add b t (h t φ ψ hφ e).1 (h' t φ ψ hφ e).1,
      ← (h t φ ψ hφ e).2, ← (h' t φ ψ hφ e).2]; rfl⟩

theorem smul (h : Lnk b X Y) (c : ℂ) : Lnk b (c • X) (c • Y) := fun t φ ψ hφ e =>
  ⟨(h t φ ψ hφ e).1.smul c, by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, slice_smul b t c (h t φ ψ hφ e).1, ← (h t φ ψ hφ e).2]; rfl⟩

theorem alg (c : ℂ) : Lnk (s := s) b (algebraMap ℂ _ c) (algebraMap ℂ _ c) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  exact one.smul c

theorem sum {ι : Type} {A : Finset ι} {X : ι → Module.End ℂ (Sm E (r + s))} {Y : ι → Module.End ℂ (Sm E s)}
    (h : ∀ i ∈ A, Lnk b (X i) (Y i)) : Lnk b (∑ i ∈ A, X i) (∑ i ∈ A, Y i) := by
  classical
  induction A using Finset.induction_on with
  | empty => exact zero
  | insert a A ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem prod : ∀ {k : ℕ} {X : Fin k → Module.End ℂ (Sm E (r + s))} {Y : Fin k → Module.End ℂ (Sm E s)},
    (∀ i, Lnk b (X i) (Y i)) → Lnk b (List.ofFn X).prod (List.ofFn Y).prod
  | 0, _, _, _ => by simpa using one
  | k + 1, X, Y, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact (h 0).mul (prod fun i => h i.succ)

theorem eop (τ : E →+* ℂ) (i j : Fin s) : Lnk b (Eop τ (Fin.natAdd r i) (Fin.natAdd r j)) (Eop τ i j) := fun t φ ψ hφ e => by
  obtain ⟨ψ', h1, -, h2, -⟩ := sliceUmg E S r s b t φ hφ
  obtain rfl : ψ = ψ' := Subtype.ext (e.trans h1.symm)
  exact ⟨uC_genC τ (Fin.natAdd r i) (Fin.natAdd r j) ▸ hφ.uc _, h2 τ i j⟩

theorem tr (g : GA E s) : Lnk b (rt E (r + s) (lev (Ad E) r s (1, g))) (rt E s g) := fun t φ ψ hφ e => by
  obtain ⟨ψ', h1, -, -, h2, -⟩ := sliceUmg E S r s b t φ hφ
  obtain rfl : ψ = ψ' := Subtype.ext (e.trans h1.symm)
  exact ⟨hφ.tr _, h2 g⟩

theorem J (d : Dat S s) (j : Fin d.len) : Lnk b ((Dat.cons b d).J (Dat.sc b d j)) (d.J j) := by
  rw [Dat.J_succ, Dat.J]
  exact (sum fun τ _ => sum fun i _ => eop τ i i).smul _

end Lnk

theorem Umg.j1 {φ : Sm E (r + s)} (h : Umg φ) : Umg (j1 E r s φ) := by
  rw [BW.j1, LinearMap.smul_apply, LinearMap.sum_apply]
  refine (Umg.sum fun τ _ => ?_).smul _
  rw [LinearMap.sum_apply]
  exact Umg.sum fun i _ => uC_genC τ (Fin.castAdd s i) (Fin.castAdd s i) ▸ h.uc _

end UpperTheory.ConvolutionTheory.BW
