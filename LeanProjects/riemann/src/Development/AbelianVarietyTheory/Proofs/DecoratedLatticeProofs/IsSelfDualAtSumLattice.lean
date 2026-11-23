import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst

noncomputable section
open scoped Matrix Classical TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.Inhab
variable {D : D7}

section Generic

open Matrix Formalism.UG

variable {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) {n m k : Type}

def frameCols (s : A) (x y : Matrix n k A) (z : Matrix n m A) : Matrix n ((k ⊕ m) ⊕ k) A :=
  fromCols (fromCols (s • (x + y)) z) (s • (x - y))

def frameRows (u : A) (x y : Matrix k n A) (z : Matrix m n A) : Matrix ((k ⊕ m) ⊕ k) n A :=
  fromRows (fromRows (u • (x + y)) z) (u • (x - y))

theorem cT_fromCols {n₁ n₂ : Type} (x : Matrix m n₁ A) (y : Matrix m n₂ A) :
    cT σ (fromCols x y) = fromRows (cT σ x) (cT σ y) := by
  ext (i | i) j <;> rfl

theorem cT_fromRows {n₁ n₂ : Type} (x : Matrix n₁ m A) (y : Matrix n₂ m A) :
    cT σ (fromRows x y) = fromCols (cT σ x) (cT σ y) := by
  ext i (j | j) <;> rfl

theorem cT_smul_add {s : A} (h : σ s = s) (x y : Matrix n k A) : cT σ (s • (x + y)) = s • (cT σ x + cT σ y) := by
  ext i j; simp [cT, h, mul_add]

theorem cT_smul_sub {s : A} (h : σ s = s) (x y : Matrix n k A) : cT σ (s • (x - y)) = s • (cT σ x - cT σ y) := by
  ext i j; simp [cT, h]

variable [Fintype n] [Fintype m] [Fintype k] [DecidableEq n] [DecidableEq m] [DecidableEq k]

theorem cols_mul_rows {s u : A} (h : 2 * (s * u) = 1) {x y : Matrix n k A} {z : Matrix n m A} {p q : Matrix k n A}
    {r : Matrix m n A} (h1 : x ⬝ p + z ⬝ r + y ⬝ q = 1) (e : n ≃ (k ⊕ m) ⊕ k) :
    (frameCols s x y z).submatrix id e ⬝ (frameRows u p q r).submatrix e id = 1 := by
  rw [submatrix_mul_equiv, submatrix_id_id, frameCols, frameRows, fromCols_mul_fromRows, fromCols_mul_fromRows, ← h1]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub]
  linear_combination (norm := module) h • (x ⬝ p + y ⬝ q)

theorem rows_form (φ : A →+* B) {u : A} (h : σ u = u) (hu : φ (2 * (u * u)) = 1) (p q : Matrix k n A) (r : Matrix m n A)
    (e : n ≃ (k ⊕ m) ⊕ k) :
    (cT σ ((frameRows u p q r).submatrix e id) ⬝ (frameRows u p q r).submatrix e id).map φ =
      (cT σ p ⬝ p + cT σ r ⬝ r + cT σ q ⬝ q).map φ := by
  have h2 : cT σ ((frameRows u p q r).submatrix e id) ⬝ (frameRows u p q r).submatrix e id =
      cT σ (frameRows u p q r) ⬝ frameRows u p q r := submatrix_mul_equiv (cT σ (frameRows u p q r)) _ id e id
  have h3 : cT σ (frameRows u p q r) ⬝ frameRows u p q r =
      (2 * (u * u)) • (cT σ p ⬝ p) + cT σ r ⬝ r + (2 * (u * u)) • (cT σ q ⬝ q) := by
    rw [frameRows, cT_fromRows, cT_fromRows, fromCols_mul_fromRows, fromCols_mul_fromRows, cT_smul_add σ h, cT_smul_sub σ h]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub]
    module
  rw [h2, h3]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul φ (2 * (u * u)), hu, one_mul]

theorem cols_gram (φ : A →+* B) {s : A} (h : σ s = s) (hs : φ (2 * (s * s)) = 1) {x y : Matrix n k A} {z : Matrix n m A}
    {G : Matrix n n A} (xx : cT σ x ⬝ (G ⬝ x) = 0) (xy : cT σ x ⬝ (G ⬝ y) = 1) (yx : cT σ y ⬝ (G ⬝ x) = 1)
    (yy : cT σ y ⬝ (G ⬝ y) = 0) (xz : cT σ x ⬝ (G ⬝ z) = 0) (yz : cT σ y ⬝ (G ⬝ z) = 0) (zx : cT σ z ⬝ (G ⬝ x) = 0)
    (zy : cT σ z ⬝ (G ⬝ y) = 0) {ε : m → Bool} (zz : (cT σ z ⬝ (G ⬝ z)).map φ = diagonal fun i => if ε i = true then 1 else -1)
    (e : n ≃ (k ⊕ m) ⊕ k) : ∃ ε' : n → Bool,
    (cT σ ((frameCols s x y z).submatrix id e) ⬝ G ⬝ (frameCols s x y z).submatrix id e).map φ =
      diagonal fun i => if ε' i = true then 1 else -1 := by
  have h1 : cT σ (frameCols s x y z) ⬝ G ⬝ frameCols s x y z =
      fromBlocks (fromBlocks ((2 * (s * s)) • 1) 0 0 (cT σ z ⬝ (G ⬝ z))) 0 0 (-(2 * (s * s)) • 1) := by
    rw [frameCols, cT_fromCols, cT_fromCols, Matrix.mul_assoc, mul_fromCols G, mul_fromCols G, fromRows_mul_fromCols,
      fromRows_mul_fromCols, fromRows_mul, mul_fromCols, cT_smul_add σ h, cT_smul_sub σ h]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      xx, xy, yx, yy, xz, yz, zx, zy, add_zero, zero_add, sub_zero, zero_sub, smul_zero, sub_self,
      add_neg_cancel, neg_add_cancel, fromRows_zero, fromCols_zero, smul_neg, sub_neg_eq_add]
    congr 1
    · congr 1
      module
    · module
  have h2 : cT σ ((frameCols s x y z).submatrix id e) ⬝ G ⬝ (frameCols s x y z).submatrix id e =
      (cT σ (frameCols s x y z) ⬝ G ⬝ frameCols s x y z).submatrix e e := rfl
  have h4 : ∀ a : A, (a • (1 : Matrix k k A)).map φ = diagonal fun _ => φ a := fun a => by
    rw [smul_one_eq_diagonal, diagonal_map (map_zero _)]
  refine ⟨Sum.elim (Sum.elim (fun _ => true) ε) (fun _ => false) ∘ e, ?_⟩
  rw [h2, ← submatrix_map, h1, fromBlocks_map, fromBlocks_map, zz, h4, h4, map_neg, hs]
  simp only [Matrix.map_zero _ (map_zero φ), fromBlocks_diagonal, submatrix_diagonal_equiv]
  congr 1
  ext i
  have h5 : ∀ j : (k ⊕ m) ⊕ k, Sum.elim (Sum.elim (fun _ => (1 : B)) fun i => if ε i = true then 1 else -1) (fun _ => -1) j =
      if Sum.elim (Sum.elim (fun _ => true) ε) (fun _ => false) j = true then 1 else -1 := by
    rintro ((j | j) | j) <;> rfl
  exact h5 (e i)

end Generic

theorem compInf_cA (w : InfinitePlace D.host.F) (x : AE D) :
    compInf D.host.F D.host.E w (cA D x) = sigR w.Completion D.sp.cm.sig (compInf D.host.F D.host.E w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [compInf, sigR]
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]

theorem compInf_incA (w : InfinitePlace D.host.F) (x : D.host.E) :
    compInf D.host.F D.host.E w (incA D x) = inclR w.Completion x := by
  simp [compInf, inclR, incA]

theorem maj_eq (V : HSp D) (a : GL (Fin V.rank) (AE D)) (w : InfinitePlace D.host.F) :
    Formalism.UG.cT (sigR w.Completion D.sp.cm.sig) (Formalism.UG.bc (compInf D.host.F D.host.E w) a).1 * JR w.Completion V.gram *
      (Formalism.UG.bc (compInf D.host.F D.host.E w) a).1 = (adj a.1 * gA V * a.1).map (compInf D.host.F D.host.E w) := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  exact (compInf_cA w _).symm

theorem exists_scalars (D : D7) : ∃ s u : AE D, cA D s = s ∧ cA D u = u ∧ 2 * (s * u) = 1 ∧
    (∀ w, compInf D.host.F D.host.E w (2 * (s * s)) = 1) ∧ ∀ w, compInf D.host.F D.host.E w (2 * (u * u)) = 1 := by
  have h : ∀ w : InfinitePlace D.host.F, ∃ x : w.Completion, 2 * (x * x) = 1 := fun w => by
    let f := InfinitePlace.Completion.ringEquivRealOfIsReal (DualPairCompare.isReal D w)
    refine ⟨f.symm (Real.sqrt (1 / 2)), f.injective ?_⟩
    rw [map_mul, map_mul, map_one, map_ofNat, f.apply_symm_apply, Real.mul_self_sqrt (by norm_num)]
    norm_num
  choose x hx using h
  let r : AF D.host.F := (x, 1)
  let r' : AF D.host.F := (x, algebraMap D.host.F _ (1 / 2))
  have hr : 2 * (r * r') = 1 := by
    refine Prod.ext (funext fun w => hx w) ?_
    change 2 * (1 * algebraMap D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (1 / 2)) = 1
    rw [one_mul, ← map_ofNat (algebraMap D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) 2, ← map_mul]
    norm_num
  have key : ∀ y : AF D.host.F, y.1 = x → ∀ w, compInf D.host.F D.host.E w (2 * ((y ⊗ₜ 1) * (y ⊗ₜ 1))) = 1 := by
    intro y hy w
    have e : compInf D.host.F D.host.E w (y ⊗ₜ 1) = Algebra.TensorProduct.includeLeftRingHom (x w) := by
      rw [← hy]; rfl
    rw [map_mul, map_mul, e, map_ofNat, ← map_ofNat (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F)
      (A := w.Completion) (B := D.host.E)) 2, ← map_mul, ← map_mul, hx, map_one]
  refine ⟨r ⊗ₜ 1, r' ⊗ₜ 1, by simp [sigR], by simp [sigR], ?_, key r rfl, key r' rfl⟩
  have := congrArg (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (B := D.host.E)) hr
  rw [map_mul, map_mul, map_ofNat, map_one] at this
  exact this

section Lattice

variable {T T' : HSp D} {t : ℕ} (d : HypDec T T' t)

def sumLattice (L' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)) : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E) :=
  (stdLattice D.host.E t).comap (d.qX.mulVecLin.restrictScalars _) ⊓ (L'.comap (d.q0.mulVecLin.restrictScalars _) ⊓
    (stdLattice D.host.E t).comap (d.qY.mulVecLin.restrictScalars _))

variable {L' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}

theorem mem_sumLattice (z : Fin T.rank → D.host.E) : z ∈ sumLattice d L' ↔
    (d.qX *ᵥ z ∈ stdLattice D.host.E t ∧ d.q0 *ᵥ z ∈ L' ∧ d.qY *ᵥ z ∈ stdLattice D.host.E t) := Iff.rfl

theorem eq_one_of_rat {k : ℕ} {a : Matrix (Fin k) (Fin T.rank) D.host.E} {b : Matrix (Fin T.rank) (Fin k) D.host.E}
    (h : rat a * rat b = 1) (x : Fin k → D.host.E) : a *ᵥ (b *ᵥ x) = x := by
  have : a * b = 1 := rat_injective (by rw [rat_mul, rat_one]; exact h)
  rw [Matrix.mulVec_mulVec, this, Matrix.one_mulVec]

theorem eq_zero_of_rat {k l : ℕ} {a : Matrix (Fin k) (Fin T.rank) D.host.E} {b : Matrix (Fin T.rank) (Fin l) D.host.E}
    (h : rat a * rat b = 0) (x : Fin l → D.host.E) : a *ᵥ (b *ᵥ x) = 0 := by
  have : a * b = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact h)
  rw [Matrix.mulVec_mulVec, this, Matrix.zero_mulVec]

theorem e_mem {a : Fin t → D.host.E} (ha : a ∈ stdLattice D.host.E t) : d.e *ᵥ a ∈ sumLattice d L' := by
  rw [mem_sumLattice, eq_one_of_rat d.pX_jX, eq_zero_of_rat d.p0_jX, eq_zero_of_rat d.pY_jX]
  exact ⟨ha, zero_mem _, zero_mem _⟩

theorem e'_mem {a : Fin t → D.host.E} (ha : a ∈ stdLattice D.host.E t) : d.e' *ᵥ a ∈ sumLattice d L' := by
  rw [mem_sumLattice, eq_one_of_rat d.pY_jY, eq_zero_of_rat d.p0_jY, eq_zero_of_rat d.pX_jY]
  exact ⟨zero_mem _, zero_mem _, ha⟩

theorem i₀_mem {a : Fin T'.rank → D.host.E} (ha : a ∈ L') : d.i₀ *ᵥ a ∈ sumLattice d L' := by
  rw [mem_sumLattice, eq_one_of_rat d.p0_j0, eq_zero_of_rat d.pX_j0, eq_zero_of_rat d.pY_j0]
  exact ⟨zero_mem _, ha, zero_mem _⟩

theorem decomp (z : Fin T.rank → D.host.E) : z = d.e *ᵥ (d.qX *ᵥ z) + d.i₀ *ᵥ (d.q0 *ᵥ z) + d.e' *ᵥ (d.qY *ᵥ z) := by
  simp only [Matrix.mulVec_mulVec, ← Matrix.add_mulVec, d.sum_eq_one_rat, Matrix.one_mulVec]

theorem mulVec_mem_span {k n : ℕ} (A : Matrix (Fin n) (Fin k) D.host.E) {N : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    (hN : Submodule.IsLattice D.host.E N) {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : ∀ a ∈ N, A *ᵥ a ∈ L)
    (z : Fin k → D.host.E) : A *ᵥ z ∈ Submodule.span D.host.E (L : Set (Fin n → D.host.E)) := by
  have h1 : Submodule.span D.host.E (N : Set (Fin k → D.host.E)) ≤
      (Submodule.span D.host.E (L : Set (Fin n → D.host.E))).comap A.mulVecLin :=
    Submodule.span_le.2 fun a ha => Submodule.subset_span (h a ha)
  exact h1 (by rw [hN.span_eq_top]; trivial)

theorem isLattice_sumLattice (hL : Submodule.IsLattice D.host.E L') : Submodule.IsLattice D.host.E (sumLattice d L') := by
  have hs : Submodule.IsLattice D.host.E (stdLattice D.host.E t) := isLattice_stdLattice
  refine ⟨?_, eq_top_iff.2 fun z _ => ?_⟩
  · have e : sumLattice d L' = (stdLattice D.host.E t).map (d.e.mulVecLin.restrictScalars _) ⊔
        L'.map (d.i₀.mulVecLin.restrictScalars _) ⊔ (stdLattice D.host.E t).map (d.e'.mulVecLin.restrictScalars _) := by
      refine le_antisymm (fun z hz => ?_) (sup_le (sup_le ?_ ?_) ?_)
      · rw [decomp d z]
        exact Submodule.add_mem_sup (Submodule.add_mem_sup ⟨_, hz.1, rfl⟩ ⟨_, hz.2.1, rfl⟩) ⟨_, hz.2.2, rfl⟩
      · rintro _ ⟨a, ha, rfl⟩; exact e_mem d ha
      · rintro _ ⟨a, ha, rfl⟩; exact i₀_mem d ha
      · rintro _ ⟨a, ha, rfl⟩; exact e'_mem d ha
    rw [e]
    exact ((hs.fg.map _).sup (hL.fg.map _)).sup (hs.fg.map _)
  · rw [decomp d z]
    exact add_mem (add_mem (mulVec_mem_span _ hs (fun _ => e_mem d) _) (mulVec_mem_span _ hL (fun _ => i₀_mem d) _))
      (mulVec_mem_span _ hs (fun _ => e'_mem d) _)

theorem hE_eq {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    hE D.sp.cm.sig J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp only [hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rfl

theorem hE_mulVec {n k : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (A : Matrix (Fin n) (Fin k) D.host.E)
    (x : Fin k → D.host.E) (y : Fin n → D.host.E) :
    hE D.sp.cm.sig J (A *ᵥ x) y = star x ⬝ᵥ ((Aᴴ * J) *ᵥ y) := by
  rw [hE_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

theorem hE_i₀ (x : Fin T'.rank → D.host.E) (y : Fin T.rank → D.host.E) :
    hE D.sp.cm.sig T.gram (d.i₀ *ᵥ x) y = hE D.sp.cm.sig T'.gram x (d.q0 *ᵥ y) := by
  rw [hE_mulVec, hE_eq, Matrix.mulVec_mulVec, HypDec.q0,
    Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 (AutFunCounterexample.gram_det_ne T'))]

theorem mem_std_iff (y : Fin t → D.host.E) : y ∈ stdLattice D.host.E t ↔
    ∀ x ∈ stdLattice D.host.E t, star x ⬝ᵥ y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have h := (SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) (J := (1 : Matrix (Fin t) (Fin t) D.host.E))
    (L := stdLattice D.host.E t) (by simp) isLattice_stdLattice).1 (fun v => isSelfDualAt_stdLattice_one ..) y
  simpa only [hE_eq, Matrix.one_mulVec] using h

theorem isSelfDualAt_sumLattice (hL : Submodule.IsLattice D.host.E L')
    (hd : ∀ v, IsSelfDualAt D.sp.cm.sig T'.gram L' v) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    IsSelfDualAt D.sp.cm.sig T.gram (sumLattice d L') v := by
  have h' := (SelfDual.forall_isSelfDualAt_iff (AutFunCounterexample.gram_det_ne T') hL).1 hd
  refine (SelfDual.forall_isSelfDualAt_iff (AutFunCounterexample.gram_det_ne T) (isLattice_sumLattice d hL)).2 (fun y => ?_) v
  constructor
  · intro hy x hx
    have e : hE D.sp.cm.sig T.gram x y = hE D.sp.cm.sig T.gram (d.e *ᵥ (d.qX *ᵥ x)) y +
        hE D.sp.cm.sig T.gram (d.i₀ *ᵥ (d.q0 *ᵥ x)) y + hE D.sp.cm.sig T.gram (d.e' *ᵥ (d.qY *ᵥ x)) y := by
      simp only [hE_eq]
      rw [← add_dotProduct, ← add_dotProduct, ← star_add, ← star_add, ← decomp d x]
    rw [e, hE_i₀, hE_mulVec _ d.e, hE_mulVec _ d.e']
    exact add_mem (add_mem ((mem_std_iff _).1 hy.2.2 _ hx.1) ((h' _).1 hy.2.1 _ hx.2.1)) ((mem_std_iff _).1 hy.1 _ hx.2.2)
  · intro h
    refine ⟨(mem_std_iff _).2 fun x hx => ?_, (h' _).2 fun x hx => ?_, (mem_std_iff _).2 fun x hx => ?_⟩
    · have := h _ (e'_mem d hx)
      rwa [hE_mulVec] at this
    · have := h _ (i₀_mem d hx)
      rwa [hE_i₀] at this
    · have := h _ (e_mem d hx)
      rwa [hE_mulVec] at this

end Lattice

theorem isMaj_iff (V : HSp D) (a : GL (Fin V.rank) (AE D)) : IsMaj V a ↔ ∀ w, ∃ ε : Fin V.rank → Bool,
    (adj a.1 ⬝ gA V ⬝ a.1).map (compInf D.host.F D.host.E w) = Matrix.diagonal fun i => if ε i = true then 1 else -1 :=
  forall_congr' fun w => exists_congr fun _ => ⟨(maj_eq V a w).symm.trans, (maj_eq V a w).trans⟩

section Frame

variable {T T' : HSp D} {t : ℕ} (d : HypDec T T' t)

theorem sum_frame (c : GL (Fin T'.rank) (AE D)) : d.jX ⬝ d.pX + (d.j0 ⬝ c.1) ⬝ ((c⁻¹).1 ⬝ d.p0) + d.jY ⬝ d.pY = 1 := by
  rw [Matrix.mul_assoc, cancel₂ c.mul_inv, Matrix.one_mul, d.sum_eq_one]

variable (c : Mx D T'.rank T'.rank)

theorem gram_Xc : adj d.jX ⬝ (gA T ⬝ (d.j0 ⬝ c)) = 0 := by rw [cancel₃ d.wittDecomp_gram_X_anisotropic, Matrix.zero_mul]

theorem gram_Yc : adj d.jY ⬝ (gA T ⬝ (d.j0 ⬝ c)) = 0 := by rw [cancel₃ d.gramR_Y0_eq_TI, Matrix.zero_mul]

theorem gram_cX : adj (d.j0 ⬝ c) ⬝ (gA T ⬝ d.jX) = 0 := by rw [adj_mul, Matrix.mul_assoc, d.gram_0X, Matrix.mul_zero]

theorem gram_cY : adj (d.j0 ⬝ c) ⬝ (gA T ⬝ d.jY) = 0 := by rw [adj_mul, Matrix.mul_assoc, d.gram_0Y, Matrix.mul_zero]

theorem gram_cc : adj c ⬝ gA T' ⬝ c = adj (d.j0 ⬝ c) ⬝ (gA T ⬝ (d.j0 ⬝ c)) := by
  rw [adj_mul, Matrix.mul_assoc, Matrix.mul_assoc, cancel₃ d.gram_00]

theorem adjoint_form_p_zero : adj d.p0 ⬝ ((adj c ⬝ c) ⬝ d.p0) = adj (c ⬝ d.p0) ⬝ (c ⬝ d.p0) := by
  rw [adj_mul, Matrix.mul_assoc, Matrix.mul_assoc]

theorem exists_frame (l' : Lvl T') (hm : IsMaj T' l'.c) :
    ∃ c : GL (Fin T.rank) (AE D), IsMaj T c ∧
    ∀ w, (adj (c⁻¹).1 ⬝ (c⁻¹).1 : Mx D T.rank T.rank).map (compInf D.host.F D.host.E w) =
      (adj d.pX ⬝ d.pX + adj d.p0 ⬝ (l'.form ⬝ d.p0) + adj d.pY ⬝ d.pY : Mx D T.rank T.rank).map
        (compInf D.host.F D.host.E w) := by
  obtain ⟨s, u, hs, hu, hsu, hss, huu⟩ := exists_scalars D
  have e : Fin T.rank ≃ (Fin t ⊕ Fin T'.rank) ⊕ Fin t := Fintype.equivOfCardEq (by simp [← d.rank_add]; ring)
  have h1 := cols_mul_rows hsu (sum_frame d l'.c) e
  refine ⟨⟨_, _, h1, mul_eq_one_comm.1 h1⟩, (isMaj_iff _ _).2 fun w => ?_, fun w => ?_⟩
  · obtain ⟨ε, hε⟩ := (isMaj_iff _ _).1 hm w
    rw [gram_cc d] at hε
    exact cols_gram (cA D) _ hs (hss w) d.gram_XX d.gram_XY d.gram_YX d.gram_YY (gram_Xc d _) (gram_Yc d _) (gram_cX d _)
      (gram_cY d _) hε e
  · rw [Lvl.form, adjoint_form_p_zero]
    exact rows_form (cA D) _ hu (huu w) d.pX d.pY _ e

end Frame

theorem exists_good (V : HSp D) : ∃ l : Lvl V, l.Good :=
  let ⟨a, ha⟩ := GlobalTheory.Doubling.exists_isMaj V
  ⟨⟨frameLat V, a⟩, isLattice_frameLat_host V, SelfDual.isSelfDualAt_frameLat D V, ha⟩

theorem exists_good_compat {T T' : HSp D} {t : ℕ} (d : HypDec T T' t) (l' : Lvl T') (h : l'.Good) :
    ∃ l : Lvl T, l.Good ∧ Compat d l l' :=
  let ⟨c, hc, hf⟩ := exists_frame d l' h.2.2
  ⟨⟨sumLattice d l'.L, c⟩, ⟨isLattice_sumLattice d h.1, isSelfDualAt_sumLattice d h.1 h.2.1, hc⟩, mem_sumLattice d, hf⟩

theorem good_iff_isLevel {V : HSp D} (l : Lvl V) : l.Good ↔ GlobalTheory.EisCont.IsLevel V l.L l.c :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2, h.3⟩⟩

theorem K_eq_lev {V : HSp D} (l : Lvl V) : l.K = GlobalTheory.EisCont.lev V l.L l.c := rfl

theorem levels_exist (D : D7) :
    (∀ V : HSp D, ∃ l : Lvl V, l.Good) ∧
    (∀ (T T' : HSp D) (t : ℕ) (d : HypDec T T' t) (l' : Lvl T'), l'.Good → ∃ l : Lvl T, l.Good ∧ Compat d l l') ∧
    ∀ (V : HSp D) (l : Lvl V), (l.Good ↔ GlobalTheory.EisCont.IsLevel V l.L l.c) ∧ l.K = GlobalTheory.EisCont.lev V l.L l.c :=
  ⟨exists_good, fun _ _ _ => exists_good_compat, fun _ l => ⟨good_iff_isLevel l, rfl⟩⟩

end GlobalTheory.RegSch.Inhab
