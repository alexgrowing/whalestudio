import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.StdPos

open Formalism.UG (cT bc cT_mul cT_one)
open Matrix

section Pure

variable {R : Type} [CommRing R] (s : R →+* R) {n r m : ℕ} (J : Matrix (Fin n) (Fin n) R)

theorem exists_frame_of_inverse {κ : Type} [Fintype κ] [DecidableEq κ] (e : κ ≃ Fin n) (A : Matrix (Fin n) κ R)
    (B : Matrix κ (Fin n) R) (ε : κ → Bool) (hA : cT s A * J * A = diagonal fun i => if ε i then 1 else -1)
    (h2 : B * A = 1) :
    ∃ (b : GL (Fin n) R) (δ : Fin n → Bool), (cT s b.1 * J * b.1 = diagonal fun i => if δ i then 1 else -1) ∧
      cT s (b⁻¹).1 * (b⁻¹).1 = cT s B * B := by
  have h3 : A * B = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (Fintype.card_congr e)).1 h2
  refine ⟨⟨A.submatrix id e.symm, B.submatrix e.symm id, ?_, ?_⟩, fun i => ε (e.symm i), ?_, ?_⟩
  · rw [submatrix_mul_equiv, h3, submatrix_id_id]
  · exact (submatrix_mul _ _ _ id _ Function.bijective_id).symm.trans (by rw [h2, submatrix_one_equiv])
  · have := congrArg (fun y => y.submatrix e.symm e.symm) hA
    simp only [submatrix_diagonal_equiv] at this
    exact this
  · change (cT s B).submatrix id e.symm * B.submatrix e.symm id = _
    rw [submatrix_mul_equiv, submatrix_id_id]

theorem exists_frame_std (hn : m + 2 * r = n) {X Y : Matrix (Fin n) (Fin r) R} {I : Matrix (Fin n) (Fin m) R}
    {Q : Matrix (Fin m) (Fin n) R} {G : Matrix (Fin m) (Fin m) R} (c : GL (Fin m) R) (ε : Fin m → Bool)
    {u : R} (hu : u * u + u * u = 1) (hs : s u = u)
    (XX : cT s X * J * X = 0) (YY : cT s Y * J * Y = 0) (YX : cT s Y * J * X = 1) (XY : cT s X * J * Y = 1)
    (IX : cT s I * J * X = 0) (IY : cT s I * J * Y = 0) (XI : cT s X * J * I = 0) (YI : cT s Y * J * I = 0)
    (II : cT s I * J * I = G) (QX : Q * X = 0) (QY : Q * Y = 0) (QI : Q * I = 1)
    (hc : cT s c.1 * G * c.1 = diagonal fun i => if ε i then 1 else -1) :
    ∃ (b : GL (Fin n) R) (δ : Fin n → Bool), (cT s b.1 * J * b.1 = diagonal fun i => if δ i then 1 else -1) ∧
      cT s (b⁻¹).1 * (b⁻¹).1 = cT s (cT s Y * J) * (cT s Y * J) + cT s Q * ((cT s (c⁻¹).1 * (c⁻¹).1) * Q) +
        cT s (cT s X * J) * (cT s X * J) := by
  have hΔ : (diagonal fun i => if Sum.elim (Sum.elim (fun _ : Fin r => true) fun _ : Fin r => false) ε i then (1 : R) else -1) =
      fromBlocks (fromBlocks 1 0 0 (-1)) 0 0 (diagonal fun i => if ε i then 1 else -1) := by
    rw [← diagonal_one, diagonal_neg, fromBlocks_diagonal, fromBlocks_diagonal]
    exact congrArg diagonal (funext fun i => by rcases i with (i | i) | i <;> rfl)
  have hp : ∀ {k l : ℕ} (A B : Matrix (Fin k) (Fin l) R), cT s (u • A + u • B) = u • cT s A + u • cT s B :=
    fun A B => by ext i j; simp [cT, hs]
  have hm : ∀ {k l : ℕ} (A B : Matrix (Fin k) (Fin l) R), cT s (u • A - u • B) = u • cT s A - u • cT s B :=
    fun A B => by ext i j; simp [cT, hs]
  have hA : cT s (fromCols (fromCols (u • X + u • Y) (u • X - u • Y)) (I * c.1)) =
      fromRows (fromRows (u • cT s X + u • cT s Y) (u • cT s X - u • cT s Y)) (cT s c.1 * cT s I) := by
    rw [← hp, ← hm, ← cT_mul]; ext ((i | i) | i) j <;> rfl
  have h1 : ∀ {k : ℕ} (A : Matrix (Fin k) (Fin k) R), (u * u) • A + (u * u) • A = A := fun A => by
    rw [← add_smul, hu, one_smul]
  have IX' : cT s c.1 * cT s I * J * X = 0 := by
    rw [Matrix.mul_assoc (cT s c.1), Matrix.mul_assoc (cT s c.1), IX, Matrix.mul_zero]
  have IY' : cT s c.1 * cT s I * J * Y = 0 := by
    rw [Matrix.mul_assoc (cT s c.1), Matrix.mul_assoc (cT s c.1), IY, Matrix.mul_zero]
  have XI' : cT s X * J * (I * c.1) = 0 := by rw [← Matrix.mul_assoc, XI, Matrix.zero_mul]
  have YI' : cT s Y * J * (I * c.1) = 0 := by rw [← Matrix.mul_assoc, YI, Matrix.zero_mul]
  have II' : cT s c.1 * cT s I * J * (I * c.1) = diagonal fun i => if ε i then 1 else -1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (cT s c.1), Matrix.mul_assoc (cT s c.1), II, hc]
  have QX' : (c⁻¹).1 * Q * X = 0 := by rw [Matrix.mul_assoc, QX, Matrix.mul_zero]
  have QY' : (c⁻¹).1 * Q * Y = 0 := by rw [Matrix.mul_assoc, QY, Matrix.mul_zero]
  have QI' : (c⁻¹).1 * Q * (I * c.1) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, QI, Matrix.one_mul, Units.inv_mul]
  obtain ⟨b, δ, hb, hf⟩ := exists_frame_of_inverse s J (Fintype.equivFinOfCardEq (by simp [← hn]; ring))
    (fromCols (fromCols (u • X + u • Y) (u • X - u • Y)) (I * c.1))
    (fromRows (fromRows (u • (cT s Y * J) + u • (cT s X * J)) (u • (cT s Y * J) - u • (cT s X * J))) ((c⁻¹).1 * Q))
    (Sum.elim (Sum.elim (fun _ => true) fun _ => false) ε) (by
      rw [hΔ, hA, fromRows_mul _ _ J, fromRows_mul _ _ J, fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul,
        mul_fromCols]
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, XX, YY,
        YX, XY, IX', IY', XI', YI', II', smul_zero, add_zero, zero_add, sub_zero, zero_sub, fromRows_zero, fromCols_zero,
        smul_smul, smul_neg, h1, sub_self, neg_add_cancel, add_neg_cancel, ← neg_add', sub_neg_eq_add]) (by
      rw [fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols]
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, XX, YY,
        YX, XY, QX', QY', XI', YI', QI', smul_zero, add_zero, zero_add, sub_zero, zero_sub, fromRows_zero, fromCols_zero,
        smul_smul, smul_neg, h1, sub_self, neg_add_cancel, add_neg_cancel, ← neg_add', sub_neg_eq_add, fromBlocks_one])
  refine ⟨b, δ, hb, hf.trans ?_⟩
  generalize cT s Y * J = P, cT s X * J = P'
  have hB : cT s (fromRows (fromRows (u • P + u • P') (u • P - u • P')) ((c⁻¹).1 * Q)) =
      fromCols (fromCols (u • cT s P + u • cT s P') (u • cT s P - u • cT s P')) (cT s Q * cT s (c⁻¹).1) := by
    rw [← hp, ← hm, ← cT_mul]; ext i ((j | j) | j) <;> rfl
  rw [hB, fromCols_mul_fromRows, fromCols_mul_fromRows]
  conv_rhs => rw [← h1 (cT s P * P), ← h1 (cT s P' * P')]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    smul_add, smul_sub, Matrix.mul_assoc]
  abel

theorem map_cT {A : Type} [CommRing A] {s' : A →+* A} {φ : A →+* R} (h : ∀ x, φ (s' x) = s (φ x)) {k l : ℕ}
    (M : Matrix (Fin k) (Fin l) A) : (cT s' M).map φ = cT s (M.map φ) := by
  ext i j
  exact h _

theorem map_form {A : Type} [CommRing A] {s' : A →+* A} {φ : A →+* R} (h : ∀ x, φ (s' x) = s (φ x)) (c : GL (Fin m) A) :
    (cT s' (c⁻¹).1 * (c⁻¹).1).map φ = cT s ((bc φ c)⁻¹).1 * ((bc φ c)⁻¹).1 := by
  rw [Matrix.map_mul, map_cT s h, ← map_inv]
  rfl

theorem map_std {A : Type} [CommRing A] {s' : A →+* A} {φ : A →+* R} (h : ∀ x, φ (s' x) = s (φ x)) (c : GL (Fin m) A)
    (P P' : Matrix (Fin r) (Fin n) A) (Q : Matrix (Fin m) (Fin n) A) :
    (cT s' P * P + cT s' Q * ((cT s' (c⁻¹).1 * (c⁻¹).1) * Q) + cT s' P' * P').map φ =
      cT s (P.map φ) * P.map φ + cT s (Q.map φ) * ((cT s ((bc φ c)⁻¹).1 * ((bc φ c)⁻¹).1) * Q.map φ) +
        cT s (P'.map φ) * P'.map φ := by
  rw [← map_form s h, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), Matrix.map_mul (M := P),
    Matrix.map_mul (M := P'), Matrix.map_mul (L := cT s' Q), Matrix.map_mul (M := Q), map_cT s h, map_cT s h, map_cT s h]

end Pure

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n r m : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

omit [NumberField F] [NumberField E] in
theorem hE_mulVec {P : Matrix (Fin n) (Fin m) E} {G : Matrix (Fin m) (Fin m) E} {Q : Matrix (Fin m) (Fin n) E}
    (h : G * Q = cT (σ : E →+* E) P * J) (u : Fin m → E) (y : Fin n → E) : hE σ J (P *ᵥ u) y = hE σ G u (Q *ᵥ y) := by
  have h0 : ∀ {k : ℕ} (K : Matrix (Fin k) (Fin k) E) (x y : Fin k → E), hE σ K x y = (fun i => σ (x i)) ⬝ᵥ K *ᵥ y :=
    fun K x y => by simp [hE, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have e : (fun i => σ ((P *ᵥ u) i)) = (fun i => σ (u i)) ᵥ* cT (σ : E →+* E) P := by
    ext i; simp [cT, mulVec, vecMul, dotProduct, mul_comm]
  rw [h0, h0, mulVec_mulVec, h, e, ← dotProduct_mulVec, mulVec_mulVec]

theorem exists_lattice_std (hJ : J.det ≠ 0) {G : Matrix (Fin m) (Fin m) E} (hG : G.det ≠ 0)
    {L₀ : Submodule (𝓞 E) (Fin m → E)} (hL : Submodule.IsLattice E L₀) (hd : ∀ v, IsSelfDualAt σ G L₀ v)
    {X Y : Matrix (Fin n) (Fin r) E} {I : Matrix (Fin n) (Fin m) E} {Q : Matrix (Fin m) (Fin n) E}
    (XX : cT (σ : E →+* E) X * J * X = 0) (YY : cT (σ : E →+* E) Y * J * Y = 0) (YX : cT (σ : E →+* E) Y * J * X = 1)
    (XY : cT (σ : E →+* E) X * J * Y = 1) (XI : cT (σ : E →+* E) X * J * I = 0) (YI : cT (σ : E →+* E) Y * J * I = 0)
    (QX : Q * X = 0) (QY : Q * Y = 0) (QI : Q * I = 1) (hQ : G * Q = cT (σ : E →+* E) I * J)
    (h1 : X * (cT (σ : E →+* E) Y * J) + I * Q + Y * (cT (σ : E →+* E) X * J) = 1) :
    ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (∀ v, IsSelfDualAt σ J L v) ∧
      ∀ z, z ∈ L ↔ (cT (σ : E →+* E) Y * J) *ᵥ z ∈ stdLattice E r ∧ Q *ᵥ z ∈ L₀ ∧
        (cT (σ : E →+* E) X * J) *ᵥ z ∈ stdLattice E r := by
  let im : ∀ {k : ℕ}, Matrix (Fin n) (Fin k) E → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin n → E) :=
    fun P M => M.map (P.mulVecLin.restrictScalars (𝓞 E))
  have sp : ∀ {k : ℕ} (P : Matrix (Fin n) (Fin k) E) {M : Submodule (𝓞 E) (Fin k → E)}, Submodule.IsLattice E M →
      ∀ u, P *ᵥ u ∈ Submodule.span E (im P M : Set (Fin n → E)) := fun P M hM u =>
    Submodule.apply_mem_span_image_of_mem_span P.mulVecLin
      (hM.span_eq_top ▸ Submodule.mem_top : u ∈ Submodule.span E (M : Set _))
  have ad : ∀ x x' y : Fin n → E, hE σ J (x + x') y = hE σ J x y + hE σ J x' y := fun x x' y => by
    simp [hE, Formalism.UG.hform, add_mul, Finset.sum_add_distrib]
  set L := im X (stdLattice E r) ⊔ im I L₀ ⊔ im Y (stdLattice E r)
  have l1 : im X (stdLattice E r) ≤ L := le_sup_left.trans le_sup_left
  have l2 : im I L₀ ≤ L := le_sup_right.trans le_sup_left
  have l3 : im Y (stdLattice E r) ≤ L := le_sup_right
  have hz : ∀ z : Fin n → E, z = X *ᵥ ((cT (σ : E →+* E) Y * J) *ᵥ z) + I *ᵥ (Q *ᵥ z) +
      Y *ᵥ ((cT (σ : E →+* E) X * J) *ᵥ z) := fun z => by
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, ← add_mulVec, ← add_mulVec, h1, one_mulVec]
  have hm : ∀ z, z ∈ L ↔ (cT (σ : E →+* E) Y * J) *ᵥ z ∈ stdLattice E r ∧ Q *ᵥ z ∈ L₀ ∧
      (cT (σ : E →+* E) X * J) *ᵥ z ∈ stdLattice E r := fun z => by
    refine ⟨fun h => ?_, fun h => hz z ▸ add_mem (add_mem (l1 ⟨_, h.1, rfl⟩) (l2 ⟨_, h.2.1, rfl⟩)) (l3 ⟨_, h.2.2, rfl⟩)⟩
    obtain ⟨_, h', _, ⟨c, hc, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h'
    simp only [LinearMap.restrictScalars_apply, mulVecLin_apply, mulVec_add, mulVec_mulVec, XX, YY, YX, XY, XI, YI, QX, QY, QI,
      zero_mulVec, one_mulVec, add_zero, zero_add]
    exact ⟨ha, hb, hc⟩
  have hs : Submodule.IsLattice E (stdLattice E r) := isLattice_stdLattice
  have hl : Submodule.IsLattice E L := ⟨((hs.fg.map _).sup (hL.fg.map _)).sup (hs.fg.map _), eq_top_iff.2 fun z _ =>
    hz z ▸ add_mem (add_mem (Submodule.span_mono l1 (sp X hs _))
      (Submodule.span_mono l2 (sp I hL _))) (Submodule.span_mono l3 (sp Y hs _))⟩
  have d0 := (SelfDual.forall_isSelfDualAt_iff hG hL).1 hd
  have d1 := (SelfDual.forall_isSelfDualAt_iff (by simp) hs).1 (isSelfDualAt_stdLattice_one σ)
  have eX := hE_mulVec σ J (Matrix.one_mul (cT (σ : E →+* E) X * J))
  have eY := hE_mulVec σ J (Matrix.one_mul (cT (σ : E →+* E) Y * J))
  have eI := hE_mulVec σ J hQ
  refine ⟨L, hl, (SelfDual.forall_isSelfDualAt_iff hJ hl).2 fun y => ⟨fun hy x hx => ?_, fun h => (hm y).2
    ⟨(d1 _).2 fun u hu => eY u y ▸ h _ (l3 ⟨u, hu, rfl⟩), (d0 _).2 fun u hu => eI u y ▸ h _ (l2 ⟨u, hu, rfl⟩),
      (d1 _).2 fun u hu => eX u y ▸ h _ (l1 ⟨u, hu, rfl⟩)⟩⟩, hm⟩
  rw [hm] at hx hy
  rw [hz x, ad, ad, eX, eI, eY]
  exact add_mem (add_mem ((d1 _).1 hy.2.2 _ hx.1) ((d0 _).1 hy.2.1 _ hx.2.1)) ((d1 _).1 hy.1 _ hx.2.2)

omit [NumberField E] in

theorem exists_sqrt_half [IsTotallyReal F] (w : InfinitePlace F) :
    ∃ u : w.Completion ⊗[F] E, u * u + u * u = 1 ∧ sigR _ σ u = u := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  refine ⟨e.symm (√2)⁻¹ ⊗ₜ 1, ?_, by simp [sigR]⟩
  have h : (√2)⁻¹ * (√2)⁻¹ + (√2)⁻¹ * (√2)⁻¹ = (1 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← TensorProduct.add_tmul, ← map_mul, ← map_add, h, map_one]
  rfl

omit [NumberField E] in

theorem exists_arch_frame_std [IsTotallyReal F] (hn : m + 2 * r = n) {G : Matrix (Fin m) (Fin m) E}
    {X Y : Matrix (Fin n) (Fin r) E} {I : Matrix (Fin n) (Fin m) E} {Q : Matrix (Fin m) (Fin n) E}
    (XX : cT (σ : E →+* E) X * J * X = 0) (YY : cT (σ : E →+* E) Y * J * Y = 0) (YX : cT (σ : E →+* E) Y * J * X = 1)
    (XY : cT (σ : E →+* E) X * J * Y = 1) (IX : cT (σ : E →+* E) I * J * X = 0) (IY : cT (σ : E →+* E) I * J * Y = 0)
    (XI : cT (σ : E →+* E) X * J * I = 0) (YI : cT (σ : E →+* E) Y * J * I = 0) (II : cT (σ : E →+* E) I * J * I = G)
    (QX : Q * X = 0) (QY : Q * Y = 0) (QI : Q * I = 1) (w : InfinitePlace F) (c : GL (Fin m) (w.Completion ⊗[F] E))
    (ε : Fin m → Bool) (hc : cT (sigR _ σ) c.1 * JR w.Completion G * c.1 = diagonal fun i => if ε i then 1 else -1)
    {P P' : Matrix (Fin r) (Fin n) (w.Completion ⊗[F] E)} {Q' : Matrix (Fin m) (Fin n) (w.Completion ⊗[F] E)}
    (hP : P = (cT (σ : E →+* E) Y * J).map (inclR (F := F) w.Completion))
    (hP' : P' = (cT (σ : E →+* E) X * J).map (inclR (F := F) w.Completion))
    (hQ' : Q' = Q.map (inclR (F := F) w.Completion)) :
    ∃ (b : GL (Fin n) (w.Completion ⊗[F] E)) (δ : Fin n → Bool),
      (cT (sigR _ σ) b.1 * JR w.Completion J * b.1 = diagonal fun i => if δ i then 1 else -1) ∧
      cT (sigR _ σ) (b⁻¹).1 * (b⁻¹).1 = cT (sigR _ σ) P * P +
        (cT (sigR _ σ) Q' * ((cT (sigR _ σ) (c⁻¹).1 * (c⁻¹).1) * Q' : Matrix (Fin m) (Fin n) (w.Completion ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) + cT (sigR _ σ) P' * P' := by
  obtain ⟨u, hu, hσ⟩ := exists_sqrt_half σ w
  have up0 : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) E), (cT (σ : E →+* E) A * J).map (inclR (F := F) w.Completion) =
      (cT (sigR _ σ) (A.map (inclR (F := F) w.Completion)) * JR w.Completion J :
        Matrix (Fin k) (Fin n) (w.Completion ⊗[F] E)) := fun A => by
    rw [Matrix.map_mul]; rfl
  have up : ∀ {k l : ℕ} {A : Matrix (Fin n) (Fin k) E} {B : Matrix (Fin n) (Fin l) E} {C : Matrix (Fin k) (Fin l) E},
      cT (σ : E →+* E) A * J * B = C →
      (cT (sigR _ σ) (A.map (inclR (F := F) w.Completion)) * JR w.Completion J :
        Matrix (Fin k) (Fin n) (w.Completion ⊗[F] E)) *
        B.map (inclR (F := F) w.Completion) = C.map (inclR (F := F) w.Completion) := fun h => by
    rw [← up0, ← Matrix.map_mul, h]
  have z : ∀ {k l : ℕ}, (0 : Matrix (Fin k) (Fin l) E).map (inclR (F := F) w.Completion) = 0 :=
    Matrix.map_zero _ (map_zero _)
  have o : ∀ {k : ℕ}, (1 : Matrix (Fin k) (Fin k) E).map (inclR (F := F) w.Completion) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rw [hP, hP', hQ', up0, up0]
  exact exists_frame_std (sigR _ σ) (JR w.Completion J) hn (Q := Q.map (inclR (F := F) w.Completion)) c ε hu hσ
    ((up XX).trans z) ((up YY).trans z) ((up YX).trans o) ((up XY).trans o) ((up IX).trans z)
    ((up IY).trans z) ((up XI).trans z) ((up YI).trans z) (up II)
    (by rw [← Matrix.map_mul, QX, z]) (by rw [← Matrix.map_mul, QY, z]) (by rw [← Matrix.map_mul, QI, o]) hc

omit [NumberField E] in
theorem compInf_sigR (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    compInf F E w (sigR _ σ z) = sigR _ σ (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => rfl

omit [NumberField E] in
theorem map_inclR_compInf {k l : ℕ} (M : Matrix (Fin k) (Fin l) E) (w : InfinitePlace F) :
    (M.map (inclR (F := F) (AF F))).map (compInf F E w) = M.map (inclR (F := F) w.Completion) := by
  ext i j
  simp [compInf, inclR]

omit [NumberField E] in

theorem exists_adelic_frame_std [IsTotallyReal F] (hn : m + 2 * r = n) {G : Matrix (Fin m) (Fin m) E}
    {X Y : Matrix (Fin n) (Fin r) E} {I : Matrix (Fin n) (Fin m) E} {Q : Matrix (Fin m) (Fin n) E}
    (XX : cT (σ : E →+* E) X * J * X = 0) (YY : cT (σ : E →+* E) Y * J * Y = 0) (YX : cT (σ : E →+* E) Y * J * X = 1)
    (XY : cT (σ : E →+* E) X * J * Y = 1) (IX : cT (σ : E →+* E) I * J * X = 0) (IY : cT (σ : E →+* E) I * J * Y = 0)
    (XI : cT (σ : E →+* E) X * J * I = 0) (YI : cT (σ : E →+* E) Y * J * I = 0) (II : cT (σ : E →+* E) I * J * I = G)
    (QX : Q * X = 0) (QY : Q * Y = 0) (QI : Q * I = 1) (c : GL (Fin m) (AF F ⊗[F] E)) (hc : IsMajorantFrame σ G c)
    {P P' : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)} {Q' : Matrix (Fin m) (Fin n) (AF F ⊗[F] E)}
    (hP : P = (cT (σ : E →+* E) Y * J).map (inclR (F := F) (AF F)))
    (hP' : P' = (cT (σ : E →+* E) X * J).map (inclR (F := F) (AF F))) (hQ' : Q' = Q.map (inclR (F := F) (AF F))) :
    ∃ a : GL (Fin n) (AF F ⊗[F] E), IsMajorantFrame σ J a ∧ ∀ w,
      (cT (sigR _ σ) (a⁻¹).1 * (a⁻¹).1).map (compInf F E w) = (cT (sigR _ σ) P * P +
        (cT (sigR _ σ) Q' * ((cT (sigR _ σ) (c⁻¹).1 * (c⁻¹).1) * Q' : Matrix (Fin m) (Fin n) (AF F ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) + cT (sigR _ σ) P' * P').map (compInf F E w) := by
  choose ε hε using hc
  choose b δ hb hf using fun w => exists_arch_frame_std σ J hn XX YY YX XY IX IY XI YI II QX QY QI w
    (bc (compInf F E w) c) (ε w) (hε w) (P := P.map (compInf F E w)) (P' := P'.map (compInf F E w))
    (Q' := Q'.map (compInf F E w)) (hP ▸ map_inclR_compInf _ w) (hP' ▸ map_inclR_compInf _ w) (hQ' ▸ map_inclR_compInf _ w)
  obtain ⟨a, -, ha⟩ := Frames.exists_GL_of_components ∅ (fun _ => 1) (fun _ _ => rfl) b
  refine ⟨a, fun w => ⟨δ w, by rw [ha w]; exact hb w⟩, fun w => ?_⟩
  refine (map_form _ (compInf_sigR σ w) a).trans (Eq.trans ?_ (map_std _ (compInf_sigR σ w) c P P' Q').symm)
  rw [ha w]
  exact hf w

end Lattice

end GlobalTheory.RegSch.StdPos

namespace GlobalTheory.RegSch

open Formalism.UG (cT bc cT_mul cT_one)
open Matrix StdPos

theorem exists_good_compat : ∀ (D : D7) (T T' : HSp D) (t : ℕ) (d : HypDec T T' t) (l' : GlobalTheory.RegSch.Lvl T'), l'.Good →
    ∃ l : GlobalTheory.RegSch.Lvl T, l.Good ∧ GlobalTheory.RegSch.Compat d l l' := by
  intro D T T' t d l' hl'
  have sw : ∀ {k l : ℕ} {A : Matrix (Fin T.rank) (Fin k) D.host.E} {B : Matrix (Fin T.rank) (Fin l) D.host.E}
      {C : Matrix (Fin k) (Fin l) D.host.E}, Aᴴ * T.gram * B = C → Bᴴ * T.gram * A = Cᴴ := fun h => by
    rw [← h, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, Matrix.mul_assoc]
  have XY := (sw d.e'e).trans conjTranspose_one
  have XI := (sw d.i₀e).trans conjTranspose_zero
  have YI := (sw d.i₀e').trans conjTranspose_zero
  have h0 := isHermND_gram T'
  have hu : IsUnit T'.gram.det := h0.2.isUnit
  have QX : d.q0 * d.e = 0 := by rw [HypDec.q0, Matrix.mul_assoc, d.i₀e, Matrix.mul_zero]
  have QY : d.q0 * d.e' = 0 := by rw [HypDec.q0, Matrix.mul_assoc, d.i₀e', Matrix.mul_zero]
  have QI : d.q0 * d.i₀ = 1 := by rw [HypDec.q0, Matrix.mul_assoc, d.iso, nonsing_inv_mul _ hu]
  obtain ⟨L, hL, hd, hs⟩ := exists_lattice_std D.sp.cm.sig T.gram (isHermND_gram T).2 h0.2 hl'.1 hl'.2.1
    (X := d.e) (Y := d.e') (I := d.i₀) (Q := d.q0) d.ee d.e'e' d.e'e XY XI YI QX QY QI
    (mul_nonsing_inv_cancel_left _ _ hu) d.sum_eq_one_rat
  have := (isCMExt_host D).1
  obtain ⟨a, ha, hf⟩ := exists_adelic_frame_std D.sp.cm.sig T.gram d.rank_add (X := d.e) (Y := d.e') (I := d.i₀)
    (Q := d.q0) d.ee d.e'e' d.e'e XY d.i₀e d.i₀e' XI YI d.iso QX QY QI l'.c hl'.2.2 (P := d.pX) (P' := d.pY) (Q' := d.p0)
    rfl rfl rfl
  exact ⟨⟨L, a⟩, ⟨hL, hd, ha⟩, hs, hf⟩

theorem exists_good_frameLat (D : D7) (V : HSp D) : ∃ a, Lvl.Good (⟨frameLat V, a⟩ : Lvl V) :=
  (exists_isMaj V).imp fun _ h => ⟨isLattice_frameLat_host V, SelfDual.isSelfDualAt_frameLat D V, h⟩

end GlobalTheory.RegSch

end
