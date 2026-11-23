import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HypAdapt

open Formalism.UG (cT bc cT_mul cT_one)
open Matrix

section Pure

variable {R : Type} [CommRing R] (s : R →+* R) {n r m : ℕ} (J : Matrix (Fin n) (Fin n) R)

theorem exists_frame_of_sign {κ : Type} [Fintype κ] [DecidableEq κ] (e : κ ≃ Fin n) (A : Matrix (Fin n) κ R) (ε : κ → Bool)
    {X Z : Matrix (Fin n) (Fin r) R} (M N : Matrix κ (Fin r) R)
    (hA : cT s A * J * A = diagonal fun i => if ε i then 1 else -1) (hM : A * M = X) (hN : A * N = Z)
    (h : (diagonal fun i => if ε i then (1 : R) else -1) * N = M) :
    ∃ (b : GL (Fin n) R) (δ : Fin n → Bool), (cT s b.1 * J * b.1 = diagonal fun i => if δ i then 1 else -1) ∧
      cT s (b⁻¹).1 * (b⁻¹).1 * X = J * Z := by
  set Δ : Matrix κ κ R := diagonal fun i => if ε i then (1 : R) else -1 with hΔ
  have h1 : Δ * Δ = 1 := by
    rw [hΔ, diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i => by split_ifs <;> simp)
  have h2 : Δ * (cT s A * J) * A = 1 := by rw [Matrix.mul_assoc, hA, h1]
  have h3 : A * (Δ * (cT s A * J)) = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (Fintype.card_congr e)).1 h2
  generalize Δ * (cT s A * J) = B at h2 h3
  have h4 : cT s B * cT s A = 1 := by rw [← cT_mul, h3, cT_one]
  refine ⟨⟨A.submatrix id e.symm, B.submatrix e.symm id, ?_, ?_⟩, fun i => ε (e.symm i), ?_, ?_⟩
  · rw [submatrix_mul_equiv, h3, submatrix_id_id]
  · exact (submatrix_mul _ _ _ id _ Function.bijective_id).symm.trans (by rw [h2, submatrix_one_equiv])
  · have := congrArg (fun y => y.submatrix e.symm e.symm) hA
    simp only [hΔ, submatrix_diagonal_equiv] at this
    exact this
  · change (cT s B).submatrix id e.symm * B.submatrix e.symm id * X = _
    rw [submatrix_mul_equiv, submatrix_id_id, ← hM, Matrix.mul_assoc, ← Matrix.mul_assoc B, h2, Matrix.one_mul, ← h, ← hA,
      ← hN, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc, h4, Matrix.one_mul]

theorem exists_frame_hyp (hn : m + 2 * r = n) {X Y : Matrix (Fin n) (Fin r) R} {I : Matrix (Fin n) (Fin m) R} (ε : Fin m → Bool)
    {t : R} (ht : t + t = 1) (hs : s t = t)
    (XX : cT s X * J * X = 0) (YY : cT s Y * J * Y = 0) (YX : cT s Y * J * X = 1) (XY : cT s X * J * Y = 1)
    (IX : cT s I * J * X = 0) (IY : cT s I * J * Y = 0) (XI : cT s X * J * I = 0) (YI : cT s Y * J * I = 0)
    (II : cT s I * J * I = diagonal fun i => if ε i then 1 else -1) :
    ∃ (b : GL (Fin n) R) (δ : Fin n → Bool), (cT s b.1 * J * b.1 = diagonal fun i => if δ i then 1 else -1) ∧
      cT s (b⁻¹).1 * (b⁻¹).1 * X = (J * Y : Matrix (Fin n) (Fin r) R) * diagonal fun _ : Fin r => t := by
  have hΔ : (diagonal fun i => if Sum.elim (Sum.elim (fun _ : Fin r => true) fun _ : Fin r => false) ε i then (1 : R) else -1) =
      fromBlocks (fromBlocks 1 0 0 (-1)) 0 0 (diagonal fun i => if ε i then 1 else -1) := by
    rw [← diagonal_one, diagonal_neg, fromBlocks_diagonal, fromBlocks_diagonal]
    exact congrArg diagonal (funext fun i => by rcases i with (i | i) | i <;> rfl)
  have hp : cT s (X + t • Y) = cT s X + t • cT s Y := by ext i j; simp [cT, hs]
  have hm : cT s (X - t • Y) = cT s X - t • cT s Y := by ext i j; simp [cT, hs]
  have hc : cT s (fromCols (fromCols (X + t • Y) (X - t • Y)) I) =
      fromRows (fromRows (cT s X + t • cT s Y) (cT s X - t • cT s Y)) (cT s I) := by
    rw [← hp, ← hm]; ext ((i | i) | i) j <;> rfl
  have h1 : (t • 1 + t • 1 : Matrix (Fin r) (Fin r) R) = 1 := by rw [← add_smul, ht, one_smul]
  rw [Matrix.mul_assoc J]
  refine exists_frame_of_sign s J (Fintype.equivFinOfCardEq (by simp [← hn]; ring))
    (fromCols (fromCols (X + t • Y) (X - t • Y)) I) (Sum.elim (Sum.elim (fun _ => true) fun _ => false) ε)
    (fromRows (fromRows (t • 1) (t • 1)) 0) (fromRows (fromRows (t • 1) (-(t • 1))) 0) ?_ ?_ ?_ ?_
  · rw [hΔ, hc, fromRows_mul _ _ J, fromRows_mul _ _ J, fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, XX, YY, YX, XY,
      IX, IY, XI, YI, II, smul_zero, add_zero, zero_add, sub_zero, zero_sub, fromRows_zero, fromCols_zero, h1, sub_self,
      neg_add_cancel, add_neg_cancel, ← neg_add', sub_neg_eq_add]
  · rw [fromCols_mul_fromRows, fromCols_mul_fromRows, ← Matrix.add_mul]
    simp [← add_smul, smul_add, ht]
  · rw [fromCols_mul_fromRows, fromCols_mul_fromRows, ← smul_eq_mul_diagonal]
    have h2 : t • Y = (t * t) • Y + (t * t) • Y := by rw [← add_smul, ← mul_add, ht, mul_one]
    simp only [Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_zero, add_zero, smul_add, smul_sub, smul_smul]
    rw [h2]; abel
  · rw [hΔ, fromBlocks_mul_fromRows, fromBlocks_mul_fromRows]
    simp

theorem exists_frame_hyp' (hn : m + 2 * r = n) {X Y : Matrix (Fin n) (Fin r) R} {I : Matrix (Fin n) (Fin m) R}
    {G c : Matrix (Fin m) (Fin m) R} (ε : Fin m → Bool) {t : R} (ht : t + t = 1) (hs : s t = t)
    (XX : cT s X * J * X = 0) (YY : cT s Y * J * Y = 0) (YX : cT s Y * J * X = 1) (XY : cT s X * J * Y = 1)
    (IX : cT s I * J * X = 0) (IY : cT s I * J * Y = 0) (XI : cT s X * J * I = 0) (YI : cT s Y * J * I = 0)
    (II : cT s I * J * I = G) (hc : cT s c * G * c = diagonal fun i => if ε i then 1 else -1) :
    ∃ (b : GL (Fin n) R) (δ : Fin n → Bool), (cT s b.1 * J * b.1 = diagonal fun i => if δ i then 1 else -1) ∧
      cT s (b⁻¹).1 * (b⁻¹).1 * X = (J * Y : Matrix (Fin n) (Fin r) R) * diagonal fun _ : Fin r => t := by
  refine exists_frame_hyp s J hn (I := I * c) ε ht hs XX YY YX XY ?_ ?_ ?_ ?_ ?_
  · rw [cT_mul, Matrix.mul_assoc (cT s c), Matrix.mul_assoc (cT s c), IX, Matrix.mul_zero]
  · rw [cT_mul, Matrix.mul_assoc (cT s c), Matrix.mul_assoc (cT s c), IY, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, XI, Matrix.zero_mul]
  · rw [← Matrix.mul_assoc, YI, Matrix.zero_mul]
  · rw [← Matrix.mul_assoc, cT_mul, Matrix.mul_assoc (cT s c), Matrix.mul_assoc (cT s c), II, hc]

end Pure

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n r m : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

def imLat (P : Matrix (Fin n) (Fin m) E) (L : Submodule (𝓞 E) (Fin m → E)) : Submodule (𝓞 E) (Fin n → E) :=
  L.map (P.mulVecLin.restrictScalars (𝓞 E))

omit [NumberField E] in
theorem mulVec_mem_span_imLat (P : Matrix (Fin n) (Fin m) E) {L : Submodule (𝓞 E) (Fin m → E)} (hL : Submodule.IsLattice E L)
    (u : Fin m → E) : P *ᵥ u ∈ Submodule.span E (imLat P L : Set (Fin n → E)) :=
  Submodule.apply_mem_span_image_of_mem_span P.mulVecLin (hL.span_eq_top ▸ Submodule.mem_top : u ∈ Submodule.span E (L : Set _))

omit [NumberField F] [NumberField E] in
theorem hE_eq (x y : Fin n → E) : hE σ J x y = (fun i => σ (x i)) ⬝ᵥ J *ᵥ y := by
  simp [hE, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

omit [NumberField F] [NumberField E] in
theorem hE_mulVec {P : Matrix (Fin n) (Fin m) E} {G : Matrix (Fin m) (Fin m) E} {Q : Matrix (Fin m) (Fin n) E}
    (h : G * Q = cT (σ : E →+* E) P * J) (u : Fin m → E) (y : Fin n → E) : hE σ J (P *ᵥ u) y = hE σ G u (Q *ᵥ y) := by
  have e : (fun i => σ ((P *ᵥ u) i)) = (fun i => σ (u i)) ᵥ* cT (σ : E →+* E) P := by
    ext i; simp [cT, mulVec, vecMul, dotProduct, mul_comm]
  rw [hE_eq, hE_eq, mulVec_mulVec, h, e, ← dotProduct_mulVec, mulVec_mulVec]

omit [NumberField F] [NumberField E] in
theorem hE_add (x x' y : Fin n → E) : hE σ J (x + x') y = hE σ J x y + hE σ J x' y := by
  simp [hE, Formalism.UG.hform, add_mul, Finset.sum_add_distrib]

omit [NumberField E] in
theorem smul_col_mem {X : Matrix (Fin n) (Fin r) E} {u : Fin r → E} (hu : u ∈ stdLattice E r) (i : Fin r) :
    u i • Xᵀ i ∈ imLat X (stdLattice E r) := by
  refine ⟨Pi.single i (u i), fun j _ => ?_, ?_⟩
  · by_cases h : j = i
    · subst h; simpa using hu j trivial
    · simp [h]
  · ext j; simp [mul_comm]

theorem exists_lattice_hyp (hJ : J.det ≠ 0) {G : Matrix (Fin m) (Fin m) E} (hG : G.det ≠ 0)
    {L₀ : Submodule (𝓞 E) (Fin m → E)} (hL : Submodule.IsLattice E L₀) (hd : ∀ v, IsSelfDualAt σ G L₀ v)
    {X Y : Matrix (Fin n) (Fin r) E} {I : Matrix (Fin n) (Fin m) E} {Q : Matrix (Fin m) (Fin n) E}
    (XX : cT (σ : E →+* E) X * J * X = 0) (YY : cT (σ : E →+* E) Y * J * Y = 0) (YX : cT (σ : E →+* E) Y * J * X = 1)
    (XY : cT (σ : E →+* E) X * J * Y = 1) (XI : cT (σ : E →+* E) X * J * I = 0) (YI : cT (σ : E →+* E) Y * J * I = 0)
    (QX : Q * X = 0) (QY : Q * Y = 0) (QI : Q * I = 1) (hQ : G * Q = cT (σ : E →+* E) I * J)
    (h1 : X * (cT (σ : E →+* E) Y * J) + I * Q + Y * (cT (σ : E →+* E) X * J) = 1) :
    ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (∀ v, IsSelfDualAt σ J L v) ∧
      ∀ z ∈ L, ∀ i, ((cT (σ : E →+* E) Y * J) *ᵥ z) i • Xᵀ i ∈ L ∧ ((cT (σ : E →+* E) X * J) *ᵥ z) i • Yᵀ i ∈ L := by
  set L := imLat X (stdLattice E r) ⊔ imLat I L₀ ⊔ imLat Y (stdLattice E r)
  have l1 : imLat X (stdLattice E r) ≤ L := le_sup_left.trans le_sup_left
  have l2 : imLat I L₀ ≤ L := le_sup_right.trans le_sup_left
  have l3 : imLat Y (stdLattice E r) ≤ L := le_sup_right
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
    hz z ▸ add_mem (add_mem (Submodule.span_mono l1 (mulVec_mem_span_imLat X hs _))
      (Submodule.span_mono l2 (mulVec_mem_span_imLat I hL _))) (Submodule.span_mono l3 (mulVec_mem_span_imLat Y hs _))⟩
  have d0 := (SelfDual.forall_isSelfDualAt_iff hG hL).1 hd
  have d1 := (SelfDual.forall_isSelfDualAt_iff (by simp) hs).1 (isSelfDualAt_stdLattice_one σ)
  have eX := hE_mulVec σ J (Matrix.one_mul (cT (σ : E →+* E) X * J))
  have eY := hE_mulVec σ J (Matrix.one_mul (cT (σ : E →+* E) Y * J))
  have eI := hE_mulVec σ J hQ
  refine ⟨L, hl, (SelfDual.forall_isSelfDualAt_iff hJ hl).2 fun y => ⟨fun hy x hx => ?_, fun h => (hm y).2
    ⟨(d1 _).2 fun u hu => eY u y ▸ h _ (l3 ⟨u, hu, rfl⟩), (d0 _).2 fun u hu => eI u y ▸ h _ (l2 ⟨u, hu, rfl⟩),
      (d1 _).2 fun u hu => eX u y ▸ h _ (l1 ⟨u, hu, rfl⟩)⟩⟩,
    fun z h i => ⟨l1 (smul_col_mem ((hm z).1 h).1 i), l3 (smul_col_mem ((hm z).1 h).2.2 i)⟩⟩
  rw [hm] at hx hy
  rw [hz x, hE_add, hE_add, eX, eI, eY]
  exact add_mem (add_mem ((d1 _).1 hy.2.2 _ hx.1) ((d0 _).1 hy.2.1 _ hx.2.1)) ((d1 _).1 hy.1 _ hx.2.2)

theorem exists_arch_frame_hyp (h : IsCMExt F E σ) (hn : m + 2 * r = n) {G : Matrix (Fin m) (Fin m) E} (hG : IsHermND σ G)
    {X Y : Matrix (Fin n) (Fin r) E} {I : Matrix (Fin n) (Fin m) E}
    (XX : cT (σ : E →+* E) X * J * X = 0) (YY : cT (σ : E →+* E) Y * J * Y = 0) (YX : cT (σ : E →+* E) Y * J * X = 1)
    (XY : cT (σ : E →+* E) X * J * Y = 1) (IX : cT (σ : E →+* E) I * J * X = 0) (IY : cT (σ : E →+* E) I * J * Y = 0)
    (XI : cT (σ : E →+* E) X * J * I = 0) (YI : cT (σ : E →+* E) Y * J * I = 0) (II : cT (σ : E →+* E) I * J * I = G)
    (w : InfinitePlace F) : ∃ (b : GL (Fin n) (w.Completion ⊗[F] E)) (δ : Fin n → Bool),
      (cT (sigR _ σ) b.1 * JR w.Completion J * b.1 = diagonal fun i => if δ i then 1 else -1) ∧
      cT (sigR _ σ) (b⁻¹).1 * (b⁻¹).1 * X.map (inclR (F := F) w.Completion) =
        (JR w.Completion J * Y.map (inclR (F := F) w.Completion) : Matrix (Fin n) (Fin r) (w.Completion ⊗[F] E)) *
          diagonal fun _ : Fin r => inclR (F := F) w.Completion (2⁻¹ : E) := by
  obtain ⟨c, ε, hc⟩ := Frames.exists_arch_frame h hG w
  have up : ∀ {k l : ℕ} {A : Matrix (Fin n) (Fin k) E} {B : Matrix (Fin n) (Fin l) E} {C : Matrix (Fin k) (Fin l) E},
      cT (σ : E →+* E) A * J * B = C →
      (cT (sigR _ σ) (A.map (inclR (F := F) w.Completion)) * JR w.Completion J :
        Matrix (Fin k) (Fin n) (w.Completion ⊗[F] E)) *
        B.map (inclR (F := F) w.Completion) = C.map (inclR (F := F) w.Completion) := fun h => by
    rw [← h, Matrix.map_mul, Matrix.map_mul]; rfl
  have z : ∀ {k l : ℕ}, (0 : Matrix (Fin k) (Fin l) E).map (inclR (F := F) w.Completion) = 0 :=
    Matrix.map_zero _ (map_zero _)
  have o : (1 : Matrix (Fin r) (Fin r) E).map (inclR (F := F) w.Completion) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  refine exists_frame_hyp' _ _ hn (I := I.map (inclR (F := F) w.Completion)) ε
    (by rw [← map_add, ← map_one (inclR (F := F) w.Completion)]; norm_num) ?_
    ((up XX).trans z) ((up YY).trans z) ((up YX).trans o) ((up XY).trans o) ((up IX).trans z) ((up IY).trans z)
    ((up XI).trans z) ((up YI).trans z) (up II) hc
  change inclR (F := F) w.Completion (σ (2⁻¹ : E)) = _
  rw [map_inv₀, map_ofNat]

end Lattice

end GlobalTheory.HypAdapt

end
