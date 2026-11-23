import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm

section Abstract

variable {R : Type} [CommRing R] {m : Type} [Fintype m] [DecidableEq m]

theorem commute_of_proj {x y P Q : Matrix m m R} (hPQ : P + Q = 1) (hxP : x * P = P * x) (hxQ : x * Q = Q)
    (hyP : y * P = P) (hyQ : y * Q = Q * y) : x * y = y * x := by
  have e1 : x * y = x * P + Q * y := by
    calc x * y = x * y * (P + Q) := by rw [hPQ, Matrix.mul_one]
      _ = x * (y * P) + (x * Q) * y := by
        rw [Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc x y Q, hyQ, ← Matrix.mul_assoc x Q y]
      _ = x * P + Q * y := by rw [hyP, hxQ]
  have e2 : y * x = x * P + Q * y := by
    calc y * x = y * x * (P + Q) := by rw [hPQ, Matrix.mul_one]
      _ = (y * P) * x + y * Q := by
        rw [Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc y x Q, hxP, hxQ, ← Matrix.mul_assoc]
      _ = x * P + Q * y := by rw [hyP, hyQ, hxP]
  rw [e1, e2]

theorem mul_eq_of_unitary {s : R →+* R} {g M J : Matrix m m R} (hJ : IsUnit J.det)
    (hg : Formalism.UG.cT s g * J * g = J) (hM : Formalism.UG.cT s M * J = J * M) (h : g * M = M) : M * g = M := by
  have h1 : Formalism.UG.cT s M * Formalism.UG.cT s g = Formalism.UG.cT s M := by rw [← Formalism.UG.cT_mul, h]
  have h2 : J * (M * g) = J * M := by
    calc J * (M * g) = (Formalism.UG.cT s M * J) * g := by rw [hM, Matrix.mul_assoc]
      _ = Formalism.UG.cT s M * (Formalism.UG.cT s g * J * g) := by
        conv_lhs => rw [← h1]
        simp only [Matrix.mul_assoc]
      _ = J * M := by rw [hg, hM]
  calc M * g = J⁻¹ * (J * (M * g)) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul]
    _ = M := by rw [h2, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul]

theorem cT_add {s : R →+* R} {a b : Type} (M N : Matrix a b R) :
    Formalism.UG.cT s (M + N) = Formalism.UG.cT s M + Formalism.UG.cT s N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_sub {s : R →+* R} {a b : Type} (M N : Matrix a b R) :
    Formalism.UG.cT s (M - N) = Formalism.UG.cT s M - Formalism.UG.cT s N := by
  ext i j; simp [Formalism.UG.cT]

end Abstract

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

theorem sig_sig (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2, hCM.2.2.2, star_star]

def blockDiag (B : Set (Fin r)) : Matrix (Fin r) (Fin r) E := diagonal (B.indicator 1)

theorem blockDiag_mul_self (B : Set (Fin r)) : blockDiag (E := E) B * blockDiag B = blockDiag B := by
  simp only [blockDiag, diagonal_mul_diagonal]
  congr 1; funext i
  by_cases h : i ∈ B <;> simp [h]

theorem blockDiag_mul_disj {B B' : Set (Fin r)} (h : Disjoint B B') : blockDiag (E := E) B * blockDiag B' = 0 := by
  simp only [blockDiag, diagonal_mul_diagonal]
  rw [← diagonal_zero]
  congr 1; funext i
  by_cases hi : i ∈ B
  · have : i ∉ B' := Set.disjoint_left.1 h hi
    simp [this]
  · simp [hi]

theorem cT_blockDiag (B : Set (Fin r)) : Formalism.UG.cT (σ : E →+* E) (blockDiag B) = blockDiag B := by
  ext i j
  by_cases h : j ∈ B <;> by_cases e : i = j <;> simp [Formalism.UG.cT, blockDiag, diagonal, h, e, eq_comm]

theorem blockDiag_cancel {B : Set (Fin r)} (N : Matrix (Fin r) (Fin n) E) :
    blockDiag (E := E) B * (N - blockDiag (E := E) B * N) = 0 := by
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, blockDiag_mul_self, sub_self]

theorem blockDiag_disj_zero {B B' : Set (Fin r)} (h : Disjoint B' B) (N : Matrix (Fin r) (Fin n) E) :
    blockDiag (E := E) B' * (blockDiag (E := E) B * N) = 0 := by
  rw [← Matrix.mul_assoc, blockDiag_mul_disj h, Matrix.zero_mul]

theorem row_zero {B : Set (Fin r)} {M : Matrix (Fin r) (Fin n) E} (h : blockDiag (E := E) B * M = 0) {i : Fin r} (hi : i ∈ B)
    (j : Fin n) : M i j = 0 := by
  have := congrFun (congrFun h i) j
  simpa [blockDiag, diagonal_mul, Set.indicator_of_mem hi] using this

variable (X Y : Matrix (Fin n) (Fin r) E)

def frameProj (B : Set (Fin r)) : Matrix (Fin n) (Fin n) E :=
  X * blockDiag (E := E) B * (Formalism.UG.cT (σ : E →+* E) Y * J) + Y * blockDiag (E := E) B * (Formalism.UG.cT (σ : E →+* E) X * J)

variable {σ J X Y}

theorem yJx (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
  have hcJ : Formalism.UG.cT (σ : E →+* E) J = J := by ext i j; simp [Formalism.UG.cT, hJ.1 i j]
  have hcc : Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) X) = X := by
    ext i j; simp [Formalism.UG.cT, sig_sig σ hCM]
  have := congrArg (Formalism.UG.cT (σ : E →+* E)) hW.xy
  rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hcJ, hcc, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this

theorem xJ_frameProj (hW : IsWittFrame σ J X Y) (B : Set (Fin r)) :
    Formalism.UG.cT (σ : E →+* E) X * J * frameProj σ J X Y B = blockDiag B * (Formalism.UG.cT (σ : E →+* E) X * J) := by
  simp only [frameProj, Matrix.mul_add, ← Matrix.mul_assoc, hW.xx, hW.xy, Matrix.zero_mul, Matrix.one_mul, zero_add]
  exact Matrix.mul_assoc _ _ _

theorem yJ_frameProj (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (B : Set (Fin r)) :
    Formalism.UG.cT (σ : E →+* E) Y * J * frameProj σ J X Y B = blockDiag B * (Formalism.UG.cT (σ : E →+* E) Y * J) := by
  simp only [frameProj, Matrix.mul_add, ← Matrix.mul_assoc, hW.yy, yJx hCM hJ hW, Matrix.zero_mul, Matrix.one_mul,
    add_zero]
  exact Matrix.mul_assoc _ _ _

theorem frameProj_selfAdj (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (B : Set (Fin r)) :
    Formalism.UG.cT (σ : E →+* E) (frameProj σ J X Y B) * J = J * frameProj σ J X Y B := by
  have hcJ : Formalism.UG.cT (σ : E →+* E) J = J := by ext i j; simp [Formalism.UG.cT, hJ.1 i j]
  have hcc : ∀ Z : Matrix (Fin n) (Fin r) E, Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) Z) = Z := fun Z => by
    ext i j; simp [Formalism.UG.cT, sig_sig σ hCM]
  simp only [frameProj, GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.cT_add, Formalism.UG.cT_mul, hcJ, hcc, cT_blockDiag, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  rw [add_comm]

end Field

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem sigR_incl (e : E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem cT_map {a b : Type} (M : Matrix a b E) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (M.map (inclR (F := F) (AF F))) =
      (Formalism.UG.cT (σ : E →+* E) M).map (inclR (F := F) (AF F)) := by
  ext i j; simp [Formalism.UG.cT, sigR_incl]

theorem mem_colPerp (C : Matrix (Fin n) (Fin r) E) {B : Set (Fin r)} {M : Matrix (Fin n) (Fin n) E}
    (h : blockDiag (E := E) B * (Formalism.UG.cT (σ : E →+* E) C * J * M) = 0) (v : Fin n → AF F ⊗[F] E) :
    M.map (inclR (F := F) (AF F)) *ᵥ v ∈ colPerp σ J C B := by
  simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply, Matrix.mulVecLin_apply,
    LinearMap.proj_apply]
  intro i hi
  rw [mulVec_mulVec, ← Matrix.map_mul]
  simp [mulVec, dotProduct, row_zero h hi]

theorem fix_of_perp {B : Set (Fin r)} {g : GAd σ J} (hg : g ∈ ptStab σ J (colPerp σ J X B ⊓ colPerp σ J Y B))
    (M : Matrix (Fin n) (Fin n) E) (hX : blockDiag (E := E) B * (Formalism.UG.cT (σ : E →+* E) X * J * M) = 0)
    (hY : blockDiag (E := E) B * (Formalism.UG.cT (σ : E →+* E) Y * J * M) = 0) :
    (GlobalTheory.AdelicU.matHom (AF F) σ J g).1 * M.map (inclR (F := F) (AF F)) = M.map (inclR (F := F) (AF F)) := by
  have key : ∀ v, (GlobalTheory.AdelicU.matHom (AF F) σ J g).1 *ᵥ (M.map (inclR (F := F) (AF F)) *ᵥ v) =
      M.map (inclR (F := F) (AF F)) *ᵥ v := fun v =>
    hg _ (Submodule.mem_inf.2 ⟨mem_colPerp X hX v, mem_colPerp Y hY v⟩)
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  rw [mulVec_mulVec, mulVec_single_one, mulVec_single_one] at this
  exact this

theorem mem_colSpan (C : Matrix (Fin n) (Fin r) E) {B I : Set (Fin r)} (hB : B ⊆ I) (w : Fin r → AF F ⊗[F] E) :
    adMat F C *ᵥ ((blockDiag (E := E) B).map (inclR (F := F) (AF F)) *ᵥ w) ∈ colSpan F C I := by
  have e : ∀ u : Fin r → AF F ⊗[F] E, adMat F C *ᵥ u = ∑ i, u i • (adMat F C)ᵀ i := fun u => by
    ext j; simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [e]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i ∈ B
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hB hi, rfl⟩)
  · have : ((blockDiag (E := E) B).map (inclR (F := F) (AF F)) *ᵥ w) i = 0 := by
      simp [blockDiag, diagonal_map, mulVec_diagonal, hi]
    rw [this, zero_smul]
    exact zero_mem _

theorem frameProj_map (B : Set (Fin r)) :
    (frameProj σ J X Y B).map (inclR (F := F) (AF F)) =
      adMat F X * (blockDiag (E := E) B).map (inclR (F := F) (AF F)) * adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) +
      adMat F Y * (blockDiag (E := E) B).map (inclR (F := F) (AF F)) * adMat F (Formalism.UG.cT (σ : E →+* E) X * J) := by
  rw [frameProj, Matrix.map_add _ (map_add (inclR (F := F) (E := E) (AF F)))]
  simp only [Matrix.map_mul]

theorem fix_of_span {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ uPart σ J X Y T) {k : Fin r} (hk : k ∈ T) :
    (GlobalTheory.AdelicU.matHom (AF F) σ J g).1 * (frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F)) =
      (frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F)) := by
  have hB : block T k ⊆ upTo T := fun i hi => ⟨k, hk, hi.1⟩
  have key : ∀ v, (GlobalTheory.AdelicU.matHom (AF F) σ J g).1 *ᵥ ((frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F)) *ᵥ v) =
      (frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F)) *ᵥ v := fun v => by
    refine hg _ ?_
    rw [frameProj_map, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    exact Submodule.add_mem_sup (mem_colSpan X hB _) (mem_colSpan Y hB _)
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  rw [mulVec_mulVec, mulVec_single_one, mulVec_single_one] at this
  exact this

theorem block_disjoint {T : Finset (Fin r)} {k k' : Fin r} (hk : k ∈ T) (hk' : k' ∈ T) (hne : k ≠ k') :
    Disjoint (block T k) (block T k') := by
  refine Set.disjoint_left.2 fun i hi hi' => ?_
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd (hi'.2 k hk h) (not_lt.2 hi.1)
  · exact absurd (hi.2 k' hk' h) (not_lt.2 hi'.1)

theorem comm_gl (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {T : Finset (Fin r)} {k : Fin r}
    {x y : GAd σ J} (hx : x ∈ glPart σ J X Y T k)
    (hy : (GlobalTheory.AdelicU.matHom (AF F) σ J y).1 * (frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F)) =
      (frameProj σ J X Y (block T k)).map (inclR (F := F) (AF F))) : Commute x y := by
  set P := frameProj σ J X Y (block T k)
  set P' := P.map (inclR (F := F) (AF F))
  set gx := (GlobalTheory.AdelicU.matHom (AF F) σ J x).1
  set gy := (GlobalTheory.AdelicU.matHom (AF F) σ J y).1
  have hgx : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) gx * JR (F := F) (AF F) J * gx = JR (F := F) (AF F) J :=
    (show HR (AF F) σ J from x).2
  have hgy : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) gy * JR (F := F) (AF F) J * gy = JR (F := F) (AF F) J :=
    (show HR (AF F) σ J from y).2
  have hJR : JR (F := F) (AF F) J = J.map (inclR (F := F) (AF F)) := rfl
  have hJu : IsUnit (JR (F := F) (AF F) J).det := by
    rw [hJR, show (J.map (inclR (F := F) (E := E) (AF F))).det = inclR (F := F) (E := E) (AF F) J.det from
      (RingHom.map_det (inclR (F := F) (E := E) (AF F)) J).symm]
    exact (isUnit_iff_ne_zero.2 hJ.2).map (inclR (F := F) (E := E) (AF F))
  have hPs : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) P' * JR (F := F) (AF F) J = JR (F := F) (AF F) J * P' := by
    rw [cT_map, hJR, ← Matrix.map_mul, ← Matrix.map_mul, frameProj_selfAdj hCM hJ]
  have hQs : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (1 - P') * JR (F := F) (AF F) J = JR (F := F) (AF F) J * (1 - P') := by
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm.cT_sub, Formalism.UG.cT_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hPs]
  have hQ : 1 - P' = (1 - P).map (inclR (F := F) (AF F)) := by
    rw [Matrix.map_sub _ (map_sub (inclR (F := F) (E := E) (AF F))), Matrix.map_one _ (map_zero _) (map_one _)]
  have hxQ : gx * (1 - P') = 1 - P' := by
    rw [hQ]
    refine fix_of_perp (Subgroup.mem_inf.1 hx).2 (1 - P) ?_ ?_
    · rw [Matrix.mul_sub, Matrix.mul_one, xJ_frameProj hW]
      exact blockDiag_cancel _
    · rw [Matrix.mul_sub, Matrix.mul_one, yJ_frameProj hCM hJ hW]
      exact blockDiag_cancel _
  have hQx : (1 - P') * gx = 1 - P' := mul_eq_of_unitary hJu hgx hQs hxQ
  have hxP : gx * P' = P' * gx := by
    have := hxQ.trans hQx.symm
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul] at this
    exact sub_right_injective this
  have hyP' : P' * gy = P' := mul_eq_of_unitary hJu hgy hPs hy
  have hyQ : gy * (1 - P') = (1 - P') * gy := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hy, hyP']
  have hc : gx * gy = gy * gx := commute_of_proj (add_sub_cancel P' 1) hxP hxQ hy hyQ
  refine GlobalTheory.AdelicU.matHom_injective (AF F) σ J ?_
  rw [map_mul, map_mul]
  exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hc)

end Adelic

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm

theorem part_commute : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ T : Finset (Fin r), Pairwise fun i j : Option {k // k ∈ T} => ∀ x y : GAd σ J, x ∈ part σ J X Y T i → y ∈ part σ J X Y T j → Commute x y := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW T i j hij x y hx hy
  rcases i with _ | ⟨k, hk⟩ <;> rcases j with _ | ⟨k', hk'⟩
  · exact absurd rfl hij
  · exact (comm_gl hCM hJ hW hy (fix_of_span hx hk')).symm
  · exact comm_gl hCM hJ hW hx (fix_of_span hy hk)
  · have hne : k ≠ k' := fun e => hij (by subst e; rfl)
    refine comm_gl hCM hJ hW hx (fix_of_perp (Subgroup.mem_inf.1 hy).2 _ ?_ ?_)
    · rw [xJ_frameProj hW]
      exact blockDiag_disj_zero (block_disjoint hk' hk hne.symm) _
    · rw [yJ_frameProj hCM hJ hW]
      exact blockDiag_disj_zero (block_disjoint hk' hk hne.symm) _

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Comm
