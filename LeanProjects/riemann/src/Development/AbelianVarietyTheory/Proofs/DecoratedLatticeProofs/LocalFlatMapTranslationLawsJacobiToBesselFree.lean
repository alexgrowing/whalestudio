import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LocMod

namespace GlobalTheory.LocMod.TransLaw

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

def colMx {T : HSp D} {ρ : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (FT : Frame k T.rank Y) (r : Y) (i : Fin ρ)
    (b : k) : Mx D T.rank ρ :=
  Matrix.of fun row col => if col = i then p.ι (b * FT.β row r) else 0

def rowMx {ρ m : ℕ} (l : Fin ρ) (v : Fin m → k) : Mx D ρ m :=
  Matrix.of fun row col => if row = l then p.ι (v col) else 0

def lastMat {T T₀ : HSp D} {σ : ℕ} (d : HypDec T T₀ σ) (z : Fin T₀.rank → D.host.E) :
    Matrix (Fin T.rank) (Fin (σ + 1)) D.host.E :=
  Matrix.of fun row => Fin.snoc (d.e row) ((d.i₀ *ᵥ z) row)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def pairVal {T : HSp D} {ρ : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (FT : Frame k T.rank Y)
    (X : Matrix (Fin T.rank) (Fin ρ) D.host.E) (r : Y) (i : Fin ρ) : k :=
  ∑ c, (Xᴴ * T.gram).map p.pr i c * FT.β c r

theorem xLast_eq_rat {T T₀ : HSp D} {σ : ℕ} (d : HypDec T T₀ σ) (z : Fin T₀.rank → D.host.E) :
    xLast d z = rat (lastMat d z) := by
  ext row i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [xLast, lastMat, rat, HypDec.j0, ratV, Matrix.mulVec, dotProduct, map_sum]
  · simp [xLast, lastMat, rat, HypDec.jX]

theorem e_mul_ι (x : k) : p.e * p.ι x = p.ι x := by
  have h := p.ι_π (p.ι x)
  rw [p.π_ι] at h
  exact h.symm

theorem ι_mul_incA (x : k) (b : D.host.E) : p.ι x * incA D b = p.ι (x * p.pr b) := by
  have h := p.ι_π (p.ι x * incA D b)
  rw [map_mul, p.π_ι, ← mul_assoc, e_mul_ι] at h
  rw [← h]; rfl

theorem incA_mul_ι (x : k) (b : D.host.E) : incA D b * p.ι x = p.ι (p.pr b * x) := by
  rw [mul_comm, ι_mul_incA, mul_comm]

theorem map_ι_mul_rat {a b c : Type} [Fintype b] (M : Matrix a b k) (N : Matrix b c D.host.E) :
    M.map p.ι * N.map (incA D) = (M * N.map p.pr).map p.ι := by
  ext i j
  simp [Matrix.mul_apply, ι_mul_incA, map_sum]

theorem rat_mul_map_ι {a b c : Type} [Fintype b] (N : Matrix a b D.host.E) (M : Matrix b c k) :
    N.map (incA D) * M.map p.ι = (N.map p.pr * M).map p.ι := by
  ext i j
  simp [Matrix.mul_apply, incA_mul_ι, map_sum]

theorem infPart_e : infPart D p.e = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, hα, -⟩, h3⟩ := p.split
  have h4 : p.e = p.e * (algebraMap (AF D.host.F) (AE D) ε) := by
    rw [← h3, mul_add, h1, h2, add_zero]
  have h5 : infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    subst hα
    change infPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E))
      ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    have h0 : fstA D.host.F (pairA D.host.F 0 α) = 0 := rfl
    rw [h0, TensorProduct.zero_tmul]
  rw [h4, map_mul, h5, mul_zero]

theorem infPart_ι (x : k) : infPart D (p.ι x) = 0 := by
  rw [← e_mul_ι, map_mul, infPart_e, zero_mul]

theorem mxAt_of_ι {m' n' : ℕ} (M : Mx D m' n') (hM : ∀ i j, ∃ x, M i j = p.ι x) :
    GlobalTheory.FinPl.MxAt (fun _ => True) M := by
  intro i j
  obtain ⟨x, hx⟩ := hM i j
  have hid : GlobalTheory.FinPl.idAt D (fun _ => True) = RingHom.ker (infPart D) := by
    unfold GlobalTheory.FinPl.idAt; simp
  rw [hid, RingHom.mem_ker, hx, infPart_ι]

theorem mxAt_colMx {T : HSp D} {ρ : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (FT : Frame k T.rank Y) (r : Y) (i : Fin ρ)
    (b : k) : GlobalTheory.FinPl.MxAt (fun _ => True) (colMx p FT r i b) :=
  mxAt_of_ι p _ fun row col => by
    by_cases h : col = i
    · exact ⟨_, if_pos h⟩
    · exact ⟨0, (if_neg h).trans (map_zero _).symm⟩

theorem mxAt_rowMx {ρ m : ℕ} (l : Fin ρ) (v : Fin m → k) : GlobalTheory.FinPl.MxAt (fun _ => True) (rowMx p l v) :=
  mxAt_of_ι p _ fun row col => by
    by_cases h : row = l
    · exact ⟨_, if_pos h⟩
    · exact ⟨0, (if_neg h).trans (map_zero _).symm⟩

theorem pr_ne_zero {a : D.host.E} (ha : a ≠ 0) : p.pr a ≠ 0 :=
  (_root_.map_ne_zero (p.π.comp (incA D))).2 ha

theorem up_single {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (r : Y) (q : Y') (a : k) (row : Fin T.rank) (col : Fin S.rank) :
    p.up FS FT (Matrix.single r q a) row col = p.ι (FT.β row r * a * FS.γ q col) := by
  simp only [Place.up, Matrix.map_apply]
  congr 1
  rw [Matrix.mul_apply, Finset.sum_eq_single q (fun b _ hb => by rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), Matrix.mul_single_apply_same]

theorem extY_colMx {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {Y : Type} [Fintype Y] [DecidableEq Y]
    (FT : Frame k T.rank Y) (r : Y) (i : Fin ρ) (b : k) (row : Fin T.rank) (col : Fin S.rank) :
    d.extY T (colMx p FT r i b) row col = p.ι (b * FT.β row r * p.pr (d.qY i col)) := by
  rw [HypDec.extY_apply, Matrix.mul_apply, Finset.sum_eq_single i (fun m _ hm => by rw [show colMx p FT r i b row m = 0 from if_neg hm, zero_mul]) (fun h => absurd (Finset.mem_univ _) h),
    ← ι_mul_incA]
  rw [show colMx p FT r i b row i = _ from if_pos rfl]
  rfl

theorem wittExtZero_inclusionX_adelicSingleRowMatrix {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec T T₀ σ) (l : Fin σ)
    (v : Fin S₀.rank → k) (row : Fin T.rank) (col : Fin S.rank) :
    d.ext0 T (d'.incX S₀ (rowMx p l v)) row col = p.ι (∑ m, p.pr (d'.e row l) * v m * p.pr (d.q0 m col)) := by
  rw [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.mul_apply, Finset.sum_eq_single l (fun m' _ hm => by rw [show rowMx p l v m' m = 0 from if_neg hm, mul_zero]) (fun h => absurd (Finset.mem_univ _) h), ← ι_mul_incA, ← incA_mul_ι]
  rw [show rowMx p l v l m = _ from if_pos rfl]
  rfl

theorem frame_row {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) (q : Y) (v : Fin N → k)
    (h : ∀ q', ∑ col, v col * F.β col q' = if q' = q then 1 else 0) (col : Fin N) : F.γ q col = v col := by
  have h1 : v ᵥ* F.β = Pi.single q 1 := funext fun q' => (h q').trans (Pi.single_apply q 1 q').symm
  have h2 : v = Pi.single q 1 ᵥ* F.γ := by rw [← h1, Matrix.vecMul_vecMul, F.βγ, Matrix.vecMul_one]
  rw [h2, Matrix.single_one_vecMul]
  rfl

theorem pr_mul {l m n : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E) (N : Matrix (Fin m) (Fin n) D.host.E) :
    (M * N).map p.pr = M.map p.pr * N.map p.pr :=
  Matrix.map_mul (f := p.π.comp (incA D))

theorem pr_zero : p.pr 0 = 0 := map_zero (p.π.comp (incA D))

theorem pr_sum_zero {l m n : ℕ} {M : Matrix (Fin l) (Fin m) D.host.E} {N : Matrix (Fin m) (Fin n) D.host.E}
    (h : M * N = 0) (i : Fin l) (j : Fin n) : ∑ c, p.pr (M i c) * p.pr (N c j) = 0 := by
  have := congrFun (congrFun (pr_mul p M N) i) j
  rw [h] at this
  exact this.symm.trans (map_zero (p.π.comp (incA D)))

theorem pr_sum_one {l m : ℕ} {M : Matrix (Fin l) (Fin m) D.host.E} {N : Matrix (Fin m) (Fin l) D.host.E}
    (h : M * N = 1) (i j : Fin l) : ∑ c, p.pr (M i c) * p.pr (N c j) = if i = j then 1 else 0 := by
  have := congrFun (congrFun (pr_mul p M N) i) j
  rw [h] at this
  refine this.symm.trans ?_
  change (p.π.comp (incA D)) ((1 : Matrix (Fin l) (Fin l) D.host.E) i j) = _
  rw [Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem gram_swap' (S : HSp D) {l m : ℕ} {M : Matrix (Fin S.rank) (Fin l) D.host.E} {N : Matrix (Fin S.rank) (Fin m) D.host.E}
    {Z : Matrix (Fin l) (Fin m) D.host.E} (h : Mᴴ * S.gram * N = Z) : Nᴴ * S.gram * M = Zᴴ := by
  rw [← h, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, Matrix.mul_assoc]

section Dec
variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem qY_i₀ : d.qY * d.i₀ = 0 := (gram_swap' S d.i₀e).trans conjTranspose_zero
theorem qY_e' : d.qY * d.e' = 1 := (gram_swap' S d.e'e).trans conjTranspose_one
theorem wittDecomposition_coreProj_mul_e_eq_zero : d.q0 * d.e = 0 := by rw [HypDec.q0, Matrix.mul_assoc, d.i₀e, Matrix.mul_zero]
theorem wittZeroProjection_mul_dualBasis_eq_zero : d.q0 * d.e' = 0 := by rw [HypDec.q0, Matrix.mul_assoc, d.i₀e', Matrix.mul_zero]
theorem wittDecomposition_coreProj_mul_core_eq_one : d.q0.map p.pr * d.i₀.map p.pr = 1 := by
  have h := congrArg (fun M : Mx D S₀.rank S₀.rank => M.map p.π) d.p0_j0
  simp only [Matrix.map_one p.π (map_zero _) (map_one _)] at h
  rw [← h]
  exact (Matrix.map_mul (f := p.π)).symm

end Dec

section Jac
variable {ρ : ℕ} {J : JacLev D ρ} {s hh : k} {n' : Type} [Fintype n'] [DecidableEq n'] {c : ℕ}
  {G₀ : Frame k J.W₀.rank n'} {FW : Frame k J.W.rank (n' ⊕ Fin c)}

theorem jac_cases (h : c = 2 * ρ) (j : Fin c) : (∃ i : Fin ρ, j.val = i.val) ∨ ∃ i : Fin ρ, j.val + i.val + 1 = 2 * ρ := by
  have := j.isLt
  rcases Nat.lt_or_ge j.val ρ with h1 | h1
  · exact Or.inl ⟨⟨j.val, h1⟩, rfl⟩
  · exact Or.inr ⟨⟨2 * ρ - 1 - j.val, by omega⟩, by simp only; omega⟩

theorem jac_γ_inr (h : p.IsJacFrame J s hh G₀ FW) (hs : s ≠ 0) (hhh : hh ≠ 0) (hξ : p.xi ≠ 0) (i : Fin ρ) (j : Fin c)
    (hij : j.val + i.val + 1 = 2 * ρ) (col : Fin J.W.rank) :
    FW.γ (Sum.inr j) col = (s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val))⁻¹ * p.pr (J.d.qY i col) := by
  refine frame_row FW _ (fun col => (s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val))⁻¹ * p.pr (J.d.qY i col)) ?_ col
  have hne : s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hs (div_ne_zero hhh hξ)) (pow_ne_zero _ (div_ne_zero (neg_ne_zero.2 one_ne_zero) hξ))
  rintro (a | j')
  · rw [if_neg Sum.inl_ne_inr]
    simp only [h.2.1, mul_assoc]
    rw [← Finset.mul_sum]
    have : ∑ col, p.pr (J.d.qY i col) * (J.d.i₀.map p.pr * G₀.β) col a =
        (J.d.qY.map p.pr * (J.d.i₀.map p.pr * G₀.β)) i a := rfl
    rw [this, ← Matrix.mul_assoc, ← pr_mul, qY_i₀, Matrix.map_zero _ (pr_zero p), Matrix.zero_mul,
      Matrix.zero_apply, mul_zero]
  · rcases jac_cases h.1 j' with ⟨i', hi'⟩ | ⟨i', hi'⟩
    · have := i.isLt
      have := i'.isLt
      rw [if_neg fun h => by have := Sum.inr_injective h; omega]
      simp only [h.2.2.1 i' j' hi', mul_mul_mul_comm _ (p.pr (J.d.qY i _))]
      rw [← Finset.mul_sum, pr_sum_zero p (show J.d.qY * J.d.e = 0 from J.d.ee), mul_zero]
    · simp only [h.2.2.2 i' j' hi', mul_mul_mul_comm _ (p.pr (J.d.qY i _))]
      rw [← Finset.mul_sum, pr_sum_one p (qY_e' J.d)]
      by_cases hi : i = i'
      · subst hi
        rw [if_pos rfl, if_pos (congrArg Sum.inr (Fin.ext (by omega))), mul_one, inv_mul_cancel₀ hne]
      · rw [if_neg hi, mul_zero, if_neg fun h => hi (Fin.ext (by have := Sum.inr_injective h; omega))]

theorem jac_γ_inl (h : p.IsJacFrame J s hh G₀ FW) (j : n') (col : Fin J.W.rank) :
    FW.γ (Sum.inl j) col = ∑ m, G₀.γ j m * p.pr (J.d.q0 m col) := by
  refine frame_row FW _ (fun col => (G₀.γ * J.d.q0.map p.pr) j col) ?_ col
  have key : ∀ (N : Matrix (Fin J.W.rank) (Fin ρ) D.host.E), J.d.q0 * N = 0 → ∀ (t : k) (i : Fin ρ),
      ∑ col, (G₀.γ * J.d.q0.map p.pr) j col * (t * p.pr (N col i)) = 0 := fun N hN t i => by
    have : ∑ col, (G₀.γ * J.d.q0.map p.pr) j col * p.pr (N col i) = (G₀.γ * J.d.q0.map p.pr * N.map p.pr) j i := rfl
    simp only [mul_left_comm _ t]
    rw [← Finset.mul_sum, this, Matrix.mul_assoc, ← pr_mul, hN, Matrix.map_zero _ (pr_zero p),
      Matrix.mul_zero, Matrix.zero_apply, mul_zero]
  rintro (a | j')
  · simp only [h.2.1]
    have : ∑ col, (G₀.γ * J.d.q0.map p.pr) j col * (J.d.i₀.map p.pr * G₀.β) col a =
        (G₀.γ * J.d.q0.map p.pr * (J.d.i₀.map p.pr * G₀.β)) j a := rfl
    rw [this, Matrix.mul_assoc, ← Matrix.mul_assoc (J.d.q0.map p.pr), wittDecomposition_coreProj_mul_core_eq_one, Matrix.one_mul, G₀.γβ, Matrix.one_apply]
    simp only [Sum.inl.injEq, eq_comm]
  · rw [if_neg Sum.inr_ne_inl]
    rcases jac_cases h.1 j' with ⟨i', hi'⟩ | ⟨i', hi'⟩
    · simp only [h.2.2.1 i' j' hi']
      exact key _ (wittDecomposition_coreProj_mul_e_eq_zero J.d) _ _
    · simp only [h.2.2.2 i' j' hi']
      exact key _ (wittZeroProjection_mul_dualBasis_eq_zero J.d) _ _

end Jac

section Pair
variable {T : HSp D} {ρ : ℕ} (X : Matrix (Fin T.rank) (Fin ρ) D.host.E) {Y : Type} [Fintype Y] [DecidableEq Y]
  (FT : Frame k T.rank Y) (r : Y) (i : Fin ρ) (b : k)

theorem gram_colMx (m m' : Fin ρ) : (adj (colMx p FT r i b) ⬝ (gA T ⬝ rat X)) m m' =
    if m = i then cA D (p.ι (b * pairVal p FT X r m')) else 0 := by
  rw [gA, ← rat_mul, Matrix.mul_apply]
  split_ifs with hm
  · subst hm
    rw [pairVal, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 : (Xᴴ * T.gram) m' c = star ((T.gram * X) c m') := by
      rw [← conjTranspose_apply, conjTranspose_mul, gram_conjTranspose]
    have h2 : adj (colMx p FT r m b) m c = cA D (p.ι (b * FT.β c r)) := congrArg (cA D) (if_pos rfl)
    rw [h2, Matrix.map_apply, h1, mul_comm (p.pr _), ← mul_assoc, ← ι_mul_incA, map_mul (cA D), GlobalTheory.DualPairCheck.cA_incA, star_star]
    rfl
  · refine Finset.sum_eq_zero fun c _ => ?_
    have h2 : adj (colMx p FT r i b) m c = 0 := (congrArg (cA D) (if_neg hm)).trans (map_zero _)
    rw [h2, zero_mul]

theorem pairS_colMx : pairS T (rat X) (colMx p FT r i b) = cA D (p.ι (b * pairVal p FT X r i)) := by
  change ∑ m, (adj (colMx p FT r i b) ⬝ (gA T ⬝ rat X)) m m = _
  rw [Finset.sum_eq_single i (fun m _ hm => (gram_colMx p X FT r i b m m).trans (if_neg hm)) (fun h => absurd (Finset.mem_univ _) h)]
  exact (gram_colMx p X FT r i b i i).trans (if_pos rfl)

theorem uInv_colMx (h : ∀ m : Fin ρ, m < i → pairVal p FT X r m = 0) :
    GlobalTheory.FinPl.UInv T (rat X) (colMx p FT r i b) := by
  intro u
  obtain ⟨hu0, hu1⟩ := (GlobalTheory.UniIndexPrime.mem_uniSub _).1 u.2
  rw [pairS_colMx]
  have h1 : pairS T (rat X ⬝ u.1.1) (colMx p FT r i b) =
      ∑ m, ∑ m', (adj (colMx p FT r i b) ⬝ (gA T ⬝ rat X)) m m' * u.1.1 m' m := by
    change (adj (colMx p FT r i b) ⬝ (gA T ⬝ (rat X ⬝ u.1.1))).trace = _
    rw [← Matrix.mul_assoc (gA T), ← Matrix.mul_assoc (adj _)]
    rfl
  refine h1.trans ?_
  rw [Finset.sum_eq_single i (fun m _ hm => Finset.sum_eq_zero fun m' _ => by rw [gram_colMx, if_neg hm, zero_mul]) (fun h => absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single i (fun m _ hm => ?_) (fun h => absurd (Finset.mem_univ _) h), hu1, mul_one, gram_colMx, if_pos rfl]
  rcases lt_or_gt_of_ne hm with hm | hm
  · rw [gram_colMx, if_pos rfl, h m hm, mul_zero, map_zero, map_zero, zero_mul]
  · rw [hu0 m i hm, mul_zero]

theorem psi_symplO_colMx {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (hχ : p.IsChar ψ ψk) {S S₀ : HSp D}
    (d : HypDec S S₀ ρ) : ψ (symplO S T (d.extX T (rat X)) (d.extY T (colMx p FT r i b))) =
      (ψk (-(b * pairVal p FT X r i)) : ℂ) := by
  have h4 : (2 : AF D.host.F) * algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num
  have h1 : symplO S T (d.extX T (rat X)) (d.extY T (colMx p FT r i b)) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS T (rat X) (colMx p FT r i b)) := by
    have h0 : algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T (d.extX T (rat X)) (d.extY T (colMx p FT r i b)) =
        algebraMap D.host.F (AF D.host.F) (1 / 2) *
          Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS T (rat X) (colMx p FT r i b)) :=
      d.symplOH_extX_extY T (rat X) (colMx p FT r i b)
    rw [← one_mul (symplO _ _ _ _), ← h4, mul_assoc, h0, ← mul_assoc, h4, one_mul]
  have h2 : ∀ w : k, cA D (incA D D.host.xi0 * p.ι (-w)) = incA D D.host.xi0 * cA D (p.ι w) := fun w => by
    rw [map_mul (cA D), GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg (incA D), map_neg p.ι,
      map_neg (cA D), neg_mul_neg]
  rw [hχ, h1, pairS_colMx, ← h2, GlobalTheory.DualPairCheck.trace_cA]
  rfl

end Pair

section Bes
variable {σ : ℕ} (B : BesLev D σ)

def zCol : Matrix (Fin B.V.rank) (Fin 1) D.host.E := B.d.i₀ * (B.o.iB * Matrix.of fun r (_ : Fin 1) => B.ζ r)

theorem zCol_apply (r : Fin B.V.rank) : zCol B r 0 = (B.d.i₀ *ᵥ vecB B.o B.ζ) r := rfl

theorem zCol_gram {m : ℕ} (N : Matrix (Fin B.V.rank) (Fin m) D.host.E) : (zCol B)ᴴ * B.V.gram * N =
    (Matrix.of fun r (_ : Fin 1) => B.ζ r)ᴴ * (B.o.iBᴴ * (B.d.i₀ᴴ * B.V.gram * N)) := by
  simp only [zCol, conjTranspose_mul, Matrix.mul_assoc]

theorem zCol_e : (zCol B)ᴴ * B.V.gram * B.d.e = 0 := by rw [zCol_gram, B.d.i₀e, Matrix.mul_zero, Matrix.mul_zero]

theorem zCol_e' : (zCol B)ᴴ * B.V.gram * B.d.e' = 0 := by rw [zCol_gram, B.d.i₀e', Matrix.mul_zero, Matrix.mul_zero]

theorem zCol_A : (zCol B)ᴴ * B.V.gram * (B.d.i₀ * B.o.iA) = 0 := by
  rw [zCol_gram, ← Matrix.mul_assoc _ B.d.i₀, B.d.iso, ← Matrix.mul_assoc B.o.iBᴴ, B.o.orth, Matrix.mul_zero]

theorem zCol_zCol : ((zCol B)ᴴ * B.V.gram * zCol B) 0 0 = star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ := by
  rw [zCol_gram, zCol, ← Matrix.mul_assoc _ B.d.i₀, B.d.iso, ← Matrix.mul_assoc B.o.iBᴴ, ← Matrix.mul_assoc _ B.o.iB,
    B.o.isoB]
  rfl

theorem qY_zCol : B.d.qY * zCol B = 0 := by rw [zCol, ← Matrix.mul_assoc, qY_i₀, Matrix.zero_mul]

theorem qY_A : B.d.qY * (B.d.i₀ * B.o.iA) = 0 := by rw [← Matrix.mul_assoc, qY_i₀, Matrix.zero_mul]

variable {B} {s : k} {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {FA : Frame k B.A.rank n}
  {FV : Frame k B.V.rank (n ⊕ Fin c)}

theorem pairVal_castSucc (r : n ⊕ Fin c) (i : Fin σ) : pairVal p FV (lastMat B.d (vecB B.o B.ζ)) r i.castSucc =
    ∑ x, p.pr (B.d.qY i x) * FV.β x r := by
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Matrix.map_apply, HypDec.qY, Matrix.mul_apply, conjTranspose_apply, lastMat, Matrix.of_apply, Fin.snoc_castSucc]

theorem pairVal_last (r : n ⊕ Fin c) : pairVal p FV (lastMat B.d (vecB B.o B.ζ)) r (Fin.last σ) =
    ∑ x, p.pr (((zCol B)ᴴ * B.V.gram) 0 x) * FV.β x r := by
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Matrix.map_apply, Matrix.mul_apply, conjTranspose_apply, lastMat, Matrix.of_apply, Fin.snoc_last, zCol_apply]

theorem sum_core_zero {m : ℕ} {Q : Matrix (Fin m) (Fin B.V.rank) D.host.E} (hQ : Q * (B.d.i₀ * B.o.iA) = 0) (i : Fin m)
    (a : n) : ∑ x, p.pr (Q i x) * ((B.d.i₀ * B.o.iA).map p.pr * FA.β) x a = 0 := by
  change (Q.map p.pr * ((B.d.i₀ * B.o.iA).map p.pr * FA.β)) i a = 0
  rw [← Matrix.mul_assoc, ← pr_mul, hQ, Matrix.map_zero _ (pr_zero p), Matrix.zero_mul, Matrix.zero_apply]

theorem pairVal_mid (h : p.IsBesFrame B s FA FV) (l : Fin c) (hl : l.val = σ) :
    pairVal p FV (lastMat B.d (vecB B.o B.ζ)) (Sum.inr l) (Fin.last σ) = s * p.hz B := by
  rw [pairVal_last]
  simp only [h.2.2.2.1 l hl, ← zCol_apply, mul_left_comm _ s]
  rw [← Finset.mul_sum, Place.hz, ← zCol_zCol]
  exact congrArg (s * ·) (congrFun (congrFun (pr_mul p ((zCol B)ᴴ * B.V.gram) (zCol B)) 0) 0).symm

theorem pairVal_dual (h : p.IsBesFrame B s FA FV) (l : Fin c) (i : Fin (σ + 1)) (hl : σ < l.val)
    (hli : l.val + i.val = 2 * σ) : pairVal p FV (lastMat B.d (vecB B.o B.ζ)) (Sum.inr l) i =
      s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (σ - 1 - i.val) := by
  obtain ⟨i, rfl⟩ : ∃ i' : Fin σ, i = i'.castSucc := ⟨⟨i.val, by omega⟩, rfl⟩
  rw [pairVal_castSucc]
  simp only [h.2.2.2.2 i l hli, mul_left_comm (p.pr (B.d.qY i _))]
  rw [← Finset.mul_sum, pr_sum_one p (qY_e' B.d), if_pos rfl, mul_one]
  rfl

theorem pairVal_zero (h : p.IsBesFrame B s FA FV) (r : n ⊕ Fin c) (i : Fin (σ + 1))
    (hr : ∀ l, r = Sum.inr l → l.val + i.val ≠ 2 * σ) : pairVal p FV (lastMat B.d (vecB B.o B.ζ)) r i = 0 := by
  have hc := h.1
  rcases r with a | l
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [pairVal_last]
      simp only [h.2.1]
      exact sum_core_zero p (zCol_A B) _ _
    · rw [pairVal_castSucc]
      simp only [h.2.1]
      exact sum_core_zero p (qY_A B) _ _
  have hl := hr l rfl
  have hlc := l.isLt
  rcases lt_trichotomy l.val σ with h1 | h1 | h1
  · have hβ := h.2.2.1 ⟨l.val, h1⟩ l rfl
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [pairVal_last]
      simp only [hβ, mul_left_comm (p.pr (((zCol B)ᴴ * B.V.gram) 0 _))]
      rw [← Finset.mul_sum, pr_sum_zero p (zCol_e B), mul_zero]
    · rw [pairVal_castSucc]
      simp only [hβ, mul_left_comm (p.pr (B.d.qY i _))]
      rw [← Finset.mul_sum, pr_sum_zero p (show B.d.qY * B.d.e = 0 from B.d.ee), mul_zero]
  · have := i.isLt
    obtain ⟨i, rfl⟩ : ∃ i' : Fin σ, i = i'.castSucc := ⟨⟨i.val, by omega⟩, rfl⟩
    rw [pairVal_castSucc]
    simp only [h.2.2.2.1 l h1, ← zCol_apply, mul_left_comm _ s]
    rw [← Finset.mul_sum, pr_sum_zero p (qY_zCol B), mul_zero]
  · have hβ := h.2.2.2.2 ⟨2 * σ - l.val, by omega⟩ l (by simp only; omega)
    revert hl
    refine Fin.lastCases (fun _ => ?_) (fun i hl => ?_) i
    · rw [pairVal_last]
      simp only [hβ, mul_left_comm (p.pr (((zCol B)ᴴ * B.V.gram) 0 _))]
      rw [← Finset.mul_sum, pr_sum_zero p (zCol_e' B), mul_zero]
    · rw [pairVal_castSucc]
      simp only [hβ, mul_left_comm (p.pr (B.d.qY i _))]
      rw [← Finset.mul_sum, pr_sum_one p (qY_e' B.d), if_neg, mul_zero]
      intro hi
      have := congrArg Fin.val hi
      simp only [Fin.val_castSucc] at this hl
      omega

end Bes

theorem scale_ratio {k : Type} [Field k] (a s ξ z t : k) (hs : s ≠ 0) (hξ : ξ ≠ 0) (hz : z ≠ 0) (ht : t ≠ 0) :
    -(a * (s * (-ξ ^ 2 * z / ξ) * (t * (-1 / ξ)))⁻¹ * (s * ξ * (-z / ξ) * t)) = a := by
  have h : s * (-ξ ^ 2 * z / ξ) * (t * (-1 / ξ)) = s * z * t := by field_simp
  have h' : s * ξ * (-z / ξ) * t = -(s * z * t) := by field_simp
  rw [h, h', mul_neg, neg_neg, mul_assoc, inv_mul_cancel₀ (mul_ne_zero (mul_ne_zero hs hz) ht), mul_one]

end GlobalTheory.LocMod.TransLaw

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

theorem GlobalTheory.LocMod.flatFB_trans_free : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (σ + 1) (r, q) → (∀ i, q = Sum.inr i → σ < i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → flatFB st (Tm Φ') = (ψk (ch (Matrix.single r q a)) : ℂ) • flatFB st (Tm Φ) := by
  intro D hFL _ k _ _ _ _ _ _ p ψ ψk hχ σ J B st s hs n n' _ _ _ _ c G₀ FW FA F₀ FV hJF _ hBF Tm hTm r q hfree hq a Φ Φ' hΦ
  have hL := ((hFL ψ (fun _ => True)).2 σ J B st).Heisenberg₂
  have hc : c = 2 * σ + 1 := hBF.1
  rw [hTm.trans _ Φ Φ' hΦ]
  rcases q with j | j
  · rcases r with r | l
    · exact hfree.elim
    have hl : l.val < σ := by have : l.val + 1 < σ + 1 := hfree; omega
    have hup : p.up FW FV (Matrix.single (Sum.inr l) (Sum.inl j) a) = J.d.ext0 B.V (B.d.incX J.W₀
        (TransLaw.rowMx p ⟨l.val, hl⟩ fun m => s * p.xi * p.xi ^ (σ - l.val) * a * G₀.γ j m)) := by
      ext row col
      rw [TransLaw.up_single, hBF.2.2.1 ⟨l.val, hl⟩ l rfl, TransLaw.jac_γ_inl p hJF,
        TransLaw.wittExtZero_inclusionX_adelicSingleRowMatrix]
      congr 1
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hup, hL.iso _ (hTm.theta Φ) _ (TransLaw.mxAt_rowMx p _ _), map_zero]
    simp [symplO, hO, ch, Matrix.single]
  · have hj : σ < j.val := hq j rfl
    have hjc := j.isLt
    have hξ : p.xi ≠ 0 := TransLaw.pr_ne_zero p GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
    have hz : p.hz B ≠ 0 := TransLaw.pr_ne_zero p B.line.2
    have hhh : -p.xi ^ 2 * p.hz B ≠ 0 := mul_ne_zero (neg_ne_zero.2 (pow_ne_zero _ hξ)) hz
    obtain ⟨i, hi⟩ : ∃ i : Fin (σ + 1), j.val + i.val + 1 = 2 * (σ + 1) :=
      ⟨⟨2 * σ + 1 - j.val, by omega⟩, by simp only; omega⟩
    have hb1 := TransLaw.pairVal_mid p hBF
    have hb2 := TransLaw.pairVal_dual p hBF
    have hb3 := TransLaw.pairVal_zero p hBF
    have hup : p.up FW FV (Matrix.single r (Sum.inr j) a) = J.d.extY B.V (TransLaw.colMx p FV r i
        (a * (s * (-p.xi ^ 2 * p.hz B / p.xi) * (-1 / p.xi) ^ (σ + 1 - 1 - i.val))⁻¹)) := by
      ext row col
      rw [TransLaw.up_single, TransLaw.jac_γ_inr p hJF hs hhh hξ i j hi, TransLaw.extY_colMx]
      congr 1
      ring
    have hU : GlobalTheory.FinPl.UInv B.V (xLast B.d (vecB B.o B.ζ)) (TransLaw.colMx p FV r i
        (a * (s * (-p.xi ^ 2 * p.hz B / p.xi) * (-1 / p.xi) ^ (σ + 1 - 1 - i.val))⁻¹)) := by
      rw [TransLaw.xLast_eq_rat]
      refine TransLaw.uInv_colMx p _ FV r i _ fun m hm => hb3 r m ?_
      rintro l rfl
      have h1 : l.val < j.val := hfree
      have h2 : m.val < i.val := hm
      omega
    rw [hup, hL.dual _ (hTm.theta Φ) _ (TransLaw.mxAt_colMx p _ _ _ _) hU, TransLaw.xLast_eq_rat,
      TransLaw.psi_symplO_colMx p _ FV r i _ hχ]
    congr 3
    by_cases h : ∃ l, r = Sum.inr l ∧ l.val + i.val = 2 * σ
    · obtain ⟨l, rfl, hl⟩ := h
      have hjl : j = l.succ := Fin.ext (by simp only [Fin.val_succ]; omega)
      have hch : ch (Matrix.single (Sum.inr l : n ⊕ Fin c) (Sum.inr j : n' ⊕ Fin (c + 1)) a) = a := by
        subst hjl
        simp only [ch]
        rw [Finset.sum_eq_single l (fun b _ hb => by simp [Matrix.single, hb.symm]) (by simp)]
        simp
      rw [hch]
      have hi' := i.isLt
      rcases Nat.lt_or_ge σ l.val with hσ | hσ
      · rw [hb2 l i hσ hl, show σ + 1 - 1 - i.val = σ - 1 - i.val + 1 by omega, pow_succ (-1 / p.xi)]
        have : (-1 / p.xi) ^ (σ - 1 - i.val) ≠ 0 := pow_ne_zero _ (div_ne_zero (neg_ne_zero.2 one_ne_zero) hξ)
        exact TransLaw.scale_ratio a s p.xi (p.hz B) _ hs hξ hz this
      · have hil : i = Fin.last σ := Fin.ext (by simp only [Fin.val_last]; omega)
        subst hil
        rw [hb1 l (by simp only [Fin.val_last] at hl; omega)]
        simp only [Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, pow_zero]
        field_simp
    · rw [hb3 r i (fun l hl hl' => h ⟨l, hl, hl'⟩), mul_zero, neg_zero]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
      rintro ⟨h1, h2⟩
      have h3 : j = l.succ := Sum.inr_injective h2
      refine h ⟨l, h1, ?_⟩
      have : j.val = l.val + 1 := by rw [h3, Fin.val_succ]
      omega

end
