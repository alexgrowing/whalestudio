import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfValuationBound

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M

section Hom

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

def zLet : Fin (G.T.t + 1) → Fin (N + 1) :=
  Fin.lastCases (Fin.castSucc G.uPos) (fun i => M.finPos N (G.T.pos i))

def sLet : Fin (G.T.t + 1) → Fin (N + 1) :=
  Fin.lastCases (Fin.last N) (fun i => M.finPos N (G.T.pos i + 1))

def wL (a : Fin (N + 1)) : M.BVar N r G.T.t → ℕ
  | Sum.inl (a', _) => if a' = a then 1 else 0
  | Sum.inr (i, false) => if zLet G i = a then 1 else 0
  | Sum.inr (i, true) => if sLet G i = a then 1 else 0

def chDeg (LL : M.Letters N) (a : Fin (N + 1)) : ℕ := ∑ a0 : Fin N, if Fin.castSucc a0 = a then LL.deg a0 else 0

def dLvl (j : Fin G.T.t → ℕ) (jp : ℕ) (a : Fin (N + 1)) : ℕ :=
  (∑ i, j i • ((if M.finPos N (G.T.pos i) = a then 1 else 0) + (if M.finPos N (G.T.pos i + 1) = a then 1 else 0))) +
    jp • ((if Fin.castSucc G.uPos = a then 1 else 0) + (if Fin.last N = a then 1 else 0)) +
    (∑ i, G.T.z i • (if M.finPos N (G.T.pos i) = a then 1 else 0)) +
    G.zPlus • (if Fin.castSucc G.uPos = a then 1 else 0) + chDeg (G.lettersAt j jp) a +
    (if Fin.last N = a then G.B - jp else 0)

theorem zLet_castSucc (i : Fin G.T.t) : zLet G (Fin.castSucc i) = M.finPos N (G.T.pos i) := by
  simp [zLet]

theorem zLet_last : zLet G (Fin.last G.T.t) = Fin.castSucc G.uPos := by
  simp [zLet]

theorem sLet_castSucc (i : Fin G.T.t) : sLet G (Fin.castSucc i) = M.finPos N (G.T.pos i + 1) := by
  simp [sLet]

theorem sLet_last : sLet G (Fin.last G.T.t) = Fin.last N := by
  simp [sLet]

theorem hom_Ehat (a : Fin (N + 1)) (i : Fin G.T.t) :
    IsWeightedHomogeneous (wL (r := r) G a) (G.Ehat p (r := r) i)
      ((if M.finPos N (G.T.pos i) = a then 1 else 0) + (if M.finPos N (G.T.pos i + 1) = a then 1 else 0)) := by
  unfold M.BlockData.Ehat
  apply IsWeightedHomogeneous.add
  · convert (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalZ N r G.T.t (Fin.castSucc i))).mul
      (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalS N r G.T.t (Fin.castSucc i))) using 1
    simp [wL, M.scalZ, M.scalS, zLet_castSucc, sLet_castSucc]
  · apply IsWeightedHomogeneous.sum
    intro c _
    convert (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (Sum.inl (M.finPos N (G.T.pos i), c) : M.BVar N r G.T.t)).mul
      (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (Sum.inl (M.finPos N (G.T.pos i + 1), c) : M.BVar N r G.T.t)) using 1
    simp [wL]

theorem hom_Eplus (a : Fin (N + 1)) :
    IsWeightedHomogeneous (wL (r := r) G a) (G.Eplus p (r := r))
      ((if Fin.castSucc G.uPos = a then 1 else 0) + (if Fin.last N = a then 1 else 0)) := by
  unfold M.BlockData.Eplus
  apply IsWeightedHomogeneous.add
  · convert (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalZ N r G.T.t (Fin.last G.T.t))).mul
      (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalS N r G.T.t (Fin.last G.T.t))) using 1
    simp [wL, M.scalZ, M.scalS, zLet_last, sLet_last]
  · apply IsWeightedHomogeneous.sum
    intro c _
    convert (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (Sum.inl (Fin.castSucc G.uPos, c) : M.BVar N r G.T.t)).mul
      (isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.xiVar N r G.T.t c)) using 1
    simp [wL, M.xiVar]

theorem hom_chain (a : Fin (N + 1)) (LL : M.Letters N) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hy : y ∈ M.Pol p r LL) :
    IsWeightedHomogeneous (wL (r := r) G a) (rename (M.chainEmb N r G.T.t) y) (chDeg LL a) := by
  classical
  have hsupp : ∀ m ∈ y.support, M.MultiDeg LL m := fun m hm => hy hm
  rw [y.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [rename_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => add_smul _ _ _),
    Finsupp.sum_fintype _ _ (fun _ => by simp)]
  unfold chDeg
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← hsupp m hm i]
  simp only [M.chainEmb, wL]
  by_cases h : Fin.castSucc i = a <;> simp [h]

theorem hom_xi (a : Fin (N + 1)) (b : ℕ) (g : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hg : g ∈ M.XiPolZ p N r G.T.t b) :
    IsWeightedHomogeneous (wL (r := r) G a) g (if Fin.last N = a then b else 0) := by
  classical
  intro μ hμ
  obtain ⟨hv, hb⟩ := hg.1 (mem_support_iff.mpr hμ)
  have hw : ∀ v, μ v * wL (r := r) G a v = μ v * (if Fin.last N = a then 1 else 0) := by
    intro v
    by_cases h0 : μ v = 0
    · simp [h0]
    · obtain ⟨c, rfl⟩ := hv v (Finsupp.mem_support_iff.mpr h0)
      rfl
  have hsum : ∑ v, μ v = ∑ c, μ (M.xiVar N r G.T.t c) := by
    rw [← Finset.sum_image (s := Finset.univ) (g := M.xiVar N r G.T.t) (by intro c _ c' _ h; simpa [M.xiVar] using h)]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv'
    by_contra h0
    obtain ⟨c, rfl⟩ := hv v (Finsupp.mem_support_iff.mpr h0)
    exact hv' (Finset.mem_image_of_mem _ (Finset.mem_univ c))
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp only [smul_eq_mul, hw, ← Finset.sum_mul, hsum, hb]
  split_ifs <;> simp

theorem hom_gens (a : Fin (N + 1)) (j : Fin G.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hx : x ∈ G.gens p (r := r) j jp) : IsWeightedHomogeneous (wL (r := r) G a) x (dLvl G j jp a) := by
  obtain ⟨y, hy, g, hg, rfl⟩ := hx
  have hX : ∀ i, IsWeightedHomogeneous (wL (r := r) G a) (X (M.scalZ N r G.T.t (Fin.castSucc i)) : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
      (if M.finPos N (G.T.pos i) = a then 1 else 0) := by
    intro i
    convert isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalZ N r G.T.t (Fin.castSucc i)) using 1
    simp [wL, M.scalZ, zLet_castSucc]
  have hXP : IsWeightedHomogeneous (wL (r := r) G a) (X (M.scalZ N r G.T.t (Fin.last G.T.t)) : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
      (if Fin.castSucc G.uPos = a then 1 else 0) := by
    convert isWeightedHomogeneous_X ℚ_[p] (wL (r := r) G a) (M.scalZ N r G.T.t (Fin.last G.T.t)) using 1
    simp [wL, M.scalZ, zLet_last]
  unfold dLvl
  exact (((((IsWeightedHomogeneous.prod _ _ _ (fun i _ => (hom_Ehat p G a i).pow (j i))).mul
    ((hom_Eplus p G a).pow jp)).mul (IsWeightedHomogeneous.prod _ _ _ (fun i _ => (hX i).pow (G.T.z i)))).mul
    (hXP.pow G.zPlus)).mul (hom_chain p G a _ y hy.2.1)).mul (hom_xi p G a _ g hg)

theorem SSZ_support (z : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hz : z ∈ G.SSZ p (r := r)) :
    ∀ μ ∈ z.support, ∃ (j : Fin G.T.t → ℕ) (jp : ℕ), G.LevelOK j jp ∧
      ∀ a, Finsupp.weight (wL (r := r) G a) μ = dLvl G j jp a := by
  classical
  induction hz using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, hlev, hx⟩ := hx
    intro μ hμ
    exact ⟨j, jp, hlev, fun a => hom_gens p G a j jp x hx (mem_support_iff.mp hμ)⟩
  | zero => simp
  | add x y _ _ hx hy =>
    intro μ hμ
    rcases Finset.mem_union.mp (support_add hμ) with h | h
    · exact hx μ h
    · exact hy μ h
  | smul c x _ hx =>
    intro μ hμ
    exact hx μ (support_smul hμ)

end Hom

end Formalism.MainNotions.G.SymmetricFormBlocks

end
