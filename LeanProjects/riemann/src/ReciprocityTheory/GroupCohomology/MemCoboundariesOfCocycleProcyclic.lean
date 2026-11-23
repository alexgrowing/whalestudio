import ReciprocityTheory.GroupCohomology.ModelComparisonDegreeZeroBijective

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology Function

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def tr (M : TRep R G) (f : G × G → M.V) (s : G) : ℕ → M.V
  | 0 => f (1, 1)
  | j + 1 => tr M f s j - f (s ^ j, s)

theorem tr_key (M : TRep R G) (f : G × G → M.V) (hf : f ∈ Z2 M.rho) (s : G) (i j : ℕ) :
    f (s ^ i, s ^ j) = M.rho (s ^ i) (tr M f s j) - tr M f s (i + j) + tr M f s i := by
  have hc := hf.2
  induction j with
  | zero =>
    have e := hc (s ^ i) 1 1
    simp only [mul_one] at e
    rw [sub_add_cancel, sub_eq_zero] at e
    simp only [pow_zero, add_zero]
    rw [sub_add_cancel]
    exact e.symm
  | succ j ih =>
    have e := hc (s ^ i) (s ^ j) s
    rw [← pow_add, ← pow_succ, ih] at e
    have e2 : tr M f s (j + 1) = tr M f s j - f (s ^ j, s) := rfl
    have e3 : tr M f s (i + (j + 1)) = tr M f s (i + j) - f (s ^ (i + j), s) := rfl
    rw [e2, e3, map_sub, ← sub_eq_zero, ← e]
    abel

theorem tr_add (M : TRep R G) (f : G × G → M.V) (s : G) (j t : ℕ) :
    tr M f s (j + t) = tr M f s j - ∑ i ∈ Finset.range t, f (s ^ (j + i), s) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e : tr M f s (j + (t + 1)) = tr M f s (j + t) - f (s ^ (j + t), s) := rfl
    rw [e, ih, Finset.sum_range_succ]
    abel

end ProcyclicCohomology

end ReciprocityTheory.Coh

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology Function

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem mem_coboundaries_of_cocycle_procyclic [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (htor : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) (f : G × G → M.V) (hf : f ∈ Z2 M.rho) :
    f ∈ B2 M.rho := by
  obtain ⟨N, -, hNo, hconst, hfix⟩ := FiniteLevelCohomology.exists_open_normal M (n := 2)
    (fun v : Fin 2 → G => f (v 0, v 1))
    (hf.1.comp ((continuous_apply 0).prodMk (continuous_apply 1)))
  have hbi : ∀ g h w w', w ∈ N → w' ∈ N → f (g * w, h * w') = f (g, h) := by
    intro g h w w' hw hw'
    have := hconst ![g, h] ![w, w'] (fun i => by fin_cases i <;> simpa)
    simpa using this
  have hfixf : ∀ g h, ∀ a ∈ N, M.rho a (f (g, h)) = f (g, h) := by
    intro g h a ha
    simpa using hfix ![g, h] a ha
  set T := tr M f s
  set n := N.index
  have hsn : s ^ n ∈ N := by simpa using (zpow_mem_iff hc hs hNo (n : ℤ)).2 dvd_rfl

  set a := ∑ i ∈ Finset.range n, f (s ^ i, s)
  have hwin : ∀ j, ∑ i ∈ Finset.range n, f (s ^ (j + i), s) = a := by
    intro j
    induction j with
    | zero => simp [a]
    | succ j ih =>
      have h1 : ∑ i ∈ Finset.range (n + 1), f (s ^ (j + i), s) =
          ∑ i ∈ Finset.range n, f (s ^ (j + 1 + i), s) + f (s ^ (j + 0), s) := by
        rw [Finset.sum_range_succ']
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show j + (i + 1) = j + 1 + i by omega]
      have h2 := Finset.sum_range_succ (fun i => f (s ^ (j + i), s)) n
      have hp : f (s ^ (j + n), s) = f (s ^ (j + 0), s) := by
        rw [pow_add, add_zero]
        simpa using hbi (s ^ j) s (s ^ n) 1 hsn N.one_mem
      rw [← ih]
      rw [hp] at h2
      exact add_right_cancel (h1.symm.trans h2)
  have hTn : ∀ j t, T (j + n * t) = T j - t • a := by
    intro j t
    induction t with
    | zero => simp
    | succ t ih =>
      have htadd : ∀ j t, T (j + t) = T j - ∑ i ∈ Finset.range t, f (s ^ (j + i), s) :=
        tr_add M f s
      rw [Nat.mul_succ, ← add_assoc, htadd, ih, hwin, succ_nsmul]; abel
  obtain ⟨k, hk0, hka⟩ := htor a
  have hn0 : 0 < n := index_pos hc hNo
  obtain ⟨W0, hW0o, hW0i⟩ := hidx (n * k) (Nat.mul_pos hn0 hk0)
  set W := N ⊓ W0
  have hWo : IsOpen (W : Set G) := hNo.inter hW0o
  have hWN : W ≤ N := inf_le_left
  have hdvd : n * k ∣ W.index := hW0i ▸ Subgroup.index_dvd_of_le inf_le_right
  have hper : ∀ j, T (j + W.index) = T j := by
    obtain ⟨t, ht⟩ := hdvd
    intro j; rw [ht]
    refine per_mul _ _ (fun j => ?_) j t
    rw [hTn, hka, sub_zero]
  have hfixT : ∀ w ∈ N, ∀ j, M.rho w (T j) = T j := by
    intro w hw j
    induction j with
    | zero => exact hfixf 1 1 w hw
    | succ j ih =>
      show M.rho w (T j - f (s ^ j, s)) = T j - f (s ^ j, s)
      rw [map_sub, ih, hfixf _ _ w hw]
  have hex := exists_pow hc hs hWo
  refine ⟨desc W hex T, desc_continuous hc hs hWo hex T hper, ?_⟩
  funext ⟨g, h⟩
  have hg := Classical.choose_spec (hex g)
  have hh := Classical.choose_spec (hex h)
  set i := Classical.choose (hex g)
  set j := Classical.choose (hex h)
  have hgh : (g * h)⁻¹ * s ^ (i + j) ∈ W := by
    have e : (g * h)⁻¹ * s ^ (i + j) = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by
      calc (g * h)⁻¹ * s ^ (i + j) = h⁻¹ * (g⁻¹ * s ^ i) * s ^ j := by
            rw [mul_inv_rev, pow_add]; group
        _ = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by rw [hc h⁻¹ (g⁻¹ * s ^ i), mul_assoc]
    rw [e]; exact W.mul_mem hg hh
  have e1 : desc W hex T (g * h) = T (i + j) := desc_eq hc hs hWo hex _ hper hgh
  have e2 : desc W hex T g = T i := rfl
  have e3 : desc W hex T h = T j := rfl
  have hgeq : g = s ^ i * (g⁻¹ * s ^ i)⁻¹ := by group
  have hheq : h = s ^ j * (h⁻¹ * s ^ j)⁻¹ := by group
  rw [d1_apply, e1, e2, e3]
  have hr : M.rho g (T j) = M.rho (s ^ i) (T j) := by
    conv_lhs => rw [hgeq, map_mul, Module.End.mul_apply]
    rw [hfixT _ (hWN (W.inv_mem hg))]
  have hfv : f (g, h) = f (s ^ i, s ^ j) := by
    conv_lhs => rw [hgeq, hheq]
    exact hbi _ _ _ _ (hWN (W.inv_mem hg)) (hWN (W.inv_mem hh))
  rw [hr, hfv, tr_key M f hf s i j]

theorem subsingleton_H2_of_procyclic_of_torsion [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (htor : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) : Subsingleton (H2 M.rho) := by
  have hz : ∀ z : H2 M.rho, z = 0 := by
    intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact (Submodule.Quotient.mk_eq_zero _).mpr (mem_coboundaries_of_cocycle_procyclic M hc hs hidx htor z.1 z.2)
  exact ⟨fun x y => by rw [hz x, hz y]⟩

end ProcyclicCohomology

end ReciprocityTheory.Coh
