import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.TorsStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.Descend
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.PhiZSeq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCountAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.BockAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.FibCount

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

private theorem UpperTheory.V.ZK.rankCount_mod (hR : RankCount) (H B : Type) [AddCommGroup H] [inst : Module ℤ H]
    [AddCommGroup B] (q r : ℕ) (hq : 0 < q) (hB : ∀ b : B, q • b = 0) (hH : Finite (AddCommGroup.torsion H)) (X : Set H)
    (hX : Module.rank ℤ (Submodule.span ℤ X) ≤ r) (f : H →+ B) (S : Finset B)
    (hS : ∀ s ∈ S, ∃ x ∈ X, ∃ u : ℤ, s = f (SMul.smul (self := (AddCommGroup.toIntModule H).toSMul) u x)) :
    S.card ≤ q ^ r * Nat.card (AddCommGroup.torsion H) := by
  obtain rfl : inst = AddCommGroup.toIntModule H := Subsingleton.elim _ _
  refine hR H B q r hq hB hH _ hX f S fun s hs => ?_
  obtain ⟨x, hx, u, e⟩ := hS s hs
  exact ⟨u • x, Submodule.smul_mem _ u (Submodule.subset_span hx), e⟩

private theorem UpperTheory.V.ZK.selmer_upper_bound_of_inputs (hS : TorsStab) (hD : Descend) (hZ : ZVal) (hR : RankCount) (hB : Bock)
    (hF : FibCount) : UpperTheory.V.ZK.SUpperOf := by
  intro hC hO L _ _ hL k hk hr l ν hl B _ _ Φ hΦ S hSm
  classical
  have hl0 : 0 < l := hl.out.pos
  have hq : 0 < l ^ ν := pow_pos hl0 ν
  have hqB : ∀ b : B, l ^ ν • b = 0 := fun b => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ ν)), ZMod.natCast_self, zero_smul]
  obtain ⟨φ, hφ, hφΦ⟩ := hD (𝓞 L) (l ^ ν) k B Φ hΦ
  choose! nn hnn using hSm
  obtain ⟨n, hn0, hnS⟩ : ∃ n, 2 * (k + 1) + 4 ≤ n ∧ ∀ s ∈ S, nn s ≤ n :=
    ⟨max (2 * (k + 1) + 4) (S.sup nn), le_max_left _ _, fun s hs => le_max_of_le_right (Finset.le_sup hs)⟩
  obtain ⟨β, hβ⟩ := hB (l ^ ν) hq (GL (Fin n) (𝓞 L)) k
  obtain ⟨hfin, hcard⟩ := hS L hL k (2 * (k + 1) + 4) n (by omega) hn0
  have hlev : ∀ t, n ≤ lev l n t := fun t => by
    induction t with
    | zero => exact le_rfl
    | succ t ih => exact ih.trans (Nat.le_mul_of_pos_left _ hl0)
  obtain ⟨hfin', hcard'⟩ := hS L hL (k + 1) (2 * (k + 1) + 4) (lev l n k) le_rfl (hn0.trans (hlev k))
  obtain ⟨u, hu⟩ := hZ (𝓞 L) B (k + 1) l ν hl0 hqB φ hφ n k
  let g : LinearMap.ker (bd (ZMod (l ^ ν)) (GL (Fin n) (𝓞 L)) k) →+ B :=
    (nsmulAddMonoidHom (l ^ k)).comp
      ((Φ n).toAddMonoidHom.comp (LinearMap.ker (bd (ZMod (l ^ ν)) (GL (Fin n) (𝓞 L)) k)).subtype.toAddMonoidHom)
  have hg : ∀ y, g y = l ^ k • Φ n y.1 := fun y => rfl
  have key := hF _ _ B β g ((l ^ ν) ^ InfinitePlace.nrComplexPlaces L * tc L (2 * (k + 1) + 4) (k + 1)) ?_ S ?_
  · rw [hcard] at key
    exact key
  · intro T hT
    rw [← hcard']
    refine rankCount_mod hR _ B (l ^ ν) _ hq hqB hfin' _ (hO L hL k hk hr l hl0 n hn0) (φ (lev l n k)) T fun s hs => ?_
    obtain ⟨y, hy, rfl⟩ := hT s hs
    obtain ⟨z, hz, hzy⟩ := hβ y hy
    obtain ⟨x, hx⟩ := hφΦ n z hz
    refine ⟨zSeq (𝓞 L) hl0 x k, ⟨x, rfl⟩, u, ?_⟩
    rw [hg, ← hzy, ← hx, hu]
    rfl
  · intro s hs
    obtain ⟨y, hy, e⟩ := hnn s hs
    refine ⟨⟨cm _ (stab (𝓞 L) (nn s) n (hnS s hs)) (k + 1) y, ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, (hC _).2.1, show bd _ _ k y = 0 from hy, map_zero]
    · rw [hg, hΦ.stab _ _ _ _ hy]
      exact e

theorem UpperTheory.V.ZK.sUpperOf :
    UpperTheory.V.ZK.SUpperOf :=
  selmer_upper_bound_of_inputs torsStab descend zVal rankCount bock fibCount
