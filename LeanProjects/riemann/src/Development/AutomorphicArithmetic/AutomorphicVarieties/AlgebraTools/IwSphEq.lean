import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSimpleOrbit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwPermMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwLenStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkTrace
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwBruhatKO
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwPermCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkNorm
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools GlobalTheory.PRep

private theorem hk_fixed {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) {I K : Subgroup G} (h : I ≤ K) (hI : HeckePair I) {x : G} (hx : x ∈ K)
    (v : fixd ρ I) (hv : (v : M) ∈ fixd ρ K) :
    hk ρ I x v = (((MulAction.orbit I (x : G ⧸ I)).ncard : ℕ) : A) • v := by
  have hF : (MulAction.orbit I (x : G ⧸ I)).Finite := hI x
  ext
  change (hk2 ρ I I x v : M) = _
  rw [(hkApply A G M ρ I I x hF).1 v, dc,
    finsum_set_coe_eq_finsum_mem (f := fun q : G ⧸ I => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ hF,
    LinearMap.sum_apply, Finset.sum_congr rfl (g := fun _ => (v : M))]
  · rw [Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hF, Submodule.coe_smul, Nat.cast_smul_eq_nsmul]
  · intro q hq
    rw [Set.Finite.mem_toFinset] at hq
    obtain ⟨a, ha⟩ := hq
    have ha' : (((a : G) * x : G) : G ⧸ I) = (q.out : G) := by
      rw [QuotientGroup.out_eq']
      exact ha
    have h1 := mul_mem (mul_mem (h a.2) hx) (h (QuotientGroup.eq.1 ha'))
    rw [mul_inv_cancel_left] at h1
    exact hv _ h1

private theorem sum_ncard {G : Type} [Group G] {I K : Subgroup G} (h : I ≤ K) (hI : HeckePair I) {ι : Type}
    [Fintype ι] (w : ι → G) (hw : ∀ i, w i ∈ K) (hu : ∀ g ∈ K, ∃! i, ∃ a ∈ I, ∃ b ∈ I, g = a * w i * b) :
    ∑ i, (MulAction.orbit I (w i : G ⧸ I)).ncard = I.relIndex K := by
  obtain ⟨-, h1, h2⟩ := hkTrace ℤ G ℤ (Representation.trivial ℤ G ℤ) I K h ι w hI hw hu
  let v : fixd (Representation.trivial ℤ G ℤ) K := ⟨1, fun _ _ => rfl⟩
  have h3 := LinearMap.congr_fun h1 (inc _ h v)
  rw [LinearMap.comp_apply, h2, LinearMap.sum_apply,
    Finset.sum_congr rfl fun i _ => hk_fixed _ h hI (hw i) (inc _ h v) v.2, ← Finset.sum_smul, map_smul] at h3
  have h4 : (∑ i, (((MulAction.orbit I (w i : G ⧸ I)).ncard : ℕ) : ℤ)) * 1 = (I.relIndex K : ℤ) * 1 :=
    congrArg Subtype.val h3
  rw [mul_one, mul_one] at h4
  exact_mod_cast h4

private theorem invLen_one (n : ℕ) : invLen (1 : Equiv.Perm (Fin n)) = 0 := by
  rw [invLen, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun p _ h => lt_asymm h.1 h.2

theorem UpperTheory.V.AlgebraTools.sphEq :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M), IsSMulRegular M ((iwC k n ⊤).relIndex (KO k (Fin n)) : A) → ∀ v : fixd ρ (iwC k n ⊤), (v : M) ∈ fixd ρ (KO k (Fin n)) ↔ ∀ i j : Fin n, (j : ℕ) = i + 1 → hk ρ (iwC k n ⊤) (pm k n (Equiv.swap i j)) v = (resCard k : A) • v := by
  intro k _ _ _ _ n A M _ _ _ ρ hreg v
  have hI := (heckePairIwC k n ⊤).1
  have he : iwC k n ⊤ = iwahori k (Fin n) := (memIwC k n ⊤).2.1
  have hle : iwC k n ⊤ ≤ KO k (Fin n) := he ▸ iwahori_le_KO k (Fin n)
  obtain ⟨hw, hu⟩ := bruhatKO k n
  rw [← he] at hu
  constructor
  · intro hv i j hij
    have h2 := ((lenStep n 1).1 i j hij).1 (by
      show i < j
      rw [Fin.lt_def]; omega)
    rw [mul_one, invLen_one] at h2
    rw [hk_fixed ρ hle hI (hw _) v hv, permCard, h2, zero_add, pow_one]
  · intro hs
    have key : ∀ (m : ℕ) (w : Equiv.Perm (Fin n)), invLen w = m →
        hk ρ (iwC k n ⊤) (pm k n w) v = ((resCard k : A) ^ m) • v := by
      intro m
      induction m with
      | zero =>
        intro w hm
        rw [(lenStep n w).2.1 hm, map_one, (hkNorm A _ M ρ _ 1 hI (one_mem _)).2.1, pow_zero, one_smul]
        rfl
      | succ m ih =>
        intro w hm
        have hw1 : w ≠ 1 := by
          rintro rfl
          rw [invLen_one] at hm
          omega
        obtain ⟨i, j, hij, hlt⟩ := (lenStep n w).2.2 hw1
        have hl := ((lenStep n w).1 i j hij).2 hlt
        have hp := permMul k n ⊤ A M ρ (Equiv.swap i j * w) i j hij (by simpa using hlt)
        rw [Equiv.swap_mul_self_mul] at hp
        rw [← hp, Module.End.mul_apply, ih _ (by omega), map_smul, hs i j hij, smul_smul, pow_succ]
    have h1 := LinearMap.congr_fun (hkTrace A _ M ρ _ _ hle _ (fun w => pm k n w) hI hw hu).2.1 v
    have h2 := sum_ncard hle hI (fun w => pm k n w) hw hu
    simp only [permCard] at h2
    rw [LinearMap.sum_apply, Finset.sum_congr rfl fun w _ => key _ w rfl, ← Finset.sum_smul] at h1
    have h3 : ((iwC k n ⊤).relIndex (KO k (Fin n)) : A) • (v : M) = (trc ρ (KO k (Fin n)) (iwC k n ⊤) v : M) := by
      rw [← h2, Nat.cast_sum]
      simp only [Nat.cast_pow]
      exact congrArg Subtype.val h1
    intro g hg
    apply hreg
    show _ • ρ g v = _ • (v : M)
    rw [← map_smul, h3]
    exact (trc ρ (KO k (Fin n)) (iwC k n ⊤) v).2 g hg
