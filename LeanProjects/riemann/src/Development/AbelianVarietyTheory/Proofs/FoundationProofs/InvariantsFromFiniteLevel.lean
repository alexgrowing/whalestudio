import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralTraceEqZetaSubOneTopStatement

open GlobalTheory.K5

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem charZero_of_tower (T : Tower p Ω) : CharZero Ω := by
  have hpp : p.Prime := Fact.out
  have hp : (p : Ω) ≠ 0 := by
    intro h0
    haveI : CharP Ω p := (CharP.charP_iff_prime_eq_zero hpp).mpr h0
    have hz := T.prim 1
    rw [pow_one] at hz
    have h1 : (T.ζ 1 - 1) ^ p = 0 := by rw [sub_pow_char, one_pow, hz.pow_eq_one, sub_self]
    have h2 : T.ζ 1 = 1 := sub_eq_zero.mp (pow_eq_zero_iff hpp.ne_zero |>.mp h1)
    rw [h2] at hz
    exact hpp.one_lt.ne' (hz.eq_orderOf.trans orderOf_one)
  let f : ℤ_[p] →+* Ω :=
    (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp (algebraMap ℤ_[p] (Lau p)))
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra hn0
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hpp.one_lt.ne'
  have hu : IsUnit (((m : ℤ) : ℤ_[p])) := by
    refine PadicInt.isUnit_iff.mpr (le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hm ?_))
    exact Int.natCast_dvd_natCast.mp ((PadicInt.norm_int_lt_one_iff_dvd _).mp h)
  have hmu : IsUnit (m : Ω) := by
    have := hu.map f
    simpa using this
  push_cast at hn
  rcases mul_eq_zero.mp hn with h | h
  · exact hp (pow_eq_zero_iff' |>.mp h).1
  · exact hmu.ne_zero h

end GlobalTheory.K5.FinLevel

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zeta_eq_pow (T : Tower p Ω) (i d : ℕ) : T.ζ i = T.ζ (i + d) ^ (p ^ d) := by
  induction d with
  | zero => simp
  | succ d ih => rw [ih, ← T.ζpow (i + d), ← pow_mul, ← pow_succ', add_assoc]

theorem qq_eq_pow (T : Tower p Ω) (i d : ℕ) : T.qq i = T.qq (i + d) ^ (p ^ d) := by
  induction d with
  | zero => simp
  | succ d ih => rw [ih, ← T.qpow (i + d), ← pow_mul, ← pow_succ', add_assoc]

def gens (T : Tower p Ω) (n : ℕ) : Set Ω :=
  Set.range (algebraMap (O0 p) Ω) ∪ T.ζ '' Set.Iic n ∪ T.qq '' Set.Iic n

theorem gens_mono (T : Tower p Ω) {m n : ℕ} (h : m ≤ n) : gens T m ⊆ gens T n := by
  unfold gens
  gcongr <;> exact Set.Iic_subset_Iic.mpr h

theorem fixes_gens (T : Tower p Ω) (n : ℕ) (g : Gal p Ω) (hg : g ∈ Gn T n) :
    ∀ a ∈ gens T n, g a = a := by
  have hz : g (T.ζ n) = T.ζ n := (Subgroup.mem_inf.mp hg).1
  have hq : g (T.qq n) = T.qq n := (Subgroup.mem_inf.mp hg).2
  rintro a ((⟨r, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · exact g.commutes r
  · have hi' : i + (n - i) = n := Nat.add_sub_cancel' hi
    rw [zeta_eq_pow T i (n - i), hi', map_pow, hz]
  · have hi' : i + (n - i) = n := Nat.add_sub_cancel' hi
    rw [qq_eq_pow T i (n - i), hi', map_pow, hq]

end GlobalTheory.K5.FinLevel

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem exists_level_of_fixed (hClo : IsClo p Ω) (T : Tower p Ω) (y : Ω)
    (hy : ∀ h ∈ ⨅ n, Gn T n, h y = y) : ∃ n, ∀ g ∈ Gn T n, g y = y := by
  haveI := charZero_of_tower T
  let L : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (⋃ n, gens T n)
  have hmemL : ∀ a ∈ ⋃ n, gens T n, a ∈ L := fun a ha => IntermediateField.subset_adjoin ℚ _ ha
  have hO : ∀ r : O0 p, algebraMap (O0 p) Ω r ∈ L := fun r =>
    hmemL _ (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inl ⟨r, rfl⟩)⟩)
  let φ : O0 p →+* L := (algebraMap (O0 p) Ω).codRestrict L hO
  have hφ : ∀ r, algebraMap L Ω (φ r) = algebraMap (O0 p) Ω r := fun r => rfl
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply hClo.inj
    rw [← hφ a, ← hφ b, hab]
  haveI halg : Algebra.IsAlgebraic L Ω := by
    constructor
    intro z
    obtain ⟨P, hP0, hPz⟩ := hClo.alg.isAlgebraic z
    refine ⟨P.map φ, (Polynomial.map_ne_zero_iff hφinj).mpr hP0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def] at hPz
    convert hPz using 2
    exact RingHom.ext hφ
  haveI : IsAlgClosure L Ω := ⟨hClo.clo, halg⟩
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  have hyL : y ∈ L := by
    have : y ∈ Set.range (algebraMap L Ω) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro f
      let g : Gal p Ω := AlgEquiv.ofRingEquiv (f := f.toRingEquiv) (fun r => f.commutes (φ r))
      have hg : g ∈ ⨅ n, Gn T n := by
        refine Subgroup.mem_iInf.mpr fun n => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · show g (T.ζ n) = T.ζ n
          exact f.commutes ⟨T.ζ n, hmemL _ (Set.mem_iUnion.mpr ⟨n, Or.inl (Or.inr ⟨n, Set.mem_Iic.mpr le_rfl, rfl⟩)⟩)⟩
        · show g (T.qq n) = T.qq n
          exact f.commutes ⟨T.qq n, hmemL _ (Set.mem_iUnion.mpr ⟨n, Or.inr ⟨n, Set.mem_Iic.mpr le_rfl, rfl⟩⟩)⟩
      exact hy g hg
    obtain ⟨l, rfl⟩ := this
    exact l.2
  obtain ⟨S, hS, hyS⟩ := IntermediateField.exists_finset_of_mem_adjoin hyL
  have hex : ∀ t ∈ S, ∃ m, t ∈ gens T m := fun t ht => Set.mem_iUnion.mp (hS ht)
  choose! m hm using hex
  refine ⟨S.sup m, fun g hg => ?_⟩
  have hSN : (S : Set Ω) ⊆ gens T (S.sup m) := fun t ht =>
    gens_mono T (Finset.le_sup (f := m) ht) (hm t ht)
  have hyN : y ∈ IntermediateField.adjoin ℚ (gens T (S.sup m)) :=
    IntermediateField.adjoin.mono ℚ _ _ hSN hyS
  let gq : Ω ≃ₐ[ℚ] Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun q => by simp)
  have hle : Algebra.adjoin ℚ (gens T (S.sup m)) ≤ AlgHom.equalizer (gq : Ω →ₐ[ℚ] Ω) (AlgHom.id ℚ Ω) :=
    Algebra.adjoin_le fun a ha => fixes_gens T _ g hg a ha
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hyN
  have hr' : g r = r := hle hr
  have hs' : g s = s := hle hs
  rw [map_div₀, hr', hs']

end GlobalTheory.K5.FinLevel

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem sum_fixed (H : Subgroup (Gal p Ω)) (E : Finset (Gal p Ω)) (y₀ x : Ω)
    (hEH : ∀ g ∈ E, g ∈ H)
    (huniq : ∀ h ∈ H, ∃! g, g ∈ E ∧ h y₀ = g y₀ ∧ ∀ s ∈ ({x} : Finset Ω), h s = g s) :
    ∀ h ∈ H, h (∑ g ∈ E, g (y₀ * x)) = ∑ g ∈ E, g (y₀ * x) := by
  classical
  simp only [Finset.mem_singleton, forall_eq] at huniq
  let rep : Gal p Ω → Gal p Ω := fun a => if ha : a ∈ H then (huniq a ha).exists.choose else 1
  have hrep : ∀ a ∈ H, rep a ∈ E ∧ a y₀ = rep a y₀ ∧ a x = rep a x := by
    intro a ha
    simp only [rep, dif_pos ha]
    exact (huniq a ha).exists.choose_spec
  have hun : ∀ a ∈ H, ∀ g ∈ E, a y₀ = g y₀ → a x = g x → rep a = g := by
    intro a ha g hg h1 h2
    exact ((huniq a ha).unique (hrep a ha) ⟨hg, h1, h2⟩)
  intro h hh
  rw [map_sum]
  have hmem : ∀ g ∈ E, h * g ∈ H := fun g hg => H.mul_mem hh (hEH g hg)
  have hmem' : ∀ g ∈ E, h⁻¹ * g ∈ H := fun g hg => H.mul_mem (H.inv_mem hh) (hEH g hg)
  refine Finset.sum_bij' (fun g _ => rep (h * g)) (fun g _ => rep (h⁻¹ * g))
    (fun g hg => (hrep _ (hmem g hg)).1) (fun g hg => (hrep _ (hmem' g hg)).1) ?_ ?_ ?_
  · intro g hg
    obtain ⟨_, h1, h2⟩ := hrep _ (hmem g hg)
    refine hun _ (hmem' _ (hrep _ (hmem g hg)).1) g hg ?_ ?_
    · rw [AlgEquiv.mul_apply, ← h1, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  · intro g hg
    obtain ⟨_, h1, h2⟩ := hrep _ (hmem' g hg)
    refine hun _ (hmem _ (hrep _ (hmem' g hg)).1) g hg ?_ ?_
    · rw [AlgEquiv.mul_apply, ← h1, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  · intro g hg
    obtain ⟨_, h1, h2⟩ := hrep _ (hmem g hg)
    show (h * g) (y₀ * x) = _
    rw [map_mul, map_mul (rep (h * g)), h1, h2]

end GlobalTheory.K5.FinLevel
