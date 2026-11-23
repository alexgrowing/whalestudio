import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SmoothChange

section Loc

variable {Ω : Type} [Field Ω] [CharZero Ω]

theorem isLocalization_of_mem_iff (C L : Subalgebra ℚ Ω) (hCL : C ≤ L) (P : Ideal C) [P.IsPrime]
    (h : ∀ a : Ω, a ∈ L ↔ ∃ s : C, s ∉ P ∧ (s : Ω) * a ∈ C) :
    letI : Algebra C L := (Subalgebra.inclusion hCL).toRingHom.toAlgebra
    IsLocalization.AtPrime L P := by
  letI : Algebra C L := (Subalgebra.inclusion hCL).toRingHom.toAlgebra
  have hne : ∀ s : C, s ∉ P → (s : Ω) ≠ 0 := fun s hs h0 =>
    hs (by rw [show s = 0 from Subtype.ext h0]; exact P.zero_mem)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    have hs' : s ∉ P := hs
    have hinv : (s : Ω)⁻¹ ∈ L := (h _).2 ⟨s, hs', by rw [mul_inv_cancel₀ (hne s hs')]; exact C.one_mem⟩
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : L) (Subtype.ext ?_)
    exact mul_inv_cancel₀ (hne s hs')
  · intro z
    obtain ⟨s, hs, hsa⟩ := (h z).1 z.2
    refine ⟨(⟨_, hsa⟩, ⟨s, hs⟩), Subtype.ext ?_⟩
    exact mul_comm _ _
  · intro x y e
    refine ⟨1, ?_⟩
    have : x = y := Subtype.ext (congrArg (fun t : L => (t : Ω)) e)
    rw [this]

theorem formallySmooth_of_mem_iff (C L : Subalgebra ℚ Ω) (hCL : C ≤ L) (P : Ideal C) [P.IsPrime]
    (h : ∀ a : Ω, a ∈ L ↔ ∃ s : C, s ∉ P ∧ (s : Ω) * a ∈ C) [Algebra.FormallySmooth ℚ C] :
    Algebra.FormallySmooth ℚ L := by
  letI : Algebra C L := (Subalgebra.inclusion hCL).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ C L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsLocalization.AtPrime L P := isLocalization_of_mem_iff C L hCL P h
  haveI : Algebra.FormallySmooth C L := Algebra.FormallySmooth.of_isLocalization P.primeCompl
  exact Algebra.FormallySmooth.comp ℚ C L

theorem formallySmooth_atPrime_of_mem_iff (C L : Subalgebra ℚ Ω) (hCL : C ≤ L) (P : Ideal C) [P.IsPrime]
    (h : ∀ a : Ω, a ∈ L ↔ ∃ s : C, s ∉ P ∧ (s : Ω) * a ∈ C) [Algebra.FormallySmooth ℚ L] :
    Algebra.FormallySmooth ℚ (Localization.AtPrime P) := by
  letI : Algebra C L := (Subalgebra.inclusion hCL).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ C L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsLocalization.AtPrime L P := isLocalization_of_mem_iff C L hCL P h
  exact Algebra.FormallySmooth.of_equiv
    ((IsLocalization.algEquiv P.primeCompl L (Localization.AtPrime P)).restrictScalars ℚ)

end Loc

section Pts

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {κ : Type} {x : κ → Ω} {c : κ} {p : Cpt ξ}

theorem unitAt_mul {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem unitAt_inv {a : Ω} (ha : unitAt ξ p a) : unitAt ξ p a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem unitAt_of_mul {a b : Ω} (ha : unitAt ξ p a) (hab : unitAt ξ p (a * b)) : unitAt ξ p b := by
  have := unitAt_mul (unitAt_inv ha) hab
  rwa [inv_mul_cancel_left₀ ha.1] at this

theorem mem_chQ_of_mem_chZ {a : Ω} (ha : a ∈ chRing ℤ x c) : a ∈ chRing ℚ x c := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact Algebra.subset_adjoin ha
  | algebraMap n => simpa using intCast_mem (chRing ℚ x c) n
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem exists_nat_mul_mem {a : Ω} (ha : a ∈ chRing ℚ x c) :
    ∃ n : ℕ, 0 < n ∧ (n : Ω) * a ∈ chRing ℤ x c := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact ⟨1, one_pos, by simpa using Algebra.subset_adjoin ha⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_pos, ?_⟩
    have : (q.den : Ω) * algebraMap ℚ Ω q = (q.num : Ω) := by
      calc (q.den : Ω) * algebraMap ℚ Ω q = algebraMap ℚ Ω ((q.den : ℚ) * q) := by
            rw [map_mul, map_natCast]
        _ = algebraMap ℚ Ω (q.num : ℚ) := by rw [Rat.den_mul_eq_num]
        _ = (q.num : Ω) := map_intCast _ _
    rw [this]
    exact intCast_mem _ _
  | add a b _ _ ha hb =>
    obtain ⟨n, hn, hna⟩ := ha
    obtain ⟨m, hm, hmb⟩ := hb
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (a + b) = (m : Ω) * ((n : Ω) * a) + (n : Ω) * ((m : Ω) * b) := by
      push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem _ m) hna) (mul_mem (natCast_mem _ n) hmb)
  | mul a b _ _ ha hb =>
    obtain ⟨n, hn, hna⟩ := ha
    obtain ⟨m, hm, hmb⟩ := hb
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (a * b) = ((n : Ω) * a) * ((m : Ω) * b) := by
      push_cast; ring
    rw [this]
    exact mul_mem hna hmb

theorem chZ_mem_regAt (tie : CoordTie ℤ ξ x) (hc : InChart ξ x c p) {a : Ω} (ha : a ∈ chRing ℤ x c) :
    a ∈ regAt ξ p :=
  (tie.ring c hc.1 a).1 ha p hc

theorem chQ_mem_regAt (tie : CoordTie ℤ ξ x) (hc : InChart ξ x c p) (hp : p ∈ genFib ξ) {a : Ω}
    (ha : a ∈ chRing ℚ x c) : a ∈ regAt ξ p := by
  obtain ⟨n, hn, hna⟩ := exists_nat_mul_mem ha
  have h := mul_mem (hp n hn).2.2 (chZ_mem_regAt tie hc hna)
  rwa [inv_mul_cancel_left₀ (hp n hn).1] at h

theorem mem_regAt_iff (tie : CoordTie ℤ ξ x) (hc : InChart ξ x c p) (hp : p ∈ genFib ξ) (a : Ω) :
    a ∈ regAt ξ p ↔ ∃ s ∈ chRing ℚ x c, unitAt ξ p s ∧ s * a ∈ chRing ℚ x c := by
  constructor
  · intro ha
    obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x tie c p hc a).1 ha
    exact ⟨s, mem_chQ_of_mem_chZ hs, hu, mem_chQ_of_mem_chZ hsa⟩
  · rintro ⟨s, _, hu, hsa⟩
    have h := mul_mem hu.2.2 (chQ_mem_regAt tie hc hp hsa)
    rwa [inv_mul_cancel_left₀ hu.1] at h

theorem isLocalRing_regAt (gen : IsCptGen ξ) (p : Cpt ξ) : IsLocalRing (regAt ξ p) :=
  (RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun _ _ h => gen.inj p (congrArg Subtype.val h), (genMap ξ p).rangeRestrict_surjective⟩).isLocalRing

theorem exists_prime_of_point (tie : CoordTie ℤ ξ x) (hc : InChart ξ x c p) (hp : p ∈ genFib ξ) :
    ∃ P : Ideal (chRing ℚ x c), P.IsPrime ∧ ∀ s : chRing ℚ x c, s ∉ P ↔ unitAt ξ p (s : Ω) := by
  haveI := isLocalRing_regAt tie.gen p
  let f : chRing ℚ x c →+* regAt ξ p :=
    RingHom.codRestrict (algebraMap (chRing ℚ x c) Ω) (regAt ξ p) fun s => chQ_mem_regAt tie hc hp s.2
  refine ⟨Ideal.comap f (IsLocalRing.maximalIdeal _), inferInstance, fun s => ?_⟩
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  constructor
  · intro hu
    obtain ⟨t, ht⟩ := hu.exists_right_inv
    have ht' : (s : Ω) * (t : Ω) = 1 := congrArg (fun u : regAt ξ p => (u : Ω)) ht
    have h0 : (s : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one ht'
    refine ⟨h0, (f s).2, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right ht']
    exact t.2
  · rintro ⟨h0, _, h2⟩
    exact IsUnit.of_mul_eq_one (⟨_, h2⟩ : regAt ξ p) (Subtype.ext (mul_inv_cancel₀ h0))

theorem exists_point_of_prime (tie : CoordTie ℤ ξ x) (hc : x c ≠ 0) (P : Ideal (chRing ℚ x c)) [P.IsPrime] :
    ∃ p : Cpt ξ, InChart ξ x c p ∧ p ∈ genFib ξ ∧ ∀ s : chRing ℚ x c, s ∉ P ↔ unitAt ξ p (s : Ω) := by
  let inc : chRing ℤ x c →+* chRing ℚ x c :=
    RingHom.codRestrict (algebraMap (chRing ℤ x c) Ω) (chRing ℚ x c) fun s => mem_chQ_of_mem_chZ s.2
  obtain ⟨p, ⟨hpc, hpu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ κ x tie c hc (Ideal.comap inc P) inferInstance
  have hnP : ∀ n : ℕ, 0 < n → (n : chRing ℚ x c) ∉ P := by
    intro n hn hmem
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have h1 : (algebraMap ℚ (chRing ℚ x c) (n : ℚ)⁻¹) * (n : chRing ℚ x c) = 1 := by
      rw [← map_natCast (algebraMap ℚ (chRing ℚ x c)), ← map_mul, inv_mul_cancel₀ hn0, map_one]
    exact (inferInstance : P.IsPrime).ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ P.mul_mem_left _ hmem))
  have hg : p ∈ genFib ξ := by
    intro n hn
    have := (hpu (n : chRing ℤ x c)).1 (fun h => hnP n hn (by simpa [Ideal.mem_comap] using h))
    simpa using this
  refine ⟨p, hpc, hg, fun s => ?_⟩
  obtain ⟨n, hn, hr⟩ := exists_nat_mul_mem s.2
  let r : chRing ℤ x c := ⟨_, hr⟩
  have hr' : inc r = (n : chRing ℚ x c) * s := Subtype.ext (by simp [inc, r])
  have hrP : r ∉ Ideal.comap inc P ↔ s ∉ P := by
    rw [Ideal.mem_comap, hr', (inferInstance : P.IsPrime).mul_mem_iff_mem_or_mem]
    simp [hnP n hn]
  rw [← hrP, hpu r]
  exact ⟨fun h => unitAt_of_mul (hg n hn) h, fun h => unitAt_mul (hg n hn) h⟩

def regAlg (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (h : ∀ q : ℚ, algebraMap ℚ Ω q ∈ regAt ξ p) :
    Subalgebra ℚ Ω :=
  { (regAt ξ p).toSubsemiring with algebraMap_mem' := h }

end Pts

section Main

variable {Ω : Type} [Field Ω] [CharZero Ω] {X₁ X₂ : Scheme.{0}}

theorem exists_image_genFib {ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁} {ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂}
    {g : X₂ ⟶ X₁} (gen : IsCptGen ξ₂) (dom : Dominates ξ₂ ξ₁ g (RingHom.id Ω)) (p : Cpt ξ₂)
    (hp : p ∈ genFib ξ₂) : ∃ q : Cpt ξ₁, g p.1 = q.1 ∧ q ∈ genFib ξ₁ := by
  obtain ⟨h, -, hu⟩ := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates X₁ Ω ξ₁ X₂ Ω ξ₂ g (RingHom.id Ω) dom p
  exact ⟨⟨g p.1, h⟩, rfl, fun n hn => hu gen n (natCast_mem _ n) (hp n hn)⟩

theorem formallySmooth_atPrime {κ₁ κ₂ : Type} {x₁ : κ₁ → Ω} {x₂ : κ₂ → Ω}
    {ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁} {ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂} {g : X₂ ⟶ X₁}
    (tie₁ : CoordTie ℤ ξ₁ x₁) (tie₂ : CoordTie ℤ ξ₂ x₂) (dom : Dominates ξ₂ ξ₁ g (RingHom.id Ω))
    (sm : ∀ c, x₁ c ≠ 0 → Algebra.FormallySmooth ℚ (chRing ℚ x₁ c))
    (iso : ∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) {c : κ₂} (hc : x₂ c ≠ 0)
    (P : Ideal (chRing ℚ x₂ c)) [P.IsPrime] : Algebra.FormallySmooth ℚ (Localization.AtPrime P) := by
  obtain ⟨p, hpc, hpg, hpu⟩ := exists_point_of_prime tie₂ hc P
  obtain ⟨q, hq, hqg⟩ := exists_image_genFib tie₂.gen dom p hpg
  obtain ⟨c', hc'⟩ := tie₁.cover q
  have hreg : regAt ξ₂ p = regAt ξ₁ q := by simpa using (iso q hqg).2 p hq
  obtain ⟨P₁, hP₁, hu₁⟩ := exists_prime_of_point tie₁ hc' hqg
  let L : Subalgebra ℚ Ω := regAlg ξ₁ q fun r => chQ_mem_regAt tie₁ hc' hqg (Subalgebra.algebraMap_mem _ r)
  have hL : ∀ a, a ∈ L ↔ a ∈ regAt ξ₁ q := fun _ => Iff.rfl
  haveI := sm c' hc'.1
  haveI : Algebra.FormallySmooth ℚ L := by
    refine formallySmooth_of_mem_iff (chRing ℚ x₁ c') L (fun a ha => chQ_mem_regAt tie₁ hc' hqg ha) P₁ fun a => ?_
    rw [hL, mem_regAt_iff tie₁ hc' hqg]
    constructor
    · rintro ⟨s, hs, hu, hsa⟩
      exact ⟨⟨s, hs⟩, (hu₁ _).2 hu, hsa⟩
    · rintro ⟨s, hs, hsa⟩
      exact ⟨s, s.2, (hu₁ s).1 hs, hsa⟩
  refine formallySmooth_atPrime_of_mem_iff (chRing ℚ x₂ c) L
    (fun a ha => (hL a).2 (hreg ▸ chQ_mem_regAt tie₂ hpc hpg ha)) P fun a => ?_
  rw [hL, ← hreg, mem_regAt_iff tie₂ hpc hpg]
  constructor
  · rintro ⟨s, hs, hu, hsa⟩
    exact ⟨⟨s, hs⟩, (hpu _).2 hu, hsa⟩
  · rintro ⟨s, hs, hsa⟩
    exact ⟨s, s.2, (hpu s).1 hs, hsa⟩

theorem smooth_chRing {κ₁ κ₂ : Type} [Finite κ₂] {x₁ : κ₁ → Ω} {x₂ : κ₂ → Ω}
    {ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁} {ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂} {g : X₂ ⟶ X₁}
    (tie₁ : CoordTie ℤ ξ₁ x₁) (tie₂ : CoordTie ℤ ξ₂ x₂) (dom : Dominates ξ₂ ξ₁ g (RingHom.id Ω))
    (sm : ∀ c, x₁ c ≠ 0 → Algebra.FormallySmooth ℚ (chRing ℚ x₁ c))
    (iso : ∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) {c : κ₂} (hc : x₂ c ≠ 0) :
    Algebra.Smooth ℚ (chRing ℚ x₂ c) := by
  haveI : Algebra.FiniteType ℚ (chRing ℚ x₂ c) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  haveI : Algebra.FinitePresentation ℚ (chRing ℚ x₂ c) := Algebra.FinitePresentation.of_finiteType.1 this
  refine ⟨?_, inferInstance⟩
  rw [← Algebra.smoothLocus_eq_univ_iff]
  refine Set.eq_univ_of_forall fun P => ?_
  exact formallySmooth_atPrime tie₁ tie₂ dom sm iso hc P.asIdeal

theorem adjoin_blocks_eq {K : Type} [Fintype K] {J : K → Type} (y : (Σ k, J k) → Ω) (c : (k : K) → J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) =
      chRing ℚ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c := by
  classical
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    refine Algebra.subset_adjoin ⟨Function.update c k i, ?_⟩
    show (∏ k', y ⟨k', Function.update c k i k'⟩) / (∏ k', y ⟨k', c k'⟩) = y ⟨k, i⟩ / y ⟨k, c k⟩
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · simp
    · intro b _ hb
      rw [Function.update_of_ne hb, div_self (hc b)]
    · intro h
      exact absurd (Finset.mem_univ k) h
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨c', rfl⟩
    show (∏ k, y ⟨k, c' k⟩) / (∏ k, y ⟨k, c k⟩) ∈ _
    rw [← Finset.prod_div_distrib]
    exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, c' k⟩, rfl⟩

end Main

theorem smoothGenericFibreM_of_isoAt : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω) (K₂ : Type) [Fintype K₂] (J₂ : K₂ → Type) [∀ k, Fintype (J₂ k)] (y₂ : (Σ k, J₂ k) → Ω) (X₁ X₂ : Scheme.{0}) (ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂) (g : X₂ ⟶ X₁), (∀ q : X₁, GlobalTheory.CompanionTheory.Ar.genPt ξ₁ ⤳ q) → (∀ q : X₂, GlobalTheory.CompanionTheory.Ar.genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ (fun c' : (k : K₁) → J₁ k => ∏ k, y₁ ⟨k, c' k⟩) → CoordTie ℤ ξ₂ (fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) → GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω) → SmoothGenericFibreM y₁ → (∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) → SmoothGenericFibreM y₂ := by
  intro Ω _ _ K₁ _ J₁ _ y₁ K₂ _ J₂ _ y₂ X₁ X₂ ξ₁ ξ₂ g _ _ t₁ t₂ dom sm iso c hc
  have hne : (∏ k, y₂ ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  rw [adjoin_blocks_eq y₂ c hc]
  refine smooth_chRing t₁ t₂ dom (fun c' hc' => ?_) iso hne
  have hc'' : ∀ k, y₁ ⟨k, c' k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc' k (Finset.mem_univ k)
  have h := sm c' hc''
  rw [adjoin_blocks_eq y₁ c' hc''] at h
  exact h.formallySmooth

end GlobalTheory.CompanionTheory.Ar.SmoothChange
