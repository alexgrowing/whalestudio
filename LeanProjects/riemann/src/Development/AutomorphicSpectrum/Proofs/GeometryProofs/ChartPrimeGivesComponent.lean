import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

section Alg

variable {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] {κ : Type}

abbrev chartZ (x : κ → Ω) (c : κ) : Subalgebra ℤ Ω :=
  Algebra.adjoin ℤ (Set.range fun j => x j / x c)

theorem chartZ_le (x : κ → Ω) (c : κ) {t : Ω} (ht : t ∈ chartZ x c) : t ∈ chartQ x c := by
  induction ht using Algebra.adjoin_induction with
  | mem a ha => exact Algebra.subset_adjoin ha
  | algebraMap r => simpa using intCast_mem (chartQ x c) r
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem exists_natCast_mul_mem (x : κ → Ω) (c : κ) {s : Ω} (hs : s ∈ chartQ x c) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : Ω) * s ∈ chartZ x c := by
  induction hs using Algebra.adjoin_induction with
  | mem a ha => exact ⟨1, one_ne_zero, by simpa using Algebra.subset_adjoin ha⟩
  | algebraMap r =>
    refine ⟨r.den, r.den_nz, ?_⟩
    have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
    have e : (r.den : Ω) * algebraMap ℚ Ω r = (r.num : Ω) := by
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [e]
    exact intCast_mem _ _
  | add a b _ _ ha hb =>
    obtain ⟨k, hk0, hk⟩ := ha
    obtain ⟨l, hl0, hl⟩ := hb
    refine ⟨k * l, mul_ne_zero hk0 hl0, ?_⟩
    have e : ((k * l : ℕ) : Ω) * (a + b) = (l : Ω) * ((k : Ω) * a) + (k : Ω) * ((l : Ω) * b) := by
      push_cast
      ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) hk) (mul_mem (natCast_mem _ _) hl)
  | mul a b _ _ ha hb =>
    obtain ⟨k, hk0, hk⟩ := ha
    obtain ⟨l, hl0, hl⟩ := hb
    refine ⟨k * l, mul_ne_zero hk0 hl0, ?_⟩
    have e : ((k * l : ℕ) : Ω) * (a * b) = ((k : Ω) * a) * ((l : Ω) * b) := by
      push_cast
      ring
    rw [e]
    exact mul_mem hk hl

def chartIncl (x : κ → Ω) (c : κ) : chartZ x c →+* chartQ x c :=
  ((chartZ x c).val : chartZ x c →+* Ω).codRestrict (chartQ x c) fun t => chartZ_le x c t.2

theorem natCast_notMem_chartQ (x : κ → Ω) (c : κ) {I : Ideal (chartQ x c)} (hI : I.IsPrime) {m : ℕ}
    (hm : m ≠ 0) : (m : chartQ x c) ∉ I := by
  intro h
  apply hI.ne_top
  rw [Ideal.eq_top_iff_one]
  have hd : (m : Ω) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hi : (m : Ω)⁻¹ ∈ chartQ x c := by
    have := (chartQ x c).algebraMap_mem ((m : ℚ)⁻¹)
    simpa using this
  have e : (⟨(m : Ω)⁻¹, hi⟩ : chartQ x c) * (m : chartQ x c) = 1 :=
    Subtype.ext (by simp [hd])
  rw [← e]
  exact I.mul_mem_left _ h

theorem natCast_mul_notMem_iff (x : κ → Ω) (c : κ) {I : Ideal (chartQ x c)} (hI : I.IsPrime) {m : ℕ}
    (hm : m ≠ 0) (s : chartQ x c) : (m : chartQ x c) * s ∉ I ↔ s ∉ I := by
  refine not_congr ⟨fun h => ?_, fun h => I.mul_mem_left _ h⟩
  exact (hI.mem_or_mem h).resolve_left (natCast_notMem_chartQ x c hI hm)

end Alg

section Pts

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] {κ : Type}

theorem notMem_comap_iff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal B) (P : A → Prop)
    (h : ∀ t, t ∉ I.comap f ↔ P t) (t : A) : f t ∉ I ↔ P t := by
  rw [← h t, Ideal.mem_comap]

theorem algebraMap_mem_regAt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} (hp : Char0 ξ p) (r : ℚ) :
    algebraMap ℚ Ω r ∈ regAt ξ p := by
  have e : algebraMap ℚ Ω r = (r.num : Ω) * ((r.den : Ω))⁻¹ := by
    rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
  rw [e]
  exact (regAt ξ p).mul_mem (intCast_mem _ _) (Char0.unitAt_natCast hp r.den_nz).2.2

theorem chartQ_le_regAt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : κ → Ω} {c : κ} {p : Cpt ξ} (hp : Char0 ξ p)
    (hc : InChart ξ x c p) {s : Ω} (hs : s ∈ chartQ x c) : s ∈ regAt ξ p := by
  induction hs using Algebra.adjoin_induction with
  | mem a ha => obtain ⟨j, rfl⟩ := ha; exact hc.2 j
  | algebraMap r => exact algebraMap_mem_regAt hp r
  | add a b _ _ ha hb => exact (regAt ξ p).add_mem ha hb
  | mul a b _ _ ha hb => exact (regAt ξ p).mul_mem ha hb

theorem char_zero_of_chart_inclusion {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : κ → Ω} {c : κ} {I : Ideal (chartQ x c)}
    (hI : I.IsPrime) {p : Cpt ξ} (hp : ∀ t : chartZ x c, chartIncl x c t ∉ I ↔ unitAt ξ p (t : Ω)) :
    Char0 ξ p := by
  intro r hr hF
  apply hF
  have h := (hp ⟨(r : Ω), natCast_mem _ r⟩).1
  apply h
  have e : chartIncl x c ⟨(r : Ω), natCast_mem _ r⟩ = (r : chartQ x c) := Subtype.ext (by simp [chartIncl])
  rw [e]
  exact natCast_notMem_chartQ x c hI hr.ne_zero

theorem notMem_iff_unitAt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : κ → Ω} {c : κ} {I : Ideal (chartQ x c)}
    (hI : I.IsPrime) {p : Cpt ξ} (hchar : Char0 ξ p) (hc : InChart ξ x c p)
    (hp : ∀ t : chartZ x c, chartIncl x c t ∉ I ↔ unitAt ξ p (t : Ω)) (s : chartQ x c) :
    s ∉ I ↔ unitAt ξ p (s : Ω) := by
  obtain ⟨m, hm, hms⟩ := exists_natCast_mul_mem x c s.2
  have e : chartIncl x c ⟨_, hms⟩ = (m : chartQ x c) * s := Subtype.ext (by simp [chartIncl])
  have h1 := hp ⟨_, hms⟩
  rw [e, natCast_mul_notMem_iff x c hI hm] at h1
  rw [h1]
  constructor
  · intro h
    exact unitAt_of_mul_right h (natCast_mem _ m) (chartQ_le_regAt hchar hc s.2)
  · intro h
    exact unitAt_mul (Char0.unitAt_natCast hchar hm) h

theorem isLocAt_of_unit {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : κ → Ω} {c : κ} {I : Ideal (chartQ x c)}
    {p : Cpt ξ} (hchar : Char0 ξ p) (hc : InChart ξ x c p)
    (hreg : ∀ a : Ω, a ∈ regAt ξ p ↔ ∃ s ∈ chartZ x c, unitAt ξ p s ∧ s * a ∈ chartZ x c)
    (hunit : ∀ s : chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) : IsLocAt (chartQ x c) I (regAt ξ p) := by
  refine fun a => ⟨fun ha => ?_, ?_⟩
  · obtain ⟨s, hs, hsu, hsa⟩ := (hreg a).1 ha
    exact ⟨⟨s, chartZ_le x c hs⟩, (hunit _).2 hsu, chartZ_le x c hsa⟩
  · rintro ⟨s, hs, hsa⟩
    have hu := (hunit s).1 hs
    have e : a = (s : Ω)⁻¹ * ((s : Ω) * a) := by
      rw [inv_mul_cancel_left₀ hu.1]
    rw [e]
    exact (regAt ξ p).mul_mem hu.2.2 (chartQ_le_regAt hchar hc hsa)

theorem chart_prime_component_point (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : κ → Ω) (c : κ)
    (hT : CoordTie ℤ ξ x) (hc0 : x c ≠ 0) (I : Ideal (chartQ x c)) (hI : I.IsPrime) :
    ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧
      IsLocAt (chartQ x c) I (regAt ξ p) := by
  have hJ : (I.comap (chartIncl x c)).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨p, ⟨hc, hp⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ κ x hT c hc0 _ hJ
  have hp' := notMem_comap_iff (chartIncl x c) I (fun t => unitAt ξ p (t : Ω)) hp
  have hchar : Char0 ξ p := char_zero_of_chart_inclusion hI hp'
  have hunit := notMem_iff_unitAt hI hchar hc hp'
  exact ⟨p, hchar, hc, hunit, isLocAt_of_unit hchar hc (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x hT c p hc) hunit⟩

end Pts

theorem chartPrime_point : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ I : Ideal (Mdl.chartQ x c), I.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧ IsLocAt (Mdl.chartQ x c) I (regAt ξ p) :=
  fun _ _ _ _ ξ _ x c hT hc0 I hI => chart_prime_component_point ξ x c hT hc0 I hI

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
