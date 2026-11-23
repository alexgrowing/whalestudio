import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mh_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem mh_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k

theorem mh_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem mh_C (r : ℤ) : IsMultiHomog (MvPolynomial.C r : MRing ι) 0 := by
  classical
  intro m hm k
  have hm0 : m = 0 := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
    by_contra hne
    exact hm (if_neg (Ne.symm hne))
  subst hm0
  simp

private theorem isMultiHomog_mul_of_mRing {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, h1, m2, h2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hf m1 h1 k, hg m2 h2 k]

theorem mh_prod {I : Type} (S : Finset I) {f : I → MRing ι} {d : I → K → ℕ}
    (h : ∀ i ∈ S, IsMultiHomog (f i) (d i)) : IsMultiHomog (∏ i ∈ S, f i) (∑ i ∈ S, d i) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    simpa using mh_C (ι := ι) 1
  · intro i S hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact isMultiHomog_mul_of_mRing (h i (Finset.mem_insert_self i S)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Forms

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] {𝕜 : Type} [Field 𝕜]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → 𝕜}

theorem hv_zero : Small.HasVal y (0 : K → ℤ) (0 : Ω) z (0 : 𝕜) := by
  refine ⟨0, 0, 0, 1, mh_zero 0, by simpa using mh_C (ι := ι) 1, fun k => by simp, by simp, by simp, by simp⟩

theorem hv_add {s s' : Ω} {w w' : 𝕜} (h : Small.HasVal y (0 : K → ℤ) s z w)
    (h' : Small.HasVal y (0 : K → ℤ) s' z w') : Small.HasVal y (0 : K → ℤ) (s + s') z (w + w') := by
  obtain ⟨dg, dh, g, hp, hg, hh, e, ey, hz, ez⟩ := h
  obtain ⟨dg', dh', g', hp', hg', hh', e', ey', hz', ez'⟩ := h'
  have hd : dg = dh := funext fun k => by
    have := e k
    simp only [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hd' : dg' = dh' := funext fun k => by
    have := e' k
    simp only [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  subst hd hd'
  refine ⟨dg + dg', dg + dg', g * hp' + g' * hp, hp * hp', mh_add (isMultiHomog_mul_of_mRing hg hh') ?_,
    isMultiHomog_mul_of_mRing hh hh', fun k => by simp, ?_, ?_, ?_⟩
  · rw [add_comm dg dg']
    exact isMultiHomog_mul_of_mRing hg' hh
  · simp only [map_add, map_mul, ey, ey']
    ring
  · rw [map_mul]
    exact mul_ne_zero hz hz'
  · simp only [map_add, map_mul, ez, ez']
    ring

theorem hv_neg {s : Ω} {w : 𝕜} (h : Small.HasVal y (0 : K → ℤ) s z w) :
    Small.HasVal y (0 : K → ℤ) (-s) z (-w) := by
  obtain ⟨dg, dh, g, hp, hg, hh, e, ey, hz, ez⟩ := h
  exact ⟨dg, dh, -g, hp, mh_neg hg, hh, e, by rw [map_neg, ey, neg_mul], hz, by rw [map_neg, ez, neg_mul]⟩

theorem hv_quot {d : K → ℕ} {g h : MRing ι} (hg : IsMultiHomog g d) (hh : IsMultiHomog h d)
    {s : Ω} (e : MvPolynomial.aeval y g = s * MvPolynomial.aeval y h) (hz : MvPolynomial.aeval z h ≠ 0) :
    Small.HasVal y (0 : K → ℤ) s z (MvPolynomial.aeval z g / MvPolynomial.aeval z h) := by
  exact ⟨d, d, g, h, hg, hh, fun k => by simp, e, hz, (div_mul_cancel₀ _ hz).symm⟩

theorem hv_natInv [CharZero Ω] [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) :
    Small.HasVal y (0 : K → ℤ) ((n : Ω))⁻¹ z ((n : 𝕜))⁻¹ := by
  refine ⟨0, 0, 1, MvPolynomial.C (n : ℤ), by simpa using mh_C (ι := ι) 1, mh_C (n : ℤ), fun k => by simp,
    ?_, ?_, ?_⟩
  · simp [hn]
  · simpa using hn
  · simp [hn]

def valRing (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → 𝕜) : Subring Ω where
  carrier := {s | ∃ w, Small.HasVal y (0 : K → ℤ) s z w}
  mul_mem' := by
    rintro a b ⟨w, hw⟩ ⟨w', hw'⟩
    have := hv_mul hw hw'
    rw [add_zero] at this
    exact ⟨_, this⟩
  one_mem' := ⟨1, hv_one⟩
  add_mem' := by
    rintro a b ⟨w, hw⟩ ⟨w', hw'⟩
    exact ⟨_, hv_add hw hw'⟩
  zero_mem' := ⟨0, hv_zero⟩
  neg_mem' := by
    rintro a ⟨w, hw⟩
    exact ⟨_, hv_neg hw⟩

def valMap (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) : valRing y z →+* 𝕜 where
  toFun x := x.2.choose
  map_one' := GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (valRing y z).one_mem.choose_spec hv_one
  map_mul' a b := by
    have := hv_mul a.2.choose_spec b.2.choose_spec
    rw [add_zero] at this
    exact GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (a * b).2.choose_spec this
  map_zero' := GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (valRing y z).zero_mem.choose_spec hv_zero
  map_add' a b :=
    GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (a + b).2.choose_spec
      (hv_add a.2.choose_spec b.2.choose_spec)

theorem hasVal_valMap (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) (x : valRing y z) :
    Small.HasVal y (0 : K → ℤ) (x : Ω) z (valMap hz x) := by
  exact x.2.choose_spec

end Values

theorem exists_subring_val : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω), Birational y → ∀ B : Finset Ω, ∃ u : MRing ι, Small.IsFormOff (mCoordIdeal y) u ∧ ∀ (𝕜 : Type) [Field 𝕜] [CharZero 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → MvPolynomial.aeval z u ≠ 0 → ∃ (A : Subring Ω) (ev : A →+* 𝕜), (↑B : Set Ω) ⊆ A ∧ (∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ A) ∧ ∀ x : A, Small.HasVal y 0 (x : Ω) z (ev x) := by
  intro K _ ι _ Ω _ _ y hbir B
  have hb' : ∀ s : Ω, ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧
      MvPolynomial.aeval y h ≠ 0 ∧ MvPolynomial.aeval y g = s * MvPolynomial.aeval y h := hbir
  choose d g hq hg hh hyne e using hb'
  have key : ∀ f : MRing ι, MvPolynomial.eval (fun _ => (1 : Ω)) (mConeMap y f) = MvPolynomial.aeval y f := by
    intro f
    induction f using MvPolynomial.induction_on
    · simp [mConeMap]
    · rename_i hp hq
      simp only [map_add, hp, hq]
    · rename_i hp
      simp only [map_mul, hp]
      simp [mConeMap]
  refine ⟨∏ b ∈ B, hq b, ⟨⟨∑ b ∈ B, d b, mh_prod B fun b _ => hh b⟩, ?_⟩, ?_⟩
  · intro hu
    have h0 : MvPolynomial.aeval y (∏ b ∈ B, hq b) = 0 := by
      rw [← key, show mConeMap y (∏ b ∈ B, hq b) = 0 from hu, map_zero]
    rw [map_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨b, _, hb⟩ := h0
    exact hyne b hb
  · intro 𝕜 _ _ z hz hzu
    rw [map_prod] at hzu
    refine ⟨valRing y z, valMap hz, ?_, ?_, fun x => hasVal_valMap hz x⟩
    · intro b hb
      exact ⟨_, hv_quot (hg b) (hh b) (e b) (Finset.prod_ne_zero_iff.mp hzu b hb)⟩
    · intro n hn
      exact ⟨_, hv_natInv hn⟩

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub
