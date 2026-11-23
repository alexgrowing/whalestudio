import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockExtensionArithVarStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineIsomorphismGroupoidLawsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LineIsomorphismDefectFunctionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockJoinInclusionsCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockPullbackHermLineStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CommonResolutionPotentialComparisonStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCoversComplexPointsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicRealisationHolomorphicMapStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.Build

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem evC_torus {f : MRing ι} {b : K → ℕ} (hf : IsMultiHomog f b) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    evC (fun p => c p.1 * z p) f = (∏ k, c k ^ b k) * evC z f := by
  classical
  simp only [evC, eval_map]
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∏ p : Σ k, ι k, c p.1 ^ m p = ∏ k, c k ^ b k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ b k
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  simp only [mul_pow, Finset.prod_mul_distrib, h1]
  ring

theorem evC_eq_zero_iff_of_sameOrbit {f : MRing ι} {b : K → ℕ} (hf : IsMultiHomog f b)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : evC z f = 0 ↔ evC z' f = 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  have h0 : ∏ k, c k ^ b k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  rw [evC_torus hf]
  simp [h0]

theorem evC_rename (v : (Σ k, ι k) → Σ k, ι' k) (z : (Σ k, ι' k) → ℂ) (f : MRing ι) :
    evC z (rename v f) = evC (fun p => z (v p)) f := by
  rw [evC, map_rename, eval_rename]
  rfl

theorem evC_mul (z : (Σ k, ι k) → ℂ) (f g : MRing ι) : evC z (f * g) = evC z f * evC z g := by
  simp [evC]

theorem sum_mapDomain {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : ∀ p, (v p).1 = κ p.1)
    [DecidableEq K'] (m : (Σ k, ι k) →₀ ℕ) (k' : K') :
    ∑ i, (Finsupp.mapDomain v m) ⟨k', i⟩ = ∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0 := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf, hg]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  | single p n =>
    have hR : (∑ q : Σ k, ι k, if κ q.1 = k' then (Finsupp.single p n) q else 0) =
        if κ p.1 = k' then n else 0 := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq
        simp [Finsupp.single_apply, Ne.symm hq]
      · simp
    have hL : ∀ q : Σ k, ι' k, ∑ i, (Finsupp.single q n) ⟨k', i⟩ = if q.1 = k' then n else 0 := by
      rintro ⟨kq, iq⟩
      by_cases h : kq = k'
      · subst h
        simp [Finsupp.single_apply]
      · simp [Finsupp.single_apply, h]
    rw [Finsupp.mapDomain_single, hL, hR, hv]

theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v) {f : MRing ι}
    {b : K → ℕ} (hf : IsMultiHomog f b) : IsMultiHomog (rename v f) (Function.extend κ b 0) := by
  classical
  intro m hm k'
  rw [support_rename_of_injective hb.2.1, Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  rw [sum_mapDomain hb.2.2.1, Fintype.sum_sigma]
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hb.1.extend_apply, Finset.sum_eq_single k]
    · simpa using hf m₀ hm₀ k
    · intro k₂ _ hne
      exact Finset.sum_eq_zero fun i _ => if_neg (hb.1.ne hne)
    · simp
  · rw [Function.extend_apply' _ _ _ hk]
    exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => if_neg fun h => hk ⟨k, h⟩

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m₁ h₁ k, hg m₂ h₂ k]

end Forms

section Sides

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]

theorem exists_bdry_form {P₁ : Ideal (MRing ι₁)} {D : ℕ} {σ : Type} {S : AnSys D σ} (Re : Realis S P₁)
    (h : AlgOver Re) : ∃ (γ : MRing ι₁) (c : K₁ → ℕ), IsMultiHomog γ c ∧ γ ∉ P₁ ∧
      ∀ x, Re.π x ∈ bdry S.s → evC (Re.R.lift x x) γ = 0 := by
  obtain ⟨K₀, _, ι₀, _, κ, v, U, lam, β, b, hb, -, hor, hβ, hn, hz⟩ := h
  refine ⟨rename v β, Function.extend κ b 0, isMultiHomog_rename hb hβ, hn, fun x hx => ?_⟩
  rw [evC_rename, ← evC_eq_zero_iff_of_sameOrbit hβ (hor x)]
  exact hz _ hx

theorem side {κ₁ : K₁ → K} {v₁ : (Σ k, ι₁ k) → Σ k, ι k} (hb : IsBlockMap κ₁ v₁) {P J : Ideal (MRing ι)}
    {D : ℕ} {σ : Type} {S : AnSys D σ} {P₁ : Ideal (MRing ι₁)} (Re : Realis S P₁) (e : imageZ v₁ P = P₁)
    (R : AnLogRes P J D) (har : IsArithVar P (D + 1)) (alg : AlgOver Re) :
    ∃ (π : R.X → S.X) (hπ : HoloMap R.A S.A π),
      (∀ (x : R.X) (x₁ : Re.R.X), SameOrbit (Re.R.lift x₁ x₁) (fun p => R.lift x x (v₁ p)) → π x = Re.π x₁) ∧
      (∀ a (ref' : HermLine ι), IsPullHerm κ₁ v₁ (Re.ref a) ref' →
        SamePot R.A Set.univ (potOf R ref') ((S.th a).pullback π hπ.1)) ∧
      (∀ a t, 0 < t → t ≤ S.t₀ → ∀ x, Real.log ((Re.line a t).h fun p => R.lift x x (v₁ p)) =
        Real.log ((Re.ref a).h fun p => R.lift x x (v₁ p)) + S.phT a t (π x)) := by
  subst e
  obtain ⟨π, hπ, h1, h2, h3, -⟩ := GlobalTheory.T.algebraic_realisation_holomorphic_map K ι K₁ ι₁ κ₁ v₁ P J D σ S Re R hb har alg
  exact ⟨π, hπ, h1, h2, h3⟩

theorem evC_bdry {κ₁ : K₁ → K} {v₁ : (Σ k, ι₁ k) → Σ k, ι k} (hb : IsBlockMap κ₁ v₁) {P J : Ideal (MRing ι)}
    {D : ℕ} {σ : Type} {S : AnSys D σ} {P₁ : Ideal (MRing ι₁)} (Re : Realis S P₁) (e : imageZ v₁ P = P₁)
    (R : AnLogRes P J D) {π : R.X → S.X}
    (hπ : ∀ (x : R.X) (x₁ : Re.R.X), SameOrbit (Re.R.lift x₁ x₁) (fun p => R.lift x x (v₁ p)) → π x = Re.π x₁)
    {γ : MRing ι₁} {c : K₁ → ℕ} (hγ : IsMultiHomog γ c)
    (hz : ∀ x, Re.π x ∈ bdry S.s → evC (Re.R.lift x x) γ = 0) (x : R.X) (hx : π x ∈ bdry S.s) :
    evC (R.lift x x) (rename v₁ γ) = 0 := by
  have hmem : (fun p => R.lift x x (v₁ p)) ∈ mcPts P₁ :=
    e ▸ (GlobalTheory.T.block_pullback_herm_line K₁ ι₁ K ι κ₁ v₁ hb).2.2.1 P _ (R.mem x x (R.mem_U x))
  obtain ⟨x₁, hx₁⟩ := GlobalTheory.T.log_resolution_covers_complex_points K₁ ι₁ P₁ _ D Re.R Re.arith _ hmem
  rw [evC_rename, ← evC_eq_zero_iff_of_sameOrbit hγ hx₁]
  exact hz x₁ (hπ x x₁ hx₁ ▸ hx)

end Sides

section Assemble

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

end Assemble

end GlobalTheory.CompanionTheory.Ar.Cmp.Build
