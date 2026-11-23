import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockExtensionArithVar
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineIsomorphismGroupoidLawsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LineIsomorphismDefectFunctionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockJoinInclusionsCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockPullbackHermLineStatement
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.RCombine
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCoversComplexPointsStatement
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.DenseNonvan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.BuildK

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
  obtain ⟨π, hπ, h1, h2, h3, -⟩ := PositivityTheory.UnitarySelfGeneration.r_pull K ι K₁ ι₁ κ₁ v₁ P J D σ S Re R hb har alg
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

theorem exists_pair {P : Ideal (MRing ι)} {f g : MRing ι} (h : UnitRatio P f g) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) : ∃ u w : MRing ι, u * f - w * g ∈ P ∧ evC z u ≠ 0 := by
  let ρ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hρ : ∀ q, ρ q = evC z q := fun _ => rfl
  have hprime : (RingHom.ker ρ).IsPrime := RingHom.ker_isPrime ρ
  have hle : P ≤ RingHom.ker ρ := fun q hq => hz.2 q hq
  have hrel : IsRelevant (RingHom.ker ρ) := fun k => by
    obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, fun hm => hi ?_⟩
    simpa [ρ] using (RingHom.mem_ker.1 hm)
  obtain ⟨u, w, hu, -, huw⟩ := h.2.2 _ hprime hle hrel
  exact ⟨u, w, huw, fun h0 => hu (RingHom.mem_ker.2 h0)⟩

end Sides

section Assemble

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem assemble (hPB : PullbackStatement) {κ₁ : K₁ → K} {v₁ : (Σ k, ι₁ k) → Σ k, ι k} {κ₂ : K₂ → K}
    {v₂ : (Σ k, ι₂ k) → Σ k, ι k} {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} {σ : Type} [Fintype σ]
    {S₁ S₂ : AnSys D σ} (Re₁ : Realis S₁ (mCoordIdeal (y ∘ v₁))) (Re₂ : Realis S₂ (mCoordIdeal (y ∘ v₂)))
    {β : MRing ι} (hb₁ : IsBlockMap κ₁ v₁) (hb₂ : IsBlockMap κ₂ v₂) (har : IsArithVar (mCoordIdeal y) (D + 1))
    (alg₁ : AlgOver Re₁) (alg₂ : AlgOver Re₂)
    (hS : ∀ a, SameSing Re₁ Re₂ (mCoordIdeal y) κ₁ v₁ κ₂ v₂ β a a)
    {γ₁ : MRing ι₁} {c₁ : K₁ → ℕ} (hγ₁ : IsMultiHomog γ₁ c₁)
    (hz₁ : ∀ x, Re₁.π x ∈ bdry S₁.s → evC (Re₁.R.lift x x) γ₁ = 0)
    {γ₂ : MRing ι₂} {c₂ : K₂ → ℕ} (hγ₂ : IsMultiHomog γ₂ c₂)
    (hz₂ : ∀ x, Re₂.π x ∈ bdry S₂.s → evC (Re₂.R.lift x x) γ₂ = 0)
    {B : MRing ι} (hBdef : B = β * rename v₁ γ₁ * rename v₂ γ₂) {b : K → ℕ} (hB : IsMultiHomog B b)
    (hBn : B ∉ mCoordIdeal y)
    {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} {y' : (Σ k, ι' k) → Ω} {J : Ideal (MRing ι')}
    (R : AnLogRes (mCoordIdeal y') J D) (Amp : HermLine ι') (hb : IsBlockMap κ v) (hy : y' ∘ v = y)
    (har' : IsArithVar (mCoordIdeal y') (D + 1)) (hpot : IsPotential R.A (potOf R Amp))
    (hpos : IsPosPot R.A (potOf R Amp))
    (hbad : ∀ z ∈ mcPts (mCoordIdeal y'), evC z (rename v B) = 0 → z ∈ mcPts J) :
    ∃ (S : AnSys D (σ ⊕ σ)) (Re : Realis S (mCoordIdeal y')) (f g : σ → MRing ι') (d : σ → S.X → ℝ),
      Re.deg = 1 ∧ S.t₀ ≤ S₁.t₀ ∧ S.t₀ ≤ S₂.t₀ ∧
      (∀ a t, IsPullHerm (κ ∘ κ₁) (v ∘ v₁) (Re₁.line a t) (Re.line (Sum.inl a) t) ∧
        IsPullHerm (κ ∘ κ₂) (v ∘ v₂) (Re₂.line a t) (Re.line (Sum.inr a) t)) ∧
      (∀ a, IsLineIso (mCoordIdeal y') (Re.ref (Sum.inl a)).a (Re.ref (Sum.inr a)).a (f a) (g a)) ∧
      (∀ a, S.A.Smooth (d a)) ∧
      (∀ a, ∀ x ∈ S.open', S.ph (Sum.inl a) x = S.ph (Sum.inr a) x + d a x) ∧
      ∀ a x, ∀ u w : MRing ι', u * f a - w * g a ∈ mCoordIdeal y' → evC (Re.R.lift x x) u ≠ 0 →
        d a (Re.π x) = Real.log (‖evC (Re.R.lift x x) w‖ / ‖evC (Re.R.lift x x) u‖ *
          (Re.ref (Sum.inr a)).h (Re.R.lift x x) / (Re.ref (Sum.inl a)).h (Re.R.lift x x)) := by
  have hjb := GlobalTheory.T.block_join_inclusions_compat
  have e₀ : imageZ v (mCoordIdeal y') = mCoordIdeal y := by
    rw [hjb.2.1 K ι K' ι' κ v Ω y' hb, hy]
  have hc₁ : IsBlockMap (κ ∘ κ₁) (v ∘ v₁) := (hjb.2.2 K₁ ι₁ K ι K' ι' κ₁ v₁ κ v hb₁ hb).1
  have hc₂ : IsBlockMap (κ ∘ κ₂) (v ∘ v₂) := (hjb.2.2 K₂ ι₂ K ι K' ι' κ₂ v₂ κ v hb₂ hb).1
  have e₁ : imageZ (v ∘ v₁) (mCoordIdeal y') = mCoordIdeal (y ∘ v₁) := by
    rw [hjb.2.1 K₁ ι₁ K' ι' (κ ∘ κ₁) (v ∘ v₁) Ω y' hc₁, ← hy]
    rfl
  have e₂ : imageZ (v ∘ v₂) (mCoordIdeal y') = mCoordIdeal (y ∘ v₂) := by
    rw [hjb.2.1 K₂ ι₂ K' ι' (κ ∘ κ₂) (v ∘ v₂) Ω y' hc₂, ← hy]
    rfl
  obtain ⟨π₁, h₁, l₁, p₁, q₁⟩ := side hc₁ Re₁ e₁ R har' alg₁
  obtain ⟨π₂, h₂, l₂, p₂, q₂⟩ := side hc₂ Re₂ e₂ R har' alg₂
  have hB0 : ∀ z, evC z (rename v B) = evC (fun p => z (v p)) β * evC z (rename (v ∘ v₁) γ₁) *
      evC z (rename (v ∘ v₂) γ₂) := by
    intro z
    rw [hBdef, evC_rename, evC_mul, evC_mul, evC_rename (v ∘ v₁), evC_rename (v ∘ v₂), evC_rename v₁,
      evC_rename v₂]
    rfl
  have hbd₁ : ∀ x, π₁ x ∈ bdry S₁.s → evC (R.lift x x) (rename v B) = 0 := fun x hx => by
    rw [hB0, evC_bdry hc₁ Re₁ e₁ R l₁ hγ₁ hz₁ x hx]
    simp
  have hbd₂ : ∀ x, π₂ x ∈ bdry S₂.s → evC (R.lift x x) (rename v B) = 0 := fun x hx => by
    rw [hB0, evC_bdry hc₂ Re₂ e₂ R l₂ hγ₂ hz₂ x hx]
    simp
  have hBn' : rename v B ∉ mCoordIdeal y' := fun h => hBn (e₀ ▸ h)
  obtain ⟨L, s, nb, m, W, C₅, C, t₀, hL, hsec, hsnc, hnorm, hbd, ht₁, ht₂, hm₁, hm₂⟩ :=
    PositivityTheory.UnitarySelfGeneration.r_combine hPB K' ι' _ J D R Amp (rename v B) _ σ S₁ S₂ π₁ π₂ h₁ h₂ hpot hpos
      (isMultiHomog_rename hb hB) hBn' hbad (fun x hx => hbd₁ x hx) (fun x hx => hbd₂ x hx)
  let S : AnSys D (σ ⊕ σ) :=
    { X := R.X, A := R.A, Θ := potOf R Amp, L := L, s := s, nb := nb, m := m, W := W, potΘ := hpot,
      posΘ := hpos, potL := hL, sec := hsec, snc := hsnc, norm_le := hnorm,
      th := Sum.elim (fun a => (S₁.th a).pullback π₁ h₁.1) (fun a => (S₂.th a).pullback π₂ h₂.1),
      ph := Sum.elim (fun a => S₁.ph a ∘ π₁) (fun a => S₂.ph a ∘ π₂),
      phT := Sum.elim (fun a t => S₁.phT a t ∘ π₁) (fun a t => S₂.phT a t ∘ π₂),
      C₅ := C₅, C := C, t₀ := t₀,
      sing := by
        rintro (a | a)
        exacts [(hm₁ a).1, (hm₂ a).1]
      reg := by
        rintro (a | a)
        exacts [(hm₁ a).2.1, (hm₂ a).2.1]
      c2 := by
        rintro (a | a)
        exacts [(hm₁ a).2.2, (hm₂ a).2.2] }
  have hp₁ := GlobalTheory.T.block_pullback_herm_line K₁ ι₁ K' ι' (κ ∘ κ₁) (v ∘ v₁) hc₁
  have hp₂ := GlobalTheory.T.block_pullback_herm_line K₂ ι₂ K' ι' (κ ∘ κ₂) (v ∘ v₂) hc₂
  choose r₁ hr₁ using fun a => (hp₁.1 (Re₁.ref a)).exists
  choose r₂ hr₂ using fun a => (hp₂.1 (Re₂.ref a)).exists
  choose n₁ hn₁ using fun a t => (hp₁.1 (Re₁.line a t)).exists
  choose n₂ hn₂ using fun a t => (hp₂.1 (Re₂.line a t)).exists
  have sm₁ : ∀ a, IsSmoothHerm (r₁ a) := fun a => hp₁.2.1 _ _ (hr₁ a) (Re₁.ref_smooth a)
  have sm₂ : ∀ a, IsSmoothHerm (r₂ a) := fun a => hp₂.2.1 _ _ (hr₂ a) (Re₂.ref_smooth a)
  let Re : Realis S (mCoordIdeal y') :=
    { arith := har', J := J, R := R, π := id, holo := holoMap_id R.A, deg := 1, deg_pos := one_pos, br := ∅,
      degree := isDegreeOff_id R.A, ref := Sum.elim r₁ r₂, line := Sum.elim n₁ n₂,
      ref_smooth := by
        rintro (a | a)
        exacts [sm₁ a, sm₂ a]
      ref_pot := by
        rintro (a | a) x hx
        · obtain ⟨V, hV, hxV, G, hG, h⟩ := p₁ a _ (hr₁ a) x hx
          exact ⟨V, hV, hxV, G, hG, h⟩
        · obtain ⟨V, hV, hxV, G, hG, h⟩ := p₂ a _ (hr₂ a) x hx
          exact ⟨V, hV, hxV, G, hG, h⟩
      line_deg := by
        rintro (a | a) t
        · show (n₁ a t).a = (r₁ a).a
          rw [(hn₁ a t).1, (hr₁ a).1, Re₁.line_deg]
        · show (n₂ a t).a = (r₂ a).a
          rw [(hn₂ a t).1, (hr₂ a).1, Re₂.line_deg]
      line_smooth := by
        rintro (a | a) t ht ht'
        · exact hp₁.2.1 _ _ (hn₁ a t) (Re₁.line_smooth a t ht (ht'.trans ht₁))
        · exact hp₂.2.1 _ _ (hn₂ a t) (Re₂.line_smooth a t ht (ht'.trans ht₂))
      line_eq := by
        rintro (a | a) t ht ht' x
        · show Real.log ((n₁ a t).h (R.lift x x)) = Real.log ((r₁ a).h (R.lift x x)) + S₁.phT a t (π₁ x)
          rw [(hn₁ a t).2, (hr₁ a).2]
          exact q₁ a t ht (ht'.trans ht₁) x
        · show Real.log ((n₂ a t).h (R.lift x x)) = Real.log ((r₂ a).h (R.lift x x)) + S₂.phT a t (π₂ x)
          rw [(hn₂ a t).2, (hr₂ a).2]
          exact q₂ a t ht (ht'.trans ht₂) x }
  simp only [SameSing] at hS
  choose f₀ g₀ hfg using hS
  have hiso : ∀ a, IsLineIso (mCoordIdeal y') (r₁ a).a (r₂ a).a (rename v (f₀ a)) (rename v (g₀ a)) := by
    intro a
    rw [(hr₁ a).1, (hr₂ a).1, (hjb.2.2 K₁ ι₁ K ι K' ι' κ₁ v₁ κ v hb₁ hb).2,
      (hjb.2.2 K₂ ι₂ K ι K' ι' κ₂ v₂ κ v hb₂ hb).2]
    exact (GlobalTheory.T.line_isomorphism_groupoid_laws K ι _ har.2.1).2.2.2.2 K' ι' κ v _ hb e₀ _ _ _ _ (hfg a).1
  choose w hw hinv hsm using fun a => GlobalTheory.T.line_isomorphism_defect_function K' ι' _ J D R (r₁ a) (r₂ a) (rename v (f₀ a))
    (rename v (g₀ a)) har'.2.1 (hiso a) (sm₁ a) (sm₂ a)
  have hmain : ∀ a x, x ∉ bdry s → S₁.ph a (π₁ x) = S₂.ph a (π₂ x) + w a (R.lift x x) := by
    intro a x hx
    have hzP : R.lift x x ∈ mcPts (mCoordIdeal y') := R.mem x x (R.mem_U x)
    have hz : (fun p => R.lift x x (v p)) ∈ mcPts (mCoordIdeal y) :=
      e₀ ▸ (GlobalTheory.T.block_pullback_herm_line K ι K' ι' κ v hb).2.2.1 _ _ hzP
    have hne : evC (R.lift x x) (rename v B) ≠ 0 := fun h => hx ((hbd x).2 h)
    have hβ' : evC (fun p => R.lift x x (v p)) β ≠ 0 := fun h => hne (by rw [hB0, h]; simp)
    have hx₁ : π₁ x ∉ bdry S₁.s := fun h => hne (hbd₁ x h)
    have hx₂ : π₂ x ∉ bdry S₂.s := fun h => hne (hbd₂ x h)
    have hm1 : (fun p => R.lift x x ((v ∘ v₁) p)) ∈ mcPts (mCoordIdeal (y ∘ v₁)) :=
      e₁ ▸ hp₁.2.2.1 _ _ hzP
    have hm2 : (fun p => R.lift x x ((v ∘ v₂) p)) ∈ mcPts (mCoordIdeal (y ∘ v₂)) :=
      e₂ ▸ hp₂.2.2.1 _ _ hzP
    obtain ⟨y₁, hy₁⟩ := GlobalTheory.T.log_resolution_covers_complex_points K₁ ι₁ _ _ D Re₁.R Re₁.arith _ hm1
    obtain ⟨y₂, hy₂⟩ := GlobalTheory.T.log_resolution_covers_complex_points K₂ ι₂ _ _ D Re₂.R Re₂.arith _ hm2
    have ε₁ : π₁ x = Re₁.π y₁ := l₁ x y₁ hy₁
    have ε₂ : π₂ x = Re₂.π y₂ := l₂ x y₂ hy₂
    obtain ⟨u, t, hut, hu⟩ := exists_pair (hfg a).1.2 hz
    have key := (hfg a).2 _ hz hβ' y₁ y₂ hy₁ hy₂ (ε₁ ▸ hx₁) (ε₂ ▸ hx₂) u t hut hu
    have hmem : rename v u * rename v (f₀ a) - rename v t * rename v (g₀ a) ∈ mCoordIdeal y' := by
      have : rename v (u * f₀ a - t * g₀ a) ∈ mCoordIdeal y' := by
        have h' : u * f₀ a - t * g₀ a ∈ imageZ v (mCoordIdeal y') := e₀ ▸ hut
        exact h'
      simpa using this
    have hdf := hw a _ hzP (rename v u) (rename v t) hmem (by rw [evC_rename]; exact hu)
    rw [evC_rename, evC_rename, (hr₂ a).2, (hr₁ a).2] at hdf
    have h3 : w a (R.lift x x) = S₁.ph a (π₁ x) - S₂.ph a (π₂ x) := by
      rw [ε₁, ε₂]
      exact hdf.trans key
    linarith
  refine ⟨S, Re, fun a => rename v (f₀ a), fun a => rename v (g₀ a), fun a x => w a (R.lift x x), rfl, ht₁, ht₂,
    fun a t => ⟨hn₁ a t, hn₂ a t⟩, hiso, hsm, fun a x hx => hmain a x hx, ?_⟩
  exact fun a x u t h1 h2 => hw a _ (R.mem x x (R.mem_U x)) u t h1 h2

end Assemble

theorem joint_system : Inputs → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (σ : Type) [Fintype σ] (S₁ S₂ : AnSys D σ) (Re₁ : Realis S₁ (mCoordIdeal (y ∘ v₁))) (Re₂ : Realis S₂ (mCoordIdeal (y ∘ v₂))) (β : MRing ι) (b : K → ℕ), IsBlockMap κ₁ v₁ → IsBlockMap κ₂ v₂ → IsArithVar (mCoordIdeal y) (D + 1) → IsMultiHomog β b → β ∉ mCoordIdeal y → AlgOver Re₁ → AlgOver Re₂ → (∀ a, SameSing Re₁ Re₂ (mCoordIdeal y) κ₁ v₁ κ₂ v₂ β a a) → ∃ (K' : Type) (_ : Fintype K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (y' : (Σ k, ι' k) → Ω) (S : AnSys D (σ ⊕ σ)) (Re : Realis S (mCoordIdeal y')) (f g : σ → MRing ι') (d : σ → S.X → ℝ), IsBlockMap κ v ∧ y' ∘ v = y ∧ blockFnField y' = blockFnField y ∧ Re.deg = 1 ∧ S.t₀ ≤ S₁.t₀ ∧ S.t₀ ≤ S₂.t₀ ∧ (∀ a t, IsPullHerm (κ ∘ κ₁) (v ∘ v₁) (Re₁.line a t) (Re.line (Sum.inl a) t) ∧ IsPullHerm (κ ∘ κ₂) (v ∘ v₂) (Re₂.line a t) (Re.line (Sum.inr a) t)) ∧ (∀ a, IsLineIso (mCoordIdeal y') (Re.ref (Sum.inl a)).a (Re.ref (Sum.inr a)).a (f a) (g a)) ∧ (∀ a, S.A.Smooth (d a)) ∧ (∀ a, ∀ x ∈ S.open', S.ph (Sum.inl a) x = S.ph (Sum.inr a) x + d a x) ∧ ∀ a x, ∀ u w : MRing ι', u * f a - w * g a ∈ mCoordIdeal y' → evC (Re.R.lift x x) u ≠ 0 → d a (Re.π x) = Real.log (‖evC (Re.R.lift x x) w‖ / ‖evC (Re.R.lift x x) u‖ * (Re.ref (Sum.inr a)).h (Re.R.lift x x) / (Re.ref (Sum.inl a)).h (Re.R.lift x x)) := by
  intro hI hK K _ ι _ K₁ _ ι₁ _ K₂ _ ι₂ _ κ₁ v₁ κ₂ v₂ Ω _ _ y D σ _ S₁ S₂ Re₁ Re₂ β b hb₁ hb₂ har hβ hβn alg₁ alg₂ hS
  obtain ⟨γ₁, c₁, hγ₁, hγn₁, hz₁⟩ := exists_bdry_form Re₁ alg₁
  obtain ⟨γ₂, c₂, hγ₂, hγn₂, hz₂⟩ := exists_bdry_form Re₂ alg₂
  have hjb := GlobalTheory.T.block_join_inclusions_compat
  have hprime : (mCoordIdeal y).IsPrime := har.2.1.1
  have hn₁ : rename v₁ γ₁ ∉ mCoordIdeal y := fun h => hγn₁ (by
    rw [← hjb.2.1 K₁ ι₁ K ι κ₁ v₁ Ω y hb₁]
    exact h)
  have hn₂ : rename v₂ γ₂ ∉ mCoordIdeal y := fun h => hγn₂ (by
    rw [← hjb.2.1 K₂ ι₂ K ι κ₂ v₂ Ω y hb₂]
    exact h)
  have hBn : β * rename v₁ γ₁ * rename v₂ γ₂ ∉ mCoordIdeal y := fun h => by
    rcases hprime.mem_or_mem h with h | h
    · rcases hprime.mem_or_mem h with h | h
      exacts [hβn h, hn₁ h]
    · exact hn₂ h
  have hB := isMultiHomog_mul (isMultiHomog_mul hβ (isMultiHomog_rename hb₁ hγ₁)) (isMultiHomog_rename hb₂ hγ₂)
  obtain ⟨K', _, ι', _, κ, v, y', J, R, Amp, hb, hy, hfield, har', -, -, hpot, hpos, hbad⟩ :=
    GlobalTheory.CompanionTheory.Ar.Cmp.Good.exists_good_model hK K ι Ω y D _ _ har hB hBn
  obtain ⟨S, Re, f, g, d, h⟩ := assemble hI.pullback Re₁ Re₂ hb₁ hb₂ har alg₁ alg₂ hS hγ₁ hz₁ hγ₂ hz₂ rfl hB hBn
    R Amp hb hy har' hpot hpos hbad
  exact ⟨K', _, ι', _, κ, v, y', S, Re, f, g, d, hb, hy, hfield, h⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.BuildK

namespace PositivityTheory.UnitarySelfGeneration

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

end PositivityTheory.UnitarySelfGeneration
