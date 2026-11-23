import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.Sep

section Forms

variable {Ω : Type} [Field Ω] {N : ℕ}

theorem aeval_eq_pow_mul {σ : Type} [Fintype σ] {v w : σ → Ω} {t : Ω} (h : ∀ i, w i = t * v i)
    {G : MvPolynomial σ ℤ} {d : ℕ} (hG : G.IsHomogeneous d) :
    MvPolynomial.aeval w G = t ^ d * MvPolynomial.aeval v G := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i, m i = d := by
    have := hG (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [h, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem ratEval_eq_pow_mul (x : Fin (N + 1) → Ω) {c c' : Fin (N + 1)} (hc : x c ≠ 0)
    {G : MRing (fun _ : Unit => Fin (N + 1))} {d : ℕ} (hG : G.IsHomogeneous d) :
    ratEval x c' G = (x c / x c') ^ d * ratEval x c G := by
  refine aeval_eq_pow_mul (fun i => ?_) hG
  field_simp

theorem ratEval_C (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) (n : ℤ) :
    ratEval x c (MvPolynomial.C n) = (n : Ω) :=
  (MvPolynomial.aeval_C _ n).trans (eq_intCast _ n)

theorem ratEval_X_mul (x : Fin (N + 1) → Ω) (c c' : Fin (N + 1)) (H : MRing (fun _ : Unit => Fin (N + 1))) :
    ratEval x c' (MvPolynomial.X ⟨(), c⟩ * H) = x c / x c' * ratEval x c' H := by
  simp only [map_mul, MvPolynomial.aeval_X]

theorem isHomogeneous_X_mul (c : Fin (N + 1)) {H : MRing (fun _ : Unit => Fin (N + 1))} {d : ℕ}
    (hH : H.IsHomogeneous d) : (MvPolynomial.X ⟨(), c⟩ * H : MRing (fun _ : Unit => Fin (N + 1))).IsHomogeneous (d + 1) := by
  rw [add_comm d 1]
  exact (MvPolynomial.isHomogeneous_X ℤ (⟨(), c⟩ : Σ _ : Unit, Fin (N + 1))).mul hH

theorem exists_form [Algebra ℚ Ω] (x : Fin (N + 1) → Ω) {c : Fin (N + 1)} (hc : x c ≠ 0) {a : Ω}
    (ha : a ∈ chartQ x c) :
    ∃ (m d : ℕ) (H : MRing (fun _ : Unit => Fin (N + 1))),
      m ≠ 0 ∧ H.IsHomogeneous d ∧ ratEval x c H = m * a := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    exact ⟨1, 1, MvPolynomial.X ⟨(), j⟩, one_ne_zero, MvPolynomial.isHomogeneous_X _ _, by simp⟩
  | algebraMap r =>
    refine ⟨r.den, 0, MvPolynomial.C r.num, r.den_nz, MvPolynomial.isHomogeneous_C _ _, ?_⟩
    have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
    rw [eq_ratCast (algebraMap ℚ Ω) r, Rat.cast_def]
    rw [ratEval_C]
    field_simp
  | add a b _ _ ha hb =>
    obtain ⟨m₁, d₁, H₁, hm₁, hH₁, hv₁⟩ := ha
    obtain ⟨m₂, d₂, H₂, hm₂, hH₂, hv₂⟩ := hb
    have hX : (MvPolynomial.X ⟨(), c⟩ : MRing (fun _ : Unit => Fin (N + 1))).IsHomogeneous 1 :=
      MvPolynomial.isHomogeneous_X _ _
    refine ⟨m₁ * m₂, d₁ + d₂,
      MvPolynomial.C (m₂ : ℤ) * H₁ * MvPolynomial.X ⟨(), c⟩ ^ d₂ +
        MvPolynomial.C (m₁ : ℤ) * H₂ * MvPolynomial.X ⟨(), c⟩ ^ d₁,
      mul_ne_zero hm₁ hm₂, ?_, ?_⟩
    · refine MvPolynomial.IsHomogeneous.add ?_ ?_
      · simpa using ((MvPolynomial.isHomogeneous_C _ (m₂ : ℤ)).mul hH₁).mul (hX.pow d₂)
      · simpa [add_comm] using ((MvPolynomial.isHomogeneous_C _ (m₁ : ℤ)).mul hH₂).mul (hX.pow d₁)
    · simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_X, ratEval_C, hv₁, hv₂, div_self hc]
      push_cast
      ring
  | mul a b _ _ ha hb =>
    obtain ⟨m₁, d₁, H₁, hm₁, hH₁, hv₁⟩ := ha
    obtain ⟨m₂, d₂, H₂, hm₂, hH₂, hv₂⟩ := hb
    refine ⟨m₁ * m₂, d₁ + d₂, H₁ * H₂, mul_ne_zero hm₁ hm₂, hH₁.mul hH₂, ?_⟩
    simp only [map_mul, hv₁, hv₂]
    push_cast
    ring

end Forms

section Pts

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ}

theorem ratEval_regular {x : Fin (N + 1) → Ω} {c : Fin (N + 1)} {p : Cpt ξ} (hc : InChart ξ x c p)
    (g : MRing (fun _ : Unit => Fin (N + 1))) : ratEval x c g ∈ regAt ξ p := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa using intCast_mem (regAt ξ p) a
  | add a b ha hb => simpa using (regAt ξ p).add_mem ha hb
  | mul_X a i ha => simpa using (regAt ξ p).mul_mem ha (hc.2 i.2)

theorem inChart_of_unitAt {x : Fin (N + 1) → Ω} {c c' : Fin (N + 1)} {q : Cpt ξ} (hc : x c ≠ 0)
    (hc' : InChart ξ x c' q) (ht : unitAt ξ q (x c / x c')) : InChart ξ x c q := by
  refine ⟨hc, fun j => ?_⟩
  have e : x j / x c = x j / x c' * (x c / x c')⁻¹ := by
    have := hc'.1
    field_simp
  rw [e]
  exact (regAt ξ q).mul_mem (hc'.2 j) ht.2.2

theorem not_unitAt_form [CharZero Ω] {x : Fin (N + 1) → Ω} {c c' : Fin (N + 1)} {q : Cpt ξ} {a : Ω}
    (hc : x c ≠ 0) (hq0 : Char0 ξ q) (hc' : InChart ξ x c' q) (har : InChart ξ x c q → a ∈ regAt ξ q)
    (hnon : InChart ξ x c q → ¬ unitAt ξ q a) {m d : ℕ} {H : MRing (fun _ : Unit => Fin (N + 1))} (hm : m ≠ 0)
    (hH : H.IsHomogeneous d) (hv : ratEval x c H = m * a) :
    ¬ unitAt ξ q (ratEval x c' (MvPolynomial.X ⟨(), c⟩ * H)) := by
  intro hunit
  have ht : x c / x c' ∈ regAt ξ q := hc'.2 c
  have h₁ := hunit
  rw [ratEval_X_mul] at h₁
  have htu : unitAt ξ q (x c / x c') := unitAt_of_mul_left h₁ ht (ratEval_regular hc' H)
  have hcq : InChart ξ x c q := inChart_of_unitAt hc hc' htu
  have hr : a ∈ regAt ξ q := har hcq
  have hmu := Char0.unitAt_natCast hq0 hm
  have h₂ := hunit
  rw [ratEval_eq_pow_mul x hc (isHomogeneous_X_mul c hH), ratEval_X_mul, div_self hc, _root_.one_mul, hv] at h₂
  have hma : unitAt ξ q ((m : Ω) * a) :=
    unitAt_of_mul_right h₂ ((regAt ξ q).pow_mem ht _) ((regAt ξ q).mul_mem hmu.2.1 hr)
  exact hnon hcq (unitAt_of_mul_right hma hmu.2.1 hr)

end Pts

section Sep

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} {N : ℕ}

theorem exists_form_sep {x : Fin (N + 1) → Ω} {c : Fin (N + 1)} {B : Set (Cpt ξ)} {p : Cpt ξ} {a : Ω}
    (hB : ∀ q ∈ B, Char0 ξ q) (hp : Char0 ξ p) (hc : InChart ξ x c p)
    (hreg : ∀ q : Cpt ξ, Char0 ξ q → InChart ξ x c q → a ∈ regAt ξ q) (hu : unitAt ξ p a)
    (hnon : ∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a) {m d : ℕ}
    {H : MRing (fun _ : Unit => Fin (N + 1))} (hm : m ≠ 0) (hH : H.IsHomogeneous d)
    (hv : ratEval x c H = m * a) : ∃ G ∈ bdGens ξ x B, unitAt ξ p (ratEval x c G) := by
  have hmem : MvPolynomial.X ⟨(), c⟩ * H ∈ bdGens ξ x B :=
    ⟨d + 1, isHomogeneous_X_mul c hH, fun c' q hq hc' =>
      not_unitAt_form hc.1 (hB q hq) hc' (hreg q (hB q hq)) (hnon q hq) hm hH hv⟩
  refine ⟨_, hmem, ?_⟩
  rw [ratEval_X_mul, div_self hc.1, _root_.one_mul, hv]
  exact unitAt_mul (Char0.unitAt_natCast hp hm) hu

end Sep

theorem exists_bdGens_unitAt : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) (B : Set (Cpt ξ)) (p : Cpt ξ) (a : Ω), (∀ q ∈ B, Char0 ξ q) → Char0 ξ p → InChart ξ x c p → a ∈ Mdl.chartQ x c → unitAt ξ p a → (∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a) → ∃ G ∈ Mdl.bdGens ξ x B, unitAt ξ p (Mdl.ratEval x c G) := by
  intro Ω _ _ X ξ N x c B p a hB hp hc ha hu hnon
  obtain ⟨m, d, H, hm, hH, hv⟩ := exists_form x hc.1 ha
  exact exists_form_sep hB hp hc (fun q hq hcq => chartQ_le hq hcq ha) hu hnon hm hH hv

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.Sep
