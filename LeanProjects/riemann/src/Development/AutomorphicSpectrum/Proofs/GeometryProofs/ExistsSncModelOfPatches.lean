import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroCentreOfComplex
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingDeterminesComponentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeGivesComponentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGivesChartPrimeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationsEqualBasicOpensStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothAdjoinInverseStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerBasisAdjoinInverseStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPatchBoundaryUnitsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryGeneratorUnitStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelFromLocalPatchesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryPointsCoordsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem ratEval_mem {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ} {x : Fin (N + 1) → Ω}
    {c : Fin (N + 1)} {p : Cpt ξ} (hc : InChart ξ x c p) (g : MRing (fun _ : Unit => Fin (N + 1))) :
    ratEval x c g ∈ regAt ξ p := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa using intCast_mem (regAt ξ p) a
  | add a b ha hb => simpa using (regAt ξ p).add_mem ha hb
  | mul_X a i ha =>
    simpa using (regAt ξ p).mul_mem ha (hc.2 i.2)

theorem not_unitAt_of_mem_span {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ}
    {x : Fin (N + 1) → Ω} {B : Set (Cpt ξ)} (hξ : IsCptGen ξ) {c : Fin (N + 1)} {p : Cpt ξ} (hp : p ∈ B)
    (hc : InChart ξ x c p) {g : MRing (fun _ : Unit => Fin (N + 1))} (hg : g ∈ Ideal.span (bdGens ξ x B)) :
    ¬ unitAt ξ p (ratEval x c g) := by
  induction hg using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨d, -, h⟩ := hG
    exact h c p hp hc
  | zero => simpa [unitAt] using fun h : (0 : Ω) ≠ 0 => absurd rfl h
  | add a b _ _ ha hb =>
    have := not_unitAt_add hξ (ratEval_mem hc a) (ratEval_mem hc b) ha hb
    simpa using this
  | smul a b _ hb =>
    intro h
    have e : ratEval x c (a • b) = ratEval x c a * ratEval x c b := by simp
    rw [e] at h
    exact hb (unitAt_of_mul_right h (ratEval_mem hc a) (ratEval_mem hc b))

theorem patch_invAdj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {Pt Bd : Set (Subring Ω)} {e : ℕ} {A : Subalgebra ℚ Ω}
    {z : Fin e → A} {n : ℕ} (hA : IsSncPatch Pt Bd e A z n) {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0) :
    ∃ z' : Fin e → invAdj A g, IsSncPatch Pt Bd e (invAdj A g) z' n ∧ ∀ i, (z' i : Ω) = z i := by
  let z' : Fin e → invAdj A g := fun i => ⟨z i, le_invAdj A g (z i).2⟩
  have hd := GlobalTheory.T.kaehler_basis_adjoin_inverse Ω A g hg h0 e z z' (fun _ => rfl) hA.li hA.span
  refine ⟨z', ⟨?_, GlobalTheory.T.smooth_adjoin_inverse Ω A g hg h0 hA.smooth, hA.le, hd.1, hd.2, ?_⟩, fun _ => rfl⟩
  · obtain ⟨S, hS⟩ := hA.fg
    classical
    refine ⟨insert g⁻¹ S, ?_⟩
    rw [Finset.coe_insert]
    apply le_antisymm
    · refine Algebra.adjoin_mono (Set.insert_subset_insert ?_)
      rw [← hS]
      exact Algebra.subset_adjoin
    · refine Algebra.adjoin_le (Set.insert_subset (Algebra.subset_adjoin (Set.mem_insert _ _)) ?_)
      rw [← hS]
      exact Algebra.adjoin_mono (Set.subset_insert _ _)
  · intro q hq
    obtain ⟨R, hR, hloc, hbd⟩ := hA.pts (primeUnder A g q) (Ideal.comap_isPrime _ _)
    refine ⟨R, hR, isLocAt_invAdj hg h0 hq hloc, hbd.trans ?_⟩
    exact exists_congr fun i => and_congr_right fun _ => Iff.rfl

theorem chartQ_fg {Ω : Type} [Field Ω] [Algebra ℚ Ω] {N : ℕ} (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) :
    (chartQ x c).FG :=
  ⟨(Set.finite_range (fun j => x j / x c)).toFinset, by simp⟩

theorem not_mem_primeUnder {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : Subalgebra ℚ Ω} {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0)
    {q : Ideal (invAdj A g)} (hq : q.IsPrime) : (⟨g, hg⟩ : A) ∉ primeUnder A g q :=
  not_mem_of_isPrime hg h0 hq

variable {Ω : Type} [Field Ω] [CharZero Ω] {X : Scheme.{0}} {ξ : Sp Ω ⟶ X}

theorem exists_patch {N : ℕ} {x : Fin (N + 1) → Ω} {e : ℕ} {B : Set (Cpt ξ)} (hT : CoordTie ℤ ξ x)
    (hP : ∀ p, Char0 ξ p → ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A),
      IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p))
    (c : Fin (N + 1)) (p : Cpt ξ) (hp : Char0 ξ p) (hc : InChart ξ x c p) :
    ∃ h ∈ chartQ x c, unitAt ξ p h ∧ ∃ (z : Fin e → invAdj (chartQ x c) h) (n : ℕ),
      IsSncPatch (Pts ξ) (regAt ξ '' B) e (invAdj (chartQ x c) h) z n := by
  obtain ⟨A, z, n, q, hA, hq, hl⟩ := hP p hp
  obtain ⟨I, hI, hu, hIl⟩ := GlobalTheory.T.component_gives_chart_prime Ω X ξ _ x c hT p hp hc
  obtain ⟨g, h, hg, hh, he⟩ := GlobalTheory.T.localizations_equal_basic_opens Ω A (chartQ x c) q I (regAt ξ p) hA.fg (chartQ_fg x c) hq hI hl hIl
  have hg0 : (g : Ω) ≠ 0 := fun h0 => hg (by
    have : g = 0 := Subtype.ext h0
    rw [this]; exact q.zero_mem)
  obtain ⟨z', hz', -⟩ := patch_invAdj hA g.2 hg0
  refine ⟨h, h.2, (hu h).1 hh, ?_⟩
  rw [← he]
  exact ⟨z', n, hz'⟩

theorem primePoint {κ : Type} {x : κ → Ω} {c : κ} (hT : CoordTie ℤ ξ x) (hx : x c ≠ 0) {h : Ω}
    (hh : h ∈ chartQ x c) (h0 : h ≠ 0) (q : Ideal (invAdj (chartQ x c) h)) (hq : q.IsPrime) :
    ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ unitAt ξ p h ∧
      (∀ s : invAdj (chartQ x c) h, s ∉ q ↔ unitAt ξ p (s : Ω)) ∧
      IsLocAt (invAdj (chartQ x c) h) q (regAt ξ p) := by
  obtain ⟨p, hp, hc, hu, hl⟩ := GlobalTheory.T.chart_prime_gives_component Ω X ξ κ x c hT hx (primeUnder _ h q) (Ideal.comap_isPrime _ _)
  have hhu : unitAt ξ p h := (hu ⟨h, hh⟩).1 (not_mem_primeUnder hh h0 hq)
  refine ⟨p, hp, hc, hhu, ?_, isLocAt_invAdj hh h0 hq hl⟩
  intro s
  obtain ⟨k, hk⟩ := exists_mul_pow_mem hh h0 s.2
  have hreg : (s : Ω) ∈ regAt ξ p := invAdj_le hp (fun _ => chartQ_le hp hc) hhu s.2
  rw [not_congr (mem_iff_mul_pow hh h0 hq s k ⟨_, hk⟩ rfl), hu]
  exact ⟨fun u => unitAt_of_mul_left u hreg (unitAt_pow hhu k).2.1, fun u => unitAt_mul u (unitAt_pow hhu k)⟩

theorem pointPrime {κ : Type} {x : κ → Ω} {c : κ} (hT : CoordTie ℤ ξ x) {h : Ω} (hh : h ∈ chartQ x c)
    (p : Cpt ξ) (hp : Char0 ξ p) (hc : InChart ξ x c p) (hu : unitAt ξ p h) :
    ∃ q : Ideal (invAdj (chartQ x c) h), q.IsPrime ∧
      (∀ s : invAdj (chartQ x c) h, s ∉ q ↔ unitAt ξ p (s : Ω)) ∧
      IsLocAt (invAdj (chartQ x c) h) q (regAt ξ p) := by
  haveI hloc : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hT.gen p).1
  have hmem : ∀ s : invAdj (chartQ x c) h, (s : Ω) ∈ regAt ξ p :=
    fun s => invAdj_le hp (fun _ => chartQ_le hp hc) hu s.2
  let f : invAdj (chartQ x c) h →+* regAt ξ p :=
    ((invAdj (chartQ x c) h).val : invAdj (chartQ x c) h →+* Ω).codRestrict (regAt ξ p) hmem
  have hq : (Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p))).IsPrime := inferInstance
  have hs : ∀ s : invAdj (chartQ x c) h,
      s ∉ Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p)) ↔ unitAt ξ p (s : Ω) := by
    intro s
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    constructor
    · intro hu'
      obtain ⟨b, hb⟩ := hu'.exists_right_inv
      have e1 : (s : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
      have h0 : (s : Ω) ≠ 0 := fun h0 => by simp [h0] at e1
      refine ⟨h0, hmem s, ?_⟩
      rw [inv_eq_of_mul_eq_one_right e1]
      exact b.2
    · rintro ⟨h0, -, hinv⟩
      exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  obtain ⟨I, -, hI, hIl⟩ := GlobalTheory.T.component_gives_chart_prime Ω X ξ κ x c hT p hp hc
  have e : primeUnder (chartQ x c) h (Ideal.comap f (IsLocalRing.maximalIdeal (regAt ξ p))) = I := by
    ext a
    exact not_iff_not.1 ((hs ⟨a, le_invAdj _ h a.2⟩).trans (hI a).symm)
  exact ⟨_, hq, hs, isLocAt_invAdj hh hu.1 hq (e ▸ hIl)⟩

theorem patchClause {κ : Type} {x : κ → Ω} {e : ℕ} {B : Set (Cpt ξ)} (hT : CoordTie ℤ ξ x)
    {S : Subalgebra ℚ Ω} {z : Fin e → S} {n : ℕ} (hS : IsSncPatch (Pts ξ) (regAt ξ '' B) e S z n)
    (q : Ideal S) (hq : q.IsPrime) (p : Cpt ξ) (hl : IsLocAt S q (regAt ξ p)) :
    p ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q := by
  obtain ⟨R, -, hRl, hbd⟩ := hS.pts q hq
  have hR : R = regAt ξ p := Subring.ext fun a => (hRl a).trans (hl a).symm
  subst hR
  rw [← hbd]
  constructor
  · exact fun hp => ⟨p, hp, rfl⟩
  · rintro ⟨p', hp', e'⟩
    have := GlobalTheory.T.regular_ring_determines_component X Ω ξ ℤ κ x hT p' p e'
    exact this ▸ hp'

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

namespace GlobalTheory.CompanionTheory.Ar.SncBase

open Mdl in

theorem exists_isSncModel_of_patches : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (B : Set (Cpt ξ)), CoordTie ℤ ξ x → (∀ p ∈ B, Char0 ξ p) → (∀ p, Char0 ξ p → ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A), IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p)) → ∃ bd : Ideal (MRing (fun _ : Unit => Fin (N + 1))), Cmp.IsSncModel (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) e bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) z w → (w ∈ mcPts bd ↔ ∃ h : genPt ξ ⤳ centre z, (⟨centre z, h⟩ : Cpt ξ) ∈ B) := by
  intro Ω _ _ X ξ N x e B hT hB hP
  have hcov := fun c p hp hc => exists_patch (B := B) hT hP c p hp hc
  have hsep : ∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → p ∉ B →
      ∃ G ∈ bdGens ξ x B, unitAt ξ p (ratEval x c G) := by
    intro c p hp hc hnB
    obtain ⟨h, hh, hu, z, n, hz⟩ := hcov c p hp hc
    have hcl : ∀ q : Cpt ξ, Char0 ξ q → InChart ξ x c q → unitAt ξ q h →
        (q ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ ¬ unitAt ξ q (z i : Ω)) := by
      intro q hq hcq huq
      obtain ⟨Q, hQ, hs, hl⟩ := pointPrime hT hh q hq hcq huq
      rw [patchClause hT hz Q hQ q hl]
      refine exists_congr fun i => and_congr_right fun _ => ?_
      rw [← hs (z i), not_not]
    obtain ⟨a, ha, hau, hnon⟩ := GlobalTheory.T.snc_patch_boundary_units Ω X ξ _ x c B h e n z p hT.gen hB hh hu.1 hcl hp hc hu hnB
    exact GlobalTheory.T.boundary_generator_unit Ω X ξ N x c B p a hB hp hc ha hau hnon
  refine ⟨Ideal.span (bdGens ξ x B), ?_, GlobalTheory.T.boundary_points_coords Ω X ξ N x B hT.gen hsep⟩
  refine GlobalTheory.T.snc_model_from_local_patches Ω X ξ N x e B _ hcov ?_ ?_ ?_
  · intro c hx I hI
    obtain ⟨p, a, b, d, -⟩ := GlobalTheory.T.chart_prime_gives_component Ω X ξ _ x c hT hx I hI
    exact ⟨p, a, b, d⟩
  · intro c h hx hh h0 q hq
    obtain ⟨p, hp, hc, -, hs, hl⟩ := primePoint hT hx hh h0 q hq
    exact ⟨p, hp, hc, hs, fun z n hz => patchClause hT hz q hq p hl⟩
  · intro c p hp hc
    constructor
    · intro hpB g hg
      exact not_unitAt_of_mem_span hT.gen hpB hc hg
    · intro hall
      by_contra hn
      obtain ⟨G, hG, hu⟩ := hsep c p hp hc hn
      exact hall G (Ideal.subset_span hG) hu

end GlobalTheory.CompanionTheory.Ar.SncBase
