import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalSchemeCoordsInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.ChartHol

open Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt GlobalTheory.HolHom GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

theorem diffOn_div {f g : V → ℂ} {s : Set V} (hf : DifferentiableOn ℂ f s) (hg : DifferentiableOn ℂ g s)
    (h0 : ∀ b ∈ s, g b ≠ 0) : DifferentiableOn ℂ (fun b => f b / g b) s :=
  (hf.mul (hg.inv h0)).congr fun b _ => by simp [div_eq_mul_inv]

theorem holAt_of_isAffineOpen {N : Set V} {c : V → (Sp ℂ ⟶ X)} {A : X.Opens} (hA : IsAffineOpen A) (hN : IsOpen N)
    (hin : ∀ b ∈ N, ⊤ ≤ c b ⁻¹ᵁ A) (hz : ∀ r : Γ(X, A), DifferentiableOn ℂ (fun b => valAt' (c b) A r) N)
    {b₀ : V} (hb₀ : b₀ ∈ N) : HolAt c b₀ := by
  intro U hU
  have hmU : (c b₀) (default : PrimeSpectrum ℂ) ∈ U := (le_preimage_iff _ _).1 hU
  have hmA : (c b₀) (default : PrimeSpectrum ℂ) ∈ A := (le_preimage_iff _ _).1 (hin b₀ hb₀)
  obtain ⟨r, hrU, hr0⟩ := hA.exists_basicOpen_le (V := U) ⟨_, hmU⟩ hmA
  set M := {b ∈ N | valAt' (c b) A r ≠ 0} with hMdef
  have hMo : IsOpen M := (hz r).continuousOn.isOpen_inter_preimage hN isOpen_ne
  have hD : ∀ b ∈ M, ⊤ ≤ c b ⁻¹ᵁ X.basicOpen r := fun b hb =>
    (le_basicOpen_iff (c b) (hin b hb.1) r).2 hb.2
  have hb0M : b₀ ∈ M := ⟨hb₀, (le_basicOpen_iff (c b₀) (hin b₀ hb₀) r).1 ((le_preimage_iff _ _).2 hr0)⟩
  refine ⟨?_, fun f => ?_⟩
  · filter_upwards [hMo.mem_nhds hb0M] with b hb
    exact (hD b hb).trans (Scheme.Hom.preimage_mono _ hrU)
  · haveI := hA.isLocalization_basicOpen r
    obtain ⟨⟨hh, s⟩, hk⟩ := IsLocalization.surj (Submonoid.powers r) (X.presheaf.map (homOfLE hrU).op f)
    obtain ⟨k, hks⟩ := s.2
    dsimp only at hk
    have hval : ∀ b ∈ M, valAt' (c b) U f * valAt' (c b) A r ^ k = valAt' (c b) A hh := by
      intro b hb
      have e := congrArg (valAt' (c b) (X.basicOpen r)) hk
      rw [valAt'_mul, valAt'_res (c b) hrU (hD b hb)] at e
      have e2 : ∀ x : Γ(X, A), valAt' (c b) (X.basicOpen r) (algebraMap Γ(X, A) Γ(X, X.basicOpen r) x) =
          valAt' (c b) A x := fun x => valAt'_res (c b) (X.basicOpen_le r) (hD b hb) x
      rw [e2, e2, ← hks] at e
      have e3 : valAt' (c b) A (r ^ k) = valAt' (c b) A r ^ k := map_pow (valHom (c b) A (hin b hb.1)) r k
      rw [e3] at e
      exact e
    have h1 : DifferentiableOn ℂ (fun b => valAt' (c b) A hh) M := (hz hh).mono fun b (hb : b ∈ M) => hb.1
    have h2 : DifferentiableOn ℂ (fun b => valAt' (c b) A r) M := (hz r).mono fun b (hb : b ∈ M) => hb.1
    have h3 : DifferentiableOn ℂ (fun b => valAt' (c b) A hh / valAt' (c b) A r ^ k) M :=
      diffOn_div h1 (h2.fun_pow k) fun b hb => pow_ne_zero _ hb.2
    refine ((h3.congr fun b hb => ?_).differentiableAt (hMo.mem_nhds hb0M))
    rw [eq_div_iff (pow_ne_zero _ hb.2)]
    exact hval b hb

variable {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

theorem genMap_germ {A : X.Opens} (hg : genPt ξ ∈ A) (q : Cpt ξ) (hq : q.1 ∈ A) (r : Γ(X, A)) :
    genMap ξ q (X.presheaf.germ A q.1 hq r) =
      (X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ).hom r := by
  have h1 := X.presheaf.germ_stalkSpecializes (U := A) (y := q.1) hq q.2
  have h3 : X.presheaf.germ A q.1 hq ≫ (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) =
      X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) h1)
  exact congrArg (fun f => f.hom r) h3

theorem valAt_section (hall : ∀ q : X, genPt ξ ⤳ q) {A : X.Opens} (hg : genPt ξ ∈ A) (r : Γ(X, A))
    {z : Sp ℂ ⟶ X} (hz : ⊤ ≤ z ⁻¹ᵁ A) :
    ValAt ξ z ((X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ).hom r) (valAt' z A r) := by
  have hc : centre z ∈ A := (le_preimage_iff z A).1 hz
  refine ⟨hall _, X.presheaf.germ A (centre z) hc r, genMap_germ hg ⟨centre z, hall _⟩ hc r, ?_⟩
  rw [valAt'_of _ _ hz]
  exact congrArg (fun φ => φ.hom r) (GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap z A hz)

theorem exists_hol_value (hall : ∀ q : X, genPt ξ ⤳ q) {N : Set V} {β : V → (Σ k, J k) → ℂ} {ζ : V → (Sp ℂ ⟶ X)}
    (c : (k : K) → J k) (hβ : ∀ p, DifferentiableOn ℂ (fun b => β b p) N)
    (hco : ∀ b ∈ N, CoordsAt ξ y (ζ b) (β b)) (hne : ∀ b ∈ N, ∀ k, β b ⟨k, c k⟩ ≠ 0) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) :
    ∃ F : V → ℂ, DifferentiableOn ℂ F N ∧ ∀ b ∈ N, ValAt ξ (ζ b) a (F b) := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    refine ⟨fun b => ∏ k, β b ⟨k, j k⟩ / β b ⟨k, c k⟩, ?_, fun b hb => ?_⟩
    · have hS : ∀ S : Finset K, DifferentiableOn ℂ (fun b => ∏ k ∈ S, β b ⟨k, j k⟩ / β b ⟨k, c k⟩) N := by
        classical
        intro S
        induction S using Finset.induction_on with
        | empty => simpa using differentiableOn_const (c := (1 : ℂ))
        | insert k S hk ih =>
          simp only [Finset.prod_insert hk]
          exact (diffOn_div (hβ _) (hβ _) fun b hb => hne b hb k).fun_mul ih
      exact hS _
    · simp only [← Finset.prod_div_distrib]
      have hS : ∀ S : Finset K, ValAt ξ (ζ b) (∏ k ∈ S, y ⟨k, j k⟩ / y ⟨k, c k⟩)
          (∏ k ∈ S, β b ⟨k, j k⟩ / β b ⟨k, c k⟩) := by
        classical
        intro S
        induction S using Finset.induction_on with
        | empty => simpa using val_one (ξ := ξ) (z := ζ b) (hall _)
        | insert k S hk ih =>
          rw [Finset.prod_insert hk, Finset.prod_insert hk]
          refine val_mul ?_ ih
          obtain ⟨r, hr, hr'⟩ := ((hco b hb).2 k (c k) (isUnit_iff_ne_zero.2 (hne b hb k))).2 (j k)
          rwa [hr', mul_div_cancel_right₀ _ (hne b hb k)]
      exact hS _
  | algebraMap n =>
    refine ⟨fun _ => (n : ℂ), differentiableOn_const _, fun b _ => ?_⟩
    exact ⟨hall _, (n : X.presheaf.stalk (centre (ζ b))), by simp, map_intCast _ n⟩
  | add a a' _ _ h h' =>
    obtain ⟨F, hF, hv⟩ := h
    obtain ⟨F', hF', hv'⟩ := h'
    exact ⟨fun b => F b + F' b, hF.fun_add hF', fun b hb => val_add (hv b hb) (hv' b hb)⟩
  | mul a a' _ _ h h' =>
    obtain ⟨F, hF, hv⟩ := h
    obtain ⟨F', hF', hv'⟩ := h'
    exact ⟨fun b => F b * F' b, hF.fun_mul hF', fun b hb => val_mul (hv b hb) (hv' b hb)⟩

theorem isHolTo_of_coordsAt (htie : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hall : ∀ q : X, genPt ξ ⤳ q) {B : Set V} {β : V → (Σ k, J k) → ℂ} {ζ : V → (Sp ℂ ⟶ X)} (hB : IsOpen B)
    (hβ : ∀ p, DifferentiableOn ℂ (fun b => β b p) B) (hco : ∀ b ∈ B, CoordsAt ξ y (ζ b) (β b)) :
    IsHolTo B ζ := by
  refine isHolTo_of_holAt hB fun b₁ hb₁ => ?_
  choose c hc using (hco b₁ hb₁).1
  set N := {b ∈ B | ∀ k, β b ⟨k, c k⟩ ≠ 0} with hNdef
  have hNB : N ⊆ B := fun b hb => hb.1
  have hNo : IsOpen N := by
    refine isOpen_iff_mem_nhds.2 fun b hb => ?_
    have hk : ∀ᶠ t in 𝓝 b, ∀ k, β t ⟨k, c k⟩ ≠ 0 := eventually_all.2 fun k =>
      ((hβ _).continuousOn.continuousAt (hB.mem_nhds hb.1)).eventually_ne (hb.2 k)
    filter_upwards [hB.mem_nhds hb.1, hk] with t h1 h2 using ⟨h1, h2⟩
  have hb₁N : b₁ ∈ N := ⟨hb₁, fun k => (hc k).ne_zero⟩
  have hx0 : (∏ k, y ⟨k, c k⟩) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => ((hco b₁ hb₁).2 k (c k) (hc k)).1
  obtain ⟨A, hA, hAq⟩ := htie.affine c hx0
  have hin : ∀ b ∈ N, ⊤ ≤ ζ b ⁻¹ᵁ A := fun b hb =>
    (le_preimage_iff _ _).2 ((hAq _).2 ⟨hall _, in_chart (hall _) (hco b hb.1) hb.2⟩)
  have hg : genPt ξ ∈ A := (hall _).mem_open A.2 ((le_preimage_iff _ _).1 (hin b₁ hb₁N))
  refine holAt_of_isAffineOpen hA hNo hin (fun r => ?_) hb₁N
  have ha := (htie.ring c hx0 ((X.presheaf.germ A (genPt ξ) hg ≫ Scheme.stalkClosedPointTo ξ).hom r)).2
    fun p hp => ⟨_, genMap_germ hg p ((hAq _).2 ⟨p.2, hp⟩) r⟩
  obtain ⟨F, hF, hFv⟩ := exists_hol_value hall c (fun p => (hβ p).mono hNB) (fun b hb => hco b hb.1)
    (fun b hb => hb.2) ha
  refine hF.congr fun b hb => ?_
  exact val_unique htie.gen (valAt_section hall hg r (hin b hb)) (hFv b hb)

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.ChartHol
