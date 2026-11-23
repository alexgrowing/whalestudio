import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.ArchRep

theorem exists_local_quot {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : LB X} (ψ : GlobalTheory.Weight q σ L) (r : L.ι → X.functionFieldˣ) (y : GlobalTheory.CxPts q σ) :
    ∃ (W : X.Opens) (b : L.ι) (a d : Γ(X, W)) (h : genericPoint X ∈ W),
      y ∈ ptsIn q σ W ∧ W ≤ L.U b ∧ fnOf W h d ≠ 0 ∧
        (r b : X.functionField) * fnOf W h d = fnOf W h a := by
  have hb := mem_pick ψ.isLB y
  obtain ⟨W, hW, hyW, hWb⟩ := exists_isAffineOpen_mem_and_subset (mem_ptsIn.1 hb)
  have hg : genericPoint X ∈ W := gen_mem hyW
  haveI : Nonempty W := ⟨⟨_, hg⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X W hW
  obtain ⟨a, d, hd, e⟩ := IsFractionRing.div_surjective (A := Γ(X, W)) (r (pick ψ.isLB y) : X.functionField)
  have hd0 : fnOf W hg d ≠ 0 := by
    have : algebraMap Γ(X, W) X.functionField d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    exact this
  refine ⟨W, pick ψ.isLB y, a, d, hg, mem_ptsIn.2 hyW, hWb, hd0, ?_⟩
  rw [← e]
  change algebraMap Γ(X, W) X.functionField a / algebraMap Γ(X, W) X.functionField d * fnOf W hg d = _
  have e' : algebraMap Γ(X, W) X.functionField d = fnOf W hg d := rfl
  have e'' : algebraMap Γ(X, W) X.functionField a = fnOf W hg a := rfl
  rw [e', e'', div_mul_cancel₀ _ hd0]

theorem logNorm_of_quot {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : LB X} (ψ : GlobalTheory.Weight q σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r)
    {W : X.Opens} {b : L.ι} {a d : Γ(X, W)} {h : genericPoint X ∈ W} (hWb : W ≤ L.U b)
    (e : (r b : X.functionField) * fnOf W h d = fnOf W h a) {y : GlobalTheory.CxPts q σ} (hy : y ∈ ptsIn q σ W)
    (ho : y ∈ offSupp q σ (divOfRatSec ψ.isLB hr)) (hd : ev q σ W d y ≠ 0) :
    GlobalTheory.Cartier.logNorm ψ r y = Real.log ‖ev q σ W a y‖ - Real.log ‖ev q σ W d y‖ - ψ.φ b y / 2 := by
  have hb : y ∈ ptsIn q σ (L.U b) := mem_ptsIn.2 (hWb (mem_ptsIn.1 hy))
  have hu := IsRatSec.unitAt ψ.isLB hr ho hb
  have hv : ratVal (r b : X.functionField) y ≠ 0 := ratVal_ne_zero hu
  have ev' : ratVal (r b : X.functionField) y * ev q σ W d y = ev q σ W a y := by
    rw [← ratVal_fnOf hy h d, ← ratVal_mul hu.regAt (regAt_fnOf (mem_ptsIn.1 hy) h d), e, ratVal_fnOf hy]
  rw [logNorm_eq ψ hr ho hb, ← ev', norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 hv) (norm_ne_zero_iff.2 hd)]
  ring

theorem logNorm_finite_rep {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    [CompactSpace (GlobalTheory.CxPts q σ)] {L : LB X} (ψ : GlobalTheory.Weight q σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) :
    ∃ (N : ℕ) (W : Fin N → X.Opens) (b : Fin N → L.ι) (a d : ∀ l, Γ(X, W l)),
      (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) ∧ (∀ l, W l ≤ L.U (b l)) ∧
      (∀ l, ∃ h : genericPoint X ∈ W l, fnOf (W l) h (d l) ≠ 0) ∧
      ∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ offSupp q σ (divOfRatSec ψ.isLB hr) → ev q σ (W l) (d l) y ≠ 0 →
        GlobalTheory.Cartier.logNorm ψ r y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2 := by
  choose W₀ b₀ a₀ d₀ h₀ hy₀ hWb₀ hd₀ e₀ using exists_local_quot ψ r
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => ptsIn q σ (W₀ y))
    (fun y => isOpen_ptsIn _) fun y _ => Set.mem_iUnion.2 ⟨y, hy₀ y⟩
  let c : Fin t.card → GlobalTheory.CxPts q σ := fun l => (t.equivFin.symm l).1
  refine ⟨t.card, fun l => W₀ (c l), fun l => b₀ (c l), fun l => a₀ (c l), fun l => d₀ (c l), fun y => ?_,
    fun l => hWb₀ _, fun l => ⟨h₀ _, hd₀ _⟩, fun l y hy ho hd => logNorm_of_quot ψ hr (hWb₀ _) (e₀ _) hy ho hd⟩
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨t.equivFin ⟨z, hz⟩, ?_⟩
  simpa [c] using hyz

end GlobalTheory.CompanionTheory.MixZ.ArchRep
