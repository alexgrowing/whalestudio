import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTameFieldGoodLatticePotentiallyCrystallineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTDescendSmallerCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftSurjectionGoodCrystallineLatticesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmodStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffFieldContainsUnramifiedWittTameDescenStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremTClosing

section Mono

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem liftF_of_le {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {e e' : ℕ}
    (hF : F.LiftF PD e) (he : e ≤ e') : F.LiftF PD e' := by
  intro c hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact (F.ImF PD).smul_mem _ (hF c hc)

end Mono

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ C : ℕ, 40 ≤ C →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.ElementDenominator.HodgeTateFromSandwich D HW F C := by
  intro hBS hFB C hC D HW F _ l _ K' h hN hF hS LL
  have hlp : l.Prime := Fact.out
  have hl2 : 2 ≤ l := hlp.two_le
  obtain ⟨a, ha⟩ : ∃ a, a = (l - 1).factorial := ⟨_, rfl⟩
  haveI : NeZero a := ⟨by rw [ha]; exact Nat.factorial_ne_zero _⟩
  have hla : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) (by omega)
  obtain ⟨e, he⟩ : ∃ e, e + 1 = l ^ a := ⟨l ^ a - 1, by omega⟩
  haveI : NeZero e := ⟨by
    intro h0
    rw [h0, zero_add] at he
    omega⟩
  have hnd : ¬ l ∣ a := by
    rw [ha, hlp.dvd_factorial]
    omega
  obtain ⟨⟨LL', hle, hUnr⟩, -⟩ := GlobalTheory.T.exists_coeffField_containsUnramifiedWitt_tameDescent l a e he hnd LL
  haveI := hUnr
  haveI : TameDescentExponentData ↥LL'.1 l e a := (GlobalTheory.T.exists_coeffField_containsUnramifiedWitt_tameDescent l a e he hnd LL').2 hUnr
  refine GlobalTheory.T.theoremT_descend_smaller_coefficients l (D.loc l) K' h hN hF hS LL LL' hle C ?_
  have ϖ : PiSys l e := Classical.arbitrary _
  have hStd : IsStd (D.loc l) (D.locA l) := IsStd.of_tied (D.locT l)
  intro T₁ T₂ g N η H U Sig Fr hP1 hP2 hOnto hFr hFS h1 hcard h2N hIT1 hIT2 hUr hU0 hUc hη hηH hJ1 hJ2 hl
  have hp : (pc (D.loc l) h hN hF hS).PD.p = l := (D.loc l).PD_p _
  have hlarge : 40 * (H * N ^ 2 + N ^ 3) < l := lt_of_le_of_lt (Nat.mul_le_mul_right _ hC) hl
  have hNl : N < l := by
    have : N ≤ N ^ 3 := Nat.le_self_pow (by norm_num) N
    omega
  have hcop : ∀ χ ∈ Sig, Nat.Coprime (orderOf χ) l := fun χ hχ => by
    have := hIT1.2.1 χ hχ
    rwa [hp] at this
  obtain ⟨Sig', hS1, hS2, hS3, hS4, hS5⟩ := GlobalTheory.T.exists_tameField_goodLattice_potentiallyCrystalline hFB l a e ϖ LL' (D.loc l) (D.locA l) hStd ha
    K' h hN hF hS Sig Fr N hFr hFS h1 hcard hNl hIT1.1 hcop
  obtain ⟨c1, t1⟩ := hS5 T₁ hP1 hIT1
  obtain ⟨c2, t2⟩ := hS5 T₂ hP2 hIT2
  have hnum : GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig' U :=
    ⟨hS1, hS2, hS3, h2N, hUr, hU0, hUc, hη, hηH, hlarge⟩
  have hcore := GlobalTheory.T.lift_surjection_good_crystalline_lattices hBS hFB l a e ϖ LL' (D.loc l) (D.locA l) hStd N η H Sig' U hnum T₁ T₂ g hOnto
    ⟨c1, t1, hJ1⟩ ⟨c2, t2, hJ2⟩
  have horb := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a hlp (Nat.one_le_iff_ne_zero.2 (NeZero.ne a)) he Sig' N hS1 hS2 hS3 h2N
  rw [hS4] at hcore horb
  refine ⟨horb.2.1, ?_⟩
  exact liftF_of_le _ g hcore (Nat.mul_le_mul_right _ (by omega))

end GlobalTheory.TheoremTClosing
