import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToH0BijectiveOfInitial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormAlternating
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DFormMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IndexZeroForallOfExtend
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.VanishingOfLadder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison.Pb

theorem loc_gr : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (r : ℤ)
    (hQ : ∀ r' ≤ r + 1, Q.Crit Fil r') (j : ℕ),
    (r < j → Subsingleton (CH.H (gr Fil r) j)) ∧
    ∀ q : ℕ, r = j + q →
      (∀ c : CH.H (gr Fil r) j, ∃ x : Idx j d → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) ∧
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j d, E.form σ I.1 (x I) s) c) ∧
      ∀ x : Idx j d → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) →
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j d, E.form σ I.1 (x I) s) 0 → ∀ I, x I ∈ (Fil ((q : ℤ) + 1)).S E.D := @GlobalTheory.CompanionTheory.LocGrInd.loc_gr

theorem loc_van : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {a b : ℤ → IdF Φ.A}
    {d : ℕ} (E : Frame Φ d) (r : ℤ) (hQ : Q.Ladder a b r),
    (∀ r', r - d ≤ r' → r' ≤ r → (a r').S E.D ≤ (b r').S E.D) → ∀ j, Subsingleton (CH.H (sq (a r) (b r)) j) :=
  by intro R _ C _ Φ Q a b d E r hQ h; exact vanishing_of_ladder d Q E r hQ h

theorem loc_bc : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {Φ : PDF R C} {Φ' : PDF R' C'} (m : SMor Φ Φ' (algebraMap R R')) (Q : Poly Φ) (Q' : Poly Φ') {d : ℕ} (E : Frame Φ d)
    (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e) (hρ : ∀ T, Function.Injective (m.ρ T)) {ι : Type} [Fintype ι] [DecidableEq ι] (N : ι → Type)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] [∀ i, Module.Flat R (N i)] (ν : ∀ i, N i →ₗ[R] R')
    (a b : ι → ℤ → IdF Φ.A) (a' b' : ℤ → IdF Φ'.A) (r : ℤ) (hQ : ∀ i, Q.Ladder (a i) (b i) r) (hQ' : Q'.Ladder a' b' r)
    (ha : ∀ i n r', m.LeC (ν i n) (a i r') (a' r')) (hb : ∀ i n r', m.LeC (ν i n) (b i r') (b' r')),
    (∀ r', r - d ≤ r' → r' ≤ r → Tens R (N := N) (M := fun i => (sq (a i r') (b i r')).obj E.D) (M' := (sq (a' r') (b' r')).obj E'.D)
      fun i n x => (m.sqC (ν i n) (ha i n r') (hb i n r')).τ E'.D (((sq (a i r') (b i r')).map e).hom x)) →
    ∀ j, Tens R (N := N) (M := fun i => CH.H (sq (a i r) (b i r)) j) (M' := CH.H (sq (a' r) (b' r)) j)
      fun i n x => (m.sqC (ν i n) (ha i n r) (hb i n r)).pull j x := @GlobalTheory.CompanionTheory.LocBC.local_base_change

end CrystallineSemistableComparison.Pb
