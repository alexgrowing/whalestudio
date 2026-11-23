import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtAlong
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistNZ

theorem mem_nz_iff {Y : Scheme.{0}} {H : LB Y} (s : LB.Sec H) (k : H.ι)
    {x : Y} (hk : x ∈ H.U k) : x ∈ nonzeroLocus s ↔ x ∈ Y.basicOpen (s.f k) := by
  refine ⟨fun hx => ?_, fun hx => TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx⟩⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have e := congrArg Y.basicOpen (s.compat k l)
  rw [Scheme.basicOpen_mul, Y.basicOpen_of_isUnit (H.g k l).isUnit] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ H.U k ⊓ H.U l := ⟨hk, Y.basicOpen_le _ hl⟩
  exact (e.ge ⟨hx', hx', hl⟩).2

theorem twistPull_nonzero : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}, L.IsLB → ∀ {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)), IsTwistPull A L ψ m hm a b α s s' → ∀ p : (T ⊗ A).left, ψ.left.base p ∈ nonzeroLocus s → p ∈ nonzeroLocus s' := by
  intro S A _ L hL T ψ m hm a b α s s' H p hp
  have hcov : ∀ y : A.left, ∃ i, y ∈ L.U i := fun y => by
    have : y ∈ (⨆ i, L.U i : A.left.Opens) := by rw [hL.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  obtain ⟨i0, h0⟩ := hcov ((snd T A).left.base p)
  obtain ⟨i1, h1⟩ := hcov (m.left.base p)
  let j : Fin 2 → L.ι := ![i0, i1]
  have e₀ : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  have hpj : p ∈ LB.wchart L ![(snd T A).left, m.left] j := by
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · exact h0
    · exact h1

  have hψ : ψ.left.base p ∈ (LPow A L b T).U (fun _ => j 1) := by
    refine Set.mem_iInter.2 fun _ => ?_
    show ((snd T A).left.base (ψ.left.base p)) ∈ (L.U i1 : Set A.left)
    have : (ψ.left ≫ (snd T A).left).base p = m.left.base p := by rw [e₀]
    rw [Scheme.Hom.comp_base, TopCat.comp_app] at this
    rw [this]; exact h1
  have h2 : ψ.left.base p ∈ (T ⊗ A).left.basicOpen (s.f (fun _ => j 1)) :=
    (mem_nz_iff s _ hψ).1 hp
  have h3 : p ∈ (T ⊗ A).left.basicOpen ((ψ.left.app _).hom (s.f (fun _ => j 1))) := by
    rw [← Scheme.preimage_basicOpen]; exact h2
  have e := congrArg (T ⊗ A).left.basicOpen (H j)
  dsimp only at e
  erw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (α.s j).isUnit] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hp4 := e.ge ⟨hpj, hpj, h3⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨_, hp4.2⟩

end GlobalTheory.TwistNZ
