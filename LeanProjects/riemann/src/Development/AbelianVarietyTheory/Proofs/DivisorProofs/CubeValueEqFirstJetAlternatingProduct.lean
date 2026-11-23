import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingCubeProductValueFderivAtZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueConstPointsTangentEqDualFibreValueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubeJet

theorem cube_jet : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (G : Geo ν d),
    (∀ (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
      (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
      valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
        (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I) →
    ∀ (W : Fin g → ℂ) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    IsD ν d W gm.b → ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      1 + TrivSqZeroExt.inr
        (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex (x + y))).left)) (x + y) W / G.frG (ν.J (ν.eA (d.ex (x + y))).left) (x + y) +
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W / G.frG (ν.J (ν.eA (d.ex 0)).left) 0 -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex x)).left)) x W / G.frG (ν.J (ν.eA (d.ex x)).left) x -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex y)).left)) y W / G.frG (ν.J (ν.eA (d.ex y)).left) y) := by
  intro R _ _ D _ N g ν d G hprod W gm h0 hD χ χ' x y hx hy
  obtain ⟨U, f, hv, hU0, hUz⟩ := GlobalTheory.T.cubeValue_constPoints_tangent_eq_dualFibreValue ν d gm h0 χ χ' x y hx hy
  rw [hv, hD U f hU0]
  have hO : IsOpen {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} := (G.hol U f).1
  have hFeq : (fun z => valF (ptB ν d z) U f) =ᶠ[nhds 0] fun z => ∏ I : thK.{0},
      G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I := by
    filter_upwards [hO.mem_nhds hU0] with z hz
    obtain ⟨hI, hval⟩ := hUz z hz
    rw [hval]
    exact hprod x y z _ hI
  have hopen : ∀ i, IsOpen {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ D.P.L.U i} := fun i => by
    have e : ∀ z, (ν.eA (d.ex z)).left = ptB ν d z ≫ (DegPre.prB D ℂ).left := fun z => by
      rw [ptB, DegPre.prB, ← Over.comp_left, lift_snd]
    have := (G.hol ((DegPre.prB D ℂ).left ⁻¹ᵁ D.P.L.U i) 0).1
    simpa only [e, Scheme.Hom.comp_preimage] using this
  have hd : ∀ I : thK.{0}, DifferentiableAt ℂ (G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left))
      (∑ i ∈ I.down, ![x, y, 0] i) := fun I =>
    (G.fr_hol _).differentiableAt ((hopen _).mem_nhds (ν.good _))
  have hn : ∀ I : thK.{0}, G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)
      (∑ i ∈ I.down, ![x, y, 0] i) ≠ 0 := fun I => by
    rw [← G.fr_eq]
    exact mul_ne_zero (Units.ne_zero _) (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  have hpair : ∀ I : thK.{0}, 2 ∉ I.down →
      G.frG (ν.J (ν.eA (d.ex (∑ i ∈ (insert 2 I.down), ![x, y, 0] i))).left) =
        G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left) := fun I h2 => by
    rw [Finset.sum_insert h2]
    simp
  obtain ⟨h1, h2⟩ := GlobalTheory.T.alternatingCubeProduct_value_fderiv_at_zero x y W (fun I : thK.{0} => G.frG (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)) _
    hFeq hd hn hpair
  rw [h1, h2]
  simp [Finset.sum_insert]

end GlobalTheory.MBLow.Cl.CubeJet
