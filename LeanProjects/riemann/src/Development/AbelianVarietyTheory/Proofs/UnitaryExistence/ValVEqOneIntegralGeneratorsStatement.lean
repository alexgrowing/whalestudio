import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValVEqOneIntegralGenerators
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valV_eq_one_integral_generators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y y' : FrPt Xo c T.Fr) (G G₂ : SAB H (Sp T.V)) (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t y.x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t₂ Xo.univ.t y'.x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), y'.x = y.x → k.φ ≫ n₁.φ = m₁.φ → m₂.φ ≫ n.φ = k.φ ≫ n₂.φ → ∀ (θ : LB.Sec G.PP.L) (θ₂ : LB.Sec G₂.PP.L), ((∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m₁.φ)) (w2 : LB.Iso t.PP.L (G.PP.L.pull m₂.φ)) (σ : LB.Sec t.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m₁.φ)) (θ2 : LB.Sec (G.PP.L.pull m₂.φ)), RigIso m₁ w1 ∧ RigIso m₂ w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m₂.φ θ θ2 ∧ ∀ g : t.G.left ⟶ Gx y.x, g ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = m₁.φ → g ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = t.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m₁.φ).U j ≤ g ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (y.s.f (fun _ => j PUnit.unit))) → ((∀ σ : LB.Sec G₂.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G₂.G.left (le_top : G₂.PP.L.U i ≤ ⊤) ((G₂.G.hom).appTop.hom (toΓ T.V a)) * θ₂.f i) ∧ ∃ (w1 : LB.Iso t₂.PP.L (Xo.univ.t.PP.L.pull n₁.φ)) (w2 : LB.Iso t₂.PP.L (G₂.PP.L.pull n₂.φ)) (σ : LB.Sec t₂.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull n₁.φ)) (θ2 : LB.Sec (G₂.PP.L.pull n₂.φ)), RigIso n₁ w1 ∧ RigIso n₂ w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec n₂.φ θ₂ θ2 ∧ ∀ g : t₂.G.left ⟶ Gx y'.x, g ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = n₁.φ → g ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = t₂.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull n₁.φ).U j ≤ g ⁻¹ᵁ (PPx y'.x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (y'.s.f (fun _ => j PUnit.unit))) → ∀ a : T.Frˣ, SecBC (RingHom.id T.Fr) (a : T.Fr) y.x y'.x y.s y'.s → valV T.V (a : T.Fr) = 1 := by
  first | exact @GlobalTheory.IntegralGenerator.valV_eq_one | exact GlobalTheory.IntegralGenerator.valV_eq_one | (intros; apply GlobalTheory.IntegralGenerator.valV_eq_one <;> assumption)
