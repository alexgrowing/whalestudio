import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPolarizationFormPrimitive
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_polarization_form_primitive : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.ConjugateFiltration → GlobalTheory.Published.CubeTheorem → ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (hK : (p : K) = 0) (A : Over (Sp K)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A), SmoothOfRelativeDimension g A.hom → ∀ P : LB (A ⊗ A).left, IsDual A A P → LBIso (swap P) P → ∀ (ψ : HdR A →ₗ[K] HdR A →ₗ[K] K) (β : primDR A →ₗ[K] HdR A), IsCorrForm (dp0 K) (𝟙 _) A A P ψ → (∀ s y, ψ (β s) y = y s) → ∀ (e : GlobalTheory.Published.DeRhamVectorExtension.Family p) (ε : ℤˣ), e.Filtered → e.Tangent → GlobalTheory.Published.BarsottiTateDieudonne.WeilCompatible e ε → ∀ (hn : IsNilpotent (p : K)) (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A) (w : 𝒜 ⟶ 𝒜.dual), IsWeilHom t t P w → Function.Bijective (vecExtMap w) ∧ ∀ (y : 𝒜.dual.RigExt) (b : CartierDual K (𝒜.A 1)), 𝒜.dual.IsConnecting (𝒜.dual.rigToExt y) b → ∀ (η' : 𝒜.omega) (a : 𝒜.A 1), dUnit K a = η'.1 1 → β ((e hn hA t).symm (rigExtMap w y)) ((e hn hA t).symm (𝒜.rigOfOmega η')) = (-ε) • b a := by
  first | exact @GlobalTheory.HodgeWeil.vecExtMap_bijective_and_pairing | exact GlobalTheory.HodgeWeil.vecExtMap_bijective_and_pairing | (intros; apply GlobalTheory.HodgeWeil.vecExtMap_bijective_and_pairing <;> assumption)
