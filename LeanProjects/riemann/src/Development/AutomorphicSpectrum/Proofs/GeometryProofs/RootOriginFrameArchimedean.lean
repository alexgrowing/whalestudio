import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem sigma_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ s : CMType H ⊕ CMType H, ∃ σ : 𝓞 E →+* T.V, (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) ∧ ∀ a, algebraMap T.V T.Fr (σ a) = io (labelEmb c s a) := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hev hG la T io e y evT zT t hI zV hR s
  have hgen := Or.𝔐.tie.gen
  have hsp : GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ ⤳ centre zV := Or.𝔐.all _
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom _ _ Or.𝔐.ξ T.V zV hsp hgen
  have hm : ∀ a : 𝓞 E, Or.𝔐.emb s a ∈ regAt Or.𝔐.ξ ⟨centre zV, hsp⟩ := fun a =>
    HodgeBasic.mem_regAt_of_isIntegral hgen Or.𝔐.all Or.𝔐.normal _
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (Or.𝔐.emb s).toIntAlgHom)
  let σ : 𝓞 E →+* T.V := φ.comp ((Or.𝔐.emb s).codRestrict _ hm)
  have hv : ∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a) := fun a => (hφ _ _).2 ⟨hm a, rfl⟩
  refine ⟨σ, hv, fun a => ?_⟩
  have hA : Or.𝔐.cst (labelEmb c s a) ∈ A := hG.1 _
  have h1 := LieTangent.valAt_base hgen (algebraMap T.V T.Fr) (hv a)
  have h2 : GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ (gen T zV) (Or.𝔐.emb s a) (evT ⟨_, hA⟩) := hR ⟨_, hA⟩
  have h5 : evT ⟨_, hA⟩ = io (labelEmb c s a) := hI.2.2.2.2.1 _ hA
  exact (LieTangent.valAt_unique hgen h1 h2).trans h5

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
