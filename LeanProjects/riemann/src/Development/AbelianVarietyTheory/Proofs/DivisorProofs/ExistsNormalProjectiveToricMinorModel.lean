import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalModelThetaTupleMaximalMinorsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinGeometricOfSemistableReductionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicFieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatementsStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegrallyClosedStalkOfRingOn
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.SiegJoin

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem isUnit_of_isHom {X M : RatModel o Ω} {f : M.Z ⟶ X.Z} (hf : X.IsHom M (AlgHom.id o Ω) f) {z : M.Z} {y : Ω}
    (hy : y ∈ X.O (f z)) (hu : IsUnit (⟨y, hf.map_mem_O hy⟩ : M.O z)) : IsUnit (⟨y, hy⟩ : X.O (f z)) := by
  obtain ⟨U, a, hz, rfl⟩ := hy
  rw [RatModel.isUnit_valF_iff hz]
  have hz' : z ∈ f ⁻¹ᵁ U := hz
  have e : (⟨valF X.pt U a, hf.map_mem_O ⟨U, a, hz, rfl⟩⟩ : M.O z) =
      ⟨valF M.pt (f ⁻¹ᵁ U) (f.app U a), RatModel.valF_mem_O hz' _⟩ :=
    Subtype.ext (hf.valF_app ⟨_, hz⟩ a).symm
  rw [e, RatModel.isUnit_valF_iff hz', ← Scheme.preimage_basicOpen] at hu
  exact hu

theorem div_iff_of_isHom {X M : RatModel o Ω} {f : M.Z ⟶ X.Z} (hf : X.IsHom M (AlgHom.id o Ω) f) {J : Type}
    {t : J → Ω} (hX : X.HasDiv t) (z : M.Z) (x : J) : M.Div t x z ↔ X.Div t x (f z) := by
  obtain ⟨i, hi⟩ := hX (f z)
  have hi' : M.Div t i z := hf.div hi
  refine ⟨fun hx => ?_, fun hx => hf.div hx⟩
  rw [hi.div_iff_isUnit]
  exact isUnit_of_isHom hf (hi.2 x) ((hi'.div_iff_isUnit x).1 hx)

end GlobalTheory.SiegJoin

namespace GlobalTheory.SiegJoin

theorem minor_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω → ∃ (X M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (Zh : ZHOut ρ M U₀ EE), MinorAt S X M U₀ EE f Xab ∧ IsOpen (abLocus Zh.G) ∧ (abLocus Zh.G : Set M.Z) = f ⁻¹' (Xab : Set X.Z) := by
  intro o Ω _ _ _ _ S ρ hB hfin
  have hL := GlobalTheory.abelianSchemeLaws_all
  have hT : S.HasTests := (GlobalTheory.T.thetaSystem_hasTests_of_real_point GlobalTheory.T.semistableReduction_ppav_padicField GlobalTheory.T.uniformisationExistence_and_torsion_statements.1 hL.1 hL.2 GlobalTheory.T.uniformisationExistence_and_torsion_statements.2 o Ω S ρ).1
  obtain ⟨n, a, GG, X, M, U₀, EE, f, Xab, hNm, hP, -, hO, hE, hH, hXab, hI, hgen, -⟩ := GlobalTheory.T.exists_normal_model_theta_tuple_maximal_minors o Ω S hT hfin
  obtain ⟨Zh⟩ := GlobalTheory.T.zarhinGeometric_of_semistableReduction GlobalTheory.T.semistableReduction_ppav_padicField o Ω S ρ hB M U₀ EE hO hE ⟨n, a, GG, hgen⟩
  have hsupI : ∀ z : M.Z, S.supI M z = S.supI X (f z) := fun z =>
    Set.ext fun x => div_iff_of_isHom hH hNm.1 z x
  have key : (abLocus Zh.G : Set M.Z) = f ⁻¹' (Xab : Set X.Z) := by
    rw [Zh.ab, hXab]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ThetaSys.TT, ThetaSys.HH, hsupI z]
  refine ⟨X, M, U₀, EE, f, Xab, Zh, ⟨hNm, hP, hNm.isNormalScheme, hO, hE, hH, hXab, hI⟩, ?_, key⟩
  rw [key]
  exact Xab.isOpen.preimage f.continuous

end GlobalTheory.SiegJoin
