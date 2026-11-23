import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecFracExt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameFinalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointAbelianMapCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrPullbackSemiabelianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorLieModelLiftStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLieModelCompleteDvrStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelEigenFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelLatticeStatement

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open Limits

theorem lieEig_basis_rf : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (u : Fin (labelRk Dw s) → EC) (σ : 𝓞 E →+* T.V), (∀ i, FinRd.Roots.IsFrameVec Or io zT MC (u i) s i) → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → LinearIndependent T.Fr u ∧ ∃ yb : Fin (labelRk Dw s) → EC, FinRd.Roots.TriIn u (fun i => (t (Small.labelIx Dw ⟨s, i⟩) : T.Fr)) yb ∧ FinRd.Roots.lieEig Or MC ρC σ = Submodule.span T.V (Set.range yb) := by
  intro hGiven E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hval hA la T io e y evT zT t hI zV hR EC _ _ _ _ MC ρC hρ s u σ hu hσ
  letI := io.toAlgebra
  obtain ⟨hp, hOver, hAlg, hphi, hcst, hnorm, hsp, hBor⟩ := hI
  have hI' : FinRd.IsIntPt Fr A ev la T io e y evT zT t := ⟨hp, hOver, hAlg, hphi, hcst, hnorm, hsp, hBor⟩
  have hExt : GlobalTheory.Published.SemiAbelianHomExtension := hGiven.2.2.1
  have hξ : IsCptGen Or.𝔐.ξ := Or.𝔐.tie.gen
  have hptz : Small.ptY Y zT = FinRd.Roots.gen T zV ≫ Or.𝔐.f :=
    GlobalTheory.T.root_origin_generic_frame_final E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y evT zT t hI' zV hR
  have hpty : Small.ptY Y y.1 = FinRd.Roots.gen T zV ≫ Or.𝔐.f := by
    rw [← hptz, Small.ptY, Small.ptY]
    congr 1
    apply Limits.pullback.hom_ext
    · rw [Small.ptF_fst, Small.ptF_fst, hBor.1]
    · rw [Small.ptF_snd, Small.ptF_snd]
  obtain ⟨G, t', m1, m2, ⟨ub, htan, heig, hbasis, hlift⟩, -⟩ := y.2.2
  obtain ⟨b, hb, hbact, hbu⟩ := GlobalTheory.T.frame_point_abelian_map_compat E H Dw l Xo c O β Y Or.𝔐.X Or.𝔐.t Or.𝔐.f Or.𝔐.m T.Fr y.1 t' m1 _ hpty
  obtain ⟨Ψ, hΨ, hm2, hΨact⟩ := GlobalTheory.T.complete_dvr_pullback_semiabelian E H hExt Or.𝔐.X Or.𝔐.t T zV G t' m2 b hb hbact
  have hsig : ∀ a, algebraMap T.V T.Fr (σ a) = io (embK c (Small.labelC s) a) := fun a => by
    rw [Small.embK_labelC]
    have h1 := hA.1 (labelEmb c s a)
    have h2 := hR ⟨_, h1⟩
    have h3 := LieTangent.valAt_base hξ (algebraMap T.V T.Fr) (hσ a)
    rw [← hcst _ h1]
    exact LieTangent.valAt_unique hξ h3 h2
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  have hyb : ∀ i, ∃ w : EC, (MC.pt w).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap T.V T.Fr))) ≫
      (ub (Small.labelC s) (Small.labelFin Dw s i)).left ≫ Ψ := fun i =>
    GlobalTheory.T.tangent_vector_lie_model_lift E H Or.𝔐.X Or.𝔐.t T zV G Ψ hΨ EC MC _ (htan _ _)
  choose yb hyb using hyb
  have hybT : ∀ i, (MC.pt (yb i)).left ≫ Or.𝔐.m.φ = Small.tanY Y y.1 (Small.labelC s) (Small.labelFin Dw s i) := fun i => by
    obtain ⟨u', hu1, hu2⟩ := hlift (Small.labelC s) (Small.labelFin Dw s i)
    have hu2' : u' ≫ m2.φ = Spec.map (CommRingCat.ofHom (dualMap (algebraMap T.V T.Fr))) ≫
        (ub (Small.labelC s) (Small.labelFin Dw s i)).left := hu2
    have hbase : u' ≫ t'.G.hom = Spec.map (CommRingCat.ofHom (algebraMap T.Fr (DualNumber T.Fr))) :=
      base_eq T G t' m2 _ u' hu2'
    rw [← hbu _ _ u' hu1 hbase, hyb, ← hm2]
    simp only [Category.assoc]
    rw [← Category.assoc (Spec.map _), ← hu2']
    simp only [Category.assoc]
  have hr : labelRk Dw s = Dw.mult (Small.labelC s) := (Small.mult_labelC Dw s).symm
  have hu' : ∀ i, (MC.pt (u i)).left ≫ Or.𝔐.m.φ = Small.tanY Y zT (Small.labelC s) (Fin.cast hr i) := hu
  refine ⟨GlobalTheory.T.abelian_map_lie_model_eigen_frame E H Dw l Xo c O β Y Or.𝔐.X Or.𝔐.t Or.𝔐.f Or.𝔐.m T.Fr _ EC MC zT hptz _ _ hr u hu', yb,
    GlobalTheory.T.abelian_map_lie_model_lattice E H Dw l Xo c O β Y Or.𝔐.X Or.𝔐.t Or.𝔐.f Or.𝔐.m T.Fr _ EC MC zT hptz y.1 t hBor _ _ hr u yb hu' hybT, ?_⟩
  have hsm : AlgebraicGeometry.Smooth Or.𝔐.t.G.hom := Or.𝔐.t.semi.smooth
  refine GlobalTheory.T.eigen_lie_model_complete_dvr E H Or.𝔐.X Or.𝔐.t T zV G Ψ hΨ hΨact EC MC ρC hρ σ _ (fun i => ub (Small.labelC s) (Small.labelFin Dw s i))
    (fun i => htan _ _) (fun i a => heig _ _ a _ (hsig a)) ?_ yb hyb _ (fun w =>
      lieLat_fibAt_iff _ _ _ _ _ Or.𝔐.M T.V zV T.Fr EC MC hξ hsm (Or.𝔐.all _) (Or.𝔐.all _) w)
  intro w hw hwe
  have hw' : IsEigV c io G (Small.labelC s) w := fun a z' hz' => by
    have : z' = σ a := hinj (hz'.trans (hsig a).symm)
    rw [this]; exact hwe a
  obtain ⟨cf, hcf, -⟩ := hbasis _ w hw hw'
  exact ⟨_, isComb_cast hr _ _ _ hcf⟩

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.PositivityTheory.UnitarySelfGeneration.linearIndependent_and_exists_triIn_lieEig_eq_span : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (u : Fin (labelRk Dw s) → EC) (σ : 𝓞 E →+* T.V), (∀ i, FinRd.Roots.IsFrameVec Or io zT MC (u i) s i) → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → LinearIndependent T.Fr u ∧ ∃ yb : Fin (labelRk Dw s) → EC, FinRd.Roots.TriIn u (fun i => (t (Small.labelIx Dw ⟨s, i⟩) : T.Fr)) yb ∧ FinRd.Roots.lieEig Or MC ρC σ = Submodule.span T.V (Set.range yb) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.lieEig_basis_rf | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.lieEig_basis_rf | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.lieEig_basis_rf <;> assumption)

end
