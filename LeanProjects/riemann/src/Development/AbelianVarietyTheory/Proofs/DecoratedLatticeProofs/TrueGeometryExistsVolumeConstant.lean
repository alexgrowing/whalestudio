import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevSph
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLevelSphericalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometrySubspacePropertyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainBoundStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanLevelVolumeMulRelIndexStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexPreimagePiEqProdStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLSplitPlaceOfCarriesLatticeCompletioStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualStabilizerWithPrescribedSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLocHom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

noncomputable section

theorem GlobalTheory.TopVol.main : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∃ VT : ℂ, VT ≠ 0 ∧ ∀ t (J : QJ a t), J.Reads → J.VolT VT := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT
  obtain ⟨hle, hc, ho⟩ := GlobalTheory.T.true_geometry_level_spherical W hW u a ha haT
  have hv := GlobalTheory.T.true_geometry_subspace_property W hW u a ha haT _ hle hc ho
  refine ⟨(volLev a.g.volT (levSph W a.g.bT) : ℂ), Complex.ofReal_ne_zero.2 hv, fun t J hJ => ?_⟩
  have hA := GlobalTheory.T.true_geometry_twist_chain_identity W hW u a ha haT t J hJ
  have hK := GlobalTheory.T.true_geometry_twist_chain_bound W hW u a ha haT t J hJ
  have hM := GlobalTheory.T.true_geometry_twist_chain_relation W hW u a ha haT t J hJ
  have hinj := GlobalTheory.T.injective_QJ_G_q_v W hW u a ha haT t J hJ
  set S := (I.rec7 l Z).sp.X'
  set U := levSph W a.g.bT
  set U' := levTw W a.g.bT t
  let Jf : (i : Fin J.r) → Subgroup (GL _ (J.G i).k) := fun i => ((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).levTop.J
  let φ : GA (I.rec7 l Z) S →* ((i : Fin J.r) → GL _ (J.G i).k) :=
    MonoidHom.pi fun i => GlobalTheory.LevIdx.locHom (J.G i).q S (J.G i).FT
  have hφi : ∀ g i, φ g i = GlobalTheory.LevIdx.locHom (J.G i).q S (J.G i).FT g := fun _ _ => rfl
  have hU'' : ∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i, φ g i ∈ Jf i := by
    intro g
    rw [hA g]
    refine and_congr_right fun _ => forall_congr' fun i => ?_
    refine ⟨fun h => h _ ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl), fun h x hx => ?_⟩
    rw [(GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 hx]; exact h
  have hle' : U' ≤ U := fun g hg => ((hU'' g).1 hg).1
  have hidx : U'.relIndex U = ∏ i, (Jf i).relIndex (GlobalTheory.SplitWeil.KO (J.G i).k _) := by
    refine GlobalTheory.T.relIndex_eq_prod_relIndex_of_surjective_pi φ U U' (fun i => GlobalTheory.SplitWeil.KO (J.G i).k _) Jf (fun i => (J.E i).leT) ?_ ?_ hU''
    · intro g hg i
      exact GlobalTheory.T.mem_integralGL_split_place_of_carries_latticeCompletion (J.G i).q S (J.G i).FT a.v.NT _ ⟨i, rfl⟩ (J.G i).latT g (hM g hg) _
        ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl)
    · intro x hx
      obtain ⟨g, hg, hgx⟩ := GlobalTheory.T.exists_selfDual_stabilizer_with_prescribed_splitPlace_matrices S a.v.NT ha.vis.sdT (fun i => (J.G i).k) (fun i => (J.G i).q) _
        (fun i => (J.G i).FT) hinj (fun i => (J.G i).latT) x hx
      refine ⟨g, hK g hg, funext fun i => ?_⟩
      rw [hφi]; exact ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 (hgx i)).symm
  have hU'o : IsOpen ((U'.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) := by
    have e : ((U'.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) =
        ((U.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) ∩
          ⋂ i, (fun g : GfC S => GlobalTheory.LevIdx.locHom (J.G i).q S (J.G i).FT g.1) ⁻¹' (Jf i : Set (GL _ (J.G i).k)) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      rw [hU'']
      rfl
    rw [e]
    exact ho.inter (isOpen_iInter_of_finite fun i =>
      ((J.E i).openT).preimage ((GlobalTheory.LevIdx.continuous_locHom (J.G i).q S (J.G i).FT).comp continuous_subtype_val))
  have hvol := GlobalTheory.T.archimedeanLevelVolume_mul_relIndex (I.rec7 l Z) S a.g.volT U' U hle' hle hc hU'o
  refine ⟨U', fun h => mem_levTw h, fun β => ?_⟩
  have hw : ∀ i, (J.E i).wt B.R.m (β i) = (((Jf i).relIndex (GlobalTheory.SplitWeil.KO (J.G i).k _) : ℕ) : ℂ) := by
    intro i
    have key : ∀ j (e : (J.G i).s + 1 + 1 = j) (y : (J.E i).Ch j), (J.E i).wt j y = ((J.E i).idx j : ℂ) := by
      rintro j rfl y; exact (J.E i).wt_top y
    have e2 : (J.E i).wt B.R.m (β i) = ((J.E i).idx B.R.m : ℂ) := key _ (J.G i).hs (β i)
    have e3 : (J.E i).idx B.R.m = (J.E i).idx ((J.G i).s + 1 + 1) := congrArg (J.E i).idx (J.G i).hs.symm
    rw [e2, e3, (J.E i).idx_top]
  rw [← hvol, QJ.wt]
  simp only [hw]
  rw [hidx]
  push_cast
  ring

end
