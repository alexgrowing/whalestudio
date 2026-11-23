import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSubgroupAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesUnder
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GlMemLevelStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevOnto
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u}
theorem pl_eq_of_quadratic_data_same_place (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) {t t₂ : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (hJ : J.Reads) (J₂ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₂)
    (hJ₂ : J₂.Reads) (i : Fin J.r) (i₂ : Fin J₂.r) (h : (J.G i).q.v = (J₂.G i₂).q.v) : J.pl i = J₂.pl i₂ := by
  have h1 := (_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hTr t J hJ).2 i
  have h2 := (_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hTr t₂ J₂ hJ₂).2 i₂
  exact hW.pk.sel _ _ ⟨t, J.mem i⟩ ⟨t₂, J₂.mem i₂⟩ (h1.symm.trans (h.trans h2))
theorem locHom_gl_eq_self_of_map_pr_eq (j : ℕ) {PP} (h₁ h₂ : _root_.GlobalTheory.Fam.QAllAlt W PP) (hj₁ : j ≤ (a.Q PP h₁).s + 1) (hj₂ : j ≤ (a.Q PP h₂).s + 1)
    (gl : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (a.Q PP h₂).k →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (hgl : ∀ y, (mt _ (gl y)).map (a.Q PP h₂).q.pr = ((a.Q PP h₂).FX j hj₂).β * y.val * ((a.Q PP h₂).FX j hj₂).γ) (y) :
    GlobalTheory.LevIdx.locHom (a.Q PP h₁).q _ ((a.Q PP h₁).FX j hj₁) (gl y) = y :=
  ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 (hgl y)).symm
end GlobalTheory.LevOnto
end
namespace GlobalTheory.LevOnto
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u}
theorem gl_mem_relax_of_supp_at_and_map_pr (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 2 ≤ B.R.m) {t t₂ : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (hJ : J.Reads)
    (α : J.Ch j) (J₂ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₂) (hJ₂ : J₂.Reads) (i : Fin J₂.r)
    (gl : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J₂.G i).k →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (hgl : ∀ y, SuppAt (J₂.G i).q.e _ (gl y) ∧ (mt _ (gl y)).map (J₂.G i).q.pr =
      ((J₂.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj; omega)).β * y.val * ((J₂.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj; omega)).γ)
    (y) (hy : y ∈ KO (J₂.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)) : gl y ∈ _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α := by
  have hAt : ∀ P : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop, P (J₂.G i).q.v → gl y ∈ GlobalTheory.FinPl.grpAt _ P :=
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ _ _ _ (hgl y).1
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hAt (· = (J₂.G i).q.v) rfl)⟩, ?_⟩
  · by_cases hv : _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J (J₂.G i).q.v
    · exact Subgroup.mem_sup_right (hAt _ hv)
    · exact Subgroup.mem_sup_left (_root_.GlobalTheory.T.true_geometry_lattice_open_alt W hW u a ha hTr j hj t J hJ α t₂ J₂ hJ₂ i hv gl hgl y hy)
  · rw [Subgroup.mem_comap, Subgroup.mem_pi]
    intro i' _
    show GlobalTheory.LevIdx.locHom (J.G i').q _ ((J.G i').FX j _) (gl y) ∈ KO (J.G i').k _
    by_cases hv : (J.G i').q.v = (J₂.G i).q.v
    · have e := _root_.GlobalTheory.LevOnto.pl_eq_of_quadratic_data_same_place hW ha hTr J hJ J₂ hJ₂ i' i hv
      have key : ∀ P (hP : P ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (hj₁ : j ≤ (a.Q P ⟨t, hP⟩).s + 1), P = J₂.pl i →
          GlobalTheory.LevIdx.locHom (a.Q P ⟨t, hP⟩).q _ ((a.Q P ⟨t, hP⟩).FX j hj₁) (gl y) ∈ KO (a.Q P ⟨t, hP⟩).k
            (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) := by
        rintro P hP hj₁ rfl
        rw [_root_.GlobalTheory.LevOnto.locHom_gl_eq_self_of_map_pr_eq j _ _ hj₁ _ gl (fun y => (hgl y).2) y]
        exact hy
      exact key _ (J.mem i') _ e
    · rw [locHom_eq_one (J₂.G i).q (J.G i').q _ _ (gl y) (hgl y).1 (Ne.symm hv)]
      exact one_mem _
theorem onto_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → J.Ch j → ∀ x : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k, (∀ i, x i ∈ KO (J.G i).k _) → ∃ g ∈ _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj, _root_.GlobalTheory.LevProd.localHomProduct J j hj g = x := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α x hx
  have hex : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j) := ⟨t, J, hJ, ⟨α⟩⟩
  have hUp : _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj = _root_.GlobalTheory.LevProd.relaxedLevelSubgroup hex.choose_spec.choose j hj hex.choose_spec.choose_spec.2.some := by
    unfold _root_.GlobalTheory.LevProd.upperLevelSubgroup
    rw [dif_pos hex]
  have hJ₀ : hex.choose_spec.choose.Reads := hex.choose_spec.choose_spec.1
  have hgl := fun i : Fin J.r => GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j)
    (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega))
  choose gl _ hglp _ using hgl
  refine ⟨((List.finRange J.r).map fun i => gl i (x i)).prod, ?_, ?_⟩
  · rw [hUp]
    apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact _root_.GlobalTheory.LevOnto.gl_mem_relax_of_supp_at_and_map_pr hW ha hTr j hj _ hJ₀ _ J hJ i (gl i) (hglp i) (x i) (hx i)
  · rw [map_list_prod, List.map_map]
    have hphi : ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj (gl i (x i)) = Pi.mulSingle i (x i) := by
      intro i
      funext i'
      show GlobalTheory.LevIdx.locHom (J.G i').q _ ((J.G i').FX j _) (gl i (x i)) = _
      by_cases h : i' = i
      · subst h
        rw [Pi.mulSingle_eq_same]
        exact ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 ((hglp i' (x i')).2)).symm
      · rw [Pi.mulSingle_eq_of_ne h]
        refine locHom_eq_one (J.G i).q (J.G i').q _ _ _ (hglp i (x i)).1 fun hv => h ?_
        exact hJ.inj (_root_.GlobalTheory.LevOnto.pl_eq_of_quadratic_data_same_place hW ha hTr J hJ J hJ i' i hv.symm)
    simp only [Function.comp_def, hphi]
    exact list_prod_mulSingle x
end GlobalTheory.LevOnto
end
