import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StatementCOfCasselmanWallachStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisExistsChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePlacesCoverStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BadPlacesSubsetRamifiedPlacesOfCmDatum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParahoricShapeTransferOfCmDatum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelUniformityOfCmDatum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsJointLevelOfCmDatum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CellWeightsAdmissibleOfCmDatum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepOfTwistExistsWithProperties
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.LevCmp
variable {D : D7}
theorem exists_level_comparison_choice_alt (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hG : IsGalois ℚ ↥D.LL0) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (M : MtFam D) (X : NExpTied D)
    (F : TwFrameC D) (xi : D.what₂.Tup → HChar D.host.E) (χ : D.what₂.places.Pl → HChar D.host.E)
    (Q : D.what₂.places.Pl → Finset (PlE D.host)) (k : D.what₂.places.Pl → ℕ) (s : D.what₂.places.Pl → D.ntw.Tw)
    (hs : ∀ v, ∃ b, ReadsAt (s v) b v) (c1 : ∀ v, s (D.what₂.places.conj v) = s v)
    (htp : ∀ C : NChoice D, C.Q = Q → ∃ tp : TupTied D cf C, tp.xi = xi ∧ tp.psi = χ)
    (h1 : ∀ v, IsPsi (H := D.host) (D.what₂.places.resChar v) (Q v) (χ v))
    (h2 : ∀ v, (χ v).OrderDvd (D.what₂.places.resChar v ^ k v))
    (h3 : ∀ v, ∃ z : D.what₂.LL, IsPrimitiveRoot z (D.what₂.places.resChar v ^ k v))
    (h4 : ∀ v, ¬ TwistedAt D v → Q v = ∅) (h5 : ∀ v, Disjoint (Q v) (D.ntw.S0 (s v)))
    (h6 : ∀ v v', (∀ x ∈ D.LL0, 0 ≤ D.what₂.places.val v x ↔ 0 ≤ D.what₂.places.val v' x) → k v = k v' ∧ χ v = χ v')
    (h7 : ∀ v, χ (D.what₂.places.conj v) = χ v ∧ k (D.what₂.places.conj v) = k v)
    (h8 : ∀ v b (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok (s v) (k v))ˣ) (hA : NX.AdmTw D (s v) (k v) (Q v) ψ) (j : Fin D.R.m),
      TwistedAt D v → D.ntw.l (s v) = D.what₂.places.resChar v → IntegralHeckeForms.TwOK (s v) (k v) (Q v) ψ → ∀ e, SideRead (s v) b (k v) e →
      ReadsHecke e ψ (χ v) →
      LevEq (mtAt M v j).J (mtAt M v j).χ (cell X b hA j).J (cx e (cell X b hA j).χ) ∧ CellWt (mtAt M v j) X b hA j e) :
    ∃ (C : NChoice D) (tp : TupTied D cf C), tp.xi = xi ∧ tp.psi = χ ∧ C.Q = Q ∧ C.k' = k ∧ ChoiceSide D cf M X C tp ∧
      (∀ v, IntegralHeckeForms.TwOK (C.twI v) (C.k' v) (C.Q v) ((C.psi' v).comp (D.ntw.art (C.twI v) (C.Q v)))) ∧ C.twI = s := by
  classical
  have hl : ∀ v, D.ntw.l (s v) = D.what₂.places.resChar v := fun v => let ⟨_, h⟩ := hs v; h.l_eq
  have hQ : ∀ v v', χ v = χ v' → Q v = Q v' := fun v v' e => Finset.ext fun u =>
    not_iff_not.1 (((h1 v).ram u).symm.trans (e ▸ (h1 v').ram u))
  let g : HChar D.host.E → ℕ → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) := fun c n =>
    @Classical.epsilon _ ⟨1⟩ fun ψ₀ => GalOf D c ψ₀ ∧ ∀ g, ψ₀ g ^ n = 1
  let ψ₀ := fun v => g (χ v) (D.ntw.l (s v) ^ k v)
  have hψ : ∀ v, GalOf D (χ v) (ψ₀ v) ∧ ∀ g, ψ₀ v g ^ (D.ntw.l (s v) ^ k v) = 1 := fun v =>
    Classical.epsilon_spec (GlobalTheory.T.exists_galoisCharacter_of_finiteOrder_heckeCharacter hP.what₂.art D (χ v) _ (pow_pos (D.ntw.lPrime _).out.pos _) (hl v ▸ h2 v) (hl v ▸ h3 v))
  have c4 : ∀ v, ψ₀ (D.what₂.places.conj v) = ψ₀ v := fun v => by simp only [ψ₀, c1, (h7 v).1, (h7 v).2]
  have hd := fun v b (ρ : Reading (s v) (k v) b v) =>
    let ⟨a1, a2, a3⟩ := _root_.GlobalTheory.T.exists_galoisRep_of_twist_of_prime hP D _ (Q v) (χ v) (ψ₀ v) (D.ntw.lPrime (s v)).out (hl v ▸ h1 v) (hψ v).1
    GlobalTheory.T.exists_ringClassGroup_descent_of_coeffFieldTwist D (s v) (k v) b v ρ (Q v) (ψ₀ v) (h1 v).split (h5 v) (hψ v).1.1 a1 (hψ v).2 a2 a3
  obtain ⟨b, ρ, ψ, hr, hp, hb, hc⟩ := exists_data hG s Q k ψ₀ hs c1 (fun v => hQ _ _ (h7 v).1) (fun v => (h7 v).2) c4
    fun v b ρ => (hd v b ρ).1
  have hok := fun v => (hd v _ (ρ v)).2 _ (hp v)
  choose ι hι using fun v => GlobalTheory.T.exists_complexEmbedding_readingFractionRing_over_coeffField D F (s v) (k v) (b v) v (ρ v)
  have hlev := fun v hA j (hv : TwistedAt D v) =>
    let ⟨a1, a2⟩ := reads_of_pulls (ρ v) (hp v) (hψ v).1 (hι v)
    h8 v (b v) _ hA j hv (hl v) (hok v) _ a1 a2
  have hrk : ∀ v, TwistedAt D v → GlobalTheory.TwistChoice.RankEq (s v) (b v) (Q v) (k v) (ψ v) v := fun v hv j j1 j2 => by
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨a1, a2⟩ := hlev v (GlobalTheory.MtRead.admissible_twist_of_twisting_character (hok v)) ⟨j, j2⟩ hv
    exact rank_of_levEq _ X _ _ ⟨j, j2⟩ _ a1 a2
  let C := GlobalTheory.TwistChoice.choiceOf s b Q k ψ hr ρ hrk
  obtain ⟨tp, t1, t2⟩ := htp C rfl
  refine ⟨C, tp, t1, t2, rfl, rfl, ⟨⟨fun a => hE.elim a, fun a => hE.elim a, fun a => hE.elim a,
    ⟨ψ₀, c4, hp, fun a => hE.elim a⟩, fun v x y z _ hx => (ρ v).emb_side x y z hx⟩,
    ⟨c1, fun v _ => (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v)).1, fun v _ x => (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v)).2.2 _ x, fun v _ => hb v,
      fun v v' _ _ e => ?_, fun v _ => hc v⟩, h4, fun v _ => GlobalTheory.MtRead.admissible_twist_of_twisting_character (hok v), ?_, ?_⟩, hok, rfl⟩
  · have e' : s v' = s v := e
    have key : k v' = k v ∧ χ v' = χ v := by
      have a1 := (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v)).1
      have a2 := (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v')).1
      have a3 := (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ ((ρ v').conj hG)).1
      rw [e'] at a2 a3
      by_cases hbb : b v' = b v
      · rw [hbb] at a2
        exact h6 _ _ fun x hx => (a2 ⟨x, hx⟩).trans (a1 ⟨x, hx⟩).symm
      · have : (!b v') = b v := by revert hbb; cases b v <;> cases b v' <;> simp
        rw [this] at a3
        have a4 := h6 _ _ fun x hx => (a3 ⟨x, hx⟩).trans (a1 ⟨x, hx⟩).symm
        exact ⟨(h7 v').2.symm.trans a4.1, (h7 v').1.symm.trans a4.2⟩
    exact pack_pow (ρ v) (ρ v') e' (hQ _ _ key.2) key.1 (by simp only [ψ₀, e', key.1, key.2]) (hl v ▸ h3 v) (hψ v).2 (hp v) (hp v')
  · intro v _ u hu _ A σ hA hσ y hy
    obtain ⟨-, art, ha, h⟩ := (hψ v).1
    have a1 := h.val_eq ha (((h1 v).ram u).2 hu) hA hσ
    have a2 : y = (ψ₀ v σ : D.what₂.LLˣ) := D.what₂.embLL.injective (by rw [hy, t2, a1, inv_inv]; rfl)
    rw [a2]
    exact hp v σ
  · intro v j j1 j2 hv hA
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨⟨a1, a2⟩, -⟩ := hlev v hA ⟨j, j2⟩ hv
    exact ⟨ι v, hι v, a1, fun κ h h' => congrArg Units.val (a2 κ h h')⟩
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
theorem stageCExists_of_harishChandra_serN : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.ThirdStageExists hL := by
  intro hCo hCW hHM hP hS hL
  refine ((_root_.GlobalTheory.T.nonGalois_exists_choice_alt hCo hCW hHM hP hS hL).and ((_root_.GlobalTheory.T.gPlaces_of_levelA hL).and (GlobalTheory.T.twistConductors_avoid_excludedPrimes.and ((_root_.GlobalTheory.T.badV_subset_gPl_union_qPl_of_admTw hP hL).and ((_root_.GlobalTheory.T.paraShape_of_twisted_sideRead_readsHecke hP hL).and ((_root_.GlobalTheory.T.level_uniformity_of_cmDatum_alt hP hL).and
    ((_root_.GlobalTheory.T.joint_level_of_cm_datum_twOK hP hL).and (_root_.GlobalTheory.T.cellWt_of_sideRead_of_twOK hP hL)))))))).trans (StepW.of_all ?_)
  rintro K B f T w - - ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ P x l s hs c1
  have hl : ∀ v, (Dof x).ntw.l (s v) = B.places.resChar v := fun v => let ⟨_, h⟩ := hs v; h.l_eq
  obtain ⟨C, tp, b1, b2, b3, b4, b5, b6, b7⟩ := _root_.GlobalTheory.LevCmp.exists_level_comparison_choice_alt (D := Dof x) hP B.coeffGaloisSubfield_isGalois l.a.A.bare (cfOf x) l.mt.M l.b.Bs.exp
    l.b.Bs.twF w.I.xi T.psi (QOf P) T.k s hs c1 (exists_tp x) (fun v => Model.qOf_eq (P := P) v ▸ T.psi_is v) T.psi_ord P.coh.roots
    (fun v hv => Model.qOf_off v fun h => hv ((Model.twisted_iff x v).2 h))
    (fun v => disjoint_conductorPlaces_excludedSet (l.b.rootsOfUnityRing_le_wittIntegers (s v)) (fun u hu h => T.Q_l v u (Model.qOf_eq (P := P) v ▸ hu) (hl v ▸ h))
      fun u hu => a2 P x v u (Model.qOf_eq (P := P) v ▸ hu))
    (fun v v' h => (P.coh.same v v' h).2) T.conj fun v b ψ hA j hv hl' hok e he hr => by
      have hg := TupTie.good_set f T (w.xi_range ▸ Set.mem_range_self ((Dof x).what₂.muTw v))
      exact ⟨levEq _ _ b hA j e he (a1 P x l.toLA)
        (fun s' ξ => GlobalTheory.T.exists_local_unit_character_nontrivial (Dof x) (cfOf x) j _ s' ξ hg.2.1 hg.2.2) (l.mt.mt.prod v j) (l.mt.mt.para v j) (l.mt.mt.uni v j)
        (l.mt.mt.hyp v j) (a3 P x l v _ b ψ hA j hv hl' hok) (a4 P x l v _ b ψ hA j hv hl' hok e he hr)
        (a5 P x l v _ b ψ hA j hv hl' hok) (a6 P x l v _ b ψ hA j hv hl' hok), a7 P x l v _ b ψ hA j hv hl' hok e he⟩
  obtain ⟨c, hc⟩ := a0 P x l C tp b1 b2 b3 (fun v _ => congrFun b4 v) b5 fun v _ => b6 v
  exact ⟨c, hc.trans b7⟩
end GlobalTheory.LevCmp
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stageCExists_of_casselmanWallach : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.ThirdStageExists hL := by
  first | exact @_root_.GlobalTheory.LevCmp.stageCExists_of_harishChandra_serN | exact _root_.GlobalTheory.LevCmp.stageCExists_of_harishChandra_serN | (intros; apply _root_.GlobalTheory.LevCmp.stageCExists_of_harishChandra_serN <;> assumption)
end
end
