import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyInvariance
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColNone
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamCol
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DatExistsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VolLevelWtConstStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KomExistsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsSideStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColOfReadSStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesUnderStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamOfEpsMemStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LawsRescStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QLevOfReadsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QVecPinTupStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamOfPinTupCombAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamAllQ
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZeroColOfStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsExistsStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
theorem GlobalTheory.Fam.colSide_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (k : _root_.GlobalTheory.Fam.FamilyConstants a) row, (∀ t, (row t).Is) → (∀ t t', (row t).Same (row t')) → ∃ col w₀ w F, _root_.GlobalTheory.AdForm.FamilyColumnCondition (a.fam row col) ∧ _root_.GlobalTheory.Fam.ColumnOutputCondition (a := a) k (row := row) (col := col) w₀ w F := by
  intro hDS hHC B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT hiA k row hrow hsame
  classical
  have hm : (I.rec7 l Z).R.m = B.R.m := rfl
  have hRow : ∀ col, (a.fam row col).RowOK := fun col => ⟨ha.meas, ha.last, ha.x, hrow, hsame⟩
  have hc : (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is := (_root_.GlobalTheory.T.famCh_is_and_tuples_is_of_colOK hDS hHC W u hW.pk (a.fam row _root_.GlobalTheory.Fam.trivialColumnChoice) (hRow _)).1
  choose J hJ using _root_.GlobalTheory.T.exists_quadratic_extension_reads_of_true W hW u a ha haT hc
  obtain ⟨C, hC0, hC⟩ := _root_.GlobalTheory.T.true_geometry_row_pair_relation_alt_alt_alt W hW u a ha haT hiA
  choose s ζ ρ hD using fun t => hC t (J t) (hJ t)
  obtain ⟨V, VT, hV0, hVT0, hV⟩ := _root_.GlobalTheory.T.true_geometry_exists_volume_data_alt W hW u a ha haT
  obtain ⟨kom, hkom⟩ := _root_.GlobalTheory.T.true_geometry_exists_kernel_alt W hW u a ha haT
  have hdd0 : ∀ t j α γ, ∃ d, j < B.R.m → GlobalTheory.SeeSaw.IsFinComb d ∧ ∀ f, comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ d f =
      comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((J t).dQ (s t) j α γ) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dG j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) f)) := by
    intro t j α γ
    by_cases hj : j < B.R.m
    · obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.T.true_geometry_twist_local_value_alt W hW u a ha haT t (J t) (hJ t) (s t) j α γ hj
      obtain ⟨d, hd⟩ := GlobalTheory.Fam.finComb3 _ (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ _ _ _ h1 h2 h3
      exact ⟨d, fun _ => hd⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose dd hdd using hdd0
  obtain ⟨S', hS'⟩ := _root_.GlobalTheory.T.true_geometry_joint_twist_relation_alt W hW u a ha haT J hJ k
  have hone : ∀ t, ∃ β₀ : (J t).Ch B.R.m, ∀ β, β = β₀ := fun t => by
    have hc1 : Fintype.card ((J t).Ch B.R.m) = 1 := by
      rw [Fintype.card_pi]
      refine Finset.prod_eq_one fun i _ => ?_
      have h1 := ((J t).E i).one
      have h2 : ((J t).G i).s + 1 + 1 = B.R.m := ((J t).G i).hs
      rw [h2] at h1
      exact h1
    exact Fintype.card_eq_one_iff.1 hc1
  choose β₀ hβ₀ using hone
  let cQf : W.P.T → ℕ → ℂ := fun t j => ∏ i, ((((J t).E i).idx (j + 1) : ℂ) * (((J t).E i).idx (j + 1 + 1) : ℂ))⁻¹
  let cTf : W.P.T → ℕ → ℂ := fun t j => @TDat.mono _ _ _ a.fld a.val a.top a.loc _ a.o (k.r j) (k.e j) ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1))
  let cK : W.P.T → ℕ → ℂ := fun t j => V j * C j * a.c₀ j * ρ t j
  let cP : W.P.T → ℂ := fun t => VT * ∑ β, s t B.R.m β
  let cV : W.P.T → ℕ → ℂ := fun t j => if h : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m then
      k.v.kap j h.choose h.choose_spec * (k.sc t j * k.sc t (j + 1)) * cQf t j * k.v.cG j * cTf t j
    else (k.sc t j * k.sc t (j + 1)) * cQf t j * k.v.cG j * cTf t j
  let col := _root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd (fun t j => S' t j (k.ε j)) s cV cK cP
  let F := _root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col (fun _ => rfl)
  let w₀ := fun t => (F t).pinTup (k.sc t) (cTf t)
  let w := fun t => GlobalTheory.QTw.resc (w₀ t) (s t)
  have hPinCh : ∀ t, ∃ w, PinChL (_root_.GlobalTheory.Fam.pk_z W) a.g (col t) a.c₀ (J t).A (J t).ι w := fun t => by
    refine ⟨fun j α γ => C j * (J t).wt j α * ζ t j α γ, ?_⟩
    refine
      { is := (hJ t).is
        live := (hJ t).live
        om := fun j hj => by rw [(hJ t).chr j hj]; exact hkom t j hj
        dat := fun j hj α γ => ⟨(hdd t j α γ (by omega)).1, by
          show IsRatDatum _ _ _ _ _ _ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (dd t j α γ) (a.g.vac j))
          rw [(hdd t j α γ (by omega)).2]
          exact ((hD t).2.2.2 j hj α γ).1⟩
        cst := fun j hj α γ _ => by
          have h1 := ((hV t (J t) (hJ t)).1 j (by omega) α)
          have h2 := ((hD t).2.2.2 j hj α γ).2
          show V j * C j * a.c₀ j * ρ t j = _
          rw [← h1, ← h2]
          ring
        ram := fun j _ φ => Iff.rfl
        rdq := fun j hj β φ y => dif_pos hj }
  refine ⟨col, w₀, w, F, ⟨a.c₀, haT.pinX, fun t => ⟨⟨(J t).Ch₀, (J t).A, (J t).ι, hPinCh t⟩, ?_⟩⟩, ?_⟩
  · obtain ⟨UT, hUT1, hUT2⟩ := (hV t (J t) (hJ t)).2
    refine ⟨UT, s t B.R.m (β₀ t) * (J t).wt B.R.m (β₀ t),
      { emb := haT.emb
        lev := hUT1
        eT := fun n h β => ?_
        cP := ?_ }⟩
    · subst h
      rw [hβ₀ t β]
      show (s t B.R.m (β₀ t) • Finsupp.single (1 : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') ((J t).wt B.R.m (β₀ t))).mapDomain (· * a.g.bT) = _
      rw [Finsupp.smul_single, Finsupp.mapDomain_single, one_mul, smul_eq_mul]
    · show VT * ∑ β, s t B.R.m β = _
      rw [Fintype.sum_eq_single (β₀ t) (fun b hb => absurd (hβ₀ t b) hb), ← hUT2 (β₀ t)]
      ring
  have hdQ : ∀ t j α γ, j < B.R.m → (w t).dQ j α γ = (J t).dQ (s t) j α γ := fun t j α γ hj => by
    show _ • (if j < B.R.m then _ else 0) = _
    rw [if_pos hj]
    rfl
  have hpl := fun t => _root_.GlobalTheory.T.true_geometry_twist_local_data_alt W hW u a ha haT t (J t) (hJ t)
  have hQ : ∀ t p, p ∈ (w₀ t).Q ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) := fun t p => by
    show p ∈ Finset.univ.image (fun i => ((J t).G i).q.v) ↔ _
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, -, rfl⟩
      exact ⟨(J t).pl i, (J t).mem i, (hpl t).2 i⟩
    · rintro ⟨PP, hPP, rfl⟩
      obtain ⟨i, hi⟩ := (hJ t).surj PP hPP
      exact ⟨i, Finset.mem_univ _, by rw [(hpl t).2 i, hi]⟩
  have hPins : ∀ t, (F t).Pins (w₀ t) := fun t =>
    { inj := (hpl t).1
      places := fun p => by
        show p ∈ Finset.univ.image (fun i => ((J t).G i).q.v) ↔ _
        rw [Finset.mem_image]
        exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, Finset.mem_univ _, h⟩⟩
      kom := fun j hj => hkom t j hj
      mid := fun j σ h => ⟨(_root_.GlobalTheory.Fam.pk_z W).eta⁻¹, ((hrow t).sBF j (σ + 1) h).2.2.1, ((hrow t).sBF j (σ + 1) h).2.2.2,
        ((hrow t).sFB j σ h).2.2.1, ((hrow t).sFB j σ h).2.2.2⟩
      lastc := fun j h => ((hrow t).sBF j 0 h).2.2.2
      eQ := fun j hj => if_pos hj
      eQT := fun j h => rfl
      dQ := fun j hj α γ => if_pos hj
      ε := fun j ρ' h α => if_pos (Or.inl ⟨ρ', h⟩)
      εT := fun n h β => rfl
      FY := fun j _ f hf => hf
      cQ := fun j _ => rfl }
  have hbT : a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := by
    have h1 := ha.vis.bT
    rw [((ha.tie row col).1.bT).1] at h1
    exact h1
  have hOK : (a.fam row col).ColOK :=
    { kom := fun t j hj => hkom t j hj
      ker := fun t j hj α γ => by
        have hx := haT.pinX.xs j (by omega)
        have hx' := haT.pinX.xs (j + 1) (by omega)
        have hL : ((a.g.x j).L : Set _) = GlobalTheory.AdForm.intVec _ _ := Set.ext fun z => SetLike.mem_coe.trans (hx.2.2 z)
        have hL' : ((a.g.x (j + 1)).L : Set _) = GlobalTheory.AdForm.intVec _ _ := Set.ext fun z => SetLike.mem_coe.trans (hx'.2.2 z)
        have hv : IsVacO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ _ _ (a.g.x j).s (a.g.x (j + 1)).s ((a.g.x j).L : Set _)
            ((a.g.x (j + 1)).L : Set _) (a.g.vac j) := by
          rw [hx.1, hx'.1, hL, hL']
          exact haT.pinX.vc j hj
        exact ⟨⟨_, _, hkom t j hj⟩, hv, (hdd t j α γ hj).1⟩
      e := fun t j α g hg => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
        exact (_root_.GlobalTheory.T.true_geometry_joint_twist_data_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) (cTf t) t j α x (Finsupp.support_smul hx)).2
      eT := fun t n h β g hg => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
        have : x = 1 := by
          exact Finset.mem_singleton.1 (Finsupp.support_single_subset (Finsupp.support_smul hx))
        subst this
        simpa using hbT
      stabK := fun t j hj ψ hψ => GlobalTheory.T.chainKernel_preserves_ramifiedForms_liveCharts I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) (J t).Ch₀ (J t).Ch (J t).A (J t).ι
        (hJ t).is (hJ t).live j hj ψ hψ
      stabS := fun t j hj ψ hψ => (hS' t).1 j hj (k.ε j) ψ hψ }
  have hcv : ∀ t, CVEq k.v (w t) := fun t => by
    refine ⟨fun j σ h => ?_, fun j h => ?_⟩
    · have hex : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m := ⟨σ, h⟩
      have hk : ∀ σ' (h' : j + 2 * (σ' + 1) + 2 = B.R.m), k.v.kap j σ' h' = k.v.kap j σ h := fun σ' h' => by
        obtain rfl : σ' = σ := by omega
        rfl
      show (if h' : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m then _ else _) = _
      rw [dif_pos hex, hk]
      rfl
    · have hex : ¬ ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m := fun ⟨σ, h'⟩ => by omega
      show (if h' : ∃ σ, j + 2 * (σ + 1) + 2 = B.R.m then _ else _) = _
      rw [dif_neg hex]
      rfl
  have hroot : ∀ (Sp : ℕ → Prop) (x : ℂ), (∃ n : ℕ, 0 < n ∧ x ^ n = 1) → ∀ y : ℂ, (∃ n : ℕ, 0 < n ∧ y ^ n = 1) → ∀ c : ℂ, c ≠ 0 →
      GlobalTheory.Fam.UnitRatio Sp (c * x) (c * y) := fun Sp x ⟨n1, hn1, hx⟩ y ⟨n2, hn2, hy⟩ c hc => by
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hy
      exact zero_ne_one hy
    refine (GlobalTheory.Fam.unitRatio_laws Sp).2.2.1 _ _ (n1 * n2) (mul_ne_zero hc hy0) (Nat.mul_pos hn1 hn2) ?_
    rw [mul_pow, mul_pow, pow_mul x, hx, pow_mul' y, hy, one_pow, one_pow]
  have hsum : ∀ t, ∑ β, s t B.R.m β = s t B.R.m (β₀ t) := fun t =>
    Fintype.sum_eq_single (β₀ t) (fun b hb => absurd (hβ₀ t b) hb)
  refine
    { ok := hOK
      pins := hPins
      same := fun t => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      laws := fun t => _root_.GlobalTheory.T.true_geometry_family_final_alt hDS hHC W hW u a ha haT row col (hRow col) hOK t (F t) (w₀ t) (s t) (hD t).1 (hPins t) (hQ t)
      lev := fun t => _root_.GlobalTheory.T.true_geometry_quadratic_twist_level_alt W hW u a ha haT t (J t) (hJ t) row col (F t) rfl rfl (fun i => HEq.rfl)
      vec := fun t => _root_.GlobalTheory.T.true_geometry_joint_twist_identity_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) _ t
      FY := fun t j f => Iff.rfl
      FT := fun t f => Set.mem_univ f
      FX := fun t j _ ψ _ α y => Set.mem_univ _
      atQ := fun t j => by
        obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.T.true_geometry_joint_twist_value_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) (cTf t) t j
        refine ⟨h1, h2, fun α γ x hx => h3 α γ x (Finsupp.support_smul hx)⟩
      e := fun t j α => ⟨rfl, fun g hg => (_root_.GlobalTheory.T.true_geometry_joint_twist_data_alt W hW u a ha haT J hJ row col (fun _ => rfl) (k.sc t) (cTf t) t j α g (Finsupp.support_smul hg)).1⟩
      eT := fun t n h β => ⟨rfl, fun g hg => by
        have hg' := Finsupp.support_single_subset (Finsupp.support_smul hg)
        rw [Finset.mem_singleton.1 hg']
        exact Subgroup.one_mem _⟩
      dd := fun t j hj α γ f _ => by
        rw [hdQ t j α γ hj]
        exact (hdd t j α γ hj).2 f
      read := fun t => ⟨S' t 0, (hS' t).2 row kom dd s cV cK cP⟩
      sc := fun t => rfl
      cT := fun t j ρ' h => (congrArg (@TDat.mono _ _ _ a.fld a.val a.top a.loc _ a.o (k.r j) (k.e j)) ((hrow t).sBF j ρ' h).2.2.2).symm
      cv := hcv
      cK := fun t j hj => hroot _ _ ((hD t).2.2.1 j) _ ((hD _).2.2.1 j) _
        (mul_ne_zero (mul_ne_zero (hV0 j hj) (hC0 j hj)) (haT.pinX.mv j (by omega)).1)
      cP := fun t => by
        show GlobalTheory.Fam.UnitRatio _ (VT * ∑ β, s t B.R.m β) (VT * ∑ β, s _ B.R.m β)
        rw [hsum, hsum]
        exact hroot _ _ ((hD t).1 _ _) _ ((hD _).1 _ _) _ hVT0
      zero := _root_.GlobalTheory.T.true_geometry_joint_twist_bound_alt W hW u a ha haT J hJ row kom dd _ s cV cK cP (fun t α => (hD t).2.1 α) hPinCh }
end
