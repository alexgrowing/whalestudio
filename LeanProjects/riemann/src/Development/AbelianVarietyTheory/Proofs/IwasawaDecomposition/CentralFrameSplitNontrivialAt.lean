import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardFrameNonsplitMaxCompactInLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNonsplitPlaceWithInertDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.FrameTypes

open ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.CenFrame

set_option maxHeartbeats 4000000 in

theorem mtInput_of {hL : GlobalTheory.Published.LocalLanglandsGL} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : NTrue hL D' cf' C' tp') (M' : MtFam D') (hM : HEq (mtL nt.L nt.M) M') :
    ∃ tup Q, MtInput D' M' tup Q := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  have hm : mtL L M = M' := eq_of_heq hM
  subst hm
  exact ⟨tp.tup, C.Q, { mt with }⟩

def IsBlockUpperUnipotentMatrix {k : Type} [CommRing k] {n : ℕ} (r : ℕ) (x : GL (Fin n) k) : Prop :=
  ∀ i j : Fin n, (r ≤ i.val → j.val < r → x.val i j = 0) ∧ (i.val < r → j.val < i.val → x.val i j = 0) ∧
    (i.val < r → i = j → x.val i j = 1)

theorem blkUni_one {k : Type} [CommRing k] {n : ℕ} (r : ℕ) : IsBlockUpperUnipotentMatrix r (1 : GL (Fin n) k) := by
  intro i j
  refine ⟨fun h1 h2 => ?_, fun _ h2 => ?_, fun _ h2 => ?_⟩
  · rw [Units.val_one, Matrix.one_apply_ne]; rintro rfl; omega
  · rw [Units.val_one, Matrix.one_apply_ne]; rintro rfl; omega
  · rw [Units.val_one, h2, Matrix.one_apply_eq]

theorem IsBlockUpperUnipotentMatrix.blk2 {k : Type} [CommRing k] {n r : ℕ} {x : GL (Fin n) k} (h : IsBlockUpperUnipotentMatrix r x) : x ∈ blockTri (blk2 r) := by
  refine mem_blockTri.2 fun i j hij => ?_
  unfold Formalism.L2.DIV.blk2 at hij
  refine (h i j).1 ?_ ?_ <;> split_ifs at hij <;> omega

theorem IsBlockUpperUnipotentMatrix.blkOf {k : Type} [CommRing k] {n r t : ℕ} (hn : n ≤ r + t) {x : GL (Fin n) k} (h : IsBlockUpperUnipotentMatrix r x) :
    x ∈ blockTri (blkOf r t) := by
  refine mem_blockTri.2 fun i j hij => ?_
  unfold Formalism.L2.DIV.blkOf at hij
  have hi := i.2
  by_cases h1 : i.val < r
  · rw [if_pos h1] at hij; omega
  · rw [if_neg h1, Nat.div_eq_of_lt (show i.val - r < t by omega)] at hij
    refine (h i j).1 (by omega) ?_
    by_contra h2
    rw [if_neg h2] at hij
    exact absurd hij (not_lt.2 (Nat.succ_le_succ (Nat.zero_le _)))

theorem IsBlockUpperUnipotentMatrix.unip {k : Type} [CommRing k] {n r : ℕ} (hr : r ≤ n) {x : GL (Fin n) k} (h : IsBlockUpperUnipotentMatrix r x) :
    upperLeftBlock hr x ∈ unip k r := by
  refine ⟨mem_blockTri.2 fun i j hij => ?_, fun i => ?_⟩
  · rw [upper_block_val_submatrix hr h.blk2]
    exact (h _ _).2.1 i.2 hij
  · rw [upper_block_val_submatrix hr h.blk2]
    exact (h _ _).2.2 i.2 rfl

variable {D : D7}

theorem isConjPl_of_under (s : SplitPlace D.host.E) {PP : PlE D.host} (hne : PP ≠ s.w)
    (h : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) PP = s.v) : Formalism.IndefR.Lev.IsConjPl (D := D) PP s.w := by
  rcases Formalism.L2.eq_or_eq_conjPlE s.w PP ((congrArg HeightOneSpectrum.asIdeal h).trans s.w_under.symm) with e | e
  · exact absurd e hne
  · intro c hc
    rw [e, Formalism.L2.mem_conjPlE] at hc
    refine ⟨_, hc, ?_⟩
    rw [IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.TypePlaces.star_eq_conj, GlobalTheory.SplitPlaceOver.host_conj_eq']

theorem mem_level {V : TH.HSp D} {n : ℕ} (hn : V.rank = n) {hF : D.host.F = maximalRealSubfield D.host.E}
    {P : Formalism.IndefR.principalLevelFrame.RowPsi V n} (hP : StdFrame hF P) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1)
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hrt : V.rank ≤ L.r + L.t)
    (hH : ∀ g : G0 L.Pg L.r, (∀ PP, g PP ∈ unip (kP PP.1) L.r) → g ∈ L.P.H)
    (s : SplitPlace D.host.E) (hsep : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP s.w)
    {φ : Os s →+* kP s.w} {b : GL (Fin n) (kP s.w)} (hfr : FrameRed hn P β s φ b)
    {κ : GAf D.host.E n} (hU : κ ∈ Umax D.host.E n) (hT : TrivOutside {s.v} κ) {y : GL (Fin n) (Os s)} (hy : IsCompOf s κ y) :
    (IsBlockUpperUnipotentMatrix L.r (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹) → P.ψ κ ∈ Formalism.IndefR.Links.levS V β L) ∧
    (Matrix.GeneralLinearGroup.map φ y = 1 →
      P.ψ κ ∈ Formalism.IndefR.Links.levS V β L ∧ Formalism.IndefR.Lev.levChi V β L (P.ψ κ) = 1) := by
  have hS := (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hB (P.into κ)).2 ((hP.2 κ).1 hU)
  have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ s.w → redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
    intro PP hPP hne
    refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {PP.under (𝓞 D.host.F)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
    rw [Finset.mem_singleton.1 hu]
    exact GlobalTheory.NonSplitLevel.projV_eq_one hP κ PP (hT _ fun e => hsep PP hPP (isConjPl_of_under s hne e))
  have hent : ∀ i j : Fin V.rank, (redFn β s.w (Formalism.IndefR.Lev.finE V (P.ψ κ))).val i j =
      (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val (Fin.cast hn i) (Fin.cast hn j) :=
    fun i j => hfr κ hU y hy (Fin.cast hn i) (Fin.cast hn j)
  refine ⟨fun hb => ?_, fun h1 => ?_⟩
  · have hall : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → IsBlockUpperUnipotentMatrix L.r (redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ))) := by
      intro PP hPP
      by_cases e : PP = s.w
      · subst e
        intro i j
        rw [hent]
        have hb' := hb (Fin.cast hn i) (Fin.cast hn j)
        exact ⟨hb'.1, hb'.2.1, fun h1 h2 => hb'.2.2 h1 (congrArg _ h2)⟩
      · rw [hred PP hPP e]; exact blkUni_one _
    exact ⟨P.into κ, mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hS, fun PP h => (hall PP (Or.inl h)).blkOf hrt,
      fun PP h => (hall PP (Or.inr h)).blk2⟩, hH _ fun PP => (hall PP.1 (Or.inl PP.2)).unip L.hr⟩⟩
  · have hall : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
      intro PP hPP
      by_cases e : PP = s.w
      · subst e
        refine Units.ext (Matrix.ext fun i j => ?_)
        rw [hent, h1, mul_one, mul_inv_cancel, Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
        exact if_congr (Fin.cast_injective hn).eq_iff rfl rfl
      · exact hred PP hPP e
    refine ⟨⟨P.into κ, GlobalTheory.LevSplit.mem_lev_of_red _ _ β L _ (GlobalTheory.LevSplit.finE_mem_UA V _) hS hall⟩, ?_⟩
    unfold Formalism.IndefR.Lev.levChi
    rw [GlobalTheory.LevSplit.levFn_eq_one β L _ hall, Units.val_one]

section Read
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : Formalism.IndefR.Links.RealDat3 D A3 Ks}
  {F : Formalism.IndefR.Links.Face3 D A3} {X0 : BaseLevelRowSide D} {Y : Read R.toRealDat F.lv2 X0} {M : MtFam D}

set_option maxHeartbeats 1000000 in

theorem exists_fn (ad : MtAd Y M) (μ : D.what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 D μ) (k : Fin D.R.m)
    (hnt : Nontrivial (D.what₂.Mt μ ((k : ℕ) + 1))) :
    ∃ f : GAf D.host.E D.R.nV → ℂ, f ≠ 0 ∧
      (∀ κ (h : κ ∈ (M μ (k.1 + 1) (by omega) (by omega)).J) g,
        f (g * κ) = (((M μ (k.1 + 1) (by omega) (by omega)).χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
      ∀ κ, (ad.PV k).ψ κ ∈ levS _ (R.toRealDat.βV k)
          (Formalism.IndefR.RecTie.datVP R.toRealDat k (Y.tupT μ) (R.toRealDat.levR F.lv2 false)) →
        ∀ g, f (g * κ) = levChi _ (R.toRealDat.βV k)
          (Formalism.IndefR.RecTie.datVP R.toRealDat k (Y.tupT μ) (R.toRealDat.levR F.lv2 false)) ((ad.PV k).ψ κ) * f g := by
  obtain ⟨x, hx⟩ := exists_ne (0 : D.what₂.Mt μ ((k : ℕ) + 1))
  have hr : (M μ (k.1 + 1) (by omega) (by omega)).real x ≠ 0 := fun e =>
    hx ((M μ (k.1 + 1) _ _).real_inj (e.trans (map_zero _).symm))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hr
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ hg₀
  have hm : (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).real x ∈ NG.TypeSp (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).wt.ρ
      (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).J (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).χ :=
    (M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).real_range ▸ LinearMap.mem_range_self _ x
  refine ⟨fun g => l ((M μ (k.1 + 1) (Nat.le_add_left _ _) k.2).real x g), fun e => hl (congrFun e g₀), fun κ h g => ?_, fun κ hJ g => ?_⟩
  · have e := congrFun (hm.2 ⟨κ, h⟩) g
    exact (congrArg l e).trans (map_smul l _ _)
  · have e1 := ad.read _ hμ k x (g * κ)
    have e2 := ad.read _ hμ k x g
    have e3 := (Y.IL.jMt _ hμ k x).2.2 _ hJ ((ad.PV k).ψ g)
    rw [← map_mul] at e3
    have e4 := e1.trans (e3.trans (congrArg _ e2.symm))
    rw [← map_smul] at e4
    exact (congrArg l ((ad.eW _ hμ k).injective e4)).trans (map_smul l _ _)

set_option maxHeartbeats 1000000 in

theorem types_of (ad : MtAd Y M) {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (hin : MtInput D M tup Q) {μ0 : T} (hlev : R.toRealDat.toLevCh.Is μ0) (hgl : R.toRealDat.grp_levels F.lv2)
    (i : D.nd.Loc) (μ : D.what₂.Tup) (k : Fin D.R.m) (hμ : μ = D.nd.mu i) (hnt : Nontrivial (D.what₂.Mt μ ((k : ℕ) + 1)))
    (s : SplitPlace D.host.E) (φ : Os s →+* kP s.w) (b : GL (Fin D.R.nV) (kP s.w)) (hs : s.w ∈ R.Pg)
    (hw : ∃ kk v, s.w = D.naut.plGw kk v) (hfr : FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) (ad.PV k) (R.βV k) s φ b) :
    ∃ (f : GAf D.host.E D.R.nV → ℂ) (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ)
      (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
      (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ),
      f ≠ 0 ∧ NG.IsPsi0 s ψ₀ ∧ NG.LevelUni J χ s D.R.r ψ₀ ξ ∧ (∀ κ (h : κ ∈ J) g, f (g * κ) = ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
      ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → ∀ y : GL (Fin D.R.nV) (Os s), IsCompOf s κ y →
        (IsBlockUpperUnipotentMatrix D.R.r (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹) → ∃ c : ℂ, ∀ g, f (g * κ) = c * f g) ∧
        (Matrix.GeneralLinearGroup.map φ y = 1 → ∀ g, f (g * κ) = f g) := by
  have hu : Formalism.IndefR.RecTie.Used0 D μ := hμ ▸ Model.used_loc i
  rw [D.nd.mu_w i] at hμ
  subst hμ
  obtain ⟨kk, v, hv⟩ := hw
  obtain ⟨ψ₀, ξ, h1, -, h2⟩ := hin.uni (D.nd.w i) k kk v s hv
  obtain ⟨f, hf, hJ, hL⟩ := exists_fn ad _ hu k hnt
  obtain ⟨c, hc⟩ := hlev.βV k
  rw [one_pow] at hc
  obtain ⟨ψ0, -, hP0, -⟩ := hgl
  refine ⟨f, _, _, ψ₀, ξ, hf, h1, h2, hJ, fun κ hU hT y hy => ?_⟩
  have key := mem_level (GlobalTheory.FrameBlockDiagonal.rankV D k) (ad.std k) hc
    (Formalism.IndefR.RecTie.datVP R.toRealDat k (Y.tupT (D.what₂.muTw (D.nd.w i))) (R.toRealDat.levR F.lv2 false))
    (le_of_eq (GlobalTheory.FrameBlockDiagonal.rankV D k))
    (fun g hg => by
      show g ∈ (R.toRealDat.levR F.lv2 false).H
      rw [hP0]
      exact fun PP _ => hg PP)
    s (fun PP hPP => GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hlev _ hPP (Or.inl hs)) hfr hU hT hy
  refine ⟨fun hb => ⟨_, hL κ (key.1 hb)⟩, fun h1 g => ?_⟩
  rw [hL κ (key.2 h1).1 g, (key.2 h1).2, one_mul]

end Read

set_option maxHeartbeats 1000000 in

theorem main : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s (k : Fin (w.st Z).toD7.R.m), t.r.Y.tup s = (w.st Z).toD7.nd.mu i →
    Nontrivial ((w.st Z).toD7.what₂.Mt (t.r.Y.tup s) ((k : ℕ) + 1)) →
    ∀ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w ∈ t.r.z.R.Pg → GlobalTheory.CenFrame.IsResidue s' φ →
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b →
        ∃ (f : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV → ℂ) (J : Subgroup (Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV)) (χ : J →* ℂˣ)
          (ψ₀ : AddChar (s'.v.adicCompletion (NumberField.maximalRealSubfield (w.st Z).toD7.host.E)) ℂ)
          (ξ : (s'.v.adicCompletion (NumberField.maximalRealSubfield (w.st Z).toD7.host.E))ˣ →* ℂˣ),
          f ≠ 0 ∧ Formalism.L2.NG.IsPsi0 s' ψ₀ ∧ Formalism.L2.NG.LevelUni J χ s' (w.st Z).toD7.R.r ψ₀ ξ ∧
          (∀ κ (h : κ ∈ J) g, f (g * κ) = ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
          (∀ κ ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV, ReciprocityTheory.Aut.TrivOutside {s'.v} κ → ∀ y : GL (Fin (w.st Z).toD7.R.nV) (GlobalTheory.CenFrame.Os s'),
        GlobalTheory.CenFrame.IsCompOf s' κ y →
      ((∀ i j : Fin (w.st Z).toD7.R.nV, ((w.st Z).toD7.R.r ≤ i.val → j.val < (w.st Z).toD7.R.r → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < (w.st Z).toD7.R.r → j.val < i.val → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < (w.st Z).toD7.R.r → i = j → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 1)) →
        ∃ c : ℂ, ∀ g, f (g * κ) = c * f g) ∧
      (Matrix.GeneralLinearGroup.map φ y = 1 → ∀ g, f (g * κ) = f g)) := by
  intro hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE hR hP => ?_
  intro ad i s k hs hnt s' φ b hPg _ hfr
  obtain ⟨tup, Q, hin⟩ := mtInput_of c.a.nt c.a.all.gal.mt c.a.mt_eq
  obtain ⟨plg, iso, h1, -⟩ := t.r.z.pins.keep.grp
  exact types_of (D := (w.st Z).toD7) ad hin t.r.z.pins.char.base.lev t.r.z.pins.char.base.grp.levels i _ k hs hnt s' φ b hPg
    ⟨(plg.symm ⟨s'.w, hPg⟩).1, (plg.symm ⟨s'.w, hPg⟩).2, by rw [← h1, plg.apply_symm_apply]⟩ hfr

end GlobalTheory.FrameTypes

end
