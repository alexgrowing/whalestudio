import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealQuotientVolumeGrowthOfScalarHypotheses
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardResidueFieldOfRingEquivAdicCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralsPositionOneEqCellSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridVertexMeasureEqOfSameNormalisation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridBlockCongruenceOffTypePrimeDescription
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip
open ValuativeRel
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.TopFlip.MeasLevel

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem vol_mul_relIndex [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] (J : Subgroup (GL n k))
    (ho : IsOpen (J : Set (GL n k))) (hle : J ≤ KO k n) :
    (haarVol (KO k n)).real (J.map invT : Subgroup _) * (J.relIndex (KO k n) : ℝ) = 1 := by
  obtain ⟨ho', hle'⟩ := isOpen_map_invT ho hle
  have hK : (KO k n).map invT = KO k n := by
    refine le_antisymm ?_ fun g hg => ⟨invT g, invT_mem_KO hg, GlobalTheory.SplitFlip.invT_invT g⟩
    rintro _ ⟨g, hg, rfl⟩
    exact invT_mem_KO hg
  have hinj : Function.Injective (invT : GL n k →* GL n k) := Function.LeftInverse.injective GlobalTheory.SplitFlip.invT_invT
  have hi : (J.map invT).relIndex (KO k n) = J.relIndex (KO k n) := by
    conv_lhs => rw [← hK]
    exact Subgroup.relIndex_map_map_of_injective _ _ hinj
  haveI : CompactSpace (KO k n) := isCompact_iff_compactSpace.1 GlobalTheory.SplitFlip.isCompact_KO
  have ho2 : IsOpen (((J.map invT).subgroupOf (KO k n) : Subgroup (KO k n)) : Set (KO k n)) :=
    ho'.preimage continuous_subtype_val
  haveI : Finite (KO k n ⧸ (J.map invT).subgroupOf (KO k n)) := Subgroup.quotient_finite_of_isOpen _ ho2
  haveI : ((J.map invT).subgroupOf (KO k n)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h := GlobalTheory.IndexVolume.relIndex_mul_measure_subgroup _ (KO k n) hle' ho'.measurableSet (haarVol (KO k n))
  rw [haarVol_self GlobalTheory.SplitFlip.isOpen_KO le_rfl, hi] at h
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one, mul_comm] at h2
  exact h2

theorem gl_residue_surjective (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Function.Surjective (GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue O)) := by
  intro g
  choose f hf using (IsLocalRing.residue_surjective (R := O))
  have hM : (IsLocalRing.residue O).mapMatrix (g.val.map f) = g.val := by
    ext a b
    simp [hf]
  have hd : IsUnit (g.val.map f).det := by
    refine (isUnit_map_iff (IsLocalRing.residue O) _).1 ?_
    rw [RingHom.map_det, hM]
    exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hd
  refine ⟨u, Units.ext ?_⟩
  rw [← hM, ← hu]
  rfl

theorem relIndex_parahoric {n : ℕ} (r : ℕ) (J : Subgroup (GL (Fin n) k))
    (hJ : ∀ g, g ∈ J ↔ g ∈ KO k (Fin n) ∧ ∀ a b, blk2 r b < blk2 r a → valuation k (g.1 a b) < 1) :
    J.relIndex (KO k (Fin n)) = (blockTri (blk2 r) : Subgroup (GL (Fin n) 𝓀[k])).index := by
  have e : J.comap (GeneralLinearGroup.map (n := Fin n) (algebraMap (valuation k).integer k)) =
      (blockTri (blk2 r) : Subgroup (GL (Fin n) 𝓀[k])).comap
        (GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue (valuation k).integer)) := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_comap, hJ, mem_blockTri]
    have key : ∀ x : (valuation k).integer, IsLocalRing.residue (valuation k).integer x = 0 ↔ valuation k (x : k) < 1 :=
      fun x => by
        rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
          Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    refine ⟨fun h a b hab => (key _).2 (h.2 a b hab), fun h => ⟨⟨g, rfl⟩, fun a b hab => (key _).1 (h a b hab)⟩⟩
  rw [KO, ← Subgroup.index_comap, e, Subgroup.index_comap_of_surjective _ (gl_residue_surjective _ n)]

end Local

variable {D : D7}

theorem index_residue (w : Pl D.host.E) {n n' r s : ℕ} (h : n = r + s) (h' : n' = r + s) :
    ((blockTri (blk2 r) : Subgroup (GL (Fin n) 𝓀[Kw w])).index : ℝ) =
      (blockTri (blk2 r) : Subgroup (GL (Fin n') (kP w))).index := by
  letI : Field (kP w) := Ideal.Quotient.field _
  have hq : Nat.card (kP w) = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hq' : Nat.card 𝓀[Kw w] = Ideal.absNorm w.asIdeal :=
    GlobalTheory.LocalResidue.card_residue_of_ringEquiv D.host.E w (Kw w) (RingEquiv.refl _) fun a =>
      (GivenAdm.isEquiv_val w).le_one_iff_le_one.symm
  refine (GlobalTheory.ParabIndex.index_maxParabolic_GL_finiteField 𝓀[Kw w] n r s h).trans
    (Eq.trans ?_ (GlobalTheory.ParabIndex.index_maxParabolic_GL_finiteField (kP w) n' r s h').symm)
  rw [hq, hq', h, h']

open Classical in

theorem relIndex_lev (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ)
    (hN : Lev.IsBaseFrame V β Λ N) {r t j : ℕ} (hr : r ≤ V.rank) (Pg Q : Finset (Pl D.host.E))
    (hnc : ∀ P ∈ Pg ∪ Q, ∀ P' ∈ Pg ∪ Q, ¬ Lev.IsConjPl P P') (hd : Disjoint Pg Q)
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ≤
      lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) ∧
    (lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B)).relIndex
      (lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B)) =
      ∏ PP ∈ Q, (blockTri (blk2 r) : Subgroup (GL (Fin V.rank) (kP PP))).index := by
  have hmem := fun x => GlobalTheory.TwistIndex.mem_datY_iff V β hr hr Pg Q χ χ ξ ξ' (r := r) (t := t) (j := j) x
  refine ⟨fun x hx => ((hmem x).1 hx).1, ?_⟩
  have hSt : lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) ≤
      St β := fun x hx => parLev_St hx.1
  let φ : lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) →*
      (∀ PP : Q, GL (Fin V.rank) (kP PP.1)) :=
    MonoidHom.pi fun PP => (redAt β PP.1).comp (Subgroup.inclusion hSt)
  have hφ : ∀ x PP, φ x PP = redFn β PP.1 x.1 := by
    intro x PP
    unfold redFn
    rw [extendOne_of_mem _ (hSt x.2)]
    rfl
  have hcomap : (lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B)).subgroupOf
      (lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B)) =
      (Subgroup.pi Set.univ fun PP : Q =>
        (blockTri (blk2 r) : Subgroup (GL (Fin V.rank) (kP PP.1)))).comap φ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hmem]
    simp only [hφ]
    constructor
    · rintro ⟨-, h⟩ PP -
      exact h PP.1 PP.2
    · intro h
      exact ⟨x.2, fun PP hP => h ⟨PP, hP⟩ (Set.mem_univ _)⟩
  have hsurj : Function.Surjective φ := by
    intro g
    let L' : LevDat D.host.E ℂ V.rank := Lev.datW V.rank (Pg ∪ Q) (LevelP.triv (Pg ∪ Q) V.rank ℂ) Lev.Frm.B
    have hlift : Lev.LiftsExist V β L' :=
      GlobalTheory.ParahoricLift.liftsExist V β L' Λ N hN (fun PP hP PP' hP' => by
        rcases hP' with h | h
        · exact hnc PP hP PP' h
        · exact absurd h (Finset.notMem_empty _)) (Finset.disjoint_empty_right _)
    let g0 : G0 L'.Pg L'.r := fun PP => if h : PP.1 ∈ Q then g ⟨PP.1, h⟩ else 1
    obtain ⟨κ, hκ⟩ := hlift g0
    have hκ1 : Lev.finE V κ ∈ parLev D.sp.cm V.gram β L' := hκ.2.1
    have hκ2 : rTup β L' (Lev.finE V κ) = g0 := hκ.2.2
    have hred : ∀ PP (h : PP ∈ Pg ∪ Q), redFn β PP (Lev.finE V κ) = g0 ⟨PP, h⟩ := by
      intro PP h
      exact (GlobalTheory.TwistIndex.restrictedBlock_self_apply _).symm.trans (congrFun hκ2 ⟨PP, h⟩)
    have hPg : ∀ PP ∈ Pg, redFn β PP (Lev.finE V κ) = 1 := by
      intro PP hP
      rw [hred PP (Finset.mem_union_left _ hP)]
      have hq : PP ∉ Q := Finset.disjoint_left.1 hd hP
      show (if h : PP ∈ Q then g ⟨PP, h⟩ else (1 : GL (Fin V.rank) (kP PP))) = 1
      exact dif_neg hq
    have hSt' := parLev_St hκ1
    have hxbig : Lev.finE V κ ∈
        lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) := by
      refine ⟨⟨⟨⟨parLev_UA hκ1, hSt'⟩, ?_⟩, ?_⟩, ?_⟩
      · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP =>
          mem_parah.2 ⟨hSt', by rw [hPg PP hP]; exact Subgroup.one_mem _⟩
      · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)
      · show rTup β (Lev.datY V.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) (Lev.finE V κ) ∈
          (⊥ : Subgroup (G0 Pg r))
        refine Subgroup.mem_bot.2 (funext fun PP => ?_)
        show upperLeftBlock hr (redFn β PP.1 (Lev.finE V κ)) = 1
        rw [hPg PP.1 PP.2]
        exact blockDiagonalExtendByOnePrimeField_one _ _
    refine ⟨⟨_, hxbig⟩, funext fun PP => ?_⟩
    rw [hφ, hred PP.1 (Finset.mem_union_right _ PP.2)]
    show (if h : PP.1 ∈ Q then g ⟨PP.1, h⟩ else 1) = g PP
    rw [dif_pos PP.2]
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj, GlobalTheory.TwistIndex.index_pi_univ]
  exact Finset.prod_coe_sort Q fun PP => (blockTri (blk2 r) : Subgroup (GL (Fin V.rank) (kP PP))).index

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}

theorem Q_base (h : L.Is μ₀) : L.Q μ₀ = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
  have h1 := (h.Q_ram μ₀ PP).2 (Or.inl hPP)
  rw [h.xi_base] at h1
  exact h1 fun _ _ => rfl

open Classical in

theorem not_conj (h : L.Is μ₀) (t : T) : ∀ P ∈ L.Pg ∪ L.Q t, ∀ P' ∈ L.Pg ∪ L.Q t, ¬ Lev.IsConjPl P P' := by
  intro P hP P' hP' hc
  rcases Finset.mem_union.1 hP with hP | hP <;> rcases Finset.mem_union.1 hP' with hP' | hP'
  · obtain ⟨k, hk⟩ := (h.Pg P).1 hP
    obtain ⟨k', hk'⟩ := (h.Pg P').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl L.C.P hk hk' hc
  · obtain ⟨k, hk⟩ := (h.Pg P).1 hP
    obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hP'
    exact GlobalTheory.LevelRamif.not_two_primes P' hq (D.host.g_prime k) (hne k) hm
      (GlobalTheory.LevelRamif.natCast_mem_conj hc (GlobalTheory.LevelRamif.typePrime_mem hk))
  · obtain ⟨k, hk⟩ := (h.Pg P').1 hP'
    obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hP
    exact GlobalTheory.LevelRamif.not_two_primes P' hq (D.host.g_prime k) (hne k) (GlobalTheory.LevelRamif.natCast_mem_conj hc hm)
      (GlobalTheory.LevelRamif.typePrime_mem hk)
  · exact (h.Q_pl t P hP).2 P' hP' hc

theorem relIndex_levCol (h : L.Is μ₀) (t : T) {j : ℕ} (hj : j + 1 < D.R.m) :
    levCol L t j ≤ levCol L μ₀ j ∧ levCol L μ₀ j ≤ UA D.sp.cm (columnBlock L (j + 1)).sp.gram ∧
      (levCol L t j).relIndex (levCol L μ₀ j) =
        ∏ PP ∈ L.Q t, (blockTri (blk2 D.R.r) : Subgroup (GL (Fin (Yc D (j + 1)).rank) (kP PP))).index := by
  obtain ⟨c, hc⟩ := h.βY (j + 1) hj
  have H := relIndex_lev (Yc D (j + 1)) (L.βY (j + 1)) _ _ hc (t := D.R.t) (j := j + 1) (r_le_Y (j + 1)) L.Pg (L.Q t)
    (not_conj h t) (GlobalTheory.LevelRamif.ramif_at_levels D T L μ₀ h t ⟨j + 1, hj⟩).1 L.chi (L.xiR t) (L.xiR μ₀)
  have e0 : L.datYt μ₀ (j + 1) L.triv = Lev.datY _ D.R.r D.R.t (j + 1) (r_le_Y (j + 1)) L.Pg ∅ (LevelP.triv _ _ _) L.chi
      (L.xiR μ₀) Lev.Frm.B := by
    rw [LevCh.datYt, Q_base h]
  rw [← e0] at H
  have key : ∀ (Y : LSp D) (V : HSp D) Λ (K K₀ : Subgroup (GL (Fin Y.sp.rank) (Lev.EAf D)))
      (K' K₀' : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (n : ℕ), Y = ⟨V, Λ⟩ → HEq K K' → HEq K₀ K₀' →
      K' ≤ K₀' → K₀' ≤ UA D.sp.cm V.gram → K'.relIndex K₀' = n → K ≤ K₀ ∧ K₀ ≤ UA D.sp.cm Y.sp.gram ∧ K.relIndex K₀ = n := by
    rintro _ V Λ K K₀ K' K₀' n rfl e e' a b c
    obtain rfl := eq_of_heq e
    obtain rfl := eq_of_heq e'
    exact ⟨a, b, c⟩
  exact key _ _ _ _ _ _ _ _ (colY_lt L hj) (levCol_lt L t hj) (levCol_lt L μ₀ hj) H.1 lev_le_UA H.2

theorem nu_scale {M M₀ : Vol G} {X : Node} {K₁ K₀ : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))}
    (h₁ : M.IsAt X K₁) (h₀ : M₀.IsAt X K₀) (hle : K₁ ≤ K₀) (hU : K₀ ≤ UA D.sp.cm (G.V X).gram) (hne : K₁.relIndex K₀ ≠ 0)
    (ho : IsOpen ((K₁.comap (Lev.finE (G.V X)) : Subgroup (GA D (G.V X))) : Set (GA D (G.V X)))) :
    M.ν X = (K₁.relIndex K₀ : ℝ≥0∞) • M₀.ν X := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V X)
  unfold GlobalTheory.FunObj.Vol.IsAt at h₁ h₀
  split_ifs at h₁ h₀
  · exact GlobalTheory.ChainTw.VolScale.scale _ _ (fun _ _ hm => hm.1) _ _ _ _ hle hU hne ho.measurableSet h₁.1 h₀.1
  · exact GlobalTheory.ChainTw.VolScale.scale _ _ (fun _ _ hm => hm.1) _ _ _ _ hle hU hne ho.measurableSet h₁.1 h₀.1

theorem levVol_of_KO {t : T} {i j : Fin D.R.m} {w : Pl D.host.E} (h : givenLevel G t w (i, j) = KO (Kw w) _) :
    levVol G t i j w = 1 := by
  have := vol_mul_relIndex (KO (Kw w) (Fin ((locGrid G t w).rank (i, j)))) GlobalTheory.SplitFlip.isOpen_KO le_rfl
  rw [Subgroup.relIndex_self, Nat.cast_one, mul_one] at this
  rw [levVol, h]
  exact this

theorem levVol_ne_zero (hL : L.Is μ₀) {t : T} (i j : Fin D.R.m) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    levVol G t i j w ≠ 0 := by
  have h := GivenAdm.givenLevel_open (G := G) hL hw ((i : ℕ), (j : ℕ))
  exact left_ne_zero_of_mul_eq_one (vol_mul_relIndex _ h.1 h.2)

theorem givenLevel_base (hL : L.Is μ₀) (j : ℕ) {w : Pl D.host.E} (hw : w ∉ L.Pg) :
    givenLevel G μ₀ w (0, j + 1) = KO (Kw w) _ := by
  ext g
  refine (GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description G μ₀ w hw (j + 1) g).trans ?_
  simp [Q_base hL]

theorem levVol_base (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) {w : Pl D.host.E} (hw : w ∈ L.Q t) (hw' : w ∉ G.pl.W0) :
    levVol G μ₀ i j w = 1 := by
  refine levVol_of_KO ?_
  have hP : w ∉ L.Pg := Finset.disjoint_right.1 (GlobalTheory.LevelRamif.ramif_at_levels D T L μ₀ hL t i).1 hw
  obtain ⟨i, hi⟩ := i
  obtain ⟨_ | j, hj⟩ := j
  · ext g
    show g ∈ glLatCong (unifAt w ^ cosExp G w) (GlobalTheory.SplitFlip.stdLat (Kw w) _) ↔ _
    rw [(depthAt_of_notMem G hw').1, pow_zero, GivenAdm.mem_glLatCong]
    refine and_iff_left_of_imp fun hg a b => ?_
    have := ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg).1 a b
    simp only [Units.val_one, map_one, Matrix.sub_apply]
    refine Valuation.map_sub_le _ this ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp
  · rcases i with _ | i
    · exact givenLevel_base hL j hP
    · rfl

theorem levVol_col (hL : L.Is μ₀) (t : T) {j : ℕ} (hi : 0 < D.R.m) (hj : j + 1 < D.R.m) {w : Pl D.host.E} (hw : w ∉ L.Q t) :
    levVol G t ⟨0, hi⟩ ⟨j + 1, hj⟩ w = levVol G μ₀ ⟨0, hi⟩ ⟨j + 1, hj⟩ w := by
  have e : stepGroup L t w (j + 1) = stepGroup L μ₀ w (j + 1) := by
    simp [stepGroup, hw, Q_base hL]
  have a : ∀ t' : T, levVol G t' ⟨0, hi⟩ ⟨j + 1, hj⟩ w =
      (haarVol (KO (Kw w) (Fin ((locGrid G μ₀ w).rank (0, j + 1))))).real
        (((stepGroup L t' w (j + 1)).map (GlobalTheory.StepData.reGL (ixFin G μ₀ w (j + 1))).toMonoidHom).map invT : Subgroup _) :=
    fun _ => rfl
  rw [a, a, e]

theorem exists_factors (hL : L.Is μ₀) (i j : Fin D.R.m) (t : T) {M M₀ : Vol G} (hM : M.Is t) (hM₀ : M₀.Is μ₀) :
    ∃ n : Pl D.host.E → ℕ, M.ν (.grid i j) = ((∏ w ∈ L.Q t, n w : ℕ) : ℝ≥0∞) • M₀.ν (.grid i j) ∧
      (∀ w ∈ L.Q t, levVol G t i j w * n w = levVol G μ₀ i j w) ∧ ∀ w ∉ L.Q t, levVol G t i j w = levVol G μ₀ i j w := by
  have hX : (Node.grid i j).InRange D.R.m := ⟨i.2.le, j.2.le⟩
  have easy : levJ G t (.grid i j) = levJ G μ₀ (.grid i j) → (∀ w, levVol G t i j w = levVol G μ₀ i j w) →
      ∃ n : Pl D.host.E → ℕ, M.ν (.grid i j) = ((∏ w ∈ L.Q t, n w : ℕ) : ℝ≥0∞) • M₀.ν (.grid i j) ∧
      (∀ w ∈ L.Q t, levVol G t i j w * n w = levVol G μ₀ i j w) ∧ ∀ w ∉ L.Q t, levVol G t i j w = levVol G μ₀ i j w := by
    intro e h
    refine ⟨fun _ => 1, ?_, fun w _ => by rw [h, Nat.cast_one, mul_one], fun w _ => h w⟩
    rw [Finset.prod_const_one, Nat.cast_one, one_smul]
    exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M₀ _ _ (hM.vtx _ hX) (e ▸ hM₀.vtx _ hX)
  obtain ⟨i, hi⟩ := i
  obtain ⟨_ | j, hj⟩ := j
  · exact easy ((levJ_row G t i).trans (levJ_row G μ₀ i).symm) fun _ => rfl
  rcases i with _ | i
  swap
  · exact easy rfl fun _ => rfl
  obtain ⟨h1, h2, h3⟩ := relIndex_levCol hL t hj
  have hne : (levCol L t j).relIndex (levCol L μ₀ j) ≠ 0 := by
    rw [h3]
    exact Finset.prod_ne_zero_iff.2 fun w _ => Subgroup.index_ne_zero_of_finite
  refine ⟨fun PP => (blockTri (blk2 D.R.r) : Subgroup (GL (Fin (Yc D (j + 1)).rank) (kP PP))).index, ?_,
    fun w hw => ?_, fun w hw => ?_⟩
  · rw [← h3]
    exact nu_scale (X := .grid 0 (j + 1)) (hM.vtx _ hX) (hM₀.vtx _ hX) h1 h2 hne (levJ_open_compact G hL t hX).1
  · classical
    have hP : w ∉ L.Pg := Finset.disjoint_right.1 (GlobalTheory.LevelRamif.ramif_at_levels D T L μ₀ hL t ⟨0, hi⟩).1 hw
    have ho := GivenAdm.givenLevel_open (G := G) hL (t := t) (w := w) (by unfold locPl; simp [hw]) (0, j + 1)
    have hv := vol_mul_relIndex _ ho.1 ho.2
    rw [relIndex_parahoric D.R.r (givenLevel G t w (0, j + 1)) (fun g => (GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description G t w hP (j + 1) g).trans (by simp [hw])),
      index_residue w (s := (j + 1) * D.R.t) (n' := (Yc D (j + 1)).rank)
        (by change D.R.r + (j + 1) * D.R.t + 0 * sLen D = _; rw [zero_mul, add_zero])
        ((D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [min_eq_left hj.le]; rfl))] at hv
    rw [levVol_of_KO (t := μ₀) (givenLevel_base hL j hP)]
    exact hv
  · exact levVol_col hL t hi hj hw

theorem measure_mul_levVol : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → (∀ t, SquareStanding G t) → ∀ (i j : Fin D.R.m) (m : Measure (GA D (spW₁ G i j))), m.IsHaarMeasure →
      ∃ c : ℝ, c ≠ 0 ∧ ∀ (t : T) (M : Vol G), M.Is t → ∀ s : NNReal, M.ν (.grid i j) = s • m →
        (s : ℝ) * ∏ w ∈ locPl G t, levVol G t i j w = c := by
  intro D T L sc G μ₀ hL _ i j m hm
  classical
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (spW₁ G i j)
  obtain ⟨M₀, hM₀⟩ := exists_vol G hL μ₀
  have hX : (Node.grid i j).InRange D.R.m := ⟨i.2.le, j.2.le⟩
  haveI := (hM₀.vtx _ hX).haar_fund.1
  have e₀ := Measure.isMulLeftInvariant_eq_smul (M₀.ν (.grid i j)) m
  have p₀ := Measure.haarScalarFactor_pos_of_isHaarMeasure (M₀.ν (.grid i j)) m
  set s₀ := Measure.haarScalarFactor (M₀.ν (.grid i j)) m
  refine ⟨s₀ * ∏ w ∈ locPl G μ₀, levVol G μ₀ i j w, mul_ne_zero (by exact_mod_cast p₀.ne')
    (Finset.prod_ne_zero_iff.2 fun w hw => levVol_ne_zero hL i j hw), fun t M hM s hs => ?_⟩
  obtain ⟨n, h1, h2, h3⟩ := exists_factors hL i j t hM hM₀
  have hsn : (s : ℝ) = (∏ w ∈ L.Q t, n w : ℕ) * (s₀ : ℝ) := by
    obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : GA D (spW₁ G i j))
    have h0 : m C ≠ 0 := (Measure.measure_pos_of_mem_nhds m hC1).ne'
    have h := congrArg (fun μ : Measure (GA D (spW₁ G i j)) => μ C) (hs.symm.trans h1)
    rw [e₀] at h
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ← mul_assoc] at h
    have h' := congrArg ENNReal.toReal ((ENNReal.mul_left_inj h0 hC.measure_lt_top.ne).1 h)
    simpa using h'
  have hsub : locPl G μ₀ ⊆ locPl G t := by
    unfold locPl
    rw [Q_base hL]
    simp
  have hQ : L.Q t ⊆ locPl G t := by
    unfold locPl
    simp
  have e1 : ∏ w ∈ locPl G μ₀, levVol G μ₀ i j w = ∏ w ∈ locPl G t, levVol G μ₀ i j w :=
    Finset.prod_subset hsub fun w hw hw' => by
      have a : w ∉ G.pl.W0 := fun h => hw' (by unfold locPl; simp [h])
      exact levVol_base hL t i j (by unfold locPl at hw; simpa [a] using hw) a
  rw [hsn, e1, ← Finset.prod_sdiff hQ, ← Finset.prod_sdiff hQ (f := levVol G μ₀ i j),
    ← Finset.prod_congr rfl h2, Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun w hw => h3 w (Finset.mem_sdiff.1 hw).2, Nat.cast_prod]
  ring

end GlobalTheory.TopFlip.MeasLevel

end
