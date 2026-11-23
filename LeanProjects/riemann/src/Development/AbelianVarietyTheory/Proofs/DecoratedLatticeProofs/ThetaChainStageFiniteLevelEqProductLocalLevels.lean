import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PushforwardHaarRealPointsTimesLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapRestrictIsHaarOfOpenProductCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactFiniteAdelicSubgroupIntegralOpenStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw.LevLoc

variable {D : D7}

def LocOK {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (PP : Pl D.host.E) (y : GL (Fin n) (Formalism.L2.DIV.kP PP)) : Prop :=
  (PP ∈ L.Pg → y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr y = 1) ∧
    (PP ∈ L.Q → y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 L.r))

theorem locOK_one {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (PP : Pl D.host.E) : LocOK L PP 1 :=
  ⟨fun _ => ⟨one_mem _, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _⟩, fun _ => one_mem _⟩

theorem mem_lev_iff {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (hP : L.P.H = ⊥) (x : GL (Fin n) (Lev.EAf D)) :
    x ∈ Formalism.L2.DIV.lev D.sp.cm J β L ↔ x ∈ Formalism.L2.DIV.UA D.sp.cm J ∧ x ∈ Formalism.L2.DIV.St β ∧
      ∀ PP, LocOK L PP (Formalism.L2.DIV.redFn β PP x) := by
  rw [Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev, hP, Subgroup.mem_bot]
  constructor
  · rintro ⟨⟨hU, hS, hg, hq⟩, hr⟩
    exact ⟨hU, hS, fun PP => ⟨fun h => ⟨hg PP h, congrFun hr ⟨PP, h⟩⟩, fun h => hq PP h⟩⟩
  · rintro ⟨hU, hS, h⟩
    exact ⟨⟨hU, hS, fun PP hP => ((h PP).1 hP).1, fun PP hP => (h PP).2 hP⟩, funext fun PP => ((h PP.1).1 PP.2).2⟩

theorem finE_gAt_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (g : GA D V) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hv : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) :
    Lev.finE V (gAt V (.inl v) g) ∈ Formalism.L2.DIV.St β := by
  refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V β Λ hfr _).2 fun w => ?_
  show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram w
    (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)) ∈ _
  by_cases e : w = v
  · subst e
    rw [GlobalTheory.AdelicU.proj_emb_self]
    exact hv
  · rw [GlobalTheory.AdelicU.proj_emb_ne _ _ e]
    exact one_mem _

theorem red_local {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (g : GA D V) (hg : Lev.finE V g ∈ Formalism.L2.DIV.St β) (PP : Pl D.host.E) :
    Formalism.L2.DIV.redFn β PP (Lev.finE V g) =
      Formalism.L2.DIV.redFn β PP (Lev.finE V (gAt V (.inl (PP.under (𝓞 D.host.F))) g)) := by
  set v := PP.under (𝓞 D.host.F)
  set k := gAt V (.inl v) g with hkdef
  have hk : Lev.finE V k ∈ Formalism.L2.DIV.St β := finE_gAt_mem_St hfr g v ((GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V β Λ hfr g).1 hg v)
  have hpk : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k = GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g := by
    show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v
      (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)) = _
    rw [GlobalTheory.AdelicU.proj_emb_self]
  have h2 : Lev.finE V (k⁻¹ * g) ∈ Formalism.L2.DIV.St β := by
    rw [map_mul, map_inv]; exact mul_mem (inv_mem hk) hg
  have h3 : Formalism.L2.DIV.redFn β PP (Lev.finE V (k⁻¹ * g)) = 1 :=
    GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D V β _ PP h2 (by rw [map_mul, map_inv, hpk, inv_mul_cancel])
  have e : g = k * (k⁻¹ * g) := by group
  conv_lhs => rw [e]
  rw [map_mul, Formalism.L2.DIV.redFn_mul hk h2, h3, mul_one]

end GlobalTheory.ChainTw.LevLoc

namespace GlobalTheory.ChainTw.LevLoc

open Classical in

theorem levLoc : ∀ D : D7, ForStageQ D fun c w _ s => MeasurableSet (levSet s) ∧ MeasurableSet (intOff c s) ∧ (∀ g, g ∈ levSet s ↔ g ∈ intOff c s ∧ ∀ v ∈ c.S, gAt s.V (.inl v) g ∈ Lev.levG s.V s.β s.L) ∧ (∀ g ∈ levSet s, ∃ b : GinfC s.V, ∃ κ ∈ Lev.levG s.V s.β s.L, g = (b : GA D s.V) * κ) ∧ (∀ κ ∈ Lev.levG s.V s.β s.L, ‖Lev.levChi s.V s.β s.L κ‖ = 1 ∧ ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧ ∃ mR, IsLevMeas s mR := by
  intro D c w hw j _ s hs
  obtain ⟨hr, hL, hfl⟩ := hs
  have hfr : Formalism.L2.DIV.IsFrame s.β s.Λ := hfl.frame
  haveI : s.ν.IsHaarMeasure := hfl.haar
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  have hP : s.L.P.H = ⊥ := by rw [hL]; rfl
  have hPl : ∀ PP, PP ∈ s.L.Pg ∨ PP ∈ s.L.Q → PP.under (𝓞 D.host.F) ∈ c.S := by
    intro PP hPP
    have h1 : PP ∈ c.Pg := by
      rw [hw.union, Finset.mem_union]
      rw [hL] at hPP
      exact hPP
    unfold Com.S
    exact Finset.mem_image_of_mem _ h1
  set V := s.V
  set K := Lev.levG s.V s.β s.L

  have h3 : ∀ k ∈ K, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram s.Λ v :=
    fun k hk v => (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V s.β s.Λ hfr k).1 (GlobalTheory.ChainOnto.LevelFacts.finE_mem_St hk) v

  have h1 : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ K := by
    obtain ⟨U, hU, hUk⟩ := GlobalTheory.T.exists_open_principal_congruence_finitely_many_primes D V s.β (s.L.Pg ∪ s.L.Q)
    refine ⟨U, hU, fun k hk hkf => ⟨hkf, ?_⟩⟩
    exact GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm V.gram s.β s.L _ (GlobalTheory.LevSplit.finE_mem_UA V k) (hUk k hk).1
      fun PP hPP => (hUk k hk).2 PP (Finset.mem_union.2 hPP)

  have hloc : ∀ g, g ∈ levSet s ↔ g ∈ intOff c s ∧ ∀ v ∈ c.S, gAt s.V (.inl v) g ∈ K := by
    intro g
    constructor
    · intro hg
      obtain ⟨-, hS, hl⟩ := (mem_lev_iff V.gram s.β s.L hP _).1 hg
      refine ⟨fun v _ => (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V s.β s.Λ hfr g).1 hS v, fun v _ => ?_⟩
      have hkS := finE_gAt_mem_St hfr g v ((GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V s.β s.Λ hfr g).1 hS v)
      refine ⟨GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC V v _, ?_⟩
      refine (mem_lev_iff V.gram s.β s.L hP _).2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hkS, fun PP => ?_⟩
      by_cases e : PP.under (𝓞 D.host.F) = v
      · subst e
        rw [← red_local hfr g hS PP]
        exact hl PP
      · rw [GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D V s.β _ PP hkS (GlobalTheory.AdelicU.proj_emb_ne _ _ e _)]
        exact locOK_one _ _
    · rintro ⟨hI, hK⟩
      have hS : Lev.finE V g ∈ Formalism.L2.DIV.St s.β := by
        refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V s.β s.Λ hfr g).2 fun v => ?_
        by_cases hv : v ∈ c.S
        · have := h3 _ (hK v hv) v
          have e : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (gAt s.V (.inl v) g) = GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g := by
            show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v
              (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)) = _
            rw [GlobalTheory.AdelicU.proj_emb_self]
          rw [e] at this
          exact this
        · exact hI v hv
      refine (mem_lev_iff V.gram s.β s.L hP _).2 ⟨GlobalTheory.LevSplit.finE_mem_UA V g, hS, fun PP => ?_⟩
      by_cases hPP : PP ∈ s.L.Pg ∨ PP ∈ s.L.Q
      · rw [red_local hfr g hS PP]
        exact ((mem_lev_iff V.gram s.β s.L hP _).1 (hK _ (hPl PP hPP)).2).2.2 PP
      · exact ⟨fun h => absurd (Or.inl h) hPP, fun h => absurd (Or.inr h) hPP⟩
  let A : Subgroup (GA D V) := (Formalism.L2.DIV.lev D.sp.cm V.gram s.β s.L).comap (Lev.finE V)
  have hAset : (A : Set (GA D V)) = levSet s := rfl
  have hfinK : ∀ g ∈ A, (GlobalTheory.AutMult.toFin V g : GA D V) ∈ K := fun g hg =>
    ⟨(GlobalTheory.AutMult.toFin V g).2, Subgroup.mem_comap.2 (by rw [GlobalTheory.ChainOnto.HaarInf.finE_toFin]; exact Subgroup.mem_comap.1 hg)⟩
  have hAopen : IsOpen (A : Set (GA D V)) := by
    obtain ⟨U, hU, hUK⟩ := h1
    let Lf : Subgroup (GfC V) := K.subgroupOf (GfC V)
    have hLf : IsOpen (Lf : Set (GfC V)) := by
      refine Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) (fun k hk => ?_) (hU.preimage continuous_subtype_val)
      exact hUK k hk k.2
    have e : (A : Set (GA D V)) = GlobalTheory.AutMult.toFin V ⁻¹' (Lf : Set (GfC V)) := by
      ext g
      refine ⟨fun hg => hfinK g hg, fun hg => ?_⟩
      have := Subgroup.mem_comap.1 hg.2
      refine Subgroup.mem_comap.2 ?_
      rw [← GlobalTheory.ChainOnto.HaarInf.finE_toFin]; exact this
    rw [e]; exact hLf.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have hAint : (A : Set (GA D V)) ⊆ intOff c s := fun g hg => ((hloc g).1 hg).1
  let I : Subgroup (GA D V) :=
    { carrier := intOff c s
      mul_mem' := fun {a b} ha hb v hv => by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)
      one_mem' := fun v _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun {a} ha v hv => by rw [map_inv]; exact inv_mem (ha v hv) }
  have hIopen : IsOpen (I : Set (GA D V)) := Subgroup.isOpen_mono (H₁ := A) hAint hAopen
  have hker : {g : GA D V | g ∈ A ∧ GlobalTheory.AutMult.toInf V g = 1} = (K : Set (GA D V)) := by
    ext g
    simp only [Set.mem_setOf_eq, GlobalTheory.ChainOnto.HaarInf.toInf_eq_one_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hKc : IsCompact (K : Set (GA D V)) :=
    GlobalTheory.T.isCompact_finite_adelic_subgroup_integral_open D V s.Λ hsd K inf_le_left h3 h1
  have hpi : ∀ b : GinfC V, GlobalTheory.AutMult.toInf V ((GinfC V).subtype b) = b := fun b => GlobalTheory.AutMult.toInf_coe b
  have hiA : ∀ b : GinfC V, (GinfC V).subtype b ∈ A := fun b => by
    refine Subgroup.mem_comap.2 ?_
    rw [Subgroup.subtype_apply, GlobalTheory.ChainOnto.HaarInf.finE_of_mem_ginfC V b.2]; exact one_mem _
  have hHaar : (Measure.map (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V)))).IsHaarMeasure :=
    GlobalTheory.T.map_restrict_isHaar_of_open_product_compact (GA D V) (GinfC V) s.ν A (GinfC V).subtype (GlobalTheory.AutMult.toInf V) hAopen
      continuous_subtype_val (GlobalTheory.AutMult.continuous_toInf V) hpi hiA (hker ▸ hKc)
  refine ⟨hAopen.measurableSet, hIopen.measurableSet, hloc, fun g hg => ?_, fun κ hκ =>
    ⟨GlobalTheory.ChainOnto.LevelFacts.levChi_norm s.β s.L κ, h3 κ hκ⟩, ?_⟩
  · exact ⟨GlobalTheory.AutMult.toInf V g, GlobalTheory.AutMult.toFin V g, hfinK g hg, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  refine ⟨_, hHaar, fun f F hf hF => ?_⟩
  have hmeas : AEMeasurable (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V))) :=
    (GlobalTheory.AutMult.continuous_toInf V).measurable.aemeasurable
  have hFA : ∀ g ∈ (A : Set (GA D V)), F g = f (GlobalTheory.AutMult.toInf V g) := fun g hg => by
    conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
    exact hF _ _ (hfinK g hg)
  have hint : IntegrableOn (fun g => f (GlobalTheory.AutMult.toInf V g)) (A : Set (GA D V)) s.ν :=
    (integrable_map_measure hf.aestronglyMeasurable hmeas).1 hf
  refine ⟨hint.congr_fun (fun g hg => (hFA g hg).symm) hAopen.measurableSet, ?_⟩
  rw [← hAset, setIntegral_congr_fun hAopen.measurableSet hFA, integral_map hmeas hf.aestronglyMeasurable]

end GlobalTheory.ChainTw.LevLoc

end
