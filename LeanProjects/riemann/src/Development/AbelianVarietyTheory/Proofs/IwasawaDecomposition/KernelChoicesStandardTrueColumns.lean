import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompanionCrd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtTwTieStd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdStdBot
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem memSideU_std {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hOk : I.Ok) (hP : TC.Pins B X) (hS : I.StdKer l Z t) (hpi : ex.errX.piT = X.piT) : t.MemSideU := by
  intro u
  refine ⟨?_, ?_, ?_⟩
  · show (t.O u I.mu0).mt = _
    rw [hS.O.mt u I.mu0, hOk.trueColumnChoices_heckeChar_reference_eq_one, tildeQ_one]
    funext j
    split_ifs
    · exact mul_one _
    · rfl
  · intro i c
    show (t.O u I.mu0).dt i c = _
    rw [hS.O.dt u I.mu0 i c]
    rfl
  · rw [hpi]
    exact memLatAt_std I hOk hP l Z u (t.memObj u) fun i c => hS.O.lat u I.mu0 i c

theorem piSide_std {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hS : I.StdKer l Z t) (hpi : ex.errX.piT = X.piT) : t.PiSide := by
  obtain ⟨hX, hseam, hPr, -, -, -, hword, -⟩ := hS
  cases t
  dsimp only at *
  subst hX
  cases hseam
  cases hPr
  cases hword
  intro u
  rw [hpi]
  rfl

theorem chOk_std {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hOk : I.Ok) (hS : I.StdKer l Z t) : t.Ch.Ok ∧ MuValTie t.Ch t.glob ∧ ∀ a, (t.cst a).sharp = true := by
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, -⟩ := hS
  cases t
  dsimp only at *
  subst hX
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hglob
  exact ⟨hOk.ch_ok, fun j v h => hOk.ch_tied.muVal j v h, fun a => hOk.sharp a⟩

theorem k_pins_of_fields {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hOk : I.Ok) (hP : TC.Pins B X)
    (hX : t.X = B.fields) (hseam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)) (hPr : HEq t.Pr (B.primes X))
    (hCh : HEq t.Ch I.Ch) (hsel : HEq t.sel I.sel) (hSS : t.S = I.S) (hword : HEq t.word fun u : B.Word => u)
    (htup : HEq t.tup I.tup) (hcst : HEq t.cst I.cst) (hglob : HEq t.glob I.glob) (hO : I.StdO l Z Y.Qp t.O)
    (hpi : ex.errX.piT = X.piT) : t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  have hU : t.MemSideU := by
    intro u
    refine ⟨?_, ?_, ?_⟩
    · show (t.O u I.mu0).mt = _
      rw [hO.mt u I.mu0, hOk.trueColumnChoices_heckeChar_reference_eq_one, tildeQ_one]
      funext j
      split_ifs
      · exact mul_one _
      · rfl
    · intro i c
      show (t.O u I.mu0).dt i c = _
      rw [hO.dt u I.mu0 i c]
      rfl
    · rw [hpi]
      exact memLatAt_std I hOk hP l Z u (t.memObj u) fun i c => hO.lat u I.mu0 i c
  have hPi : t.PiSide := by
    clear hU hO hglob hcst htup hSS hsel hCh
    cases t
    dsimp only at *
    subst hX
    cases hseam
    cases hPr
    cases hword
    intro u
    rw [hpi]
    rfl
  have hC : t.Ch.Ok ∧ MuValTie t.Ch t.glob ∧ ∀ a, (t.cst a).sharp = true := by
    clear hU hPi
    cases t
    dsimp only at *
    subst hX
    cases hPr
    cases hCh
    cases hsel
    subst hSS
    cases htup
    cases hcst
    cases hglob
    exact ⟨hOk.ch_ok, fun j v h => hOk.ch_tied.muVal j v h, fun a => hOk.sharp a⟩
  have hM : t.MtTwTie := by
    clear hU hPi hC
    cases t
    dsimp only at *
    subst hX
    cases hseam
    subst hSS
    cases htup
    refine ⟨(QuotientGroup.mk' (KDq B.host I.SQ)).comp (finIdele (afIso B.host.F B.host.E)), ⟨fun y => ?_, fun k z hz => ?_⟩,
      fun μ _ _ => ⟨tildeQ B.host I.SQ (I.xi μ), fun x => ?_, fun u => ?_⟩⟩
    · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective (show DtQ B.host I.SQ from y)
      refine ⟨finAf B.host.F B.host.E a, ?_⟩
      exact mk_eq_of_snd_eq B.host I.SQ (afIso_finAf B.host.F B.host.E a)
    · have hz' : (show B.host.E from z.1) * B.host.conj (k : B.host.E) = k := hz
      show (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) (ratId B.host.F B.host.E k)) : DtQ B.host I.SQ) = e1Q B.host I.SQ z
      rw [← isUnitaryPointsMap_unitaryRationalPointsFiner B.host I.SQ k z hz']
      refine mk_eq_of_snd_eq B.host I.SQ ?_
      show afIso B.host.F B.host.E ((k : B.host.E) ⊗ₜ[B.host.F] 1) = _
      rw [afIso_tmul_one]
      rfl
    · have hk : KDq B.host I.SQ ≤ ((I.xi μ).1.comp (finPartI B.host.E)).ker :=
        (KDq_anti B.host (I.Q_subset_SQ μ)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk).2.2 μ).1
      show tildeQ B.host I.SQ (I.xi μ) (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) x)) = _
      rw [tildeQ_mk B.host I.SQ hk, finPartI_eq_self fun _ => rfl]
      exact Units.ext ((hOk.xi_reads μ).apply _ x rfl)
    · rw [hO.mt u μ]
      rfl
  exact ⟨⟨hC.1, hC.2.1, hPi, fun u _ => hU u⟩, hU, hM, hC.2.2⟩

theorem k_pins_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKerTie l Z t → ex.errX.piT = X.piT → t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS hpi
  exact k_pins_of_fields I l Z t hOk hP hS.X_eq hS.seam hS.Pr hS.Ch hS.sel hS.S hS.word hS.tup hS.cst hS.glob hS.O hpi

theorem k_pins : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ex.errX.piT = X.piT → t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS hpi
  have hU := memSideU_std I l Z t hOk hP hS hpi
  obtain ⟨h1, h2, h3⟩ := chOk_std I l Z t hOk hS
  exact ⟨⟨h1, h2, piSide_std I l Z t hS hpi, fun u _ => hU u⟩, hU, mtTwTie_std I hOk l Z L hT Gi Gl K Y cX ex t hS, h3⟩

end GlobalTheory.Mem.Col2.TC

end
