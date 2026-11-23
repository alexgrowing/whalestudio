import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValConjSubLt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace.TraceFwd

open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge GlobalTheory.RootEx

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_colGroup {κ τ n : ℕ} (e : XIx (Fin κ) (Fin τ) 0 ≃ Fin n) (he : IsOrd xPos e) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hint : ∀ a b, valuation k (g.val a b) ≤ 1)
    (h : ∀ a b, e b ≤ e a → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1) : g ∈ colGroup k κ (Fin τ) := by
  have hp : ∀ c, colPos κ (Fin τ) c = (e c).val := fun c => by
    rw [he c]
    rcases c with (c | c) | c
    exacts [rfl, c.elim0, c.1.elim0]
  let M : Matrix (XIx (Fin κ) (Fin τ) 0) (XIx (Fin κ) (Fin τ) 0) 𝒪[k] := Matrix.of fun a b => ⟨g.val a b, hint a b⟩
  have hM : ∀ a b, e b ≤ e a → (residue 𝒪[k]).mapMatrix M a b = (1 : Matrix _ _ 𝓀[k]) a b := fun a b hab => by
    have h1 : (1 : Matrix _ _ 𝓀[k]) a b = residue 𝒪[k] ((1 : Matrix _ _ 𝒪[k]) a b) := by
      simp only [Matrix.one_apply, apply_ite (residue 𝒪[k]), map_one, map_zero]
    rw [h1, RingHom.mapMatrix_apply, Matrix.map_apply, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    refine Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 ?_
    convert h a b hab using 2
    simp only [M, Matrix.one_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hdet : ((residue 𝒪[k]).mapMatrix M).det = 1 := by
    rw [← Matrix.det_submatrix_equiv_self e.symm, Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      rw [Matrix.submatrix_apply, hM _ _ le_rfl, Matrix.one_apply_eq]
    · intro i j hij
      have hij' : j < i := hij
      rw [Matrix.submatrix_apply, hM _ _ (by simpa using hij'.le), Matrix.one_apply_ne (e.symm.injective.ne hij'.ne')]
  have hu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, ← residue_ne_zero_iff_isUnit, RingHom.map_det, hdet]
    exact one_ne_zero
  refine ⟨_, ⟨hu.unit, Units.ext ?_, rfl⟩, fun a b hab => ?_⟩
  · ext a b
    rfl
  · rw [hp, hp] at hab
    exact hM a b hab

theorem embX_mem {s κ τ : ℕ} (S : SymData k s κ) (g : GL (XIx (Fin κ) (Fin τ) 0) k) (hg : g ∈ colGroup k κ (Fin τ)) :
    embX (s + 1) g ∈ ((S.T (Fin τ)).lev 0 (s + 1) (Nat.zero_add _)).J := by
  obtain ⟨-, h2, -⟩ := GlobalTheory.FirstVertexFrame.firstVertex_typeChain k S.ψ S.ϖ s (Fin τ) κ S.P
    (GlobalTheory.SymShape.sym_shape _ _ _ _ _ _ _ S.sym) S.μ S.tame (s + 1) (Nat.zero_add _)
  exact (h2 g hg).1

set_option maxHeartbeats 1000000 in

theorem colGroup_of_red {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (V : HSp D) {n κ τ : ℕ} (hr : V.rank = n) (hn : n = κ) (F : Frame k V.rank (XIx (Fin κ) (Fin τ) 0)) (hF : IsStdFr xPos F)
    {x : GA D V} {y : GL (Fin n) (GlobalTheory.AdForm.EF D)} (hy : GlobalTheory.AdForm.finM V hr x = y.1)
    {A : GL (Fin n) (𝓞 D.host.E ⧸ PP.asIdeal)} (hA : LevRead.IsRed (F := D.host.F) PP y A.1)
    (hU : A ∈ Formalism.L2.Col.uniUT n _ κ []) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hg : (mt V x).map q.pr = F.β * g.val * F.γ) : g ∈ colGroup k κ (Fin τ) := by
  subst hr
  obtain ⟨e, he, hβ⟩ := hF
  choose R hR hR' using hA
  have hM : ∀ i j, valuation k ((mt V x).map q.pr i j - q.pr (incA D (R i j))) < 1 := fun i j => by
    have h2 : y.1 i j = toEAf D (mt V x i j) := by
      rw [← hy]
      rfl
    have h3 := LevChi.val_pr_lt q hq (z := mt V x i j - incA D (R i j)) (by
      rw [RingHom.map_sub, ← h2, RingHom.map_sub]
      exact (congrArg (fun t => Valued.v (adAt D.host.F PP (y.1 i j) - t)) (adAt_inclE D.host.F PP _)).trans_lt (hR' i j))
    rwa [RingHom.map_sub] at h3
  have hgM : ∀ a b, g.val a b = (mt V x).map q.pr (e a) (e b) := fun a b => by
    have h1 : (mt V x).map q.pr * F.β = F.β * g.val := by rw [hg, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    have h2 := congrFun (congrFun h1 (e a)) b
    rw [hβ] at h2
    simpa [Matrix.mul_apply, Matrix.one_apply] using h2.symm
  refine mem_colGroup e he g (fun a b => ?_) fun a b hab => ?_
  · have := (valuation k).map_add_le (hM (e a) (e b)).le (LevelTest.val_le_one q (R (e a) (e b)))
    rwa [sub_add_cancel, ← hgM] at this
  · obtain ⟨-, h1, h2⟩ := Formalism.L2.Col.mem_uniUT.1 hU
    have ha : (e a).val < κ := hn ▸ (e a).2
    rcases hab.eq_or_lt with h | h
    · obtain rfl : b = a := e.injective h
      have h3 : R (e b) (e b) - 1 ∈ PP.asIdeal := by
        rw [← Ideal.Quotient.eq, hR, h2 _ ha, map_one]
      have := (valuation k).map_add_lt (hM (e b) (e b)) ((LevelTest.val_lt_one_iff q hq _).2 h3)
      rw [← hgM] at this
      simpa using this
    · have h3 : R (e a) (e b) ∈ PP.asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, hR, h1 _ _ ha h]
      have := (valuation k).map_add_lt (hM (e a) (e b)) ((LevelTest.val_lt_one_iff q hq _).2 h3)
      rw [sub_add_cancel, ← hgM] at this
      rwa [Matrix.one_apply_ne (fun h' : a = b => h.ne' (congrArg e h')), sub_zero]

end Loc

theorem exists_red {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : TC B X) (hI : I.Ok) {u : B.Word} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {J : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) B.host.E} (hJ : J = 1)
    (S : Formalism.L2.Forms.StepLevel B.host.F B.host.E B.sp.cm.sig J T f bad) {y : (I.stp u I.mu0 0).Cl → TC.GA B (B.R.N 0)}
    {st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E} {k : Unit → TC.GA B (B.R.N 0)}
    (hR : I.Reads u I.mu0 0 (fun _ => ()) (fun _ => S.Lb) (fun _ => S.U) (fun _ => S.chi) y st k) (x : S.U)
    (w : HeightOneSpectrum (𝓞 B.host.E)) (hw : w ∈ (B.primes X).vGs) :
    ∃ A : GL (Fin (B.R.N 0)) (𝓞 B.host.E ⧸ w.asIdeal), A ∈ Formalism.L2.Col.uniUT (B.R.N 0) _ B.R.k [] ∧ LevRead.IsRed w x.1 A.1 := by
  subst hJ
  obtain ⟨h, h1, h2, -⟩ := TC.GLev0.chi_prod I S hR hI x
  exact ⟨_, inv_mem (h1 ⟨w, hw⟩), h2 ⟨w, hw⟩⟩

set_option maxHeartbeats 1000000 in

theorem traceAtG_of_mem : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (F0 W u).cls0.lev.U → GlobalTheory.FamTrace.TraceAtG a κ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha _ row col _ κ _ y hκy hy i g hg
  obtain ⟨hS⟩ := hA.tr.std
  obtain ⟨hP⟩ := hA.tr.pins
  obtain ⟨k₀, hR⟩ := (hS u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  obtain ⟨A, hU, hA'⟩ := exists_red I hA.tr.ok ((TC.spaces_in_coordinates I hA.tr.ok hP l Z).2.2.2 0 (Nat.zero_le _)).1
    ((W.R.T.cols.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).lev hR ⟨_, hy⟩ (a.pl i).1 ((hA.lev.2.1 _).1 (a.pl i).2)
  letI := (a.G i).fld; letI := (a.G i).val; letI := (a.G i).top; letI := (a.G i).loc
  exact embX_mem (a.G i).S g (colGroup_of_red (a.G i).q ((ha.tie row col).2.idem i).1 ((I.rec7 l Z).sp.X 0)
    (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) (show B.R.N 0 = B.R.k by simp [Ranks.N]) _
    ((ha.stdG i).1 0 (Nat.zero_le _)) hκy hA' hU g hg)

end GlobalTheory.FamTrace.TraceFwd

end
