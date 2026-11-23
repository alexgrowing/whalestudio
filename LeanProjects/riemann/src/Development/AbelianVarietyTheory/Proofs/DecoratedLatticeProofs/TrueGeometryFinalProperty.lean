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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesOfMatrixMemLevelZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TraceAtG

theorem mat_embA_besFrame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {ρ : ℕ} (B : BesLev D ρ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)) (hF : p.IsBesFrame B s FA F) (h : GA D B.A)
    (g₀ : GL n k) (hh : (mt B.A h).map p.π = FA.β * g₀.val * FA.γ) :
    (mt B.V (embA B.d B.o h)).map p.π = F.β * (GlobalTheory.RootEx.embX c g₀).val * F.γ := by
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  have eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  have hint : (mt B.V (B.d.emb0 (B.o.emb (h, 1)))).map p.π * ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) =
      (rat (B.d.i₀ * B.o.iA)).map p.π * FA.β * g₀.val := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, eA, Matrix.map_mul, hh]
    simp only [Matrix.mul_assoc]
    rw [FA.γβ, Matrix.mul_one]
  refine GlobalTheory.LocGrp.eq_embX F _ g₀ ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 hint fun j => ?_
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine GlobalTheory.LocGrp.fix_vec (GlobalTheory.LocGrp.map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r => (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩ (hY _ j (by simp only; omega))

end GlobalTheory.TraceAtG

end

noncomputable section
open GlobalTheory.FamTrace

theorem GlobalTheory.TraceAtG.levAtG_embA_iff : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), (GlobalTheory.FamTrace.LevAtG a (embA a.d.B.d a.d.B.o κ) ↔ GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun p => p ∈ a.v.gP) ∧ GlobalTheory.FamTrace.TraceAtG a κ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col hc κ hκ
  have hmi : ∀ i, 0 + 2 * (I.rec7 l Z).R.rS + 2 = (I.rec7 l Z).R.m := fun i => by
    have h1 := (a.G i).hs
    have h2 := (a.G i).S.odd
    unfold Ranks.rS; omega

  have hbes : ∀ i, (ofSplit (a.G i).q).IsBesFrame a.d.B.lev ((a.G i).sc 0) ((a.G i).FX 0 (Nat.zero_le _))
      ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)) := by
    intro i
    have hm := hmi i
    have key : ∀ Bl : BesLev (I.rec7 l Z) (I.rec7 l Z).R.rS, Bl = (commOf (pk W) u a.g).B 0 _ hm →
        ∀ (FA : Frame (a.G i).k Bl.A.rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0))
          (F : Frame (a.G i).k Bl.V.rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) 0 ⊕ Fin ((a.G i).s + 1))), HEq FA ((a.G i).FX 0 (Nat.zero_le _)) →
          HEq F ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)) → (ofSplit (a.G i).q).IsBesFrame Bl ((a.G i).sc 0) FA F := by
      rintro Bl rfl FA F h1 h2
      cases h1; cases h2
      exact (a.G i).bes 0 _ hm _ _
    exact key _ (ha.bot.1 hm) _ _ HEq.rfl HEq.rfl
  have hmat : ∀ i g, IsMatrixInFrameOfXZero (a.G i) κ g → (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) (embA a.d.B.d a.d.B.o κ)
      (GlobalTheory.RootEx.embX ((a.G i).s + 1) g) := fun i g hg =>
    GlobalTheory.TraceAtG.mat_embA_besFrame (ofSplit (a.G i).q) a.d.B.lev _ _ _ (hbes i) κ g hg
  have huniq : ∀ i x m m', (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m →
      (a.G i).Mat 0 ((a.G i).s + 1) (Nat.zero_add _) x m' → m = m' := by
    intro i x m m' h1 h2
    unfold GLoc.Mat at h1 h2
    rw [h1] at h2
    refine Units.ext ?_
    have := congrArg (fun M => ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).γ * M *
      ((a.G i).FY 0 ((a.G i).s + 1) (Nat.zero_add _)).β) h2
    simp only [← Matrix.mul_assoc, Frame.γβ, Matrix.one_mul] at this
    simpa only [Matrix.mul_assoc, Frame.γβ, Matrix.mul_one] using this
  have hex : ∀ i, ∃ g, IsMatrixInFrameOfXZero (a.G i) κ g := fun i =>
    ⟨coordHom _ (a.G i).q.pr _ _ ((a.G i).FX 0 (Nat.zero_le _)).βγ ((a.G i).FX 0 (Nat.zero_le _)).γβ κ,
      (eq_coordHom_iff _ _ _ _ _ _ κ _).2 rfl⟩
  constructor
  · intro hlev
    have htr : TraceAtG a κ := fun i g hg => hlev i _ (hmat i g hg)
    refine ⟨?_, htr⟩
    have hsd := (ha.x 0 (Nat.zero_le _)).sd
    have hloc : ∀ i, GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (· = (a.G i).q.v) := by
      intro i
      obtain ⟨g, hg⟩ := hex i
      have hlev0 := htr i g hg
      let β := GlobalTheory.SplitLat.frameOf (a.G i).q ((I.rec7 l Z).sp.X 0) _ ((a.G i).FX 0 (Nat.zero_le _))
      have hIs : β.IsLat (a.g.x 0).L (GlobalTheory.SplitLat.stdLat (a.G i).k _) := fun x => by
        rw [GlobalTheory.SplitLat.mem_std]; exact (a.G i).latX 0 (Nat.zero_le _) x
      have key := GlobalTheory.T.stabilizes_selfDual_iff_frame_matrix_stabilizes _ (a.G i).k (a.G i).q ((I.rec7 l Z).sp.X 0) _ β (a.g.x 0).L _ hsd hIs κ
      refine key.2 ?_
      have hreg := ((Chain.ofType_regular _ _ _ _ _ : ((a.G i).S.T (Fin (I.rec7 l Z).R.t)).Regular).2.2 0
        ((a.G i).s + 1) (Nat.zero_add _)).2.2
      have hst := hreg hlev0
      have hK := GlobalTheory.LevX.mem_KO_of_embX_mem_stabLat (a.G i).S.ϖ
        (stdOrd (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) (l := (a.G i).s + 1) 0 ((a.G i).s + 1) (Nat.zero_add _)) hst
      have hcoord : coordHom ((I.rec7 l Z).sp.X 0) (a.G i).q.pr β.b β.b' β.bb' β.b'b κ = g :=
        ((eq_coordHom_iff _ _ _ _ _ _ κ g).1 hg).symm
      rw [hcoord]
      exact GlobalTheory.LevX.smul_stdLat_of_mem_KO hK
    intro y hy
    have hlat := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua (I.rec7 l Z) (fun p => p ∈ a.v.gP)).2 ((I.rec7 l Z).sp.X 0)).2.2.2 (a.g.x 0).L
    have hy' : ∀ j, (mt ((I.rec7 l Z).sp.X 0) κ *ᵥ y) j ∈ GlobalTheory.FinPl.idAt (I.rec7 l Z) (fun p => p ∈ a.v.gP) := fun j => by
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun t _ => Ideal.mul_mem_left _ _ (hy t)
    have hey : ∀ v e, e ∈ GlobalTheory.FinPl.intAt (I.rec7 l Z) (· = v) → ∀ j, (e • y) j ∈ GlobalTheory.FinPl.idAt (I.rec7 l Z) (· = v) :=
      fun v e he j => by simpa [smul_eq_mul] using Ideal.mul_mem_right (y j) _ he.1
    rw [hlat y hsd.1, hlat _ hsd.1]
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨hy', fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := (ha.gpin.places v).1 hv
      rw [← Matrix.mulVec_smul]
      exact (hloc i _ (hey _ e he)).1 (h2 _ hv e he)
    · rintro ⟨-, h2⟩
      refine ⟨hy, fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := (ha.gpin.places v).1 hv
      have := h2 _ hv e he
      rw [← Matrix.mulVec_smul] at this
      exact (hloc i _ (hey _ e he)).2 this
  · rintro ⟨-, htr⟩ i m hm'
    obtain ⟨g, hg⟩ := hex i
    rw [huniq i _ _ _ hm' (hmat i g hg)]
    exact htr i g hg

end
