import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionIffForallPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceUnitaryStabilizesSelfDualLatticeIffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBesselCoreMatrixEqBlockDiagonalOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmulOfMemFlagSubOne
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
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffTrace
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

theorem supp_mulVec' {D : D7} {m n : ℕ} (X : Matrix (Fin m) (Fin n) (AE D)) {I : Ideal (AE D)} {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) (i : Fin m) : (X *ᵥ y) i ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem colMul_zero' {D : D7} {m n : ℕ} (x : Mx D m n) (i : Fin n) : colMul x i 0 = 0 := by
  funext r; simp [colMul]

theorem glued_stab_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (q : Unif k) (P : Pair k n) (g : GL n k) :
    GlobalTheory.RootEx.embX 1 g • gluedS q 1 P.ker P.vec = gluedS q 1 P.ker P.vec ↔ g • P = P := by
  rw [GlobalTheory.LevelUnfold.embX_smul_gluedS, Pair.smul_eq_iff P.hasVal_vec]
  constructor
  · intro h
    have h1 : g • P.ker = P.ker := by
      have := GlobalTheory.LevelUnfold.interX_gluedS (q := q) (le_refl 1) (g • P.ker) (g • P.vec)
      rw [h, GlobalTheory.LevelUnfold.interX_gluedS (le_refl 1)] at this
      exact this.symm
    refine ⟨h1, ?_⟩
    have h2 := GlobalTheory.LevelUnfold.glue_mem_gluedS (q := q) (c := 1) (g • P.ker) (g • P.vec)
    rw [h] at h2
    exact (GlobalTheory.LevelUnfold.glue_mem_gluedS_iff (le_refl 1)).1 h2
  · rintro ⟨h1, h2⟩
    rw [h1]
    exact GlobalTheory.LevelUnfold.gluedS_congr h2

theorem moves_emb_iff {D : D7} {S A B : HSp D} (o : OrthDec S A B) (M : GlobalTheory.FinPl.Lat S) (LA : GlobalTheory.FinPl.Lat A)
    (LB : GlobalTheory.FinPl.Lat B) (v : GlobalTheory.FinPl.Pl D) (h : GlobalTheory.FinPl.OrthAt o M LA LB v) (κ : GA D A) :
    GlobalTheory.FinPl.Moves S (o.emb (κ, 1)) M M (· = v) ↔ GlobalTheory.FinPl.Moves A κ LA LA (· = v) := by
  have e1 : ∀ y, o.pA *ᵥ (mt S (o.emb (κ, 1)) *ᵥ y) = mt A κ *ᵥ (o.pA *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; congr 1; exact o.pA_emb κ 1
  have e2 : ∀ y, o.pB *ᵥ (mt S (o.emb (κ, 1)) *ᵥ y) = o.pB *ᵥ y := fun y => by
    rw [Matrix.mulVec_mulVec, o.pB_emb]; simp [Formalism.L2.Theta.mt]
  constructor
  · intro hM yA hyA
    have hy : ∀ i, (o.jA *ᵥ yA) i ∈ idAt D (· = v) := supp_mulVec' _ hyA
    have hA1 : o.pA *ᵥ (o.jA *ᵥ yA) = yA := by rw [Matrix.mulVec_mulVec, o.pA_jA, Matrix.one_mulVec]
    have hB1 : o.pB *ᵥ (o.jA *ᵥ yA) = 0 := by rw [Matrix.mulVec_mulVec, o.pB_jA, Matrix.zero_mulVec]
    have := hM _ hy
    rw [h, h, e1, e2, hA1, hB1] at this
    simpa only [zero_mem, and_true] using this
  · intro hA y hy
    rw [h, h, e1, e2, ← hA _ (supp_mulVec' _ hy)]

theorem carriesLattice_wittEmbedding_iff_core {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (N : GlobalTheory.FinPl.Lat S) (M : GlobalTheory.FinPl.Lat S₀)
    (v : GlobalTheory.FinPl.Pl D) (h : GlobalTheory.FinPl.MonoAt d N M v) (g : GA D S₀) :
    GlobalTheory.FinPl.Moves S (d.emb0 g) N N (· = v) ↔ GlobalTheory.FinPl.Moves S₀ g M M (· = v) := by
  have eX : ∀ y, d.pX *ᵥ (mt S (d.emb0 g) *ᵥ y) = d.pX *ᵥ y := fun y => by
    rw [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]
  have eY : ∀ y, d.pY *ᵥ (mt S (d.emb0 g) *ᵥ y) = d.pY *ᵥ y := fun y => by
    rw [Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]
  have e0 : ∀ y, d.p0 *ᵥ (mt S (d.emb0 g) *ᵥ y) = mt S₀ g *ᵥ (d.p0 *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; congr 1; exact d.wittDecomp_projAnisotropic_anisotropicEmbedding g
  constructor
  · intro hM y₀ hy₀
    have hy : ∀ i, (d.j0 *ᵥ y₀) i ∈ idAt D (· = v) := supp_mulVec' _ hy₀
    have hX1 : d.pX *ᵥ (d.j0 *ᵥ y₀) = 0 := by rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]
    have hY1 : d.pY *ᵥ (d.j0 *ᵥ y₀) = 0 := by rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]
    have h01 : d.p0 *ᵥ (d.j0 *ᵥ y₀) = y₀ := by rw [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]
    have := hM _ hy
    rw [h, h, eX, eY, e0, hX1, hY1, h01] at this
    simpa only [Pi.zero_apply, colMul_zero', zero_mem, true_and, implies_true] using this
  · intro hA y hy
    rw [h, h, eX, eY, e0, ← hA _ (supp_mulVec' _ hy)]

theorem exists_gl_frame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : GlobalTheory.FinPl.SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p S n)
    (κ : GA D S) : ∃ g : GL n k, (mt S κ).map p.pr = β.b * g.val * β.b' := by
  have e1 : mt S κ * mt S κ⁻¹ = 1 := by
    rw [show mt S κ * mt S κ⁻¹ = mt S (κ * κ⁻¹) from rfl, mul_inv_cancel]; rfl
  have e2 : mt S κ⁻¹ * mt S κ = 1 := by
    rw [show mt S κ⁻¹ * mt S κ = mt S (κ⁻¹ * κ) from rfl, inv_mul_cancel]; rfl
  have hM : (mt S κ).map p.pr * (mt S κ⁻¹).map p.pr = 1 := by
    rw [← Matrix.map_mul, e1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hM' : (mt S κ⁻¹).map p.pr * (mt S κ).map p.pr = 1 := by
    rw [← Matrix.map_mul, e2]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨β.b' * (mt S κ).map p.pr * β.b, β.b' * (mt S κ⁻¹).map p.pr * β.b, ?_, ?_⟩, ?_⟩
  · calc β.b' * (mt S κ).map p.pr * β.b * (β.b' * (mt S κ⁻¹).map p.pr * β.b)
          = β.b' * ((mt S κ).map p.pr * (β.b * β.b') * (mt S κ⁻¹).map p.pr) * β.b := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [β.bb', Matrix.mul_one, hM, Matrix.mul_one, β.b'b]
  · calc β.b' * (mt S κ⁻¹).map p.pr * β.b * (β.b' * (mt S κ).map p.pr * β.b)
          = β.b' * ((mt S κ⁻¹).map p.pr * (β.b * β.b') * (mt S κ).map p.pr) * β.b := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [β.bb', Matrix.mul_one, hM', Matrix.mul_one, β.b'b]
  · show _ = β.b * (β.b' * (mt S κ).map p.pr * β.b) * β.b'
    calc (mt S κ).map p.pr = (β.b * β.b') * (mt S κ).map p.pr * (β.b * β.b') := by
          rw [β.bb', Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.OffTrace

open GlobalTheory.LatPair GlobalTheory.FinPl in
open scoped Pointwise in

theorem GlobalTheory.OffTrace.embA_moves_off_level_iff : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), (GlobalTheory.FinPl.Moves (Yc (I.rec7 l Z) 0) (embA a.d.B.d a.d.B.o κ) (a.v.N 0) (a.v.N 0) (fun p => p ∉ a.v.gP) ↔ GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun p => p ∉ a.v.gP) ∧ GlobalTheory.FamTrace.KeepsPairs a κ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col hc κ hκ
  letI := a.fld; letI := a.val; letI := a.top; letI := a.loc
  have h0 : 0 + 2 * (I.rec7 l Z).R.rS + 2 = (I.rec7 l Z).R.m := by
    have := Formalism.BasicNotions.Ranks.rS_two (I.rec7 l Z).R; omega
  have hB := ha.bot.1 h0
  have key : ∀ B' : BesLev (I.rec7 l Z) (I.rec7 l Z).R.rS, B' = (commOf (pk W) u a.g).B 0 _ h0 →
      HEq (embA B'.d B'.o) (embA ((commOf (pk W) u a.g).B 0 _ h0).d ((commOf (pk W) u a.g).B 0 _ h0).o) := by
    rintro _ rfl; rfl
  have hE := eq_of_heq (key a.d.B.lev hB)
  have hE' : embA a.d.B.d a.d.B.o κ = ((commOf (pk W) u a.g).B 0 _ h0).d.emb0 (((commOf (pk W) u a.g).B 0 _ h0).o.emb (κ, 1)) :=
    DFunLike.congr_fun hE κ
  rw [hE']
  have hm : 0 < (I.rec7 l Z).R.m := by omega
  have hN : Submodule.IsLattice (I.rec7 l Z).host.E (a.v.N 0) := (ha.vis.sd 0 hm).1
  have hL : Submodule.IsLattice (I.rec7 l Z).host.E (a.g.x 0).L := (ha.x 0 (Nat.zero_le _)).sd.1
  rw [GlobalTheory.T.carriesLatticeCompletion_iff_forall_place _ _ _ hN, GlobalTheory.T.carriesLatticeCompletion_iff_forall_place _ _ _ hL]
  have hA : ∀ v, Moves ((commOf (pk W) u a.g).V 0)
      (((commOf (pk W) u a.g).B 0 _ h0).d.emb0 (((commOf (pk W) u a.g).B 0 _ h0).o.emb (κ, 1))) (a.v.N 0) (a.v.N 0) (· = v) ↔
      Moves ((commOf (pk W) u a.g).B 0 _ h0).V₀ (((commOf (pk W) u a.g).B 0 _ h0).o.emb (κ, 1)) (a.o.M 0 _ h0)
        (a.o.M 0 _ h0) (· = v) := fun v =>
    GlobalTheory.OffTrace.carriesLattice_wittEmbedding_iff_core _ _ _ v ((ha.shape.good v).bf 0 _ h0).monoV _
  have hoff : ∀ v, v ∉ a.v.tP → (Moves ((commOf (pk W) u a.g).V 0)
      (((commOf (pk W) u a.g).B 0 _ h0).d.emb0 (((commOf (pk W) u a.g).B 0 _ h0).o.emb (κ, 1))) (a.v.N 0) (a.v.N 0) (· = v) ↔
      Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (· = v)) := by
    intro v hv
    obtain ⟨LL, -, hO⟩ := (ha.shape.split v hv).core 0 _ h0
    exact (hA v).trans (GlobalTheory.OffTrace.moves_emb_iff _ _ _ _ v hO κ)
  have hcore : ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X 0).rank) a.k),
      (mt ((I.rec7 l Z).sp.X 0) κ).map (a.o.p i).pr = (a.o.β 0 i).b * g.val * (a.o.β 0 i).b' →
      (Moves ((commOf (pk W) u a.g).V 0)
        (((commOf (pk W) u a.g).B 0 _ h0).d.emb0 (((commOf (pk W) u a.g).B 0 _ h0).o.emb (κ, 1))) (a.v.N 0) (a.v.N 0)
        (· = (a.o.p i).v) ↔ g • a.o.Q 0 i = a.o.Q 0 i) := by
    intro i g hg
    have hgl := ha.shape.glued 0 _ h0 i
    exact (hA _).trans ((GlobalTheory.T.splitPlace_unitary_stabilizes_selfDual_lattice_iff (a.o.β₀ 0 _ h0 i) (a.o.M 0 _ h0) _
      ((ha.shape.good (a.o.p i).v).bf 0 _ h0).sdV₀ hgl.lat _ _
      (GlobalTheory.T.splitPlace_besselCore_matrix_eq_blockDiagonal_one _ _ _ hgl.sum κ g hg)).trans (GlobalTheory.OffTrace.glued_stab_iff _ _ _))
  have hX : ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X 0).rank) a.k),
      (mt ((I.rec7 l Z).sp.X 0) κ).map (a.o.p i).pr = (a.o.β 0 i).b * g.val * (a.o.β 0 i).b' →
      (Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (· = (a.o.p i).v) ↔ g • (a.o.Q 0 i).lat = (a.o.Q 0 i).lat) :=
    fun i g hg => GlobalTheory.T.splitPlace_unitary_stabilizes_selfDual_lattice_iff (a.o.β 0 i) (a.g.x 0).L _ (ha.x 0 (Nat.zero_le _)).sd
      (ha.shape.pre.latT 0 (Nat.zero_le _) i) κ g hg
  have hTg : ∀ i, (a.o.p i).v ∉ a.v.gP := fun i hg' =>
    Finset.disjoint_left.1 ha.vis.disj hg' ((ha.shape.pre.tP _).2 ⟨i, rfl⟩)
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun i g hg => (hcore i g hg).1 (h _ (hTg i))⟩
    by_cases hT : v ∈ a.v.tP
    · obtain ⟨i, rfl⟩ := (ha.shape.pre.tP v).1 hT
      obtain ⟨g, hg⟩ := GlobalTheory.OffTrace.exists_gl_frame (a.o.β 0 i) κ
      have h1 := (hcore i g hg).1 (h _ hv)
      exact (hX i g hg).2 (by rw [← Pair.smul_lat, h1])
    · exact (hoff v hT).1 (h v hv)
  · rintro ⟨h1, h2⟩ v hv
    by_cases hT : v ∈ a.v.tP
    · obtain ⟨i, rfl⟩ := (ha.shape.pre.tP v).1 hT
      obtain ⟨g, hg⟩ := GlobalTheory.OffTrace.exists_gl_frame (a.o.β 0 i) κ
      exact (hcore i g hg).2 (h2 i g hg)
    · exact (hoff v hT).2 (h1 v hv)
