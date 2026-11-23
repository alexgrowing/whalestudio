import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RdLevOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimeLevelIffReductionLevelConjugateCharactStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelReadingRationalAtTwistExtendsIntegralUnitarStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleReadingLevelCharacterStatement

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix GlobalTheory.EX
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.SeeSaw.TopLevel

namespace GlobalTheory.SeeSaw.TwLev

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cl_nonempty {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι) : Nonempty (I.stX a).Cl := by
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  exact ⟨⟨(), Quotient.mk _ ⟨(DecoF.base _ _ _ _ _, ∅), Set.mem_singleton _⟩⟩⟩

theorem q_inj {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) :
    ∀ P P' : I.Q a, underPl B.host.F P.1 = underPl B.host.F P'.1 → P = P' := by
  classical
  intro P P' e
  rcases (GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 P'.1).1 (HeightOneSpectrum.ext (congrArg HeightOneSpectrum.asIdeal e.symm)) with h | h
  · exact Subtype.ext h.symm
  · exact absurd (h ▸ Finset.mem_union_right _ (GlobalTheory.Mem.Col2.ChEx.q_sub_SQ I a P'.2))
      ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk).1.split P.1 (Finset.mem_union_right _ (GlobalTheory.Mem.Col2.ChEx.q_sub_SQ I a P.2)))

set_option maxHeartbeats 2000000 in

theorem levIs_reads_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hPins : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (a : I.ι) (ha : a ≠ I.mu0) {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) 1 (I.rec7 l Z).R.f bad)
    {y lat st}
    (hO : letI := Formalism.BasicNotions.tensTopL (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F);
      ∀ᶠ (u : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))) in nhds 1,
        ∀ κ : S.U, κ.1 = u → S.chi κ = 1)
    (hK : I.ReadsP a S.Lb S.U S.chi y lat st)
    (P' : LevelP (B.primes X).vGs B.R.r ℂ) (hH : ∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (I.Ps w).H)
    (hchi : ∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (I.Ps w).H),
      ((P'.chi g : ℂˣ) : ℂ) = ∏ w, B.embLL (((I.Ps w).lam ⟨g.1 w, hg w⟩ : B.LLˣ) : B.LL))
    (cg : ℕ → ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ)
    (hcg : ∀ c (w : (B.primes X).vGs) x, ((cg (c + 1) w.1 x : ℂˣ) : ℂ) = B.embLL ((Formalism.L2.Col.chiAt I.Ch w c x : B.LLˣ) : B.LL))
    (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ)
    (hξ : ∀ PP ∈ I.Q a, ∀ x, ((ξ PP x : ℂˣ) : ℂ) =
      B.embLL ((Formalism.L2.DIV.resChar (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) PP x : B.LLˣ) : B.LL))
    (hr : B.R.r ≤ (I.rec7 l Z).sp.X'.rank),
    LevIs S (levS _ 1 (Lev.datY (I.rec7 l Z).sp.X'.rank B.R.r B.R.t B.R.m hr (B.primes X).vGs (I.Q a) P' cg ξ Lev.Frm.B))
      (Lev.levChi _ 1 (Lev.datY (I.rec7 l Z).sp.X'.rank B.R.r B.R.t B.R.m hr (B.primes X).vGs (I.Q a) P' cg ξ Lev.Frm.B)) := by
  intro B X I hOk hPins l Z a ha bad S y lat st hO hK P' hH hchi cg hcg ξ hξ hr
  obtain ⟨-, gP, -, -⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z
  have gX : (I.rec7 l Z).sp.X'.gram = 1 := by
    have := congrArg (Matrix.reindex (finCongr (rankP (I.rec7 l Z))) (finCongr (rankP (I.rec7 l Z)))).symm gP
    rw [gramP, Equiv.symm_apply_apply] at this
    rw [this, Matrix.reindex_symm, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  have hLb : S.Lb = Formalism.L2.Col.stdLat B.fields.E (B.R.N B.R.m - 1) := by
    ext x
    refine (hK.lb x).trans (Iff.trans ?_ (Formalism.L2.Col.mem_stdLat x).symm)
    exact forall_congr' fun j => ⟨fun ⟨r, h, _⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm, fun _ => one_dvd _⟩⟩
  obtain ⟨c⟩ := cl_nonempty I a
  have hR := GlobalTheory.T.levelReading_rationalAtTwist_extends_integralUnitary (Q := I.Q a) B.sp.cm gP S (rowTyG I.Ch I.Ps) B.embLL _ _ (GlobalTheory.Mem.Col2.ChEx.q_conj I hOk a)
    (q_inj I hOk a) hO (GlobalTheory.T.twistedTuple_reading_level_character I hOk hPins l Z a S hK c ξ hξ)
  have key := @GlobalTheory.T.twistPrimeLevel_iff_reductionLevel_conjugateCharacter B.fields.F B.fields.E B.fields.K _ _ _ _ (GlobalTheory.Mem.Col2.starE B) _ _ B.sp.cm (B.R.N B.R.m - 1) _
    (rankP (I.rec7 l Z)) _ _ _ gX gP _ _ _ S hLb B.R.r B.R.t B.R.m (Formalism.L2.Col.r_le_X' B.R) hr
    (Formalism.L2.Col.t_pos B.R) (Formalism.L2.Col.rank_X'_eq B.R) (B.primes X).vGs (I.Q a) I.Ps (Formalism.L2.Col.chiAt I.Ch) B.embLL ξ hR
    P' cg hH hchi hcg
  show (∀ h, h ∈ levS _ 1 _ ↔ _) ∧ _
  refine ⟨fun h => ⟨fun hh => ?_, fun ⟨κ, h1, h2⟩ => ⟨h1, (key _ κ.1 h2).1.2 κ.2⟩⟩, fun h κ hκ => (key _ κ.1 hκ.2).2 κ.2⟩
  obtain ⟨y, hy⟩ := exists_copy (rankP (I.rec7 l Z)) (Lev.finE (I.rec7 l Z).sp.X' h)
  exact ⟨⟨y, (key _ y hy).1.1 hh.2⟩, hh.1, hy⟩

end GlobalTheory.SeeSaw.TwLev
