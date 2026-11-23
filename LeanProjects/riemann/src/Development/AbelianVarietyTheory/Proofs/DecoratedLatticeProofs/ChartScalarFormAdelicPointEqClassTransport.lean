import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorsOnCharts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalAdelicPointOfUnitaryBaseSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicUnitaryLiftOfChartBasePoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.UG

namespace GlobalTheory.AdForm.RdTrans

theorem finM_inf' {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GinfC V) : finM V hn k = 1 := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.finM_inf V k hk

end GlobalTheory.AdForm.RdTrans

namespace GlobalTheory.AdForm.RdTrans

theorem infM_fin'' {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GfC V)
    (τ : D.what₂.Tau) : infM θ V hn k τ = 1 := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ

end GlobalTheory.AdForm.RdTrans

namespace GlobalTheory.AdForm.RdTrans

theorem atInf_mul_inv {E : Type} [Field E] {n : ℕ} {ι : Type} (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    atInf emb γ.val τ * atInf emb (γ⁻¹).val τ = 1 := by
  unfold atInf
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem eq_of_mul_eq_one {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℂ) (h1 : A * B = 1) (h2 : C * D = 1) (h3 : B = C) :
    A = D := by
  calc A = A * (C * D) := by rw [h2, Matrix.mul_one]
    _ = (A * B) * D := by rw [h3, Matrix.mul_assoc]
    _ = D := by rw [h1, Matrix.one_mul]

end GlobalTheory.AdForm.RdTrans

namespace GlobalTheory.AdForm.RdTrans

set_option maxHeartbeats 1000000 in

theorem exists_level {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {Ch : Type}
    {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (TC.GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → TC.GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → TC.GA B (B.R.N i)}
    (h : I.Reads u a i chOf Lb U chi y st k) (b : (I.stp u a i).β) (d : (I.stp u a i).D b)
    (hco : cosetIn d = cosetIn ((I.stp u a i).rep ((I.stp u a i).cl b d)))
    (w : TC.GA B (B.R.N i)) (hw : TC.PtOf (w * k (chOf ((I.stp u a i).cl b d))) d.1.1) :
    ∃ x : U (chOf ((I.stp u a i).cl b d)), w = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
        ((I.stp u a i).gam b ((I.stp u a i).mv b d)) * y ((I.stp u a i).cl b d) * x.1 ∧
      ((chi _ x : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr b ((I.stp u a i).mv b d) : B.LLˣ) : B.LL) := by
  have hg := (I.stp u a i).mv_smul b d
  generalize (I.stp u a i).mv b d = g at hg ⊢
  have hlev := h.lev ((I.stp u a i).cl b d)
  have hchr := h.chr ((I.stp u a i).cl b d)
  generalize y ((I.stp u a i).cl b d) = y' at hlev hchr ⊢
  obtain ⟨γ, κ⟩ := g
  have hk : (I.stp u a i).act b (1, κ) ((I.stp u a i).rep ((I.stp u a i).cl b d)) =
      (I.stp u a i).act b (γ⁻¹, 1) d := by
    refine Eq.trans ?_ (congrArg ((I.stp u a i).act b (γ⁻¹, 1)) hg)
    refine Eq.trans ?_ (((I.stp u a i).actD b).mul_smul (γ⁻¹, 1) (γ, κ) _)
    rw [Prod.mk_mul_mk, inv_mul_cancel, one_mul]
    rfl
  have hpt : TC.PtOf (y' * (y'⁻¹ * (ratAd B.host.F γ⁻¹ * w)) * k (chOf ((I.stp u a i).cl b d)))
      ((I.stp u a i).act b (1, κ) ((I.stp u a i).rep ((I.stp u a i).cl b d))).1.1 := by
    rw [hk, mul_inv_cancel_left, mul_assoc]
    exact GlobalTheory.T.isPointOf_rational_unitary_adelic_mul _ _ _ _ _ _ _ γ⁻¹ _ _ hw
  have hx := (hlev _ _ hpt).2 ⟨(1, κ), map_one (Formalism.L2.Col.ufGL _ _), rfl, by
    refine Eq.trans ?_ hco
    refine (congrArg (fun q : (I.stp u a i).D b => cosetIn q) hk).trans ?_
    exact GlobalTheory.T.couplingCoset_frames_invariant_rational_unitary _ _ _ _ _ _ _ _ _ (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr _ _ γ⁻¹ rfl rfl⟩
  refine ⟨⟨_, hx⟩, ?_, hchr ⟨_, hx⟩ (1, κ) (map_one (Formalism.L2.Col.ufGL _ _)) hpt⟩
  show w = ratAd B.host.F γ * y' * (y'⁻¹ * (ratAd B.host.F γ⁻¹ * w))
  rw [mul_assoc, mul_inv_cancel_left, ← mul_assoc]
  unfold ratAd
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, one_mul]

end GlobalTheory.AdForm.RdTrans

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.AdForm.rd_trTo : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ b (c : (I.chain l u a).cls j) (d : (I.stp u a j).D c.1)
    (x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (z : TC.GA B (B.R.N j)), x ∈ GfC _ →
    z.1 = finM _ (rankN (I.rec7 l Z) j hj) x → TC.PtOf (z * A.kb j b) (extTo I.SQ d.1.1) →
    A.chOf j ((I.stp u a j).cl c.1 d) = b →
    cosetIn d = cosetIn ((I.stp u a j).rep ((I.stp u a j).cl c.1 d)) → ∀ y,
      A.rd θ j hj b φ y x = (I.stp u a j).trTo B.fields.emb B.embLL c.1 d (φ ((I.stp u a j).cl c.1 d)) y := by
  intro B X I hI hP l Z u a Ch A hA θ hθ j hj φ hφ b c d x z hx hzx hpt hb hco y
  subst hb
  have hd : Disjoint (B.primes X).vGs (I.Q a) := (LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)
  have hw : TC.PtOf (z * A.kb j (A.chOf j ((I.stp u a j).cl c.1 d))) d.1.1 := IsPtOf.of_extTo (I.Q_subset_SQ a) hd hpt
  obtain ⟨x₀, hz, hchi⟩ := GlobalTheory.AdForm.RdTrans.exists_level I l u a j (hA.reads j hj) c.1 d hco z hw
  have hg1 := ((GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z).2.2.2 j hj).1
  unfold Formalism.L2.Forms.gramN at hg1
  have hγ : (I.stp u a j).gam c.1 ((I.stp u a j).mv c.1 d) ∈ UJ (Formalism.L2.Forms.sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
      (Matrix.reindex (finCongr (rankN (I.rec7 l Z) j hj)) (finCongr (rankN (I.rec7 l Z) j hj)) (HSpace.gram ((I.rec7 l Z).sp.X j))) := by
    rw [hg1]
    show cT _ _ * 1 * _ = 1
    rw [Matrix.mul_one]
    exact GlobalTheory.Mem.Col2.StepOk.ufGL_conjTranspose_mul _
  obtain ⟨α, hαQ, hαf, hαi⟩ := GlobalTheory.Core.Mi.exists_GQ_of_unitary θ hθ _ (rankN (I.rec7 l Z) j hj) _ hγ
  obtain ⟨ai, hai, af, haf, hα⟩ := (GlobalTheory.UnitarySplit.real_finite_split _ ((I.rec7 l Z).sp.X j)).1 α
  have hcomm := (GlobalTheory.UnitarySplit.real_finite_split _ ((I.rec7 l Z).sp.X j)).2.1
  have hh := hA.h j hj (A.chOf j ((I.stp u a j).cl c.1 d)) ⟨(I.stp u a j).cl c.1 d, rfl⟩
  let F : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* TC.GA B (B.R.N j) := GlobalTheory.ClassSumLevel.finGLHom _ (rankN (I.rec7 l Z) j hj)
  have hFx : F x = z := Units.ext hzx.symm
  have hFh : F (A.h j (A.chOf j ((I.stp u a j).cl c.1 d)) ⟨(I.stp u a j).cl c.1 d, rfl⟩) =
      ((A.K j hj (A.chOf j ((I.stp u a j).cl c.1 d))).y ⟨(I.stp u a j).cl c.1 d, rfl⟩).1 := Units.ext hh.2
  have hFi : F ai = 1 :=
    Units.ext (GlobalTheory.AdForm.RdTrans.finM_inf' _ _ ai hai)
  have hFa : F af =
      bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stp u a j).gam c.1 ((I.stp u a j).mv c.1 d)) := by
    have e : F α = _ := Units.ext hαf
    rw [hα, map_mul, hFi, one_mul] at e
    exact e
  have hFκ : F
      ((A.h j (A.chOf j ((I.stp u a j).cl c.1 d)) ⟨(I.stp u a j).cl c.1 d, rfl⟩)⁻¹ * af⁻¹ * x) = x₀.1 := by
    rw [map_mul, map_mul, map_inv, map_inv, hFx, hFh, hFa, hz]
    have key : ∀ {G : Type} [Group G] (p q r : G), p⁻¹ * q⁻¹ * (q * p * r) = r := by intros; group
    exact key _ _ _
  have hU : (A.h j (A.chOf j ((I.stp u a j).cl c.1 d)) ⟨(I.stp u a j).cl c.1 d, rfl⟩)⁻¹ * af⁻¹ * x ∈
      A.U j (A.chOf j ((I.stp u a j).cl c.1 d)) :=
    (hA.U j hj _ _).2 ⟨mul_mem (mul_mem (inv_mem hh.1) (inv_mem haf)) hx, x₀, by rw [← hFκ]; rfl⟩
  have hchiA := hA.chi j hj _ ⟨_, hU⟩ x₀ (by rw [← hFκ]; rfl)
  have hdec : x = α * (A.h j (A.chOf j ((I.stp u a j).cl c.1 d)) ⟨(I.stp u a j).cl c.1 d, rfl⟩ * ai⁻¹) *
      ((A.h j (A.chOf j ((I.stp u a j).cl c.1 d)) ⟨(I.stp u a j).cl c.1 d, rfl⟩)⁻¹ * af⁻¹ * x) := by
    have e1 := hcomm _ (inv_mem hai) _ hh.1
    have e2 := hcomm _ (inv_mem hai) _ haf
    rw [hα, ← e1]
    have key : ∀ {G : Type} [Group G] (p q r t : G), q * p⁻¹ = p⁻¹ * q → t = p * q * (p⁻¹ * r) * (r⁻¹ * q⁻¹ * t) := by
      intro G _ p q r t h
      calc t = p * (p⁻¹ * q) * q⁻¹ * t := by group
        _ = p * (q * p⁻¹) * q⁻¹ * t := by rw [h]
        _ = p * q * (p⁻¹ * r) * (r⁻¹ * q⁻¹ * t) := by group
    exact key _ _ _ _ e2.symm
  have hinf : ∀ τ, infM θ _ (rankN (I.rec7 l Z) j hj) ai⁻¹ τ =
      atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (((I.stp u a j).gam c.1 ((I.stp u a j).mv c.1 d))⁻¹ : GL _ _).val τ := by
    intro τ
    have e1 : infM θ _ (rankN (I.rec7 l Z) j hj) α τ = infM θ _ (rankN (I.rec7 l Z) j hj) ai τ := by
      rw [hα, GlobalTheory.AdForm.Model.infM_mul, GlobalTheory.AdForm.RdTrans.infM_fin'' θ _ _ af haf, Matrix.mul_one]
    have e2 : infM θ _ (rankN (I.rec7 l Z) j hj) ai⁻¹ τ * infM θ _ (rankN (I.rec7 l Z) j hj) ai τ = 1 := by
      rw [← GlobalTheory.AdForm.Model.infM_mul, inv_mul_cancel, GlobalTheory.AdForm.Model.infM_one]
    exact GlobalTheory.AdForm.RdTrans.eq_of_mul_eq_one _ _ _ _ e2
      (GlobalTheory.AdForm.RdTrans.atInf_mul_inv (Formalism.L2.Forms.embT (I.rec7 l Z)) ((I.stp u a j).gam c.1 ((I.stp u a j).mv c.1 d)) τ)
      (e1.symm.trans (hαi τ))
  let y' : (I.chain l u a).Y j :=
    ⟨(frMul B.fields.emb B.embLL ((I.stp u a j).gam c.1 ((I.stp u a j).mv c.1 d))⁻¹ ⟨y.1, y.2⟩).1,
      (frMul B.fields.emb B.embLL ((I.stp u a j).gam c.1 ((I.stp u a j).mv c.1 d))⁻¹ ⟨y.1, y.2⟩).2⟩
  have hTr : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) ai⁻¹) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := by
    intro τ
    rw [hinf τ]
    have he : Formalism.L2.Col.embAt B.embLL B.fields.emb τ = Formalism.L2.Forms.embT (I.rec7 l Z) τ := by
      unfold Formalism.L2.Col.embAt Formalism.L2.Forms.embT
      exact FieldsLaws.embLL_comp_emb B τ
    unfold atInf
    show (((I.stp u a j).gam c.1 ((I.stp u a j).mv c.1 d))⁻¹ : GL _ _).val.map (Formalism.L2.Col.embAt B.embLL B.fields.emb τ) * y.1 τ = _
    rw [he]
    rfl
  have key := (GlobalTheory.AdForm.rd_charts I hI hP l Z u a Ch A hA θ hθ j hj φ hφ).2 (A.chOf j ((I.stp u a j).cl c.1 d)) y α hαQ
    ⟨(I.stp u a j).cl c.1 d, rfl⟩ ai⁻¹ (inv_mem hai) ⟨_, hU⟩ y' hTr
  rw [hdec, key, hchiA]
  exact congrArg₂ (· * ·) hchi rfl
