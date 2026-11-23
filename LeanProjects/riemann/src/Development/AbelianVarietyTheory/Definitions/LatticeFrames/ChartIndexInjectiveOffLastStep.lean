import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotTopPtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfDecoratedLatticeUnique

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm.TwTest
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type}
  {A : TwDat I l Z u a Ch}

theorem cosetIn_eq_empty {j : ℕ} (h : j + 1 ≠ B.R.m) (p : PtAt B.R I.sel (I.tup a) (I.cst a) u j) : cosetIn p = fun _ => ∅ := by
  have h1 : p.1.2 = ∅ := by
    have := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) h] at this
    exact this
  funext P
  ext z
  simp [cosetIn, h1]

theorem chartIndex_injective_offLastStep (hA : A.Is) {j : ℕ} (hj : j ≤ B.R.m) (h : j + 1 ≠ B.R.m) : Function.Injective (A.b0 j) := fun α β e =>
  hA.chart_ext j hj α β e (by rw [cosetIn_eq_empty h, cosetIn_eq_empty h])

theorem subsingleton_top (hA : A.Is) : Subsingleton (Ch B.R.m) :=
  ⟨fun α β => chartIndex_injective_offLastStep hA le_rfl (by omega) (by rw [Idx.eq_top (A.b0 _ α) le_rfl, Idx.eq_top (A.b0 _ β) le_rfl])⟩

theorem finite_charts (hA : A.Is) {j : ℕ} (hj : j ≤ B.R.m) : Finite (Ch j) :=
  letI := (I.chain l u a).clsFin j
  haveI : Finite (I.stp u a j).Cl := (inferInstance : Finite ((I.chain l u a).cls j))
  Finite.of_surjective _ (hA.chOf_onto j hj)

theorem kb_top_ne_one (hI : I.Ok) (hA : A.Is) [NeZero (B.R.N B.R.m - 1)] (P : I.Q a)
    (hpi : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 1) (β : Ch B.R.m) : A.kb B.R.m β ≠ 1 := fun h =>
  TopPtModel.not_topPt_one I l Z hI P hpi (h ▸ hA.top β)

theorem bad_finite (hA : A.Is) (hG : (Formalism.L2.Forms.badG (I.rec7 l Z)).Finite) {j : ℕ} (hj : j ≤ B.R.m) : (A.bad j).Finite := by
  refine (hG.union ((I.Q a).finite_toSet.image fun P => P.under (𝓞 B.host.F))).subset fun v hv => ?_
  rcases hA.bad_le j hj v hv with h | ⟨P, hP, e⟩
  exacts [Or.inl h, Or.inr ⟨P, hP, e⟩]

theorem mem_Q_of_underQ (hI : I.Ok) {a' : I.ι} {P : HeightOneSpectrum (𝓞 B.fields.E)} (hP : P ∈ I.Q a')
    (h : I.UnderQ a (P.under (𝓞 B.host.F))) : P ∈ I.Q a := by
  have key : ∀ (b : I.ι), ∀ w ∈ I.Q b, I.sel (w.under (𝓞 B.fields.F)) = w := fun b w hw => by
    unfold ColIn.Q Formalism.L2.Col.QE at hw
    split_ifs at hw with hf
    · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hw
      congr 1
      exact HeightOneSpectrum.ext (hI.sel_ok v)
    · exact absurd hw (Finset.notMem_empty _)
  obtain ⟨P', hP', e⟩ := h
  have e2 : P' = P := by
    rw [← key a P' hP', ← key a' P hP]
    exact congrArg I.sel e
  exact e2 ▸ hP'

set_option maxHeartbeats 800000 in

theorem exists_top_base (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    ∃ (k : TC.GA B (B.R.N B.R.m)) (p : PtAt B.R I.sel (I.tup a) (I.cst a) u B.R.m), I.TopPt l Z u a k ∧
      TC.PtOf k (extTo I.SQ p.1.1) ∧ p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N B.R.m) ∧
      ∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v →
        Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) k = 1 := by
  obtain ⟨k, ⟨p₀, h₀, hN₀⟩, h2, -, h4⟩ := TopPtModel.exists_topPt I l Z hI hP u a
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have h1 := B.R.two_le_m
    have h2 : B.R.m ≤ B.R.m * (B.R.t + 1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold Ranks.N
    omega⟩
  have hb := TopPtModel.topPt_base I l Z h4
  obtain ⟨p, hp⟩ := exists_ptAt I.sel (I.tup a) (I.cst a) (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u (Formalism.L2.Col.DecoF.base _ _ _ _ _))
  rw [← hp] at hb
  have hN : p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N B.R.m) := by
    rw [← hN₀]
    ext v
    exact (PtUniq.mem_iff_hatL (F := B.host.F) p.1.1.deco.2.lat v).trans (((hb.lat _).trans (h₀.lat _).symm).trans
      (PtUniq.mem_iff_hatL (F := B.host.F) p₀.deco.2.lat v).symm)
  refine ⟨k, p, h4, ⟨hb.uni, hb.lat, hb.f, hb.be, fun P i j => ?_⟩, hN, h2⟩
  obtain ⟨a', -, ha'⟩ := Finset.mem_biUnion.1 P.2
  have hq := (TwistPrimes.twist_primes_away I hI).2 u a' P.1 ha'
  by_cases hQ : P.1 ∈ I.Q a
  · rw [extTo_fr, ptFr_of_mem _ hq.1.2.1 hQ]
    exact hb.fr ⟨P.1, hQ⟩ i j
  · have e1 := TopPtModel.adAt_of_prV P.1 (h2 _ hq.2.2 fun h => hQ (mem_Q_of_underQ hI ha' h))
    have e2 : (extTo I.SQ p.1.1).fr P = 1 := by
      rw [extTo_fr]
      unfold ptFr GlobalTheory.Mem.Col2.latFr
      rw [dif_neg hq.1.2.1, dif_neg hQ, hN]
      exact if_pos rfl
    rw [e2]
    refine (congrFun (congrFun e1 i) j).trans ?_
    show _ = algebraMap _ _ ((Pi.single j 1 : Fin _ → B.host.E) i)
    rw [Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp

section Pin
variable {ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ} {θ : InfFam (I.rec7 l Z)}
    {x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)} {vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ} {c₀ : ℕ → ℂ}
    {kom kom' : ∀ j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))}
    {dd dd' : ∀ j, Ch j → Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ}
    {w w' : ∀ j, Ch j → Ch (j + 1) → ℂ} {Ram Ram' : ∀ j, Set (ColT I l u a j)}
    {rd rd' : ∀ j, Ch j → ColT I l u a j → (I.chain l u a).Y j → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ} {cK : ℕ → ℂ}

theorem w_unique (h : PinColN A ψ θ x vac c₀ kom dd w Ram rd cK) (h' : PinColT A ψ θ x vac c₀ kom' dd' w' Ram' rd' cK)
    (j : ℕ) (hj : j < B.R.m) (α : Ch j) (γ : Ch (j + 1)) : w j α γ = w' j α γ := by
  obtain ⟨-, h1, h2⟩ := h.w_ne j hj α γ
  have e := (h.cst j hj α γ).symm.trans (h'.cst j hj α γ)
  have h3 : (volLev (x j).vol (A.U j α) : ℂ) ≠ 0 := by exact_mod_cast h1
  exact mul_left_cancel₀ h3 (mul_right_cancel₀ h2 (mul_right_cancel₀ (Circle.coe_ne_zero _)
    (mul_right_cancel₀ (inv_ne_zero (Circle.coe_ne_zero _)) e)))

theorem norm_cK (h : PinColT A ψ θ x vac c₀ kom dd w Ram rd cK) (j : ℕ) (hj : j < B.R.m) (α : Ch j) (γ : Ch (j + 1)) :
    ‖cK j‖ = |volLev (x j).vol (A.U j α)| * ‖w j α γ‖ * ‖c₀ j‖ := by
  rw [h.cst j hj α γ]
  simp [Circle.norm_coe]

end Pin

end GlobalTheory.AdForm.TwTest
