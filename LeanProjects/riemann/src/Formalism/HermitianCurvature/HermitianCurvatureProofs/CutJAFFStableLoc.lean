import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {k r : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem mem_level_zero_of_mem_group {g : B.Mat k r} (hg : g ∈ B.GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => by simp at ha⟩

def LocSm (g₀ : B.Mat k r) (h : B.Mat k r → E') : Prop :=
  ∃ (U : Set (B.Mat k r)) (F : B.Mat k r → E'), IsOpen U ∧ g₀ ∈ U ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧ ∀ x ∈ U, x ∈ B.GV k r → h x = F x

theorem locSm_of_ckOn {UU : Set (B.Mat k r)} {h : B.Mat k r → E'} (hh : B.CkOn ⊤ UU h) {g₀ : B.Mat k r}
    (hg : g₀ ∈ UU) : LocSm g₀ h := hh g₀ hg

theorem locSm_zero (g₀ : B.Mat k r) : LocSm g₀ (fun _ => (0 : E')) :=
  ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem locSm_add {g₀ : B.Mat k r} {h₁ h₂ : B.Mat k r → E'} (h1 : LocSm g₀ h₁) (h2 : LocSm g₀ h₂) :
    LocSm g₀ (fun x => h₁ x + h₂ x) := by
  obtain ⟨U₁, F₁, o₁, m₁, c₁, e₁⟩ := h1
  obtain ⟨U₂, F₂, o₂, m₂, c₂, e₂⟩ := h2
  exact ⟨U₁ ∩ U₂, fun x => F₁ x + F₂ x, o₁.inter o₂, ⟨m₁, m₂⟩,
    (c₁.mono Set.inter_subset_left).add (c₂.mono Set.inter_subset_right),
    fun x hx hxG => by simp only [e₁ x hx.1 hxG, e₂ x hx.2 hxG]⟩

theorem locSm_smul {g₀ : B.Mat k r} {h : B.Mat k r → E'} (c : ℂ) (h1 : LocSm g₀ h) :
    LocSm g₀ (fun x => c • h x) := by
  obtain ⟨U, F, o, m, cd, e⟩ := h1
  exact ⟨U, fun x => c • F x, o, m, cd.const_smul c, fun x hx hxG => by simp only [e x hx hxG]⟩

theorem locSm_clm {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] {g₀ : B.Mat k r}
    {a : B.Mat k r → (E' →L[ℂ] E₂)} {φ : B.Mat k r → E'} (ha : LocSm g₀ a) (hφ : LocSm g₀ φ) :
    LocSm g₀ (fun x => a x (φ x)) := by
  obtain ⟨U₁, F₁, o₁, m₁, c₁, e₁⟩ := ha
  obtain ⟨U₂, F₂, o₂, m₂, c₂, e₂⟩ := hφ
  refine ⟨U₁ ∩ U₂, fun x => F₁ x (F₂ x), o₁.inter o₂, ⟨m₁, m₂⟩, ?_,
    fun x hx hxG => by simp only [e₁ x hx.1 hxG, e₂ x hx.2 hxG]⟩
  have c₁' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (F₁ x).restrictScalars ℝ) (U₁ ∩ U₂) :=
    ((ContinuousLinearMap.restrictScalarsL ℂ E' E₂ ℝ ℝ).contDiff.comp_contDiffOn
      (c₁.mono Set.inter_subset_left))
  exact c₁'.clm_apply (c₂.mono Set.inter_subset_right)

theorem locSm_listSum {ι : Type*} {g₀ : B.Mat k r} (l : List ι) (φ : ι → B.Mat k r → E')
    (h : ∀ i ∈ l, LocSm g₀ (φ i)) : LocSm g₀ (fun x => (l.map fun i => φ i x).sum) := by
  induction l with
  | nil => simpa using locSm_zero (E' := E') g₀
  | cons a l ih =>
    simpa using locSm_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem ckOn_Rw_top {f : B.Mat k r → E'} (hf : B.CkOn ⊤ (B.GV k r) f) (w : List (B.Mat k r))
    (hw : ∀ X ∈ w, B.inLie k r X) : B.CkOn ⊤ (B.GV k r) (B.Rw w f) := by
  induction w with
  | nil => exact hf
  | cons X w ih =>
    have ih' := ih (fun Y hY => hw Y (by simp [hY]))
    show B.CkOn ⊤ (B.GV k r) (RdV X (B.Rw w f))
    exact Formalism.FourierDecayAlt.P.B5.ckOn_RdV (m := ⊤) (hw X (by simp)) (by rw [top_add]; exact ih')

theorem locSm_smoothLev {O : Set (B.Mat k r)} {h : B.Mat k r → E'}
    (hh : ∀ g₀ ∈ B.GV k r, g₀ ∈ O → LocSm g₀ h) : Q.SmoothLev k r 0 O h := by
  intro g₀ hg₀
  obtain ⟨U, F, o, m, c, e⟩ := hh g₀ hg₀.1.1 hg₀.2
  exact ⟨U, F, o, m, c, fun x hx hxG => e x hx hxG.1⟩

end loc

theorem extension_locality_holds : ExtLoc := by
  intro k r E' _ _ O J hO hJ g₀ hg₀ hg₀O
  obtain ⟨U₀, F, hU₀, hgU₀, hF, hFJ⟩ := hJ g₀ ⟨mem_level_zero_of_mem_group hg₀, hg₀O⟩
  have hV : U₀ ∩ O ∈ nhds g₀ := (hU₀.inter hO).mem_nhds ⟨hgU₀, hg₀O⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  let b : ContDiffBump g₀ := ⟨ε / 3, 2 * ε / 3, by positivity, by linarith⟩
  have hts : tsupport (fun x => b x • F x) ⊆ Metric.closedBall g₀ (2 * ε / 3) :=
    (tsupport_smul_subset_left _ _).trans b.tsupport_eq.subset
  have hcb : Metric.closedBall g₀ (2 * ε / 3) ⊆ U₀ ∩ O := fun x hx =>
    hball (Metric.closedBall_subset_ball (by linarith) hx)
  refine ⟨fun x => b x • F x, Metric.ball g₀ (ε / 3), ?_, ?_, fun x hx => (hcb (hts hx)).2,
    Metric.isOpen_ball, Metric.mem_ball_self (by positivity), ?_⟩
  · intro g _
    refine ⟨Set.univ, fun x => b x • F x, isOpen_univ, trivial, ?_, fun _ _ _ => rfl⟩
    apply ContDiff.contDiffOn
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U₀
    · exact ((b.contDiff.contDiffOn).smul hF).contDiffAt (hU₀.mem_nhds hx)
    · have hx' : x ∉ tsupport (fun x => b x • F x) := fun h => hx (hcb (hts h)).1
      exact (contDiffAt_const (c := (0 : E'))).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 hx')
  · exact IsCompact.of_isClosed_subset (isCompact_closedBall g₀ (2 * ε / 3)) (isClosed_tsupport _) hts
  · intro x hx hxG
    have hb : b x = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    have hxU : x ∈ U₀ := (hball (Metric.ball_subset_ball (by linarith) hx)).1
    simp only [hb, one_smul]
    exact (hFJ x hxU (mem_level_zero_of_mem_group hxG)).symm

theorem smooth_operators_holds : SmoothOps := by
  intro k r Wp Wq _ _ _ _ _ D Θ O hO hOP hΘ f hf hs
  have hsupp : closure {g | g ∈ B.GV k r ∧ f g ≠ 0} ⊆ B.GPos D := by
    intro x hx
    have hxG : x ∈ B.GV k r :=
      (Formalism.FourierDecayAlt.P.B5.GV_closed (k := k) (r := r)).closure_subset_iff.2 (fun y hy => hy.1) hx
    have hxT : x ∈ tsupport f := closure_mono (fun y hy => hy.2) hx
    exact hOP x (hs hxT) hxG
  constructor
  · apply locSm_smoothLev
    intro g₀ hg₀ hg₀O
    apply locSm_listSum
    intro T hT
    exact locSm_clm (locSm_of_ckOn (hΘ T hT).1 (hOP g₀ hg₀O hg₀))
      (locSm_of_ckOn (ckOn_Rw_top hf T.word T.word_lie) hg₀)
  · apply locSm_smoothLev
    intro g₀ hg₀ hg₀O
    apply locSm_listSum
    intro T hT
    apply locSm_smul
    have hc : B.CkOn ⊤ (B.GV k r) (fun x => T.coefAdj x (f x)) :=
      Formalism.FourierDecayAlt.P.B5.ckOn_coef (hΘ T hT).2 hf hsupp
    exact locSm_of_ckOn (ckOn_Rw_top hc T.word.reverse
      (fun X hX => T.word_lie X (List.mem_reverse.1 hX))) hg₀

theorem omP_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f) :
    OmP S T v = Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' := by
  ext g
  constructor
  · rintro ⟨hG, hD⟩
    refine ⟨fun l hl => ?_, hG⟩
    rcases Nat.eq_zero_or_pos l.val with h0 | hpos
    · have : l = ⟨0, by omega⟩ := Fin.ext h0
      rw [this]
      rw [show Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g ⟨0, by omega⟩ = 1 by
        unfold Dmin; exact Matrix.det_isEmpty]
      exact one_ne_zero
    · have := hD ⟨l.val - 1, by omega⟩
      have e : (⟨(l.val - 1) + 1, by omega⟩ : Fin (S.G.r + 2)) = l := Fin.ext (by simp; omega)
      simpa [e] using this
  · rintro ⟨hD, hG⟩
    exact ⟨hG, fun a => hD ⟨a.val + 1, by omega⟩ (by have := a.isLt; simp only [Fin.val_mk]; omega)⟩

theorem positive_domain_condition_holds : OmPDom := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v
  refine ⟨?_, fun g hg hgG => ⟨hgG, hg.1⟩⟩
  rw [omP_eq]
  exact Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (T v).base.z_mem (T v).base.z'_mem

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
