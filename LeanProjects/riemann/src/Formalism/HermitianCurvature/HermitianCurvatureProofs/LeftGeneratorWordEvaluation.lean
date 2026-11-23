import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace FExpL

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Rep (m : ℕ∞) (O : Set (B.Mat k r)) (φ : B.Mat k r → E) : Prop :=
  ∃ F : B.Mat k r → E, ContDiffOn ℝ (m : WithTop ℕ∞) F O ∧ ∀ x ∈ O, x ∈ B.GV k r → φ x = F x

theorem rep_mono {m m' : ℕ∞} (hmm : m ≤ m') {O : Set (B.Mat k r)} {φ : B.Mat k r → E} (h : Rep m' O φ) :
    Rep m O φ := by
  obtain ⟨F, hF, he⟩ := h
  exact ⟨F, hF.of_le (by exact_mod_cast hmm), he⟩

theorem curveL_hasDerivAt (x X : B.Mat k r) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * x) (X * x) 0 := by
  have h := (mulRightRealCLM x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_mul_exp_smul_zero (1 : B.Mat k r) X)
  have e2 : (mulRightRealCLM x) ((1 : B.Mat k r) * X) = X * x := by
    show (1 * X) * x = X * x
    rw [Matrix.one_mul]
  refine (h.congr_deriv e2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show NormedSpace.exp ((t : ℂ) • X) * x = (1 * NormedSpace.exp ((t : ℂ) • X)) * x
  rw [Matrix.one_mul]

theorem curveL_zero (x X : B.Mat k r) : NormedSpace.exp (((0 : ℝ) : ℂ) • X) * x = x := by
  simp [NormedSpace.exp_zero]

theorem curveL_mem {x X : B.Mat k r} (hxG : x ∈ B.GV k r) (hX : B.inLie k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) * x ∈ B.GV k r := WeylGroupFacts.uh_mul (Formalism.FourierDecayAlt.P.B5.exp_mem hX t) hxG

theorem hasDerivAt_of_extL {φ F : B.Mat k r → E} {U : Set (B.Mat k r)} (hU : IsOpen U) {g X : B.Mat k r}
    (hg : g ∈ U) (hgG : g ∈ B.GV k r) (hX : B.inLie k r X) (hF : DifferentiableAt ℝ F g)
    (he : ∀ x ∈ U, x ∈ B.GV k r → φ x = F x) :
    HasDerivAt (fun t : ℝ => φ (NormedSpace.exp ((t : ℂ) • X) * g)) (fderiv ℝ F g (X * g)) 0 := by
  have hγ := curveL_hasDerivAt g X
  have hγ0 := curveL_zero g X
  have hcomp : HasDerivAt (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g)) (fderiv ℝ F g (X * g)) 0 :=
    hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, NormedSpace.exp ((t : ℂ) • X) * g ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
  filter_upwards [hmem] with t ht
  exact he _ ht (curveL_mem hgG hX t)

theorem rep_LdV {m : ℕ∞} {O : Set (B.Mat k r)} (hO : IsOpen O) {φ : B.Mat k r → E} {X : B.Mat k r}
    (hX : B.inLie k r X) (h : Rep (m + 1) O φ) : Rep m O (Q.LdV X φ) := by
  obtain ⟨F, hF, he⟩ := h
  refine ⟨fun x => fderiv ℝ F x (X * x), ?_, ?_⟩
  · have h1 := hF.fderiv_of_isOpen (m := (m : WithTop ℕ∞)) hO (by push_cast; exact le_rfl)
    exact h1.clm_apply (Formalism.FourierDecayAlt.P.B5.mulLc X).contDiff.contDiffOn
  · intro x hx hxG
    have hd : DifferentiableAt ℝ F x :=
      (hF.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx)
    exact (hasDerivAt_of_extL hO hx hxG hX hd he).deriv

theorem rep_Rw {O : Set (B.Mat k r)} (hO : IsOpen O) {f : B.Mat k r → E} {N : ℕ} (h : Rep (N : ℕ∞) O f)
    (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) (m : ℕ) (hle : m + w.length ≤ N) :
    Rep (m : ℕ∞) O (w.foldr Q.LdV f) := by
  induction w generalizing m with
  | nil => exact rep_mono (by exact_mod_cast (by simpa using hle)) h
  | cons X w ih =>
    have e : (X :: w).foldr Q.LdV f = Q.LdV X (w.foldr Q.LdV f) := rfl
    rw [e]
    apply rep_LdV hO (hw X (by simp))
    have := ih (fun Y hY => hw Y (by simp [hY])) (m + 1) (by simp at hle; omega)
    exact_mod_cast this

theorem rep_hasDerivAt {O : Set (B.Mat k r)} (hO : IsOpen O) {φ : B.Mat k r → E} {x X : B.Mat k r}
    (hx : x ∈ O) (hxG : x ∈ B.GV k r) (hX : B.inLie k r X) (h : Rep ((1 : ℕ) : ℕ∞) O φ) :
    HasDerivAt (fun t : ℝ => φ (NormedSpace.exp ((t : ℂ) • X) * x)) (Q.LdV X φ x) 0 := by
  obtain ⟨F, hF, he⟩ := h
  have hd : DifferentiableAt ℝ F x := (hF.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx)
  exact (hasDerivAt_of_extL hO hx hxG hX hd he).differentiableAt.hasDerivAt

theorem ldV_congr {O : Set (B.Mat k r)} (hO : IsOpen O) {φ ψ : B.Mat k r → E}
    (he : ∀ y ∈ O, y ∈ B.GV k r → φ y = ψ y) {x X : B.Mat k r} (hx : x ∈ O) (hxG : x ∈ B.GV k r)
    (hX : B.inLie k r X) : Q.LdV X φ x = Q.LdV X ψ x := by
  show deriv (fun t : ℝ => φ (NormedSpace.exp ((t : ℂ) • X) * x)) 0 =
    deriv (fun t : ℝ => ψ (NormedSpace.exp ((t : ℂ) • X) * x)) 0
  apply Filter.EventuallyEq.deriv_eq
  have hγ := curveL_hasDerivAt x X
  have hγ0 := curveL_zero x X
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, NormedSpace.exp ((t : ℂ) • X) * x ∈ O :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hO.mem_nhds hx)
  filter_upwards [hmem] with t ht
  exact he _ ht (curveL_mem hxG hX t)

theorem wsEvalL_append (a b : List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ) (f : B.Mat k r → E)
    (x : B.Mat k r) : wsEvalL (a ++ b) u f x = wsEvalL a u f x + wsEvalL b u f x := by
  simp [wsEvalL, List.map_append, List.sum_append]

theorem wsEvalL_flatMap {α : Type} (F : α → List (Polynomial ℂ × List (B.Mat k r))) (u : ℂ)
    (f : B.Mat k r → E) (x : B.Mat k r) :
    ∀ L : List α, wsEvalL (L.flatMap F) u f x = (L.map fun a => wsEvalL (F a) u f x).sum
  | [] => by simp [wsEvalL]
  | a :: L => by
    rw [List.flatMap_cons, wsEvalL_append, wsEvalL_flatMap F u f x L, List.map_cons, List.sum_cons]

theorem wsEvalL_map_mul (p : Polynomial ℂ) (φ : List (B.Mat k r) → List (B.Mat k r)) (u : ℂ)
    (f : B.Mat k r → E) (x : B.Mat k r) :
    ∀ ws : List (Polynomial ℂ × List (B.Mat k r)),
      wsEvalL (ws.map fun t => (p * t.1, φ t.2)) u f x = p.eval u • wsEvalL (ws.map fun t => (t.1, φ t.2)) u f x
  | [] => by simp [wsEvalL]
  | t :: ws => by
    have ih := wsEvalL_map_mul p φ u f x ws
    simp only [wsEvalL, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, smul_add, Polynomial.eval_mul, mul_smul]

theorem fexp_words : ∀ (gens : List (GenW k r)), (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) →
    ∀ t ∈ fexp gens, t.2.length ≤ gens.length ∧ ∀ X ∈ t.2, B.inLie k r X
  | [], _, t, ht => by
    simp only [fexp, List.mem_singleton] at ht
    subst ht
    simp
  | gn :: gs, hL, t, ht => by
    have hL' : ∀ g ∈ gs, ∀ dX ∈ g.2, B.inLie k r dX.2 := fun g hg => hL g (List.mem_cons_of_mem _ hg)
    have ih := fexp_words gs hL'
    simp only [fexp, List.mem_append, List.mem_map, List.mem_flatMap] at ht
    rcases ht with ⟨s, hs, rfl⟩ | ⟨dX, hdX, s, hs, rfl⟩
    · have := (ih s hs).1
      refine ⟨?_, (ih s hs).2⟩
      show s.2.length ≤ (gn :: gs).length
      simp only [List.length_cons]; omega
    · have := (ih s hs).1
      refine ⟨?_, ?_⟩
      · show (dX.2 :: s.2).length ≤ (gn :: gs).length
        simp only [List.length_cons]; omega
      · intro X hX
        rcases List.mem_cons.1 hX with rfl | hX
        · exact hL gn (by simp) dX hdX
        · exact (ih s hs).2 X hX

theorem ws_hasDerivAt {O : Set (B.Mat k r)} (hO : IsOpen O) {x X : B.Mat k r} (hx : x ∈ O)
    (hxG : x ∈ B.GV k r) (hX : B.inLie k r X) (u : ℂ) (f : B.Mat k r → E) :
    ∀ ws : List (Polynomial ℂ × List (B.Mat k r)), (∀ t ∈ ws, Rep ((1 : ℕ) : ℕ∞) O (t.2.foldr Q.LdV f)) →
      HasDerivAt (fun s : ℝ => wsEvalL ws u f (NormedSpace.exp ((s : ℂ) • X) * x))
        (wsEvalL (ws.map fun t => (t.1, X :: t.2)) u f x) 0
  | [], _ => by
    have e : ∀ y, wsEvalL ([] : List (Polynomial ℂ × List (B.Mat k r))) u f y = (0 : E) := fun y => by
      simp [wsEvalL]
    simp only [List.map_nil, e]
    exact hasDerivAt_const _ _
  | t :: ws, h => by
    have h1 := (rep_hasDerivAt hO hx hxG hX (h t (by simp))).const_smul (t.1.eval u)
    have h2 := ws_hasDerivAt hO hx hxG hX u f ws (fun s hs => h s (List.mem_cons_of_mem _ hs))
    have e1 : (fun s : ℝ => wsEvalL (t :: ws) u f (NormedSpace.exp ((s : ℂ) • X) * x)) =
        fun s : ℝ => t.1.eval u • t.2.foldr Q.LdV f (NormedSpace.exp ((s : ℂ) • X) * x) +
          wsEvalL ws u f (NormedSpace.exp ((s : ℂ) • X) * x) := by
      funext s; simp only [wsEvalL, List.map_cons, List.sum_cons]
    have e2 : wsEvalL ((t :: ws).map fun t => (t.1, X :: t.2)) u f x =
        t.1.eval u • Q.LdV X (t.2.foldr Q.LdV f) x + wsEvalL (ws.map fun t => (t.1, X :: t.2)) u f x := by
      simp only [wsEvalL, List.map_cons, List.sum_cons]
      rfl
    rw [e1, e2]
    exact h1.add h2

theorem left_generator_word_evaluation (u : ℂ) : ∀ (gens : List (GenW k r)) (O : Set (B.Mat k r)) (f : B.Mat k r → E), IsOpen O →
    (∀ gn ∈ gens, ∀ dX ∈ gn.2, B.inLie k r dX.2) → Rep (gens.length : ℕ∞) O f → ∀ x ∈ O, x ∈ B.GV k r →
      (gens.map (fun gn => genOpL gn u)).foldr (fun T h => T h) f x = wsEvalL (fexp gens) u f x
  | [], O, f, _, _, _, x, _, _ => by simp [fexp, wsEvalL]
  | gn :: gs, O, f, hO, hL, hf, x, hx, hxG => by
    have hL' : ∀ g ∈ gs, ∀ dX ∈ g.2, B.inLie k r dX.2 := fun g hg => hL g (List.mem_cons_of_mem _ hg)
    have hf' : Rep (gs.length : ℕ∞) O f := rep_mono (by exact_mod_cast (by simp : gs.length ≤ (gn :: gs).length)) hf
    have IH := left_generator_word_evaluation u gs O f hO hL' hf'
    have hW := fexp_words gs hL'
    have hrep : ∀ t ∈ fexp gs, Rep ((1 : ℕ) : ℕ∞) O (t.2.foldr Q.LdV f) := fun t ht =>
      rep_Rw hO hf t.2 (hW t ht).2 1 (by have := (hW t ht).1; simp only [List.length_cons]; omega)
    have hD : ∀ X, B.inLie k r X → Q.LdV X (wsEvalL (fexp gs) u f) x =
        wsEvalL ((fexp gs).map fun t => (t.1, X :: t.2)) u f x := fun X hX =>
      (ws_hasDerivAt hO hx hxG hX u f (fexp gs) hrep).deriv
    have hR : wsEvalL (fexp (gn :: gs)) u f x = gn.1.eval u • wsEvalL (fexp gs) u f x +
        (gn.2.map fun dX => dX.1 • wsEvalL ((fexp gs).map fun t => (t.1, dX.2 :: t.2)) u f x).sum := by
      simp only [fexp]
      rw [wsEvalL_append, wsEvalL_flatMap]
      congr 1
      · have := wsEvalL_map_mul gn.1 id u f x (fexp gs)
        simpa using this
      · congr 1
        apply List.map_congr_left
        intro dX _
        have := wsEvalL_map_mul (Polynomial.C dX.1) (fun w => dX.2 :: w) u f x (fexp gs)
        simpa using this
    set Φ := (gs.map fun gn => genOpL gn u).foldr (fun T h => T h) f with hΦdef
    have hΦ : ∀ X, B.inLie k r X → Q.LdV X Φ x = Q.LdV X (wsEvalL (fexp gs) u f) x := fun X hX =>
      ldV_congr hO (fun y hy hyG => IH y hy hyG) hx hxG hX
    rw [hR]
    change gn.1.eval u • Φ x + (gn.2.map fun dX => dX.1 • Q.LdV dX.2 Φ x).sum = _
    rw [IH x hx hxG]
    congr 2
    apply List.map_congr_left
    intro dX hdX
    have hX := hL gn (by simp) dX hdX
    rw [hΦ dX.2 hX, hD dX.2 hX]

end FExpL

theorem left_exponential_evaluation : FExpEvalL := by
  intro k r E _ _ gens u UU f hL hf g hg hgG
  obtain ⟨U, f', hU, hgU, hf', he⟩ := hf g hg
  exact FExpL.left_generator_word_evaluation u gens U f hU hL ⟨f', hf', he⟩ g hgU hgG

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
