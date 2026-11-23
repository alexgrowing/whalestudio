import Formalism.HermitianCurvature.HermitianCurvatureProofs.ListMapSumApply

open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma mem_steps_of_mem (D : RealPlaceData k r Wp Wq) {nf : ℕ} {e : CT k r nf × List (Mat k r)} {Lf : FS k r nf}
    (he : e ∈ Lf) : ∀ w : List (Mat k r), (e.1, w ++ e.2) ∈ steps D w Lf := by
  intro w
  obtain ⟨s, t, rfl⟩ := List.append_of_mem he
  rw [steps_append, List.mem_append]
  right
  rw [show e :: t = [e] ++ t from rfl, steps_append, List.mem_append]
  exact Or.inl (mem_steps_full D e w)

private lemma rw_congr_on_domL {O : Set (Mat k r)} (hO : IsOpen O) {H H' : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ GV k r, g ∈ O → H g = H' g) :
    ∀ w : List (Mat k r), (∀ X ∈ w, inLie k r X) → ∀ g ∈ GV k r, g ∈ O → Rw w H g = Rw w H' g := by
  intro w
  induction w with
  | nil => intro _ g hg hgO; exact h g hg hgO
  | cons X w ih =>
    intro hw g hg hgO
    have hX : inLie k r X := hw X (by simp)
    have ih' := ih (fun Y hY => hw Y (by simp [hY]))
    show RdV X (Rw w H) g = RdV X (Rw w H') g
    show deriv (fun t : ℝ => Rw w H (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
      deriv (fun t : ℝ => Rw w H' (g * NormedSpace.exp ((t : ℂ) • X))) 0
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [crv_ev (x := (false, X)) hO hgO] with t ht
    have hm := crv_mem (x := (false, X)) hX hg t
    simp only [crv, Bool.false_eq_true, if_false] at ht hm
    exact ih' _ hm ht

lemma opApply_congr (Θ : DiffOp k r Wp Wq) {O : Set (Mat k r)} (hO : IsOpen O) {H H' : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ GV k r, g ∈ O → H g = H' g) {g : Mat k r} (hg : g ∈ GV k r) (hgO : g ∈ O) :
    opApply Θ H g = opApply Θ H' g := by
  unfold opApply
  congr 1
  refine List.map_congr_left (fun T _ => ?_)
  rw [rw_congr_on_domL hO h T.word T.word_lie g hg hgO]

lemma ckOn_rsmul {m : ℕ∞} {b : Mat k r → ℝ} (hb : ContDiff ℝ ∞ b) {Φ : Mat k r → (Wq →L[ℂ] Wp)}
    (hΦ : CkOn m (GV k r) Φ) : CkOn m (GV k r) (fun x => b x • Φ x) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hΦ g₀ hg₀
  refine ⟨U, fun x => b x • f' x, hU, hgU, ?_, fun g hg hgv => by simp only [hfe g hg hgv]⟩
  exact ((hb.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn).smul hf'

private lemma ckOn_GV_add {m : ℕ∞} {f f₂ : Mat k r → (Wq →L[ℂ] Wp)} (hf : CkOn m (GV k r) f)
    (hg : CkOn m (GV k r) f₂) : CkOn m (GV k r) (fun x => f x + f₂ x) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hf g₀ hg₀
  obtain ⟨V, g', hV, hgV, hg', hge⟩ := hg g₀ hg₀
  refine ⟨U ∩ V, fun x => f' x + g' x, hU.inter hV, ⟨hgU, hgV⟩,
    (hf'.mono Set.inter_subset_left).add (hg'.mono Set.inter_subset_right), ?_⟩
  intro x hx hxG
  simp only [hfe x hx.1 hxG, hge x hx.2 hxG]

lemma ckOn_list_sum {m : ℕ∞} {α : Type*} (L : List α) (f : α → Mat k r → (Wq →L[ℂ] Wp))
    (h : ∀ a ∈ L, CkOn m (GV k r) (f a)) : CkOn m (GV k r) (fun g => (L.map fun a => f a g).sum) := by
  induction L with
  | nil =>
    intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => by simp⟩
  | cons a t ih =>
    have := ckOn_GV_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))
    simpa using this

lemma opOrder_le_of (Θ : DiffOp k r Wp Wq) {n : ℕ} (h : ∀ T ∈ Θ, T.word.length ≤ n) : opOrder Θ ≤ n := by
  unfold opOrder
  induction Θ with
  | nil => simp
  | cons T t ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h T (by simp)) (ih fun T' hT' => h T' (by simp [hT']))

lemma one_uw (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mat k r) ∈ UWset k r z := by
  simp only [UWset, Set.mem_setOf_eq, Matrix.one_mulVec, and_self, implies_true, and_true]
  simp [UH]

end Formalism.FourierDecayAlt.P.MinorPolynomials

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.MinorPolynomials

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem compose_differential_operators : C6.ComposeDDPlus := by
  intro k r Wp Wq _ _ _ _ _ _ D nf fib L o₁ κ₁ o₂ κ₂ Θ₁ Θ₂ hfib h₁ h₂
  have hfibC : ∀ j, CkOn ⊤ (GPos D) (fib j) := fun j => (hfib j).1
  obtain ⟨L₁, hB₁, hW₁, hE₁⟩ := toFS D fib L Θ₁ h₁.2.2
  obtain ⟨L₂, hB₂, hW₂, hE₂⟩ := toFS D fib L Θ₂ h₂.2.2
  set Lf := compFS D L₁ L₂ with hLf
  have hBf := compFS_bound D hB₁ hB₂
  have hlieF : ∀ e ∈ Lf, ∀ X ∈ e.2, inLie k r X := fun e he => (hBf e he).1.2.2
  set Θ := Lf.map (mkTerm D fib) with hΘ
  have hopΘ : ∀ F g, opApply Θ F g = shape D fib F Lf g := fun F g => opApply_mk D fib Lf hlieF F g

  have ident : ∀ (m : ℕ), (∀ e₁ ∈ L₁, ∀ e ∈ L₂, e.2.length + e₁.2.length ≤ m) →
      ∀ F : Mat k r → (Wq →L[ℂ] Wp), CkOn (m : ℕ∞) (GV k r) F → ∀ g ∈ C6.domL D L,
        opApply Θ F g = opApply Θ₁ (opApply Θ₂ F) g := by
    intro m hm F hF g hg
    rw [hopΘ, hE₁ _ g hg]
    exact (comp_identity D fib hfibC L (fun e he => (hB₁ e he).1) (fun e he => (hB₂ e he).1) hm hF
      (fun g' hg' => hE₂ F g' hg') hg).symm

  have hN : ∀ e₁ ∈ L₁, ∀ e ∈ L₂, e.2.length + e₁.2.length ≤ opOrder Θ := by
    intro e₁ he₁ e he
    have hmem : (mulCT e₁.1 e.1, e₁.2 ++ e.2) ∈ Lf := by
      simp only [hLf, compFS, List.mem_flatMap, List.mem_map]
      exact ⟨e₁, he₁, (e.1, e₁.2 ++ e.2), mem_steps_of_mem D he e₁.2, rfl⟩
    have h1 := word_le_order Θ (T := mkTerm D fib (mulCT e₁.1 e.1, e₁.2 ++ e.2)) (List.mem_map_of_mem hmem)
    rw [mkTerm_word D fib (hlieF _ hmem)] at h1
    simp only [List.length_append] at h1
    omega
  refine ⟨Θ, ⟨?_, ?_, ?_⟩, ident (o₁ + o₂) (fun e₁ he₁ e he => by
    have := (hB₁ e₁ he₁).2.2; have := (hB₂ e he).2.2; omega)⟩
  ·
    intro T hT
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hT
    have hc := ckOn_cv D fib hfibC (hBf e he).1
    refine ⟨hc, ?_⟩
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hff⟩ := hc g₀ hg₀
    exact ⟨U, fun x => Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjR (f' x), hU, hgU, (Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjR (Wp := Wp) (Wq := Wq)).contDiff.comp_contDiffOn hf',
      fun g hg hG => by
        show Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjH (cv D fib e.1 g) = _
        rw [hff g hg hG]; rfl⟩
  ·
    intro p hp f hf g hg
    by_cases hLe : Lf = []
    · have : Θ = [] := by rw [hΘ, hLe]; rfl
      rw [this]; simp [opApply, rho]
    obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil _ hLe
    simp only [hLf, compFS, List.mem_flatMap, List.mem_map] at he₀
    obtain ⟨e₁₀, he₁₀, e₂₀, he₂₀, -⟩ := he₀
    have hL₂ne : ∃ e ∈ L₂, True := by
      by_contra hc
      push Not at hc
      have : L₂ = [] := List.eq_nil_iff_forall_not_mem.2 fun e he => hc e he
      rw [this] at he₂₀
      have hnil : ∀ w : List (Mat k r), steps D w ([] : FS k r nf) = [] := by
        intro w; induction w with
        | nil => rfl
        | cons X w ih => show step D X (steps D w []) = []; rw [ih]; rfl
      rw [hnil] at he₂₀; simp at he₂₀
    obtain ⟨e₂₁, he₂₁, -⟩ := hL₂ne
    set N := opOrder Θ with hNdef

    have hord₂ : ∀ T ∈ Θ₂, T.word.length + e₁₀.2.length ≤ N := by
      intro T hT; obtain ⟨e, he, hw⟩ := hW₂ T hT; rw [← hw]; exact hN e₁₀ he₁₀ e he
    have hord₁ : ∀ T ∈ Θ₁, ∀ T' ∈ Θ₂, T'.word.length + T.word.length ≤ N := by
      intro T hT T' hT'
      obtain ⟨e, he, hw⟩ := hW₁ T hT; obtain ⟨e', he', hw'⟩ := hW₂ T' hT'
      rw [← hw, ← hw']; exact hN e he e' he'
    have hO2 : opOrder Θ₂ ≤ N := opOrder_le_of Θ₂ fun T hT => by have := hord₂ T hT; omega
    have hfo2 : CkOn (opOrder Θ₂ : ℕ∞) (GV k r) f := sCkOn_mono (by exact_mod_cast hO2) hf

    set s : Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with hsdef
    set s' : Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hs'def
    have hs : s ∈ Sset k r D.z :=
      ⟨_, Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.1, _, (Formalism.QuantumDeterminants.nSubgroup k r).2.2 _ hp.2.1, rfl⟩
    have hs' : s' ∈ Sset k r D.z' :=
      (Formalism.QuantumDeterminants.sGroup k r D.z' D.z'_mem).2.1 _ ⟨1, one_uw D.z', _, hp.2.2.2, by simp⟩ _
        ⟨_, hp.2.2.1, 1, (Formalism.QuantumDeterminants.nSubgroup k r).1, by simp⟩
    have hsG := Sset_sub hs
    have hs'G := Sset_sub hs'
    have hsgs : ∀ y : Mat k r, sgs p y = s * y * s' := by
      intro y; simp [sgs, hsdef, hs'def, Matrix.mul_assoc]
    set x₀ := sgs p g with hx₀
    have hx₀D : x₀ ∈ C6.domL D L := by
      rw [hx₀, hsgs]
      refine ⟨gv_mul (gv_mul hsG hg.1) hs'G, ?_, fun l hl => ?_⟩
      · rw [Formalism.QuantumDeterminants.gInv k r D.z D.z' D.z_mem D.z'_mem s hs s' hs' g]; exact hg.2.1
      · rw [Formalism.QuantumDeterminants.dInv k r D.z D.z' D.z_mem D.z'_mem s hs s' hs' g l]; exact hg.2.2 l hl
    have hρf : CkOn (N : ℕ∞) (GV k r) (rho D p f) := by
      rw [rho_eq_trn]; exact CkOn_trn _ hsG hs'G hf

    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (isOpen_big_cell_set D L) x₀ ((mem_domL D L x₀).1 hx₀D).2
    let bb : ContDiffBump x₀ := ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩
    set φ := opApply Θ₂ f with hφ
    set φt : Mat k r → (Wq →L[ℂ] Wp) := fun x => (bb x : ℝ) • φ x with hφt
    have hbb1 : ∀ y ∈ Metric.ball x₀ (ρ / 4), φt y = φ y := by
      intro y hy
      simp [hφt, bb.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]

    set m₁ := opOrder Θ₁
    have hφt : CkOn (m₁ : ℕ∞) (GV k r) φt := by
      set O := (Metric.closedBall x₀ (ρ / 2))ᶜ with hOdef
      have hO : IsOpen O := Metric.isClosed_closedBall.isOpen_compl
      have hcov : ∀ y ∈ GV k r, y ∈ O ∨ y ∈ C6.domL D L := by
        intro y hy
        by_cases hyc : y ∈ Metric.closedBall x₀ (ρ / 2)
        · right
          exact (mem_domL D L y).2 ⟨hy, hball (Metric.closedBall_subset_ball (by linarith) hyc)⟩
        · exact Or.inl hyc
      have e1 : φt = fun x => (Θ₂.map fun T => ap T.coef (fun y => (bb y : ℝ) • Rw T.word f y) x).sum := by
        funext x
        simp only [hφt, hφ, opApply, ap, List.smul_sum, List.map_map, Function.comp_def]
        congr 1
        apply List.map_congr_left
        intro T _
        exact ((T.coef x).map_smul_of_tower (bb x : ℝ) _).symm
      rw [e1]
      apply ckOn_list_sum
      intro T hT
      have hm : m₁ + T.word.length ≤ N := by
        have := opOrder_le_of Θ₁ (n := N - T.word.length) fun T₁ hT₁ => by
          have := hord₁ T₁ hT₁ T hT; omega
        have := hord₂ T hT
        omega
      have hPr : Pr O (C6.domL D L) (m₁ : ℕ∞) T.coef (fun y => (bb y : ℝ) • Rw T.word f y) :=
        ⟨sCkOn_mono le_top (h₂.1 T hT).1,
          ckOn_rsmul bb.contDiff (PI.UnitaryGroupMassFormula.UsCompose.ck_Rw hf T.word_lie m₁ hm),
          fun y _ hyO => by
            have : bb y = 0 := by
              rw [← Function.notMem_support, bb.support_eq]
              exact fun h => hyO (Metric.ball_subset_closedBall h)
            simp [this]⟩
      exact hPr.ck hO hcov

    have hgV := ((mem_domL D L g).1 hg).2
    rw [ident N hN (rho D p f) hρf g hg]
    have e3 : opApply Θ₁ (opApply Θ₂ (rho D p f)) g = opApply Θ₁ (rho D p φ) g :=
      opApply_congr Θ₁ (isOpen_big_cell_set D L)
        (fun g' hg' hV => h₂.2.1 p hp f hfo2 g' ((mem_domL D L g').2 ⟨hg', hV⟩)) hg.1 hgV
    have hO' : IsOpen ((fun y : Mat k r => s * y * s') ⁻¹' Metric.ball x₀ (ρ / 4)) :=
      Metric.isOpen_ball.preimage ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
    have e8 : opApply Θ₁ (rho D p φ) g = opApply Θ₁ (rho D p φt) g := by
      refine opApply_congr Θ₁ hO' (fun y _ hy => ?_) hg.1 ?_
      · simp only [rho]
        rw [hsgs, ← hbb1 _ hy]
      · show s * g * s' ∈ Metric.ball x₀ (ρ / 4)
        rw [← hsgs]; exact Metric.mem_ball_self (by positivity)
    have e9 := h₁.2.1 p hp φt hφt g hg
    have e10 : opApply Θ₁ φt x₀ = opApply Θ₁ φ x₀ :=
      opApply_congr Θ₁ Metric.isOpen_ball (fun y _ hy => hbb1 y hy) hx₀D.1 (Metric.mem_ball_self (by positivity))
    have e11 : opApply Θ₁ φ x₀ = opApply Θ f x₀ := (ident N hN f hf x₀ hx₀D).symm
    rw [e3, e8, e9]
    simp only [rho]
    rw [← hx₀, e10, e11]
  ·
    intro T hT
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hT
    obtain ⟨hg, hd, ho⟩ := hBf e he
    refine ⟨fun g => eval (PI.UnitaryGroupMassFormula.UsCompose.vars g) e.1.q, e.1.a, e.1.b, e.1.c, e.1.es, ⟨e.1.q, hd, fun g => rfl⟩, ?_, ?_, hg.2.1, ?_⟩
    · intro l hl hl'
      by_contra hc
      rw [not_and_or] at hc
      rcases hg.1 l hc with h | h
      · exact hl h
      · exact hl' h
    · rw [mkTerm_word D fib (hlieF e he)]; exact ho
    · intro g _; rfl

end Formalism.FourierDecayAlt.P
