import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureOperatorFacts

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.FcConcT

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open GlobalTheory.CompanionTheory.FcCls

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Abstract

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem twice (M : Submodule ℂ H) (Ω : M →ₗ[ℂ] M) (S : H →L[ℂ] H)
    (hS : ∀ x : M, ∃ v : M, (v : H) = S x ∧ (Ω v : H) = S (Ω x)) (x : M) :
    ∃ v : M, (v : H) = S x ∧ (Ω (Ω v) : H) = S (Ω (Ω x)) := by
  obtain ⟨v, hv, hv'⟩ := hS x
  obtain ⟨u, hu, hu'⟩ := hS (Ω x)
  have e : u = Ω v := Subtype.ext (hu.trans hv'.symm)
  exact ⟨v, hv, by rw [← e]; exact hu'⟩

theorem symB (M : Submodule ℂ H) (Ω : M →ₗ[ℂ] M)
    (hsym : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ) (x y : M) :
    ⟪(x : H) + (Ω (Ω x) : H), (y : H)⟫_ℂ = ⟪(x : H), (y : H) + (Ω (Ω y) : H)⟫_ℂ := by
  rw [inner_add_left, inner_add_right, hsym (Ω x) y, hsym x (Ω y)]

theorem coerB (M : Submodule ℂ H) (Ω : M →ₗ[ℂ] M)
    (hsym : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ) (x : M) :
    ‖(x : H)‖ ^ 2 + ‖(Ω x : H)‖ ^ 2 = (⟪(x : H) + (Ω (Ω x) : H), (x : H)⟫_ℂ).re := by
  have e1 : (⟪(x : H), (x : H)⟫_ℂ).re = ‖(x : H)‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (x : H)
  have e2 : (⟪(Ω x : H), (Ω x : H)⟫_ℂ).re = ‖(Ω x : H)‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (Ω x : H)
  rw [inner_add_left, hsym (Ω x) x, Complex.add_re, e1, e2]

theorem inverse_of_dense [CompleteSpace H] (M : Submodule ℂ H) (Ω : M →ₗ[ℂ] M) (D : Submodule ℂ H)
    (hDM : D ≤ M) (hD : Dense (D : Set H))
    (hsym : ∀ x y : M, ⟪(Ω x : H), y⟫_ℂ = ⟪(x : H), Ω y⟫_ℂ)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hTD : ∀ d : D, T ((d : H) + (Ω (Ω ⟨d, hDM d.2⟩) : H)) = d)
    (hTM : ∀ x : M, ∃ v : M, (v : H) = T x ∧ (Ω v : H) = T (Ω x)) :
    (∀ x : M, ∃ v : M, (v : H) = T x ∧ (v : H) + (Ω (Ω v) : H) = x) ∧
      ∀ x : M, T ((x : H) + (Ω (Ω x) : H)) = x := by
  have hTinner : ∀ u v : H, ⟪T u, v⟫_ℂ = ⟪u, T v⟫_ℂ := by
    intro u v
    rw [← ContinuousLinearMap.adjoint_inner_right, hT.adjoint_eq]
  have key : ∀ x : M, T ((x : H) + (Ω (Ω x) : H)) = x := by
    intro x
    set y : M := x + Ω (Ω x) with hy
    obtain ⟨v, hv, -⟩ := hTM y
    have hyH : (y : H) = (x : H) + (Ω (Ω x) : H) := rfl
    set w : M := v - x with hw
    have hwH : (w : H) = T y - x := by simp [hw, hv]
    have horth : ∀ d : D, ⟪(w : H) + (Ω (Ω w) : H), (d : H)⟫_ℂ = 0 := by
      intro d
      have hd := hTD d
      rw [symB M Ω hsym w ⟨d, hDM d.2⟩]
      change ⟪(w : H), (d : H) + (Ω (Ω ⟨d, hDM d.2⟩) : H)⟫_ℂ = 0
      rw [hwH, inner_sub_left, hTinner, hd]
      have := symB M Ω hsym x ⟨d, hDM d.2⟩
      simp only at this
      rw [← this, hyH, sub_self]
    have hz : (w : H) + (Ω (Ω w) : H) = 0 := by
      have hfun : (fun u : H => ⟪(w : H) + (Ω (Ω w) : H), u⟫_ℂ) = fun _ => 0 :=
        Continuous.ext_on hD (by fun_prop) continuous_const (fun u hu => horth ⟨u, hu⟩)
      exact inner_self_eq_zero.1 (congrFun hfun _)
    have hn := coerB M Ω hsym w
    rw [hz, inner_zero_left, Complex.zero_re] at hn
    have hw0 : ‖(w : H)‖ = 0 := by
      have a2 := sq_nonneg ‖(Ω w : H)‖
      have a1 := sq_nonneg ‖(w : H)‖
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (by linarith)
    have hw1 : (w : H) = 0 := norm_eq_zero.1 hw0
    rw [hwH] at hw1
    rw [← hyH]
    exact sub_eq_zero.1 hw1
  refine ⟨fun x => ?_, key⟩
  obtain ⟨v, hv, hv2⟩ := twice M Ω T hTM x
  exact ⟨v, hv, by rw [hv, hv2, ← map_add]; exact key x⟩

end Abstract

section Conc

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

omit [MeasurableSpace (G n)] [BorelSpace (G n)] in
theorem isOpen_GLs' : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_compl_singleton.preimage hc

theorem val_mem_mul {y : Mat n} (hy : y ∈ GLs n) (h : G n) : y * h.val ∈ GLs n := by
  have hm := val_mem_GLs h
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hy hm

theorem sob_memLp {f : Mat n → V} (h : Sob μ f) : MemLp (fun y : G n => f y.val) 2 μ := h.2 []

omit [MeasurableSpace (G n)] [BorelSpace (G n)] in
theorem rd_congr {f f' : Mat n → V} (h : ∀ g ∈ GLs n, f g = f' g) (X : Mat n) :
    ∀ g ∈ GLs n, Rd X f g = Rd X f' g := by
  intro g hg
  have he : f =ᶠ[𝓝 g] f' := by
    filter_upwards [isOpen_GLs'.mem_nhds hg] with y hy using h y hy
  simp only [Rd, he.fderiv_eq]

omit [MeasurableSpace (G n)] [BorelSpace (G n)] in
theorem om_congr (hOm : OmFormula) {f f' : Mat n → V} (hc : ContDiffOn ℝ ∞ f (GLs n))
    (hc' : ContDiffOn ℝ ∞ f' (GLs n)) (h : ∀ g ∈ GLs n, f g = f' g) :
    ∀ g ∈ GLs n, Om f g = Om f' g := by
  intro g hg
  rw [hOm n V f hc g hg, hOm n V f' hc' g hg]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [rd_congr (rd_congr h _) _ g hg, rd_congr (rd_congr h _) _ g hg]

theorem cls_zero' : cls μ (0 : Mat n → V) = 0 := by
  have h0 : MemLp (fun y : G n => (0 : Mat n → V) y.val) 2 μ := MemLp.zero'
  have := cls_add_smul μ (1 : ℂ) h0 h0
  simpa using this

theorem cls_sub' {f f' : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ)
    (hf' : MemLp (fun y : G n => f' y.val) 2 μ) :
    cls μ (fun g => f g - f' g) = cls μ f - cls μ f' := by
  have e : (fun g => f g - f' g) = (-1 : ℂ) • f' + f := by
    ext g; simp [sub_eq_add_neg, add_comm]
  rw [e, cls_add_smul μ (-1) hf' hf]
  simp [sub_eq_add_neg, add_comm]

theorem cls_sum' {ι : Type} (s : Finset ι) (F : ι → Mat n → V)
    (h : ∀ i ∈ s, MemLp (fun y : G n => F i y.val) 2 μ) :
    cls μ (fun g => ∑ i ∈ s, F i g) = ∑ i ∈ s, cls μ (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact cls_zero'
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 : ∀ i ∈ s, MemLp (fun y : G n => F i y.val) 2 μ :=
      fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hs : MemLp (fun y : G n => (fun g => ∑ i ∈ s, F i g) y.val) 2 μ :=
      memLp_finset_sum s h2
    have e : (fun g => ∑ i ∈ insert a s, F i g) = (1 : ℂ) • F a + fun g => ∑ i ∈ s, F i g := by
      ext g; simp [Finset.sum_insert ha]
    rw [e, cls_add_smul μ 1 h1 hs, ih h2, Finset.sum_insert ha, one_smul]

def pw (b : Bool) (a c : Fin n) : List (Bool × Fin n × Fin n) := [(b, a, c), (b, c, a)]

theorem cls_om (hOm : OmFormula) {f : Mat n → V} (hf : Sob μ f) :
    cls μ (Om f) = ∑ a, ∑ c, (cls μ (Rw (pw true a c) f) - cls μ (Rw (pw false a c) f)) := by
  have e : cls μ (Om f) = cls μ (fun g => ∑ a, ∑ c,
      (Rw (pw true a c) f g - Rw (pw false a c) f g)) :=
    cls_congr μ (fun g hg => hOm n V f hf.1 g hg)
  have hs : ∀ a c, MemLp (fun y : G n => Rw (pw true a c) f y.val - Rw (pw false a c) f y.val) 2 μ :=
    fun a c => (hf.2 _).sub (hf.2 _)
  rw [e, cls_sum' Finset.univ (fun a g => ∑ c, (Rw (pw true a c) f g - Rw (pw false a c) f g))
    (fun a _ => memLp_finset_sum _ fun c _ => hs a c)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [cls_sum' Finset.univ (fun c g => Rw (pw true a c) f g - Rw (pw false a c) f g)
    (fun c _ => hs a c)]
  exact Finset.sum_congr rfl fun c _ => cls_sub' (hf.2 _) (hf.2 _)

theorem ibp_pw (hLg : LgFacts) (hU : Unimod) (hR : RCalc) (hOps : SobOps) (hIbp : IbpSob)
    {f f' : Mat n → V} (hf : Sob μ f) (hf' : Sob μ f') (b : Bool) (a c : Fin n) :
    ⟪cls μ (Rw (pw b a c) f), cls μ f'⟫_ℂ = ⟪cls μ f, cls μ (Rw (pw b c a) f')⟫_ℂ := by
  have h1 := hIbp n μ V hLg hU hR (Rw [(b, c, a)] f) f'
    ((hOps n μ V hLg hU hR f hf).2.1 _) hf' (bs (b, a, c))
  have h2 := hIbp n μ V hLg hU hR f (Rw [(b, a, c)] f') hf
    ((hOps n μ V hLg hU hR f' hf').2.1 _) (bs (b, c, a))
  have h1' : ⟪cls μ (Rw (pw b a c) f), cls μ f'⟫_ℂ =
      -⟪cls μ (Rw [(b, c, a)] f), cls μ (Rw [(b, a, c)] f')⟫_ℂ := h1
  have h2' : ⟪cls μ (Rw [(b, c, a)] f), cls μ (Rw [(b, a, c)] f')⟫_ℂ =
      -⟪cls μ f, cls μ (Rw (pw b c a) f')⟫_ℂ := h2
  rw [h1', h2', neg_neg]

theorem sym_cls (hLg : LgFacts) (hU : Unimod) (hR : RCalc) (hOps : SobOps) (hOm : OmFormula)
    (hIbp : IbpSob) {f f' : Mat n → V} (hf : Sob μ f) (hf' : Sob μ f') :
    ⟪cls μ (Om f), cls μ f'⟫_ℂ = ⟪cls μ f, cls μ (Om f')⟫_ℂ := by
  rw [cls_om hOm hf, cls_om hOm hf']
  simp only [sum_inner, inner_sum, inner_sub_left, inner_sub_right,
    ibp_pw hLg hU hR hOps hIbp hf hf']
  exact Finset.sum_comm

theorem sob_zero (hLg : LgFacts) (hR : RCalc) (hCpt : CptSob) : Sob μ (0 : Mat n → V) :=
  (hCpt n μ V hLg hR 0 contDiffOn_const ⟨0, fun _ _ _ => rfl⟩).1

theorem msob_rep (hLg : LgFacts) (hU : Unimod) (hR : RCalc) (hOps : SobOps) (hCpt : CptSob)
    {x : Lp V 2 μ} (hx : x ∈ Msob μ V) : ∃ f, Sob μ f ∧ cls μ f = x := by
  induction hx using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact ⟨0, sob_zero hLg hR hCpt, cls_zero'⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨f', hf', rfl⟩ := hy
    refine ⟨(1 : ℂ) • f + f', ((hOps n μ V hLg hU hR f hf).2.2.2.1 1 f' hf').1, ?_⟩
    rw [cls_add_smul μ 1 (sob_memLp hf) (sob_memLp hf'), one_smul]
  | smul a x _ hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    have h0 := sob_zero (μ := μ) (V := V) (n := n) hLg hR hCpt
    refine ⟨a • f + 0, ((hOps n μ V hLg hU hR f hf).2.2.2.1 a 0 h0).1, ?_⟩
    rw [cls_add_smul μ a (sob_memLp hf) (sob_memLp h0), cls_zero', add_zero]

theorem cls_om_comb (hLg : LgFacts) (hU : Unimod) (hR : RCalc) (hOps : SobOps) (a : ℂ)
    {f f' : Mat n → V} (hf : Sob μ f) (hf' : Sob μ f') :
    cls μ (Om (a • f + f')) = a • cls μ (Om f) + cls μ (Om f') := by
  have e : cls μ (Om (a • f + f')) = cls μ (a • Om f + Om f') :=
    cls_congr μ ((hOps n μ V hLg hU hR f hf).2.2.2.1 a f' hf').2
  rw [e, cls_add_smul μ a (sob_memLp (hOps n μ V hLg hU hR f hf).1)
    (sob_memLp (hOps n μ V hLg hU hR f' hf').1)]

theorem exists_Om (hLg : LgFacts) (hU : Unimod) (hR : RCalc) (hOps : SobOps) (hCpt : CptSob)
    (hOm : OmFormula) :
    ∃ Ω : Msob μ V →ₗ[ℂ] Msob μ V, ∀ (f : Mat n → V) (hf : cls μ f ∈ Msob μ V), Sob μ f →
      (Ω ⟨cls μ f, hf⟩ : Lp V 2 μ) = cls μ (Om f) := by
  have inM : ∀ f : Mat n → V, Sob μ f → cls μ f ∈ Msob μ V :=
    fun f h => Submodule.subset_span ⟨f, h, rfl⟩
  have rep : ∀ x : Msob μ V, ∃ f, Sob μ f ∧ cls μ f = (x : Lp V 2 μ) :=
    fun x => msob_rep hLg hU hR hOps hCpt x.2
  choose r hr hc using rep
  have key : ∀ (x : Msob μ V) (f : Mat n → V), Sob μ f → cls μ f = (x : Lp V 2 μ) →
      cls μ (Om (r x)) = cls μ (Om f) := by
    intro x f hf e
    refine cls_congr μ (om_congr hOm (hr x).1 hf.1 ?_)
    exact cls_unique μ (hr x).1.continuousOn hf.1.continuousOn (sob_memLp (hr x)) (sob_memLp hf)
      ((hc x).trans e.symm)
  have omS : ∀ f : Mat n → V, Sob μ f → Sob μ (Om f) :=
    fun f hf => (hOps n μ V hLg hU hR f hf).1
  have comb : ∀ (a : ℂ) (f f' : Mat n → V), Sob μ f → Sob μ f' → Sob μ (a • f + f') :=
    fun a f f' hf hf' => ((hOps n μ V hLg hU hR f hf).2.2.2.1 a f' hf').1
  have h0 := sob_zero (μ := μ) (V := V) (n := n) hLg hR hCpt
  have hz : cls μ (Om (0 : Mat n → V)) = 0 := by
    have := cls_om_comb hLg hU hR hOps (1 : ℂ) h0 h0
    simpa using this
  refine ⟨{ toFun := fun x => ⟨cls μ (Om (r x)), inM _ (omS _ (hr x))⟩, map_add' := ?_,
            map_smul' := ?_ }, ?_⟩
  · intro x y
    apply Subtype.ext
    change cls μ (Om (r (x + y))) = cls μ (Om (r x)) + cls μ (Om (r y))
    have e : cls μ ((1 : ℂ) • r x + r y) = ((x + y : Msob μ V) : Lp V 2 μ) := by
      rw [cls_add_smul μ 1 (sob_memLp (hr x)) (sob_memLp (hr y)), hc, hc, one_smul]
      rfl
    rw [key (x + y) _ (comb _ _ _ (hr x) (hr y)) e, cls_om_comb hLg hU hR hOps 1 (hr x) (hr y),
      one_smul]
  · intro a x
    apply Subtype.ext
    change cls μ (Om (r (a • x))) = a • cls μ (Om (r x))
    have e : cls μ (a • r x + 0) = ((a • x : Msob μ V) : Lp V 2 μ) := by
      rw [cls_add_smul μ a (sob_memLp (hr x)) (sob_memLp h0), hc, cls_zero', add_zero]
      rfl
    rw [key (a • x) _ (comb _ _ _ (hr x) h0) e, cls_om_comb hLg hU hR hOps a (hr x) h0, hz,
      add_zero]
  · intro f hf hs
    exact key _ f hs rfl

omit [MeasurableSpace (G n)] [BorelSpace (G n)] [InnerProductSpace ℂ V] in
theorem cpt_comb (a : ℂ) [Module ℂ V] {f f' : Mat n → V} (h : Cpt f) (h' : Cpt f') :
    Cpt (a • f + f') := by
  obtain ⟨R, hf⟩ := h
  obtain ⟨R', hf'⟩ := h'
  refine ⟨max R R', fun y hy hl => ?_⟩
  simp [hf y hy (lt_of_le_of_lt (le_max_left _ _) hl),
    hf' y hy (lt_of_le_of_lt (le_max_right _ _) hl)]

theorem exists_Dm (hLg : LgFacts) (hU : Unimod) (hR : RCalc) (hOps : SobOps) (hCpt : CptSob) :
    ∃ D : Submodule ℂ (Lp V 2 μ), ∀ x, x ∈ D ↔
      ∃ f : Mat n → V, ContDiffOn ℝ ∞ f (GLs n) ∧ Cpt f ∧ cls μ f = x := by
  have sob : ∀ f : Mat n → V, ContDiffOn ℝ ∞ f (GLs n) → Cpt f → Sob μ f :=
    fun f hc hp => (hCpt n μ V hLg hR f hc hp).1
  have z : Cpt (0 : Mat n → V) := ⟨0, fun _ _ _ => rfl⟩
  refine ⟨{ carrier := {x | ∃ f : Mat n → V, ContDiffOn ℝ ∞ f (GLs n) ∧ Cpt f ∧ cls μ f = x},
            add_mem' := ?_, zero_mem' := ⟨0, contDiffOn_const, z, cls_zero'⟩, smul_mem' := ?_ },
    fun x => Iff.rfl⟩
  · rintro _ _ ⟨f, hc, hp, rfl⟩ ⟨f', hc', hp', rfl⟩
    have hf := sob f hc hp
    have hf' := sob f' hc' hp'
    refine ⟨(1 : ℂ) • f + f', ((hOps n μ V hLg hU hR f hf).2.2.2.1 1 f' hf').1.1,
      cpt_comb 1 hp hp', ?_⟩
    rw [cls_add_smul μ 1 (sob_memLp hf) (sob_memLp hf'), one_smul]
  · rintro a _ ⟨f, hc, hp, rfl⟩
    have hf := sob f hc hp
    have h0 := sob 0 contDiffOn_const z
    refine ⟨a • f + 0, ((hOps n μ V hLg hU hR f hf).2.2.2.1 a 0 h0).1.1, cpt_comb a hp z, ?_⟩
    rw [cls_add_smul μ a (sob_memLp hf) (sob_memLp h0), cls_zero', add_zero]

theorem cpt_transl (hLg : LgFacts) (h : G n) {f : Mat n → V} (hp : Cpt f) :
    Cpt (fun y => f (y * h.val)) := by
  obtain ⟨R, hf⟩ := hp
  refine ⟨R + lg h.val, fun y hy hl => hf _ (val_mem_mul hy h) ?_⟩
  have hm := val_mem_GLs h
  have hi : (h.val)⁻¹ ∈ GLs n := by
    have := val_mem_GLs h⁻¹
    rwa [Matrix.coe_units_inv] at this
  have h1 := (hLg n).1 _ (val_mem_mul hy h) _ hi
  have h2 := (hLg n).2.1 _ hm
  have e : y * h.val * (h.val)⁻¹ = y := by
    rw [← Matrix.coe_units_inv]
    exact Units.mul_inv_cancel_right y h
  rw [e, h2] at h1
  linarith

theorem sob_transl (hLg : LgFacts) (hU : Unimod) (hR : RCalc) (hOps : SobOps) (h : G n)
    {f : Mat n → V} (hf : Sob μ f) :
    Sob μ (fun y => f (y * h.val)) ∧
      ∀ g ∈ GLs n, Om (fun y => f (y * h.val)) g = Om f (g * h.val) :=
  (hOps n μ V hLg hU hR f hf).2.2.2.2 h (ContinuousLinearMap.id ℂ V)

theorem rR_norm (hU : Unimod) (h : G n) (x : Lp V 2 μ) : ‖rR μ V h x‖ = ‖x‖ := by
  have hmp : MeasurePreserving (fun y : G n => y * h) μ μ := by
    haveI := (hU n μ).1
    exact measurePreserving_mul_right μ h
  unfold rR
  rw [dif_pos hmp]
  exact (Lp.compMeasurePreservingₗᵢ ℂ (fun y : G n => y * h) hmp).norm_map x

end Conc

section Main

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem rR_mul_inv (hLg : LgFacts) (hU : Unimod) (hR : RCalc) (hOps : SobOps) (hCpt : CptSob)
    (hDn : Dense {x : Lp V 2 μ | ∃ f : Mat n → V, ContDiffOn ℝ ∞ f (GLs n) ∧ Cpt f ∧ cls μ f = x})
    (h : G n) (x : Lp V 2 μ) : rR μ V h (rR μ V h⁻¹ x) = x := by
  have hfun : (fun x : Lp V 2 μ => rR μ V h (rR μ V h⁻¹ x)) = fun x => x := by
    refine Continuous.ext_on hDn (by fun_prop) continuous_id ?_
    rintro _ ⟨f, hc, hp, rfl⟩
    have hf : Sob μ f := (hCpt n μ V hLg hR f hc hp).1
    have hf' := (sob_transl hLg hU hR hOps h⁻¹ hf).1
    change rR μ V h (rR μ V h⁻¹ (cls μ f)) = cls μ f
    rw [rR_cls μ hU h⁻¹ (sob_memLp hf), rR_cls μ hU h (sob_memLp hf')]
    exact cls_congr μ fun g _ => congrArg f (Units.mul_inv_cancel_right g h)
  exact congrFun hfun x

end Main

theorem concT : ConcT := by
  intro n _ _ μ _ V _ _ _ hLg hU hR hS hPS hFr hCF hOps hCpt hOm hIbp hDn
  have hDn' := hDn n μ V hLg
  have inM : ∀ f : Mat n → V, Sob μ f → cls μ f ∈ Msob μ V :=
    fun f h => Submodule.subset_span ⟨f, h, rfl⟩
  have sob : ∀ f : Mat n → V, ContDiffOn ℝ ∞ f (GLs n) → Cpt f → Sob μ f :=
    fun f hc hp => (hCpt n μ V hLg hR f hc hp).1
  refine ⟨fun x hx => msob_rep hLg hU hR hOps hCpt hx, ?_⟩
  obtain ⟨Ω, hΩ⟩ := exists_Om (μ := μ) (V := V) hLg hU hR hOps hCpt hOm
  obtain ⟨D, hD⟩ := exists_Dm (μ := μ) (V := V) hLg hU hR hOps hCpt
  have hDM : D ≤ Msob μ V := by
    intro x hx
    obtain ⟨f, hc, hp, rfl⟩ := (hD x).1 hx
    exact inM f (sob f hc hp)
  have hDense : Dense (D : Set (Lp V 2 μ)) := by
    refine hDn'.mono fun x hx => (hD x).2 hx
  have hDenseM : Dense (Msob μ V : Set (Lp V 2 μ)) := hDense.mono hDM
  have rep : ∀ x : Msob μ V, ∃ f, Sob μ f ∧ ∃ hf : cls μ f ∈ Msob μ V, x = ⟨cls μ f, hf⟩ := by
    intro x
    obtain ⟨f, hf, e⟩ := msob_rep hLg hU hR hOps hCpt x.2
    exact ⟨f, hf, inM f hf, Subtype.ext e.symm⟩
  have hsym : ∀ x y : Msob μ V, ⟪(Ω x : Lp V 2 μ), y⟫_ℂ = ⟪(x : Lp V 2 μ), Ω y⟫_ℂ := by
    intro x y
    obtain ⟨f, hf, hm, rfl⟩ := rep x
    obtain ⟨f', hf', hm', rfl⟩ := rep y
    rw [hΩ f hm hf, hΩ f' hm' hf']
    exact sym_cls hLg hU hR hOps hOm hIbp hf hf'

  have hRΩ : ∀ (h : G n) (x : Msob μ V), ∃ v : Msob μ V, (v : Lp V 2 μ) = rR μ V h x ∧
      (Ω v : Lp V 2 μ) = rR μ V h (Ω x) := by
    intro h x
    obtain ⟨f, hf, hm, rfl⟩ := rep x
    obtain ⟨hs, ho⟩ := sob_transl hLg hU hR hOps h hf
    refine ⟨⟨cls μ (fun y => f (y * h.val)), inM _ hs⟩, (rR_cls μ hU h (sob_memLp hf)).symm, ?_⟩
    rw [hΩ _ _ hs, hΩ f hm hf, rR_cls μ hU h (sob_memLp (hOps n μ V hLg hU hR f hf).1)]
    exact cls_congr μ ho
  let A : D →ₗ[ℂ] Lp V 2 μ :=
    (Msob μ V).subtype ∘ₗ (LinearMap.id + Ω ∘ₗ Ω) ∘ₗ Submodule.inclusion hDM
  have hA : ∀ d : D, A d = (d : Lp V 2 μ) + (Ω (Ω ⟨d, hDM d.2⟩) : Lp V 2 μ) := fun d => rfl
  have hAs : ∀ x y : D, ⟪A x, (y : Lp V 2 μ)⟫_ℂ = ⟪(x : Lp V 2 μ), A y⟫_ℂ :=
    fun x y => symB (Msob μ V) Ω hsym ⟨x, hDM x.2⟩ ⟨y, hDM y.2⟩
  have hAc : ∀ x : D, ‖(x : Lp V 2 μ)‖ ^ 2 ≤ (⟪A x, (x : Lp V 2 μ)⟫_ℂ).re := by
    intro x
    have e := coerB (Msob μ V) Ω hsym ⟨x, hDM x.2⟩
    have e' : ‖(x : Lp V 2 μ)‖ ^ 2 + ‖(Ω ⟨x, hDM x.2⟩ : Lp V 2 μ)‖ ^ 2 =
        (⟪A x, (x : Lp V 2 μ)⟫_ℂ).re := e
    have := sq_nonneg ‖(Ω ⟨x, hDM x.2⟩ : Lp V 2 μ)‖
    linarith
  obtain ⟨T, hTs, -, hTD, hTU⟩ := hFr (Lp V 2 μ) D A hAs hAc

  have hkeep : ∀ (h : G n) (x : D), ∃ y : D, (y : Lp V 2 μ) = rR μ V h x ∧ A y = rR μ V h (A x) := by
    intro h x
    obtain ⟨f, hc, hp, e⟩ := (hD x).1 x.2
    have hf := sob f hc hp
    have hy : rR μ V h x ∈ D := by
      refine (hD _).2 ⟨fun y => f (y * h.val), (sob_transl hLg hU hR hOps h hf).1.1,
        cpt_transl hLg h hp, ?_⟩
      rw [← e, rR_cls μ hU h (sob_memLp hf)]
    obtain ⟨v, hv, hv2⟩ := twice (Msob μ V) Ω (rR μ V h) (hRΩ h) ⟨x, hDM x.2⟩
    refine ⟨⟨rR μ V h x, hy⟩, rfl, ?_⟩
    have hvv : (⟨rR μ V h x, hDM hy⟩ : Msob μ V) = v := Subtype.ext hv.symm
    rw [hA, hA, map_add, ← hv2]
    change rR μ V h x + (Ω (Ω ⟨rR μ V h x, hDM hy⟩) : Lp V 2 μ) = _
    rw [hvv]
  have hcomm : ∀ h : G n, T * rR μ V h = rR μ V h * T := by
    intro h
    have hinv1 : ∀ x, rR μ V h (rR μ V h⁻¹ x) = x := rR_mul_inv hLg hU hR hOps hCpt hDn' h
    have hinv2 : ∀ x, rR μ V h⁻¹ (rR μ V h x) = x := by
      intro x
      have := rR_mul_inv hLg hU hR hOps hCpt hDn' h⁻¹ x
      rwa [inv_inv] at this
    have h1 : ContinuousLinearMap.adjoint (rR μ V h) * rR μ V h = 1 :=
      (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (rR μ V h)).1 (rR_norm hU h)
    have hadj : ContinuousLinearMap.adjoint (rR μ V h) = rR μ V h⁻¹ := by
      ext1 x
      have := congrArg (fun S : Lp V 2 μ →L[ℂ] Lp V 2 μ => S (rR μ V h⁻¹ x)) h1
      simp only [ContinuousLinearMap.mul_apply, hinv1, ContinuousLinearMap.one_apply] at this
      exact this
    have h2 : rR μ V h * ContinuousLinearMap.adjoint (rR μ V h) = 1 := by
      rw [hadj]
      ext1 x
      exact hinv1 x
    refine (hTU (rR μ V h) h1 h2 (hkeep h) ?_).symm
    rw [hadj]
    exact hkeep h⁻¹

  have hTM : ∀ x : Msob μ V, ∃ v : Msob μ V, (v : Lp V 2 μ) = T x ∧ (Ω v : Lp V 2 μ) = T (Ω x) := by
    intro x
    obtain ⟨f, hf, hm, rfl⟩ := rep x
    obtain ⟨f', hf', e, ew⟩ := hPS n μ V T hLg hU hR hS hcomm f hf
    refine ⟨⟨cls μ f', inM f' hf'⟩, e, ?_⟩
    rw [hΩ f' _ hf', hΩ f hm hf, cls_om hOm hf', cls_om hOm hf, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_sub, ew, ew]
  obtain ⟨h1, h2⟩ := inverse_of_dense (Msob μ V) Ω D hDM hDense hsym T hTs
    (fun d => hTD d) hTM
  exact ⟨Ω, T, hDenseM, hsym, h1, h2, hΩ⟩

end GlobalTheory.CompanionTheory.FcConcT
