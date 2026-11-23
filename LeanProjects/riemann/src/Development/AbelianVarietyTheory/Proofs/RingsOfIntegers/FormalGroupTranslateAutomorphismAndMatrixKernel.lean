import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpecStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MaximalIdealFormalPointsFormModuleStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalModuleMatrixApplyPointsActionLawsStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.ShiftPf
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
variable {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def Sm1 {n : ℕ} (x : Pt V n d) : Prop := ∀ i, MvPowerSeries.constantCoeff (x i) ∈ maximalIdeal V

def Sm {m n : ℕ} (x : Fin m → Pt V n d) : Prop := ∀ b, Sm1 (x b)

theorem evV_hom {m n : ℕ} {a : Fin m → Pt V n d} (ha : Sm a) :
    ∃ ψ : PS V m d →ₐ[V] PS V n d, (∀ j, ψ (MvPowerSeries.X j) = a j.1 j.2) ∧ ∀ f, evV a f = ψ f := by
  obtain ⟨ψ, hψ, he⟩ := (GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin 0) (fun p => a p.1 p.2)
    (fun p => ha p.1 p.2)).1
  exact ⟨ψ, fun j => hψ j, fun f => he f⟩

theorem evV_X {m n : ℕ} {a : Fin m → Pt V n d} (ha : Sm a) (b : Fin m) (i : Fin d) :
    evV a (MvPowerSeries.X (b, i)) = a b i := by
  obtain ⟨ψ, hψ, he⟩ := evV_hom ha
  rw [he]
  exact hψ (b, i)

theorem evV_pt {m n : ℕ} {a : Fin m → Pt V n d} (ha : Sm a) (b : Fin m) :
    (fun i => evV a (pt V d b i)) = a b := by
  funext i
  exact evV_X ha b i

theorem evV_cpt {m n : ℕ} {a : Fin m → Pt V n d} (ha : Sm a) (α : Fin d → V) :
    (fun i => evV a ((cpt α : Pt V m d) i)) = cpt α := by
  funext i
  obtain ⟨ψ, -, he⟩ := evV_hom ha
  rw [he]
  show ψ (MvPowerSeries.C (α i)) = MvPowerSeries.C (α i)
  rw [MvPowerSeries.c_eq_algebraMap, AlgHom.commutes]
  first
  | rfl
  | simp [MvPowerSeries.algebraMap_apply]

theorem evV_zero {m n : ℕ} {a : Fin m → Pt V n d} (ha : Sm a) : evV a 0 = 0 := by
  obtain ⟨ψ, -, he⟩ := evV_hom ha
  rw [he, map_zero]

theorem evV_comp {m n k : ℕ} {a : Fin m → Pt V n d} (ha : Sm a) {b : Fin n → Pt V k d} (hb : Sm b) (f : PS V m d) :
    evV b (evV a f) = evV (fun j i => evV b (a j i)) f := (GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin k × Fin d) (fun p => a p.1 p.2)
    (fun p => ha p.1 p.2)).2.2.2 (fun p => b p.1 p.2) (fun p => hb p.1 p.2) f

theorem sm_evV {m n : ℕ} {a : Fin m → Pt V n d} (ha : Sm a) {x : Pt V m d} (hx : Sm1 x) :
    Sm1 (fun i => evV a (x i)) := by
  intro i
  exact (GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin 0) (fun p => a p.1 p.2)
    (fun p => ha p.1 p.2)).2.1 (x i) (hx i)

omit [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem sm_pt {n : ℕ} (b : Fin n) : Sm1 (pt V d b) := by
  intro i
  show MvPowerSeries.constantCoeff (MvPowerSeries.X (b, i)) ∈ maximalIdeal V
  rw [MvPowerSeries.constantCoeff_X]
  exact zero_mem _

omit [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem sm_zero {n : ℕ} : Sm1 (0 : Pt V n d) := by
  intro i
  simp

omit [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem sm_cpt {n : ℕ} {α : Fin d → V} (h : Small α) : Sm1 (cpt α : Pt V n d) := by
  intro i
  simpa [cpt] using h i

theorem evV_id {n : ℕ} (f : PS V n d) : evV (fun b => pt V d b) f = f := by
  have h0 : ∀ p : Fin n × Fin d, MvPowerSeries.constantCoeff ((pt V d p.1 : Pt V n d) p.2) = 0 :=
    fun p => MvPowerSeries.constantCoeff_X _
  have e := (GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec V (Fin n × Fin d) (Fin n × Fin d) (Fin 0) (fun p => (pt V d p.1 : Pt V n d) p.2)
    (fun p => sm_pt p.1 p.2)).2.2.1 h0 f
  have hX : (fun p : Fin n × Fin d => (pt V d p.1 : Pt V n d) p.2) = MvPowerSeries.X := funext fun p => rfl
  show evC (fun p : Fin n × Fin d => (pt V d p.1 : Pt V n d) p.2) f = f
  rw [e, hX, MvPowerSeries.subst_self, id_eq]

theorem evV_addV {m n : ℕ} (F : Fin d → PS V 2 d) {a : Fin m → Pt V n d} (ha : Sm a) {x y : Pt V m d}
    (hx : Sm1 x) (hy : Sm1 y) :
    (fun i => evV a (addV F x y i)) = addV F (fun i => evV a (x i)) (fun i => evV a (y i)) := by
  have hxy : Sm ![x, y] := by
    intro b
    fin_cases b
    · exact hx
    · exact hy
  have e : (fun j i => evV a ((![x, y] : Fin 2 → Pt V m d) j i)) =
      ![fun i => evV a (x i), fun i => evV a (y i)] := by
    funext j l
    fin_cases j <;> rfl
  funext i
  show evV a (evV ![x, y] (F i)) = evV ![fun i => evV a (x i), fun i => evV a (y i)] (F i)
  rw [evV_comp hxy ha, e]

theorem sm_addV (B : FB V d O) {n : ℕ} {x y : Pt V n d} (hx : Sm1 x) (hy : Sm1 y) : Sm1 (addV B.G.F x y) := (GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B n x y x hx hy hx).1

theorem sm_matV (B : FB V d O) {n m : ℕ} (p : Matrix (Fin n) (Fin n) O) {x : Fin n → Pt V m d} (hx : Sm x) :
    Sm (matV B p x) := fun b i => (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n m p p x x (fun b i => hx b i) (fun b i => hx b i)).1 b i

theorem evV_matV (B : FB V d O) {n m k : ℕ} (p : Matrix (Fin n) (Fin n) O) {x : Fin n → Pt V m d} (hx : Sm x)
    {a : Fin m → Pt V k d} (ha : Sm a) :
    (fun b i => evV a (matV B p x b i)) = matV B p (fun b i => evV a (x b i)) := by
  have e1 := (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n m p p x x (fun b i => hx b i) (fun b i => hx b i)).2.2.2.2.1
  have hx' : Sm (fun b i => evV a (x b i)) := fun b => sm_evV ha (hx b)
  have e2 := (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n k p p (fun b i => evV a (x b i)) (fun b i => evV a (x b i))
    (fun b i => hx' b i) (fun b i => hx' b i)).2.2.2.2.1
  funext b i
  rw [← e1 b i, evV_comp hx ha, e2 b i]

private lemma eq_zero_of_addV_self_eq (B : FB V d O) {n : ℕ} {z : Pt V n d} (hz : Sm1 z)
    (h : addV B.G.F z z = z) : z = 0 := by
  have Tz := GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B n z z z hz hz hz
  have hw : Sm1 (compV (B.A.act (-1)) z) := (Tz.2.2.2.2.2.2.2 (-1) 0).1
  have T := GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B n z z (compV (B.A.act (-1)) z) hz hz hw
  calc z = addV B.G.F z 0 := T.2.2.2.1.symm
    _ = addV B.G.F z (addV B.G.F z (compV (B.A.act (-1)) z)) := by rw [Tz.2.2.2.2.1]
    _ = addV B.G.F (addV B.G.F z z) (compV (B.A.act (-1)) z) := T.2.2.1.symm
    _ = addV B.G.F z (compV (B.A.act (-1)) z) := by rw [h]
    _ = 0 := Tz.2.2.2.2.1

theorem matV_zero (B : FB V d O) {n m : ℕ} (p : Matrix (Fin n) (Fin n) O) :
    matV B p (0 : Fin n → Pt V m d) = 0 := by
  have h0 : Sm (0 : Fin n → Pt V m d) := fun _ => sm_zero
  have e3 : matV B p (fun b => addV B.G.F ((0 : Fin n → Pt V m d) b) ((0 : Fin n → Pt V m d) b))
      = fun b => addV B.G.F (matV B p 0 b) (matV B p 0 b) :=
    (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n m p p 0 0 (fun b i => h0 b i) (fun b i => h0 b i)).2.2.1
  have hz : (fun b => addV B.G.F ((0 : Fin n → Pt V m d) b) ((0 : Fin n → Pt V m d) b)) = 0 := by
    funext b
    exact (GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B m 0 0 0 sm_zero sm_zero sm_zero).2.2.2.1
  rw [hz] at e3
  funext b
  exact eq_zero_of_addV_self_eq B (sm_matV B p h0 b) (congrFun e3 b).symm

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem eq_cpt (x : Pt V 0 d) : x = cpt fun i => MvPowerSeries.constantCoeff (x i) := by
  funext i
  ext m
  have hm : m = 0 := Subsingleton.elim _ _
  subst hm
  simp only [cpt]
  rw [MvPowerSeries.coeff_zero_C, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem cpt_zero {n : ℕ} : (cpt (0 : Fin d → V) : Pt V n d) = 0 := by
  funext i
  simp [cpt]

theorem addV_cpt (F : Fin d → PS V 2 d) {α β δ : Fin d → V} (hα : Small α) (hβ : Small β)
    (h : (cpt δ : Pt V 0 d) = addV F (cpt α) (cpt β)) (n : ℕ) :
    (cpt δ : Pt V n d) = addV F (cpt α) (cpt β) := by
  let c : Fin 0 → Pt V n d := fun b => b.elim0
  have hc : Sm c := fun b => b.elim0
  rw [← evV_cpt hc δ, h, evV_addV F hc (sm_cpt hα) (sm_cpt hβ), evV_cpt hc α, evV_cpt hc β]

theorem sm_shift (B : FB V d O) {n : ℕ} {α : Fin n → Fin d → V} (hα : ∀ b, Small (α b)) :
    Sm (fun b => addV B.G.F (pt V d b) (cpt (α b)) : Fin n → Pt V n d) := fun b => sm_addV B (sm_pt b) (sm_cpt (hα b))

theorem shift_zero (B : FB V d O) {n : ℕ} (f : PS V n d) : shift B.G.F 0 f = f := by
  have e : (fun b => addV B.G.F (pt V d b) (cpt ((0 : Fin n → Fin d → V) b))) = fun b => pt V d b := by
    funext b
    have h1 : (cpt ((0 : Fin n → Fin d → V) b) : Pt V n d) = 0 := cpt_zero
    rw [h1]
    exact (GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B n (pt V d b) (pt V d b) (pt V d b) (sm_pt b) (sm_pt b) (sm_pt b)).2.2.2.1
  show evV _ f = f
  rw [e]
  exact evV_id f

theorem shift_shift (B : FB V d O) {n : ℕ} {α β δ : Fin n → Fin d → V} (hα : ∀ b, Small (α b)) (hβ : ∀ b, Small (β b))
    (h : ∀ b, (cpt (δ b) : Pt V 0 d) = addV B.G.F (cpt (α b)) (cpt (β b))) (f : PS V n d) :
    shift B.G.F α (shift B.G.F β f) = shift B.G.F δ f := by
  have hA := sm_shift B hα
  have hB := sm_shift B hβ
  have key : (fun j i => evV (fun b => addV B.G.F (pt V d b) (cpt (α b)))
      (addV B.G.F (pt V d j) (cpt (β j)) i)) = fun b => addV B.G.F (pt V d b) (cpt (δ b)) := by
    funext j
    rw [evV_addV B.G.F hA (sm_pt j) (sm_cpt (hβ j)), evV_pt hA j, evV_cpt hA (β j),
      (GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B n (pt V d j) (cpt (α j)) (cpt (β j)) (sm_pt j) (sm_cpt (hα j))
        (sm_cpt (hβ j))).2.2.1,
      ← addV_cpt B.G.F (hα j) (hβ j) (h j) n]
  show evV _ (evV _ f) = evV _ f
  rw [evV_comp hB hA, key]

theorem zero_addV (B : FB V d O) {n : ℕ} {x : Pt V n d} (hx : Sm1 x) : addV B.G.F 0 x = x := by
  have T := GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B n x 0 x hx sm_zero hx
  rw [← T.2.1]
  exact T.2.2.2.1

theorem germSubstZero_formalGroupTranslate_point (B : FB V d O) {n : ℕ} {α : Fin n → Fin d → V} (hα : ∀ b, Small (α b)) :
    (fun b i => evV (0 : Fin n → Pt V 0 d) (addV B.G.F (pt V d b) (cpt (α b)) i)) = fun b => cpt (α b) := by
  have h0 : Sm (0 : Fin n → Pt V 0 d) := fun _ => sm_zero
  funext b
  rw [evV_addV B.G.F h0 (sm_pt b) (sm_cpt (hα b)), evV_pt h0 b, evV_cpt h0 (α b)]
  exact zero_addV B (sm_cpt (hα b))

theorem shift_inj (B : FB V d O) {n : ℕ} {α β : Fin n → Fin d → V} (hα : ∀ b, Small (α b)) (hβ : ∀ b, Small (β b))
    (h : ∀ f, shift B.G.F α f = shift B.G.F β f) : α = β := by
  have hA := sm_shift B hα
  have hB := sm_shift B hβ
  have e : ∀ b, addV B.G.F (pt V d b) (cpt (α b)) = addV B.G.F (pt V d b) (cpt (β b)) := by
    intro b
    funext i
    have := h (MvPowerSeries.X (b, i))
    unfold shift at this
    rwa [evV_X hA, evV_X hB] at this
  have h1 : ∀ b, (cpt (α b) : Pt V 0 d) = cpt (β b) := by
    intro b
    have ea : (fun i => evV (0 : Fin n → Pt V 0 d) (addV B.G.F (pt V d b) (cpt (α b)) i)) =
        (cpt (α b) : Pt V 0 d) := congrFun (germSubstZero_formalGroupTranslate_point B hα) b
    have eb : (fun i => evV (0 : Fin n → Pt V 0 d) (addV B.G.F (pt V d b) (cpt (β b)) i)) =
        (cpt (β b) : Pt V 0 d) := congrFun (germSubstZero_formalGroupTranslate_point B hβ) b
    rw [← ea, ← eb, e b]
  funext b i
  have := congrArg MvPowerSeries.constantCoeff (congrFun (h1 b) i)
  simpa [cpt] using this

theorem shift_equiv (B : FB V d O) {n : ℕ} {α : Fin n → Fin d → V} (hα : ∀ b, Small (α b)) :
    ∃ ψ : PS V n d ≃ₐ[V] PS V n d, ∀ f, shift B.G.F α f = ψ f := by
  have hc : ∀ b, Sm1 (cpt (α b) : Pt V 0 d) := fun b => sm_cpt (hα b)
  have hw : ∀ b, Sm1 (compV (B.A.act (-1)) (cpt (α b) : Pt V 0 d)) := fun b =>
    ((GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B 0 _ _ _ (hc b) (hc b) (hc b)).2.2.2.2.2.2.2 (-1) 0).1
  let β : Fin n → Fin d → V := fun b i =>
    MvPowerSeries.constantCoeff (compV (B.A.act (-1)) (cpt (α b) : Pt V 0 d) i)
  have hβ : ∀ b, Small (β b) := fun b i => hw b i
  have hwβ : ∀ b, (cpt (β b) : Pt V 0 d) = compV (B.A.act (-1)) (cpt (α b)) := fun b => (eq_cpt _).symm
  have h1 : ∀ b, (cpt ((0 : Fin n → Fin d → V) b) : Pt V 0 d) = addV B.G.F (cpt (α b)) (cpt (β b)) := by
    intro b
    rw [hwβ b, (GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B 0 _ _ _ (hc b) (hc b) (hc b)).2.2.2.2.1]
    exact cpt_zero
  have h2 : ∀ b, (cpt ((0 : Fin n → Fin d → V) b) : Pt V 0 d) = addV B.G.F (cpt (β b)) (cpt (α b)) := by
    intro b
    rw [(GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B 0 _ _ _ (sm_cpt (hβ b)) (hc b) (hc b)).2.1]
    exact h1 b
  obtain ⟨ψ, -, hψ⟩ := evV_hom (sm_shift B hα)
  obtain ⟨χ, -, hχ⟩ := evV_hom (sm_shift B hβ)
  refine ⟨AlgEquiv.ofAlgHom ψ χ (AlgHom.ext fun f => ?_) (AlgHom.ext fun f => ?_), fun f => hψ f⟩
  · show ψ (χ f) = f
    rw [← hχ, ← hψ]
    exact (shift_shift B hα hβ h1 f).trans (shift_zero B f)
  · show χ (ψ f) = f
    rw [← hψ, ← hχ]
    exact (shift_shift B hβ hα h2 f).trans (shift_zero B f)

theorem mem_kerM_iff (B : FB V d O) {n : ℕ} (p : Matrix (Fin n) (Fin n) O) {α : Fin n → Fin d → V}
    (hα : ∀ b, Small (α b)) : α ∈ kerM B p ↔ ∀ f, shift B.G.F α (pullM B p f) = pullM B p f := by
  have hA := sm_shift B hα
  have hP : Sm (fun j => (pt V d j : Pt V n d)) := fun j => sm_pt j
  have h0 : Sm (0 : Fin n → Pt V 0 d) := fun _ => sm_zero
  have e5 : ∀ b i, evV (fun b => addV B.G.F (pt V d b) (cpt (α b)))
      (matV B p (fun j => pt V (n := n) d j) b i)
      = matV B p (fun b => addV B.G.F (pt V d b) (cpt (α b))) b i :=
    (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p p _ _ (fun b i => hA b i) (fun b i => hA b i)).2.2.2.2.1
  have hM : ∀ f, shift B.G.F α (pullM B p f) =
      evV (matV B p (fun b => addV B.G.F (pt V d b) (cpt (α b)))) f := by
    intro f
    show evV _ (evV _ f) = _
    rw [evV_comp (sm_matV B p hP) hA]
    exact congrArg (fun a => evV a f) (funext fun b => funext fun i => e5 b i)
  unfold kerM
  rw [Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, hk⟩ f
    let c : Fin 0 → Pt V n d := fun b => b.elim0
    have hc : Sm c := fun b => b.elim0
    have hx : Sm (fun j => (cpt (α j) : Pt V 0 d)) := fun j => sm_cpt (hα j)
    have e := evV_matV B p hx hc
    have eL : (fun b i => evV c (matV B (m := 0) p (fun j => cpt (α j)) b i)) = 0 := by
      rw [hk]
      exact funext fun b => funext fun i => evV_zero hc
    have eR : (fun b i => evV c ((cpt (α b) : Pt V 0 d) i)) = fun j => (cpt (α j) : Pt V n d) :=
      funext fun b => evV_cpt hc (α b)
    rw [eL, eR] at e
    have e3 : matV B p (fun b => addV B.G.F (pt V d b) (cpt (α b)))
        = fun b => addV B.G.F (matV B p (fun j => pt V d j) b) (matV B p (fun j => (cpt (α j) : Pt V n d)) b) :=
      (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p p (fun j => pt V d j) (fun j => cpt (α j)) (fun b i => hP b i)
        (fun b i => sm_cpt (hα b) i)).2.2.1
    rw [hM, e3, ← e]
    show evV _ f = evV _ f
    exact congrArg (fun a => evV a f) (funext fun b =>
      (GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B n _ _ _ (sm_matV B p hP b) (sm_matV B p hP b) (sm_matV B p hP b)).2.2.2.1)
  · intro h
    refine ⟨hα, ?_⟩
    have hMA : matV B p (fun b => addV B.G.F (pt V d b) (cpt (α b))) = matV B p (fun j => (pt V d j : Pt V n d)) := by
      funext b i
      have := h (MvPowerSeries.X (b, i))
      rw [hM] at this
      exact (evV_X (sm_matV B p hA) b i).symm.trans (this.trans (evV_X (sm_matV B p hP) b i))
    have e1 := evV_matV B p hA h0
    have e2 := evV_matV B p hP h0
    have e3 : (fun b i => evV (0 : Fin n → Pt V 0 d) (addV B.G.F (pt V d b) (cpt (α b)) i)) =
        fun j => (cpt (α j) : Pt V 0 d) := germSubstZero_formalGroupTranslate_point B hα
    have e4 : (fun b i => evV (0 : Fin n → Pt V 0 d) ((pt V d b : Pt V n d) i)) = 0 :=
      funext fun b => evV_pt h0 b
    rw [hMA, e2, e4, matV_zero B p, e3] at e1
    exact e1.symm

end GlobalTheory.PlaceInt.ShiftPf

open GlobalTheory.PlaceInt.ShiftPf in

theorem GlobalTheory.PlaceInt.shift_kerM : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n : ℕ) (p : Matrix (Fin n) (Fin n) O), (0 ∈ kerM B p) ∧ (∀ f : PS V n d, shift B.G.F 0 f = f) ∧ ∀ α β : Fin n → Fin d → V, (∀ b, Small (α b)) → (∀ b, Small (β b)) → (∃ ψ : PS V n d ≃ₐ[V] PS V n d, ∀ f, shift B.G.F α f = ψ f) ∧ (α ∈ kerM B p ↔ ∀ f, shift B.G.F α (pullM B p f) = pullM B p f) ∧ ((∀ f, shift B.G.F α f = shift B.G.F β f) → α = β) ∧ ∃ δ : Fin n → Fin d → V, (∀ b, Small (δ b)) ∧ (∀ b, (cpt (δ b) : Pt V 0 d) = addV B.G.F (cpt (α b)) (cpt (β b))) ∧ (∀ f, shift B.G.F α (shift B.G.F β f) = shift B.G.F δ f) ∧ (α ∈ kerM B p → β ∈ kerM B p → δ ∈ kerM B p) := by
  intro V _ _ _ _ _ d O _ _ B n p
  refine ⟨?_, fun f => shift_zero B f, fun α β hα hβ => ?_⟩
  · unfold kerM
    rw [Set.mem_setOf_eq]
    refine ⟨fun b i => by simp, ?_⟩
    have e : (fun j => (cpt ((0 : Fin n → Fin d → V) j) : Pt V 0 d)) = 0 := funext fun j => cpt_zero
    rw [e]
    exact matV_zero B p
  · let δ : Fin n → Fin d → V := fun b i =>
      MvPowerSeries.constantCoeff (addV B.G.F (cpt (α b) : Pt V 0 d) (cpt (β b)) i)
    have hδ : ∀ b, Small (δ b) := fun b i => sm_addV B (sm_cpt (hα b)) (sm_cpt (hβ b)) i
    have hδe : ∀ b, (cpt (δ b) : Pt V 0 d) = addV B.G.F (cpt (α b)) (cpt (β b)) := fun b => (eq_cpt _).symm
    refine ⟨shift_equiv B hα, mem_kerM_iff B p hα, shift_inj B hα hβ, δ, hδ, hδe,
      shift_shift B hα hβ hδe, fun ha hb => ?_⟩
    rw [mem_kerM_iff B p hα] at ha
    rw [mem_kerM_iff B p hβ] at hb
    rw [mem_kerM_iff B p hδ]
    intro f
    rw [← shift_shift B hα hβ hδe, hb, ha]
