import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpecStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MaximalIdealFormalPointsFormModuleStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.MatAct

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
  {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def Sm {m : ℕ} (x : Pt V m d) : Prop := ∀ i, MvPowerSeries.constantCoeff (x i) ∈ maximalIdeal V

omit [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
lemma sm_zero {m : ℕ} : Sm (0 : Pt V m d) := by
  intro i
  simp

@[ext] structure SP (B : FB V d O) (m : ℕ) where
  val : Pt V m d
  sm : Sm val

variable (B : FB V d O) {m : ℕ}

instance : Zero (SP B m) := ⟨⟨0, sm_zero⟩⟩
instance : Add (SP B m) :=
  ⟨fun x y => ⟨addV B.G.F x.val y.val, (GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B m x.val y.val x.val x.sm y.sm x.sm).1⟩⟩
instance : SMul O (SP B m) :=
  ⟨fun a x => ⟨compV (B.A.act a) x.val,
    ((GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B m x.val x.val x.val x.sm x.sm x.sm).2.2.2.2.2.2.2 a a).1⟩⟩

lemma val_zero : (0 : SP B m).val = 0 := rfl
lemma val_add (x y : SP B m) : (x + y).val = addV B.G.F x.val y.val := rfl
lemma val_smul (a : O) (x : SP B m) : (a • x).val = compV (B.A.act a) x.val := rfl

lemma add_comm' (x y : SP B m) : x + y = y + x :=
  SP.ext (GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B m x.val y.val x.val x.sm y.sm x.sm).2.1
lemma add_zero' (x : SP B m) : x + 0 = x :=
  SP.ext (GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B m x.val x.val x.val x.sm x.sm x.sm).2.2.2.1

instance : AddCommMonoid (SP B m) where
  add_assoc x y z := SP.ext (GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B m x.val y.val z.val x.sm y.sm z.sm).2.2.1
  add_comm := add_comm' B
  add_zero := add_zero' B
  zero_add x := by rw [add_comm', add_zero']
  nsmul := nsmulRec

lemma zero_smul' (x : SP B m) : (0 : O) • x = 0 :=
  SP.ext (GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B m x.val x.val x.val x.sm x.sm x.sm).2.2.2.2.2.2.1
lemma mul_smul' (a b : O) (x : SP B m) : (a * b) • x = a • b • x :=
  SP.ext ((GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B m x.val x.val x.val x.sm x.sm x.sm).2.2.2.2.2.2.2 a b).2.2.2

instance : Module O (SP B m) where
  one_smul x := SP.ext (GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B m x.val x.val x.val x.sm x.sm x.sm).2.2.2.2.2.1
  mul_smul := mul_smul' B
  smul_zero a := by
    have h := mul_smul' B a 0 (0 : SP B m)
    rw [mul_zero, zero_smul'] at h
    exact h.symm
  smul_add a x y := SP.ext ((GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B m x.val y.val x.val x.sm y.sm x.sm).2.2.2.2.2.2.2 a a).2.1
  add_smul a b x := SP.ext ((GlobalTheory.T.maximal_ideal_formal_points_form_module V d O B m x.val x.val x.val x.sm x.sm x.sm).2.2.2.2.2.2.2 a b).2.2.1
  zero_smul := zero_smul' B

lemma foldr_val (l : List (SP B m)) : (l.map SP.val).foldr (addV B.G.F) 0 = l.sum.val := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.foldr_cons, ih, List.sum_cons]; rfl

lemma matV_val {n : ℕ} (p : Matrix (Fin n) (Fin n) O) (x : Fin n → SP B m) :
    matV B p (fun j => (x j).val) = fun i => (∑ j, p i j • x j).val := by
  funext i
  have h := foldr_val B (List.ofFn fun j => p i j • x j)
  rw [List.map_ofFn, List.sum_ofFn] at h
  exact h

variable {B}

lemma evV_comp {k n : ℕ} (a : Fin k → Pt V n d) (x : Fin n → Pt V m d) (ha : ∀ b, Sm (a b)) (hx : ∀ b, Sm (x b))
    (f : PS V k d) : evV x (evV a f) = evV (fun b i => evV x (a b i)) f :=
  (GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec V (Fin k × Fin d) (Fin n × Fin d) (Fin m × Fin d) (fun p => a p.1 p.2)
    (fun p => ha p.1 p.2)).2.2.2 (fun q => x q.1 q.2) (fun q => hx q.1 q.2) f

lemma evV_alg {n : ℕ} (x : Fin n → Pt V m d) (hx : ∀ b, Sm (x b)) :
    ∃ ψ : PS V n d →ₐ[V] PS V m d, (∀ j, ψ (MvPowerSeries.X j) = x j.1 j.2) ∧ ∀ f, evV x f = ψ f :=
  (GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec V (Fin n × Fin d) (Fin m × Fin d) (Fin m × Fin d) (fun q => x q.1 q.2)
    (fun q => hx q.1 q.2)).1

lemma evV_sm {n : ℕ} (x : Fin n → Pt V m d) (hx : ∀ b, Sm (x b)) (f : PS V n d)
    (hf : MvPowerSeries.constantCoeff f ∈ maximalIdeal V) :
    MvPowerSeries.constantCoeff (evV x f) ∈ maximalIdeal V :=
  (GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec V (Fin n × Fin d) (Fin m × Fin d) (Fin m × Fin d) (fun q => x q.1 q.2)
    (fun q => hx q.1 q.2)).2.1 f hf

lemma evV_const {n : ℕ} (x : Fin n → Pt V m d) (hx : ∀ b i, MvPowerSeries.constantCoeff (x b i) = 0) (f : PS V n d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (evV x f) = 0 := by
  have ha : ∀ q : Fin n × Fin d, MvPowerSeries.constantCoeff (x q.1 q.2) = 0 := fun q => hx q.1 q.2
  have hm : ∀ q : Fin n × Fin d, MvPowerSeries.constantCoeff (x q.1 q.2) ∈ maximalIdeal V := fun q => by
    rw [ha q]; exact Ideal.zero_mem _
  have h := (GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec V (Fin n × Fin d) (Fin m × Fin d) (Fin m × Fin d) (fun q => x q.1 q.2) hm).2.2.1 ha f
  show MvPowerSeries.constantCoeff (evC (fun q : Fin n × Fin d => x q.1 q.2) f) = 0
  rw [h]
  exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) ha hf

variable (B) in

def evL {n : ℕ} (x : Fin n → Pt V m d) (hx : ∀ b, Sm (x b)) : SP B n →ₗ[O] SP B m where
  toFun a := ⟨fun i => evV x (a.val i), fun i => evV_sm x hx _ (a.sm i)⟩
  map_add' a b := by
    refine SP.ext (funext fun i => ?_)
    change evV x (evV ![a.val, b.val] (B.G.F i)) = evV _ (B.G.F i)
    rw [evV_comp _ _ _ hx]
    · congr 1
      funext k
      fin_cases k <;> rfl
    · intro k
      fin_cases k
      · exact a.sm
      · exact b.sm
  map_smul' c a := by
    refine SP.ext (funext fun i => ?_)
    change evV x (evV ![a.val] (B.A.act c i)) = evV _ (B.A.act c i)
    rw [evV_comp _ _ _ hx]
    · congr 1
      funext k
      fin_cases k; rfl
    · intro k
      fin_cases k
      exact a.sm

omit [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
lemma sm_pt {n : ℕ} (j : Fin n) : Sm (pt V (n := n) d j) := by
  intro i
  simp [pt]

lemma matV_sm {n : ℕ} (p : Matrix (Fin n) (Fin n) O) (x : Fin n → Pt V m d) (hx : ∀ b, Sm (x b)) (b : Fin n) :
    Sm (matV B p x b) := by
  have h : matV B p x b = (∑ j, p b j • (⟨x j, hx j⟩ : SP B m)).val :=
    congrFun (matV_val B p fun j => (⟨x j, hx j⟩ : SP B m)) b
  rw [h]
  exact (∑ j, p b j • (⟨x j, hx j⟩ : SP B m)).sm

lemma matV_mul {n : ℕ} (p q : Matrix (Fin n) (Fin n) O) (x : Fin n → Pt V m d) (hx : ∀ b, Sm (x b)) :
    matV B (p * q) x = matV B p (matV B q x) := by
  have h1 : matV B q x = fun i => (∑ j, q i j • (⟨x j, hx j⟩ : SP B m)).val :=
    matV_val B q fun j => (⟨x j, hx j⟩ : SP B m)
  have h2 : matV B p (fun i => (∑ j, q i j • (⟨x j, hx j⟩ : SP B m)).val) =
      fun k => (∑ i, p k i • ∑ j, q i j • (⟨x j, hx j⟩ : SP B m)).val :=
    matV_val B p fun i => ∑ j, q i j • (⟨x j, hx j⟩ : SP B m)
  have h3 : matV B (p * q) x = fun k => (∑ j, (p * q) k j • (⟨x j, hx j⟩ : SP B m)).val :=
    matV_val B (p * q) fun j => (⟨x j, hx j⟩ : SP B m)
  rw [h1, h2, h3]
  funext k
  congr 1
  simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

lemma evV_matV {n : ℕ} (p : Matrix (Fin n) (Fin n) O) (x : Fin n → Pt V m d) (hx : ∀ b, Sm (x b)) (b : Fin n)
    (i : Fin d) : evV x (matV B p (fun j => pt V (n := n) d j) b i) = matV B p x b i := by
  obtain ⟨ψ, hX, hψ⟩ := evV_alg x hx
  have he : ∀ j, evL B x hx ⟨pt V (n := n) d j, sm_pt j⟩ = ⟨x j, hx j⟩ := by
    intro j
    apply SP.ext
    funext i'
    show evV x (pt V (n := n) d j i') = x j i'
    rw [hψ]
    exact hX (j, i')
  have h1 : matV B p (fun j => pt V (n := n) d j) =
      fun k => (∑ j, p k j • (⟨pt V (n := n) d j, sm_pt j⟩ : SP B n)).val :=
    matV_val B p fun j => (⟨pt V (n := n) d j, sm_pt j⟩ : SP B n)
  have h2 : matV B p x = fun k => (∑ j, p k j • (⟨x j, hx j⟩ : SP B m)).val :=
    matV_val B p fun j => (⟨x j, hx j⟩ : SP B m)
  rw [h1, h2]
  show (evL B x hx (∑ j, p b j • (⟨pt V (n := n) d j, sm_pt j⟩ : SP B n))).val i = _
  rw [map_sum]
  simp only [map_smul, he]

lemma foldr_const (l : List (Pt V m d)) (hl : ∀ a ∈ l, ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin d) :
    MvPowerSeries.constantCoeff (l.foldr (addV B.G.F) 0 i) = 0 := by
  have key : ∀ l' : List (Pt V m d), (∀ a ∈ l', ∀ i, MvPowerSeries.constantCoeff (a i) = 0) →
      ∀ i, MvPowerSeries.constantCoeff (l'.foldr (addV B.G.F) 0 i) = 0 := by
    intro l' hl'
    induction l' with
    | nil => intro i'; simp
    | cons a l' ih =>
      intro i'
      rw [List.foldr_cons]
      show MvPowerSeries.constantCoeff (evV ![a, l'.foldr (addV B.G.F) 0] (B.G.F i')) = 0
      apply evV_const _ _ _ (B.G.const i')
      intro b j
      fin_cases b
      · exact hl' a (by simp) j
      · exact ih (fun c hc => hl' c (by simp [hc])) j
  exact key l hl i

theorem matV_laws : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n m : ℕ) (p q : Matrix (Fin n) (Fin n) O) (x y : Fin n → Pt V m d), (∀ b i, MvPowerSeries.constantCoeff (x b i) ∈ maximalIdeal V) → (∀ b i, MvPowerSeries.constantCoeff (y b i) ∈ maximalIdeal V) → (∀ b i, MvPowerSeries.constantCoeff (matV B p x b i) ∈ maximalIdeal V) ∧ matV B (p * q) x = matV B p (matV B q x) ∧ (matV B p (fun b => addV B.G.F (x b) (y b)) = fun b => addV B.G.F (matV B p x b) (matV B p y b)) ∧ (∀ a : O, matV B (a • (1 : Matrix (Fin n) (Fin n) O)) x = fun b => compV (B.A.act a) (x b)) ∧ (∀ b i, evV x (matV B p (fun j => pt V (n := n) d j) b i) = matV B p x b i) ∧ (∀ b i, MvPowerSeries.constantCoeff (matV B p (fun j => pt V (n := n) d j) b i) = 0) ∧ ∀ f : PS V n d, pullM B (p * q) f = pullM B q (pullM B p f) := by
  intro V _ _ _ _ _ d O _ _ B n m p q x y hx hy
  have hx' : ∀ b, Sm (x b) := hx
  have hy' : ∀ b, Sm (y b) := hy
  have hpt : ∀ j : Fin n, Sm (pt V (n := n) d j) := fun j => sm_pt j
  refine ⟨fun b => matV_sm p x hx' b, matV_mul p q x hx', ?_, ?_, fun b i => evV_matV p x hx' b i, ?_, ?_⟩
  · have h1 : matV B p (fun b => addV B.G.F (x b) (y b)) =
        fun k => (∑ j, p k j • ((⟨x j, hx' j⟩ : SP B m) + ⟨y j, hy' j⟩)).val :=
      matV_val B p fun j => (⟨x j, hx' j⟩ : SP B m) + ⟨y j, hy' j⟩
    have h2 : matV B p x = fun k => (∑ j, p k j • (⟨x j, hx' j⟩ : SP B m)).val :=
      matV_val B p fun j => (⟨x j, hx' j⟩ : SP B m)
    have h3 : matV B p y = fun k => (∑ j, p k j • (⟨y j, hy' j⟩ : SP B m)).val :=
      matV_val B p fun j => (⟨y j, hy' j⟩ : SP B m)
    rw [h1, h2, h3]
    funext k
    show _ = ((∑ j, p k j • (⟨x j, hx' j⟩ : SP B m)) + ∑ j, p k j • (⟨y j, hy' j⟩ : SP B m)).val
    rw [← Finset.sum_add_distrib]
    simp only [smul_add]
  · intro a
    have h2 : matV B (a • (1 : Matrix (Fin n) (Fin n) O)) x =
        fun k => (∑ j, (a • (1 : Matrix (Fin n) (Fin n) O)) k j • (⟨x j, hx' j⟩ : SP B m)).val :=
      matV_val B _ fun j => (⟨x j, hx' j⟩ : SP B m)
    rw [h2]
    funext k
    show _ = (a • (⟨x k, hx' k⟩ : SP B m)).val
    congr 1
    simp [Matrix.one_apply, ite_smul, Finset.sum_ite_eq]
  · intro b i
    show MvPowerSeries.constantCoeff
      ((List.ofFn fun j => compV (B.A.act (p b j)) (pt V (n := n) d j)).foldr (addV B.G.F) 0 i) = 0
    apply foldr_const
    intro a ha k
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ha
    show MvPowerSeries.constantCoeff (evV ![pt V (n := n) d j] (B.A.act (p b j) k)) = 0
    apply evV_const _ _ _ (B.A.const (p b j) k)
    intro c k'
    fin_cases c
    simp [pt]
  · intro f
    have hq : ∀ b, Sm (matV B q (fun j => pt V (n := n) d j) b) := matV_sm q _ hpt
    have hp : ∀ b, Sm (matV B p (fun j => pt V (n := n) d j) b) := matV_sm p _ hpt
    show evV (matV B (p * q) fun j => pt V (n := n) d j) f =
      evV (matV B q fun j => pt V (n := n) d j) (evV (matV B p fun j => pt V (n := n) d j) f)
    rw [evV_comp _ _ hp hq, matV_mul p q _ hpt]
    congr 1
    funext b i
    exact (evV_matV p _ hq b i).symm

end GlobalTheory.PlaceInt.MatAct
