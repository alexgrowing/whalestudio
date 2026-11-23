import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc

set_option autoImplicit false

noncomputable section

open Set Filter Topology Matrix MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec chernPoly)
open scoped ContDiff ComplexOrder ComplexConjugate

namespace GlobalTheory.CxForm

section Point

variable {n m : ℕ}

abbrev Alt (n : ℕ) : Type := ExteriorAlgebra ℂ (Fin n ⊕ Fin n → ℂ)

abbrev Ev (n : ℕ) : Type := Subalgebra.center ℂ (Alt n)

def dz (a : Fin n) : Alt n := ExteriorAlgebra.ι ℂ (Pi.single (.inl a) 1)

def dzb (a : Fin n) : Alt n := ExteriorAlgebra.ι ℂ (Pi.single (.inr a) 1)

def bas (n : ℕ) : Module.Basis (Finset (Fin (n + n))) ℂ (Alt n) :=
  ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv).ExteriorAlgebra

def IsType (p q : ℕ) (α : Alt n) : Prop :=
  ∀ S, (bas n).repr α S ≠ 0 → (S.filter (·.val < n)).card = p ∧ (S.filter (n ≤ ·.val)).card = q

def swap : Alt n →ₐ[ℂ] Alt n := ExteriorAlgebra.map (LinearMap.funLeft ℂ ℂ Sum.swap)

def IsReal (α : Alt n) : Prop := ∀ S, (bas n).repr (swap α) S = conj ((bas n).repr α S)

def pull (L : V n →L[ℂ] V m) : Alt m →ₐ[ℂ] Alt n :=
  ExteriorAlgebra.map (Matrix.toLin' (fromBlocks (of fun b a => L (coordVec b) a) 0 0
    (of fun b a => conj (L (coordVec b) a))))

theorem ι_mul_ι_mem_center (u w : Fin n ⊕ Fin n → ℂ) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w ∈ Subalgebra.center ℂ (Alt n) := by
  refine Subalgebra.mem_center_iff.2 fun b => ?_
  induction b using ExteriorAlgebra.induction with
  | algebraMap r => exact Algebra.commutes _ _
  | ι x =>
    rw [← mul_assoc, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x u), neg_mul, mul_assoc,
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x w), mul_neg, neg_neg, mul_assoc]
  | mul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]

def sym (x : Fin n × Fin n) : Ev n := ⟨dz x.1 * dzb x.2, ι_mul_ι_mem_center _ _⟩

def ofValues (α : V n → V n → ℂ) : Ev n := ∑ a, ∑ b, α (coordVec a) (coordVec b) • sym (a, b)

def vol (n : ℕ) : Ev n := ∏ a, (Complex.I / 2) • sym (a, a)

def dens (α : Alt n) : ℂ := (bas n).repr α Finset.univ / (bas n).repr (vol n : Alt n) Finset.univ

def coefwise (T : (V n → ℂ) → ℂ) (α : V n → Alt n) : Alt n :=
  ∑ S, T (fun x => (bas n).repr (α x) S) • bas n S

def delAt (α : V n → Alt n) (v : V n) : Alt n := ∑ a, dz a * coefwise (fun f => del f v (coordVec a)) α

def dbarAt (α : V n → Alt n) (v : V n) : Alt n := ∑ a, dzb a * coefwise (fun f => dbar f v (coordVec a)) α

def chernAt {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n) (j : ℕ) : Ev n :=
  kappa ^ j • MvPolynomial.aeval sym (chernPoly G v j)

theorem swap_dz (a : Fin n) : swap (dz a) = dzb a ∧ swap (dzb a) = dz a := by
  constructor <;> refine (ExteriorAlgebra.map_apply_ι _ _).trans (congrArg _ (funext ?_)) <;> rintro (b | b) <;>
    simp [LinearMap.funLeft_apply, Pi.single_apply]

theorem pull_dz (L : V n →L[ℂ] V m) (a : Fin m) : pull L (dz a) = ∑ b, L (coordVec b) a • dz b ∧
    pull L (dzb a) = ∑ b, conj (L (coordVec b) a) • dzb b := by
  simp only [dz, dzb, ← map_smul, ← map_sum]
  constructor <;> refine (ExteriorAlgebra.map_apply_ι _ _).trans (congrArg _ (funext ?_)) <;> rintro (b | b) <;>
    simp [Pi.single_apply, Finset.sum_apply]

theorem bas_singleton (i : Fin n ⊕ Fin n) :
    bas n {finSumFinEquiv i} = ExteriorAlgebra.ι ℂ (Pi.single i 1) := by
  rw [bas, ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton _), ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply]
  simp [Set.powersetCard.ofFinEmbEquiv, Set.powersetCard.ofCard]

theorem bas_empty : bas n ∅ = 1 := by
  rw [bas, ExteriorAlgebra.basis_apply_ofCard _ Finset.card_empty, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_zero_apply]

theorem bas_mul {S T : Finset (Fin (n + n))} (h : Disjoint S T) : ∃ ε : ℤˣ, bas n S * bas n T = ε • bas n (S ∪ T) := by
  have := ExteriorAlgebra.basis_mul_of_disjoint ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv)
    (Set.powersetCard.ofCard (s := S) rfl) (Set.powersetCard.ofCard (s := T) rfl) h
  exact ⟨_, this.trans (by congr 2; ext; simp [Set.powersetCard.disjUnion])⟩

theorem vol_eq (n : ℕ) : ∃ c : ℂ, c ≠ 0 ∧ (vol n : Alt n) = c • bas n Finset.univ := by
  have key (s : Finset (Fin n)) : ∃ c : ℂ, c ≠ 0 ∧ ((∏ a ∈ s, (Complex.I / 2) • sym (a, a) : Ev n) : Alt n) =
      c • bas n (Finset.univ.filter fun i => (finSumFinEquiv.symm i).elim id id ∈ s) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp [bas_empty]⟩
    | insert a s ha ih =>
      obtain ⟨c, hc, e⟩ := ih
      obtain ⟨ε, h₁⟩ := bas_mul (S := {finSumFinEquiv (.inl a)}) (T := {finSumFinEquiv (.inr a)})
        (Finset.disjoint_singleton.2 (finSumFinEquiv.injective.ne Sum.inl_ne_inr))
      obtain ⟨ε', h₂⟩ := bas_mul (S := {finSumFinEquiv (.inl a)} ∪ {finSumFinEquiv (.inr a)})
        (T := Finset.univ.filter fun i => (finSumFinEquiv.symm i).elim id id ∈ s) (by simp [ha, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right])
      refine ⟨Complex.I / 2 * c * ((ε : ℤ) * (ε' : ℤ)), by simp [hc], ?_⟩
      rw [Finset.prod_insert ha, Subalgebra.coe_mul, e, Subalgebra.coe_smul,
        show (sym (a, a) : Alt n) = dz a * dzb a from rfl, dz, dzb, ← bas_singleton,
        ← bas_singleton, h₁, smul_mul_smul_comm, smul_mul_assoc, h₂, Units.smul_def, Units.smul_def,
        ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ, smul_smul, smul_smul, mul_assoc _ (_ : ℂ) (_ : ℂ)]
      congr 2
      ext i
      obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
  simpa [vol] using key Finset.univ

theorem dens_vol (n : ℕ) : dens (vol n : Alt n) = 1 := by
  obtain ⟨c, hc, e⟩ := vol_eq n
  exact div_self (by simpa [e] using hc)

theorem isType_isReal_const (t : ℝ) : IsType 0 0 (algebraMap ℂ (Alt n) t) ∧ IsReal (algebraMap ℂ (Alt n) t) := by
  refine ⟨fun S hS => ?_, fun S => ?_⟩
  · obtain rfl : ∅ = S := by
      by_contra h
      simp [Algebra.algebraMap_eq_smul_one, ← bas_empty, h, -Complex.coe_smul] at hS
    simp
  · rw [AlgHom.commutes]
    by_cases h : ∅ = S <;>
      simp [Algebra.algebraMap_eq_smul_one, ← bas_empty, Finsupp.single_apply, h, -Complex.coe_smul]

theorem isReal_I_smul_sym (a : Fin n) : IsReal (Complex.I • (dz a * dzb a)) := fun S => by
  obtain ⟨ε, h⟩ := bas_mul (S := {finSumFinEquiv (.inl a)}) (T := {finSumFinEquiv (.inr a)})
    (Finset.disjoint_singleton.2 (finSumFinEquiv.injective.ne Sum.inl_ne_inr))
  rw [map_smul, map_mul, (swap_dz a).1, (swap_dz a).2, dz, dzb,
    eq_neg_of_add_eq_zero_right (ExteriorAlgebra.ι_add_mul_swap _ _), ← bas_singleton, ← bas_singleton, h,
    Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]
  simp only [map_smul, map_neg, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.neg_apply, Finsupp.single_apply]
  split_ifs <;> simp

theorem coefwise_smul {T : (V n → ℂ) → ℂ} (hT : T (fun _ => 0) = 0) (u : V n → ℂ) (S : Finset (Fin (n + n))) :
    coefwise T (fun x => u x • bas n S) = T u • bas n S := by
  rw [coefwise, Finset.sum_eq_single S (fun S' _ h => by simp [Finsupp.single_apply, h.symm, hT]) (by simp)]
  simp

theorem delAt_dbarAt_fun {u : V n → ℝ} {v : V n} (hu : ContDiffAt ℝ 2 u v) :
    kappa • delAt (dbarAt fun x => algebraMap ℂ (Alt n) (u x)) v = ofValues (ddc u v) := by
  have h₁ (x : V n) (S) : (bas n).repr (dbarAt (fun x => algebraMap ℂ (Alt n) (u x)) x) S =
      ∑ b, if S = {finSumFinEquiv (.inr b)} then dbar (fun x => (u x : ℂ)) x (coordVec b) else 0 := by
    simp only [dbarAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
    rw [map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one, dzb, ← bas_singleton]
    simp [Finsupp.single_apply, eq_comm]
  have h₂ (a : Fin n) : coefwise (fun f => del f v (coordVec a)) (dbarAt fun x => algebraMap ℂ (Alt n) (u x)) =
      ∑ b, leviForm u v (coordVec a) (coordVec b) • dzb b := by
    refine (bas n).ext_elem fun S => ?_
    simp only [coefwise, h₁, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finset_sum_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, dzb,
      ← bas_singleton]
    by_cases h : ∃ b, S = {finSumFinEquiv (.inr b)}
    · obtain ⟨b, rfl⟩ := h
      simp only [Finset.singleton_inj, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, leviForm]
      exact (ddbar_eq_del_dbar (contDiffAt_ofReal_comp hu) _ _).symm
    · push_neg at h
      simp [h, fun b => (h b).symm, -finSumFinEquiv_apply_right]
  simp only [delAt, h₂, ofValues, ddc, Finset.mul_sum, Finset.smul_sum, mul_smul_comm, smul_smul,
    AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym]

end Point

structure HolAtlas (M : Type) [TopologicalSpace M] (n : ℕ) where

  ι : Type

  e : ι → OpenPartialHomeomorph M (V n)

  cover : ∀ y, ∃ i, y ∈ (e i).source

  holo : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)

namespace HolAtlas

variable {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n) (A' : HolAtlas M' n')

def std (n : ℕ) : HolAtlas (V n) n :=
  ⟨Unit, fun _ => .refl _, fun _ => ⟨(), trivial⟩, fun _ _ => differentiableOn_id⟩

def ofFin (B : ReciprocityTheory.AnForm.M.FinHolAtlas n M) : HolAtlas M n where
  ι := Fin B.n
  e j := (B.chart j).transHomeomorph (EuclideanSpace.equiv (Fin n) ℂ).symm.toHomeomorph
  cover := B.cover
  holo i j := (EuclideanSpace.equiv (Fin n) ℂ).symm.differentiable.comp_differentiableOn
    ((B.holo i j).differentiableOn.comp (EuclideanSpace.equiv (Fin n) ℂ).differentiableOn fun _ hv => hv)

def Pt : Type := {x : A.ι × M // x.2 ∈ (A.e x.1).source}

variable {A} in

abbrev Pt.pt (x : A.Pt) : M := x.1.2

variable {A} in

abbrev Pt.ch (x : A.Pt) : OpenPartialHomeomorph M (V n) := A.e x.1.1

variable {A} in

abbrev Pt.crd (x : A.Pt) : V n := x.ch x.pt

abbrev Fld : Type := A.Pt → Alt n

open Classical in

def loc (α : A.Fld) (i : A.ι) (v : V n) : Alt n :=
  if h : v ∈ (A.e i).target then α ⟨(i, (A.e i).symm v), (A.e i).map_target h⟩ else 0

def HolOn (U : Set M) (g : M → ℂ) : Prop :=
  ∀ i, DifferentiableOn ℂ (g ∘ (A.e i).symm) ((A.e i).target ∩ (A.e i).symm ⁻¹' U)

def SmoothOn (U : Set M) (g : M → ℂ) : Prop :=
  ∀ i, ContDiffOn ℝ ∞ (g ∘ (A.e i).symm) ((A.e i).target ∩ (A.e i).symm ⁻¹' U)

def IsHolo (f : M' → M) : Prop :=
  Continuous f ∧ ∀ j i, DifferentiableOn ℂ (A.e i ∘ f ∘ (A'.e j).symm)
    ((A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source))

structure IsForm (α : A.Fld) : Prop where

  smooth : ∀ i S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (A.loc α i v) S) (A.e i).target

  compat : ∀ x x' : A.Pt, x.pt = x'.pt → α x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (α x')

def IsRealForm (q : ℕ) (α : A.Fld) : Prop := A.IsForm α ∧ ∀ x, IsType q q (α x) ∧ IsReal (α x)

def fn (u : M → ℝ) : A.Fld := fun x => algebraMap ℂ _ (u x.pt)

def del (α : A.Fld) : A.Fld := fun x => delAt (A.loc α x.1.1) x.crd

def dbar (α : A.Fld) : A.Fld := fun x => dbarAt (A.loc α x.1.1) x.crd

def ddc (α : A.Fld) : A.Fld := kappa • A.del (A.dbar α)

def IsExact (α : A.Fld) : Prop := ∃ u w, A.IsForm u ∧ A.IsForm w ∧ α = A.del u + A.dbar w

def pullback (f : M' → M) (α : A.Fld) : A'.Fld := fun x =>
  pull (fderiv ℂ (A.e (A.cover (f x.pt)).choose ∘ f ∘ x.ch.symm) x.crd) (α ⟨(_, f x.pt), (A.cover (f x.pt)).choose_spec⟩)

def chern {r : Type} [Fintype r] [DecidableEq r] (G : M → Matrix r r ℂ) (j : ℕ) (x : A.Pt) : Ev n :=
  chernAt (fun v => G (x.ch.symm v)) x.crd j

def part [MeasurableSpace M] (α : A.Fld) (ε : ℤˣ) : Measure M :=
  ChartGlue.glueMeas A.e fun i y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α i (A.e i y))).re)

def integral [MeasurableSpace M] (α : A.Fld) : ℝ := (A.part α 1).real univ - (A.part α (-1)).real univ

theorem loc_crd (α : A.Fld) (x : A.Pt) : A.loc α x.1.1 x.crd = α x := by
  rw [loc, dif_pos (x.ch.map_source x.2)]
  exact congrArg α (Subtype.ext (Prod.ext rfl (x.ch.left_inv x.2)))

theorem isForm_fn {u : M → ℝ} (hu : A.SmoothOn univ fun y => u y) : A.IsForm (A.fn u) := by
  refine ⟨fun i S => ?_, fun x x' h => by rw [fn, fn, AlgHom.commutes, h]⟩
  refine (((hu i).mono fun v hv => ⟨hv, trivial⟩).mul (contDiffOn_const (c := (bas n).repr 1 S))).congr fun v hv => ?_
  simp [loc, hv, fn, Algebra.algebraMap_eq_smul_one, -Complex.coe_smul]

end HolAtlas

structure HermSeq {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (r s : ℕ) where

  κ : Type

  U : κ → Set M

  isOpen : ∀ a, IsOpen (U a)

  cover : ∀ y, ∃ a, y ∈ U a

  g : κ → κ → M → Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ

  holo : ∀ a b i j, A.HolOn (U a ∩ U b) fun y => g a b y i j

  tri : ∀ a b, ∀ y ∈ U a ∩ U b, (g a b y).toBlocks₂₁ = 0

  g_self : ∀ a, ∀ y ∈ U a, g a a y = 1

  g_mul : ∀ a b c, ∀ y ∈ U a ∩ U b ∩ U c, g a b y * g b c y = g a c y

  sub : κ → M → Matrix (Fin r) (Fin r) ℂ

  mid : κ → M → Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ

  quot : κ → M → Matrix (Fin s) (Fin s) ℂ

  smooth : ∀ a, (∀ i j, A.SmoothOn (U a) fun y => sub a y i j) ∧ (∀ i j, A.SmoothOn (U a) fun y => mid a y i j) ∧
    ∀ i j, A.SmoothOn (U a) fun y => quot a y i j

  posDef : ∀ a, ∀ y ∈ U a, (sub a y).PosDef ∧ (mid a y).PosDef ∧ (quot a y).PosDef

  trans : ∀ a b, ∀ y ∈ U a ∩ U b, sub b y = chg (g a b y).toBlocks₁₁ (sub a y) ∧ mid b y = chg (g a b y) (mid a y) ∧
    quot b y = chg (g a b y).toBlocks₂₂ (quot a y)

namespace HermSeq

variable {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' r s : ℕ} {A : HolAtlas M n} {A' : HolAtlas M' n'}

def IsPull (T' : HermSeq A' r s) (T : HermSeq A r s) (f : M' → M) : Prop :=
  ∃ φ : T.κ → T'.κ → M' → Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ,
    (∀ a b i j, A'.HolOn (f ⁻¹' T.U a ∩ T'.U b) fun y => φ a b y i j) ∧
    ∀ a b y, f y ∈ T.U a → y ∈ T'.U b → (φ a b y).toBlocks₂₁ = 0 ∧
      (∀ a', f y ∈ T.U a' → T.g a' a (f y) * φ a b y = φ a' b y) ∧
      (∀ b', y ∈ T'.U b' → φ a b y * T'.g b b' y = φ a b' y) ∧
      T'.sub b y = chg (φ a b y).toBlocks₁₁ (T.sub a (f y)) ∧ T'.mid b y = chg (φ a b y) (T.mid a (f y)) ∧
      T'.quot b y = chg (φ a b y).toBlocks₂₂ (T.quot a (f y))

def IsSplit (T : HermSeq A r s) : Prop :=
  ∀ a, ∃ t : M → Matrix (Fin r) (Fin s) ℂ, (∀ i j, A.HolOn (T.U a) fun y => t y i j) ∧
    ∀ y ∈ T.U a, chg (fromBlocks 1 (t y) 0 1) (T.mid a y) = fromBlocks (T.sub a y) 0 0 (T.quot a y)

theorem isPull_self (T : HermSeq A r s) : T.IsPull T id :=
  ⟨T.g, T.holo, fun a b y ha hb => ⟨T.tri a b y ⟨ha, hb⟩, fun a' h => T.g_mul a' a b y ⟨⟨h, ha⟩, hb⟩,
    fun b' h => T.g_mul a b b' y ⟨⟨ha, hb⟩, h⟩, T.trans a b y ⟨ha, hb⟩⟩⟩

def ofGram (H : V n → Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) (h : IsPosFrame univ H) : HermSeq (.std n) r s where
  κ := Unit
  U _ := univ
  isOpen _ := isOpen_univ
  cover _ := ⟨(), trivial⟩
  g _ _ _ := 1
  holo _ _ _ _ _ := differentiableOn_const _
  tri _ _ _ _ := by ext; simp [toBlocks₂₁]
  g_self _ _ _ := rfl
  g_mul _ _ _ _ _ := mul_one _
  sub _ y := subGram (H y)
  mid _ := H
  quot _ y := quotGram (H y)
  smooth _ := ⟨fun i j _ => (h.sub.smooth i j).mono (subset_univ _), fun i j _ => (h.smooth i j).mono (subset_univ _),
    fun i j _ => (h.quot.smooth i j).mono (subset_univ _)⟩
  posDef _ y _ := ⟨h.sub.posDef y trivial, h.posDef y trivial, h.quot.posDef y trivial⟩
  trans _ _ _ _ := by
    refine ⟨?_, (chg_one _).symm, ?_⟩ <;> rw [← fromBlocks_one]
    exacts [(chg_one _).symm, (chg_one _).symm]

end HermSeq

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.VBExt (AdaptedChart)

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

structure IsRegVar (p : X ⟶ Sp k) (D : ℕ) : Prop extends IsArithVar p D where

  regular : ∀ x, IsRegularLocalRing (X.presheaf.stalk x)

theorem IsRegVar.of_smooth {p : X ⟶ Sp ℤ} [Smooth p] (h : IsArithVar p D) : IsRegVar p D := by
  refine ⟨h, fun x => ?_⟩
  have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth ℤ p x
  exact .of_isRegularRing_of_isLocalRing _

theorem isRegVar_proj (N : ℕ) : IsRegVar (PSpace.str ℤ N) N :=
  have : Smooth (PSpace.str ℤ N) := SmoothOfRelativeDimension.smooth N _
  .of_smooth (ProjSpace.isArithVar_int N)

theorem isRegVar_int : IsRegVar (𝟙 (Sp ℤ)) 0 := .of_smooth ArithBase.isArithVar_int

namespace IsRegVar

variable (h : IsRegVar p D)

def atlas (σ : k →+* ℂ) : HolAtlas (CxPts p σ) D where
  ι := AlgChart p σ D
  e c := c.e
  cover y := have ⟨R⟩ := RegGenSmooth.genSmooth h.toIsArithVar h.regular σ
    have ⟨i, hi⟩ := R.cover y
    ⟨R.chart i, hi⟩
  holo c c' := c.holo_trans c'

abbrev Fld : Type := ∀ σ, (h.atlas σ).Fld

def IsArForm (q : ℕ) (η : h.Fld) : Prop :=
  (∀ σ, (h.atlas σ).IsRealForm q (η σ)) ∧ ∀ σ σ' (x : (h.atlas σ).Pt) (x' : (h.atlas σ').Pt),
    x'.pt.1 = spMap (starRingEnd ℂ) ≫ x.pt.1 →
    (∀ z ∈ x.ch.source, ∀ z' ∈ x'.ch.source, z'.1 = spMap (starRingEnd ℂ) ≫ z.1 → ∀ a, x'.ch z' a = conj (x.ch z a)) →
    swap (η σ' x') = (-1 : ℂ) ^ q • η σ x

def integral (η : h.Fld) : ℝ := ∑ᶠ σ, (h.atlas σ).integral (η σ)

theorem smoothOn {σ : k →+* ℂ} {m : Type} {U : Set (CxPts p σ)} {G : CxPts p σ → Matrix m m ℂ}
    (H : ∀ y ∈ U, MInfAt G y) (i j : m) : (h.atlas σ).SmoothOn U fun y => G y i j := fun c v hv => by
  have := (H _ hv.2 i j).contDiffAt_chart c (c.e.map_target hv.1)
  erw [c.e.right_inv hv.1] at this
  exact this.contDiffWithinAt

theorem isArForm_fn {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) :
    h.IsArForm 0 fun σ => (h.atlas σ).fn (u σ) := by
  refine ⟨fun σ => ⟨HolAtlas.isForm_fn _ (h.smoothOn (G := fun y (_ _ : Unit) => (u σ y : ℂ)) (fun y _ _ _ =>
    (vInfAt_iff_cInfAt.2 (hu σ y)).comp_contDiff Complex.ofRealCLM.contDiff) () ()), fun _ => isType_isReal_const _⟩,
    fun σ σ' x x' e _ => ?_⟩
  rw [pow_zero, one_smul]
  refine (AlgHom.commutes _ _).trans ?_
  exact congrArg (fun t : ℝ => algebraMap ℂ _ t) (hc σ σ' PUnit.unit _ _ e mem_ptsIn_top)

def seq {S : ShortComplex X.Modules} (hS : S.ShortExact) {r s : ℕ} {h₁ : VMetric p S.X₁ r} {h₂ : VMetric p S.X₂ (r + s)}
    {h₃ : VMetric p S.X₃ s} (H₁ : h₁.IsCInf) (H₂ : h₂.IsCInf) (H₃ : h₃.IsCInf) (σ : k →+* ℂ) :
    HermSeq (h.atlas σ) r s where
  κ := AdaptedChart S r s
  U a := ptsIn p σ a.U
  isOpen _ := isOpen_ptsIn _
  cover := Met.exists_adapted hS h₁.isVB h₃.isVB
  g a b := a.tr p σ hS b
  holo a b i j c := (c.holo _ _).mono fun _ hv => ⟨hv.1, mem_ptsIn_inf.2 ⟨hv.2.2, hv.2.1⟩⟩
  tri a b y hy := by rw [a.tr_eq hS b hy.1 hy.2, toBlocks_fromBlocks₂₁]
  g_self a y hy := by rw [AdaptedChart.tr, Chart.tr_self _ hy, submatrix_one_equiv]
  g_mul a b c y hy := by
    rw [AdaptedChart.tr, AdaptedChart.tr, submatrix_mul_equiv, Chart.tr_mul _ _ _ hy.1.2 hy.2, AdaptedChart.tr]
  sub a := (h₁.met σ).G a.sub
  mid a := (h₂.met σ).gram a.frame
  quot a := (h₃.met σ).G a.quot
  smooth a := ⟨h.smoothOn (H₁ σ a.sub), h.smoothOn fun _ => (H₂ σ).gram a.frame, h.smoothOn (H₃ σ a.quot)⟩
  posDef a y hy := ⟨(h₁.met σ).posDef a.sub y hy, (h₂.met σ).posDef_gram_frame hS a hy, (h₃.met σ).posDef a.quot y hy⟩
  trans a b y hy := by
    refine ⟨?_, (h₂.met σ).gram_frame_trans hS a b hy.1 hy.2, ?_⟩ <;> rw [a.tr_eq hS b hy.1 hy.2]
    exacts [(h₁.met σ).trans a.sub b.sub y hy.1, (h₃.met σ).trans a.quot b.quot y hy.1]

end IsRegVar

def lineSeq : HermSeq ((isRegVar_proj 1).atlas (Int.castRingHom ℂ)) 1 1 :=
  (isRegVar_proj 1).seq (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact
    (HermVB.ofLB (ProjSpace.hermitianTwistingSheaf ℤ 1)).cInf ProjSpace.hermSum.cInf (HermVB.ofLB (ProjSpace.hermitianTwistingSheaf ℤ 1)).dual.cInf _

theorem isSplit_ofGram_one (n r s : ℕ) : (HermSeq.ofGram (n := n) (r := r) (s := s) (fun _ => 1)
    ⟨isOpen_univ, fun _ _ => contDiffOn_const, fun _ _ => PosDef.one⟩).IsSplit := fun _ =>
  ⟨0, fun _ _ _ => differentiableOn_const (0 : ℂ), fun _ _ => by
    simp only [HermSeq.ofGram, Pi.zero_apply, fromBlocks_one, chg_one, subGram, quotGram]
    ext (i | i) (j | j) <;> simp [toBlocks₁₁, toBlocks₂₂, toBlocks₂₁, one_apply, mul_apply]⟩

end GlobalTheory.CxForm
