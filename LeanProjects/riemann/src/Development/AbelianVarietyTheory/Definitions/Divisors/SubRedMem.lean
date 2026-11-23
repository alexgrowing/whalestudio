import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq

set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology TensorProduct

namespace GlobalTheory.AnPer

open CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}

@[reducible] def Charts.Obj.cAlg (T : K.Obj) : Algebra ℂ T.C :=
  ((algebraMap (Hol F.V) T.C).comp (algebraMap ℂ (Hol F.V))).toAlgebra

attribute [local instance] Charts.Obj.cAlg

def Charts.Hom.φc {T T' : K.Obj} (f : T ⟶ T') : T.C →ₐ[ℂ] T'.C :=
  { (f.φ : T.C →+* T'.C) with commutes' := fun c ↦ f.φ.commutes (algebraMap ℂ (Hol F.V) c) }

def Charts.Obj.ρc (T : K.Obj) : Hol (K.W T.k) →ₐ[ℂ] T.C :=
  { T.ρ with
    commutes' := fun c ↦ by
      have e : K.cst T.k (algebraMap ℂ (Hol F.V) c) = algebraMap ℂ _ c := rfl
      exact (congrArg T.ρ e.symm).trans (T.ρ_cst _) }

variable (D : Type) [CommRing D] [Algebra ℂ D]

abbrev Charts.Obj.ten (T : K.Obj) : Type := D ⊗[ℂ] T.C

def Charts.Hom.ten {T T' : K.Obj} (f : T ⟶ T') : T.ten D →ₐ[D] T'.ten D :=
  Algebra.TensorProduct.map (AlgHom.id D D) (Charts.Hom.φc f)

theorem Charts.Hom.ten_tmul {T T' : K.Obj} (f : T ⟶ T') (d : D) (c : T.C) :
    Charts.Hom.ten D f (d ⊗ₜ c) = d ⊗ₜ f.φ c := rfl

variable (K) in

@[reducible] def Charts.Ten : K.Obj ⥤ CommAlgCat.{0} D where
  obj T := CommAlgCat.of D (T.ten D)
  map f := CommAlgCat.ofHom (Charts.Hom.ten D f)
  map_id T := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun _ _ ↦ rfl)
  map_comp f f' := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun _ _ ↦ rfl)

variable {D}

variable (K) in

def Charts.tenZ (p : Λ →+ D) : Z1 (K.Ten D) :=
  ⟨fun _ T' f ↦ algebraMap D (T'.ten D) (p f.deg), fun T T' T'' f f' ↦ by
    change algebraMap D (T''.ten D) (p (f.deg + f'.deg)) =
      Charts.Hom.ten D f' (algebraMap D _ _) + algebraMap D (T''.ten D) _
    rw [AlgHom.commutes, map_add, map_add]⟩

variable (π : D →ₐ[ℂ] ℂ)

def Charts.Obj.red (T : K.Obj) : T.ten D →ₐ[ℂ] T.C :=
  Algebra.TensorProduct.lift ((Algebra.ofId ℂ T.C).comp π) (AlgHom.id ℂ T.C) fun _ _ ↦ Commute.all _ _

theorem Charts.Obj.red_tmul (T : K.Obj) (d : D) (c : T.C) : T.red π (d ⊗ₜ c) = algebraMap ℂ T.C (π d) * c := rfl

def Charts.Obj.tenJ (T : K.Obj) : Ideal (T.ten D) := T.J.comap (T.red π)

set_option autoImplicit false in
open TopologicalSpace Filter Topology TensorProduct in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : _root_.GlobalTheory.AnPer.Fam I g Λ}
  {K : _root_.GlobalTheory.AnPer.Charts F} in
attribute [local instance] _root_.GlobalTheory.AnPer.Charts.Obj.cAlg in
variable (D : Type) [CommRing D] [Algebra ℂ D] in
variable {D} in
variable (π : D →ₐ[ℂ] ℂ) in

theorem _root_.GlobalTheory.AnPer.Charts.Hom.red_ten
    {T T' : K.Obj} (f : T ⟶ T') (x : T.ten D) :
    T'.red π
        (_root_.GlobalTheory.AnPer.Charts.Hom.ten D f x) =
      f.φ (T.red π x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d c =>
    rw [_root_.GlobalTheory.AnPer.Charts.Hom.ten_tmul,
      _root_.GlobalTheory.AnPer.Charts.Obj.red_tmul,
      _root_.GlobalTheory.AnPer.Charts.Obj.red_tmul, map_mul]
    congr 1
    exact ((_root_.GlobalTheory.AnPer.Charts.Hom.φc f).commutes
      (π d)).symm
  | add x y hx hy => simp only [map_add, hx, hy]

set_option autoImplicit false in
open TopologicalSpace Filter Topology TensorProduct in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : _root_.GlobalTheory.AnPer.Fam I g Λ}
  {K : _root_.GlobalTheory.AnPer.Charts F} in
attribute [local instance] _root_.GlobalTheory.AnPer.Charts.Obj.cAlg in
variable (D : Type) [CommRing D] [Algebra ℂ D] in
variable {D} in
variable (π : D →ₐ[ℂ] ℂ) in

theorem _root_.GlobalTheory.AnPer.Charts.Hom.ten_mem {T T' : K.Obj}
    (f : T ⟶ T') {x : T.ten D} (h : x ∈ T.tenJ π) :
    _root_.GlobalTheory.AnPer.Charts.Hom.ten D f x ∈
      T'.tenJ π := by
  change T'.red π _ ∈ T'.J
  rw [_root_.GlobalTheory.AnPer.Charts.Hom.red_ten]
  exact f.mem _ h

set_option autoImplicit false in
open TopologicalSpace Filter Topology TensorProduct in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : _root_.GlobalTheory.AnPer.Fam I g Λ}
  {K : _root_.GlobalTheory.AnPer.Charts F} in
attribute [local instance] _root_.GlobalTheory.AnPer.Charts.Obj.cAlg in
variable (D : Type) [CommRing D] [Algebra ℂ D] in
variable {D} in
variable (π : D →ₐ[ℂ] ℂ) in
private theorem sub_one_tmul_red_mem_map_ker (T : K.Obj) (x : T.ten D) :
    x - (1 : D) ⊗ₜ T.red π x ∈
      (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] T.C) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d c =>
    rw [_root_.GlobalTheory.AnPer.Charts.Obj.red_tmul,
      ← Algebra.smul_def]
    have e : d ⊗ₜ[ℂ] c - (1 : D) ⊗ₜ (π d • c) =
        (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] T.C) (d - algebraMap ℂ D (π d)) *
          ((1 : D) ⊗ₜ c) := by
      rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        sub_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [e]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  | add x y hx hy =>
    rw [map_add, tmul_add, add_sub_add_comm]
    exact add_mem hx hy

set_option autoImplicit false in
open TopologicalSpace Filter Topology TensorProduct in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : _root_.GlobalTheory.AnPer.Fam I g Λ}
  {K : _root_.GlobalTheory.AnPer.Charts F} in
attribute [local instance] _root_.GlobalTheory.AnPer.Charts.Obj.cAlg in
variable (D : Type) [CommRing D] [Algebra ℂ D] in
variable {D} in
variable (π : D →ₐ[ℂ] ℂ) in

theorem _root_.GlobalTheory.AnPer.Charts.Obj.tenJ_nil
    (hπ : IsNilpotent (RingHom.ker π)) (T : K.Obj) : IsNilpotent (T.tenJ π) := by
  obtain ⟨m, hm⟩ := hπ
  obtain ⟨n, hn⟩ := T.nil
  have hle : T.tenJ π ≤
      (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] T.C) ⊔
        T.J.map (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] D ⊗[ℂ] T.C) := by
    intro x hx
    have hx' : T.red π x ∈ T.J := hx
    have e : x = (x - (1 : D) ⊗ₜ T.red π x) +
        (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] D ⊗[ℂ] T.C)
          (T.red π x) := by
      rw [Algebra.TensorProduct.includeRight_apply, sub_add_cancel]
    rw [e]
    exact add_mem (Ideal.mem_sup_left (sub_one_tmul_red_mem_map_ker π T x))
      (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hx'))
  refine ⟨m + n, eq_bot_iff.2 ?_⟩
  calc T.tenJ π ^ (m + n)
      ≤ ((RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] T.C) ⊔
          T.J.map (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] D ⊗[ℂ] T.C)) ^ (m + n) :=
        Ideal.pow_right_mono hle _
    _ ≤ (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] T.C) ^ m ⊔
          T.J.map (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] D ⊗[ℂ] T.C) ^ n :=
        Ideal.sup_pow_add_le_pow_sup_pow
    _ = ⊥ := by
        rw [← Ideal.map_pow, ← Ideal.map_pow, hm, hn]
        simp only [Ideal.zero_eq_bot, Ideal.map_bot, sup_bot_eq]

@[reducible] def Charts.Obj.tenRat (T : K.Obj) : Algebra ℚ (T.ten D) :=
  ((algebraMap ℂ (T.ten D)).comp (algebraMap ℚ ℂ)).toAlgebra

open Classical in

def Charts.Obj.tenδ (T : K.Obj) : DividedPowers (T.tenJ π) :=
  letI := T.tenRat (D := D)
  RatAlgebra.dividedPowers (T.tenJ π)

variable {X : Scheme.{0}} {s : X ⟶ Sp ℂ} {σ : ℂ →+* Hol F.V} (r : Real K s σ) (hσ : σ = algebraMap ℂ (Hol F.V))
  {D₀ : Type} [CommRing D₀] {π₀ : D₀ →+* ℂ} (κ : DividedPowers (RingHom.ker π₀)) {s' : X ⟶ Sp D₀}
  (hs : s' = s ≫ spMap π₀) (ι : D₀ →+* D) (hι : ∀ d, π (ι d) = π₀ d) (hπ : IsNilpotent (RingHom.ker π))

def Real.tenObj (T : K.Obj) : Thick κ s' where
  B := T.ten D
  alg := ((algebraMap D (T.ten D)).comp ι).toAlgebra
  J := T.tenJ π
  δ := T.tenδ π
  nil := letI := T.tenRat (D := D); isPDNilpotent_of_rat _ (T.tenJ_nil π hπ)
  dp := letI := T.tenRat (D := D); isDPMorphism_of_rat κ _ ((algebraMap D (T.ten D)).comp ι) fun d hd ↦ by
    change T.red π (ι d ⊗ₜ 1) ∈ T.J
    rw [Charts.Obj.red_tmul, hι, (RingHom.mem_ker).1 hd, map_zero, zero_mul]
    exact T.J.zero_mem
  B₀ := T.C ⧸ T.J
  π := (Ideal.Quotient.mk T.J).comp (T.red π)
  surj c := by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨1 ⊗ₜ c, congrArg (Ideal.Quotient.mk T.J) (by
      change T.red π _ = c
      rw [Charts.Obj.red_tmul, map_one, map_one, one_mul])⟩
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := (r.obj T).x
  w := by
    refine (congrArg ((r.obj T).x ≫ ·) hs).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ spMap π₀) (r.obj T).w).trans ((Cris.spMap_comp _ _).symm.trans (congrArg spMap ?_))))
    refine RingHom.ext fun d ↦ congrArg (Ideal.Quotient.mk T.J) ?_
    change algebraMap (Hol F.V) T.C (σ (π₀ d)) = T.red π (ι d ⊗ₜ 1)
    rw [Charts.Obj.red_tmul, hι, mul_one, hσ]
    rfl

def Real.tenFunctor : K.Obj ⥤ Thick κ s' where
  obj := r.tenObj π hσ κ hs ι hι hπ
  map {T T'} f :=
    { φ := { (Charts.Hom.ten D f : T.ten D →+* T'.ten D) with commutes' := fun d ↦ (Charts.Hom.ten D f).commutes (ι d) }
      φ₀ := Ideal.quotientMap T'.J (f.φ : T.C →+* T'.C) f.mem
      comm := fun x ↦ congrArg (Ideal.Quotient.mk T'.J) (Charts.Hom.red_ten π f x).symm
      dp := letI := T'.tenRat (D := D); isDPMorphism_of_rat (T.tenδ π) (T'.tenδ π)
        (Charts.Hom.ten D f : T.ten D →+* T'.ten D) fun _ h ↦ Charts.Hom.ten_mem π f h
      pt := r.analyticChartsRealization_comp_point_eq f }
  map_id T := Thick.hom_ext fun b ↦ mp_id (K.Ten D) T b
  map_comp f f' := Thick.hom_ext fun b ↦ mp_comp (K.Ten D) f f' b

def Real.tenCoef : CoefMap ι (O κ s') (K.Ten D) where
  G := r.tenFunctor π hσ κ hs ι hι hπ
  α T := RingHom.id (T.ten D)
  naturality _ _ := rfl
  smul T b c := (Algebra.smul_def (A := T.ten D) (ι b) c).symm

end GlobalTheory.AnPer
