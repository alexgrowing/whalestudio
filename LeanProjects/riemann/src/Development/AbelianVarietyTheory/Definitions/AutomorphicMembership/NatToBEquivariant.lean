import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicColimitOfIsNilpotent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ApolarMonomial

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.EigenSplit GlobalTheory.DeRham GlobalTheory.Cris
open Formalism.MainNotions.DIV.Cons (SCF intO)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

theorem isKernel_pull {S S' : Scheme.{0}} (f : S' ⟶ S) {K G B : Over S} [GrpObj B] {i : K ⟶ G} {q : G ⟶ B}
    (h : IsPullback i (toUnit K) q η[B]) :
    IsPullback ((Over.pullback f).map i) (toUnit _) ((Over.pullback f).map q) η[(Over.pullback f).obj B] := by
  have h' := h.map (Over.pullback f)
  have e : (Over.pullback f).map (toUnit K) = toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback f) :=
    (cancel_mono (Functor.OplaxMonoidal.η (Over.pullback f))).1 (toUnit_unique _ _)
  refine Diag.isPullback_toUnit_of_lift _ (h'.w.trans (by rw [e, Category.assoc]; rfl))
    (fun {T} a b k => h'.hom_ext k ((cancel_mono (Functor.OplaxMonoidal.η (Over.pullback f))).1 (toUnit_unique _ _)))
    fun {T} t ht => ⟨h'.lift t (toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback f))
      (ht.trans (Category.assoc _ _ _).symm), h'.lift_fst _ _ _⟩

theorem eigMap_exact {R S O : Type} [CommRing R] [CommRing S] [CommRing O] (f : R →+* S) {K G B : Over (Sp R)}
    [GrpObj K] [IsCommMonObj K] [GrpObj G] [IsCommMonObj G] [GrpObj B] [IsCommMonObj B] {c : OAct O K} {a : OAct O G}
    {b : OAct O B} {i : K ⟶ G} {q : G ⟶ B} (hi : IsLinearHom c a i) (hq : IsLinearHom a b q)
    (h : IsPullback i (toUnit K) q η[B]) (σ : O →+* S) :
    Function.Injective (eigMap f hi σ) ∧ Function.Exact (eigMap f hi σ) (eigMap f hq σ) := by
  haveI := hi.isMonHom
  haveI := hq.isMonHom
  obtain ⟨h₁, h₂⟩ : Function.Injective (lieMap f hi) ∧ Function.Exact (lieMap f hi) (lieMap f hq) :=
    Lie.map_kernel (isKernel_pull (spMap f) h)
  refine ⟨fun x y e => Subtype.ext (h₁ (congrArg Subtype.val e)), fun v => ⟨fun e => ?_, ?_⟩⟩
  · obtain ⟨w, hw⟩ := (h₂ v.1).1 (congrArg Subtype.val e)
    refine ⟨⟨w, fun x => h₁ ?_⟩, Subtype.ext hw⟩
    rw [lieMap_act, LinearMap.map_smul, hw]
    exact v.2 x
  · rintro ⟨w, rfl⟩
    exact Subtype.ext ((h₂ _).2 ⟨w.1, rfl⟩)

section Contr

variable {O C Λ J : Type} [CommRing O] [Field C] [Algebra O C] [CommRing Λ] [DecidableEq J] {σ : J → Λ →+* C}
  (h : IsSplitting σ) {M M' : Type*} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']

def eigDefect (ρ : Λ →+* Module.End O M) (i : J) (x : M) : C ⊗[O] M :=
  proj h (baseChangeAction C ρ) i (1 ⊗ₜ x) - 1 ⊗ₜ x

def contr (ρ : Λ →+* Module.End O M) (ψ : LinearMap.BilinForm O M) (i : J) (x x' : M) : C :=
  ψ.baseChange C (eigDefect h ρ i x) (1 ⊗ₜ x')

theorem eigDefect_map {ρ : Λ →+* Module.End O M} {ρ' : Λ →+* Module.End O M'} {f : M →ₗ[O] M'}
    (hf : IsEquivariant ρ ρ' f) (i : J) (x : M) :
    f.baseChange C (eigDefect h ρ i x) = eigDefect h ρ' i (f x) := by
  have e : IsEquivariant (baseChangeAction C ρ) (baseChangeAction C ρ') (f.baseChange C) := fun a z => by
    induction z with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul c m => exact congrArg (c ⊗ₜ[O] ·) (hf a m)
  rw [eigDefect, map_sub, e.proj h]
  rfl

theorem contr_comp {ρ : Λ →+* Module.End O M} {ρ' : Λ →+* Module.End O M'} {f : M →ₗ[O] M'}
    (hf : IsEquivariant ρ ρ' f) (ψ : LinearMap.BilinForm O M') (i : J) (x x' : M) :
    contr h ρ (ψ.compl₁₂ f f) i x x' = contr h ρ' ψ i (f x) (f x') := by
  rw [contr, contr, ← eigDefect_map h hf]
  induction eigDefect h ρ i x with
  | zero => simp
  | add z w hz hw => simp only [map_add, LinearMap.add_apply, hz, hw]
  | tmul c m => simp [LinearMap.BilinForm.baseChange_tmul]

theorem contr_of_eigen {ρ : Λ →+* Module.End O M} (ψ : LinearMap.BilinForm O M) (i : J) {x : M}
    (hx : (1 : C) ⊗ₜ[O] x ∈ eigenSub (baseChangeAction C ρ) (σ i)) (x' : M) : contr h ρ ψ i x x' = 0 := by
  rw [contr, eigDefect, proj_of_mem h hx, sub_self, map_zero, LinearMap.zero_apply]

example {ρ : Λ →+* Module.End O M} (ψ : LinearMap.BilinForm O M) {i j : J} (hij : j ≠ i) {x : M}
    (hx : (1 : C) ⊗ₜ[O] x ∈ eigenSub (baseChangeAction C ρ) (σ j)) (x' : M) :
    contr h ρ ψ i x x' = -algebraMap O C (ψ x x') := by
  rw [contr, eigDefect, proj_of_mem_ne h hij hx, zero_sub, map_neg, LinearMap.neg_apply,
    LinearMap.BilinForm.baseChange_tmul, _root_.mul_one, Algebra.algebraMap_eq_smul_one]

end Contr

section Nat

variable {O Λ : Type} [CommRing O] [CommRing Λ] {G B : Over (Sp O)} [GrpObj G] [IsCommMonObj G] [GrpObj B]
  [IsCommMonObj B] {a : OAct Λ G} {b : OAct Λ B}

variable (b) in

structure PolSplit (L : LB B.left) : Type 1 where

  ψ : LinearMap.BilinForm O (HdR B)
  pol : IsPolForm (dp0 O) (𝟙 _) B L ψ

  s : Lie b →ₗ[O] HdR B
  lift : ∀ v, IsLieImage (s v) v.hom
  lag : ∀ v w, ψ (s v) (s w) = 0

variable {q : G ⟶ B} (hq : IsLinearHom a b q)

def NatLie (_hq : IsLinearHom a b q) : Submodule O (Lie a × HdR B) where
  carrier := {z | IsLieImage z.2 (z.1.hom ≫ q)}
  add_mem' {z w} hz hw := by
    haveI := _hq.isMonHom
    have := IsLieImage.add hz hw
    rwa [← MonObj.mul_comp] at this
  zero_mem' := by
    haveI := _hq.isMonHom
    change IsLieImage 0 ((1 : epsR O ⟶ G) ≫ q)
    rw [MonObj.one_comp]
    exact isLieImage_one_iff.2 (zero_mem _)
  smul_mem' r z hz := by
    have := IsLieImage.smul hz r
    rwa [← Category.assoc] at this

def natToB : NatLie hq →ₗ[O] HdR B := LinearMap.snd O _ _ ∘ₗ (NatLie hq).subtype

def natToLie : NatLie hq →ₗ[O] Lie a := LinearMap.fst O _ _ ∘ₗ (NatLie hq).subtype

def natEnd (c : Λ) : Module.End O (NatLie hq) :=
  ((DistribSMul.toLinearMap O (Lie a) c).prodMap (DeRham.act (dp0 O) (𝟙 _) b c)).restrict fun z hz => by
    haveI := b.hom c
    have := IsLieImage.push hz (b.act c)
    rwa [Category.assoc, ← hq.comm, ← Category.assoc] at this

def natAct : Λ →+* Module.End O (NatLie hq) where
  toFun := natEnd hq
  map_one' := LinearMap.ext fun z => Subtype.ext (Prod.ext (one_smul Λ z.1.1)
    (LinearMap.congr_fun (map_one (DeRham.act (dp0 O) (𝟙 _) b)) z.1.2))
  map_mul' c c' := LinearMap.ext fun z => Subtype.ext (Prod.ext (mul_smul c c' z.1.1)
    (LinearMap.congr_fun (map_mul (DeRham.act (dp0 O) (𝟙 _) b) c c') z.1.2))
  map_zero' := LinearMap.ext fun z => Subtype.ext (Prod.ext (zero_smul Λ z.1.1)
    (LinearMap.congr_fun (map_zero (DeRham.act (dp0 O) (𝟙 _) b)) z.1.2))
  map_add' c c' := LinearMap.ext fun z => Subtype.ext (Prod.ext (add_smul c c' z.1.1)
    (LinearMap.congr_fun (map_add (DeRham.act (dp0 O) (𝟙 _) b) c c') z.1.2))

theorem natToB_equivariant : IsEquivariant (natAct hq) (DeRham.act (dp0 O) (𝟙 _) b) (natToB hq) := fun _ _ => rfl

variable {L : LB B.left} (sp : PolSplit b L)

def natForm : LinearMap.BilinForm O (NatLie hq) := sp.ψ.compl₁₂ (natToB hq) (natToB hq)

def natLift (v : Lie a) : NatLie hq :=
  ⟨(v, sp.s (Lie.mapLinear hq v)), sp.lift (Lie.mapLinear hq v)⟩

theorem natToLie_natLift (v : Lie a) : natToLie hq (natLift hq sp v) = v := rfl

variable {C J : Type} [Field C] [Algebra O C] [DecidableEq J] {σ : J → Λ →+* C} (h : IsSplitting σ)

def kapAb (i : J) (u u' : Lie b) : C := contr h (DeRham.act (dp0 O) (𝟙 _) b) sp.ψ i (sp.s u) (sp.s u')

def kapExt (i : J) (u u' : Lie a) : C :=
  contr h (natAct hq) (natForm hq sp) i (natLift hq sp u) (natLift hq sp u')

theorem kapExt_eq (i : J) (u u' : Lie a) :
    kapExt hq sp h i u u' = kapAb sp h i (Lie.mapLinear hq u) (Lie.mapLinear hq u') :=
  contr_comp h (natToB_equivariant hq) _ i _ _

example (b : OAct Λ (𝟙_ (Over (Sp O)))) (L : LB (𝟙_ (Over (Sp O))).left) (hL : ∀ i j, L.g i j = 1) :
    Nonempty (PolSplit b L) :=
  ⟨⟨0, isPolForm_zero L hL, 0, fun v => toUnit_unique 1 v.hom ▸ isLieImage_one_iff.2 (zero_mem _), fun _ _ => rfl⟩⟩

end Nat

end GlobalTheory.RayEv
