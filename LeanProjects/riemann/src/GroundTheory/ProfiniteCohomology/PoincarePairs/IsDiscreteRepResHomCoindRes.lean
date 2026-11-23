import Mathlib
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.CompactCupEqCompactCupRight
import GroundTheory.ProfiniteCohomology.MackeyFormula.CompactSupport
import GroundTheory.ProfiniteCohomology.PoincareDuality.NsmulEqZeroOfNonemptyAddEquiv
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

attribute [local instance 2000] Rep.hV2

section Eval

variable {k G : Type u} [CommRing k] [Group G]

def dualEvalPairing (D M : Rep.{u} k G) : dualRep D M ⊗ M ⟶ D :=
  (β_ (dualRep D M) M).hom ≫ evalPairing D M

@[simp]
theorem dualEvalPairing_tmul (D M : Rep.{u} k G) (f : M →ₗ[k] D) (m : M) :
    (dualEvalPairing D M).hom ((f : dualRep D M) ⊗ₜ[k] m : (dualRep D M ⊗ M : Rep k G)) = f m :=
  rfl

variable {H : Type u} [Group H]

theorem resFunctor_map_comp_id (ψ : H →* G) {A B C : Rep.{u} k G} (μ : A ⊗ B ⟶ C) :
    (Rep.resFunctor ψ).map μ ≫ 𝟙 _ =
      resTensorHom ψ (𝟙 (Rep.res ψ A)) (𝟙 (Rep.res ψ B)) ≫ (Rep.resFunctor ψ).map μ := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Eval

section CupRes

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

noncomputable def compactCupRes {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    [IsDiscreteRep C] (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) :
    compactCohomologyRes φ A r →ₗ[k] cohomology B s →ₗ[k] compactCohomologyRes φ C n :=
  compactCup φ μ (fun v => (Rep.resFunctor (φ v).toMonoidHom).map μ)
    (fun v => resFunctor_map_comp_id (φ v).toMonoidHom μ) h

def compactDualityMap (D : Rep.{u} k G) [IsDiscreteRep D] {n m r s : ℕ} (h : r + s = m)
    (t : compactCohomologyRes φ D m →+ ZMod n) (M : Rep.{u} k G) [IsDiscreteRep M]
    [IsDiscreteRep (dualRep D M)] :
    cohomology M r →+ (compactCohomologyRes φ (dualRep D M) s →+ ZMod n) where
  toFun x := t.comp ((bilinAddHom (compactCupRes φ (dualEvalPairing D M)
    ((Nat.add_comm s r).trans h))).flip x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem compactDualityMap_apply (D : Rep.{u} k G) [IsDiscreteRep D] {n m r s : ℕ} (h : r + s = m)
    (t : compactCohomologyRes φ D m →+ ZMod n) (M : Rep.{u} k G) [IsDiscreteRep M]
    [IsDiscreteRep (dualRep D M)] (x : cohomology M r)
    (y : compactCohomologyRes φ (dualRep D M) s) :
    compactDualityMap φ D h t M x y =
      t (compactCupRes φ (dualEvalPairing D M) ((Nat.add_comm s r).trans h) y x) :=
  rfl

end CupRes

section Cores

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)]
  [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)]
  (φ : ∀ v, Hv v →ₜ* G)

omit [∀ v, CompactSpace (Hv v)] in

instance isDiscreteRep_resHom_coind_res {K : Type u} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] (ψ : K →ₜ* G) (V : OpenSubgroup G) (A : Rep.{u} k G)
    [IsDiscreteRep A] :
    IsDiscreteRep (Rep.res ψ.toMonoidHom
      (Rep.coind (V : Subgroup G).subtype (Rep.res (V : Subgroup G).subtype A))) :=
  isDiscreteRep_res_coind V ψ _

noncomputable def compactCores (V : OpenSubgroup G) (A : Rep.{u} k G) [IsDiscreteRep A] (n : ℕ) :
    compactCohomologyRes (mackeyFamily V φ) (Rep.res (V : Subgroup G).subtype A) n ⟶
      compactCohomologyRes φ A n :=
  (mackeyCompactCohomologyIso V φ (Rep.res (V : Subgroup G).subtype A) n).inv ≫
    compactCohomologyMap φ (Aᵥ := fun v => Rep.res (φ v).toMonoidHom
        (Rep.coind (V : Subgroup G).subtype (Rep.res (V : Subgroup G).subtype A)))
      (Bᵥ := fun v => Rep.res (φ v).toMonoidHom A) (coindTrace (V : Subgroup G) A)
      (fun v => (Rep.resFunctor (φ v).toMonoidHom).map (coindTrace (V : Subgroup G) A))
      (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) n

end Cores

section Hypotheses

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

def zmodMulPairingRight (n : ℕ) {K : Type u} [Group K] (D : Rep.{u} (ULift.{u} ℤ) K)
    (hD : ∀ d : D, n • d = 0) : D ⊗ zmodRep.{u} K n ⟶ D :=
  (β_ D (zmodRep.{u} K n)).hom ≫ zmodMulPairing n D hD

def zmodCompactDualityMap (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D] {n : ℕ}
    (hD : ∀ d : D, n • d = 0) (U : OpenSubgroup G) {m r s : ℕ} (h : r + s = m)
    (t : compactCohomologyRes φ D m →+ ZMod n) :
    cohomology (zmodRep.{u} (U : Subgroup G) n) r →+
      (compactCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) s →+ ZMod n)
    where
  toFun x := (t.comp (compactCores φ U D m).hom.toAddMonoidHom).comp
    ((bilinAddHom (compactCupRes (mackeyFamily U φ)
      (zmodMulPairingRight n (Rep.res (U : Subgroup G).subtype D) hD)
      ((Nat.add_comm s r).trans h))).flip x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem zmodCompactDualityMap_apply (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D] {n : ℕ}
    (hD : ∀ d : D, n • d = 0) (U : OpenSubgroup G) {m r s : ℕ} (h : r + s = m)
    (t : compactCohomologyRes φ D m →+ ZMod n) (x : cohomology (zmodRep.{u} (U : Subgroup G) n) r)
    (y : compactCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) s) :
    zmodCompactDualityMap φ D hD U h t x y =
      t ((compactCores φ U D m).hom (compactCupRes (mackeyFamily U φ)
        (zmodMulPairingRight n (Rep.res (U : Subgroup G).subtype D) hD)
        ((Nat.add_comm s r).trans h) y x)) :=
  rfl

structure CompactDualityHypotheses (n : ℕ) (D : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep D]
    (t : compactCohomologyRes φ D 3 →+ ZMod n) (U₀ : OpenSubgroup G) : Prop where

  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)

  subsingleton_four : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (compactCohomologyRes φ M 4)

  bijective_base : ∀ (U : OpenSubgroup G), U ≤ U₀ → ∀ {r s : ℕ} (h : r + s = 3),
    Function.Bijective (zmodCompactDualityMap φ D
      (nsmul_eq_zero_of_nonempty_addEquiv nonempty_addEquiv) U h t)

end Hypotheses

end GroundTheory.ProfCoh
