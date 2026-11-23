import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AutomorphicArithmetic.CommutativeAlgebra.AcyclicSpecFiniteAlgebraStrictHenselian
import Development.AutomorphicArithmetic.CommutativeAlgebra.TwistCohomologyCommutesWithFilteredColimits

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.IntegralColim

variable (O R : Type) [CommRing O] [CommRing R] [Algebra O R]

private abbrev FJ : Type := {S : Subalgebra O R // Module.Finite O S}

private noncomputable def FD : FJ O R ⥤ CommRingCat.{0} where
  obj S := CommRingCat.of S.1
  map {S T} f := CommRingCat.ofHom (Subalgebra.inclusion (show S.1 ≤ T.1 from leOfHom f)).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private noncomputable def FC : Cocone (FD O R) where
  pt := CommRingCat.of R
  ι :=
    { app := fun S => CommRingCat.ofHom S.1.val.toRingHom
      naturality := fun _ _ _ => by ext; rfl }

variable {O R}

private theorem finite_sup (S T : FJ O R) : Module.Finite O ↥(S.1 ⊔ T.1) := by
  haveI := S.2
  haveI := T.2
  exact Subalgebra.finite_sup S.1 T.1

private instance : IsDirected (FJ O R) (· ≤ ·) :=
  ⟨fun S T => ⟨⟨S.1 ⊔ T.1, finite_sup S T⟩, le_sup_left (a := S.1), le_sup_right (a := S.1)⟩⟩

variable [Algebra.IsIntegral O R]

private theorem finite_adjoin (x : R) : Module.Finite O ↥(Algebra.adjoin O ({x} : Set R)) :=
  Module.Finite.iff_fg.mpr (IsIntegral.fg_adjoin_singleton (Algebra.IsIntegral.isIntegral x))

private noncomputable def gen (x : R) : FJ O R := ⟨Algebra.adjoin O {x}, finite_adjoin x⟩

private theorem mem_gen (x : R) : x ∈ (gen (O := O) x).1 := Algebra.subset_adjoin rfl

private instance : Nonempty (FJ O R) := ⟨gen 0⟩

private instance : IsFiltered (FJ O R) := inferInstance

private noncomputable def descFun (s : Cocone (FD O R)) (x : R) : s.pt :=
  (s.ι.app (gen x)).hom (⟨x, mem_gen x⟩ : (gen (O := O) x).1)

private theorem descFun_eq (s : Cocone (FD O R)) (S : FJ O R) (x : R) (hx : x ∈ S.1) :
    (s.ι.app S).hom (⟨x, hx⟩ : S.1) = descFun s x := by
  let U : FJ O R := ⟨S.1 ⊔ (gen x).1, finite_sup S (gen x)⟩
  have hS : S ≤ U := le_sup_left (a := S.1)
  have hG : gen x ≤ U := le_sup_right (a := S.1)
  unfold descFun
  rw [← s.w (homOfLE hS), ← s.w (homOfLE hG)]
  rfl

end UpperTheory.IntegralColim

namespace UpperTheory.IntegralColim
variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] [Algebra.IsIntegral O R]

private theorem two (x y : R) : ∃ S : FJ O R, x ∈ S.1 ∧ y ∈ S.1 :=
  ⟨⟨(gen (O := O) x).1 ⊔ (gen (O := O) y).1, finite_sup _ _⟩,
    (le_sup_left : (gen (O := O) x).1 ≤ _) (mem_gen x),
    (le_sup_right : (gen (O := O) y).1 ≤ _) (mem_gen y)⟩

private noncomputable def descHom (s : Cocone (FD O R)) : R →+* s.pt where
  toFun := descFun s
  map_one' := by
    have h := descFun_eq s (gen 1) 1 (one_mem _)
    rw [← h]
    exact map_one (s.ι.app (gen (O := O) (1 : R))).hom
  map_zero' := by
    have h := descFun_eq s (gen 0) 0 (zero_mem _)
    rw [← h]
    exact map_zero (s.ι.app (gen (O := O) (0 : R))).hom
  map_mul' x y := by
    obtain ⟨S, hx, hy⟩ := two (O := O) x y
    rw [← descFun_eq s S x hx, ← descFun_eq s S y hy, ← descFun_eq s S (x * y) (mul_mem hx hy)]
    exact map_mul (s.ι.app S).hom (⟨x, hx⟩ : S.1) (⟨y, hy⟩ : S.1)
  map_add' x y := by
    obtain ⟨S, hx, hy⟩ := two (O := O) x y
    rw [← descFun_eq s S x hx, ← descFun_eq s S y hy, ← descFun_eq s S (x + y) (add_mem hx hy)]
    exact map_add (s.ι.app S).hom (⟨x, hx⟩ : S.1) (⟨y, hy⟩ : S.1)

private noncomputable def isColim : IsColimit (FC O R) where
  desc s := CommRingCat.ofHom (descHom s)
  fac s S := by
    ext ⟨x, hx⟩
    exact (descFun_eq s S x hx).symm
  uniq s m hm := by
    refine CommRingCat.hom_ext (RingHom.ext fun (x : R) => ?_)
    have h := congrArg (fun f => f.hom (⟨x, mem_gen x⟩ : (gen (O := O) x).1)) (hm (gen x))
    exact h

end UpperTheory.IntegralColim

theorem UpperTheory.acyclic_spec_integral_algebra_strictHenselian :
    ∀ (q : ℕ) (O R : Type) [CommRing O] [CommRing R] [Algebra O R] [Algebra.IsIntegral O R], SH O → IsUnit (q : O) → Acyc q (sp R) := by
  intro q O R _ _ _ _ hO hq n i hn
  have hqR : IsUnit (q : R) := by
    simpa using hq.map (algebraMap O R)
  have hz : ∀ x : Ht q (sp R) n i, x = 0 := by
    intro x
    obtain ⟨j, y, hy⟩ := (UpperTheory.twistCohomology_commutes_with_filtered_colimits q (UpperTheory.IntegralColim.FD O R) (UpperTheory.IntegralColim.FC O R)
      UpperTheory.IntegralColim.isColim n i).1 x hqR
    haveI := j.2
    have hA : Acyc q (sp j.1) := UpperTheory.acyclic_spec_finite_algebra_strictHenselian q O j.1 hO hq
    haveI := hA n i hn
    have hy0 : y = 0 := Subsingleton.elim (α := Ht q (sp j.1) n i) y 0
    rw [← hy, hy0]
    exact map_zero _
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩
