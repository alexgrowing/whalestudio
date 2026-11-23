import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpExt

variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}

theorem isMonHom_prod {G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj H] {I : Type} (T : Finset I)
    (f : I → (G ⟶ H)) (hf : ∀ i, IsMonHom (f i)) : IsMonHom (∏ i ∈ T, f i) :=
  Finset.prod_induction f (fun x => IsMonHom x) (fun x y _ _ => GlobalTheory.Serre.isMonHom_mul x y) GlobalTheory.Serre.isMonHom_one
    fun i _ => hf i

def matEnd (e : Fin 8 → Fin 8 → J) (t : TObj g k J b s) (m : Matrix (Fin 8) (Fin 8) ℤ) : t.A ⟶ t.A :=
  letI := t.ab.comm
  ∏ u, ∏ v, t.act (e u v) ^ m u v

theorem isMonHom_matEnd (e : Fin 8 → Fin 8 → J) (t : TObj g k J b s) (m : Matrix (Fin 8) (Fin 8) ℤ) :
    IsMonHom (matEnd e t m) :=
  letI := t.ab.comm
  isMonHom_prod _ _ fun u => isMonHom_prod _ _ fun v =>
    haveI := t.hom (e u v)
    GlobalTheory.Serre.isMonHom_zpow _ _

def ext (e : Fin 8 → Fin 8 → J) (t : TObj g k J b s) : TObj g k (J ⊕ Matrix (Fin 8) (Fin 8) ℤ) b s :=
  { t with
    act := Sum.elim t.act (matEnd e t)
    hom := fun j => match j with
      | .inl j => t.hom j
      | .inr m => isMonHom_matEnd e t m }

theorem tMap_ext (e : Fin 8 → Fin 8 → J) {t : TObj g k J b s} {t' : TObj g k J b s'} {f : S' ⟶ S}
    (H : TMap t' t f) : TMap (ext e t') (ext e t) f := by
  obtain ⟨φ, h, hL, hpt, hact⟩ := H
  refine ⟨φ, h, hL, hpt, ?_⟩
  rintro (j | m)
  · exact hact j
  · letI := t.ab.comm
    letI := t'.ab.comm
    let U : Over.mk (t'.A.hom ≫ f) ⟶ t.A := Over.homMk φ h.1.w
    have key : pushHom h t'.A (matEnd e t' m) = preHom (G := t.A) U (matEnd e t m) := by
      simp only [matEnd, map_prod, map_zpow]
      refine Finset.prod_congr rfl fun u _ => Finset.prod_congr rfl fun v _ => congrArg (· ^ m u v) ?_
      exact Over.OverMorphism.ext (hact _)
    exact congrArg (fun q => q.left) key

theorem isSharp_ext {h : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ} {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {e : Fin 8 → Fin 8 → J}
    (he : ∀ u v, a (e u v) = Matrix.single u v 1) {t : TObj g k J b s} {c : SiegPre h k (b.ζ : o) s}
    (H : IsSharp W a bas t c) : IsSharp W (Sum.elim a id) bas (ext e t) c := by
  obtain ⟨pr, hmon, huniv, hL, hmat, hpt⟩ := H
  refine ⟨pr, hmon, huniv, hL, ?_, hpt⟩
  have hpr : ∀ u v w, t.act (e u v) ≫ pr w = if w = u then pr v else 1 := by
    intro u v w
    rw [hmat, he, List.prod_ofFn]
    split_ifs with hw
    · subst hw
      rw [Finset.prod_eq_single v] <;> simp +contextual [Matrix.single_apply, eq_comm]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp [Ne.symm hw]
  rintro (j | m) w
  · exact hmat j w
  · letI := t.ab.comm
    haveI := hmon w
    let P : (t.A ⟶ t.A) →* (t.A ⟶ c.A) := MonoidHom.mk' (· ≫ pr w) fun x y => MonObj.mul_comp x y (pr w)
    have hP : ∀ x, P x = x ≫ pr w := fun _ => rfl
    have key : P (matEnd e t m) = (List.ofFn fun v => pr v ^ m w v).prod := by
      simp only [matEnd, map_prod, map_zpow]
      simp only [hP, hpr]
      rw [List.prod_ofFn, Finset.prod_eq_single w]
      · simp
      · intro u _ hu
        simp [Ne.symm hu]
      · simp
    exact key

end GlobalTheory.SharpExt

namespace GlobalTheory

open SharpExt

theorem exists_dense_sharp_all_matrices : ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s), (∀ u v, ∃ j, a j = Matrix.single u v 1) → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ t' : TObj g k (J ⊕ Matrix (Fin 8) (Fin 8) ℤ) b s, Dense (fromSet em (SharpClass (b := b) W (Sum.elim a id) bas em) t') ∧ ∀ c : SiegPre h k (b.ζ : o) s, IsSharp W (Sum.elim a id) bas t' c → IsSharp W a bas t c := by
  intro h g W J a bas k o _ b em S s t he hd
  choose e he using he
  refine ⟨SharpExt.ext e t, hd.mono ?_, ?_⟩
  · rintro p ⟨K, _, x, hp, K₀, _, β, i, j, t₀, tx, tc, h₁, h₂, h₃, h₄, h₅, c, hc, hs⟩
    exact ⟨K, _, x, hp, K₀, _, β, i, j, SharpExt.ext e t₀, SharpExt.ext e tx, SharpExt.ext e tc, h₁, h₂,
      tMap_ext e h₃, tMap_ext e h₄, tMap_ext e h₅, c, hc, isSharp_ext he hs⟩
  · rintro c ⟨pr, hmon, huniv, hL, hmat, hpt⟩
    exact ⟨pr, hmon, huniv, hL, fun j u => hmat (.inl j) u, hpt⟩

end GlobalTheory
end
