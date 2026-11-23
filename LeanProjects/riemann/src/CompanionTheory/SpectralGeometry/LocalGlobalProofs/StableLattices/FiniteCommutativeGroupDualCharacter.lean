import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TrzCob
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.KerPull

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.KerPull.Cartier

section Alg

open scoped TensorProduct
open Coalgebra WithConv

variable (k D : Type) [Field k] [CommRing D] [Bialgebra k D] [Module.Finite k D]

abbrev Du := WithConv (Module.Dual k D)

variable {k D} {R : Type} [CommRing R]

def pair (a : D → R) (β : Du k D → R) : R :=
  ∑ i, a (Module.finBasis k D i) * β (toConv ((Module.finBasis k D).coord i))

variable [Algebra k R]

theorem pair_counit [IsCocomm k D] (β : Du k D →ₐ[k] R) :
    pair (fun d => algebraMap k R (counit (R := k) d)) β = 1 := by
  have h : ∑ i, counit (R := k) (Module.finBasis k D i) • (toConv ((Module.finBasis k D).coord i) : Du k D) = 1 := by
    apply ofConv_injective
    have := (Module.finBasis k D).sum_dual_apply_smul_coord (counit (R := k) (A := D))
    rw [LinearMap.convOne_def]
    refine Eq.trans ?_ (this.trans ?_)
    · ext d; simp
    · ext d; simp
  unfold pair
  rw [← map_one β, ← h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def]

theorem pair_mul [IsCocomm k D] (a a' : D →ₗ[k] R) (β : Du k D →ₐ[k] R) (ψ : D ⊗[k] D →+ R)
    (hψ : ∀ x y, ψ (x ⊗ₜ y) = a x * a' y) (c : D → R) (hc : ∀ d, c d = ψ (comul (R := k) d)) :
    pair c β = pair a β * pair a' β := by
  set b := Module.finBasis k D with hb
  let cc : _ → Du k D := fun i => toConv (b.coord i)
  have hexp : ∀ (f : D →ₗ[k] R) (d : D), f d = ∑ j, b.coord j d • f (b j) := by
    intro f d
    calc f d = f (∑ j, b.repr d j • b j) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, Module.Basis.coord_apply]
  have key1 : ∀ x : D ⊗[k] D, ψ x = ∑ j, ∑ l,
      (LinearMap.mul' k k (TensorProduct.map (b.coord j) (b.coord l) x)) • (a (b j) * a' (b l)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
      rw [hψ, hexp a u, hexp a' v, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, Algebra.smul_def, map_mul]
      ring
    | add x y hx hy =>
      simp only [map_add, add_smul, Finset.sum_add_distrib, hx, hy]
  have key2 : ∀ j l, β (cc j) * β (cc l) = ∑ i,
      (LinearMap.mul' k k (TensorProduct.map (b.coord j) (b.coord l) (comul (R := k) (b i)))) • β (cc i) := by
    intro j l
    rw [← map_mul]
    have h := b.sum_dual_apply_smul_coord (cc j * cc l).ofConv
    have h' : cc j * cc l = ∑ i, (cc j * cc l).ofConv (b i) • cc i := by
      apply ofConv_injective
      refine h.symm.trans ?_
      ext d; simp [cc]
    rw [h', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 1
  unfold pair
  simp only [← hb]
  rw [Finset.sum_mul_sum]
  simp only [hc, key1, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have := key2 j l
  simp only [cc] at this
  calc _ = (a (b j) * a' (b l)) * ∑ i, (LinearMap.mul' k k (TensorProduct.map (b.coord j) (b.coord l) (comul (R := k) (b i)))) • β (toConv (b.coord i)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Algebra.smul_def]; ring
    _ = _ := by rw [← this]; ring

end Alg

section Sch

open scoped TensorProduct
open Coalgebra WithConv

def fnR {X : Scheme.{0}} {A : Type} [CommRing A] (x : X ⟶ Spec (.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ x.appTop).hom

theorem fnR_comp {X Y : Scheme.{0}} {A : Type} [CommRing A] (f : Y ⟶ X) (x : X ⟶ Spec (.of A)) (a : A) :
    fnR (f ≫ x) a = f.appTop (fnR x a) := by
  rw [fnR, fnR, Scheme.Hom.comp_appTop]
  rfl

theorem fnR_specMap {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (x : X ⟶ Spec (.of B)) (a : A) :
    fnR (x ≫ Spec.map (CommRingCat.ofHom φ)) a = fnR x (φ a) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have h2 := congr($h a)
  simp only [fnR, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h2 ⊢
  simp only [CommRingCat.hom_ofHom] at h2
  rw [h2]

variable {k : Type} [Field k]

@[reducible] def wAlg (W : Over (Sp k)) : Algebra k Γ(W.left, ⊤) := (fnR W.hom).toAlgebra

theorem fnR_algebraMap {W : Over (Sp k)} {A : Type} [CommRing A] [Algebra k A]
    (x : W ⟶ (Spec (.of A)).asOver (Spec (.of k))) (c : k) :
    fnR x.left (algebraMap k A c) = fnR W.hom c := by
  have h : x.left ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = W.hom := Over.w x
  exact (fnR_specMap (algebraMap k A) x.left c).symm.trans (congrArg (fun y => fnR y c) h)

def ptr {W : Over (Sp k)} {A : Type} [CommRing A] [Algebra k A]
    (x : W ⟶ (Spec (.of A)).asOver (Spec (.of k))) :
    letI := wAlg W
    A →ₐ[k] Γ(W.left, ⊤) :=
  letI := wAlg W
  { fnR x.left with
    commutes' := fun c => by
      exact fnR_algebraMap x c }

variable {D : Type} [CommRing D] [HopfAlgebra k D]

theorem fn_mul {W : Over (Sp k)} (x y : W ⟶ (Spec (.of D)).asOver (Spec (.of k))) :
    ∃ ψ : D ⊗[k] D →+ Γ(W.left, ⊤), (∀ u v, ψ (u ⊗ₜ v) = fnR x.left u * fnR y.left v) ∧
      ∀ d, fnR (x * y).left d = ψ (comul (R := k) d) := by
  let L : W.left ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap k D))) (Spec.map (CommRingCat.ofHom (algebraMap k D))) :=
    (lift x y).left
  let M : W.left ⟶ Spec (.of (D ⊗[k] D)) := L ≫ (pullbackSpecIso k D D).hom
  have hf : L ≫ pullback.fst _ _ = x.left := by
    have := congrArg Over.Hom.left (lift_fst x y)
    rw [Over.comp_left, Over.fst_left] at this
    exact this
  have hs : L ≫ pullback.snd _ _ = y.left := by
    have := congrArg Over.Hom.left (lift_snd x y)
    rw [Over.comp_left, Over.snd_left] at this
    exact this
  have h1 : M ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = x.left :=
    (Category.assoc _ _ _).trans ((congrArg (fun z => L ≫ z) (pullbackSpecIso_hom_fst k D D)).trans hf)
  have h2 : M ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : D →ₐ[k] D ⊗[k] D).toRingHom) = y.left :=
    (Category.assoc _ _ _).trans ((congrArg (fun z => L ≫ z) (pullbackSpecIso_hom_snd k D D)).trans hs)
  refine ⟨(fnR M).toAddMonoidHom, fun u v => ?_, fun d => ?_⟩
  · have e : u ⊗ₜ[k] v = Algebra.TensorProduct.includeLeftRingHom u *
        (Algebra.TensorProduct.includeRight : D →ₐ[k] D ⊗[k] D).toRingHom v := by simp
    show fnR M _ = _
    rw [e, map_mul, ← fnR_specMap, ← fnR_specMap, h1, h2]
  · have hμ : (x * y).left = M ≫ Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom k D).toRingHom) := by
      rw [Hom.mul_def, Over.comp_left, mul_spec_asOver_spec_left (R := .of k) (A := .of D)]
      simp only [M, L]
      rfl
    rw [hμ, fnR_specMap]
    rfl

theorem fn_one {W : Over (Sp k)} (d : D) :
    fnR (1 : W ⟶ (Spec (.of D)).asOver (Spec (.of k))).left d = fnR W.hom (counit (R := k) d) := by
  have h : (1 : W ⟶ (Spec (.of D)).asOver (Spec (.of k))).left =
      W.hom ≫ Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom k D).toRingHom) := by
    rw [Hom.one_def, Over.comp_left, one_spec_asOver_spec_left (R := .of k) (A := .of D)]
    rfl
  rw [h, fnR_specMap]
  rfl

end Sch

section Aff

open scoped TensorProduct
open Coalgebra WithConv

variable (k D : Type) [Field k] [CommRing D] [HopfAlgebra k D]

abbrev GD : Over (Sp k) := (Spec (.of D)).asOver (Spec (.of k))

variable [Module.Finite k D] [IsCocomm k D]

abbrev TE : Over (Sp k) := (Spec (.of (Du k D))).asOver (Spec (.of k))

variable {k D}

def P {W : Over (Sp k)} (x : W ⟶ GD k D) (t : W ⟶ TE k D) : Γ(W.left, ⊤) :=
  pair (fnR x.left) (fnR t.left)

theorem twoPow_mul_twoPow {W : Over (Sp k)} (x y : W ⟶ GD k D) (t : W ⟶ TE k D) :
    P (x * y) t = P x t * P y t := by
  obtain ⟨ψ, h1, h2⟩ := fn_mul x y
  letI := wAlg W
  exact pair_mul (ptr x).toLinearMap (ptr y).toLinearMap (ptr t) ψ h1 _ h2

theorem P_one {W : Over (Sp k)} (t : W ⟶ TE k D) : P (1 : W ⟶ GD k D) t = 1 := by
  letI := wAlg W
  have h : (fnR (1 : W ⟶ GD k D).left : D → Γ(W.left, ⊤)) =
      fun d => algebraMap k Γ(W.left, ⊤) (counit (R := k) d) := by
    funext d
    exact fn_one d
  unfold P
  rw [h]
  exact pair_counit (ptr t)

theorem pullback_comp₂ {W W' : Over (Sp k)} (f : W' ⟶ W) (x : W ⟶ GD k D) (t : W ⟶ TE k D) :
    f.left.appTop (P x t) = P (f ≫ x) (f ≫ t) := by
  simp only [P, pair, map_sum, map_mul, Over.comp_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg₂ (· * ·) (fnR_comp f.left x.left _).symm (fnR_comp f.left t.left _).symm

def chi : Γ((GD k D ⊗ TE k D).left, ⊤) := P (fst _ _) (snd _ _)

def chiU : Γ((GD k D ⊗ TE k D).left, ⊤)ˣ where
  val := chi
  inv := P (fst _ _)⁻¹ (snd _ _)
  val_inv := by rw [chi, ← twoPow_mul_twoPow, mul_inv_cancel, P_one]
  inv_val := by rw [chi, ← twoPow_mul_twoPow, inv_mul_cancel, P_one]

end Aff

section Main

open scoped TensorProduct
open Coalgebra WithConv

variable {k : Type} [Field k]

end Main

end GlobalTheory.CompanionTheory.KerPull.Cartier
