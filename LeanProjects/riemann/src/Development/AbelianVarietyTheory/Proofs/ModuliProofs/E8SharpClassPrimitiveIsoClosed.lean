import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerIntegerMatrixPrimitiveAdjoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SharpPrim

theorem matrix_identities {n : Type} [Fintype n] [DecidableEq n] {W m m' : Matrix n n ℤ}
    (hd : (W + W.transpose).det = 1) (h : (W + W.transpose) * m = W) (h' : (W + W.transpose) * m' = W.transpose) :
    m + m' = 1 ∧ m.transpose * (W + W.transpose) = (W + W.transpose) * m' := by
  set G := W + W.transpose with hG
  have hu : IsUnit G.det := by rw [hd]; exact isUnit_one
  have hT : G.transpose = G := by
    rw [hG, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  constructor
  · have key : G * (m + m') = G := by rw [Matrix.mul_add, h, h']
    calc m + m' = G⁻¹ * (G * (m + m')) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hu, Matrix.one_mul]
      _ = 1 := by rw [key, Matrix.nonsing_inv_mul G hu]
  · have ht := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, hT] at ht
    rw [ht, h']

theorem prod_mul_prod {M : Type} [CommGroup M] {n : ℕ} (x : Fin n → M) {m m' : Matrix (Fin n) (Fin n) ℤ}
    (h : m + m' = 1) (u : Fin n) :
    (List.ofFn fun v => x v ^ m u v).prod * (List.ofFn fun v => x v ^ m' u v).prod = x u := by
  have hm : ∀ v, m u v + m' u v = if u = v then 1 else 0 := by
    intro v
    have e := congrFun (congrFun h u) v
    rwa [Matrix.add_apply, Matrix.one_apply] at e
  rw [List.prod_ofFn, List.prod_ofFn, ← Finset.prod_mul_distrib]
  simp_rw [← zpow_add, hm]
  rw [Finset.prod_eq_single u (fun v _ hv => by rw [if_neg (Ne.symm hv), zpow_zero])
    (fun hu => absurd (Finset.mem_univ u) hu), if_pos rfl, zpow_one]

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k h : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

theorem isSharp_of_tmap {W : Matrix (Fin 8) (Fin 8) ℤ} {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {t t' : TObj g k J b s}
    {c : SiegPre h k (b.ζ : o) s} (H : IsSharp W a bas t c) (m : TMap t' t (𝟙 _)) : IsSharp W a bas t' c := by
  obtain ⟨φ, hpb, hLφ, hpt, hact⟩ := m
  obtain ⟨pr, hpr, huniv, hL, hpa, hlev⟩ := H
  have : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 t.A))
  obtain ⟨e, he, heφ'⟩ := grpPullback_iso hpb (isGrpPullback_of_iso (Iso.refl t.A))
  have heφ : e.hom.left = φ := by simpa using heφ'
  have hcomm : ∀ j, t'.act j ≫ e.hom = e.hom ≫ t.act j := by
    intro j
    ext
    simp only [Over.comp_left, heφ, hact j]
  refine ⟨fun u => e.hom ≫ pr u, fun u => ?_, fun T y => ?_, ?_, fun j u => ?_, fun i u => ?_⟩
  · have := hpr u
    infer_instance
  · obtain ⟨x0, hx0, hu0⟩ := huniv T y
    refine ⟨x0 ≫ e.inv, fun u => by simpa using hx0 u, fun x hx => ?_⟩
    have hx' : x ≫ e.hom = x0 := hu0 _ fun u => by simpa using hx u
    rw [← hx']
    simp
  · have hfun : (fun uv : Fin 8 × Fin 8 => (lift (e.hom ≫ pr uv.1) (e.hom ≫ pr uv.2)).left) =
        fun uv => φ ≫ (lift (pr uv.1) (pr uv.2)).left := by
      funext uv
      rw [← comp_lift, Over.comp_left, heφ]
    rw [hfun]
    refine (CechPic.cls_eq_iff t'.isLB (LB.isLB_linComb c.isLB _ _)).1 ?_
    rw [(CechPic.cls_eq_iff t'.isLB (pull_isLB t.isLB φ)).2 hLφ, CechPic.cls_pull t.isLB,
      (CechPic.cls_eq_iff t.isLB (LB.isLB_linComb c.isLB _ _)).2 hL,
      CechPic.cls_linComb c.isLB, CechPic.cls_linComb c.isLB, map_sum]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul, ← CechPic.pull_comp]
  · rw [← Category.assoc, hcomm j, Category.assoc, hpa j u, PowerAdjoint.comp_prod_zpow]
  · have hp := hpt i
    rw [Category.id_comp] at hp
    rw [← hlev i u, Over.comp_left, Over.comp_left, heφ, ← Category.assoc, hp, Over.comp_left]

end GlobalTheory.SharpPrim

theorem GlobalTheory.sharpClass_prim_and_iso : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (t : TObj g k J b (spMap em)), SharpClass W a bas em t → (IsE8 W → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → t.Prim w w') ∧ ∀ t' : TObj g k J b (spMap em), TMap t' t (𝟙 _) → SharpClass W a bas em t' := by
  intro hΘ o _ g k J b em w w' h W a bas t ht
  obtain ⟨c, hc, hs⟩ := ht
  refine ⟨fun hE hw hw' => ?_, fun t' m => ⟨c, hc, SharpPrim.isSharp_of_tmap hs m⟩⟩
  obtain ⟨pr, hpr, huniv, hL, hact, -⟩ := hs
  have hid := SharpPrim.matrix_identities hE.2 hw hw'
  have key := PowerAdjoint.matrix_primitive_adjoint hΘ W ℂ o (spMap em) h k (b.ζ : o) c t.pol pr hpr huniv hL
    (a w) (t.act w) (hact w)
  refine ⟨?_, key.2 (a w') (t.act w') (hact w') hid.2, key.1 hw⟩
  obtain ⟨x0, -, hu0⟩ := huniv t.A pr
  have h1 : ∀ u, (t.act w * t.act w') ≫ pr u = pr u := by
    intro u
    have := hpr u
    rw [MonObj.mul_comp, hact w u, hact w' u]
    exact SharpPrim.prod_mul_prod pr hid.1 u
  rw [hu0 _ h1, hu0 (𝟙 t.A) fun u => Category.id_comp _]

end
