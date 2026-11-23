import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfSquareZeroThickening

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue.CombEx

theorem chart_rebuild {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) : spMap (chartHom V x hx) ≫ hV.fromSpec = x := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hV (isAffineOpen_top (Sp S)) hx.ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  have e : CommRingCat.ofHom (chartHom V x hx) = x.appLE V ⊤ hx.ge ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom := rfl
  show Spec.map (CommRingCat.ofHom (chartHom V x hx)) ≫ hV.fromSpec = x
  rw [e, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem top_of_comp {A B Y : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ Y) (V : Y.Opens) (h : g ⁻¹ᵁ V = ⊤) :
    (f ≫ g) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun x _ => h.ge (show f x ∈ (⊤ : B.Opens) from trivial)

theorem fromSpec_comp_top {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun _ _ => hV.range_fromSpec.subset ⟨_, rfl⟩

theorem chartHom_congr {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {x x' : Sp S ⟶ Y}
    (e : x = x') (h : x ⁻¹ᵁ V = ⊤) (h' : x' ⁻¹ᵁ V = ⊤) : chartHom V x h = chartHom V x' h' := by
  subst e; rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]; rfl

theorem chartHom_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) (hc : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap χ ≫ hV.fromSpec) hc = χ := by
  have e := chart_rebuild hV (spMap χ ≫ hV.fromSpec) hc
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem chartHom_spMap_comp {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S S' : Type} [CommRing S]
    [CommRing S'] (g : S →+* S') (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) (h' : (spMap g ≫ x) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap g ≫ x) h' = g.comp (chartHom V x hx) := by
  have e : spMap (chartHom V (spMap g ≫ x) h') ≫ hV.fromSpec =
      spMap (g.comp (chartHom V x hx)) ≫ hV.fromSpec := by
    rw [chart_rebuild, spMap_comp', Category.assoc, chart_rebuild]
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

end GlobalTheory.SecGlue.CombEx

namespace GlobalTheory.SecGlue.CombEx

theorem mul_eq_zero_of_sq {S T : Type} [CommRing S] [CommRing T] (q : S →+* T) (hsq : RingHom.ker q ^ 2 = ⊥)
    {s t : S} (hs : q s = 0) (ht : q t = 0) : s * t = 0 := by
  have h : s * t ∈ RingHom.ker q ^ 2 := by
    rw [sq]; exact Ideal.mul_mem_mul (RingHom.mem_ker.2 hs) (RingHom.mem_ker.2 ht)
  rw [hsq] at h
  exact (Submodule.mem_bot S).1 h

def combHom {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T) (hsq : RingHom.ker q ^ 2 = ⊥)
    {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S) (hq : ∀ i, q.comp (ψ i) = q.comp φ) :
    A →+* S where
  toFun x := φ x + ∑ i, a i * (ψ i x - φ x)
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add, mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  map_mul' x y := by
    have hd : ∀ i z, q (ψ i z - φ z) = 0 := fun i z => by
      rw [map_sub, ← RingHom.comp_apply, hq i, RingHom.comp_apply, sub_self]
    have hD : ∀ z, q (∑ i, a i * (ψ i z - φ z)) = 0 := fun z => by
      simp only [map_sum, map_mul, hd, mul_zero, Finset.sum_const_zero]
    have e1 : ∀ i, ψ i (x * y) - φ (x * y) = φ x * (ψ i y - φ y) + (ψ i x - φ x) * φ y := fun i => by
      have := mul_eq_zero_of_sq q hsq (hd i x) (hd i y)
      rw [map_mul, map_mul]; linear_combination this
    have e2 := mul_eq_zero_of_sq q hsq (hD x) (hD y)
    have s : ∑ i, a i * (ψ i (x * y) - φ (x * y)) =
        φ x * ∑ i, a i * (ψ i y - φ y) + φ y * ∑ i, a i * (ψ i x - φ x) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [e1 i]; ring
    show φ (x * y) + ∑ i, a i * (ψ i (x * y) - φ (x * y)) =
      (φ x + ∑ i, a i * (ψ i x - φ x)) * (φ y + ∑ i, a i * (ψ i y - φ y))
    linear_combination s + map_mul φ x y - e2

theorem combHom_apply {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) (x : A) :
    combHom q hsq φ ψ a hq x = φ x + ∑ i, a i * (ψ i x - φ x) := rfl

theorem comp_combHom {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) : q.comp (combHom q hsq φ ψ a hq) = q.comp φ := by
  ext x
  have hd : ∀ i, q (ψ i x - φ x) = 0 := fun i => by
    rw [map_sub, ← RingHom.comp_apply, hq i, RingHom.comp_apply, sub_self]
  simp only [RingHom.comp_apply, combHom_apply, map_add, map_sum, map_mul, hd, mul_zero,
    Finset.sum_const_zero, add_zero]

theorem combHom_comp_eq {R A S T : Type} [CommRing R] [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) (θ : R →+* A) (hθ : ∀ i, (ψ i).comp θ = φ.comp θ) :
    (combHom q hsq φ ψ a hq).comp θ = φ.comp θ := by
  ext r
  have h : ∀ i, ψ i (θ r) = φ (θ r) := fun i => RingHom.congr_fun (hθ i) r
  simp only [RingHom.comp_apply, combHom_apply, h, sub_self, mul_zero, Finset.sum_const_zero, add_zero]

theorem exists_comb : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), u ⁻¹ᵁ V = ⊤ →
    (∀ i, spMap q ≫ w i = spMap q ≫ u) →
    ∃ c : Sp S ⟶ Y, GlobalTheory.SecGlue.IsCombIn V u c w a ∧ spMap q ≫ c = spMap q ≫ u ∧
      ∀ (R' : Type) [CommRing R'] (p : Y ⟶ Sp R'), (∀ i, w i ≫ p = u ≫ p) → c ≫ p = u ≫ p := by
  intro Y V hV S T _ _ q hqs hsq ι _ u w a hu hw
  have hwV : ∀ i, w i ⁻¹ᵁ V = ⊤ := fun i => (GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero S T q hqs hsq Y (w i) u (hw i) V).trans hu
  have hq : ∀ i, q.comp (chartHom V (w i) (hwV i)) = q.comp (chartHom V u hu) := fun i => by
    rw [← chartHom_spMap_comp hV q (w i) (hwV i) (top_of_comp _ _ V (hwV i)),
      ← chartHom_spMap_comp hV q u hu (top_of_comp _ _ V hu)]
    exact chartHom_congr V (hw i) _ _
  let χ := combHom q hsq (chartHom V u hu) (fun i => chartHom V (w i) (hwV i)) a hq
  have hc := fromSpec_comp_top hV χ
  refine ⟨spMap χ ≫ hV.fromSpec, ⟨hu, hc, hwV, fun x => ?_⟩, ?_, ?_⟩
  · rw [chartHom_fromSpec hV χ hc]; rfl
  · calc spMap q ≫ spMap χ ≫ hV.fromSpec = spMap (q.comp χ) ≫ hV.fromSpec := by
          rw [spMap_comp', Category.assoc]
      _ = spMap (q.comp (chartHom V u hu)) ≫ hV.fromSpec := by rw [comp_combHom]
      _ = spMap q ≫ u := by rw [spMap_comp', Category.assoc, chart_rebuild]
  · intro R' _ p hp
    let θ : CommRingCat.of R' ⟶ Γ(Y, V) := Spec.preimage (hV.fromSpec ≫ p)
    have key : ∀ (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤), x ≫ p = spMap ((chartHom V x hx).comp θ.hom) := by
      intro x hx
      calc x ≫ p = spMap (chartHom V x hx) ≫ hV.fromSpec ≫ p := by rw [← Category.assoc, chart_rebuild]
        _ = spMap (chartHom V x hx) ≫ Spec.map θ := by rw [Spec.map_preimage]
        _ = spMap ((chartHom V x hx).comp θ.hom) := by
          show _ = Spec.map (CommRingCat.ofHom _)
          rw [show CommRingCat.ofHom ((chartHom V x hx).comp θ.hom) = θ ≫ CommRingCat.ofHom (chartHom V x hx)
            from rfl, Spec.map_comp]
    have hθ : ∀ i, (chartHom V (w i) (hwV i)).comp θ.hom = (chartHom V u hu).comp θ.hom := fun i => by
      have e := (key (w i) (hwV i)).symm.trans ((hp i).trans (key u hu))
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    rw [key _ hc, key u hu, chartHom_fromSpec hV χ hc]
    exact congrArg spMap (combHom_comp_eq q hsq _ _ a hq θ.hom hθ)

end GlobalTheory.SecGlue.CombEx
