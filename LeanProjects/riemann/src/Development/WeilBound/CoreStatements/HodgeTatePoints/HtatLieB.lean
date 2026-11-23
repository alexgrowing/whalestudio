import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieChartOfSmoothChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorSumDualNumber
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeVectorBundleOfSmooth

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ChartDer

noncomputable section

namespace PositivityTheory.HtPt.Htat.Lie

theorem mul_left_eq : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (hU : IsAffineOpen U)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  ∀ (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ φ ψ χ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) → (∀ a, (ψ a).fst = u a) → (∀ a, (χ a).fst = u a) →
    (∀ a, (χ a).snd = (φ a).snd + (ψ a).snd) →
    v.left = spMap φ ≫ hU.fromSpec → w.left = spMap ψ ≫ hU.fromSpec → (v * w).left = spMap χ ≫ hU.fromSpec := by
  intro S G _ U hU C _ y u hu v w hv hw φ ψ χ hφ hψ hχ hs ev ew
  have hv' : LieEx.zsec y ≫ (v : LieEx.ob y C ⟶ G) = 1 := (LieEx.isTanAt_iff y G v).1 hv
  have hw' : LieEx.zsec y ≫ (w : LieEx.ob y C ⟶ G) = 1 := (LieEx.isTanAt_iff y G w).1 hw
  have z : ∀ t : LieEx.ob y C ⟶ G, LieEx.zsec y ≫ t = 1 → LieEx.hom y (0 : C →ₗ[C] C) ≫ t = 1 := fun t ht => by
    rw [LieEx.hom_zero, Category.assoc, ht, MonObj.comp_one]
  obtain ⟨t, ht⟩ : ∃ t : LieEx.ob y (C × C) ⟶ G, t = (LieEx.hom y (LinearMap.inl C C C) ≫ (v : LieEx.ob y C ⟶ G)) *
    (LieEx.hom y (LinearMap.inr C C C) ≫ (w : LieEx.ob y C ⟶ G)) := ⟨_, rfl⟩
  have hz : LieEx.zsec y ≫ t = 1 := by
    rw [ht, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, LieEx.zsec_hom, LieEx.zsec_hom, hv', hw',
      _root_.mul_one]
  have h1 : LieEx.hom y (LinearMap.fst C C C) ≫ t = v := by
    simp only [ht, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.fst_comp_inl,
      LinearMap.fst_comp_inr, LieEx.hom_id, Category.id_comp, z w hw', _root_.mul_one]
  have h2 : LieEx.hom y (LinearMap.snd C C C) ≫ t = w := by
    simp only [ht, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.snd_comp_inl,
      LinearMap.snd_comp_inr, LieEx.hom_id, Category.id_comp, z v hv', _root_.one_mul]
  have h3 : LieEx.hom y (LinearMap.fst C C C + LinearMap.snd C C C) ≫ t = v * w := by
    simp only [ht, MonObj.comp_mul, ← Category.assoc, LieEx.hom_comp, LinearMap.add_comp,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr,
      add_zero, zero_add, LieEx.hom_id, Category.id_comp]
  have hzl : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom C C (C × C)).toRingHom) ≫ t.left =
      spMap u ≫ hU.fromSpec := (congrArg CommaMorphism.left hz).trans hu
  have hle : ⊤ ≤ t.left ⁻¹ᵁ U := by
    intro p _
    obtain ⟨q, rfl⟩ := LieVB.surj_fst (T := C) (M := C × C) p
    have e : t.left (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom C C (C × C)).toRingHom) q) =
        hU.fromSpec (spMap u q) := congrArg (fun f : Sp C ⟶ G.left => f q) hzl
    show t.left _ ∈ U
    rw [e]
    exact hU.range_fromSpec.subset (Set.mem_range_self _)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Γ(G.left, U) →+* TrivSqZeroExt C (C × C), spMap Φ ≫ hU.fromSpec = t.left :=
    ⟨_, TanMul.ringOf_spec (A := TrivSqZeroExt C (C × C)) hU t.left hle⟩
  have key : ∀ (l : C × C →ₗ[C] C), (LieEx.hom y l ≫ t).left =
      spMap ((TrivSqZeroExt.map l).toRingHom.comp Φ) ≫ hU.fromSpec := fun l => by
    rw [spMap_comp, Category.assoc, hΦ]
    rfl
  have e1 := TanMul.ring_inj hU (ev.symm.trans ((congrArg CommaMorphism.left h1).symm.trans (key _)))
  have e2 := TanMul.ring_inj hU (ew.symm.trans ((congrArg CommaMorphism.left h2).symm.trans (key _)))
  have e3 : χ = (TrivSqZeroExt.map (LinearMap.fst C C C + LinearMap.snd C C C)).toRingHom.comp Φ := by
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    · rw [hχ, ← hφ, e1]
      simp
    · rw [hs, e1, e2]
      simp
  rw [e3]
  exact (congrArg CommaMorphism.left h3).symm.trans (key _)

theorem exists_lieModel {S : Scheme.{0}} (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
    (C : Type) [CommRing C] (y : Sp C ⟶ S) (v : Γ(G.left, U) →+* C)
    (h1 : (1 : Over.mk y ⟶ G).left = spMap v ≫ hU.fromSpec)
    {E : Type} [AddCommGroup E] [Module C E] (δ : E → Γ(G.left, U) → C)
    (hadd : ∀ e a b, δ e (a + b) = δ e a + δ e b)
    (hmul : ∀ e a b, δ e (a * b) = v a * δ e b + v b * δ e a)
    (hker : ∀ e b, δ e ((G.hom.appLE V U hUV).hom b) = 0)
    (hEadd : ∀ e e' a, δ (e + e') a = δ e a + δ e' a)
    (hEsmul : ∀ (c : C) e a, δ (c • e) a = c * δ e a)
    (hinj : ∀ e e', (∀ a, δ e a = δ e' a) → e = e')
    (hsurj : ∀ δ' : Γ(G.left, U) → C, (∀ a b, δ' (a + b) = δ' a + δ' b) →
      (∀ a b, δ' (a * b) = v a * δ' b + v b * δ' a) →
      (∀ b, δ' ((G.hom.appLE V U hUV).hom b) = 0) → ∃ e, ∀ a, δ e a = δ' a) :
    ∃ M : LieModel G y E, ∀ e, ∃ φ : Γ(G.left, U) →+* DualNumber C,
      (∀ a, (φ a).fst = v a) ∧ (∀ a, (φ a).snd = δ e a) ∧ (M.pt e).left = spMap φ ≫ hU.fromSpec := by
  obtain ⟨c1, c2⟩ := GlobalTheory.T.tangent_vector_of_dual_hom S G U V hU hV hUV C y v h1
  let φ : E → (Γ(G.left, U) →+* DualNumber C) := fun e => dualOf v (δ e) (hadd e) (hmul e)
  have φfst : ∀ e a, (φ e a).fst = v a := fun e a => dualOf_fst ..
  have φsnd : ∀ e a, (φ e a).snd = δ e a := fun e a => dualOf_snd ..
  have ex : ∀ e, ∃ t : epsAt y ⟶ G, IsTanAt G y t ∧ t.left = spMap (φ e) ≫ hU.fromSpec :=
    fun e => c1 (φ e) (φfst e) fun b => by rw [φsnd, hker]
  choose pt ptan pleft using ex
  have spinj : ∀ ψ ψ' : Γ(G.left, U) →+* DualNumber C,
      spMap ψ ≫ hU.fromSpec = spMap ψ' ≫ hU.fromSpec → ψ = ψ' := fun ψ ψ' h => by
    have h2 := Spec.map_injective ((cancel_mono hU.fromSpec).1 h)
    simpa using congrArg CommRingCat.Hom.hom h2
  refine ⟨{ pt := pt, tan := ptan, inj := ?_, onto := ?_, add := ?_, smul := ?_ },
    fun e => ⟨φ e, φfst e, φsnd e, pleft e⟩⟩
  · intro e e' h
    have h2 := spinj _ _ (by rw [← pleft, ← pleft, h] : spMap (φ e) ≫ hU.fromSpec = spMap (φ e') ≫ hU.fromSpec)
    exact hinj _ _ fun a => by rw [← φsnd, h2, φsnd]
  · intro t ht
    obtain ⟨ψ, f1, f2, f3⟩ := c2 t ht
    obtain ⟨e, he⟩ := hsurj (fun a => (ψ a).snd) (fun a b => by simp)
      (fun a b => by
        simp only [map_mul, TrivSqZeroExt.snd_mul, f1]
        simp [mul_comm, add_comm]) f2
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    have h2 : φ e = ψ := RingHom.ext fun a => TrivSqZeroExt.ext (by rw [φfst, f1]) (by rw [φsnd, he])
    rw [pleft, f3, h2]
  · intro e e'
    refine Over.OverMorphism.ext ?_
    rw [mul_left_eq S G U hU C y v h1 (pt e) (pt e') (ptan e) (ptan e') (φ e) (φ e') (φ (e + e'))
      (φfst e) (φfst e') (φfst _) (fun a => by rw [φsnd, φsnd, φsnd, hEadd]) (pleft e) (pleft e'), pleft]
  · intro c e
    have h2 : φ (c • e) = (epsMul c).comp (φ e) := RingHom.ext fun a => TrivSqZeroExt.ext
      (by simp [epsMul, φfst]) (by simp [epsMul, φsnd, hEsmul])
    rw [pleft, pleft, h2, spMap_comp, Category.assoc]

theorem lieChart_of_smooth_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Sp R ⟶ S) (f : R) (U : G.left.Opens) (V : S.Opens)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V), RingHom.Smooth (G.hom.appLE V U hUV).hom →
  ∀ u : Γ(G.left, U) →+* Localization.Away f,
    (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec → LieChart G x f := by
  intro S G _ R _ x f U V hU hV hUV hsm u h1
  obtain ⟨P, i1, i2, i3, i4, i5, i6, d, dadd, dmul, dker, hP⟩ :=
    exists_diffModule (G.hom.appLE V U hUV).hom hsm f u
  have hunit : ∀ (C : Type) [CommRing C] [Algebra R C] (κ : Localization.Away f →+* C),
      κ.comp (algebraMap R (Localization.Away f)) = algebraMap R C →
      (1 : Over.mk (spMap (algebraMap R C) ≫ x) ⟶ G).left = spMap (κ.comp u) ≫ hU.fromSpec := by
    intro C _ _ κ hκ
    rw [one_left] at h1 ⊢
    simp only [Over.mk_hom] at h1 ⊢
    have e : spMap (algebraMap R C) = spMap κ ≫ spMap (algebraMap R (Localization.Away f)) := by
      rw [← spMap_comp, hκ]
    have h3 : ((spMap κ ≫ spMap (algebraMap R (Localization.Away f))) ≫ x) ≫ η[G].left =
        spMap κ ≫ (spMap (algebraMap R (Localization.Away f)) ≫ x) ≫ η[G].left := by
      simp only [Category.assoc]
    rw [e, h3, h1, spMap_comp κ u]
    exact (Category.assoc _ _ _).symm
  have key : ∀ (C : Type) [CommRing C] [Algebra R C] (hC : IsUnit (algebraMap R C f)),
      ∃ M : LieModel G (spMap (algebraMap R C) ≫ x) (P →ₗ[R] C), ∀ w,
        ∃ φ : Γ(G.left, U) →+* DualNumber C,
          (∀ a, (φ a).fst = ((IsLocalization.Away.lift f hC).comp u) a) ∧ (∀ a, (φ a).snd = w (d a)) ∧
          (M.pt w).left = spMap φ ≫ hU.fromSpec := by
    intro C _ _ hC
    have hκ := IsLocalization.Away.lift_comp (S := Localization.Away f) f hC
    obtain ⟨l1, l2, l3⟩ := hP C _ hκ
    exact exists_lieModel (E := P →ₗ[R] C) G U V hU hV hUV C _ _ (hunit C _ hκ)
      (fun (w : P →ₗ[R] C) a => w (d a))
      (fun w a b => by simp [dadd]) (fun w a b => by simp only [dmul, map_add, l1, RingHom.comp_apply])
      (fun w b => by simp [dker]) (fun w w' a => rfl) (fun c w a => by simp) l2 l3
  refine ⟨P, i1, i2, i3, i4, i5, i6, fun C _ _ hC => (key C hC).choose, ?_⟩
  intro C C' _ _ _ _ hC hC' c w
  obtain ⟨φ, f1, f2, f3⟩ := (key C hC).choose_spec w
  obtain ⟨φ', g1, g2, g3⟩ := (key C' hC').choose_spec (c.toLinearMap ∘ₗ w)
  have hc : c.toRingHom.comp (IsLocalization.Away.lift (S := Localization.Away f) f hC) =
      IsLocalization.Away.lift (S := Localization.Away f) f hC' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
    rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp]
    exact c.comp_algebraMap
  have h2 : φ' = (dualMap c.toRingHom).comp φ := RingHom.ext fun a => TrivSqZeroExt.ext
    (by
      simp only [g1, RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, f1]
      exact (RingHom.congr_fun hc (u a)).symm)
    (by
      simp only [g2, RingHom.comp_apply, dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, f2]
      rfl)
  rw [g3, f3, h2, spMap_comp, Category.assoc]

end PositivityTheory.HtPt.Htat.Lie
