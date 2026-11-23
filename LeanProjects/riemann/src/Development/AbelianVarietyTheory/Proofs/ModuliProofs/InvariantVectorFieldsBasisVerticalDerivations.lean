import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueInvariantVectorFieldOfTangent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PreimageTranslate
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS GlobalTheory.TangentOrigin GlobalTheory.SqZero GlobalTheory.LieBaseChange
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD pushR pullR fB)
open TrivSqZeroExt (inl inr)

noncomputable section

namespace GlobalTheory.InvFieldBasis

variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {n : ℕ}
variable {C : Type} [CommRing C] [Algebra K C] {B : Type} [CommRing B] [Algebra K B]

theorem exists_dualHom {A C : Type} [CommRing A] [CommRing C] (φ : A →+* C) (δ : A → C)
    (hadd : ∀ f f', δ (f + f') = δ f + δ f') (hmul : ∀ f f', δ (f * f') = φ f * δ f' + φ f' * δ f) :
    ∃ ψ : A →+* DualNumber C, ∀ f, ψ f = inl (φ f) + inr (δ f) := by
  have h0 : δ 0 = 0 := by
    have h := hadd 0 0
    simp only [add_zero] at h
    exact left_eq_add.mp h
  have h1 : δ 1 = 0 := by
    have h := hmul 1 1
    simp at h
    linear_combination h
  refine ⟨{ toFun := fun f => inl (φ f) + inr (δ f)
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun _ => rfl⟩
  · simp [h1]
  · intro f f'
    ext <;> simp [hmul, TrivSqZeroExt.snd_mul, mul_comm]
  · simp [h0]
  · intro f f'
    ext <;> simp [hadd]

theorem dual_eq_iff {C : Type} [CommRing C] (a b : C) (c d : Fin n → C) :
    (inl a + inr b : DualNumber C) = inl a + ∑ i, inr (c i) * inl (d i) ↔ b = ∑ i, c i * d i := by
  rw [add_right_inj]
  have hs : ∑ i, (inr (c i) : DualNumber C) * inl (d i) = inr (∑ i, c i * d i) := by
    ext <;> simp [TrivSqZeroExt.fst_sum, TrivSqZeroExt.snd_sum]
  rw [hs]
  exact TrivSqZeroExt.inr_injective.eq_iff

theorem evalPt_comp {Y Z : Scheme.{0}} (x : Sp B ⟶ Z) (f : Z ⟶ Y) (O : Y.Opens) (y : Sp B ⟶ Y) (hy : x ≫ f = y)
    (h' : ⊤ ≤ x ⁻¹ᵁ (f ⁻¹ᵁ O)) (h'' : ⊤ ≤ y ⁻¹ᵁ O) (s : Γ(Y, O)) :
    evalPt y O h'' s = evalPt x _ h' ((f.app O).hom s) := by
  rw [← evalPt_pbT x f (le_refl (f ⁻¹ᵁ O)) h' y hy h'' s]
  congr 1
  simp [pbT, Scheme.Hom.app_eq_appLE]

theorem evalPt_congr {Y : Scheme.{0}} {x y : Sp B ⟶ Y} (e : x = y) (O : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ O)
    (h' : ⊤ ≤ y ⁻¹ᵁ O) (s : Γ(Y, O)) : evalPt x O h s = evalPt y O h' s := by
  cases e
  rfl

theorem existsUnique_coeff_alg [Smooth G.hom] {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    {dd : Fin n → ∀ O : G.left.Opens, Γ(G.left, O) → Γ(G.left, O)} (hd : ∀ i, IsInvDer (v i) (dd i))
    {R : Type} [CommRing R] (x₀ : R →+* K) {X : Scheme.{0}} (p : X ⟶ Sp R) (m : G.left ⟶ X)
    (H : IsPullback m G.hom p (spMap x₀)) (y : sp (R₀ := K) C ⟶ G) {W : X.Opens} (hW : IsAffineOpen W)
    (h : ⊤ ≤ y.left ⁻¹ᵁ (m ⁻¹ᵁ W)) (δ : Γ(X, W) → C) (hadd : ∀ f f', δ (f + f') = δ f + δ f')
    (hmul : ∀ f f', δ (f * f') = evalPt y.left _ h ((m.app W).hom f) * δ f' +
      evalPt y.left _ h ((m.app W).hom f') * δ f)
    (hbase : ∀ r, δ (constFn p W r) = 0) :
    ∃! c : Fin n → C, ∀ f, δ f = ∑ a, c a * evalPt y.left _ h (dd a _ ((m.app W).hom f)) := by
  classical
  have hT : ∀ i, IsTangent (v i) := hv.1
  obtain ⟨ψ, hψ⟩ := exists_dualHom ((evalPt y.left _ h).comp (m.app W).hom) δ hadd hmul
  obtain ⟨x', hx', hx'ψ⟩ := exists_evalPt_eq hW ψ
  have h2 : ⊤ ≤ (y.left ≫ m) ⁻¹ᵁ W := h
  have hym : y.left ≫ m ≫ p = spMap ((algebraMap K C).comp x₀) := by
    rw [H.w, ← Category.assoc, Over.w y, spMap_comp]
    rfl
  have hbase' : ∀ r, evalPt (x' ≫ p) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      ((algebraMap K (DualNumber C)).comp x₀) r := by
    intro r
    rw [← evalPt_constFn p x' W hx' r, hx'ψ, hψ, hbase r, RingHom.comp_apply,
      ← evalPt_comp y.left m W (y.left ≫ m) rfl h h2, evalPt_constFn p (y.left ≫ m) W h2 r]
    have h3 : evalPt ((y.left ≫ m) ≫ p) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
        algebraMap K C (x₀ r) := by
      rw [Category.assoc, hym, evalPt_spMap]
      rfl
    rw [h3, TrivSqZeroExt.inr_zero, add_zero]
    rfl
  have hsq : x' ≫ p = (sp (R₀ := K) (DualNumber C)).hom ≫ spMap x₀ := by
    rw [eq_spMap_of_evalPt _ _ hbase', spMap_comp]
    rfl
  let wL : Sp (DualNumber C) ⟶ G.left := H.lift x' (sp (R₀ := K) (DualNumber C)).hom hsq
  have hwLm : wL ≫ m = x' := H.lift_fst _ _ _
  let wO : sp (R₀ := K) (DualNumber C) ⟶ G := Over.homMk wL (H.lift_snd _ _ _)
  let z : sp (R₀ := K) (DualNumber C) ⟶ G := Chart.spMap (TrivSqZeroExt.inlAlgHom K C C) ≫ y
  have top_rw : ∀ {A B : Scheme.{0}} (a : A ⟶ B) {U : B.Opens}, ⊤ ≤ U → ⊤ ≤ a ⁻¹ᵁ U := by
    intro A B a U hU
    rw [top_le_iff] at hU ⊢
    rw [hU]
    simp
  have hz : ⊤ ≤ z.left ⁻¹ᵁ (m ⁻¹ᵁ W) := top_rw (Chart.spMap (TrivSqZeroExt.inlAlgHom K C C)).left h
  have hzl : ∀ g, evalPt z.left (m ⁻¹ᵁ W) hz g = inl (evalPt y.left (m ⁻¹ᵁ W) h g) := fun g =>
    evalPt_spMap_comp (TrivSqZeroExt.inlAlgHom K C C).toRingHom y.left _ h hz g
  have key : ∀ c' : Fin n → C, ∃ hk : ⊤ ≤ ((expPt v (fun i => (inr (c' i) : DualNumber C))
      (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) * z).left ≫ m) ⁻¹ᵁ W, ∀ f,
      evalPt _ W hk f = inl (evalPt y.left _ h ((m.app W).hom f)) +
        ∑ i, inr (c' i) * inl (evalPt y.left _ h (dd i _ ((m.app W).hom f))) := by
    intro c'
    obtain ⟨h', hf⟩ := evalPt_expPt hT hd (fun i => (inr (c' i) : DualNumber C))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _) z (m ⁻¹ᵁ W) hz
    refine ⟨h', fun f => ?_⟩
    refine (evalPt_comp _ m W _ rfl h' h' f).trans ?_
    rw [hf, hzl]
    simp only [hzl]
  have hs_y : Chart.spMap ((fstD C).restrictScalars K) ≫ wO = y := by
    apply Over.OverMorphism.ext
    apply H.hom_ext
    · change (Chart.spMap ((fstD C).restrictScalars K)).left ≫ wL ≫ m = y.left ≫ m
      rw [hwLm]
      have hh : ⊤ ≤ ((Chart.spMap ((fstD C).restrictScalars K)).left ≫ x') ⁻¹ᵁ W :=
        top_rw (Chart.spMap ((fstD C).restrictScalars K)).left hx'
      refine ext_evalPt hW hh h2 (RingHom.ext fun f => ?_)
      refine (evalPt_spMap_comp ((fstD C).restrictScalars K).toRingHom x' W hx' hh f).trans ?_
      rw [hx'ψ, hψ, evalPt_comp y.left m W _ rfl h h2 f]
      simp [fstD]
    · change (Chart.spMap ((fstD C).restrictScalars K)).left ≫ wL ≫ G.hom = y.left ≫ G.hom
      rw [H.lift_snd, Over.w, Over.w]
  have hs_z : Chart.spMap ((fstD C).restrictScalars K) ≫ z = y := by
    have e1 : Chart.spMap ((fstD C).restrictScalars K) ≫ Chart.spMap (TrivSqZeroExt.inlAlgHom K C C) = 𝟙 _ := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left]
      change spMap _ ≫ spMap _ = 𝟙 _
      rw [← spMap_comp]
      have e2 : ((fstD C).restrictScalars K).toRingHom.comp (TrivSqZeroExt.inlAlgHom K C C).toRingHom =
          RingHom.id C := RingHom.ext fun _ => rfl
      rw [e2]
      simp [spMap]
    rw [← Category.assoc, e1, Category.id_comp]
  have hw : Chart.spMap ((fstD C).restrictScalars K) ≫ (wO * z⁻¹) = 1 := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hs_y, hs_z, mul_inv_cancel]
  obtain ⟨c, hc, huniq⟩ := existsUnique_expPt hv (wO * z⁻¹) hw
  have hwO : wO = expPt v (fun i => (inr (c i) : DualNumber C)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) * z := by
    rw [← hc, inv_mul_cancel_right]
  have hiff : ∀ c' : Fin n → C, (∀ f, δ f = ∑ a, c' a * evalPt y.left _ h (dd a _ ((m.app W).hom f))) ↔
      (expPt v (fun i => (inr (c' i) : DualNumber C)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) * z).left ≫ m = x' := by
    intro c'
    obtain ⟨hk, hkf⟩ := key c'
    constructor
    · intro hc'
      refine ext_evalPt hW hk hx' (RingHom.ext fun f => ?_)
      rw [hkf, hx'ψ, hψ, RingHom.comp_apply]
      exact ((dual_eq_iff _ _ _ _).mpr (hc' f)).symm
    · intro he f
      have e1 := evalPt_congr he W hk hx' f
      rw [hkf, hx'ψ, hψ, RingHom.comp_apply] at e1
      exact (dual_eq_iff _ _ _ _).mp e1.symm
  refine ⟨c, (hiff c).mpr ?_, fun c' hc' => ?_⟩
  · rw [← hwO]
    exact hwLm
  · have e := (hiff c').mp hc'
    apply huniq
    have e3 : expPt v (fun i => (inr (c' i) : DualNumber C)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) * z = wO := by
      apply Over.OverMorphism.ext
      apply H.hom_ext
      · rw [e]
        exact hwLm.symm
      · rw [Over.w, Over.w]
    rw [← e3, mul_inv_cancel_right]

theorem existsUnique_coeff_affine [Smooth G.hom] {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    {dd : Fin n → ∀ O : G.left.Opens, Γ(G.left, O) → Γ(G.left, O)} (hd : ∀ i, IsInvDer (v i) (dd i))
    {R : Type} [CommRing R] (x₀ : R →+* K) {X : Scheme.{0}} (p : X ⟶ Sp R) (m : G.left ⟶ X)
    (H : IsPullback m G.hom p (spMap x₀)) {T : Scheme.{0}} (y : T ⟶ G.left) {W : X.Opens} (hW : IsAffineOpen W)
    {V : T.Opens} (hV : IsAffineOpen V) (h : V ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W)) (δ : Γ(X, W) → Γ(T, V))
    (hadd : ∀ f f', δ (f + f') = δ f + δ f')
    (hmul : ∀ f f', δ (f * f') = pbT y ((m.app W).hom f) V * δ f' + pbT y ((m.app W).hom f') V * δ f)
    (hbase : ∀ r, δ (constFn p W r) = 0) :
    ∃! c : Fin n → Γ(T, V), ∀ f, δ f = ∑ a, c a * pbT y (dd a _ ((m.app W).hom f)) V := by
  classical
  have hfs : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  have L0 : ∀ s, evalPt (R := Γ(T, V)) hV.fromSpec V hfs s = s := by
    have e := eq_spec_fromSpec hV hV.fromSpec hfs
    have e2 : Spec.map (CommRingCat.ofHom (evalPt (R := Γ(T, V)) hV.fromSpec V hfs)) = 𝟙 _ := by
      rw [← cancel_mono hV.fromSpec, Category.id_comp]
      exact e.symm
    have e3 : CommRingCat.ofHom (evalPt (R := Γ(T, V)) hV.fromSpec V hfs) = 𝟙 _ :=
      Spec.map_inj.mp (by rw [e2, Spec.map_id])
    intro s
    have e4 := congrArg (fun q => q.hom s) e3
    simpa using e4
  let φ : K →+* Γ(T, V) := (evalPt (R := Γ(T, V)) (hV.fromSpec ≫ y ≫ G.hom) ⊤ le_rfl).comp
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  letI : Algebra K Γ(T, V) := φ.toAlgebra
  have hφ : (hV.fromSpec ≫ y) ≫ G.hom = (sp (R₀ := K) Γ(T, V)).hom := by
    rw [Category.assoc]
    exact eq_spMap_of_evalPt _ φ (fun _ => rfl)
  let y' : sp (R₀ := K) Γ(T, V) ⟶ G := Over.homMk (hV.fromSpec ≫ y) hφ
  have hkey : ∀ (g : Γ(G.left, m ⁻¹ᵁ W)) (h' : ⊤ ≤ y'.left ⁻¹ᵁ (m ⁻¹ᵁ W)),
      evalPt y'.left (m ⁻¹ᵁ W) h' g = pbT y g V := by
    intro g h'
    rw [← L0 (pbT y g V)]
    exact (evalPt_pbT hV.fromSpec y h hfs y'.left rfl h' g).symm
  have hy' : ⊤ ≤ y'.left ⁻¹ᵁ (m ⁻¹ᵁ W) := le_trans hfs (fun x hx => h hx)
  obtain ⟨c, hc, hu⟩ := existsUnique_coeff_alg (C := Γ(T, V)) hv hd x₀ p m H y' hW hy' δ hadd
    (by intro f f'; rw [hmul, hkey, hkey]) hbase
  refine ⟨c, fun f => (hc f).trans (by simp only [hkey]), fun c' hc' => hu c' fun f => (hc' f).trans ?_⟩
  simp only [hkey]

private theorem rsT_eq_resG_of_le' {Y : Scheme.{0}} {O₀ O : Y.Opens} (s : Γ(Y, O₀)) (h : O ≤ O₀) :
    rsT s O = resG Y h s := by
  simp [rsT, h]

private theorem rsT_rsT_moduli {Y : Scheme.{0}} {O₀ O₁ O : Y.Opens} (s : Γ(Y, O₀)) (h₁ : O₁ ≤ O₀) (h : O ≤ O₁) :
    rsT (rsT s O₁) O = rsT s O := by
  rw [rsT_eq_resG_of_le' _ h, rsT_eq_resG_of_le' _ h₁, rsT_eq_resG_of_le' _ (h.trans h₁), resG, resG, resG,
    ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private theorem rsT_pbT_of_le_of_le {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} {O₁ O : Z.Opens} (s : Γ(Y, O₀))
    (h₁ : O₁ ≤ f ⁻¹ᵁ O₀) (h : O ≤ O₁) : rsT (pbT f s O₁) O = pbT f s O := by
  rw [rsT_eq_resG_of_le' _ h]
  simp only [pbT, dif_pos h₁, dif_pos (h.trans h₁), resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

private theorem pbT_rsT_of_le_preimage_of_le {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ O₁ : Y.Opens} {O : Z.Opens} (s : Γ(Y, O₀))
    (h₁ : O₁ ≤ O₀) (h : O ≤ f ⁻¹ᵁ O₁) : pbT f (rsT s O₁) O = pbT f s O := by
  rw [rsT_eq_resG_of_le' _ h₁]
  simp only [pbT, dif_pos h, dif_pos (h.trans (f.preimage_mono h₁)), resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

private theorem rsT_comp_app_eq_pbT_app {Z Y X : Scheme.{0}} (y : Z ⟶ Y) (m : Y ⟶ X) {W : X.Opens} {V : Z.Opens}
    (h : V ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W)) (f : Γ(X, W)) :
    rsT (((y ≫ m).app W).hom f) V = pbT y ((m.app W).hom f) V := by
  rw [← GlobalTheory.KS.InvField.pbT_eq_app (y ≫ m) f, rsT_pbT_of_le_of_le (y ≫ m) f le_rfl h, ← GlobalTheory.KS.InvField.pbT_eq_app m f,
    GlobalTheory.KS.InvField.pbT_pbT y m le_rfl h f]

private theorem rsT_sum_mul_fintype {Y : Scheme.{0}} {O₀ O : Y.Opens} {J : Type} [Fintype J] (s t : J → Γ(Y, O₀))
    (h : O ≤ O₀) : rsT (∑ a, s a * t a) O = ∑ a, rsT (s a) O * rsT (t a) O := by
  simp only [rsT_eq_resG_of_le' _ h, map_sum, map_mul]

private theorem sheaf_map_eq_rsT {Y : Scheme.{0}} {O₀ O : Y.Opens} (e : O ⟶ O₀) (s : Γ(Y, O₀)) :
    ConcreteCategory.hom (Y.sheaf.obj.map e.op) s = rsT s O := by
  rw [rsT_eq_resG_of_le' _ (leOfHom e)]
  rfl

theorem existsUnique_coeff : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (T : Scheme.{0}) (y : T ⟶ A₀.left) (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(T, (y ≫ m) ⁻¹ᵁ W)), LocDerK (y ≫ A₀.hom) p (y ≫ m) (fun _ => 0) W₀ d → ∃! c : Fin g → Γ(T, (y ≫ m) ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f, d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
  intro K _ A₀ _ g v dd hsm hv hd R _ x₀ X p m H T y W₀ d hD
  classical
  have := hsm
  have hdd : ∀ a (O O' : A₀.left.Opens) (s : Γ(A₀.left, O)), O' ≤ O →
      dd a O' (rsT s O') = rsT (dd a O s) O' :=
    fun a O O' s hO => ((GlobalTheory.KS.InvField.main K A₀ (v a) (hv.1 a)).2 (dd a) (hd a)).2.2.1 O O' s hO
  have hsub : ∀ (Wb Wl : X.Opens) (hl : Wl ≤ Wb) (Vl : T.Opens), Vl ≤ y ⁻¹ᵁ (m ⁻¹ᵁ Wl) → ∀ a (f : Γ(X, Wb)),
      pbT y (dd a (m ⁻¹ᵁ Wl) ((m.app Wl).hom (resG X hl f))) Vl =
        pbT y (dd a (m ⁻¹ᵁ Wb) ((m.app Wb).hom f)) Vl := by
    intro Wb Wl hl Vl hVl a f
    have e1 : (m.app Wl).hom (resG X hl f) = rsT ((m.app Wb).hom f) (m ⁻¹ᵁ Wl) := by
      rw [← rsT_eq_resG_of_le' _ hl, ← GlobalTheory.KS.InvField.pbT_eq_app, ← GlobalTheory.KS.InvField.pbT_eq_app,
        pbT_rsT_of_le_preimage_of_le m f hl le_rfl, rsT_pbT_of_le_of_le m f le_rfl (m.preimage_mono hl)]
    rw [e1, hdd a _ _ _ (m.preimage_mono hl), pbT_rsT_of_le_preimage_of_le y _ (m.preimage_mono hl) hVl]
  have loc : ∀ (W : X.Opens) (V : T.Opens), IsAffineOpen W → W ≤ W₀ → IsAffineOpen V →
      V ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W) →
      ∃! c : Fin g → Γ(T, V), ∀ f, rsT (d W f) V = ∑ a, c a * pbT y (dd a _ ((m.app W).hom f)) V := by
    intro W V hW hW₀ hV hVW
    refine existsUnique_coeff_affine (G := A₀) hv hd x₀ p m H y hW hV hVW (fun f => rsT (d W f) V) ?_ ?_ ?_
    · intro f f'
      simp only [hD.add W hW₀, rsT_eq_resG_of_le' (O₀ := (y ≫ m) ⁻¹ᵁ W) _ hVW, map_add]
    · intro f f'
      simp only [hD.mul W hW₀, rsT_eq_resG_of_le' (O₀ := (y ≫ m) ⁻¹ᵁ W) _ hVW, map_add, map_mul]
      simp only [← rsT_eq_resG_of_le' (O₀ := (y ≫ m) ⁻¹ᵁ W) _ hVW, rsT_comp_app_eq_pbT_app y m hVW]
    · intro r
      simp only [hD.base W hW₀, GlobalTheory.KS.InvField.constFn_zero, rsT_eq_resG_of_le' (O₀ := (y ≫ m) ⁻¹ᵁ W) _ hVW,
        map_zero]
  let P := {pr : X.Opens × T.Opens // IsAffineOpen pr.1 ∧ pr.1 ≤ W₀ ∧ IsAffineOpen pr.2 ∧
    pr.2 ≤ y ⁻¹ᵁ (m ⁻¹ᵁ pr.1)}
  have Cex : ∀ k : P, ∃! c : Fin g → Γ(T, k.1.2), ∀ f,
      rsT (d k.1.1 f) k.1.2 = ∑ a, c a * pbT y (dd a _ ((m.app k.1.1).hom f)) k.1.2 :=
    fun k => loc _ _ k.2.1 k.2.2.1 k.2.2.2.1 k.2.2.2.2
  choose C hC using fun k => (Cex k).exists
  have cov : ∀ (Wb : X.Opens) (Vb : T.Opens), Wb ≤ W₀ → Vb ≤ y ⁻¹ᵁ (m ⁻¹ᵁ Wb) →
      Vb ≤ ⨆ k : {k : P // k.1.1 ≤ Wb ∧ k.1.2 ≤ Vb}, k.1.1.2 := by
    intro Wb Vb hWb hVb t ht
    have hq : m.base (y.base t) ∈ Wb := hVb ht
    obtain ⟨⟨W3, hW3, hW3b⟩, ht3⟩ :=
      (TopologicalSpace.Opens.mem_iSup).mp (GlobalTheory.ConstThickening.le_iSup_affine Wb hq)
    have ht' : t ∈ Vb ⊓ y ⁻¹ᵁ (m ⁻¹ᵁ W3) := ⟨ht, ht3⟩
    obtain ⟨⟨V3, hV3, hV3b⟩, htV3⟩ :=
      (TopologicalSpace.Opens.mem_iSup).mp (GlobalTheory.ConstThickening.le_iSup_affine _ ht')
    exact (TopologicalSpace.Opens.mem_iSup).mpr
      ⟨⟨⟨(W3, V3), hW3, hW3b.trans hWb, hV3, hV3b.trans inf_le_right⟩, hW3b, hV3b.trans inf_le_left⟩, htV3⟩
  have resc : ∀ (k l : P), l.1.1 ≤ k.1.1 → l.1.2 ≤ k.1.2 → ∀ a, rsT (C k a) l.1.2 = C l a := by
    intro k l hW hV
    have hlk : l.1.2 ≤ y ⁻¹ᵁ (m ⁻¹ᵁ k.1.1) := hV.trans k.2.2.2.2
    have e := (loc k.1.1 l.1.2 k.2.1 k.2.2.1 l.2.2.2.1 hlk).unique
      (y₁ := fun a => rsT (C k a) l.1.2) (y₂ := C l) ?_ ?_
    · exact fun a => congrFun e a
    · intro f
      rw [← rsT_rsT_moduli (d k.1.1 f) k.2.2.2.2 hV, hC k f, rsT_sum_mul_fintype _ _ hV]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [rsT_pbT_of_le_of_le y _ k.2.2.2.2 hV]
    · intro f
      have hq : l.1.2 ≤ (y ≫ m) ⁻¹ᵁ l.1.1 := l.2.2.2.2
      rw [← rsT_rsT_moduli (d k.1.1 f) ((y ≫ m).preimage_mono hW) hq, ← hD.res k.1.1 l.1.1 hW k.2.2.1 f,
        hC l (resG X hW f)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hsub k.1.1 l.1.1 hW l.1.2 l.2.2.2.2]
  have U0 : ∀ k : P, k.1.2 ≤ (y ≫ m) ⁻¹ᵁ W₀ := fun k => k.2.2.2.2.trans ((y ≫ m).preimage_mono k.2.2.1)
  have glue : ∀ a, ∃! s : Γ(T, (y ≫ m) ⁻¹ᵁ W₀), ∀ k : P, rsT s k.1.2 = C k a := by
    intro a
    have hcov : (y ≫ m) ⁻¹ᵁ W₀ ≤ ⨆ k : P, k.1.2 :=
      (cov W₀ _ le_rfl le_rfl).trans (iSup_le fun k => le_iSup (fun k : P => k.1.2) k.1)
    have hcomp : TopCat.Presheaf.IsCompatible T.sheaf.obj (fun k : P => k.1.2) (fun k => C k a) := by
      intro k l
      apply T.sheaf.eq_of_locally_eq' (fun j : {j : P // j.1.1 ≤ k.1.1 ⊓ l.1.1 ∧ j.1.2 ≤ k.1.2 ⊓ l.1.2} => j.1.1.2)
        (k.1.2 ⊓ l.1.2) (fun j => homOfLE j.2.2)
        (cov _ _ (inf_le_left.trans k.2.2.1) (fun t ht => ⟨k.2.2.2.2 ht.1, l.2.2.2.2 ht.2⟩))
      intro j
      erw [sheaf_map_eq_rsT, sheaf_map_eq_rsT, sheaf_map_eq_rsT, sheaf_map_eq_rsT]
      rw [rsT_rsT_moduli _ inf_le_left j.2.2, rsT_rsT_moduli _ inf_le_right j.2.2,
        resc k j.1 (j.2.1.trans inf_le_left) (j.2.2.trans inf_le_left),
        resc l j.1 (j.2.1.trans inf_le_right) (j.2.2.trans inf_le_right)]
    obtain ⟨s, hs, hsu⟩ := T.sheaf.existsUnique_gluing' (fun k : P => k.1.2) ((y ≫ m) ⁻¹ᵁ W₀)
      (fun k => homOfLE (U0 k)) hcov (fun k => C k a) hcomp
    refine ⟨s, fun k => ?_, fun s' hs' => hsu s' fun k => ?_⟩
    · exact (rsT_eq_resG_of_le' _ (U0 k)).trans (hs k)
    · exact (rsT_eq_resG_of_le' _ (U0 k)).symm.trans (hs' k)
  choose c hc using fun a => (glue a).exists
  refine ⟨c, fun W hW f => ?_, fun c' hc' => funext fun a => (glue a).unique ?_ (hc a)⟩
  · apply T.sheaf.eq_of_locally_eq' (fun j : {j : P // j.1.1 ≤ W ∧ j.1.2 ≤ (y ≫ m) ⁻¹ᵁ W} => j.1.1.2)
      ((y ≫ m) ⁻¹ᵁ W) (fun j => homOfLE j.2.2) (cov W _ hW le_rfl)
    intro j
    erw [sheaf_map_eq_rsT, sheaf_map_eq_rsT]
    rw [← rsT_rsT_moduli (d W f) ((y ≫ m).preimage_mono j.2.1) j.1.2.2.2.2, ← hD.res W j.1.1.1 j.2.1 hW f,
      hC j.1 (resG X j.2.1 f), rsT_sum_mul_fintype _ _ j.2.2]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [rsT_rsT_moduli _ ((y ≫ m).preimage_mono hW) j.2.2, hc a j.1, hsub W j.1.1.1 j.2.1 j.1.1.2 j.1.2.2.2.2,
      rsT_pbT_of_le_of_le (O₀ := m ⁻¹ᵁ W) (O₁ := (y ≫ m) ⁻¹ᵁ W) y _ le_rfl j.2.2]
  · intro k
    have e := (Cex k).unique (y₁ := fun a => rsT (c' a) k.1.2) (y₂ := C k) ?_ (hC k)
    · exact congrFun e a
    · intro f
      rw [hc' k.1.1 k.2.2.1 f, rsT_sum_mul_fintype (O₀ := (y ≫ m) ⁻¹ᵁ k.1.1) _ _ k.2.2.2.2]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [rsT_rsT_moduli _ ((y ≫ m).preimage_mono k.2.2.1) k.2.2.2.2, rsT_pbT_of_le_of_le (O₀ := m ⁻¹ᵁ k.1.1) (O₁ := (y ≫ m) ⁻¹ᵁ k.1.1) y _ le_rfl k.2.2.2.2]

end GlobalTheory.InvFieldBasis
