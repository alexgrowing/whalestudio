import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfSqZeroBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CechPic

theorem pow_add_sqZero {A : Type*} [CommRing A] (v M : A) (hM : M * M = 0) (k : ℕ) :
    (v + M) ^ (k + 1) = v ^ (k + 1) + (k + 1) * M * v ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]; push_cast
    linear_combination ((k : A) + 1) * v ^ k * hM

theorem sqZero_root_correction_mul_pow_eq_zero {A : Type*} [CommRing A] {G Sa Sb Na Nb H M : A} (k : ℕ)
    (hS : Sa = G ^ (k + 1) * Sb) (hNa : Na = Sa - 1) (hNb : Nb = Sb - 1) (hNa2 : Na * Na = 0)
    (hNb2 : Nb * Nb = 0) (hH : ((k + 1 : ℕ) : A) * H = 1) (hM : M = (1 + Na * H) - G * (1 + Nb * H))
    (hM2 : M * M = 0) : M * (G * (1 + Nb * H)) ^ k = 0 := by
  push_cast at hH
  have r1 : ∀ N : A, N * N = 0 → (1 + N * H) ^ (k + 1) = 1 + N := fun N hN => by
    rw [pow_add_sqZero 1 (N * H) (by linear_combination H ^ 2 * hN) k, one_pow, one_pow]
    linear_combination N * hH
  have e1 : (1 + Na * H) ^ (k + 1) = Sa := by rw [r1 Na hNa2]; linear_combination hNa
  have e2 : (G * (1 + Nb * H)) ^ (k + 1) = G ^ (k + 1) * Sb := by
    rw [mul_pow, r1 Nb hNb2]; linear_combination G ^ (k + 1) * hNb
  have e3 := pow_add_sqZero (G * (1 + Nb * H)) M hM2 k
  have hu : G * (1 + Nb * H) + M = 1 + Na * H := by linear_combination hM
  rw [hu] at e3
  linear_combination H * (e1 - e2 + hS - e3) - M * (G * (1 + Nb * H)) ^ k * hH

end GlobalTheory.CechPic

namespace GlobalTheory.CechPic

open scoped CategoryTheory.Obj
open IsLocalRing

theorem eq_zero_of_sqZero_baseChange_nsmul : ∀ (k : ℕ) (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → IsUnit ((k + 1 : ℕ) : R) →
    ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s₀ : X₀ ⟶ Sp R₀) (i : X₀ ⟶ X), IsPullback i s₀ s (spMap π) →
    Function.Surjective i.appTop.hom → ∀ m : GlobalTheory.CechPic.Pic X, GlobalTheory.CechPic.pull i m = 0 →
    (k + 1) • m = 0 → m = 0 := by
  intro k R R₀ _ _ π hπ hk h2 X X₀ s s₀ i hP hsurj m hm hm2
  haveI : IsClosedImmersion (spMap π) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom π) hπ
  haveI : IsClosedImmersion i :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hP.flip inferInstance
  haveI : Surjective i := GlobalTheory.LiftSys.surjective_of_isPullback_sqZero (I := RingHom.ker π)
    (by rw [hk]; rfl) hπ rfl hP
  have hsq : ∀ (W : X.Opens) (x y : Γ(X, W)), (i.app W).hom x = 0 → (i.app W).hom y = 0 → x * y = 0 :=
    GlobalTheory.SquareZero.mul_eq_zero_of_app_eq_zero R R₀ π hπ hk X X₀ s s₀ i hP
  obtain ⟨D, hD, rfl, hD1⟩ := exists_cocycle_one_on_thickening X X₀ i m hm
  have h2X : IsUnit ((k + 1 : ℕ) : Γ(X, ⊤)) := by
    have := h2.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
    rwa [map_natCast] at this
  rw [← cls_lbPow hD (k + 1) (LB.isLB_linComb hD _ _), cls_eq_zero_iff] at hm2
  obtain ⟨σ₂, hσ₂⟩ := hm2
  have hle : ∀ a, D.U a ≤ (lbPow D (k + 1)).U (fun _ => a) := fun a y hy =>
    Set.mem_iInter.2 fun _ => hy
  let σ : ∀ a, Γ(X, D.U a)ˣ := fun a => res (hle a) (σ₂.s (fun _ => a))
  have hσ : ∀ a b, res (inf_le_left : D.U a ⊓ D.U b ≤ D.U a) (σ a) =
      D.g a b ^ (k + 1) * res inf_le_right (σ b) := by
    intro a b
    refine unit_ext fun y hy => ?_
    have e := (isGen_iff_germ σ₂).1 hσ₂ y (fun _ => a) (fun _ => b) (hle a hy.1) (hle b hy.2)
    have hg := gm_linComb D (fun _ : PUnit => 𝟙 X) (fun _ => ((k + 1 : ℕ) : ℤ)) (𝟙 X) y
      (fun _ => a) (fun _ => b) (hle a hy.1) (hle b hy.2)
    rw [Fintype.prod_unique, Category.id_comp, zpow_natCast] at hg
    erw [hg] at e
    rw [map_mul, map_pow, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy]
    dsimp only [σ]
    erw [gm_res (𝟙 X) y (hle a) hy.1, gm_res (𝟙 X) y (hle b) hy.2]
    exact e
  have hg1 : ∀ a b (y : X₀) (hy : i y ∈ D.U a ⊓ D.U b), gm i y _ (D.g a b) = 1 := by
    intro a b y hy
    have e := gm_pull (𝟙 X₀) i y (D.U a ⊓ D.U b) hy (D.g a b)
    rw [Category.id_comp, hD1 a b, map_one] at e
    exact e.symm
  have hσi : ∀ a b (y : X₀) (ha : i y ∈ D.U a) (hb : i y ∈ D.U b), gm i y _ (σ a) = gm i y _ (σ b) := by
    intro a b y ha hb
    have hab : i y ∈ D.U a ⊓ D.U b := ⟨ha, hb⟩
    rw [← gm_res i y (inf_le_left : D.U a ⊓ D.U b ≤ D.U a) hab, hσ a b, map_mul, map_pow,
      hg1 a b y hab, gm_res i y inf_le_right hab, one_pow, _root_.one_mul]
  have hpi : ∀ a (y : X₀) (ha : i y ∈ D.U a), gm (𝟙 X₀) y (i ⁻¹ᵁ D.U a) (pullU i _ (σ a)) = gm i y _ (σ a) := by
    intro a y ha
    rw [gm_pull (𝟙 X₀) i y _ ha, Category.id_comp]
  obtain ⟨U₀, hU₀⟩ := glue_unit (X := X₀) (i ⁻¹ᵁ ⊤) (fun a => i ⁻¹ᵁ D.U a) (fun a _ _ => trivial)
    (fun y _ => TopologicalSpace.Opens.mem_iSup.2 (exists_chart hD (i y))) (fun a => pullU i _ (σ a))
    (fun a b y hy => by rw [hpi a y hy.1, hpi b y hy.2]; exact hσi a b y hy.1 hy.2)
  obtain ⟨v, hv⟩ := hsurj (show Γ(X₀, ⊤) from U₀.val)
  have hvu : IsUnit v := X.toRingedSpace.isUnit_of_isUnit_germ ⊤ v fun x hx => by
    obtain ⟨y, rfl⟩ := Surjective.surj (f := i) x
    have h1 : IsUnit ((i.stalkMap y).hom ((X.presheaf.germ ⊤ (i y) hx).hom v)) := by
      rw [Scheme.Hom.germ_stalkMap_apply]
      erw [hv]
      exact U₀.isUnit.map _
    exact isUnit_of_map_unit _ _ h1
  let Vu : Γ(X, ⊤)ˣ := hvu.unit
  have hVu : ∀ (y : X₀), gm i y ⊤ Vu = gm (𝟙 X₀) y (i ⁻¹ᵁ ⊤) U₀ := by
    intro y
    have e := gm_pull (𝟙 X₀) i y ⊤ trivial Vu
    rw [Category.id_comp] at e
    rw [← e]
    congr 1
    exact Units.ext hv
  let σ' : ∀ a, Γ(X, D.U a)ˣ := fun a => σ a * res (le_top : D.U a ≤ ⊤) Vu⁻¹
  have hσ'1 : ∀ a, (i.app (D.U a)).hom (σ' a).val = 1 := by
    intro a
    have e : pullU i (D.U a) (σ' a) = 1 := unit_ext fun y hy => by
      rw [map_one, gm_pull (𝟙 X₀) i y _ hy, Category.id_comp]
      dsimp only [σ']
      rw [map_mul, gm_res i y le_top hy, map_inv, hVu y, ← hpi a y hy, ← hU₀ a]
      erw [gm_res (𝟙 X₀) y (fun _ _ => trivial : i ⁻¹ᵁ D.U a ≤ i ⁻¹ᵁ ⊤) hy]
      exact mul_inv_cancel _
    exact congrArg Units.val e
  have hσ' : ∀ a b, res (inf_le_left : D.U a ⊓ D.U b ≤ D.U a) (σ' a) =
      D.g a b ^ (k + 1) * res inf_le_right (σ' b) := by
    intro a b
    dsimp only [σ']
    rw [map_mul, map_mul, hσ a b]
    simp only [res_res, _root_.mul_assoc]
  let n : ∀ a, Γ(X, D.U a) := fun a => (σ' a).val - 1
  have hn0 : ∀ a, (i.app (D.U a)).hom (n a) = 0 := fun a => by
    simp only [n, map_sub, map_one, hσ'1 a, sub_self]
  have hn2 : ∀ a, n a * n a = 0 := fun a => hsq _ _ _ (hn0 a) (hn0 a)
  let Hh : ∀ a, Γ(X, D.U a) := fun a => (res (le_top : D.U a ≤ ⊤) h2X.unit⁻¹).val
  let t : ∀ a, Γ(X, D.U a) := fun a => 1 + n a * Hh a
  have ht : ∀ a, IsUnit (t a) := fun a =>
    IsUnit.of_mul_eq_one (1 - n a * Hh a) (by linear_combination (-(Hh a * Hh a)) * hn2 a)
  have hti : ∀ a, (i.app (D.U a)).hom (t a) = 1 := fun a => by
    simp only [t, map_add, map_one, map_mul, hn0 a, zero_mul, add_zero]
  refine (cls_eq_zero_iff hD).2 ⟨⟨fun a => (ht a).unit⟩, fun a b => ?_⟩
  apply Units.ext
  let ρa := (X.presheaf.map (homOfLE (inf_le_left : D.U a ⊓ D.U b ≤ D.U a)).op).hom
  let ρb := (X.presheaf.map (homOfLE (inf_le_right : D.U a ⊓ D.U b ≤ D.U b)).op).hom
  let ρt := (X.presheaf.map (homOfLE (le_top : D.U a ⊓ D.U b ≤ ⊤)).op).hom
  show ρa (t a) = (D.g a b).val * ρb (t b)
  let Hc : Γ(X, D.U a ⊓ D.U b) := (res (le_top : D.U a ⊓ D.U b ≤ ⊤) h2X.unit⁻¹).val
  have hHa : ρa (Hh a) = Hc := congrArg Units.val (res_res inf_le_left le_top h2X.unit⁻¹)
  have hHb : ρb (Hh b) = Hc := congrArg Units.val (res_res inf_le_right le_top h2X.unit⁻¹)
  have hH : ((k + 1 : ℕ) : Γ(X, D.U a ⊓ D.U b)) * Hc = 1 := by
    show ((k + 1 : ℕ) : Γ(X, D.U a ⊓ D.U b)) * ρt h2X.unit⁻¹.val = 1
    rw [show ((k + 1 : ℕ) : Γ(X, D.U a ⊓ D.U b)) = ρt ((k + 1 : ℕ) : Γ(X, ⊤)) from (map_natCast ρt _).symm,
      ← map_mul, h2X.mul_val_inv, map_one]
  have hS : ρa (σ' a).val = (D.g a b).val ^ (k + 1) * ρb (σ' b).val := by
    have := congrArg Units.val (hσ' a b)
    rw [Units.val_mul, Units.val_pow_eq_pow_val] at this
    exact this
  have hNa : ρa (n a) = ρa (σ' a).val - 1 := by simp only [n, map_sub, map_one]
  have hNb : ρb (n b) = ρb (σ' b).val - 1 := by simp only [n, map_sub, map_one]
  have hNa2 : ρa (n a) * ρa (n a) = 0 := by rw [← map_mul, hn2 a, map_zero]
  have hNb2 : ρb (n b) * ρb (n b) = 0 := by rw [← map_mul, hn2 b, map_zero]
  have hTa : ρa (t a) = 1 + ρa (n a) * Hc := by simp only [t, map_add, map_one, map_mul, hHa]
  have hTb : ρb (t b) = 1 + ρb (n b) * Hc := by simp only [t, map_add, map_one, map_mul, hHb]
  have hG1 : (i.app (D.U a ⊓ D.U b)).hom (D.g a b).val = 1 := congrArg Units.val (hD1 a b)
  have hM0 : (i.app (D.U a ⊓ D.U b)).hom (ρa (t a) - (D.g a b).val * ρb (t b)) = 0 := by
    rw [map_sub, map_mul, app_restrict, app_restrict, hti a, hti b, hG1, map_one, map_one,
      _root_.one_mul, sub_self]
  have key := sqZero_root_correction_mul_pow_eq_zero k hS hNa hNb hNa2 hNb2 hH (by rw [hTa, hTb]) (hsq _ _ _ hM0 hM0)
  have hu : IsUnit (((D.g a b).val * (1 + ρb (n b) * Hc)) ^ k) :=
    ((D.g a b).isUnit.mul (hTb ▸ (ht b).map ρb)).pow k
  exact sub_eq_zero.1 (hu.mul_left_eq_zero.1 key)

end GlobalTheory.CechPic

namespace GlobalTheory.CechPic

theorem exists_isGen_of_lbPow_of_sqZero_abelianScheme : ∀ (T : Type) [CommRing T] [IsLocalRing T] (e : T),
    (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T →
    ∀ (A : Over (Sp T)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ k : ℕ,
    IsUnit (k : T) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) →
    ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (f' : X' ⟶ Sp (T ⧸ Ideal.span {e})),
    IsPullback π f' A.hom (spMap (Ideal.Quotient.mk (Ideal.span {e}))) →
    (∃ t : (M.pull π).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
  intro T _ _ e hme hem A _ hA M hM k hk hpow X' π f' hP hπ
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := by
    cases k with
    | zero => exact absurd hk (by rw [Nat.cast_zero]; exact not_isUnit_zero)
    | succ k => exact ⟨k, rfl⟩
  set q := Ideal.Quotient.mk (Ideal.span {e})
  have hee : e * e = 0 := hme e hem
  have hker : RingHom.ker q ^ 2 = ⊥ := by
    rw [Ideal.mk_ker, Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot, pow_two, hee]
  haveI : IsClosedImmersion (spMap q) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom q) Ideal.Quotient.mk_surjective
  have hq : Function.Surjective (spMap q).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (spMap q)).2
  have hf' : Function.Bijective f'.appTop.hom :=
    GlobalTheory.AbLaw.CubeOpen.bijective_appTop GlobalTheory.globalFns_holds A hA hP
  have hsurj : Function.Surjective π.appTop.hom := by
    intro w
    obtain ⟨c, rfl⟩ := hf'.2 w
    obtain ⟨d, rfl⟩ := hq c
    refine ⟨A.hom.appTop d, ?_⟩
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, hP.w]
  have hpull : pull π (cls M hM) = 0 := by
    rw [← cls_pull hM π (pull_isLB hM π), cls_eq_zero_iff]
    exact hπ
  have hnsmul : (k + 1) • cls M hM = 0 := by
    have h := cls_linComb hM (fun _ : Fin (k + 1) => 𝟙 A.left) (fun _ => 1) (LB.isLB_linComb hM _ _)
    have h0 : cls (LB.LinComb M (fun _ : Fin (k + 1) => 𝟙 A.left) (fun _ => 1)) (LB.isLB_linComb hM _ _) = 0 :=
      (cls_eq_zero_iff _).2 hpow
    rw [h0] at h
    simpa [pull_id] using h.symm
  exact (cls_eq_zero_iff hM).1 (eq_zero_of_sqZero_baseChange_nsmul k T (T ⧸ Ideal.span {e}) q
    Ideal.Quotient.mk_surjective hker hk A.left X' A.hom f' π hP hsurj _ hpull hnsmul)

end GlobalTheory.CechPic
