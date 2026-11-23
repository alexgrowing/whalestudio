import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsDenomOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivOfIsPushout
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenericTriv

variable {X Y Z : Scheme.{0}}

theorem cst_spMap {A C : Type} [CommRing A] [CommRing C] (q : Z ⟶ Sp C) (φ : A →+* C) (z : Z) (a : A) :
    cst (q ≫ spMap φ) z a = cst q z (φ a) :=
  (gs_pull q _ z ⊤ trivial _).symm.trans (congrArg (gs q z ⊤) (SecSpread.spMap_appTop φ a))

theorem isUnit_cst {A : Type} [CommRing A] (q : Z ⟶ Sp A) (z : Z) {a : A} (ha : IsUnit a) : IsUnit (cst q z a) := by
  rw [cst, gs_eq q z ⊤ trivial]
  exact ((ha.map _).map _).map _

theorem cst_zero {A : Type} [CommRing A] (q : Z ⟶ Sp A) (z : Z) : cst q z 0 = 0 := by
  rw [cst, gs_eq q z ⊤ trivial, map_zero, map_zero, map_zero]

theorem cst_one {A : Type} [CommRing A] (q : Z ⟶ Sp A) (z : Z) : cst q z 1 = 1 := by
  rw [cst, gs_eq q z ⊤ trivial, map_one, map_one, map_one]

theorem exists_ratio {N : LB X} (hN : N.IsLB) (σ : N.Sec) (π : Y ⟶ X) (t : (N.pull π).Gen) (ht : t.IsGen) :
    ∃ c : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : N.ι), π (r z) ∈ N.U i →
      gs (r ≫ π) z (N.U i) (σ.f i) = gs r z ⊤ c * (gm r z ((N.pull π).U fun _ => i) (t.s fun _ => i)).val := by
  let W : N.ι → Y.Opens := fun i => (N.pull π).U fun _ => i
  have hW : ∀ i, W i ≤ π ⁻¹ᵁ N.U i := fun i y hy => mem_pull.1 hy
  let u : ∀ i, Γ(Y, W i) := fun i => (π.appLE (N.U i) (W i) (hW i)).hom (σ.f i) * ((t.s fun _ => i)⁻¹).val
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : N.ι), r z ∈ W i →
      gs r z (W i) (u i) = gs (r ≫ π) z (N.U i) (σ.f i) * ((gm r z (W i) (t.s fun _ => i))⁻¹).val := by
    intro Z r z i hz
    rw [gs_mul r z _ hz, gs_appLE π _ _ _ r z hz, gs_unit r z _ hz, map_inv]
  obtain ⟨c, hc⟩ := Out.TLinPf.glue W (eq_top_iff.2 fun y _ => by
      obtain ⟨i, hi⟩ := exists_chart hN (π y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, mem_pull.2 hi⟩) u (fun i j => fn_ext fun y hy => by
    have hm : (𝟙 Y ≫ π) y ∈ N.U i ⊓ N.U j := ⟨hW i hy.1, hW j hy.2⟩
    have e := congrArg (gs (𝟙 Y ≫ π) y _) (σ.compat i j)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_unit _ y _ hm] at e
    have e' := gen_trans ht (𝟙 Y) y (j := fun _ => i) (j' := fun _ => j) hy.1 hy.2
    rw [trF, Fintype.prod_unique, zpow_one] at e'
    rw [gs_res _ y _ hy, gs_res _ y _ hy, hu _ _ y i hy.1, hu _ _ y j hy.2, e]
    refine Eq.trans (congrArg (fun q => _ * (q⁻¹).val) e') ?_
    rw [mul_inv, Units.val_mul, _root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul]
    rfl)
  refine ⟨c, fun Z r z i hi => ?_⟩
  have hz : r z ∈ W i := mem_pull.2 hi
  rw [← gs_res r z (le_top : W i ≤ ⊤) hz, hc, hu Z r z i hz, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem exists_sec_isUnit {R k : Type} [CommRing R] [Field k] (j : R →+* k) (hj : j.Flat) [CompactSpace X]
    [QuasiSeparatedSpace X] (f : X ⟶ Sp R) (π : Y ⟶ X) (f' : Y ⟶ Sp k) (H : IsPullback π f' f (spMap j))
    [Nonempty Y] (hs : Function.Surjective f'.appTop.hom) {N : LB X} (hN : N.IsLB) (t : (N.pull π).Gen)
    (ht : t.IsGen) : ∃ σ : N.Sec, ∀ y i, π y ∈ N.U i → IsUnit (gs π y (N.U i) (σ.f i)) := by
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R k j hj X f Y π f' H N hN (genSec t ht)
  choose d hd using fun a => exists_ratio hN (u a) π t ht
  have hd' : ∀ a, ∃ κ : k, ∀ y i, π y ∈ N.U i → gs π y (N.U i) ((u a).f i) =
      cst f' y κ * (gm (𝟙 Y) y ((N.pull π).U fun _ => i) (t.s fun _ => i)).val := fun a => by
    obtain ⟨κ, hκ⟩ := hs (d a)
    obtain ⟨κ, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2 κ
    refine ⟨κ, fun y i hi => ?_⟩
    have := hd a Y (𝟙 Y) y i hi
    rw [← hκ] at this
    exact this.trans (congrArg (· * _) (gs_pull (𝟙 Y) f' y ⊤ trivial _))
  choose κ hκ using hd'
  obtain ⟨a, ha⟩ : ∃ a, κ a ≠ 0 := by
    by_contra! h0
    obtain ⟨y⟩ := ‹Nonempty Y›
    obtain ⟨i, hi⟩ := exists_chart hN (π y)
    have := hu y i hi
    rw [Finset.sum_eq_zero fun a _ => by rw [hκ a y i hi, h0 a, cst_zero, zero_mul, mul_zero]] at this
    exact Units.ne_zero _ ((gs_unit (𝟙 Y) y _ (mem_pull.2 hi) (t.s fun _ => i)).symm.trans this)
  exact ⟨u a, fun y i hi => by rw [hκ a y i hi]; exact (isUnit_cst f' y ha.isUnit).mul (Units.isUnit _)⟩

theorem exists_unit_dvr {R V : Type} [CommRing R] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (g : R →+* V) (hg : Function.Injective g) (f : X ⟶ Sp R) (π : Y ⟶ X) (p : Y ⟶ Sp V) [Smooth p]
    [GeometricallyIntegral p] (hw : π ≫ f = p ≫ spMap g) (e : Sp R ⟶ X) (e' : Sp V ⟶ Y) (he : e' ≫ p = 𝟙 _)
    (he' : e' ≫ π = spMap g ≫ e) {N : LB X} (hN : N.IsLB) (σ : N.Sec) {a : R} (ha : a ≠ 0) (ρ : (N.pull e).Gen)
    (hρ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (i : N.ι), e (r z) ∈ N.U i →
      gs (r ≫ e) z (N.U i) (σ.f i) = cst r z a * (gm r z ((N.pull e).U fun _ => i) (ρ.s fun _ => i)).val)
    (hσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (i : N.ι), (f (r z)).asIdeal = ⊥ → r z ∈ N.U i →
      IsUnit (gs r z (N.U i) (σ.f i)))
    (y : Y) (i : N.ι) (hy : π y ∈ N.U i) : ∃ u, IsUnit u ∧ gs π y (N.U i) (σ.f i) = cst (π ≫ f) y a * u := by
  obtain ⟨K, _, _, _⟩ : ∃ (K : Type) (_ : Field K) (_ : Algebra V K), IsFractionRing V K :=
    ⟨FractionRing V, inferInstance, inferInstance, inferInstance⟩
  let ξ : Sp K ⟶ Sp V := spMap (algebraMap V K)
  obtain ⟨Y', j, q, hK⟩ : ∃ (Y' : Scheme.{0}) (j : Y' ⟶ Y) (q : Y' ⟶ Sp K), IsPullback j q p ξ :=
    ⟨_, _, _, IsPullback.of_hasPullback p ξ⟩
  have hs := IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  obtain ⟨eK, h₁, h₂⟩ : ∃ eK : Sp K ⟶ Y', eK ≫ j = ξ ≫ e' ∧ eK ≫ q = 𝟙 _ :=
    ⟨hK.lift (ξ ≫ e') (𝟙 _) (by rw [Category.assoc, he]; simp), hK.lift_fst _ _ _, hK.lift_snd _ _ _⟩
  have ha' : algebraMap V K (g a) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective V K), map_ne_zero_iff _ hg]; exact ha
  have hinv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp K) (z : Z),
      cst r z (algebraMap V K (g a)) * cst r z (algebraMap V K (g a))⁻¹ = 1 := fun Z r z => by
    rw [← SecSpread.cst_mul, mul_inv_cancel₀ ha', cst_one]
  let U : N.ι → Y.Opens := fun i => π ⁻¹ᵁ N.U i
  let t : ∀ i, Γ(Y', j ⁻¹ᵁ U i) := fun i =>
    constFn q _ (algebraMap V K (g a))⁻¹ * (j.app (U i)).hom ((π.app (N.U i)).hom (σ.f i))
  have ht : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (i : N.ι), r z ∈ j ⁻¹ᵁ U i →
      gs r z (j ⁻¹ᵁ U i) (t i) =
        cst (r ≫ q) z (algebraMap V K (g a))⁻¹ * gs ((r ≫ j) ≫ π) z (N.U i) (σ.f i) := fun Z r z i hz => by
    rw [gs_mul r z _ hz, gs_constFn q _ r z hz, gs_pull r j z _ hz, gs_pull (r ≫ j) π z _ hz]
  obtain ⟨i₀, h₀⟩ := exists_chart hN (e (spMap g (IsLocalRing.closedPoint V)))
  let A : (Sp V).Opens := spMap g ⁻¹ᵁ (N.pull e).U fun _ => i₀
  have hA : A ≤ e' ⁻¹ᵁ U i₀ := fun v hv =>
    (congrArg (fun m : Sp V ⟶ X => m v ∈ N.U i₀) he').mpr (mem_pull.1 hv)
  have hA' : ξ ⁻¹ᵁ A ≤ eK ⁻¹ᵁ j ⁻¹ᵁ U i₀ := fun v hv =>
    (congrArg (fun m : Sp K ⟶ Y => m v ∈ U i₀) h₁).mpr (hA hv)
  have c₁ : ∀ b c, Y'.presheaf.map (homOfLE inf_le_left).op (t b) =
      j.appLE (U b ⊓ U c) (j ⁻¹ᵁ U b ⊓ j ⁻¹ᵁ U c) le_rfl ((π.app (N.U b ⊓ N.U c)).hom (N.g b c).val) *
        Y'.presheaf.map (homOfLE inf_le_right).op (t c) := fun b c => fn_ext fun z hz => by
    have hm : ((𝟙 _ ≫ j) ≫ π) z ∈ N.U b ⊓ N.U c := hz
    have e₁ := congrArg (gs ((𝟙 _ ≫ j) ≫ π) z _) (σ.compat b c)
    rw [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm] at e₁
    refine ((gs_res _ z _ hz _).trans (ht _ _ z b hz.1)).trans (Eq.trans ?_ ((gs_mul _ z _ hz _ _).trans
      (congrArg₂ (· * ·) ((gs_appLE j _ _ _ _ z hz _).trans (gs_pull (𝟙 _ ≫ j) π z (N.U b ⊓ N.U c) hm _))
        ((gs_res _ z _ hz _).trans (ht _ _ z c hz.2)))).symm)
    rw [e₁, mul_left_comm]
  have c₂ : ∀ b, IsUnit (t b) := fun b => Y'.toRingedSpace.isUnit_of_isUnit_germ _ _ fun z hz => by
    refine (congrArg IsUnit ((gs_eq (𝟙 _) z (j ⁻¹ᵁ U b) hz _).symm.trans (ht _ (𝟙 _) z b hz))).mpr
      ((isUnit_cst _ z (inv_ne_zero ha').isUnit).mul (hσ _ _ z b ?_ hz))
    have w : ((𝟙 _ ≫ j) ≫ π) ≫ f = (q ≫ ξ) ≫ spMap g := by
      rw [Category.id_comp, Category.assoc, hw, ← Category.assoc, hK.w]
    refine (congrArg (fun m : Y' ⟶ Sp R => (m z).asIdeal) w).trans ?_
    show Ideal.comap g (Ideal.comap (algebraMap V K) (q z).asIdeal) = ⊥
    rw [Ideal.eq_bot_of_prime (q z).asIdeal, Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K),
      Ideal.comap_bot_of_injective _ hg]
  let u : Γ(Sp V, A) := ((spMap g).app ((N.pull e).U fun _ => i₀)).hom (ρ.s fun _ => i₀).val
  have c₃ : (ξ.appLE A (ξ ⁻¹ᵁ A) le_rfl).hom u = (eK.appLE (j ⁻¹ᵁ U i₀) (ξ ⁻¹ᵁ A) hA').hom (t i₀) := by
    refine fn_ext fun z hz => ?_
    have hm : ((𝟙 (Sp K) ≫ ξ) ≫ spMap g) z ∈ (N.pull e).U fun _ => i₀ := hz
    have k₁ := gs_appLE ξ A (ξ ⁻¹ᵁ A) le_rfl (𝟙 (Sp K)) z hz u
    have k₂ := gs_pull (𝟙 (Sp K) ≫ ξ) (spMap g) z ((N.pull e).U fun _ => i₀) hm (ρ.s fun _ => i₀).val
    have k₃ := gs_unit ((𝟙 (Sp K) ≫ ξ) ≫ spMap g) z ((N.pull e).U fun _ => i₀) hm (ρ.s fun _ => i₀)
    have k₄ := gs_appLE eK (j ⁻¹ᵁ U i₀) (ξ ⁻¹ᵁ A) hA' (𝟙 (Sp K)) z hz (t i₀)
    have k₅ := ht (Sp K) (𝟙 (Sp K) ≫ eK) z i₀ (hA' hz)
    have w : (((𝟙 (Sp K) ≫ eK) ≫ j) ≫ π) = ((𝟙 (Sp K) ≫ ξ) ≫ spMap g) ≫ e := by
      simp only [Category.id_comp, Category.assoc]
      rw [← Category.assoc, h₁, Category.assoc, he']
    rw [w, hρ (Sp K) ((𝟙 (Sp K) ≫ ξ) ≫ spMap g) z i₀ (mem_pull.1 hm), cst_spMap, cst_spMap,
      Category.assoc (𝟙 (Sp K)) eK q, h₂, Category.comp_id,
      ← _root_.mul_assoc, (mul_comm _ _).trans (hinv (Sp K) (𝟙 (Sp K)) z), _root_.one_mul] at k₅
    exact (k₁.trans (k₂.trans k₃)).trans (k₄.trans k₅).symm
  have c₄ : IsUnit u := (Units.isUnit _).map _
  have c₅ : IsLocalRing.closedPoint V ∈ A := mem_pull (F := e).2 h₀
  obtain ⟨s, hsu, -, hsr⟩ := (DvrModel.existsUnique_isUnit_appLE_eq hK hs (U := U)
    (g := fun a b => (π.app (N.U a ⊓ N.U b)).hom (N.g a b).val) (W := fun i => j ⁻¹ᵁ U i) (fun _ => rfl)
    (fun x => exists_chart hN (π x)) (fun a b => (Units.isUnit _).map _) (r := t) c₁ c₂
    he h₁ (a₀ := i₀) (A := A) c₅ hA (A' := ξ ⁻¹ᵁ A) rfl hA' c₄ c₃).exists
  have key : (π.app (N.U i)).hom (σ.f i) = constFn p (U i) (g a) * s i :=
    SecSpread.ext_generic hK (W := U i) fun z hz => by
      have e₁ := (gs_appLE j _ _ _ (𝟙 _) z hz _).symm.trans
        ((congrArg (gs (𝟙 _) z _) (hsr i)).trans (ht _ (𝟙 _) z i hz))
      simp only [Category.id_comp] at e₁
      refine (gs_pull j π z _ hz _).trans (Eq.trans ?_ ((gs_mul j z _ hz _ _).trans (congrArg₂ (· * ·)
        (gs_constFn p _ j z hz _) e₁)).symm)
      rw [show j ≫ p = q ≫ ξ from hK.w, cst_spMap, ← _root_.mul_assoc, hinv, _root_.one_mul]
  refine ⟨gs (𝟙 Y) y (U i) (s i), ?_, ?_⟩
  · rw [gs_eq (𝟙 Y) y (U i) hy]
    exact ((hsu i).map _).map _
  · refine (gs_pull (𝟙 Y) π y _ hy _).symm.trans ((congrArg (gs (𝟙 Y) y (U i)) key).trans
      ((gs_mul (𝟙 Y) y (U i) hy _ _).trans (congrArg (· * _) ((gs_constFn p (U i) (𝟙 Y) y hy _).trans ?_))))
    rw [hw, cst_spMap, Category.id_comp]

theorem exists_gen_of_fibre {R k : Type} [CommRing R] [IsDedekindDomain R] [Field k] (j : R →+* k)
    (hj : Function.Injective j) [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ Sp R) [Smooth f]
    [GeometricallyIntegral f] (e : Sp R ⟶ X) (he : e ≫ f = 𝟙 _) (π : Y ⟶ X) (f' : Y ⟶ Sp k)
    (H : IsPullback π f' f (spMap j)) (hs : Function.Surjective f'.appTop.hom) {N : LB X} (hN : N.IsLB)
    (ρ : (N.pull e).Gen) (hρ : ρ.IsGen) (t : (N.pull π).Gen) (ht : t.IsGen) : ∃ u : N.Gen, u.IsGen := by
  have hef : ∀ v, f (e v) = v := fun v => congrArg (fun m : Sp R ⟶ Sp R => m v) he
  have lift : ∀ x : X, (f x).asIdeal = ⊥ → ∃ y, π y = x := fun x hx => by
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback H x (⊥ : PrimeSpectrum k)
      (PrimeSpectrum.ext (hx.trans (Ideal.comap_bot_of_injective j hj).symm))
    exact ⟨y, hy⟩
  let ξ : Sp R := (⊥ : PrimeSpectrum R)
  have hξ : (f (e ξ)).asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal (hef ξ)
  have : Nonempty Y := ⟨(lift _ hξ).choose⟩
  have hflat : j.Flat := by
    let _ := j.toAlgebra
    have : FaithfulSMul R k := (faithfulSMul_iff_algebraMap_injective R k).2 hj
    exact inferInstanceAs (Module.Flat R k)
  obtain ⟨σ, hσ⟩ := exists_sec_isUnit j hflat f π f' H hs hN t ht
  have hσ₁ : ∀ x i, (f x).asIdeal = ⊥ → x ∈ N.U i → IsUnit (gs (𝟙 X) x (N.U i) (σ.f i)) := fun x i hx hi => by
    obtain ⟨y, rfl⟩ := lift x hx
    have := hσ y i hi
    rwa [gs_stalkMap π y _ hi, isUnit_map_iff] at this
  have hσ₂ : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (i : N.ι), (f (r z)).asIdeal = ⊥ → r z ∈ N.U i →
      IsUnit (gs r z (N.U i) (σ.f i)) := fun Z r z i hz hi => by
    rw [gs_stalkMap r z _ hi]
    exact (hσ₁ _ i hz hi).map _
  obtain ⟨c, hc⟩ := exists_ratio hN σ e ρ hρ
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 c
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_chart hN (e ξ)
    have h := hσ₂ _ (𝟙 _ ≫ e) ξ i hξ hi
    rw [hc _ (𝟙 _) ξ i hi] at h
    exact not_isUnit_zero ((congrArg IsUnit (cst_zero (𝟙 (Sp R)) ξ)).mp (isUnit_of_mul_isUnit_left h))
  have dvd : ∀ i, ∀ x ∈ N.U i, cst f x a ∣ gs (𝟙 X) x (N.U i) (σ.f i) ∧ gs (𝟙 X) x (N.U i) (σ.f i) ∣ cst f x a := by
    intro i x hx
    by_cases h0 : (f x).asIdeal = ⊥
    · refine ⟨IsUnit.dvd ?_, (hσ₁ x i h0 hx).dvd⟩
      obtain ⟨y, rfl⟩ := lift x h0
      have h : IsUnit (cst (π ≫ f) y a) := by
        rw [H.w, cst_spMap]
        exact isUnit_cst _ _ ((map_ne_zero_iff j hj).2 ha).isUnit
      rw [cst, ← gs_pull π f y ⊤ trivial, gs_stalkMap π y (f ⁻¹ᵁ ⊤) trivial, isUnit_map_iff] at h
      exact (congrArg IsUnit (gs_pull (𝟙 X) f (π y) ⊤ trivial _)).mp h
    · let V := Localization.AtPrime (f x).asIdeal
      have : IsDiscreteValuationRing V :=
        IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h0 V
      have hg : Function.Injective (algebraMap R V) :=
        IsLocalization.injective V (f x).asIdeal.primeCompl_le_nonZeroDivisors
      have H' := IsPullback.of_hasPullback f (spMap (algebraMap R V))
      have : Flat (spMap (algebraMap R V)) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
      obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback H' x (IsLocalRing.closedPoint V)
        (PrimeSpectrum.ext (Localization.AtPrime.comap_maximalIdeal (I := (f x).asIdeal)).symm)
      have hy' : pullback.fst f (spMap (algebraMap R V)) y ∈ N.U i := hy.symm ▸ hx
      obtain ⟨u, hu, h⟩ := exists_unit_dvr (algebraMap R V) hg f _ _ H'.w e
        (H'.lift (spMap (algebraMap R V) ≫ e) (𝟙 _) (by rw [Category.assoc, he]; simp)) (H'.lift_snd _ _ _)
        (H'.lift_fst _ _ _) hN σ ha ρ hc hσ₂ y i hy'
      rw [cst, ← gs_pull _ f y ⊤ trivial, gs_stalkMap _ y _ hy', gs_stalkMap _ y (f ⁻¹ᵁ ⊤) trivial,
        gs_pull (𝟙 X) f _ ⊤ trivial, Category.id_comp] at h
      have d₁ := dvd_descend _ y (Dvd.intro _ h.symm)
      have d₂ := dvd_descend _ y ((dvd_of_eq h).trans (hu.mul_right_dvd.2 dvd_rfl))
      clear h
      generalize pullback.fst f (spMap (algebraMap R V)) y = x' at hy hy' d₁ d₂
      subst hy
      exact ⟨d₁, d₂⟩
  obtain ⟨s, hs'⟩ := exists_div_sec f ha σ fun i x hx => (dvd i x hx).1
  have hu : ∀ i, IsUnit (s.f i) := fun i => X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => by
    obtain ⟨w, hw⟩ := (dvd i x hx).2
    rw [hs' i, gs_mul _ x _ hx, gs_constFn f _ _ x hx, Category.id_comp, _root_.mul_assoc] at hw
    have h1 := cst_regular f x ha ((_root_.mul_one _).trans hw)
    exact (congrArg IsUnit (gs_eq (𝟙 X) x (N.U i) hx _)).mp (IsUnit.of_mul_eq_one w h1.symm)
  exact ⟨⟨fun i => (hu i).unit⟩, fun i i' => Units.ext (s.compat i i')⟩

theorem exists_gen_of_generic_fibre : Out.Laws → ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (A : Over (Sp R)) [GrpObj A] (N : LB A.left) (k : Type) [Field k] (j : R →+* k), IsAbelianScheme A → N.IsLB → Function.Injective j → (∃ t : (N.pull (eSec A)).Gen, t.IsGen) → (∃ t : (N.pull (pullback.fst A.hom (spMap j))).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro hL R _ _ A _ N k _ j hA hN hj ⟨ρ, hρ⟩ ⟨t, ht⟩
  have := hA.smooth
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  exact exists_gen_of_fibre j hj A.hom (eSec A) (Over.w η[A]) _ _ (IsPullback.of_hasPullback A.hom (spMap j))
    (Out.TLinPf.const_pullback hL.globalFns (spMap j) A hA) hN ρ hρ t ht

end GlobalTheory.GenericTriv
