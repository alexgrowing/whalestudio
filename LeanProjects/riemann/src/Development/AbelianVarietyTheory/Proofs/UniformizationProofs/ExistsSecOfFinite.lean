import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SecOnBasicOpenLocalization

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlatNorm

open TopologicalSpace GlobalTheory.FiniteAmple GlobalTheory.LB GlobalTheory.LBGerm

section Algebra

variable {A B A' B' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']

def nm (φ : A →+* B) : B →* A := letI := φ.toAlgebra; Algebra.norm A

theorem nm_of_isPushout {φ : A →+* B} {α : A →+* A'} {β : B →+* B'} {φ' : A' →+* B'}
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (h : FinFree φ) (b : B) : nm φ' (β b) = α (nm φ b) := by
  algebraize [φ, α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  haveI : Module.Finite A B := h.1
  haveI : Module.Free A B := h.2
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  change LinearMap.det (Algebra.lmul A' B' (β b)) = algebraMap A A' (LinearMap.det (Algebra.lmul A B b))
  rw [← LinearMap.det_baseChange, ← LinearMap.det_conj _ hb.equiv]
  congr 1
  ext y
  obtain ⟨t, rfl⟩ := hb.equiv.surjective y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [IsBaseChange.equiv_tmul]; rfl
  | add s t hs ht => simp only [map_add, hs, ht]

theorem isUnit_of_nm {φ : A →+* B} (h : FinFree φ) {b : B} (hb : IsUnit (nm φ b)) : IsUnit b := by
  letI := φ.toAlgebra
  haveI : Module.Finite A B := h.1
  haveI : Module.Free A B := h.2
  exact Algebra.lmul_isUnit_iff.1 ((LinearMap.isUnit_iff_isUnit_det (Algebra.lmul A B b)).2 hb)

end Algebra

variable {X Y : Scheme.{0}} (π : Y ⟶ X)

theorem exists_preimage_le [IsFinite π] {x : X} {O : Y.Opens} (h : ∀ y, π y = x → y ∈ O) :
    ∃ V : X.Opens, x ∈ V ∧ π ⁻¹ᵁ V ≤ O := by
  refine ⟨⟨(π '' (O : Set Y)ᶜ)ᶜ, (π.isClosedMap _ O.isOpen.isClosed_compl).isOpen_compl⟩, ?_, fun y hy => ?_⟩
  · rintro ⟨y, hy, e⟩
    exact hy (h y e)
  · by_contra hO
    exact hy ⟨y, hO, rfl⟩

variable [IsFinite π] [Flat π] [IsLocallyNoetherian X]

abbrev FreeOpen (V : X.Opens) : Type := {W : X.Opens // IsAffineOpen W ∧ W ≤ V ∧ FinFree (π.app W).hom}

theorem le_iSup_freeOpen (V : X.Opens) : V ≤ ⨆ W : FreeOpen π V, W.1 := fun x hx => by
  obtain ⟨W, h₁, h₂, h₃, h₄⟩ := exists_finFree_app π hx
  exact Opens.mem_iSup.2 ⟨⟨W, h₁, h₃, h₄⟩, h₂⟩

theorem ext_freeOpen {V : X.Opens} {a b : Γ(X, V)}
    (h : ∀ W : FreeOpen π V, resG X W.2.2.1 a = resG X W.2.2.1 b) : a = b :=
  fun_ext_of_cover _ (fun W : FreeOpen π V => W.2.2.1) (le_iSup_freeOpen π V) h

omit [Flat π] [IsLocallyNoetherian X] in
theorem resG_nm {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V)
    (hF : FinFree (π.app V).hom) (b : Γ(Y, π ⁻¹ᵁ V)) :
    resG X h (nm (π.app V).hom b) = nm (π.app W).hom (resG Y (π.preimage_mono h) b) :=
  (nm_of_isPushout (isPushout_app π hV hW h) hF b).symm

theorem exists_normFun (V : X.Opens) (b : Γ(Y, π ⁻¹ᵁ V)) : ∃ a : Γ(X, V), ∀ W : FreeOpen π V,
    resG X W.2.2.1 a = nm (π.app W.1).hom (resG Y (π.preimage_mono W.2.2.1) b) :=
  exists_fun_of_cover _ (fun W : FreeOpen π V => W.2.2.1) (le_iSup_freeOpen π V) _ fun W W' =>
    ext_freeOpen π fun O => by
      rw [resG_resG, resG_resG, resG_nm π W.2.1 O.2.1 _ W.2.2.2, resG_nm π W'.2.1 O.2.1 _ W'.2.2.2,
        resG_resG, resG_resG]

def norm (V : X.Opens) : Γ(Y, π ⁻¹ᵁ V) →* Γ(X, V) where
  toFun b := (exists_normFun π V b).choose
  map_one' := ext_freeOpen π fun W => by
    rw [(exists_normFun π V 1).choose_spec W, map_one, map_one, map_one]
  map_mul' a b := ext_freeOpen π fun W => by
    rw [(exists_normFun π V _).choose_spec W, map_mul, map_mul, map_mul,
      (exists_normFun π V a).choose_spec W, (exists_normFun π V b).choose_spec W]

theorem resG_norm_free {V : X.Opens} (b : Γ(Y, π ⁻¹ᵁ V)) (W : FreeOpen π V) :
    resG X W.2.2.1 (norm π V b) = nm (π.app W.1).hom (resG Y (π.preimage_mono W.2.2.1) b) :=
  (exists_normFun π V b).choose_spec W

theorem resG_norm {V W : X.Opens} (h : W ≤ V) (b : Γ(Y, π ⁻¹ᵁ V)) :
    resG X h (norm π V b) = norm π W (resG Y (π.preimage_mono h) b) :=
  ext_freeOpen π fun O => by
    rw [resG_norm_free, resG_resG, resG_resG]
    exact resG_norm_free π b ⟨O.1, O.2.1, O.2.2.1.trans h, O.2.2.2⟩

theorem mem_basicOpen_norm {V : X.Opens} (b : Γ(Y, π ⁻¹ᵁ V)) {x : X} (hx : x ∈ V) :
    x ∈ X.basicOpen (norm π V b) ↔ ∀ y, π y = x → y ∈ Y.basicOpen b := by
  constructor
  · rintro h y rfl
    obtain ⟨W, h₁, h₂, h₃, h₄⟩ := exists_finFree_app π h
    have hW := h₃.trans (X.basicOpen_le _)
    have u : IsUnit (resG X hW (norm π V b)) := by
      rw [← resG_resG (X.basicOpen_le _) h₃]
      exact (X.toRingedSpace.isUnit_res_basicOpen _).map _
    have u' := isUnit_of_nm h₄ ((resG_norm_free π b ⟨W, h₁, hW, h₄⟩) ▸ u)
    have e := (Y.basicOpen_res b _).symm.trans (Y.basicOpen_of_isUnit u')
    exact (e.ge h₂).2
  · intro h
    obtain ⟨O, hO, hle⟩ := exists_preimage_le π h
    have hW : O ⊓ V ≤ V := inf_le_right
    have h₃ : π ⁻¹ᵁ (O ⊓ V) ≤ Y.basicOpen b := (π.preimage_mono inf_le_left).trans hle
    have u : IsUnit (resG Y (π.preimage_mono hW) b) := by
      rw [← resG_resG (Y.basicOpen_le _) h₃]
      exact (Y.toRingedSpace.isUnit_res_basicOpen _).map _
    have u' := u.map (norm π _)
    rw [← resG_norm π hW] at u'
    have e := (X.basicOpen_res _ _).symm.trans (X.basicOpen_of_isUnit u')
    exact (e.ge ⟨hO, hx⟩).2

section Generators

variable {Z : Scheme.{0}} {L : LB Z}

def germAt {O : Z.Opens} (i : L.ι) (y : Z) (hy : y ∈ O ⊓ L.U i) : SecOn L O →+ Z.presheaf.stalk y where
  toFun t := gs (𝟙 Z) y _ (coord t i)
  map_zero' := gs_zero _ y _ hy
  map_add' _ _ := gs_add _ y _ hy _ _

theorem germAt_smul {O : Z.Opens} (i : L.ι) (y : Z) (hy : y ∈ O ⊓ L.U i) (a : Γ(Z, O)) (t : SecOn L O) :
    germAt i y hy (a • t) = gs (𝟙 Z) y O a * germAt i y hy t :=
  (gs_mul _ y _ hy _ _).trans (congrArg (· * _) (gs_res _ y _ hy _))

theorem germAt_restrict {O O' : Z.Opens} (h : O' ≤ O) (i : L.ι) (y : Z) (hy : y ∈ O' ⊓ L.U i) (t : SecOn L O) :
    germAt i y hy (SecOn.restrict L h t) = germAt i y ⟨h hy.1, hy.2⟩ t :=
  gs_res (𝟙 Z) y (inf_le_inf_right _ h) hy _

theorem isUnit_germAt_iff {O : Z.Opens} (i j : L.ι) (y : Z) (hi : y ∈ O ⊓ L.U i) (hj : y ∈ O ⊓ L.U j)
    (t : SecOn L O) : IsUnit (germAt i y hi t) ↔ IsUnit (germAt j y hj t) := by
  have e : germAt i y hi t = _ * germAt j y hj t := gs_secOn (coord_mem t) y i j hi.1 hi.2 hj.2
  rw [e, Units.isUnit_units_mul]

theorem exists_sec_of_finite (hL : L.IsLB) {W : Z.Opens} (hW : IsAffineOpen W) {F : Set Z} (hF : F.Finite)
    (hd : _root_.IsDiscrete F) (hFW : F ⊆ W) : ∃ t : SecOn L W, ∀ y ∈ F, ∃ i, y ∈ Z.basicOpen (coord t i) := by
  classical
  choose i hi using exists_chart hL
  have key : ∀ y : F, ∃ (a : Γ(Z, W)) (t : SecOn L W), y.1 ∈ Z.basicOpen a ∧
      (∀ y' : F, y'.1 ∈ Z.basicOpen a → y' = y) ∧ IsUnit (germAt (i y) y.1 ⟨hFW y.2, hi y⟩ t) := by
    intro y
    obtain ⟨O, hO, e⟩ := isDiscrete_iff_forall_exists_isOpen.mp hd y.1 y.2
    have hyO : y.1 ∈ O := (e.ge rfl).1
    obtain ⟨a, ha, hya⟩ := hW.exists_basicOpen_le (V := ⟨O, hO⟩ ⊓ L.U (i y)) ⟨y.1, hyO, hi y⟩ (hFW y.2)
    have hU : Z.basicOpen a ≤ L.U (i y) := ha.trans inf_le_right
    obtain ⟨k, t, ht⟩ := (secOn_basicOpen_localization Z L W _ a (Z.basicOpen_le a) hL hW.isCompact
      hW.isQuasiSeparated rfl).2 ((SecOn.chart hL _ hU).symm 1)
    refine ⟨a, t, hya, fun y' hy' => Subtype.ext (e.le ⟨(ha hy').1, y'.2⟩), ?_⟩
    have h₁ := congrArg (SecOn.chart hL _ hU) ht
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, _root_.mul_one, SecOn.chart_apply,
      SecOn.coord_restrict, rs_rs] at h₁
    have h₂ := congrArg (gs (𝟙 Z) y.1 _) h₁
    rw [gs_res _ _ _ hya, gs_pow _ _ _ hya, gs_res _ _ _ hya] at h₂
    exact (congrArg IsUnit h₂).mpr (((isUnit_gs_iff (𝟙 Z) y.1 W (hFW y.2) a).2 hya).pow k)
  choose a t h₁ h₂ h₃ using key
  have := hF.fintype
  refine ⟨∑ y, a y • t y, fun y hy => ⟨i y, ?_⟩⟩
  have hy' : y ∈ W ⊓ L.U (i y) := ⟨hFW hy, hi y⟩
  refine (isUnit_gs_iff (𝟙 Z) y _ hy' _).1 (show IsUnit (germAt (i y) y hy' _) from ?_)
  rw [map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨y, hy⟩ : F))]
  have u : IsUnit (germAt (i y) y hy' (a ⟨y, hy⟩ • t ⟨y, hy⟩)) := by
    rw [germAt_smul]
    exact ((isUnit_gs_iff (𝟙 Z) y W (hFW hy) _).2 (h₁ ⟨y, hy⟩)).mul (h₃ ⟨y, hy⟩)
  have m : ∑ z ∈ Finset.univ.erase (⟨y, hy⟩ : F), germAt (i y) y hy' (a z • t z) ∈
      IsLocalRing.maximalIdeal _ := Ideal.sum_mem _ fun z hz => by
    rw [germAt_smul]
    refine Ideal.mul_mem_right _ _ fun hu => ?_
    exact (Finset.mem_erase.1 hz).1 (h₂ z ⟨y, hy⟩ ((isUnit_gs_iff (𝟙 Z) y W (hFW hy) _).1 hu)).symm
  by_contra hn
  exact (add_mem_cancel_right m).1 (show _ ∈ IsLocalRing.maximalIdeal _ from hn) u

def Generates {O : Z.Opens} (t : SecOn L O) : Prop := ∀ i, IsUnit (coord t i)

theorem Generates.restrict {O O' : Z.Opens} {t : SecOn L O} (ht : Generates t) (h : O' ≤ O) :
    Generates (SecOn.restrict L h t) := fun i => (ht i).map (rs Z (inf_le_inf_right _ h))

theorem Generates.smul_injective (hL : L.IsLB) {O : Z.Opens} {t : SecOn L O} (ht : Generates t) {a b : Γ(Z, O)}
    (h : a • t = b • t) : a = b :=
  fun_ext_of_cover (fun i => O ⊓ L.U i) (fun _ => inf_le_left) (le_iSup_inf hL.cover O) fun i =>
    (ht i).mul_right_cancel (congrArg (coord · i) h)

theorem Generates.exists_smul (hL : L.IsLB) {O : Z.Opens} {t : SecOn L O} (ht : Generates t) (σ : SecOn L O) :
    ∃ a : Γ(Z, O), a • t = σ := by
  obtain ⟨a, ha⟩ := exists_fun_of_cover (fun i => O ⊓ L.U i) (fun _ => inf_le_left) (le_iSup_inf hL.cover O)
    (fun i => coord σ i * ((ht i).unit⁻¹).val) fun i j => by
      have hij : O ⊓ L.U i ⊓ (O ⊓ L.U j) ≤ L.U i ⊓ L.U j := inf_le_inf inf_le_right inf_le_right
      have e₁ := SecOn.compat σ i j inf_le_left inf_le_right hij
      have e₂ := SecOn.compat t i j inf_le_left inf_le_right hij
      have u₁ := congrArg (rs Z (inf_le_left : O ⊓ L.U i ⊓ (O ⊓ L.U j) ≤ _)) (ht i).mul_val_inv
      have u₂ := congrArg (rs Z (inf_le_right : O ⊓ L.U i ⊓ (O ⊓ L.U j) ≤ _)) (ht j).mul_val_inv
      simp only [map_mul, map_one] at u₁ u₂ ⊢
      rw [e₂] at u₁
      rw [show resG Z _ (coord σ i) = _ from e₁]
      generalize rs Z hij (L.g i j).val = g at *
      generalize rs Z inf_le_right (coord σ j) = s at *
      generalize rs Z inf_le_right (coord t j) = r at *
      generalize rs Z inf_le_left ((ht i).unit⁻¹).val = p at *
      generalize rs Z inf_le_right ((ht j).unit⁻¹).val = q at *
      linear_combination s * q * u₁ - g * s * p * u₂
  refine ⟨a, sec_ext fun i => ?_⟩
  rw [coord_smul, ha, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]

theorem Generates.exists_unit_smul (hL : L.IsLB) {O : Z.Opens} {t t' : SecOn L O} (ht : Generates t)
    (ht' : Generates t') : ∃ a : Γ(Z, O)ˣ, a.val • t = t' := by
  obtain ⟨a, ha⟩ := ht.exists_smul hL t'
  obtain ⟨b, hb⟩ := ht'.exists_smul hL t
  have e : b * a = 1 := ht.smul_injective hL (by rw [mul_smul, ha, hb, one_smul])
  exact ⟨(IsUnit.of_mul_eq_one_right b e).unit, ha⟩

end Generators

omit [Flat π] [IsLocallyNoetherian X] in

theorem exists_generates {L : LB Y} (hL : L.IsLB) (x : X) :
    ∃ (V : X.Opens) (t : SecOn L (π ⁻¹ᵁ V)), x ∈ V ∧ Generates t := by
  obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  obtain ⟨t, ht⟩ := exists_sec_of_finite hL (hW.preimage π) (π.finite_preimage_singleton x)
    (π.isDiscrete_preimage_singleton x) (fun y (hy : π y = x) => show π y ∈ W from hy ▸ hx)
  obtain ⟨O, hO, hle⟩ := exists_preimage_le π (x := x) (O := ⨆ i, Y.basicOpen (coord t i))
    fun y hy => Opens.mem_iSup.2 (ht y hy)
  refine ⟨O ⊓ W, SecOn.restrict L (π.preimage_mono inf_le_right) t, ⟨hO, hx⟩, fun i => ?_⟩
  refine Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => ?_
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hle hy.1.1)
  have hj' := Y.basicOpen_le _ hj
  have u : IsUnit (germAt j y hj' t) := (isUnit_gs_iff (𝟙 Y) y _ hj' _).2 hj
  rw [isUnit_germAt_iff j i y hj' ⟨hj'.1, hy.2⟩, ← germAt_restrict (π.preimage_mono inf_le_right) i y hy] at u
  exact (gs_eq (𝟙 Y) y _ hy _) ▸ u

end GlobalTheory.FlatNorm

namespace GlobalTheory.FlatNorm

open TopologicalSpace GlobalTheory.LB GlobalTheory.LBGerm

theorem exists_norm_lb : ∀ (X X' : Scheme.{0}) [IsLocallyNoetherian X] (π : X' ⟶ X) [IsFinite π] [Flat π] (L : LB X') (s : LB.Sec L), L.IsLB → ∃ (N : LB X) (n : LB.Sec N), N.IsLB ∧ ∀ x : X, x ∈ nonzeroLocus n ↔ ∀ y : X', π y = x → y ∈ nonzeroLocus s := by
  intro X Y _ π _ _ L s hL
  choose V t hx ht using exists_generates π hL
  choose c hc using fun a b : X => Generates.exists_unit_smul hL
    ((ht a).restrict (π.preimage_mono (inf_le_left : V a ⊓ V b ≤ V a)))
    ((ht b).restrict (π.preimage_mono (inf_le_right : V a ⊓ V b ≤ V b)))
  choose f hf using fun a : X => (ht a).exists_smul hL (ofSec s _)
  have hc' (a b : X) {W : X.Opens} (ha : W ≤ V a) (hb : W ≤ V b) :
      rs Y (π.preimage_mono (le_inf ha hb)) (c a b).val • SecOn.restrict L (π.preimage_mono ha) (t a) =
        SecOn.restrict L (π.preimage_mono hb) (t b) := by
    have e := congrArg (SecOn.restrict L (π.preimage_mono (le_inf ha hb))) (hc a b)
    rwa [map_smulₛₗ, SecOn.restrict_restrict, SecOn.restrict_restrict] at e
  have hf' (a : X) {W : X.Opens} (ha : W ≤ V a) :
      rs Y (π.preimage_mono ha) (f a) • SecOn.restrict L (π.preimage_mono ha) (t a) = ofSec s _ := by
    have e := congrArg (SecOn.restrict L (π.preimage_mono ha)) (hf a)
    rwa [map_smulₛₗ, SecOn.restrict_ofSec] at e
  refine ⟨⟨X, V, fun a b => Units.map (norm π _) (c a b)⟩, ⟨fun a => norm π _ (f a), fun a b => ?_⟩,
    ⟨top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩, fun a => Units.ext ?_, fun a b d => Units.ext ?_⟩,
    fun x => ?_⟩
  · change resG X (inf_le_left : V a ⊓ V b ≤ V a) (norm π _ (f a)) =
      norm π (V a ⊓ V b) (c a b).val * resG X (inf_le_right : V a ⊓ V b ≤ V b) (norm π _ (f b))
    rw [resG_norm, resG_norm, ← map_mul]
    congr 1
    refine ((ht a).restrict (π.preimage_mono (inf_le_left : V a ⊓ V b ≤ V a))).smul_injective hL ?_
    rw [hf' a inf_le_left, _root_.mul_comm, mul_smul, hc, hf' b inf_le_right]
  · change resG X (le_inf le_rfl le_rfl : V a ≤ V a ⊓ V a) (norm π (V a ⊓ V a) (c a a).val) = 1
    rw [resG_norm, ← map_one (norm π (V a))]
    congr 1
    refine ((ht a).restrict le_rfl).smul_injective hL ?_
    rw [one_smul]
    exact hc' a a le_rfl le_rfl
  · have la : V a ⊓ V b ⊓ V d ≤ V a := inf_le_left.trans inf_le_left
    have lb : V a ⊓ V b ⊓ V d ≤ V b := inf_le_left.trans inf_le_right
    have ld : V a ⊓ V b ⊓ V d ≤ V d := inf_le_right
    change resG X (le_inf la lb) (norm π (V a ⊓ V b) (c a b).val) *
      resG X (le_inf lb ld) (norm π (V b ⊓ V d) (c b d).val) =
      resG X (le_inf la ld) (norm π (V a ⊓ V d) (c a d).val)
    rw [resG_norm, resG_norm, resG_norm, ← map_mul]
    congr 1
    refine ((ht a).restrict (π.preimage_mono la)).smul_injective hL ?_
    rw [_root_.mul_comm, mul_smul, hc' a b la lb, hc' b d lb ld, hc' a d la ld]
  · refine (mem_nonzeroLocus_iff_basicOpen _ (k := x) (hx x)).trans
      ((mem_basicOpen_norm π (f x) (hx x)).trans (forall₂_congr fun y hy => ?_))
    obtain ⟨i, hi⟩ := exists_chart hL y
    have hy' : y ∈ π ⁻¹ᵁ V x ⊓ L.U i := ⟨show π y ∈ V x from hy ▸ hx x, hi⟩
    have e := congrArg (germAt i y hy') (hf x)
    have e' : germAt i y hy' (ofSec s (π ⁻¹ᵁ V x)) = gs (𝟙 Y) y _ (s.f i) := gs_res (𝟙 Y) y inf_le_right hy' _
    have u : IsUnit (germAt i y hy' (t x)) := by
      change IsUnit (gs (𝟙 Y) y _ (coord (t x) i))
      rw [gs_eq (𝟙 Y) y _ hy']
      exact ((ht x i).map _).map _
    rw [mem_nonzeroLocus_iff_isUnit s hi, ← e', ← e, germAt_smul, IsUnit.mul_iff, and_iff_left u]
    exact (isUnit_gs_iff (𝟙 Y) y _ hy'.1 _).symm

end GlobalTheory.FlatNorm
