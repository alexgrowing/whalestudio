import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent resG)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.LB (resG_self)
open GlobalTheory.DualPull (appLE_resG resG_appLE)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

theorem sub_mul_sub_eq_zero_of_closure {B : Type*} [CommRing B] (ψ : B →+* B) (s : Set B)
    (hs : Subring.closure s = ⊤) (H : ∀ x ∈ s, ∀ y ∈ s, (x - ψ x) * (y - ψ y) = 0) (x y : B) :
    (x - ψ x) * (y - ψ y) = 0 := by
  have step (x : B) (hx : ∀ y ∈ s, (x - ψ x) * (y - ψ y) = 0) (y : B) :
      (x - ψ x) * (y - ψ y) = 0 := by
    have hy : y ∈ Subring.closure s := hs ▸ Subring.mem_top y
    induction hy using Subring.closure_induction with
    | mem y hy => exact hx y hy
    | zero => simp
    | one => simp
    | add a b _ _ ha hb =>
      calc (x - ψ x) * (a + b - ψ (a + b)) = (x - ψ x) * (a - ψ a) + (x - ψ x) * (b - ψ b) := by
            rw [map_add]; ring
        _ = 0 := by rw [ha, hb, add_zero]
    | neg a _ ha =>
      calc (x - ψ x) * (-a - ψ (-a)) = -((x - ψ x) * (a - ψ a)) := by rw [map_neg]; ring
        _ = 0 := by rw [ha, neg_zero]
    | mul a b _ _ ha hb =>
      calc (x - ψ x) * (a * b - ψ (a * b)) =
            b * ((x - ψ x) * (a - ψ a)) + ψ a * ((x - ψ x) * (b - ψ b)) := by rw [map_mul]; ring
        _ = 0 := by rw [ha, hb]; ring
  have hx : x ∈ Subring.closure s := hs ▸ Subring.mem_top x
  revert y
  induction hx using Subring.closure_induction with
  | mem x hx => exact step x (H x hx)
  | zero => intro y; simp
  | one => intro y; simp
  | add a b _ _ ha hb =>
    intro y
    calc (a + b - ψ (a + b)) * (y - ψ y) = (a - ψ a) * (y - ψ y) + (b - ψ b) * (y - ψ y) := by
          rw [map_add]; ring
      _ = 0 := by rw [ha, hb, add_zero]
  | neg a _ ha =>
    intro y
    calc (-a - ψ (-a)) * (y - ψ y) = -((a - ψ a) * (y - ψ y)) := by rw [map_neg]; ring
      _ = 0 := by rw [ha, neg_zero]
  | mul a b _ _ ha hb =>
    intro y
    calc (a * b - ψ (a * b)) * (y - ψ y) =
          b * ((a - ψ a) * (y - ψ y)) + ψ a * ((b - ψ b) * (y - ψ y)) := by rw [map_mul]; ring
      _ = 0 := by rw [ha, hb]; ring

variable (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]

theorem toTsze_injective : Function.Injective (toTsze O M) :=
  (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt O M))).hom).1

theorem surjective_sec_zeroSec : Function.Surjective (sec (zeroSec O M)) := by
  intro t
  have hs : Function.Surjective (TrivSqZeroExt.fstHom O O M).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have ht : (t : PrimeSpectrum (TrivSqZeroExt O M)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom O O M).toRingHom) := by
    rw [_root_.range_comap_of_surjective _ _ hs]
    intro a ha
    have ha : a.fst = 0 := ha
    have h : a * a = 0 := by ext <;> simp [ha]
    have := (t : PrimeSpectrum (TrivSqZeroExt O M)).isPrime
    exact (this.mem_or_mem (h ▸ Ideal.zero_mem _)).elim id id
  exact ht

theorem kappa_injective : Function.Injective (kappa O M) := by
  letI := (isChart O M).algebra
  letI := topModule O M
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨y, rfl⟩ := ((isChart O M).augCotEquiv (sec_hom _)).surjective x
  obtain ⟨y, rfl⟩ := (RingHom.ker ((isChart O M).aug (sec_hom _))).toCotangent_surjective y
  have h1 : (toTsze O M y).snd = 0 := by
    change (AugCot.lift _ (sndFn O M) (sndFn_der O M)) (((isChart O M).augCotEquiv
      (sec_hom _)).symm ((isChart O M).augCotEquiv (sec_hom _) _)) = 0 at hx
    rw [LinearEquiv.symm_apply_apply, AugCot.lift_toCotangent] at hx
    exact hx
  have h2 : (toTsze O M y).fst = 0 := by
    rw [← toO_sec]
    have : (isChart O M).aug (sec_hom _) y = 0 := y.2
    rw [IsChart.aug_apply] at this
    rw [this, map_zero]
  have h3 : (y : Γ((TM O M).left, ⊤)) = 0 :=
    toTsze_injective O M (by rw [map_zero]; ext <;> simp [h1, h2])
  have : y = 0 := Subtype.ext h3
  rw [this, map_zero, map_zero]

end GlobalTheory.SqZeroPt

namespace GlobalTheory.SqZeroPt

variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]

variable (M) in

abbrev preimTop (U : (Sp O).Opens) : (TM O M).left.Opens :=
  (𝟙 (TM O M).left) ⁻¹ᵁ ⊤ ⊓ (TM O M).hom ⁻¹ᵁ U

theorem mul_eq_zero_of_appLE {U : (Sp O).Opens} (hU : IsAffineOpen U)
    (hle : U ≤ sec (zeroSec O M) ⁻¹ᵁ (preimTop M U))
    (a b : Γ((TM O M).left, preimTop M U))
    (ha : (sec (zeroSec O M)).appLE (preimTop M U) U hle a = 0)
    (hb : (sec (zeroSec O M)).appLE (preimTop M U) U hle b = 0) : a * b = 0 := by
  obtain ⟨-, po⟩ := isAffineOpen_and_isPushout (IsPullback.id_horiz (TM O M).hom)
    (isAffineOpen_top (Sp O)) hU (isChart O M).affine (le_top : U ≤ (𝟙 (Sp O)) ⁻¹ᵁ ⊤) le_top
  have hs := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  let ψ := ((TM O M).hom.appLE U (preimTop M U) inf_le_right).hom.comp ((sec (zeroSec O M)).appLE (preimTop M U) U hle).hom
  have hψ₁ (r : Γ(Sp O, U)) : ψ ((TM O M).hom.appLE U (preimTop M U) inf_le_right r) =
      (TM O M).hom.appLE U (preimTop M U) inf_le_right r := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle
      ((TM O M).hom.appLE U (preimTop M U) inf_le_right r)) = _
    rw [appLE_base (sec_hom _) hle inf_le_right le_rfl, resG_self]
  have hψ₂ (x : Γ((TM O M).left, ⊤)) : ψ (Scheme.Hom.appLE (𝟙 (TM O M).left) ⊤ (preimTop M U) inf_le_left x) =
      Scheme.Hom.appLE (𝟙 (TM O M).left) ⊤ (preimTop M U) inf_le_left
        ((TM O M).hom.appLE ⊤ ⊤ le_top ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top x)) := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle
      (resG (TM O M).left (le_top : preimTop M U ≤ ⊤) x)) =
      resG (TM O M).left (le_top : preimTop M U ≤ ⊤) _
    rw [appLE_resG, ← resG_appLE (sec (zeroSec O M)) (le_top : U ≤ ⊤) le_top, appLE_resG]
    exact (resG_appLE (TM O M).hom (le_top : preimTop M U ≤ ⊤) le_top _).symm
  have h₀ (x y : Γ((TM O M).left, ⊤)) :
      (x - (TM O M).hom.appLE ⊤ ⊤ le_top ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top x)) *
        (y - (TM O M).hom.appLE ⊤ ⊤ le_top ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top y)) = 0 := by
    apply toTsze_injective O M
    rw [map_mul, map_sub, map_sub, toTsze_base, toTsze_base, toO_sec, toO_sec, map_zero]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have key := sub_mul_sub_eq_zero_of_closure ψ _ hs (by
    rintro x (⟨x, rfl⟩ | ⟨r, rfl⟩) y (⟨y, rfl⟩ | ⟨s, rfl⟩)
    · rw [hψ₂, hψ₂, ← map_sub, ← map_sub, ← map_mul, h₀, map_zero]
    · rw [hψ₁, sub_self, mul_zero]
    · rw [hψ₁, sub_self, zero_mul]
    · rw [hψ₁, sub_self, zero_mul]) a b
  have ha' : ψ a = 0 := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle a) = 0
    rw [ha, map_zero]
  have hb' : ψ b = 0 := by
    change (TM O M).hom.appLE U (preimTop M U) inf_le_right ((sec (zeroSec O M)).appLE (preimTop M U) U hle b) = 0
    rw [hb, map_zero]
  rwa [ha', hb', sub_zero, sub_zero] at key

variable {A : Over (Sp O)} [GrpObj A]

theorem preimage_le_of_zeroSec (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) {U : (Sp O).Opens}
    {W : A.left.Opens} (hU : U ≤ unitSec A ⁻¹ᵁ W) : (TM O M).hom ⁻¹ᵁ U ≤ z.left ⁻¹ᵁ W := by
  intro t ht
  obtain ⟨s, rfl⟩ := surjective_sec_zeroSec O M t
  have h₁ : s ∈ (sec (zeroSec O M) ≫ (TM O M).hom) ⁻¹ᵁ U := ht
  rw [sec_hom] at h₁
  have h₂ := hU h₁
  rw [← show sec (zeroSec O M) ≫ z.left = unitSec A from congrArg (·.left) h] at h₂
  exact h₂

end GlobalTheory.SqZeroPt

namespace GlobalTheory.SqZeroPt

theorem eq_of_Phi_eq : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A],
    (GlobalTheory.LieVB.omega A).IsQuasicoherent → (∀ (M : Type) [AddCommGroup M] [Module O M]
      [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (z z' : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A])
      (h' : zeroSec O M ≫ z' = η[A]), (∀ w, Phi z h w = Phi z' h' w) → z = z') := by
  intro O _ A _ hq M _ _ _ _ z z' h h' hΦ
  have hq' : (conormal (sec η[A])).IsQuasicoherent := hq
  have hglob (w : Γ(conormal (sec η[A]), ⊤)) : (cotMap z h).app ⊤ w = (cotMap z' h').app ⊤ w :=
    kappa_injective O M ((Phi_apply z h w).symm.trans ((hΦ w).trans (Phi_apply z' h' w)))
  have : IsIso ((tilde.adjunction (R := .of O)).counit.app (conormal (sec η[A]))) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of O) (conormal (sec η[A]))
  have hcot : cotMap z h = cotMap z' h' := by
    apply (GlobalTheory.OmegaGlobal.map_bijective_of_isIso_counit (tilde.adjunction (R := .of O)) _ _).1
    ext s
    exact hglob s
  have hz : sec (zeroSec O M) ≫ z.left = unitSec A := congrArg (·.left) h
  have hz' : sec (zeroSec O M) ≫ z'.left = unitSec A := congrArg (·.left) h'
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun t => ?_)
  obtain ⟨U, W, hU, -, c⟩ := exists_isChart (sec_hom η[A]) (V := ⊤) (x := (TM O M).hom t) trivial
  have hT : IsAffineOpen (preimTop M U) := (isAffineOpen_and_isPushout
    (IsPullback.id_horiz (TM O M).hom) (isAffineOpen_top (Sp O)) c.affine_base (isChart O M).affine
    (le_top : U ≤ (𝟙 (Sp O)) ⁻¹ᵁ ⊤) le_top).1
  have kz : preimTop M U ≤ z.left ⁻¹ᵁ W := inf_le_right.trans (preimage_le_of_zeroSec z h c.le)
  have kz' : preimTop M U ≤ z'.left ⁻¹ᵁ W := inf_le_right.trans (preimage_le_of_zeroSec z' h' c.le)
  have c₀ : IsChart (TM O M).hom (sec (zeroSec O M)) U (preimTop M U) :=
    ⟨c.affine_base, hT, fun x hx => ⟨trivial,
      (le_preimage_iff (π := (TM O M).hom) (sec_hom (zeroSec O M))).2 le_rfl hx⟩, inf_le_right⟩
  have e : z.left.appLE W (preimTop M U) kz = z'.left.appLE W (preimTop M U) kz' := by
    ext f
    rw [← sub_eq_zero]
    have ha : (sec (zeroSec O M)).appLE (preimTop M U) U c₀.le
        (z.left.appLE W (preimTop M U) kz f - z'.left.appLE W (preimTop M U) kz' f) = 0 := by
      rw [map_sub, appLE_appLE hz kz c₀.le c.le, appLE_appLE hz' kz' c₀.le c.le, sub_self]
    have hd : d (sec_hom (zeroSec O M)) c₀.le
        (z.left.appLE W (preimTop M U) kz f - z'.left.appLE W (preimTop M U) kz' f) = 0 := by
      rw [map_sub, ← cotMap_d z h c.le c₀.le kz f, ← cotMap_d z' h' c.le c₀.le kz' f, hcot,
        sub_self]
    letI := c₀.algebra
    have h₁ : AugCot.d (c₀.aug (sec_hom _))
        (z.left.appLE W (preimTop M U) kz f - z'.left.appLE W (preimTop M U) kz' f) = 0 :=
      (c₀.ofAugCot_bijective (sec_hom _)).1 (by rw [c₀.ofAugCot_d, map_zero]; exact hd)
    have h₂ := (AugCot.d_eq_zero_iff _ _).1 h₁
    rw [show c₀.aug (sec_hom _) _ = 0 from ha, map_zero, sub_zero] at h₂
    have hsq : RingHom.ker (c₀.aug (sec_hom (zeroSec O M))) ^ 2 = ⊥ := by
      rw [pow_two, eq_bot_iff, Ideal.mul_le]
      intro a ha' b hb'
      exact (Ideal.mem_bot).2 (mul_eq_zero_of_appLE c.affine_base c₀.le a b ha' hb')
    rw [hsq] at h₂
    exact (Ideal.mem_bot).1 h₂
  refine ⟨preimTop M U, ⟨trivial, hU⟩, ?_⟩
  rw [← cancel_epi hT.isoSpec.inv, ← Category.assoc, ← Category.assoc, hT.isoSpec_inv_ι,
    ← c.affine.SpecMap_appLE_fromSpec _ hT kz, ← c.affine.SpecMap_appLE_fromSpec _ hT kz', e]

end GlobalTheory.SqZeroPt
