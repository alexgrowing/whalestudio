import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamComparisonBijectiveCupSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOverOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparisonStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechDR KaehlerDifferential
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TanVanish

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem snd_val_affine {R' : Type} [CommRing R'] [Algebra R R'] (U : X.affineOpens)
    (α : Sec s U.1 →ₐ[R] TrivSqZeroExt R' R') (y : Sp (TrivSqZeroExt R' R') ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (TrivSqZeroExt R' R')))
    (e : spMap (α : Sec s U.1 →+* TrivSqZeroExt R' R') ≫ affPt s U = y) (f : Form s)
    (h0 : connForm f.1 (affPt s U) (affPt_w s U) = 0) :
    TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val y hy f.1) = 0 := by
  have hx := affPt_w s U
  letI : Algebra (Sec s U.1) R' := ((TrivSqZeroExt.fstHom R R' R').comp α).toRingHom.toAlgebra
  haveI : IsScalarTower R (Sec s U.1) R' := IsScalarTower.of_algebraMap_eq fun r ↦
    (congrArg TrivSqZeroExt.fst (α.commutes r)).symm
  let δ : Derivation R (Sec s U.1) R' :=
    { toFun := fun b ↦ (α b).snd
      map_add' := fun a b ↦ by simp
      map_smul' := fun r b ↦ by
        simp [Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl']
      map_one_eq_zero' := by simp
      leibniz' := fun a b ↦ by
        simp only [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, Algebra.smul_def,
          RingHom.algebraMap_toAlgebra]
        simp [MulOpposite.smul_eq_mul_unop]
        ring }
  let δ' := δ.liftKaehlerDifferential
  have hop : ∀ (b : Sec s U.1) (ω : Ω[Sec s U.1⁄R]), MulOpposite.op b • ω = b • ω := fun _ _ ↦ rfl
  let Φ : TrivSqZeroExt (Sec s U.1) Ω[Sec s U.1⁄R] →ₐ[R] TrivSqZeroExt R' R' :=
    { toFun := fun c ↦ TrivSqZeroExt.inl (algebraMap (Sec s U.1) R' c.fst) +
        TrivSqZeroExt.inr (δ' c.snd)
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b ↦ by ext <;> simp <;> ring
      map_mul' := fun a b ↦ by
        ext
        · simp
        · simp only [TrivSqZeroExt.snd_mul, hop, map_add, map_smul, TrivSqZeroExt.snd_add,
            TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add,
            TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, smul_eq_mul, Algebra.smul_def]
          simp [MulOpposite.smul_eq_mul_unop]
          ring
      commutes' := fun r ↦ by
        ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl', ← IsScalarTower.algebraMap_apply] }
  let α₀ : Sec s U.1 →ₐ[R] R' := (TrivSqZeroExt.fstHom R R' R').comp α
  have hπ : ∀ c, α₀ ((diagExt R (Sec s U.1)).π c) = (SqExt.ofModule R R' R').π (Φ c) := fun c ↦ by
    simp [Φ, α₀, RingHom.algebraMap_toAlgebra]
  have e₀ : spMap (α₀ : Sec s U.1 →+* R') ≫ affPt s U =
      spMap ((SqExt.ofModule R R' R').π : TrivSqZeroExt R' R' →+* R') ≫ y := by
    rw [← e, ← Category.assoc, ← Cris.spMap_comp]; rfl
  let Ψ := (diagExt R (Sec s U.1)).thickHom (SqExt.ofModule R R' R') Φ α₀ hπ hx
    ((SqExt.ofModule R R' R').red_w hy) e₀
  let a1 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶
      Thick.triv R' _ ((SqExt.ofModule R R' R').red_w hy) := Thick.trivHom α₀ e₀
  let a2 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶ Thick.triv (TrivSqZeroExt R' R') y hy :=
    Thick.trivHom α e
  have k1 := Form.ev_sq f a1 ((SqExt.ofModule R R' R').secHom ((SqExt.ofModule R R' R').red_w hy)
    (SqExt.ofModule R R' R').i (SqExt.ofModule R R' R').π_i)
    ((diagExt R (Sec s U.1)).secHom hx (diagExt R (Sec s U.1)).i fun _ ↦ rfl) Ψ rfl rfl fun c ↦ by
      change TrivSqZeroExt.inl (α₀ c) = Φ (TrivSqZeroExt.inl c)
      ext <;> simp [Φ, α₀, RingHom.algebraMap_toAlgebra]
  have k2 := Form.ev_sq f a2 ((SqExt.ofModule R R' R').idHom hy)
    ((diagExt R (Sec s U.1)).secHom hx (diagSec R (Sec s U.1)) (fst_derSec _)) Ψ rfl rfl fun c ↦ by
      change α c = Φ (diagSec R (Sec s U.1) c)
      ext
      · simp [Φ, RingHom.algebraMap_toAlgebra]
      · simp only [Φ, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
          TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, snd_derSec]
        exact (Derivation.liftKaehlerDifferential_comp_D δ c).symm
  have hΦ : ∀ z, TrivSqZeroExt.snd (Φ z) = δ' z.snd := fun z ↦ by simp [Φ]
  rw [SqExt.val_apply, k1, k2, add_sub_add_right_eq_sub]
  change TrivSqZeroExt.snd (Φ _ - Φ _) = 0
  rw [← map_sub, hΦ]
  have h0' : TrivSqZeroExt.snd (ev f.1 ((diagExt R (Sec s U.1)).secHom hx (diagExt R (Sec s U.1)).i
      fun _ ↦ rfl) - ev f.1 ((diagExt R (Sec s U.1)).secHom hx (diagSec R (Sec s U.1))
      (fst_derSec _))) = 0 := h0
  rw [h0', map_zero]

theorem snd_val_eq_zero (y : Sp (DualNumber R) ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (DualNumber R))) (f : Form s)
    (h0 : ∀ U : X.affineOpens, connForm f.1 (affPt s U) (affPt_w s U) = 0) :
    TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1) = 0 := by
  have loc : ∀ m : Ideal R, m.IsMaximal →
      ∃ t ∉ m, t * TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1) = 0 := by
    intro m hm
    haveI := hm.isPrime
    let R' := Localization.AtPrime m
    haveI : IsLocalRing (TrivSqZeroExt R' R') :=
      IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun c ↦ by
        simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
        exact IsLocalRing.isUnit_or_isUnit_one_sub_self c.fst
    let φ : DualNumber R →ₐ[R] TrivSqZeroExt R' R' :=
      { toFun := fun c ↦ TrivSqZeroExt.inl (algebraMap R R' c.fst) +
          TrivSqZeroExt.inr (algebraMap R R' c.snd)
        map_one' := by ext <;> simp
        map_zero' := by ext <;> simp
        map_add' := fun a b ↦ by ext <;> simp <;> ring
        map_mul' := fun a b ↦ by ext <;> simp [MulOpposite.smul_eq_mul_unop] <;> ring
        commutes' := fun r ↦ by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl'] }
    let y' := spMap (φ : DualNumber R →+* TrivSqZeroExt R' R') ≫ y
    have hy' : y' ≫ s = spMap (algebraMap R (TrivSqZeroExt R' R')) := by
      change (spMap (φ : DualNumber R →+* TrivSqZeroExt R' R') ≫ y) ≫ s = _
      rw [Category.assoc, hy, ← Cris.spMap_comp, φ.comp_algebraMap]
    have hv := (SqExt.dual R).val_map (SqExt.ofModule R R' R') φ (Algebra.ofId R R')
      (fun c ↦ by simp [φ]) (fun b ↦ by ext <;> simp [φ, TrivSqZeroExt.algebraMap_eq_inl']) y hy y' hy' rfl f
    obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
      (x := y' (IsLocalRing.closedPoint (TrivSqZeroExt R' R'))) trivial
    have htop := Scheme.preimage_eq_top_of_closedPoint_mem y' hp
    let α₁ : Sec s U →+* TrivSqZeroExt R' R' := evalAt y' U htop.ge
    have hα : spMap α₁ ≫ affPt s ⟨U, hU⟩ = y' := by
      have k := IsAffineOpen.SpecMap_appLE_fromSpec y' hU (isAffineOpen_top _) htop.ge
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at k
      have e1 : spMap α₁ ≫ affPt s ⟨U, hU⟩ =
          Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt R' R'))).hom) ≫
          Spec.map (y'.appLE U ⊤ htop.ge) ≫ hU.fromSpec := by
        rw [← Category.assoc, ← Spec.map_comp]; rfl
      rw [e1]
      rw [k]
      simp only [← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
    have hc : α₁.comp (algebraMap R (Sec s U)) = algebraMap R (TrivSqZeroExt R' R') := by
      have e2 : spMap (α₁.comp (algebraMap R (Sec s U))) = spMap (algebraMap R (TrivSqZeroExt R' R')) := by
        rw [Cris.spMap_comp, ← affPt_w s ⟨U, hU⟩, ← Category.assoc, hα, hy']
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
    let α : Sec s U →ₐ[R] TrivSqZeroExt R' R' :=
      { α₁ with commutes' := fun r ↦ RingHom.congr_fun hc r }
    have h1 := snd_val_affine ⟨U, hU⟩ α y' hy' hα f (h0 _)
    rw [hv] at h1
    have h2 : algebraMap R R' (TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1)) = 0 := by
      simpa [φ] using h1
    obtain ⟨⟨t, ht⟩, ht'⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl R' _).1 h2
    exact ⟨t, ht, ht'⟩
  by_contra hx
  let J : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R
    (TrivSqZeroExt.snd (R := R) ((SqExt.dual R).val y hy f.1)))
  have hJ : J ≠ ⊤ := fun h ↦ hx (by
    have : (1 : R) ∈ J := h ▸ Submodule.mem_top
    simpa [J] using this)
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨t, ht, ht'⟩ := loc m hm
  exact ht (hJm (by simpa [J] using ht'))

theorem tanVal_eq_zero_of_cmpForm_eq_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R))
    (v : epsR R ⟶ A) (f : Form (A.hom ≫ 𝟙 (Sp R))),
    GlobalTheory.CechDR.cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → tanVal v f = 0 := by
  intro R _ A v f hf
  rw [tanVal_apply]
  refine snd_val_eq_zero v.left (pt_w v) f fun U ↦ ?_
  have := congrArg (fun g : ClosedForm (A.hom ≫ 𝟙 (Sp R)) ↦ g.1.1 (Opposite.op U)) hf
  exact (cmpForm_apply _ f (Opposite.op U)).symm.trans (this.trans rfl)

end GlobalTheory.TanVanish
