import Mathlib
import GroundTheory.AutomorphicForms.SatakeNormalized

noncomputable section

open MeasureTheory ValuativeRel
open GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.Spherical
open GroundTheory.Automorphic.HeckeAlgebra

namespace UpperTheory.ConvolutionTheory.L1

variable {F F' : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field F'] [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F']

def intEquiv (c : F ≃+* F') (hv : ∀ x, c x ∈ 𝒪[F'] ↔ x ∈ 𝒪[F]) : 𝒪[F] ≃+* 𝒪[F'] where
  toFun x := ⟨c x, (hv x).2 x.2⟩
  invFun y := ⟨c.symm y, (hv _).1 (by simpa using y.2)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem qF_eq_of_iso (c : F ≃+* F') (hv : ∀ x, c x ∈ 𝒪[F'] ↔ x ∈ 𝒪[F]) : qF F' = qF F :=
  (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (intEquiv c hv)).toEquiv).symm

theorem exists_unit_uniformizer (c : F ≃+* F') (hv : ∀ x, c x ∈ 𝒪[F'] ↔ x ∈ 𝒪[F]) :
    ∃ u : (𝒪[F'])ˣ, c (uniformizer F : F) = (uniformizer F' : F') * ((u : 𝒪[F']) : F') := by
  have h1 : Irreducible (intEquiv c hv (uniformizer F)) :=
    (MulEquiv.irreducible_iff (intEquiv c hv)).2 (irreducible_uniformizer F)
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible _ (irreducible_uniformizer F') h1
  exact ⟨u, (congrArg Subtype.val hu).symm⟩

abbrev mapIso (c : F ≃+* F') (n : ℕ) : GL (Fin n) F →* GL (Fin n) F' :=
  Matrix.GeneralLinearGroup.map (c : F →+* F')

variable {n : ℕ}

theorem mapIso_mem_unipotent (c : F ≃+* F') {g : GL (Fin n) F} (hg : g ∈ unipotent F n) :
    mapIso c n g ∈ unipotent F' n := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change c ((g : Matrix (Fin n) (Fin n) F) i j) = 0
    rw [hg.1 hij, map_zero]
  · change c (g i i) = 1
    rw [hg.2 i, map_one]

theorem mapIso_mem_integralGL (c : F ≃+* F') (hv : ∀ x, c x ∈ 𝒪[F'] ↔ x ∈ 𝒪[F]) {g : GL (Fin n) F}
    (hg : g ∈ integralGL F n) : mapIso c n g ∈ integralGL F' n := by
  rw [mem_integralGL_iff] at hg ⊢
  refine ⟨fun i j => (hv _).2 (hg.1 i j), fun i j => ?_⟩
  rw [← map_inv]
  exact (hv _).2 (hg.2 i j)

theorem mapIso_torusPow (c : F ≃+* F') (hv : ∀ x, c x ∈ 𝒪[F'] ↔ x ∈ 𝒪[F]) (l : Fin n → ℤ) :
    ∃ k ∈ integralGL F' n, mapIso c n (torusPow F n l) = torusPow F' n l * k := by
  obtain ⟨u, hu⟩ := exists_unit_uniformizer c hv
  refine ⟨diagGL F' n fun i => Units.map (𝒪[F']).subtype.toMonoidHom (u ^ l i),
    diagGL_map_mem_integralGL F' n _, Units.ext (Matrix.ext fun i j => ?_)⟩
  change c (((torusPow F n l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) = _
  rw [Units.val_mul, coe_torusPow, coe_torusPow, coe_diagGL, Matrix.diagonal_mul_diagonal]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, map_zpow₀, RingEquiv.coe_toRingHom]
    rw [hu, mul_zpow]
    simp [Units.val_zpow_eq_zpow_val]
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem iwasawaExponent_mapIso (c : F ≃+* F') (hv : ∀ x, c x ∈ 𝒪[F'] ↔ x ∈ 𝒪[F]) (g : GL (Fin n) F) :
    iwasawaExponent F' n (mapIso c n g) = iwasawaExponent F n g := by
  obtain ⟨u, hu, k, hk, h⟩ := exists_eq_mul_torusPow_iwasawaExponent F n g
  set l := iwasawaExponent F n g
  obtain ⟨k', hk', ht⟩ := mapIso_torusPow c hv l
  rw [h, map_mul, map_mul, ht,
    show mapIso c n u * (torusPow F' n l * k') * mapIso c n k = mapIso c n u * torusPow F' n l * (k' * mapIso c n k) by group]
  exact iwasawaExponent_eq F' n (mapIso_mem_unipotent c hu)
    ((integralGL F' n).mul_mem hk' (mapIso_mem_integralGL c hv hk))

theorem normalize_congr (hq : qF F' = qF F) (p : LaurentRing n) : normalize F' n p = normalize F n p := by
  apply AddMonoidAlgebra.coeff_injective
  ext l
  rw [coeff_normalize, coeff_normalize, halfModulus_eq, halfModulus_eq, sqrtQ, sqrtQ, hq]

section Transport

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  [MeasurableSpace (GL (Fin n) F')] [BorelSpace (GL (Fin n) F')]
  {m : Measure (GL (Fin n) F)} [m.IsHaarMeasure] {m' : Measure (GL (Fin n) F')} [m'.IsHaarMeasure]

private def cosetMap (e : GL (Fin n) F ≃* GL (Fin n) F') (y : GL (Fin n) F' ⧸ integralGL F' n) :
    GL (Fin n) F ⧸ integralGL F n :=
  QuotientGroup.mk (e.symm y.out)

private theorem cosetMap_injective (e : GL (Fin n) F ≃* GL (Fin n) F')
    (hK : ∀ g, e g ∈ integralGL F' n ↔ g ∈ integralGL F n) : Function.Injective (cosetMap e) := by
  intro y y' h
  have h1 := QuotientGroup.eq.1 h
  rw [← hK, map_mul, map_inv, e.apply_symm_apply, e.apply_symm_apply] at h1
  rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
  exact QuotientGroup.eq.2 h1

private theorem cosetMap_surjective (e : GL (Fin n) F ≃* GL (Fin n) F')
    (hK : ∀ g, e g ∈ integralGL F' n ↔ g ∈ integralGL F n) : Function.Surjective (cosetMap e) := by
  intro x
  refine ⟨QuotientGroup.mk (e x.out), ?_⟩
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F' n) (e x.out)
  have hk2 : e.symm (k : GL (Fin n) F') ∈ integralGL F n := (hK _).1 (by simpa using k.2)
  rw [cosetMap, hk, map_mul, e.symm_apply_apply, QuotientGroup.mk_mul_of_mem _ hk2, QuotientGroup.out_eq']

theorem satake_transport (e : GL (Fin n) F ≃* GL (Fin n) F')
    (hK : ∀ g, e g ∈ integralGL F' n ↔ g ∈ integralGL F n)
    (hl : ∀ g, iwasawaExponent F' n (e g) = iwasawaExponent F n g)
    (hm : m.real (integralGL F n : Set (GL (Fin n) F)) = m'.real (integralGL F' n : Set (GL (Fin n) F')))
    (H : SphericalHecke m (F := F) (n := n)) (H' : SphericalHecke m' (F := F') (n := n))
    (hH : ∀ g, (H : HeckeAlgebra m) g = (H' : HeckeAlgebra m') (e g)) : satake m H = satake m' H' := by
  classical
  have key : ∀ y : GL (Fin n) F' ⧸ integralGL F' n, ∃ k ∈ integralGL F n,
      (cosetMap e y).out = e.symm y.out * k := fun y => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) (e.symm y.out)
    exact ⟨k, k.2, hk⟩
  have hval : ∀ y, (H : HeckeAlgebra m) (cosetMap e y).out = (H' : HeckeAlgebra m') y.out := fun y => by
    obtain ⟨k, hk, h⟩ := key y
    rw [h, (HeckeAlgebraLevel.val_mem _ _ H k hk _).2, hH, e.apply_symm_apply]
  have hexp : ∀ y, iwasawaExponent F n (cosetMap e y).out = iwasawaExponent F' n y.out := fun y => by
    obtain ⟨k, hk, h⟩ := key y
    rw [h, iwasawaExponent_mul_of_mem_integralGL F n _ hk, ← hl, e.apply_symm_apply]
  rw [satake_eq_sum H ((cosetSupport H').image (cosetMap e)) ?_, satake, hm,
    Finset.sum_image (cosetMap_injective e hK).injOn]
  · simp only [hval, hexp]
  · intro x hx
    obtain ⟨y, rfl⟩ := cosetMap_surjective e hK x
    rw [hval]
    exact apply_out_eq_zero fun hy => hx (Finset.mem_image_of_mem _ hy)

theorem satakeTransform_transport (e : GL (Fin n) F ≃* GL (Fin n) F')
    (hK : ∀ g, e g ∈ integralGL F' n ↔ g ∈ integralGL F n)
    (hl : ∀ g, iwasawaExponent F' n (e g) = iwasawaExponent F n g) (hq : qF F' = qF F)
    (hm : m.real (integralGL F n : Set (GL (Fin n) F)) = m'.real (integralGL F' n : Set (GL (Fin n) F')))
    (H : SphericalHecke m (F := F) (n := n)) (H' : SphericalHecke m' (F := F') (n := n))
    (hH : ∀ g, (H : HeckeAlgebra m) g = (H' : HeckeAlgebra m') (e g)) :
    satakeTransform m H = satakeTransform m' H' := by
  rw [satakeTransform_apply, satakeTransform_apply, satake_transport e hK hl hm H H' hH, normalize_congr hq]

end Transport

theorem exists_transport [MeasurableSpace (GL (Fin n) F')] [BorelSpace (GL (Fin n) F')]
    {m' : Measure (GL (Fin n) F')} [m'.IsHaarMeasure] (e : GL (Fin n) F ≃ₜ* GL (Fin n) F')
    (hK : ∀ g, e g ∈ integralGL F' n ↔ g ∈ integralGL F n)
    (hl : ∀ g, iwasawaExponent F' n (e g) = iwasawaExponent F n g) (hq : qF F' = qF F)
    (h1 : m' (integralGL F' n : Set (GL (Fin n) F')) = 1) (H' : SphericalHecke m' (F := F') (n := n)) :
    ∃ (_ : MeasurableSpace (GL (Fin n) F)) (_ : BorelSpace (GL (Fin n) F))
      (m : Measure (GL (Fin n) F)) (_ : m.IsHaarMeasure), m (integralGL F n : Set (GL (Fin n) F)) = 1 ∧
      ∃ H : SphericalHecke m (F := F) (n := n), (∀ x, (H : HeckeAlgebra m) x = (H' : HeckeAlgebra m') (e x)) ∧
        satakeTransform m H = satakeTransform m' H' := by
  borelize (GL (Fin n) F)
  let m : Measure (GL (Fin n) F) := Measure.map e.symm m'
  haveI hm : m.IsHaarMeasure := (e.symm.toMulEquiv).isHaarMeasure_map m' e.symm.continuous e.continuous
  have hset : (e.symm ⁻¹' (integralGL F n : Set (GL (Fin n) F))) = (integralGL F' n : Set (GL (Fin n) F')) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe]
    rw [← hK, e.apply_symm_apply]
  have hmK : m (integralGL F n : Set (GL (Fin n) F)) = m' (integralGL F' n : Set (GL (Fin n) F')) := by
    change Measure.map e.symm m' _ = _
    rw [Measure.map_apply (map_continuous e.symm).measurable (isOpen_integralGL F n).measurableSet, hset]
  let f : HeckeAlgebra m := HeckeAlgebra.mk m (fun x => (H' : HeckeAlgebra m') (e x))
    ⟨(H' : HeckeAlgebra m').mem.1.comp_continuous e.continuous,
      (H' : HeckeAlgebra m').mem.2.comp_homeomorph e.toHomeomorph⟩
  have hf : f ∈ biInvariant m (integralGL F n) := fun k hk x => by
    have hk' := (hK k).2 hk
    exact ⟨by
      change (H' : HeckeAlgebra m') (e (k * x)) = (H' : HeckeAlgebra m') (e x)
      rw [map_mul]
      exact (HeckeAlgebraLevel.val_mem _ _ H' _ hk' _).1, by
      change (H' : HeckeAlgebra m') (e (x * k)) = (H' : HeckeAlgebra m') (e x)
      rw [map_mul]
      exact (HeckeAlgebraLevel.val_mem _ _ H' _ hk' _).2⟩
  refine ⟨_, inferInstance, m, hm, hmK.trans h1, HeckeAlgebraLevel.mk _ _ f hf, fun _ => rfl, ?_⟩
  exact satakeTransform_transport e.toMulEquiv hK hl hq (by simp [Measure.real, hmK]) _ H' fun _ => rfl

end UpperTheory.ConvolutionTheory.L1
