import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallHeightOneExistsDvdMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SqHorizontal

theorem exists_of_atPrime {C S : Type} [CommRing C] [CommRing S] [Algebra C S] (p : Ideal C) [p.IsPrime]
    [IsLocalization.AtPrime S p] (H : C) (T W : S) (hW : IsUnit W) (e : T ^ 2 = W * algebraMap C S H) :
    ∃ a b c : C, b ∉ p ∧ c ∉ p ∧ b * H = c * a ^ 2 := by
  obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj p.primeCompl T
  obtain ⟨⟨d, t⟩, hd⟩ := IsLocalization.surj p.primeCompl W
  dsimp only at ha hd
  have hdu : d ∈ p.primeCompl := by
    rw [← IsLocalization.AtPrime.isUnit_to_map_iff S p, ← hd]
    exact hW.mul (IsLocalization.map_units S t)
  have key : algebraMap C S (d * (s : C) ^ 2 * H) = algebraMap C S ((t : C) * a ^ 2) := by
    simp only [map_mul, map_pow]
    rw [← ha, ← hd, mul_pow, e]
    ring
  obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists p.primeCompl S).1 key
  refine ⟨a, u * (d * (s : C) ^ 2), u * t, ?_, ?_, ?_⟩
  · exact p.primeCompl.mul_mem u.2 (p.primeCompl.mul_mem hdu (p.primeCompl.pow_mem s.2 2))
  · exact p.primeCompl.mul_mem u.2 t.2
  · linear_combination hu

theorem isIso_stalkMap {X Y : Scheme.{0}} (φ : X ⟶ Y) [Flat φ] [SurjectiveOnStalks φ] (x : X) :
    IsIso (φ.stalkMap x) := by
  have h1 := Flat.stalkMap φ x
  have h2 := φ.stalkMap_surjective x
  algebraize [(φ.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (φ x))
    (B := X.presheaf.stalk x)
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ⟨FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x), h2⟩

theorem exists_of_stalk {X Y : Scheme.{0}} (f : Y ⟶ X) (x : X) (q : Spec (X.presheaf.stalk x)) (y : Y)
    [IsIso (f.stalkMap y)] (hy : X.fromSpecStalk x q = f y) (U : X.Opens) (hx : x ∈ U) (hyU : f y ∈ U)
    (h : Γ(X, U)) (T W : Y.presheaf.stalk y) (hW : IsUnit W)
    (e : T ^ 2 = W * (Y.presheaf.germ (f ⁻¹ᵁ U) y hyU).hom ((f.app U).hom h)) :
    ∃ a b c : X.presheaf.stalk x, b ∉ q.asIdeal ∧ c ∉ q.asIdeal ∧
      b * (X.presheaf.germ U x hx).hom h = c * a ^ 2 := by
  let ψ : Y.presheaf.stalk y ⟶ (Spec (X.presheaf.stalk x)).presheaf.stalk q :=
    inv (f.stalkMap y) ≫ X.presheaf.stalkSpecializes (specializes_of_eq hy) ≫ (X.fromSpecStalk x).stalkMap q
  have hψ : f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) y hyU ≫ ψ =
      X.presheaf.germ U x hx ≫ StructureSheaf.toStalk (X.presheaf.stalk x) q := by
    rw [← Category.assoc, ← Scheme.Hom.germ_stalkMap f U y hyU]
    simp only [ψ, Category.assoc, IsIso.hom_inv_id_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc]
    rw [Scheme.Hom.germ_stalkMap, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc, TopCat.Presheaf.germ_res]
    rfl
  letI : Algebra (X.presheaf.stalk x) ((Spec (X.presheaf.stalk x)).presheaf.stalk q) :=
    (StructureSheaf.toStalk (X.presheaf.stalk x) q).hom.toAlgebra
  have hl : IsLocalization.AtPrime ((Spec (X.presheaf.stalk x)).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (X.presheaf.stalk x) q
  refine exists_of_atPrime (S := (Spec (X.presheaf.stalk x)).presheaf.stalk q) q.asIdeal _
    (ψ.hom T) (ψ.hom W) (hW.map ψ.hom) ?_
  rw [← map_pow, e, map_mul]
  congr 1
  exact congrArg (fun k => k.hom h) hψ

theorem horizontal : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (L2 : LB G₁.left) (h : L2.Sec) (Lθ : LB (pullback G₁.hom (jK R'))), Lθ.IsLB → ∀ θ : Lθ.Sec, (∀ j i, ∃ w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G₁.hom (jK R')).app (L2.U j)).hom (h.f j))) → ∀ x : G₁.left, ∀ j (hx : x ∈ L2.U j), ∀ p : Ideal (G₁.left.presheaf.stalk x), p.IsPrime → Ideal.comap ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) p = ⊥ → ∃ a b c : G₁.left.presheaf.stalk x, b ∉ p ∧ c ∉ p ∧ b * (G₁.left.presheaf.germ (L2.U j) x hx).hom (h.f j) = c * a ^ 2 := by
  intro R' _ _ _ _ G₁ _ _ _ L2 h Lθ hL θ hθ x j hx p hp hc
  have : IsPreimmersion (jK R') := IsPreimmersion.of_isLocalization (nonZeroDivisors R') (S := FractionRing R')
  have : Flat (jK R') := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat (FractionRing R') (nonZeroDivisors R'))
  let q : Spec (G₁.left.presheaf.stalk x) := ⟨p, hp⟩
  have e₁ : G₁.left.fromSpecStalk x ≫ G₁.hom = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫
      G₁.hom.appTop ≫ G₁.left.presheaf.germ ⊤ x trivial) := by
    apply ext_of_isAffine
    rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
      ← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R')).inv, ← Scheme.ΓSpecIso_inv_naturality]
    simp
  have e₂ : G₁.hom (G₁.left.fromSpecStalk x q) = jK R' (⊥ : PrimeSpectrum (FractionRing R')) := by
    rw [← Scheme.Hom.comp_apply, e₁]
    apply PrimeSpectrum.ext
    refine hc.trans ?_
    exact (Ideal.comap_bot_of_injective (algebraMap R' (FractionRing R'))
      (IsFractionRing.injective R' (FractionRing R'))).symm
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e₂
  have hs : SurjectiveOnStalks (pullback.fst G₁.hom (jK R')) :=
    MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback _ _).flip inferInstance
  have := isIso_stalkMap (pullback.fst G₁.hom (jK R')) y
  have hyU : pullback.fst G₁.hom (jK R') y ∈ L2.U j := by
    rw [hy]
    have : G₁.left.fromSpecStalk x q ∈ Set.range (G₁.left.fromSpecStalk x) := ⟨q, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open this (L2.U j).isOpen hx
  obtain ⟨i, hi⟩ : ∃ i, y ∈ Lθ.U i := by
    have : y ∈ ⨆ i, Lθ.U i := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  obtain ⟨w, hw⟩ := hθ j i
  have hm : y ∈ pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i := ⟨hyU, hi⟩
  have hw' := congrArg ((pullback G₁.hom (jK R')).presheaf.germ _ y hm).hom hw
  rw [map_pow, map_mul] at hw'
  refine exists_of_stalk (pullback.fst G₁.hom (jK R')) x q y hy.symm (L2.U j) hx hyU (h.f j) _ _
    (w.isUnit.map ((pullback G₁.hom (jK R')).presheaf.germ _ y hm).hom) (hw'.trans ?_)
  congr 1
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

end GlobalTheory.SqHorizontal
