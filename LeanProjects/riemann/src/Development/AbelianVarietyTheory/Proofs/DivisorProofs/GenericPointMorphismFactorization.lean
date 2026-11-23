import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormFnField

variable {Z : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] [Algebra Z.functionField K]

theorem stalkIso_germ_app (g : Spec (CommRingCat.of K) ⟶ Z)
    (hg : g = Spec.map (CommRingCat.ofHom (algebraMap Z.functionField K)) ≫
      Z.fromSpecStalk (genericPoint Z))
    (U : Z.Opens) (hU : g (IsLocalRing.closedPoint K) ∈ U) (a : Γ(Z, U)) :
    (stalkClosedPointIso (CommRingCat.of K)).hom
        ((Spec (CommRingCat.of K)).presheaf.germ (g ⁻¹ᵁ U) (IsLocalRing.closedPoint K) hU
          (g.app U a)) =
      algebraMap Z.functionField K
        (Z.presheaf.germ U (genericPoint Z) ((genericPoint_specializes _).mem_open U.isOpen hU) a) := by
  subst hg
  have e := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
    (CommRingCat.ofHom (algebraMap Z.functionField K)) U hU
  refine Eq.trans ?_ (congrArg (fun q => q.hom a) e)
  change _ = (stalkClosedPointIso (CommRingCat.of K)).hom.hom ((Scheme.Hom.stalkMap _ _).hom
    ((Z.presheaf.germ U _ hU).hom a))
  congr 1
  exact (Scheme.Hom.germ_stalkMap_apply _ _ _ _ _).symm

end GlobalTheory.NormFnField

namespace GlobalTheory.NormFnField

theorem normalization_functionField : ∀ (Z : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral Z] (K : Type) [Field K] [Algebra Z.functionField K] [FiniteDimensional Z.functionField K] (g : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ Z) [AlgebraicGeometry.QuasiCompact g] [AlgebraicGeometry.QuasiSeparated g], g = AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Z.functionField K)) ≫ Z.fromSpecStalk (genericPoint Z) → ∃ (hη : g.fromNormalization (genericPoint g.normalization) ⤳ genericPoint Z) (ψ : K →+* g.normalization.functionField), ψ.comp (algebraMap Z.functionField K) = GlobalTheory.TrueGeo.SmallSec.fnMap g.fromNormalization hη := by
  intro Z _ K _ _ _ g _ _ hg
  set cp : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K with hcp
  set j := g.toNormalization with hj
  set π := g.fromNormalization with hπ
  have hjπ : j ≫ π = g := g.toNormalization_fromNormalization
  have h1 : j cp ⤳ genericPoint g.normalization := by
    rw [specializes_iff_mem_closure]
    have hr : Set.range j = {j cp} :=
      Set.ext fun y => ⟨fun ⟨z, hz⟩ => hz ▸ congrArg j (Subsingleton.elim z cp),
        fun hy => ⟨cp, hy.symm⟩⟩
    rw [← hr, g.toNormalization.denseRange.closure_range]
    trivial
  have hgcp : g cp ⤳ genericPoint Z := by
    have : g cp ∈ Set.range (Z.fromSpecStalk (genericPoint Z)) := by
      rw [hg, Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hη : π (genericPoint g.normalization) ⤳ genericPoint Z := by
    have := (genericPoint_specializes (j cp)).map π.continuous
    rw [← Scheme.Hom.comp_apply, hjπ] at this
    exact this.trans hgcp
  refine ⟨hη, ?_⟩
  let φ : g.normalization.functionField ⟶ CommRingCat.of K :=
    g.normalization.presheaf.stalkSpecializes h1 ≫ Scheme.stalkClosedPointTo j

  have hφ : ∀ (V : g.normalization.Opens) (hV : genericPoint g.normalization ∈ V) (s : Γ(g.normalization, V)),
      φ.hom (g.normalization.presheaf.germ V _ hV s) =
        (stalkClosedPointIso (CommRingCat.of K)).hom
          ((Spec (CommRingCat.of K)).presheaf.germ (j ⁻¹ᵁ V) cp (h1.mem_open V.isOpen hV) (j.app V s)) := by
    intro V hV s
    change (Scheme.stalkClosedPointTo j).hom ((g.normalization.presheaf.stalkSpecializes h1).hom
      (g.normalization.presheaf.germ V _ hV s)) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    change (stalkClosedPointIso (CommRingCat.of K)).hom.hom ((Scheme.Hom.stalkMap j cp).hom _) = _
    congr 1
    exact Scheme.Hom.germ_stalkMap_apply _ _ _ _ _

  have hφf : ∀ z, φ.hom (GlobalTheory.TrueGeo.SmallSec.fnMap π hη z) = algebraMap Z.functionField K z := by
    intro z
    obtain ⟨U, hU, a, rfl⟩ := Z.presheaf.exists_germ_eq z
    have e1 : GlobalTheory.TrueGeo.SmallSec.fnMap π hη (Z.presheaf.germ U _ hU a) =
        g.normalization.presheaf.germ (π ⁻¹ᵁ U) _ (hη.mem_open U.isOpen hU) (π.app U a) := by
      change (π.stalkMap _).hom ((Z.presheaf.stalkSpecializes hη).hom (Z.presheaf.germ U _ hU a)) = _
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
      exact Scheme.Hom.germ_stalkMap_apply _ _ _ _ _
    rw [e1]
    refine (hφ _ _ _).trans ?_
    exact stalkIso_germ_app (j ≫ π) (hjπ.trans hg) U
      ((h1.map π.continuous).mem_open U.isOpen (hη.mem_open U.isOpen hU)) a
  have hinj : Function.Injective φ.hom := φ.hom.injective
  have hsurj : Function.Surjective φ.hom := by
    intro k
    obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Z)) isOpen_univ
    haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
    haveI := functionField_isFractionRing_of_isAffineOpen Z U hU
    letI : Algebra Γ(Z, U) K :=
      ((algebraMap Z.functionField K).comp (algebraMap Γ(Z, U) Z.functionField)).toAlgebra
    haveI : IsScalarTower Γ(Z, U) Z.functionField K := .of_algebraMap_eq' rfl
    have hAinj : Function.Injective (algebraMap Γ(Z, U) K) :=
      (algebraMap Z.functionField K).injective.comp (IsFractionRing.injective Γ(Z, U) Z.functionField)
    have halg : IsAlgebraic Γ(Z, U) k :=
      (IsFractionRing.isAlgebraic_iff Γ(Z, U) Z.functionField K).mpr (Algebra.IsAlgebraic.isAlgebraic k)
    obtain ⟨y, hy0, hc⟩ := halg.exists_integral_multiple
    have hcU : g cp ∈ U := hgcp.mem_open U.isOpen hηU
    letI : Algebra Γ(Z, U) Γ(Spec (CommRingCat.of K), g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
    let ρ : Γ(Spec (CommRingCat.of K), g ⁻¹ᵁ U) →+* K :=
      ((Spec (CommRingCat.of K)).presheaf.germ (g ⁻¹ᵁ U) cp hcU ≫
        (stalkClosedPointIso (CommRingCat.of K)).hom).hom
    have hρA : ∀ a : Γ(Z, U), ρ (algebraMap _ _ a) = algebraMap Γ(Z, U) K a :=
      fun a => stalkIso_germ_app g hg U hcU a
    have htop : g ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem g hcU
    let res := (Spec (CommRingCat.of K)).presheaf.map (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)).op
    have hres : Function.Bijective res.hom := by
      have : IsIso res := by
        have e : homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤) = eqToHom htop := Subsingleton.elim _ _
        simp only [res, e]; infer_instance
      exact ConcreteCategory.bijective_of_isIso res
    have hρres : ∀ t, ρ (res.hom t) = (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom t := by
      intro t
      change (stalkClosedPointIso _).hom.hom (((Spec _).presheaf.germ _ cp hcU).hom (res.hom t)) = _
      refine (congrArg (stalkClosedPointIso (CommRingCat.of K)).hom.hom
        (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of K)).presheaf
          (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)) cp hcU t)).trans ?_
      exact congrArg (fun q => q.hom t) (germ_stalkClosedPointIso_hom (CommRingCat.of K))
    have hρ : Function.Bijective ρ := by
      have hb : Function.Bijective (ρ ∘ res.hom) := by
        rw [show ρ ∘ res.hom = (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom from funext hρres]
        exact ConcreteCategory.bijective_of_isIso _
      exact (Function.Bijective.of_comp_iff ρ hres).mp hb
    let ρA : Γ(Spec (CommRingCat.of K), g ⁻¹ᵁ U) →ₐ[Γ(Z, U)] K := { ρ with commutes' := hρA }
    obtain ⟨r, hr⟩ := hρ.2 (y • k)
    have hrint : IsIntegral Γ(Z, U) r :=
      (isIntegral_algHom_iff ρA hρ.1).mp (by rw [show ρA r = y • k from hr]; exact hc)
    let b : Γ(g.normalization, π ⁻¹ᵁ U) := (g.normalizationObjIso hU).inv.hom ⟨r, hrint⟩
    have hξU : genericPoint g.normalization ∈ π ⁻¹ᵁ U := hη.mem_open U.isOpen hηU
    have hb : φ.hom (g.normalization.presheaf.germ _ _ hξU b) = y • k := by
      refine (hφ _ _ _).trans ?_
      have hv : ((g.normalizationObjIso hU).hom ≫
          CommRingCat.ofHom (Subalgebra.val _).toRingHom).hom b = r := by
        change ((g.normalizationObjIso hU).hom.hom ((g.normalizationObjIso hU).inv.hom ⟨r, hrint⟩)).1 = r
        rw [Iso.inv_hom_id_apply]
      rw [g.normalizationObjIso_hom_val hU, Scheme.Hom.appLE] at hv
      rw [← hr, ← hv]
      change _ = (stalkClosedPointIso _).hom.hom (((Spec _).presheaf.germ _ cp hcU).hom
        (((Spec _).presheaf.map _).hom ((g.toNormalization.app _).hom b)))
      exact congrArg (stalkClosedPointIso (CommRingCat.of K)).hom.hom
        (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of K)).presheaf _ cp hcU _).symm
    have hy : φ.hom (GlobalTheory.TrueGeo.SmallSec.fnMap π hη (Z.presheaf.germ U _ hηU y)) =
        algebraMap Γ(Z, U) K y := hφf _
    have hy0' : algebraMap Γ(Z, U) K y ≠ 0 := fun h => hy0 (hAinj (h.trans (map_zero _).symm))
    refine ⟨g.normalization.presheaf.germ _ _ hξU b *
      (GlobalTheory.TrueGeo.SmallSec.fnMap π hη (Z.presheaf.germ U _ hηU y))⁻¹, ?_⟩
    rw [map_mul, map_inv₀, hb, hy, Algebra.smul_def]
    field_simp
  let e := RingEquiv.ofBijective φ.hom ⟨hinj, hsurj⟩
  refine ⟨e.symm.toRingHom, ?_⟩
  ext z
  apply hinj
  change e (e.symm (algebraMap _ K z)) = φ.hom (GlobalTheory.TrueGeo.SmallSec.fnMap π hη z)
  rw [hφf]
  exact e.apply_symm_apply _

end GlobalTheory.NormFnField
