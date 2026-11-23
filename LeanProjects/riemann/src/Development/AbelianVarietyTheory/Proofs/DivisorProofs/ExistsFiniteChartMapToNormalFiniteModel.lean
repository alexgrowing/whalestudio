import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.ModelAt

open GlobalTheory.Points GlobalTheory.ZH.RatModel

theorem isIntegral_valMap {C : Type} [CommRing C] {Z : Scheme.{0}} {V : Z.Opens} (hV : IsAffineOpen V)
    (f : Sp C ⟶ V) [IsFinite f] (h : ⊤ ≤ (f ≫ V.ι) ⁻¹ᵁ V) : (valMap (f ≫ V.ι) V h).hom.IsIntegral := by
  have e := specMap_valMap_fromSpec hV (f ≫ V.ι) h
  have e2 : Spec.map (valMap (f ≫ V.ι) V h) = f ≫ hV.isoSpec.hom := by
    rw [← cancel_mono hV.fromSpec, e, Category.assoc, ← hV.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have : IsFinite (Spec.map (valMap (f ≫ V.ι) V h)) := by rw [e2]; infer_instance
  exact ((IsFinite.SpecMap_iff _).1 this).to_isIntegral

theorem mem_of_isIntegralElem {o Ω A : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing A]
    (S : Subalgebra o Ω) [IsFractionRing S Ω] [IsIntegrallyClosed S] (σ : A →+* Ω) (hσ : ∀ a, σ a ∈ S) {x : Ω}
    (hx : σ.IsIntegralElem x) : x ∈ S := by
  have h1 : (algebraMap S Ω).IsIntegralElem x := by
    obtain ⟨p, hp, h0⟩ := hx
    refine ⟨p.map (σ.codRestrict S hσ), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact h0
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (show IsIntegral S x from h1)
  exact hy ▸ y.2

theorem exists_map_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Z : Scheme.{0}) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → IsFinite π → ∀ (R : Subalgebra o Ω), (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) → IsIntegrallyClosed R → ∀ (V : Z.Opens) (f : Sp R ⟶ V), IsAffineOpen V → IsFinite f → M.pt ≫ π = spMap R.val.toRingHom ≫ f ≫ V.ι → ∃ φ : Sp R ⟶ M.Z, φ ≫ π = f ≫ V.ι ∧ ∀ (P : Sp R) (a b : R), b ∉ P.asIdeal → (a : Ω) / (b : Ω) ∈ M.O (φ P) := by
  intro o Ω _ _ _ M Z π hn hπ R hR hic V f hV hf hpt
  have hg : ⊤ ≤ (f ≫ V.ι) ⁻¹ᵁ V := fun w _ => (f w).2
  have hpV : ⊤ ≤ (M.pt ≫ π) ⁻¹ᵁ V := by
    rw [hpt]
    exact fun w _ => hg (x := _) trivial
  have hW : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  have hne : ((π ⁻¹ᵁ V : M.Z.Opens) : Set M.Z).Nonempty :=
    ⟨M.pt (IsLocalRing.closedPoint Ω), hpV (x := IsLocalRing.closedPoint Ω) trivial⟩
  haveI : IsFractionRing R Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, c, hc, h⟩ := hR z
    exact ⟨⟨a, ha⟩, ⟨c, hc⟩, h⟩
  have hα := isIntegral_valMap hV f hg
  have hβ : (π.app V).hom.IsIntegral := (π.finite_app V hV).to_isIntegral
  have hcomm : ∀ a, M.res _ hne ((π.app V).hom a) = (((valMap (f ≫ V.ι) V hg).hom a : R) : Ω) := fun a => by
    rw [res_apply, valF_eq_valR, ← valR_comp, hpt, valR_spMap_comp _ _ _ hg, valR_eq _ _ hg]
    rfl
  have hσ : (M.res _ hne).comp (π.app V).hom = R.val.toRingHom.comp (valMap (f ≫ V.ι) V hg).hom :=
    RingHom.ext hcomm
  have h1 : ∀ c, M.res _ hne c ∈ R := fun c =>
    mem_of_isIntegralElem R ((M.res _ hne).comp (π.app V).hom) (fun a => by
      rw [RingHom.comp_apply, hcomm]; exact Subtype.prop _) (by
      obtain ⟨p, hp, h0⟩ := hβ c
      exact ⟨p, hp, by rw [← Polynomial.hom_eval₂, h0, map_zero]⟩)
  have h2 : ∀ r : R, ∃ c, M.res _ hne c = r := fun r => by
    have : (r : Ω) ∈ M.ringOn (π ⁻¹ᵁ V : M.Z.Opens) := mem_ringOn.2 fun z hz => by
      have := isIntegrallyClosed_O hn z
      refine mem_of_isIntegralElem (M.O z) ((M.res _ hne).comp (π.app V).hom) (fun a => by
        rw [RingHom.comp_apply, res_apply]; exact valF_mem_O hz _) ?_
      obtain ⟨p, hp, h0⟩ := hα r
      refine ⟨p, hp, ?_⟩
      rw [hσ]
      exact (Polynomial.hom_eval₂ p _ R.val.toRingHom r).symm.trans (by rw [h0, map_zero])
    obtain ⟨c, hc⟩ := (mem_ringOn_iff_exists hne).1 this
    exact ⟨c, (M.res_apply _ hne c).trans hc⟩
  let ψ : Γ(M.Z, π ⁻¹ᵁ V) ⟶ CommRingCat.of R := CommRingCat.ofHom ((M.res _ hne).codRestrict R h1)
  have hφ := le_preimage_specMap_fromSpec hW ψ
  refine ⟨Spec.map ψ ≫ hW.fromSpec, ?_, fun P a b hb => ?_⟩
  · refine ext_of_valR hV hφ hg fun a => ?_
    rw [valR_comp, valR_eq _ _ hφ, valMap_specMap_fromSpec, valR_eq _ _ hg]
    exact Subtype.ext (hcomm a)
  · have hz : (Spec.map ψ ≫ hW.fromSpec) P ∈ π ⁻¹ᵁ V := hφ (x := P) trivial
    obtain ⟨a', ha'⟩ := h2 a
    obtain ⟨b', hb'⟩ := h2 b
    have hbz : (Spec.map ψ ≫ hW.fromSpec) P ∈ M.Z.basicOpen b' := by
      change Spec.map ψ P ∈ hW.fromSpec ⁻¹ᵁ M.Z.basicOpen b'
      rw [hW.fromSpec_preimage_basicOpen]
      change ψ.hom b' ∉ P.asIdeal
      rwa [show ψ.hom b' = b from Subtype.ext hb']
    have hu := ((isUnit_O_iff _).1 ((isUnit_valF_iff hz b').2 hbz)).2
    rw [← ha', ← hb', res_apply, res_apply, div_eq_mul_inv]
    exact mul_mem (valF_mem_O hz a') hu

end GlobalTheory.Poinc.ModelAt
