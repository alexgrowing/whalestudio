import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.DualFrame
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox

noncomputable section

open Module Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P

namespace Formalism.L2.Geo.Def.G1

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem star_int (r : 𝓞 E) :
    star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := by
  have h : IsIntegral ℤ (star (algebraMap (𝓞 E) E r)) :=
    (RingOfIntegers.isIntegral_coe r).map (starRingEnd E).toIntAlgHom
  exact ⟨⟨_, h⟩, rfl⟩

theorem mem_one_iff (e : E) : e ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ e := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact RingOfIntegers.isIntegral_coe y
  · intro h
    exact ⟨⟨e, h⟩, rfl⟩

theorem hform_sig {n : ℕ} (σ : E →ₐ[F] E) (hσ : ∀ x, σ x = star x) (J : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : Formalism.UG.hform (σ : E →+* E) J x y = Formalism.DivisionValues.hform J x y := by
  simp only [Formalism.UG.hform, Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, AlgHom.coe_toRingHom, hσ,
    starRingEnd_apply, RingHom.id_apply]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem globLat_unimod {n : ℕ} (σ : E →ₐ[F] E) (hσ : ∀ x, σ x = star x) (J : Matrix (Fin n) (Fin n) E)
    (hs : (Formalism.DivisionValues.hform J).IsSymm) (hnd : (Formalism.DivisionValues.hform J).Nondegenerate)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (Formalism.DivisionValues.hform J) Λ)
    (g : GL (Fin n) 𝒜) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    Formalism.HermitianLatticesTheory.IsUnimodular (Formalism.DivisionValues.hform J) (Formalism.UG.CS.globLat g Λ) := by
  have mem := Formalism.HermitianLatticesTheory.dualBasic_mem_dual (R := 𝓞 E) (Formalism.DivisionValues.hform J)
  have hstar : ∀ r : 𝓞 E, star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := star_int
  have hfin : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ.fg
  have hspan := hΛ.span_eq_top
  have hU' : Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform J) Λ = Λ := hU
  show Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform J) (Formalism.UG.CS.globLat g Λ) = Formalism.UG.CS.globLat g Λ
  ext x
  rw [mem]
  constructor
  · intro hx
    obtain ⟨k, gg, w, hgg, hw, hfr⟩ := dual_frame (R := 𝓞 E) (Formalism.DivisionValues.hform J) hs hnd hstar Λ hΛ
    rw [hU'] at hw
    have hF := isFrame_of J gg w hfr
    have hx' : ∀ y ∈ Formalism.UG.CS.globLat g Λ, hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range := by
      intro y hy
      rw [hform_sig σ hσ]
      exact Submodule.mem_one.mp (hx y hy)
    have hUg : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) ((g : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) * J.map ιA *
        (g : Matrix (Fin n) (Fin n) 𝒜) = J.map ιA := hg
    obtain ⟨z, hz⟩ : ∃ z, z = ((g⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) *ᵥ (fun i => ιA (x i)) := ⟨_, rfl⟩
    have hxz : (fun i => ιA (x i)) = (g : Matrix (Fin n) (Fin n) 𝒜) *ᵥ z := by
      rw [hz, mulVec_mulVec, Units.mul_inv, one_mulVec]
    have hwz : ∀ u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ,
        hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ιA) u z ∈ 𝒮 := by
      intro u hu
      have hu' := (span_recovery_of_integral_adelic_approx integral_adele_approximation_holds F E (Fin n) Λ hfin hspan g
        ((g : Matrix (Fin n) (Fin n) 𝒜) *ᵥ u)).2 (by rwa [mulVec_mulVec, Units.inv_mul, one_mulVec])
      have := csDual_span σ J (Formalism.UG.CS.globLat g Λ) x hx' _ hu'
      rwa [hxz, hform_mulVec, hUg] at this
    have hzz := hF.map ιA (sigR σ (FiniteAdeleRing (𝓞 F) F))
      (fun a => by rw [csDual_sig_incl, hσ]) z
    show ((g⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) *ᵥ (fun i => ιA (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ
    rw [← hz, hzz]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : (fun c => ιA (w i c)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ :=
      Submodule.subset_span ⟨w i, hw i, rfl⟩
    have h2 : (fun c => ιA (gg i c)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ :=
      Submodule.subset_span ⟨gg i, hgg i, rfl⟩
    exact Submodule.smul_mem _ (⟨_, hwz _ h1⟩ : 𝒮) h2
  · intro hx y hy
    have hm : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (((1 : ℤ) : E) * hform (σ : E →+* E) J x y) := by
      intro a ha b hb
      rw [hform_sig σ hσ, Int.cast_one, one_mul, ← mem_one_iff]
      rw [← hU', mem] at hb
      exact hb a ha
    have h1 := csScale_glob σ J Λ 1 hm g hg hy hx
    have h2 := csGlob_int _ h1
    rw [hform_sig σ hσ, Int.cast_one, one_mul] at h2
    exact (mem_one_iff _).2 h2

end Glob

end Formalism.L2.Geo.Def.G1
