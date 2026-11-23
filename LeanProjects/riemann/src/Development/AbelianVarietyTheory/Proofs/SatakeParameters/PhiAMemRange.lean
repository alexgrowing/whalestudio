import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc.OrdA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

theorem phiA_mem_range (A : LocAt F E n G) (hI : LocInt A) (hS : SplAlg A) (v : Fin G.P.nV)
    {x : AfE F E} (hx : x ∈ RInt F E) : phiA A v x ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
  haveI := (G.P.setting v).frac_alt
  have key : RInt F E ≤ (algebraMap (G.P.W v) (G.P.Qq v)).range.comap (phiA A v) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro _ (⟨⟨e, he⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · obtain ⟨a, rfl⟩ := he
      show phiA A v ((algebraMap (𝓞 E) E a) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range
      rw [phiA_incl]
      have hint : IsIntegral ℤ (A.iw v (algebraMap (𝓞 E) E a)) :=
        (RingOfIntegers.isIntegral_coe a).map (A.iw v).toIntAlgHom
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hint.tower_top (A := G.P.W v))
      exact ⟨y, hy⟩
    · show phiA A v ((1 : E) ⊗ₜ[F] c) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range
      have h1 : phiA A v ((1 : E) ⊗ₜ[F] c) = (A.eQ v).symm (c (A.pl v).1) := by
        have h2 : prV (E := E) (A.pl v).1 ((1 : E) ⊗ₜ[F] c) = (1 : E) ⊗ₜ[F] c (A.pl v).1 := rfl
        have h3 : A.ph v ((1 : E) ⊗ₜ[F] c (A.pl v).1) = c (A.pl v).1 := by
          show (A.spl v ((1 : E) ⊗ₜ[F] c (A.pl v).1)).1 = _
          rw [hS v]
        show (A.eQ v).symm (A.ph v (prV (E := E) (A.pl v).1 ((1 : E) ⊗ₜ[F] c))) = _
        rw [h2, h3]
      rw [h1]
      exact (hI v _).2 (by rw [RingEquiv.apply_symm_apply]; exact hc (A.pl v).1)
  exact key hx

theorem phiA_intU (A : LocAt F E n G) (hI : LocInt A) (hS : SplAlg A) (v : Fin G.P.nV) {k : (AfE F E)ˣ}
    (hk : k ∈ intU F E) : ∃ u : (G.P.W v)ˣ, phiA A v (k : AfE F E) = algebraMap (G.P.W v) (G.P.Qq v) u := by
  haveI := (G.P.setting v).frac_alt
  obtain ⟨a, ha⟩ := phiA_mem_range A hI hS v (x := (k : AfE F E)) hk.1
  obtain ⟨b, hb⟩ := phiA_mem_range A hI hS v (x := ((k⁻¹ : (AfE F E)ˣ) : AfE F E)) hk.2
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (G.P.W v) (G.P.Qq v)
    rw [map_mul, ha, hb, ← map_mul, Units.mul_inv, map_one, map_one]
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩

theorem ordA_mul (A : LocAt F E n G) (v : Fin G.P.nV) (x y : (AfE F E)ˣ) :
    ordA A v (x * y) = ordA A v x + ordA A v y := by
  haveI := (G.P.setting v).frac_alt
  have hp := (G.P.setting v).p_unif
  obtain ⟨a, u, ha⟩ := exists_eq_unit_mul_zpow₂ hp (x.isUnit.map (phiA A v)).ne_zero
  obtain ⟨b, u', hb⟩ := exists_eq_unit_mul_zpow₂ hp (y.isUnit.map (phiA A v)).ne_zero
  unfold ordA
  rw [Units.val_mul, map_mul, ha, hb, ordP_eq hp, ordP_eq hp, ← ordP_eq (Qq := G.P.Qq v) hp (a + b) (u * u')]
  congr 1
  rw [zpow_add₀ (pQ_ne hp), Units.val_mul, map_mul]; ring

theorem ordP_unit (v : Fin G.P.nV) (u : (G.P.W v)ˣ) :
    ordP (G.P.W v) p (algebraMap (G.P.W v) (G.P.Qq v) u) = 0 := by
  haveI := (G.P.setting v).frac_alt
  have := ordP_eq (Qq := G.P.Qq v) (G.P.setting v).p_unif 0 u
  simpa using this

theorem ordA_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n p : ℕ) [Fact p.Prime]
    (G : GAtP p) (A : LocAt F E n G), LocInt A → SplAlg A → ∀ v, (∀ x y, ordA A v (x * y) = ordA A v x + ordA A v y) ∧
    (∀ k ∈ intU F E, ordA A v k = 0) ∧ (∀ z : Eˣ, ordA A v (ratId F E z) = ordP (G.P.W v) p (A.iw v (z : E))) ∧
    ∀ v', v' ≠ v → ∀ x, OneOff (A.pl v').1 x → ordA A v x = 0 := by
  intro F E _ _ _ _ _ n p _ G A hI hS v
  refine ⟨ordA_mul A v, fun k hk => ?_, fun z => ?_, fun v' hv x hx => ?_⟩
  · obtain ⟨u, hu⟩ := phiA_intU A hI hS v hk
    unfold ordA
    rw [hu]
    exact ordP_unit v u
  · unfold ordA
    rw [← phiA_incl A v (z : E)]
    rfl
  · have hne : (A.pl v).1 ≠ (A.pl v').1 := fun h => hv (A.pl.injective (Subtype.ext h)).symm
    have h1 : phiA A v (x : AfE F E) = 1 := by
      simp only [phiA, RingHom.comp_apply, hx _ hne, map_one]
    unfold ordA
    rw [h1, ← map_one (algebraMap (G.P.W v) (G.P.Qq v)), ← Units.val_one]
    exact ordP_unit v 1

end GlobalTheory.TwV.Xc.OrdA
