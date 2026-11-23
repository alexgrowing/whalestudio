import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalAbelianSchemeTorsionRationalFieldPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TorsRigid

theorem epi_spMap_field {k Ω : Type} [Field k] [Field Ω] (σ : k →+* Ω) : Epi (spMap σ) := by
  letI := σ.toAlgebra
  haveI : Flat (spMap σ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem torsion_rigid : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (K L : Type) [Field K] [Field L] (y : Sp K ⟶ Xo.XF c) (x : Over.mk (y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G), x ^ l.M' = 1 → ∀ κ₁ κ₂ : Sp L ⟶ Sp K, κ₁ ≫ y = κ₂ ≫ y → κ₁ ≫ x.left = κ₂ ≫ x.left := by
  intro E _ _ _ H Dw l Xo c φ K L _ _ y x hx κ₁ κ₂ hκ
  obtain ⟨⟨p, ψ⟩, hyp⟩ := (Scheme.SpecToEquivOfField K (Xo.XF c)).symm.surjective y
  let k : Type := (Xo.XF c).residueField p
  let y₀ : Sp k ⟶ Xo.XF c := (Xo.XF c).fromSpecResidueField p
  let φ' : k →+* K := ψ.hom
  have hy : y = spMap φ' ≫ y₀ := hyp.symm
  let K' := AlgebraicClosure K
  let ιK : K →+* K' := algebraMap K K'
  haveI := epi_spMap_field ιK
  let j : Over.mk (spMap (ιK.comp φ') ≫ y₀ ≫ pullback.fst _ _) ⟶
      Over.mk (y ≫ pullback.fst _ _) :=
    Over.homMk (spMap ιK) (by
      simp only [Over.mk_hom, hy, Category.assoc]
      rw [← Category.assoc (spMap ιK), ← spMap_comp])
  have hx' : (j ≫ x) ^ l.M' = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨x₀, -, hx₀⟩ := GlobalTheory.T.universalAbelianScheme_torsion_rational_fieldPoint Xo c φ k K' (ιK.comp φ') y₀ (j ≫ x) hx'
  have hxl : x.left = spMap φ' ≫ x₀.left := by
    rw [← cancel_epi (spMap ιK)]
    have : spMap ιK ≫ x.left = spMap (ιK.comp φ') ≫ x₀.left := hx₀
    rw [this, ← Category.assoc, ← spMap_comp]
  have hκ' : κ₁ ≫ spMap φ' = κ₂ ≫ spMap φ' := by
    rw [← cancel_mono y₀]
    simpa only [hy, Category.assoc] using hκ
  rw [hxl, ← Category.assoc, hκ', Category.assoc]

end GlobalTheory.TorsRigid
