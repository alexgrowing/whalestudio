import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MorphismToLocalizedModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem sabMap_of_gmod_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → π ≫ X.s = Z.s → Nonempty (SABMap Z.t X.t π) := by
  intro E _ _ _ H D l Xo c X Z π hj hs
  haveI := c.fin
  haveI : NumberField c.F := ⟨⟩
  have hded := (GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).1
  have hloc : @IsLocalization.Away (𝓞 c.F) _ 1 (𝓞 c.F) _ (RingHom.id (𝓞 c.F)).toAlgebra := by
    letI := (RingHom.id (𝓞 c.F)).toAlgebra
    exact IsLocalization.away_of_isUnit_of_bijective _ isUnit_one Function.bijective_id
  have hid : spMap (RingHom.id (𝓞 c.F)) = 𝟙 _ := GlobalTheory.LevelCover.spMap_id' _
  haveI : IsIso (spMap (RingHom.id (𝓞 c.F))) := by rw [hid]; infer_instance
  set e := pullback.fst Z.s (spMap (RingHom.id (𝓞 c.F))) with he
  have hsnd : pullback.snd Z.s (spMap (RingHom.id (𝓞 c.F))) = e ≫ Z.s := by
    rw [he, pullback.condition, hid, Category.comp_id]
  have hF : (e ≫ π) ≫ X.s = pullback.snd _ _ := by rw [Category.assoc, hs, hsnd]
  have hjF : ∀ u : Xo.XF c ⟶ pullback Z.s (spMap (RingHom.id (𝓞 c.F))), u ≫ pullback.fst _ _ = Z.j →
      u ≫ e ≫ π = X.j := fun u hu => by rw [← Category.assoc]; exact (congrArg (· ≫ π) hu).trans hj
  obtain ⟨f, t, m₁, m₂, hf, hfj, -⟩ := dominates_of_map_on_part E H D l Xo c Z (𝓞 c.F) 1 (RingHom.id _)
    (algebraMap (𝓞 c.F) c.F) X hded (RingHom.comp_id _) hloc (e ≫ π) hF hjF

  obtain ⟨-, -, -, -, -, hdom, -⟩ :=
    GlobalTheory.genericPart_dense_proOpen (𝓞 c.F) c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open Z.jQ_dense
  haveI : IsDominant Z.j := hdom
  haveI : IsProper X.s := by
    obtain ⟨N, i, hi, e'⟩ := X.proj
    have := isProper_str (𝓞 c.F) N
    rw [← e']; infer_instance
  haveI : ∀ x, _root_.IsReduced (Z.X.presheaf.stalk x) := fun x => by
    obtain ⟨_, _⟩ := Z.normal x
    infer_instance
  haveI : IsReduced Z.X := isReduced_of_isReduced_stalk _
  have hfπ : inv e ≫ f = π := by
    refine ext_of_isDominant_of_isSeparated X.s ?_ Z.j ?_
    · rw [Category.assoc, hf, hs, hsnd, IsIso.inv_hom_id_assoc]
    · rw [hj, ← Category.assoc]
      exact hfj _ (by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id])
  obtain ⟨m', -⟩ := GlobalTheory.LevelCover.sab_cancel m₁ (GlobalTheory.ObjComp.sabMapId Z.t) (inv e) (IsIso.inv_hom_id e)
  obtain ⟨n, -⟩ := GlobalTheory.LevelCover.sab_comp m' m₂ hfπ
  exact ⟨n⟩

end GlobalTheory.TorRef
