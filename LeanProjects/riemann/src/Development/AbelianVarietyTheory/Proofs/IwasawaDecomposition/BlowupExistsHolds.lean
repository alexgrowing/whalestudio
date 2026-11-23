import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OpenImmersionCompStructureEqGeneric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryIdealPowerMapsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericPreimageEqRangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseImageBoundaryPowerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCartierOnNormalizedBlowupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalizedBlowupPolarizationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleTwistBlowupEventuallyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteNormalizationIsoStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.TorRef

theorem blowExSt : BlowExSt := by
  have h1 := GlobalTheory.T.boundary_ideal_power_maps
  have h5 := GlobalTheory.T.generic_preimage_eq_range
  have h6 := GlobalTheory.T.dense_image_boundary_power
  have h2b := GlobalTheory.T.exists_cartier_on_normalized_blowup
  have h3 := GlobalTheory.T.normalized_blowup_polarization
  have h4 := GlobalTheory.T.ample_twist_blowup_eventually
  have h2n := GlobalTheory.T.exists_finite_normalization_iso

  intro E _ _ _ H D l Xo c X Y BY k ρ hρ hamp hsupp
  obtain ⟨n, hn, hT⟩ := h1 E H D l Xo c X Y BY k ρ hρ hamp hsupp
  have htop := h5 E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) X Y ρ hρ
  have hdense := h6 E H D l Xo c X Y BY ρ n hρ htop hsupp
  have := c.fin
  have : NumberField c.F := {}
  have := X.flat
  obtain ⟨X', b, hb, hbs, hbiso⟩ := GlobalTheory.ProjBlowup.exists_blowup X.s X.proj
    (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X))
  have hbU := hbiso (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).support.compl fun x hx => hx
  have hXn : GlobalTheory.IsNormalScheme X.X := .of_pred X.normal
  let U : X.X.Opens := (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).support.compl
  have e₀ : (b ⁻¹ᵁ U).ι ≫ b = b ∣_ U ≫ U.ι := (morphismRestrict_ι _ _).symm
  have : IsOpenImmersion ((b ⁻¹ᵁ (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).support.compl).ι ≫ b) := by
    rw [e₀]; infer_instance
  have hfl : Flat ((b ⁻¹ᵁ (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).support.compl).ι ≫ b ≫ X.s) := by
    rw [← Category.assoc]; infer_instance
  have hV : GlobalTheory.IsNormalScheme (b ⁻¹ᵁ (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).support.compl).toScheme :=
    .of_isOpenImmersion ((b ⁻¹ᵁ (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).support.compl).ι ≫ b)
  obtain ⟨N, ν, hν, hN, hproj, hflat, hiso', hd'⟩ := h2n c.F X' (b ≫ X.s) _ hbs hV.pred hfl
  have hiso : IsIso (ν ∣_ (b ⁻¹ᵁ (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).support.compl)) := hiso'
  have hd : Dense ((ν ⁻¹ᵁ (b ⁻¹ᵁ (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).support.compl) : N.Opens) :
      Set N) := hd'
  obtain ⟨EX, hEX⟩ := h2b c.F X.X X' N X.s _ b ν X.proj hdense hb hν hN hiso hd
  obtain ⟨e, he₁, he₂⟩ := h3 E H D l Xo c X Y BY k n ρ X' N b ν hρ hamp hsupp hn hT hb hν hN hiso hd
  obtain ⟨t', ⟨m'⟩⟩ := exists_sab (ν ≫ b) X.t
  have hg : (Y.jQ ≫ e.hom ≫ pullback.fst _ _) ≫ ν ≫ b = X.jQ ≫ pullback.fst _ _ := by
    simp only [Category.assoc, he₂, reassoc_of% hρ]
  obtain ⟨m'', -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m' (hg ▸ X.m)
  have hpt : ∀ y : gen Y, (ν ≫ b) (pullback.fst (ν ≫ b ≫ X.s) (spMap (algebraMap (𝓞 c.F) c.F)) (e.hom y)) =
      genι X (ρ y) := fun y => by
    have := congrArg (fun f : gen Y ⟶ X.X => f y) he₂
    simpa only [Scheme.Hom.comp_apply] using this
  have hcoe : (⇑(Y.jQ ≫ e.hom)) = ⇑e.hom ∘ ⇑Y.jQ := funext fun x => Scheme.Hom.comp_apply _ _ x
  have hsurj : Function.Surjective e.hom := fun x => ⟨e.inv x, by
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl⟩
  have hinj : Function.Injective e.hom := fun x x' h => by
    have := congrArg e.inv h
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e.hom_inv_id] at this
  let Z : GMod Xo c :=
    { X := N
      s := ν ≫ b ≫ X.s
      normal := hN
      proj := hproj
      flat := hflat
      jQ := Y.jQ ≫ e.hom
      jQ_over := by rw [Category.assoc, he₁]; exact Y.jQ_over
      jQ_open := by have := Y.jQ_open; infer_instance
      jQ_dense := by
        rw [hcoe]
        exact DenseRange.comp hsurj.denseRange Y.jQ_dense e.hom.continuous
      t := t'
      oF := X.oF
      m0 := X.m0
      m := by simpa only [Category.assoc] using m''
      ab_gen := by
        ext x
        obtain ⟨y, rfl⟩ := hsurj x
        rw [Set.mem_preimage, ← GlobalTheory.OneArcCompare.mem_abLocus_pullback X.t.semi m'.cart.1, hpt,
          show genι X (ρ y) ∈ abLocus X.t.G ↔ ρ y ∈ genι X ⁻¹' abLocus X.t.G from Iff.rfl, X.ab_gen,
          ← Set.mem_preimage, htop, hcoe, Set.range_comp, hinj.mem_set_image] }
  refine ⟨Z, ν ≫ b, e, _, EX, n, hn, ?_, Category.assoc _ _ _, rfl, hEX, ?_, ?_, h4 c.F X.X X' N X.s _ b ν EX X.proj hb hν hEX⟩
  · show (Y.jQ ≫ e.hom) ≫ pullback.fst _ _ ≫ ν ≫ b = X.jQ ≫ pullback.fst _ _
    simpa only [Category.assoc] using hg
  · show (EX.idealSheaf).comap (e.hom ≫ pullback.fst (ν ≫ b ≫ X.s) (spMap (algebraMap (𝓞 c.F) c.F))) = _
    rw [hEX, ← Scheme.IdealSheafData.comap_comp, Category.assoc, he₂, hT]
  · show _ = Scheme.IdealSheafData.map _ (e.hom ≫ pullback.fst (ν ≫ b ≫ X.s) (spMap (algebraMap (𝓞 c.F) c.F)) ≫ ν ≫ b)
    rw [he₂]

end GlobalTheory.TorRef
