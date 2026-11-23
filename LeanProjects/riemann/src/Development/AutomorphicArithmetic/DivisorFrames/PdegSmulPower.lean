import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AutomorphicArithmetic.DivisorFrames.PdegEqOfIsDeg
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem isProper_strHom_of_not_mem_gen {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField O) p] [Finite (ResidueField O)] (B : Vert.Model O)
    {Z : Scheme.{0}} (i : Z ⟶ B.X) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)]
    (h : i (genericPoint Z) ∉ B.gen) : IsProper (strHom (ZMod p) Z) := by
  let φ : O →+* Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of O)).inv ≫ (i ≫ B.str).appTop).hom
  have hφ : ∀ a ∈ maximalIdeal O, φ a = 0 := fun a ha => by
    have e : φ a = i.appTop (B.const a) := by
      rw [Vert.Model.const, Vert.Model.const_eq]
      simp only [φ, Scheme.Hom.comp_appTop]
      rfl
    have h0 : B.str (i (genericPoint Z)) = closedPoint O := not_not.1 (mt Vert.Model.mem_gen.2 h)
    have h1 : genericPoint Z ∉ Z.basicOpen (φ a) := by
      rw [e, ← Scheme.preimage_basicOpen_top]
      intro hx
      exact Vert.Model.mem_basicOpen_const.1 hx (h0 ▸ ha)
    rw [← basicOpen_eq_bot_iff]
    by_contra hne
    refine h1 (((genericPoint_spec Z).mem_open_set_iff (Z.basicOpen (φ a)).isOpen).2 ?_)
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    exact ⟨x, trivial, hx⟩
  let ψ : ResidueField O →+* Γ(Z, ⊤) := Ideal.Quotient.lift _ φ hφ
  letI : Algebra (ZMod p) (ResidueField O) := ZMod.algebra _ p
  let g : Z ⟶ Sp (ResidueField O) := Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
  have h₁ : g ≫ spMap (residue O) = i ≫ B.str := by
    have e : CommRingCat.ofHom (residue O) ≫ CommRingCat.ofHom ψ =
        (Scheme.ΓSpecIso (.of O)).inv ≫ (i ≫ B.str).appTop := rfl
    refine (Category.assoc _ _ _).trans ((congrArg (Z.toSpecΓ ≫ ·)
      ((Spec.map_comp _ _).symm.trans (congrArg Spec.map e))).trans ?_)
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have h₂ : strHom (ZMod p) Z = g ≫ spMap (algebraMap (ZMod p) _) :=
    ((Category.assoc _ _ _).trans (congrArg (Z.toSpecΓ ≫ ·) ((Spec.map_comp _ _).symm.trans
      (congrArg (fun f => Spec.map (CommRingCat.ofHom f))
        (RingHom.ext_zmod (ψ.comp (algebraMap (ZMod p) _)) (algebraMap _ _)))))).symm
  have : IsProper (g ≫ spMap (residue O)) := h₁ ▸ inferInstance
  have : IsProper g := IsProper.of_comp g (spMap (residue O))
  have : IsFinite (spMap (algebraMap (ZMod p) (ResidueField O))) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 Module.Finite.of_finite)
  rw [h₂]
  infer_instance

theorem UpperTheory.pdeg_smul_power :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharP (ResidueField O) p] [Finite (ResidueField O)] (B : Vert.Model O) (d m : ℕ) (L N : Fin d → LB B.X) (hL : ∀ k, (L k).IsLB) (hN : ∀ k, (N k).IsLB), (∀ k, cls (N k) (hN k) = m • cls (L k) (hL k)) → ∀ ζ : B.X, ζ ∉ B.gen → pdeg p N ζ = (m : ℤ) ^ d * pdeg p L ζ := by
  intro O _ _ _ p _ _ _ B d m L N hL hN e ζ hζ
  by_cases h : ∃ a, IsDeg p L ζ a
  · obtain ⟨a, Z, i, hi, hZ, alg, hz, hd, ha⟩ := h
    rw [UpperTheory.pdeg_eq_of_isDeg p B.X d L hL ζ _ ⟨Z, i, hi, hZ, alg, hz, hd, rfl⟩,
      UpperTheory.pdeg_eq_of_isDeg p B.X d N hN ζ _ ⟨Z, i, hi, hZ, alg, hz, hd, rfl⟩]
    have := isProper_strHom_of_not_mem_gen p B i (hz ▸ hζ)
    obtain ⟨A, hA⟩ := B.exists_isAmpleLB
    have H := (hA.pull_of_isClosedImmersion i).diffVanish_chiPic_of_isProper
      (algebraMap_eq_strHom (ZMod p) Z) (structureModule Z) (d := d) (by rw [GlobalTheory.QCoh.suppDim_structureModule, hd])
    rw [H.interNum_of_cls_eq_zsmul (P := fun j => (L j).pull i) (Q := fun j => (N j).pull i)
      (fun j => pull_isLB (hL j) i) (fun j => pull_isLB (hN j) i) (fun _ => (m : ℤ)) fun j => by
        rw [CechPic.cls_pull (hN j), CechPic.cls_pull (hL j), e, map_nsmul, natCast_zsmul]]
    simp
  · have h' : ¬ ∃ a, IsDeg p N ζ a := fun ⟨_, Z, i, hi, hZ, alg, hz, hd, _⟩ =>
      h ⟨_, Z, i, hi, hZ, alg, hz, hd, rfl⟩
    rw [pdeg, pdeg, dif_neg h, dif_neg h', mul_zero]
