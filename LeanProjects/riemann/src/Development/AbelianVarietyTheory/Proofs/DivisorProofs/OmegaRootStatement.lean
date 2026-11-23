import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteModelOfExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutsSecOfIsLat
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.LineNorm (IsTanBasis)
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
open GlobalTheory.OmegaHT
open GlobalTheory.GroupBplus GlobalTheory.BplusDescent

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OmegaHT

theorem preimage_le_iSup_affOp {X Y : Scheme.{0}} [IsIntegral X] (f : Y ⟶ X) (V : X.Opens) :
    f ⁻¹ᵁ V ≤ ⨆ U : {U : AffOp X // U.1 ≤ V}, f ⁻¹ᵁ U.1.1 := by
  intro y hy
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (a := f y) hy V.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨U, hU, ⟨⟨f y, hyU⟩⟩⟩, hUV⟩, hyU⟩

theorem resG_resG_root {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG X h' (resG X h a) = resG X (h'.trans h) a := by
  change (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op).hom a = _
  rw [← Functor.map_comp]
  rfl

theorem exists_cover_root : RootSt := by
  intro O _ _ _ _ B hB p _ a ha
  obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (p : Kbar B.X) ha
  let K' : IntermediateField B.X.functionField (Kbar B.X) := IntermediateField.adjoin B.X.functionField {ρ}
  have hK : FiniteDimensional B.X.functionField K' :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ρ)
  obtain ⟨B', f, γ, hN, hd, -, hinj, -, hres, hrange⟩ := exists_normalization_in O B hB K' hK
  have hex : ∀ U : AffOp B.X, ∃ x : Γ(B'.X, f.f ⁻¹ᵁ U.1), (γ U x : Kbar B.X) = ρ := fun U => by
    have hm : ρ ∈ integralClosure Γ(B.X, U.1) (Kbar B.X) := mem_of_pow_mem ha (hρ ▸ natCast_mem _ p)
    have h1 : (⟨ρ, hm⟩ : U.Bp) ∈ (γ U).range := by
      rw [hrange, mem_ringOver]
      exact IntermediateField.mem_adjoin_simple_self _ ρ
    obtain ⟨x, hx⟩ := h1
    exact ⟨x, congrArg Subtype.val hx⟩
  choose x hx using hex
  have hxres : ∀ (U U' : AffOp B.X) (hle : U'.1 ≤ U.1), resG B'.X (f.f.preimage_mono hle) (x U) = x U' := by
    intro U U' hle
    apply hinj U'
    apply Subtype.ext
    rw [hx U', ← hx U]
    exact congrArg Subtype.val (hres U U' hle (x U))
  have hcov : (⊤ : B'.X.Opens) ≤ ⨆ U : {U : AffOp B.X // U.1 ≤ ⊤}, f.f ⁻¹ᵁ U.1.1 := preimage_le_iSup_affOp f.f ⊤
  obtain ⟨π, hπ⟩ := GlobalTheory.LB.exists_fun_of_cover (V := ⊤) (fun U : {U : AffOp B.X // U.1 ≤ ⊤} => f.f ⁻¹ᵁ U.1.1)
    (fun _ => le_top) hcov (fun U => x U.1) (fun U U' => by
      refine GlobalTheory.LB.fun_ext_of_cover (fun W : {W : AffOp B.X // W.1 ≤ U.1.1 ⊓ U'.1.1} => f.f ⁻¹ᵁ W.1.1)
        (fun W => f.f.preimage_mono W.2) (preimage_le_iSup_affOp f.f (U.1.1 ⊓ U'.1.1)) fun W => ?_
      exact ((resG_resG_root _ _ _).trans (hxres U.1 W.1 (W.2.trans inf_le_left))).trans
        ((resG_resG_root _ _ _).trans (hxres U'.1 W.1 (W.2.trans inf_le_right))).symm)
  refine ⟨B', f, π, hN, hd, 1, ?_⟩
  rw [Units.val_one, one_mul]
  refine GlobalTheory.LB.fun_ext_of_cover (V := ⊤) (fun U : {U : AffOp B.X // U.1 ≤ ⊤} => f.f ⁻¹ᵁ U.1.1)
    (fun _ => le_top) hcov fun U => ?_
  rw [map_pow, map_natCast, hπ U]
  apply hinj U.1
  apply Subtype.ext
  rw [map_pow, map_natCast, SubmonoidClass.coe_pow, hx, hρ]
  simp

end GlobalTheory.OmegaHT

end
