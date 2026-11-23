import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaRootStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeNonzeroInFunctionField
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain)
open GlobalTheory.ChainPts.PullHT (pullA)
open scoped TensorProduct
open GlobalTheory.ChainPts
open GlobalTheory.GroupBplus GlobalTheory.BplusDescent

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChainPts

theorem exists_cover_global_elt (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (B : GlobalTheory.Vert.Model O) (hB : GlobalTheory.IsNormalScheme B.X) (ρ : Kbar B.X)
    (hm : ∀ U : AffOp B.X, ρ ∈ integralClosure Γ(B.X, U.1) (Kbar B.X)) :
    ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (γ : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp)
      (π : Γ(B'.X, ⊤)), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ (∀ U, Function.Injective (γ U)) ∧
      ∀ U : AffOp B.X, (γ U (resG B'.X le_top π) : Kbar B.X) = ρ := by
  let K' : IntermediateField B.X.functionField (Kbar B.X) := IntermediateField.adjoin B.X.functionField {ρ}
  have hK : FiniteDimensional B.X.functionField K' :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ρ)
  obtain ⟨B', f, γ, hN, hd, -, hinj, -, hres, hrange⟩ := exists_normalization_in O B hB K' hK
  have hex : ∀ U : AffOp B.X, ∃ x : Γ(B'.X, f.f ⁻¹ᵁ U.1), (γ U x : Kbar B.X) = ρ := fun U => by
    have h1 : (⟨ρ, hm U⟩ : U.Bp) ∈ (γ U).range := by
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
  have hcov : (⊤ : B'.X.Opens) ≤ ⨆ U : {U : AffOp B.X // U.1 ≤ ⊤}, f.f ⁻¹ᵁ U.1.1 :=
    GlobalTheory.OmegaHT.preimage_le_iSup_affOp f.f ⊤
  obtain ⟨π, hπ⟩ := GlobalTheory.LB.exists_fun_of_cover (V := ⊤) (fun U : {U : AffOp B.X // U.1 ≤ ⊤} => f.f ⁻¹ᵁ U.1.1)
    (fun _ => le_top) hcov (fun U => x U.1) (fun U U' => by
      refine GlobalTheory.LB.fun_ext_of_cover (fun W : {W : AffOp B.X // W.1 ≤ U.1.1 ⊓ U'.1.1} => f.f ⁻¹ᵁ W.1.1)
        (fun W => f.f.preimage_mono W.2) (GlobalTheory.OmegaHT.preimage_le_iSup_affOp f.f (U.1.1 ⊓ U'.1.1)) fun W => ?_
      exact ((GlobalTheory.OmegaHT.resG_resG_root _ _ _).trans (hxres U.1 W.1 (W.2.trans inf_le_left))).trans
        ((GlobalTheory.OmegaHT.resG_resG_root _ _ _).trans (hxres U'.1 W.1 (W.2.trans inf_le_right))).symm)
  exact ⟨B', f, γ, π, hN, hd, hinj, fun U => by rw [hπ ⟨U, le_top⟩]; exact hx U⟩

theorem exists_cover_primitiveRoot : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ n : ℕ, ∃ (B' : GlobalTheory.Vert.Model O) (g : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B'.X ∧ g.relDim = 0 ∧ ∃ ζ : Γ(B'.X, ⊤), IsPrimitiveRoot ζ (p ^ n) := by
  intro O _ _ _ p _ _ _ B hB n
  have hp : p.Prime := Fact.out
  haveI : NeZero ((p ^ n : ℕ) : Kbar B.X) :=
    ⟨by rw [Nat.cast_pow]; exact pow_ne_zero _ (GlobalTheory.Vert.Model.natCast_prime_ne_zero_kbar O p B)⟩
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨ρ, hρ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Kbar B.X) (p ^ n)
  obtain ⟨B', f, γ, π, hN, hd, hinj, hπ⟩ := exists_cover_global_elt O B hB ρ fun U =>
    mem_of_pow_mem (pow_pos hp.pos n) (hρ.pow_eq_one ▸ one_mem _)
  refine ⟨B', f, hN, hd, π, ?_, fun l hl => ?_⟩
  · refine GlobalTheory.LB.fun_ext_of_cover (V := ⊤) (fun U : {U : AffOp B.X // U.1 ≤ ⊤} => f.f ⁻¹ᵁ U.1.1)
      (fun _ => le_top) (GlobalTheory.OmegaHT.preimage_le_iSup_affOp f.f ⊤) fun U => ?_
    rw [map_pow, map_one]
    apply hinj U.1
    apply Subtype.ext
    rw [map_pow, map_one, SubmonoidClass.coe_pow, hπ, hρ.pow_eq_one]
    rfl
  · obtain ⟨y⟩ : Nonempty B.X := inferInstance
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := B.X.isBasis_affineOpens.exists_subset_of_mem_open (a := y) (Set.mem_univ y) isOpen_univ
    let V : AffOp B.X := ⟨U, hU, ⟨⟨y, hyU⟩⟩⟩
    apply hρ.dvd_of_pow_eq_one
    rw [← hπ V, ← SubmonoidClass.coe_pow, ← map_pow, ← map_pow, hl, map_one, map_one]
    rfl

end GlobalTheory.ChainPts

end
