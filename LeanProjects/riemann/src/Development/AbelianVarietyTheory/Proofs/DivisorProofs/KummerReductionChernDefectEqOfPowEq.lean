import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrFamAddTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwistAltI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem defect_mul_prim (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤))
    (v w : (Γ(U, ⊤))ˣ) (h : (w : Γ(U, ⊤)) = ζ.1 * v) : defect Q q U w = defect Q q U v := by
  have hq0 : q ≠ 0 := fun h0 => NeZero.ne Q (Nat.eq_zero_of_zero_dvd (h0 ▸ hqQ))
  haveI : NeZero q := ⟨hq0⟩
  obtain ⟨ξ, hξ⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).2.2.2.2.2 q hqQ ζ
  have h1 : kumT Q U w = kumT Q U v + resGen 1 ζ := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting Q).2 U ζ v w h
  have h2 : (redMap Q q 1).app U 0 (resGen 1 ζ) = resGen 1 ξ := GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ 1 U ζ ξ hξ
  have h3 : ((w ^ (Q / q) : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) = ξ.1 * ((v ^ (Q / q) : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) := by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h, hξ, mul_pow]
  have h4 : kumT q U (w ^ (Q / q)) = kumT q U (v ^ (Q / q)) + resGen 1 ξ :=
    (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).2 U ξ _ _ h3
  unfold defect
  rw [h1, h4, map_add, h2]
  abel

theorem defect_mul_prim_pow (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤))
    (v : (Γ(U, ⊤))ˣ) (a : ℕ) : ∀ w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ a * v →
      defect Q q U w = defect Q q U v := by
  have hζ : IsUnit ζ.1 := IsUnit.of_pow_eq_one ((GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).1 ζ) (NeZero.ne Q)
  induction a with
  | zero =>
    intro w hw
    rw [pow_zero, one_mul] at hw
    rw [Units.ext hw]
  | succ a ih =>
    intro w hw
    have e : ((hζ.unit ^ a * v : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) = ζ.1 ^ a * v := by simp
    rw [defect_mul_prim Q q hqQ U ζ (hζ.unit ^ a * v) w (by rw [hw, e, pow_succ]; ring)]
    exact ih _ e

end GlobalTheory.EtC.RedChern

namespace GlobalTheory.EtC.RedChern

theorem defect_eq_of_pow_eq (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) (U : Scheme.{0}) (v w : (Γ(U, ⊤))ˣ)
    (hQ : IsUnit (Q : Γ(U, ⊤))) (hvw : v ^ Q = w ^ Q) : defect Q q U v = defect Q q U w := by
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) ((res _ (tw q 1)).X 0) U).1 _ _ ?_
  refine loc_bind ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).1 hQ) fun V g hV => ?_
  obtain ⟨ζ⟩ := hV
  set v' : (Γ(V, ⊤))ˣ := Units.map g.appTop.hom.toMonoidHom v
  set w' : (Γ(V, ⊤))ˣ := Units.map g.appTop.hom.toMonoidHom w
  have hx : (((w' * v'⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤))) ^ Q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, ← map_pow, ← map_pow, ← hvw, mul_inv_cancel, Units.val_one]
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q V).2.2.1 ζ _ hx) fun W k ⟨a, ha⟩ => ?_
  rw [GlobalTheory.T.kummerReductionChernDefect_restriction Q q hqQ W U (k ≫ g) v hQ, GlobalTheory.T.kummerReductionChernDefect_restriction Q q hqQ W U (k ≫ g) w hQ]
  symm
  refine defect_mul_prim_pow Q q hqQ W (ζ.map k.appTop.hom) _ a _ ?_
  have e1 : ∀ u : (Γ(U, ⊤))ˣ, ((Units.map (k ≫ g).appTop.hom.toMonoidHom u : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) =
      k.appTop.hom ((Units.map g.appTop.hom.toMonoidHom u : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) := fun u => rfl
  rw [e1, e1]
  change k.appTop.hom (w' : Γ(V, ⊤)) = (k.appTop.hom ζ.1) ^ a * k.appTop.hom (v' : Γ(V, ⊤))
  rw [← ha, ← map_mul, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

end GlobalTheory.EtC.RedChern
