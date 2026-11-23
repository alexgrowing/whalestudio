import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory

private theorem unitSec_mul {U : Scheme.{0}} (a b : (Γ(U, ⊤))ˣ) :
    unitSec (a * b) = unitSec a + unitSec b :=
  map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
    (ULift.up (Additive.ofMul a)) (ULift.up (Additive.ofMul b))

private theorem unitSec_pow {U : Scheme.{0}} (a : (Γ(U, ⊤))ˣ) (c : ℕ) :
    unitSec (a ^ c) = c • unitSec a := by
  unfold unitSec ofRings.sec
  exact map_nsmul (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U))) c
    (show (Scheme.Γ ⋙ unitsF).obj (op U) from ⟨Additive.ofMul a⟩)

private theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op
  exact (congrArg (fun f => f.hom (ULift.up (Additive.ofMul u))) h).symm

private theorem unitSec_loc {U : Scheme.{0}} (a b : (Γ(U, ⊤))ˣ) (h : unitSec a = unitSec b) :
    Loc U fun _ g => Units.map g.appTop.hom.toMonoidHom a = Units.map g.appTop.hom.toMonoidHom b := by
  have hx := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift ℤ (Scheme.Γ ⋙ unitsF)).2.1 U
    ((show (Scheme.Γ ⋙ unitsF).obj (op U) from ⟨Additive.ofMul a⟩) -
      (show (Scheme.Γ ⋙ unitsF).obj (op U) from ⟨Additive.ofMul b⟩)) (by
    rw [map_sub]
    exact sub_eq_zero.mpr h)
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ hx ?_
  intro V g hg
  rw [map_sub, sub_eq_zero] at hg
  have h2 := congrArg (fun t => Additive.toMul (ULift.down t)) hg
  exact h2

private theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => f.hom x) (φ.hom.naturality g.op)).symm

private theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := by
  simp only [Sec.res, map_add]

private theorem map_nsmul' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ)
    (a : Sec F U) : Sec.map φ (c • a) = c • Sec.map φ a :=
  map_nsmul (φ.hom.app (op U)).hom c a

private theorem kum_pow (q : ℕ) [NeZero q] {W : Scheme.{0}} (ζ : Prim q Γ(W, ⊤)) (z : (Γ(W, ⊤))ˣ)
    (hz : (z : Γ(W, ⊤)) = ζ.1) (c : ℕ) (v : (Γ(W, ⊤))ˣ) :
    kumT q W (z ^ c * v) = kumT q W v + c • resGen 1 ζ := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).2 W ζ (z ^ c * v) (z ^ (c + 1) * v) (by
      rw [← hz, pow_succ']; simp [mul_assoc])
    rw [h, ih, succ_nsmul, add_assoc]

end UpperTheory

private theorem kumT_eq_of_unitSec_eq (q : ℕ) [NeZero q] {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤)))
    (a b : (Γ(U, ⊤))ˣ) (h : unitSec a = unitSec b) : kumT q U a = kumT q U b := by
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) _ U).1
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ (UpperTheory.unitSec_loc a b h) ?_
  intro V g hg
  rw [(GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 V U g a hq, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 V U g b hq, hg]

theorem UpperTheory.kummerMap_add_of_unitSec_add :
    ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm), (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) → ∀ (V : Scheme.{0}), IsUnit (q : Γ(V, ⊤)) → ∀ (v v' : (Γ(V, ⊤))ˣ) (s : Sec (tw q 1) V), Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) V from s) + unitSec v = unitSec v' → kumT q V v' = kumT q V v + Sec.map (resι _ (tw q 1)) s := by
  intro q _ κ hκ V hq v v' s hs
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) _ V).1
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 V _ _ ((GlobalTheory.T.tateTwist_sections_locally_generated q 1).1 V s) ?_
  intro W g hg
  have hqW : IsUnit (q : Γ(W, ⊤)) := by
    have h1 := hq.map g.appTop.hom
    simpa using h1
  have hsW := congrArg (Sec.res g) hs
  rw [UpperTheory.res_add, UpperTheory.unitSec_res, UpperTheory.unitSec_res,
    UpperTheory.res_map κ g (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) V from s)] at hsW
  rw [(GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V g v' hq, UpperTheory.res_add, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V g v hq, UpperTheory.res_map]
  simp only at hsW
  rcases hg with h0 | ⟨ζ, c, hc⟩
  · have e0 : Sec.map κ (Sec.res (F := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)) g s) = 0 := by
      have h3 : Sec.res (F := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)) g s = 0 := h0
      rw [h3]
      simp only [Sec.map, map_zero]
    rw [e0, zero_add] at hsW
    rw [h0]
    simp only [Sec.map, map_zero, add_zero]
    exact (kumT_eq_of_unitSec_eq q hqW _ _ hsW).symm
  · obtain ⟨u, hu⟩ : ∃ u : (Γ(W, ⊤))ˣ, (u : Γ(W, ⊤)) = ζ.1 :=
      ⟨Units.ofPowEqOne ζ.1 q ((GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q _).1 ζ) (NeZero.ne q), rfl⟩
    have hk := hκ W ζ u hu
    simp only at hk
    have e1 : Sec.map κ (Sec.res (F := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)) g s) =
        c • unitSec u := by
      have h3 : Sec.res (F := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)) g s =
          c • (twGen 1 ζ : Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) W) := hc
      rw [h3]
      exact (UpperTheory.map_nsmul' κ c (twGen 1 ζ)).trans (by rw [hk])
    rw [e1, ← UpperTheory.unitSec_pow, ← UpperTheory.unitSec_mul] at hsW
    have h2 := kumT_eq_of_unitSec_eq q hqW _ _ hsW
    rw [UpperTheory.kum_pow q ζ u hu c] at h2
    rw [← h2, hc, UpperTheory.map_nsmul']
    rfl
