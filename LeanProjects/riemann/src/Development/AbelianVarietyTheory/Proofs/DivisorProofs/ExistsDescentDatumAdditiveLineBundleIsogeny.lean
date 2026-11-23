import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumCompatibleOfLineBundleIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackFstSndOfAdditiveTrivialKernStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentCocycleDefectOfCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalUnitTripleFibreProductInvariantSetGroupCooStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitTwistNormaliseDescentFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectNormalisedEqOneStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DescNorm

theorem twist_descCompat : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (u : Γ(pullback f f, ⊤)ˣ), DescCompat f L φ → DescCompat f L (twist f L φ u) := by
  intro X Y f L φ u hφ z i i' j j' hi hi' hj hj'
  have m : ∀ a b, pullback.fst f f z ∈ L.U a → pullback.snd f f z ∈ L.U b → (𝟙 (pullback f f)) z ∈ chart f L a b :=
    fun a b ha hb => ⟨ha, hb⟩
  simp only [twist, map_mul]
  rw [gm_res (𝟙 _) z le_top (m i' j' hi' hj'), gm_res (𝟙 _) z le_top (m i j hi hj), hφ z i i' j j' hi hi' hj hj']
  ac_rfl

theorem descentDatum_of_additive : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (q : A ⟶ A') (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → (∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ q = 1 → Triv (ev P (fst T B ≫ x) (snd T B))) → ∃ φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, GlobalTheory.LBDescent.chart (q ▷ B).left P i j)ˣ, GlobalTheory.LBDescent.DescCompat (q ▷ B).left P φ ∧ GlobalTheory.LBDescent.DescCocycle (q ▷ B).left P φ := by
  intro K _ _ A A' B _ _ _ q P hA hA' hB hq _ _ _ hP hadd hzero hker
  obtain ⟨φ₀, hφ₀⟩ := GlobalTheory.T.exists_descentDatumCompatible_of_lineBundle_iso _ P hP (GlobalTheory.T.lineBundle_iso_pullback_fst_snd_of_additive_trivial_kernel K A A' B q P hA hA' hB hq hP hadd hker)
  obtain ⟨τ, hτ⟩ := hzero
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_globalUnit_twist_normalise_descent_family K A A' B q P τ hP hτ φ₀ hφ₀
  have hc : DescCompat (q ▷ B).left P (twist (q ▷ B).left P φ₀ u) := twist_descCompat _ P φ₀ u hφ₀
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_descentCocycleDefect_of_compatible _ P _ hP hc
  have h1 := GlobalTheory.T.descentCocycleDefect_normalised_eq_one K A A' B q P τ hP _ D hu hD
  have h2 := GlobalTheory.T.globalUnit_tripleFibreProduct_invariant_setGroupCoordZero K A A' B q hB D
  refine ⟨twist (q ▷ B).left P φ₀ u, hc, fun w i j k hi hj hk => ?_⟩
  have e := hD _ (𝟙 _) w i j k hi hj hk
  rw [← h2 w, h1 w, _root_.one_mul, Category.id_comp, Category.id_comp, Category.id_comp] at e
  exact e.symm

end GlobalTheory.DescNorm
