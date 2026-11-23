import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusImageFactorQuotientGoodOpenStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothTorusQuotientOfGoodOpenCoverStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftOneParameterQuotientTorusStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS.MaxTorus
open GlobalTheory.SplitTorus

theorem surjective_of_mono {S : Scheme.{0}} [Nonempty S] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (φ : Y →+ X) [Mono (torusMap S φ)] : Function.Surjective φ := by
  let π : X →+ X ⧸ φ.range := QuotientAddGroup.mk' _
  have h : π.comp φ = (0 : X →+ X ⧸ φ.range).comp φ := by
    ext y
    simp [π]
  have h' : π = 0 := by
    apply torusMap_injective (S := S)
    rw [← cancel_mono (torusMap S φ), ← torusMap_comp, ← torusMap_comp, h]
  intro x
  have : π x = 0 := by rw [h']; rfl
  exact (QuotientAddGroup.eq_zero_iff x).1 this

theorem injective_of_surjective {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (φ : Y →+ X) (h : Function.Surjective φ) (hr : Module.finrank ℤ Y ≤ Module.finrank ℤ X) :
    Function.Injective φ := by
  have h1 : Module.finrank ℤ X ≤ Module.finrank ℤ Y :=
    LinearMap.finrank_le_finrank_of_surjective (f := φ.toIntLinearMap) h
  let e : Y ≃ₗ[ℤ] X := LinearEquiv.ofFinrankEq _ _ (le_antisymm hr h1)
  exact OrzechProperty.injective_of_surjective_of_injective e.toLinearMap φ.toIntLinearMap e.injective h

theorem exists_inv {S : Scheme.{0}} [ConnectedSpace S] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (σ : splitTorus S X ⟶ splitTorus S Y) [IsMonHom σ] [Mono σ]
    (hr : Module.finrank ℤ Y ≤ Module.finrank ℤ X) : ∃ τ, τ ≫ σ = 𝟙 _ := by
  obtain ⟨φ, rfl⟩ := exists_eq_torusMap σ
  have hs := surjective_of_mono (S := S) φ
  let e : Y ≃+ X := AddEquiv.ofBijective φ ⟨injective_of_surjective φ hs hr, hs⟩
  refine ⟨torusMap S e.symm.toAddMonoidHom, ?_⟩
  rw [← torusMap_comp, ← torusMap_id]
  congr 1
  ext y
  exact e.symm_apply_apply y

theorem exists_quot_no_cocharacter : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (B : Over (Sp k)) (_ : GrpObj B) (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q ∧ ∀ f : Gm (Sp k) ⟶ B, IsMonHom f → f = 1 := by
  classical
  intro k _ _ G _ hG
  obtain ⟨hc, hsm, hsep, hqc, hgc⟩ := id hG
  have : ConnectedSpace G.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.hom
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  let P : ℕ → Prop := fun n => ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
    (i : splitTorus (Sp k) X ⟶ G), IsMonHom i ∧ (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i V) ∧ Module.finrank ℤ X = n
  have hb : ∀ n, P n → n ≤ g := by
    rintro _ ⟨X, _, _, _, i, hi, hV, rfl⟩
    obtain ⟨B, _, q, -, hd⟩ := GlobalTheory.T.exists_smooth_torus_quotient_of_goodOpen_cover k G hG X i hi hV
    obtain ⟨a, -, ha⟩ := hd g hg
    omega
  obtain ⟨n₀, h₀⟩ : ∃ n, P n := by
    obtain ⟨X', _, _, _, i', ρ, h1, -, -, -, hV⟩ := GlobalTheory.T.splitTorus_image_factor_quotient_goodOpen k G hG PUnit 1
      (inferInstanceAs (IsMonHom (toUnit _ ≫ η[G])))
    exact ⟨_, X', _, ‹_›, ‹_›, i', h1, hV, rfl⟩
  obtain ⟨X, _, _, _, i, hi, hV, hn⟩ : P (Nat.findGreatest P g) := Nat.findGreatest_spec (hb _ h₀) h₀
  obtain ⟨B, _, q, hq, -⟩ := GlobalTheory.T.exists_smooth_torus_quotient_of_goodOpen_cover k G hG X i hi hV
  refine ⟨X, _, inferInstance, inferInstance, B, _, i, q, hq, fun f hf => ?_⟩
  obtain ⟨j, hj, rfl⟩ := GlobalTheory.T.exists_lift_oneParameter_quotient_torus k G hG X B i q hq f hf
  obtain ⟨-, hqm, -, -, -, hpb, -⟩ := hq
  have : Mono (η[B]) := ⟨fun a b _ => toUnit_unique a b⟩
  have : Mono i := hpb.mono_fst_of_mono
  let φ : splitTorus (Sp k) (X × ULift.{0} ℤ) ⟶ G :=
    (torusMap _ (AddMonoidHom.inl X (ULift.{0} ℤ)) ≫ i) * (torusMap _ (AddMonoidHom.inr X (ULift.{0} ℤ)) ≫ j)
  obtain ⟨X', _, _, _, i', ρ, h1, h2, -, h3, hV'⟩ := GlobalTheory.T.splitTorus_image_factor_quotient_goodOpen k G hG (X × ULift.{0} ℤ) φ
    (by simp only [φ]; rw [Hom.mul_def]; infer_instance)
  have hr : Module.finrank ℤ X' ≤ Module.finrank ℤ X := by
    have hP : P (Module.finrank ℤ X') := ⟨X', _, ‹_›, ‹_›, i', h1, hV', rfl⟩
    rw [hn]
    exact Nat.le_findGreatest (hb _ hP) hP
  have e1 : torusMap _ (AddMonoidHom.fst X (ULift.{0} ℤ)) ≫ φ = i := by
    simp only [φ, MonObj.comp_mul, ← Category.assoc, ← torusMap_comp, AddMonoidHom.fst_comp_inl,
      AddMonoidHom.fst_comp_inr, torusMap_id, torusMap_zero, Category.id_comp, MonObj.one_comp, _root_.mul_one]
  have e2 : torusMap _ (AddMonoidHom.snd X (ULift.{0} ℤ)) ≫ φ = j := by
    simp only [φ, MonObj.comp_mul, ← Category.assoc, ← torusMap_comp, AddMonoidHom.snd_comp_inl,
      AddMonoidHom.snd_comp_inr, torusMap_id, torusMap_zero, Category.id_comp, MonObj.one_comp, _root_.one_mul]
  let σ := torusMap _ (AddMonoidHom.fst X (ULift.{0} ℤ)) ≫ ρ
  have e3 : σ ≫ i' = i := by rw [Category.assoc, h3, e1]
  have : Mono σ := mono_of_mono_fac e3
  obtain ⟨τ, hτ⟩ := exists_inv σ hr
  have e4 : i' = τ ≫ i := by rw [← e3, ← Category.assoc, hτ, Category.id_comp]
  have e5 : i ≫ q = 1 := hpb.w
  rw [← e2, ← h3, e4]
  simp only [Category.assoc, e5, MonObj.comp_one]

end GlobalTheory.SS.MaxTorus
