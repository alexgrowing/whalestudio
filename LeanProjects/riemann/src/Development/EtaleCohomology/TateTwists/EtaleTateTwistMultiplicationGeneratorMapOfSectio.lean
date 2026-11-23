import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleTateTwistTensorIsoOfGeneratorMapIso

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations.TwMulGenMap

def twSec : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ

theorem nsmul_congr {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (n m : ℕ)
    (h : (n : ZMod q) = m) (x : M) : n • x = m • x := by
  have hn : (n : ULift.{1} (ZMod q)) = ULift.up (n : ZMod q) := by ext; simp
  have hm : (m : ULift.{1} (ZMod q)) = ULift.up (m : ZMod q) := by ext; simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), hn, hm, h]

theorem val_mul {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) (i j k : ℤ) (hk : i + j = k) :
    ((((a ^ i : (ZMod q)ˣ) : ZMod q).val * ((a ^ j : (ZMod q)ˣ) : ZMod q).val : ℕ) : ZMod q) =
      ((((a ^ k : (ZMod q)ˣ) : ZMod q).val : ℕ) : ZMod q) := by
  rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← Units.val_mul,
    ← zpow_add, hk]

theorem sec_map_nsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℕ)
    (x : Sec F U) : Sec.map φ (n • x) = n • Sec.map φ x := map_nsmul _ _ _

open LateralTheory.EtaleFoundations.TwMulPf in
theorem genMap_of (h : twSec) : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists := by
  intro q _ i j k T μ _ hk
  let π : (sgl T).X 0 ⟶ T := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 T).hom
  have hπ : π ≫ sglι T = 𝟙 _ := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 T).hom_inv_id
  let e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec T U := fun U ζ =>
    Sec.map π (μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)))
  have hnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    simp only [e]
    rw [sec_res_map, μ.nat, sec_res_map, sec_res_map, (h q i).2.2.2.1, (h q j).2.2.2.1]
  have hrel : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
      e U ξ = ((a ^ k : (ZMod q)ˣ) : ZMod q).val • e U ζ := by
    intro U ζ ξ a hξ
    simp only [e]
    rw [(h q i).2.2.2.2.1 U ζ ξ a hξ, (h q j).2.2.2.2.1 U ζ ξ a hξ]
    rw [sec_map_nsmul, sec_map_nsmul, map_nsmul, map_nsmul, LinearMap.smul_apply, smul_smul,
      sec_map_nsmul, mul_comm, nsmul_congr _ _ (val_mul a i j k hk)]
  obtain ⟨φ, hφ, -⟩ := (h q k).2.2.2.2.2 T e hnat hrel
  refine ⟨φ, fun U ζ => ?_⟩
  rw [hφ U ζ]
  simp only [e]
  rw [sec_map_comp, hπ, sec_map_id]

end LateralTheory.EtaleFoundations.TwMulGenMap

theorem LateralTheory.EtaleFoundations.etale_tate_twist_multiplication_generator_map_of_section_description (h : LateralTheory.EtaleFoundations.TwMulGenMap.twSec) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists :=
  LateralTheory.EtaleFoundations.TwMulGenMap.genMap_of h
