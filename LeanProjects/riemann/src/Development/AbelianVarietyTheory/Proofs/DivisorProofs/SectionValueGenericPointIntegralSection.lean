import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HRedFst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.IntEval
open GlobalTheory.UT.CoefBasic GlobalTheory.BoxExpansion GlobalTheory.UT.EvalZero

theorem alg_value_at {M K : Type} [CommRing M] [Fintype K] {k : ℕ} {P E Fv : Mˣ} {Sσ sA cv cl : M} {u d : K → M}
    (h₁ : Sσ = (P ^ k).val * sA) (h₂ : Sσ = ∑ i, u i) (h₃ : sA = cv * (E ^ k).val) (h₄ : P.val * E.val = cl * Fv.val)
    (h₅ : ∀ i, u i = d i * (Fv ^ k).val) : cv * cl ^ k = ∑ i, d i := by
  refine (Fv ^ k).mul_left_inj.1 ?_
  rw [Finset.sum_mul, ← Finset.sum_congr rfl fun i _ => h₅ i, ← h₂, h₁, h₃]
  simp only [Units.val_pow_eq_pow_val]
  calc cv * cl ^ k * Fv.val ^ k = cv * (cl * Fv.val) ^ k := by ring
    _ = cv * (P.val * E.val) ^ k := by rw [h₄]
    _ = _ := by ring

theorem value_at_section : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (e : FrAt x) (h : 𝟙_ (Over (Sp R)) ⟶ G) (l : FractionRing R) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))), IntTerm.Ext U x h → (∀ (z : (TF (R := R) (FractionRing R)).left) (JA : ((TF (R := R) (FractionRing R)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := R) (FractionRing R)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (Geo.Tor.gw (Y := (TF (R := R) (FractionRing R)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG (toUnit (TF (R := R) (FractionRing R)) ≫ h).left) (fun _ => JA x.left)).val * (val (Z := (TF (R := R) (FractionRing R)).left) e (𝟙 _) z JA).val = GlobalTheory.UT.cst (FractionRing R) z l * (val f (toUnit (TF (R := R) (FractionRing R))).left z JG).val) → ∀ (k : ℕ) (s : SecA A (FractionRing R) k) (σ' : U.SecGF (FractionRing R) k), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) (FractionRing R)) A.A).left (U.genF (FractionRing R)).left s (UnifPre.gFK (G := G) (FractionRing R)) (𝟙 _) σ' → ∀ (n : ℕ) (c : Fin n → FractionRing R) (σ : Fin n → H0 U.LG.L k), GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) (FractionRing R)) (fun _ => (k : ℤ)) σ' (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) (FractionRing R)) (fun i => scal (fst (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left (c i)) → ∀ xs : Fin n → R, (∀ (i : Fin n) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι), Good U.LG.L z J → sval (σ i) (r ≫ h.left) z J = Geo.Tor.cst r z (xs i) * (val f r z J ^ k).val) → ∀ v : FractionRing R, ValAt s x e v → v * l ^ k = ∑ i, c i * algebraMap R (FractionRing R) (xs i) := by
  intro R _ _ I D A G _ _ U w₀ x e h l f hExt hF k s σ' hR n c σ hσ xs hxs v hv
  obtain ⟨z⟩ := exists_pt (R := R) (F := FractionRing R)
  obtain ⟨JA, hA⟩ := exists_good' (Z := (TFK (R := R) (FractionRing R)).left) A.isLB z
  obtain ⟨JG, hG⟩ := exists_good' (Z := (TFK (R := R) (FractionRing R)).left) U.LG.isLB z
  let r : TFK (R := R) (FractionRing R) ⟶ UnifPre.GF (G := G) (FractionRing R) := lift (𝟙 _) (x ≫ U.gen.inv)
  have e₁ : r.left ≫ (snd (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left =
      x.left ≫ U.gen.inv.left := by
    rw [← Over.comp_left, lift_snd]; rfl
  have e₂ : r.left ≫ (U.genF (FractionRing R)).left = (ptSecT A.A x).left := by
    rw [← Over.comp_left]
    congr 1
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simp [r, ptSecT]
    · simp [r, ptSecT]
  have e₀ : (toUnit (TF (R := R) (FractionRing R))).left = jFK (R := R) (FractionRing R) ≫ jK R := by
    simpa using Over.w (toUnit (TF (R := R) (FractionRing R)))
  have e₃ : r.left ≫ UnifPre.gFK (G := G) (FractionRing R) = (toUnit (TF (R := R) (FractionRing R)) ≫ h).left := by
    rw [← Category.assoc, e₁, Category.assoc]; exact hExt
  have e₄ : r.left ≫ (fst (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have e₅ : (x.left ≫ U.gen.inv.left) ≫ U.gen.hom.left = x.left := by
    rw [Category.assoc, ← Over.comp_left, Iso.inv_hom_id]; exact Category.comp_id _
  have e₆ : (x.left ≫ U.gen.inv.left) ≫ pullback.fst G.hom (jK R) = (toUnit (TF (R := R) (FractionRing R)) ≫ h).left := by
    rw [Category.assoc]; exact hExt
  have a₁ := isoRel_val hR r.left z hA hG
  rw [Category.comp_id, e₁, e₂, e₅, e₆] at a₁
  have a₂ := secLin_val hσ r.left z hG
  rw [e₃] at a₂
  have a₃ := hv z JA hA
  rw [GlobalTheory.UT.NonVan.val_powFrame, zpow_natCast] at a₃
  have a₄ := hF z JA JG hA hG

  rw [cst_eq] at a₃ a₄
  apply cstH_inj (R := R) z
  rw [map_mul, map_pow, map_sum]
  refine alg_value_at a₁ a₂ a₃ a₄ (fun i => ?_)
  have b : gs r.left z ⊤ (scal (fst (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left (c i)) =
      cstH (R := R) z (c i) :=
    ((gs_pull _ _ z ⊤ trivial _).trans (by rw [e₄]; rfl)).trans (cst_eq (R := R) z _)
  have cb : Geo.Tor.cst (toUnit (TF (R := R) (FractionRing R))).left z (xs i) =
      cstH (R := R) z (algebraMap (FractionRing R) (FractionRing R) (algebraMap R _ (xs i))) := by
    rw [e₀]; exact cst_base (R := R) (FractionRing R) z (xs i)
  rw [b, Over.comp_left, hxs i _ _ z JG hG, cb, map_mul, _root_.mul_assoc]
  simp

end GlobalTheory.Poinc.IntEval
end
