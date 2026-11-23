import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyAtIffExistsKeyAtVia
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreKeyTheta

variable {X : Scheme.{0}}

theorem toStk_valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (z : Sp ℂ) (h : x z ∈ U) (a : Γ(X, U)) :
    toStk z (valAt' x U a) = gs x z U a := by
  rw [valAt', dif_pos ((top_le_iff_mem x U z).2 h), valAt, gs_eq x z U h]
  show ((Sp ℂ).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp ℂ).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

theorem cst_id (z : Sp ℂ) (a : ℂ) : cst (𝟙 (Sp ℂ)) z a = toStk z a := by
  rw [cst, gs_eq (𝟙 (Sp ℂ)) z ⊤ trivial]
  rfl

def isoSymm {A B : LB X} (w : LB.Iso A B) : LB.Iso B A :=
  ⟨fun p => (res (fun _ hy => ⟨hy.2, hy.1⟩ : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹⟩

theorem isoSymm_isGen {A B : LB X} (w : LB.Iso A B) (hw : w.IsGen) : (isoSymm w).IsGen := by
  have le : ∀ p : A.ι × B.ι, A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1 := fun p y hy => ⟨hy.2, hy.1⟩
  intro p q
  refine unit_ext fun y hy => ?_
  have hm : (𝟙 X : X ⟶ X) y ∈ B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1))) (hw (p.2, p.1) (q.2, q.1))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) y (p.2, p.1) (q.2, q.1) hm) (gm_res _ y _ hm _))))
  have v : ∀ p : A.ι × B.ι, y ∈ A.U p.1 ⊓ B.U p.2 → gm (𝟙 X) y (A.U p.1 ⊓ B.U p.2) (res (le p) (w.s (p.2, p.1)))⁻¹ =
      (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹ := fun p hp =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))
  refine ((gm_res _ y _ hy _).trans ((v p hy.1).trans (congrArg (·⁻¹) e'))).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div B A (𝟙 X) y p q hy)
    ((gm_res _ y _ hy _).trans (v q hy.2)))).trans ?_
  rw [mul_inv, mul_inv, inv_inv, mul_comm (gm (𝟙 X) y _ (A.g p.1 q.1))]
  rfl

end GlobalTheory.FibreKeyTheta

open GlobalTheory.FibreKeyTheta in

theorem GlobalTheory.FibreKeyTheta.th_isFn_const_mul : ∀ (x : KeyIn ℂ) (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (y : Sp ℂ ⟶ S) (Φ : x.P.A.left ⟶ G.left) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (w : LB.Iso (L.pull Φ) x.P.L) (θ : (Fin g → ℂ) → ℂ) (fr : L.ι → (Fin g → ℂ) → ℂ) (s : (L.pull (pullback.fst G.hom y)).Sec), L.IsLB → IsPullback Φ x.P.A.hom G.hom y → w.IsGen → (∃ z, θ z ≠ 0) → (∀ j z, ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → fr j z ≠ 0) → (∀ k j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (x.P.L.U k ⊓ (L.pull Φ).U j) → u.fr k z = valAt' (u.ex z).left (x.P.L.U k ⊓ (L.pull Φ).U j) (w.s (k, j)).val * fr (j PUnit.unit) z) → (∀ j z (p : Sp ℂ ⟶ pullback G.hom y), p ≫ pullback.fst _ _ = (u.ex z).left ≫ Φ → p ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → valAt' p ((L.pull (pullback.fst G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z) → ∃ c₀ : ℂ, u.IsFn x.th (fun z => c₀ * θ z) := by
  intro x S G _ L y Φ g u w θ fr s hL hΦ hw hθ hfr hu hs
  classical
  let km : x.P.A.left ⟶ pullback G.hom y := pullback.lift Φ x.P.A.hom hΦ.w
  have km1 : km ≫ pullback.fst G.hom y = Φ := pullback.lift_fst _ _ _
  have km2 : km ≫ pullback.snd G.hom y = x.P.A.hom := pullback.lift_snd _ _ _
  have le : ∀ j : L.ι, Φ ⁻¹ᵁ L.U j ≤ km ⁻¹ᵁ (L.pull (pullback.fst G.hom y)).U (fun _ => j) := fun j p hp =>
    mem_pull.2 ((congrArg (fun e => e p ∈ L.U j) km1).mpr hp)
  let σ : ∀ j : L.ι, Γ(x.P.A.left, Φ ⁻¹ᵁ L.U j) := fun j => (km.appLE _ _ (le j)).hom (s.f (fun _ => j))
  have hσv : ∀ {Z : Scheme.{0}} (r : Z ⟶ x.P.A.left) (z : Z) (j : L.ι), Φ (r z) ∈ L.U j →
      gs r z _ (σ j) = gs (r ≫ km) z _ (s.f (fun _ => j)) := fun r z j h =>
    gs_appLE km _ _ (le j) r z h _
  have hσ : ∀ (p : x.P.A.left) j j', Φ p ∈ L.U j → Φ p ∈ L.U j' →
      gs (𝟙 _) p _ (σ j) = (gm Φ p (L.U j ⊓ L.U j') (L.g j j')).val * gs (𝟙 _) p _ (σ j') := by
    intro p j j' h h'
    rw [hσv _ p j h, hσv _ p j' h', Category.id_comp]
    refine (sec_trans s km p (le j h) (le j' h')).trans ?_
    congr 2
    simp [trF, km1]
  have hwD : PGen (isoSymm w) := (isGen_iff _).1 (isoSymm_isGen w hw)
  obtain ⟨s', hs'⟩ := sec_down hwD hL x.P.isLB σ hσ
  have refl : LBIso x.P.L (x.P.L.pull (𝟙 _)) :=
    LBIso.chartPull (chartPullUnpull x.P.L _ rfl) (chartPullId _)
      (exists_iso_linComb (F := 𝟙 x.P.A.left) x.P.isLB (fun _ : PUnit => 𝟙 _) (fun _ => 1) fun _ _ _ => rfl)
  obtain ⟨a, ha, -⟩ := GlobalTheory.SectionBaseChange.generates GlobalTheory.allSixLaws.1.secBaseChange x.P (t := 𝟙 _) (φ := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) x.P.isLB refl x.th x.th_ne s'
  obtain ⟨pt⟩ : Nonempty (Sp ℂ) := ⟨(⊥ : PrimeSpectrum ℂ)⟩
  have key : ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i →
      a * valAt' (u.ex z).left (x.P.L.U i) (x.th.f i) = θ z * u.fr i z := by
    intro i z hi
    have hri : (u.ex z).left pt ∈ x.P.L.U i := (top_le_iff_mem _ _ pt).1 hi
    obtain ⟨j, hj⟩ := exists_chart hL (Φ ((u.ex z).left pt))
    have hj' : ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j := (top_le_iff_mem _ _ pt).2 hj
    have hr0 : (u.ex z).left ≫ x.P.A.hom = 𝟙 _ := by simpa using Over.w (u.ex z)
    have hr1 : ((u.ex z).left ≫ km) ≫ pullback.snd G.hom y = 𝟙 _ := by rw [Category.assoc, km2, hr0]
    have e1 := hs j z ((u.ex z).left ≫ km) (by rw [Category.assoc, km1]) hr1 hj'
    have hm : (u.ex z).left pt ∈ x.P.L.U i ⊓ (L.pull Φ).U (fun _ => j) := ⟨hri, mem_pull.2 hj⟩
    have e2 := hu i (fun _ => j) z ((top_le_iff_mem _ _ pt).2 hm)
    have e3 := hs' (Sp ℂ) (u.ex z).left pt j i hj hri
    rw [hσv _ pt j hj, ← toStk_valAt' ((u.ex z).left ≫ km) _ pt (le j hj), e1, ha i, gs_mul _ pt _ hri, gs_constFn _ _ _ pt hri,
      hr0] at e3
    erw [cst_id] at e3
    rw [← toStk_valAt' _ _ pt hri] at e3
    have hm' : (u.ex z).left pt ∈ (L.pull Φ).U (fun _ => j) ⊓ x.P.L.U i := ⟨mem_pull.2 hj, hri⟩
    have gwv : gw (isoSymm w) (u.ex z).left pt j i =
        (gm (u.ex z).left pt (x.P.L.U i ⊓ (L.pull Φ).U (fun _ => j)) (w.s (i, fun _ => j)))⁻¹ :=
      (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ pt _ hm' _))
    rw [gwv, Units.eq_inv_mul_iff_mul_eq] at e3
    have e3' : toStk pt (valAt' (u.ex z).left (x.P.L.U i ⊓ (L.pull Φ).U (fun _ => j)) (w.s (i, fun _ => j)).val *
        (θ z * fr j z)) = toStk pt (a * valAt' (u.ex z).left (x.P.L.U i) (x.th.f i)) := by
      rw [map_mul, map_mul (toStk pt) a]
      erw [toStk_valAt' _ _ pt hm, gs_unit _ pt _ hm]
      exact e3
    have e4 := (toStk pt).injective e3'
    rw [e2, ← e4]
    ring
  obtain ⟨z0, hz0⟩ := hθ
  obtain ⟨i0, hi0⟩ := exists_chart x.P.isLB ((u.ex z0).left pt)
  have hi0' : ⊤ ≤ (u.ex z0).left ⁻¹ᵁ x.P.L.U i0 := (top_le_iff_mem _ _ pt).2 hi0
  have ha0 : a ≠ 0 := by
    intro h0
    have e := key i0 z0 hi0'
    rw [h0, zero_mul] at e
    exact mul_ne_zero hz0 (u.fr_ne i0 z0 hi0') e.symm
  refine ⟨a⁻¹, fun i z hi => ?_⟩
  have e := key i z hi
  show _ = a⁻¹ * θ z * u.fr i z
  rw [mul_assoc, ← e, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
