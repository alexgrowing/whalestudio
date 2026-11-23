import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilLagrangianOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLiftAlongNilpotent
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystalOfDualAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTGlueIsoPol

open GlobalTheory.AbDual

section
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'}
  {S S' : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A]
  {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'} {A' : Over S'} [GrpObj A']
  {b : S' ⟶ S} {φ : A'.left ⟶ A.left} {m : GrpMor κ t A κ' t' A' (algebraMap R R') b φ}

theorem ext_of_isBC (hm : m.IsBC) {h₁ h₂ : Crys κ' t' A'} (e : ∀ c, h₁ (m.pull c) = h₂ (m.pull c)) :
    h₁ = h₂ := by
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨z, rfl⟩ := hm.2 c
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, e c]

omit [Algebra R R'] in

theorem crys_sum_apply {J : Type} (s : Finset J) (g : J → Crys κ' t' A') (q : prim κ' t' A') :
    (∑ i ∈ s, g i) q = ∑ i ∈ s, g i q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.add_apply, ih]

theorem bcMap_pull (hm : m.IsBC) (h : Crys κ t A) (c : prim κ t A) :
    hm.bcMap h (m.pull c) = algebraMap R R' (h c) :=
  (hm.corr_iff (h := h)).2 rfl c

omit [Algebra R R'] in

theorem crys_add_apply (g g' : Crys κ' t' A') (q : prim κ' t' A') : (g + g') q = g q + g' q :=
  LinearMap.add_apply g g' q

omit [Algebra R R'] in

theorem crys_smul_apply (r : R') (g : Crys κ' t' A') (q : prim κ' t' A') : (r • g) q = r * g q :=
  LinearMap.smul_apply r g q
end

theorem tsze_coords {k : Type} [Field k] {d : ℕ} (a : k) (v : Fin d → k) :
    (TrivSqZeroExt.inl a + TrivSqZeroExt.inr v : TrivSqZeroExt k (Fin d → k)) =
      algebraMap k _ a + ∑ j, TrivSqZeroExt.inr (Pi.single j 1) * algebraMap k _ (v j) := by
  ext
  · simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_sum]
  · simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_sum, Finset.sum_apply, Pi.single_apply]

theorem glue_pairing_eq_zero {k : Type} [Field k] {d : ℕ} {H M : Type*} [AddCommGroup H] [Module k H]
    [AddCommGroup M] [Module (TrivSqZeroExt k (Fin d → k)) M]
    (bc : H →ₛₗ[algebraMap k (TrivSqZeroExt k (Fin d → k))] M)
    (Φ : M →ₗ[TrivSqZeroExt k (Fin d → k)] M →ₗ[TrivSqZeroExt k (Fin d → k)] TrivSqZeroExt k (Fin d → k))
    (φ : LinearMap.BilinForm k H) (key : ∀ u v, Φ (bc u) (bc v) = algebraMap k _ (φ u v))
    {x y : H} {u v : Fin d → H} (hxy : φ x y = 0) (huv : ∀ j, φ (u j) y + φ x (v j) = 0) :
    Φ (bc x + ∑ j, (TrivSqZeroExt.inr (Pi.single j 1) : TrivSqZeroExt k (Fin d → k)) • bc (u j))
      (bc y + ∑ j, (TrivSqZeroExt.inr (Pi.single j 1) : TrivSqZeroExt k (Fin d → k)) • bc (v j)) = 0 := by
  have hee : ∀ (j l : Fin d) (r : TrivSqZeroExt k (Fin d → k)),
      (TrivSqZeroExt.inr (Pi.single j 1) : TrivSqZeroExt k (Fin d → k)) * (TrivSqZeroExt.inr (Pi.single l 1) * r) = 0 :=
    fun j l r ↦ by rw [← _root_.mul_assoc, TrivSqZeroExt.inr_mul_inr, MulZeroClass.zero_mul]
  simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, key,
    smul_eq_mul, Finset.mul_sum, mul_add, hee, Finset.sum_const_zero, add_zero, hxy, map_zero, zero_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [← mul_add, ← map_add, huv j, map_zero, mul_zero]

set_option maxHeartbeats 4000000 in

theorem glueFil_isotropic : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ Φ : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[(TrivSqZeroExt k (Fin d → k))] Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A →ₗ[(TrivSqZeroExt k (Fin d → k))] (TrivSqZeroExt k (Fin d → k)), GlobalTheory.AbDual.IsCorrForm (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A o₀.A o₀.P Φ → ∀ x ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), ∀ y ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), Φ x y = 0) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ β hβ φ hφ d f hf Φ hΦ X hX Y hY
  have h2 := GlobalTheory.FODef.sqZero k (Fin d → k)
  have hA := o₀.ab
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k o₀.A hA
  obtain ⟨A, _, i, hi, hAC, hgC⟩ := GlobalTheory.abelianScheme_constLift (TrivSqZeroExt k (Fin d → k)) k
    (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom (algebraMap k (TrivSqZeroExt k (Fin d → k)))
    (by ext; simp [TrivSqZeroExt.algebraMap_eq_inl]) o₀.A g hA hg
  have ADR := GlobalTheory.abelianDeRham
  have ADC := GlobalTheory.abelianDualCrystal_of_dualAbelianScheme GlobalTheory.dualAbelianScheme
  have CS := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 (isDPNilpotent_squareZero h2)
    (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl hAC hgC hAC hgC hi hi
  have m := GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A
  have hBC : m.IsBC := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) o₀.A hA _ m
  have hP := o₀.isLB
  have e0 : LBIso (o₀.P.pull (𝟙 _)) o₀.P := by
    first
      | exact LBIso.chartPull (chartPullPull o₀.P (𝟙 _)) (chartPullId o₀.P) (PolBaseChange.lbIso_refl hP)
      | exact LBIso.chartPull (chartPullPull o₀.P (𝟙 _)) (chartPullId o₀.P) (ChernExists.lbIso_refl hP)
  obtain ⟨Ψ, hΨ, hΨc⟩ := hφ.pull hP m m (h := 𝟙 _) (by simp) (by simp) hP e0
  obtain rfl := hΦ.unique CS hP hΨ

  have key : ∀ u v : HdR o₀.A, Φ (hBC.bcMap u) (hBC.bcMap v) = algebraMap k _ (φ u v) := fun u v ↦
    hΨc u _ v _ ((hBC.corr_iff (h := u)).2 rfl) ((hBC.corr_iff (h := v)).2 rfl)

  have dec : ∀ Z ∈ GlobalTheory.HTGlue.glueFil o₀.A f, ∃ x ∈ Fil o₀.A, ∃ z : Fin d → HdR o₀.A, (∀ j, z j ∈ Fil o₀.A) ∧
      Z = hBC.bcMap x + ∑ j, (TrivSqZeroExt.inr (Pi.single j 1) : TrivSqZeroExt k (Fin d → k)) •
        hBC.bcMap (f j x + z j) := by
    rintro Z ⟨x, hx, z, hz, hZ⟩
    refine ⟨x, hx, z, hz, ext_of_isBC hBC fun c ↦ ?_⟩
    rw [hZ c, tsze_coords, crys_add_apply]
    refine (congrArg₂ (· + ·) (bcMap_pull hBC x c) ?_).symm
    exact (crys_sum_apply _ _ _).trans (Finset.sum_congr rfl fun j _ ↦
      (crys_smul_apply _ _ _).trans (congrArg _ (bcMap_pull hBC _ c)))
  have iso := (GlobalTheory.HTLagr.fil_lagrangian p D R b N k t o₀ φ ⟨g, hg⟩ hφ).1
  refine (dec X hX).elim fun x hx' ↦ (dec Y hY).elim fun y hy' ↦ ?_
  refine hx'.2.elim fun z hz' ↦ hy'.2.elim fun w hw' ↦ ?_
  refine (congrArg₂ (fun a b ↦ Φ a b) hz'.2 hw'.2).trans ?_
  refine glue_pairing_eq_zero hBC.bcMap Φ φ key (iso x hx'.1 y hy'.1) fun j ↦ ?_
  simp only [map_add, LinearMap.add_apply, iso _ (hz'.1 j) _ hy'.1, iso _ hx'.1 _ (hw'.1 j), add_zero]
  exact (hf j).2.2 x hx'.1 y hy'.1

end GlobalTheory.HTGlueIsoPol
