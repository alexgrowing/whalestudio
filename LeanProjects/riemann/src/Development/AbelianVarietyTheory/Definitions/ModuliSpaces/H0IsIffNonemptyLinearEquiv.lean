import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}

theorem symB_iff_exists_gen {A : Over (Sp K)} [GrpObj A] (M : LB A.left) :
    SymB M ↔ ∃ u : LB.Gen (LB.LinComb M (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]), u.IsGen := by
  have g : ∀ (y : A.left) (j j' : (PUnit → M.ι) × M.ι) (J J' : Fin 2 → M.ι), J 0 = j.1 PUnit.unit → J 1 = j.2 →
      J' 0 = j'.1 PUnit.unit → J' 1 = j'.2 →
      y ∈ (LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M).U j → y ∈ (LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M).U j' →
      y ∈ LB.wchart M (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) J →
      y ∈ LB.wchart M (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) J' →
      gm (𝟙 _) y _ ((LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M).g j j') =
        gm (𝟙 _) y _ ((LB.LinComb M (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]).g J J') := by
    intro y j j' J J' a b c d hj hj' hJ hJ'
    obtain rfl : J = ![j.1 PUnit.unit, j.2] := by
      funext k; fin_cases k; exacts [a, b]
    obtain rfl : J' = ![j'.1 PUnit.unit, j'.2] := by
      funext k; fin_cases k; exacts [c, d]
    refine (gm_div M (M.pull (GrpObj.inv : A ⟶ A).left) (𝟙 _) y j j' ⟨hj, hj'⟩).trans
      (Eq.trans ?_ (gm_linComb M _ _ (𝟙 _) y _ _ hJ hJ').symm)
    refine Eq.trans (congrArg₂ (· * ·) ?_ ?_) (Fin.prod_univ_two _).symm
    · exact (gm_pull_g M _ _ y j.1 j'.1 hj.1 hj'.1).trans (zpow_one _).symm
    · exact (zpow_neg_one _).symm
  constructor
  · rintro ⟨u, hu⟩
    have le : ∀ J : Fin 2 → M.ι, LB.wchart M (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) J ≤
        (LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M).U (fun _ => J 0, J 1) :=
      fun J y hy => ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0, Set.mem_iInter.1 hy 1⟩
    exact gen_chartPull (h := 𝟙 _) (A := LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M)
      (A' := LB.LinComb M (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1])
      ⟨fun J => (fun _ => J 0, J 1), le, fun y J J' hJ hJ' =>
        (g y _ _ J J' rfl rfl rfl rfl (le J hJ) (le J' hJ') hJ hJ').symm⟩ u hu
  · rintro ⟨u, hu⟩
    have le : ∀ j : (PUnit → M.ι) × M.ι, (LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M).U j ≤
        LB.wchart M (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) ![j.1 PUnit.unit, j.2] :=
      fun j y hy => Set.mem_iInter.2 fun k => by
        fin_cases k
        exacts [Set.mem_iInter.1 hy.1 PUnit.unit, hy.2]
    exact gen_chartPull (h := 𝟙 _) (A' := LB.div (M.pull (GrpObj.inv : A ⟶ A).left) M)
      (A := LB.LinComb M (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1])
      ⟨fun j => ![j.1 PUnit.unit, j.2], le, fun y j j' hj hj' =>
        g y j j' _ _ rfl rfl rfl rfl hj hj' (le j hj) (le j' hj')⟩ u hu

theorem symB_iff_sym {A : Over (Sp K)} [GrpObj A] {M : LB A.left} (hM : M.IsLB) : SymB M ↔ Out.Sym A M := by
  rw [symB_iff_exists_gen]
  have e : ∀ U : (Sp K).Opens, (fun k => (A.hom ⁻¹ᵁ U).ι ≫ (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) k) =
      ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] := fun U => by
    funext k
    fin_cases k
    exacts [rfl, Category.comp_id _]
  constructor
  · rintro ⟨u, hu⟩ s
    refine ⟨⊤, trivial, ?_⟩
    rw [← e]
    exact ⟨_, DVR.pullGen_isGen M _ _ u hu _⟩
  · intro h
    refine DVR.gen_of_local_base hM _ _ fun s => ?_
    obtain ⟨U, hU, ht⟩ := h s
    exact ⟨U, hU, (e U).symm ▸ ht⟩

namespace Example

section Proj
open GlobalTheory.ProjSpace MvPolynomial

theorem sectionsFinDim_lbPow_O1_projSpace (N e : ℕ) : SectionsHaveFiniteDimension (PSpace.str K (N + 1)) (lbPow (O1 K (N + 1)) e)
    (Module.finrank K (homogeneousSubmodule (Fin (N + 2)) K e)) := by
  haveI : Module.Finite K (homogeneousSubmodule (Fin (N + 2)) K e) :=
    Module.Finite.iff_fg.2 (homogeneousSubmodule_fg _ _ _)
  let b := Module.finBasis K (homogeneousSubmodule (Fin (N + 2)) K e)
  refine ⟨fun i => formSec e (b i).1 (b i).2, fun t => ?_⟩
  obtain ⟨f, hf, rfl⟩ := ProjSpace.Model.exists_formSec e t
  have key : ∀ (a : _ → K) j, ∑ i, constFn (PSpace.str K (N + 1)) _ (a i) * (formSec e (b i).1 (b i).2).f j =
      (formSec e (∑ i, a i • b i).1 (∑ i, a i • b i).2).f j := fun a j => by
    erw [formSec_f, formOn_eq_aeval]
    rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    erw [formSec_f, formOn_eq_aeval]
    rw [Submodule.coe_smul, map_smul, Algebra.smul_def]
    rfl
  refine ⟨b.repr ⟨f, hf⟩, fun j => ?_, fun a ha => ?_⟩
  · rw [key]
    simp only [b.sum_repr]
  · have h := (ha fun _ => (0 : Fin (N + 2))).trans (key a _)
    have h' := congrArg (resG _ (On_U K (N + 1) e fun _ => 0).ge) h
    have : (⟨f, hf⟩ : homogeneousSubmodule (Fin (N + 2)) K e) = ∑ i, a i • b i :=
      Subtype.ext ((formOn_chart_inj K (N + 1) 0 hf (∑ i, a i • b i).2).1 h')
    rw [this]
    ext i
    simp [Finsupp.single_apply]

theorem sectionsFinDim_lbPow_O1_projLine (e : ℕ) : SectionsHaveFiniteDimension (PSpace.str K 1) (lbPow (O1 K 1) e) (e + 1) := by
  have h := sectionsFinDim_lbPow_O1_projSpace (K := K) 0 e
  rwa [ProjCut.finrank_homogeneousSubmodule, Fintype.card_fin, show e + (0 + 2) - 1 = e + 1 by omega,
    Nat.choose_succ_self_right] at h

theorem vol_line : Vol (PSpace.str K 1) (O1 K 1) 1 1 := by
  refine ⟨fun e => e + 1, sectionsFinDim_lbPow_O1_projLine, ?_⟩
  have h : Filter.Tendsto (fun e : ℕ => 1 + 1 / (e : ℝ)) Filter.atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with e he
  have : (e : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem not_vol_line_two : ¬ Vol (PSpace.str K 1) (O1 K 1) 1 2 := fun h => by
  have := h.unique vol_line
  norm_num at this

theorem vAmp_coord (N : ℕ) : VAmp (PSpace.str K N) (O1 K N) (coord K N) := by
  refine ⟨iSup_nonzeroLocus_coord K N, fun i => ?_⟩
  have hU : Out.nonzeroLocus (coord K N i) = chart K N i := nonzeroLocus_coord K N i
  refine ⟨hU ▸ isAffineOpen_chart K N i, ratioOn _ i hU.le, fun j k => ?_, fun f => ?_⟩
  · exact (ratioOn_mul_ratioOn (hi := inf_le_right) (hj := inf_le_left.trans hU.le)).symm.trans (mul_comm _ _)
  · obtain ⟨n, F, hF, h⟩ := ProjSpace.Model.exists_formOn i (resG _ hU.ge f)
    refine ⟨F, ?_⟩
    have e : f = resG _ hU.le (resG _ hU.ge f) := ((AbLaw.rs_rs _ _ f).trans (AbLaw.rs_self _ f)).symm
    rw [e, h, resG_formOn, formOn_eq_aeval]
    rfl

end Proj

theorem not_vAmp_one : ¬ VAmp (PSpace.str K 1) (ProjSpace.O1 K 1) (fun _ : Unit => ProjSpace.coord K 1 0) := by
  intro h
  have h1 : Out.nonzeroLocus (ProjSpace.coord K 1 0) = ⊤ := by simpa using h.1
  have hu : ∀ i, IsUnit ((ProjSpace.coord K 1 0).f i) := fun i => by
    refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun x hx => ?_
    have hx0 : x ∈ ProjSpace.chart K 1 0 := by
      have := ProjSpace.nonzeroLocus_coord K 1 0
      rw [h1] at this
      exact (this.le : ⊤ ≤ ProjSpace.chart K 1 0) trivial
    have hb : x ∈ (PSpace K 1).basicOpen (ProjSpace.ratio K 1 i 0) := by
      erw [ProjSpace.basicOpen_ratioOn]
      exact ⟨hx, hx0⟩
    exact ((PSpace K 1).mem_basicOpen _ x hx).1 hb
  exact ProjSpace.Model.not_isGen_O1 (R := K) (N := 0) ⟨fun i => (hu i).unit⟩ fun i j =>
    Units.ext ((ProjSpace.coord K 1 0).compat i j)

def gmPts (K : Type) [Field K] : (Out.baseOver (Sp K) ⟶ Gm (Sp K)) ≃* Kˣ :=
  (splitTorusPointsEquiv (Sp K) (ULift ℤ) _).trans <|
    (MulEquiv.monoidHomCongrLeft (AddEquiv.ulift.toMultiplicative)).trans <|
      (zpowersMulHom _).symm.trans
        (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv)

theorem torsBasis_gm {k : ℕ} [NeZero k] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ k) :
    TorsBasis (Gm (Sp K)) k ![(gmPts K).symm ζ] := by
  refine ⟨Nat.pos_of_neZero k, fun i => ?_, fun y hy => ?_⟩
  · fin_cases i
    change (gmPts K).symm ζ ^ k = 1
    rw [← map_pow, hζ.pow_eq_one, map_one]
  · have hl : ∀ c : Fin 1 → ZMod k, Out.linComb ![(gmPts K).symm ζ] (fun i => (c i).val) =
        (gmPts K).symm (ζ ^ (c 0).val) := fun c => by simp [Out.linComb]
    have hy' : gmPts K y ∈ rootsOfUnity k K := by
      rw [mem_rootsOfUnity, ← map_pow, hy, map_one]
    obtain ⟨i, hi, e⟩ := hζ.eq_pow_of_mem_rootsOfUnity hy'
    refine ⟨fun _ => (i : ZMod k), ?_, fun c hc => ?_⟩
    · beta_reduce
      rw [hl, ZMod.val_cast_of_lt hi, e, MulEquiv.symm_apply_apply]
    · beta_reduce at hc
      rw [hl, MulEquiv.symm_apply_eq, ← e] at hc
      funext j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      rw [← hζ.pow_inj (ZMod.val_lt _) hi hc, ZMod.natCast_zmod_val]

theorem actsBy_gm_pow {k : ℕ} [NeZero k] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ k) (n : ℕ) :
    ActsBy ![(gmPts K).symm ζ] (𝟙 (Gm (Sp K)) ^ n) !![(n : ZMod k)] := by
  refine ⟨Nat.pos_of_neZero k, fun i => ?_⟩
  have h := (torsBasis_gm hζ).pow_eq_one i
  fin_cases i
  rw [MonObj.comp_pow, Category.comp_id, pow_eq_pow_mod n h]
  simp [Out.linComb]

example : TorsBasis (Gm (Sp ℚ)) 2 ![(gmPts ℚ).symm (-1)] :=
  torsBasis_gm (IsPrimitiveRoot.coe_units_iff.1 (IsPrimitiveRoot.neg_one 0 (by decide)))

end Example
end GlobalTheory.ZV
end
