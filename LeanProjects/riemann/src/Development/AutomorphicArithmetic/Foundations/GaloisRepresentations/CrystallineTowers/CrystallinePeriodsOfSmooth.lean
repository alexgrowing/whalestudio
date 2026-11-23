import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.SemistableModelSemistable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmDOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.Bridge
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Formalism Formalism.BasicNotions DeRhamPotentiallySemistable.DRPst CrystallineSemistableComparison
open scoped Formalism.Per

namespace UpperTheory.Gal.Seam

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

def IsAdmP (P : LocPrime l) {d : ℕ} (G : Subgroup (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)) (r : G → Matrix (Fin d) (Fin d) ℚ_[l]) : Prop :=
  ∃ A B : Matrix (Fin d) (Fin d) P.R.BdR, (∀ i j, A i j ∈ Set.range P.ιB ∧ B i j ∈ Set.range P.ιB) ∧ A * B = 1 ∧
    ∀ σ : G, (r σ).map (algebraMap ℚ_[l] P.R.BdR) * A.map (P.actQdR σ.1) = A

theorem mem_range (T : LocTied6 l P AI) {x : Per6.BdR l} (hx : x ∈ Bcr l) : T.eD.symm x ∈ Set.range P.ιB := by
  have hι : ∀ y, T.eD (P.ιB (T.eB.symm y)) = PositivityTheory.LocInh.ιCD l y :=
    RingHom.congr_fun ((PositivityTheory.LocInh.isCrisDR_iff _).1 T.incl)
  have hinv : ∀ y : Per6.Bcris l, IsUnit y → (PositivityTheory.LocInh.ιCD l y)⁻¹ ∈ (PositivityTheory.LocInh.ιCD l).range := fun y hy =>
    ⟨↑(hy.unit⁻¹), by rw [map_units_inv]; rfl⟩
  have hle : Bcr l ≤ (PositivityTheory.LocInh.ιCD l).range := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨a, rfl⟩ | rfl | rfl)
    · exact ⟨Per6.cB l a, PositivityTheory.LocInh.ιCD_cB a⟩
    · have := hinv _ (PositivityTheory.LocInh.isUnit_cB_l l)
      rwa [PositivityTheory.LocInh.ιCD_cB, map_natCast] at this
    · have := hinv _ (PositivityTheory.LocInh.cB_isFrac l).2.1
      rwa [PositivityTheory.LocInh.ιCD_cB] at this
  obtain ⟨y, rfl⟩ := hle hx
  exact ⟨T.eB.symm y, by rw [← hι, RingEquiv.symm_apply_apply]⟩

theorem isAdmP_of_isAdm (T : LocTied6 l P AI) {d : ℕ} {G : Subgroup (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)}
    {r : G → Matrix (Fin d) (Fin d) ℚ_[l]} (h : IsAdm (Bcr l) G r) : IsAdmP P G r := by
  obtain ⟨A, B, hm, hAB, hσ⟩ := h
  refine ⟨A.map T.eD.symm, B.map T.eD.symm, fun i j => ⟨mem_range T (hm i j).1, mem_range T (hm i j).2⟩, ?_, fun σ => ?_⟩
  · rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]
  · ext i j
    apply T.eD.injective
    have := congrFun (congrFun (hσ σ) i) j
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, UpperTheory.Lit.Drps.eD_alg T, T.actD,
      RingEquiv.apply_symm_apply] at this ⊢
    exact this

theorem isAdmD_of_isAdmP (T : LocTied l P AI) {d : ℕ} {G : Subgroup (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)}
    {r : G → Matrix (Fin d) (Fin d) ℚ_[l]} (h : IsAdmP P G r) :
    GlobalTheory.AdmBr.IsAdmD ((T.eD : P.R.BdR →+* Per.BdR l).comp (algebraMap ℚ_[l] P.R.BdR))
      (Set.range (T.eD ∘ P.ιB ∘ T.eB.symm)) G r := by
  obtain ⟨A, B, hm, hAB, hσ⟩ := h
  have hS : ∀ x ∈ Set.range P.ιB, T.eD x ∈ Set.range (T.eD ∘ P.ιB ∘ T.eB.symm) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨T.eB y, by simp⟩
  refine ⟨A.map T.eD, B.map T.eD, fun i j => ⟨hS _ (hm i j).1, hS _ (hm i j).2⟩, ?_, fun σ => ?_⟩
  · rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]
  · ext i j
    have := congrArg T.eD (congrFun (congrFun (hσ σ) i) j)
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, T.actD] at this ⊢
    exact this

def CrystallinePeriodMatrices : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [hK : FiniteDimensional ℚ_[l] K] (M : Model l K),
    M.Good → Smooth M.p → ∀ (n a : ℕ) (b : Module.Basis (Fin a) ℚ_[l] (M.V n)),
      GlobalTheory.AdmBr.IsAdmD ((T.eD : P.R.BdR →+* Per.BdR l).comp (algebraMap ℚ_[l] P.R.BdR))
        (Set.range (T.eD ∘ P.ιB ∘ T.eB.symm)) (Formalism.BasicNotions.Loc.GK ⟨K, hK⟩) (M.mat n b)

theorem crystalline_periods_of_smooth (h : SmoothModelCrystalline) : CrystallinePeriodMatrices := fun l _ P AI T K _ M hM hs n a b =>
  (UpperTheory.Lit.Cmp.locTied6 l P AI ⟨T⟩).elim fun FreeQuotientRank => isAdmD_of_isAdmP T (isAdmP_of_isAdm FreeQuotientRank (h l K M hM hs n a b))

end UpperTheory.Gal.Seam
