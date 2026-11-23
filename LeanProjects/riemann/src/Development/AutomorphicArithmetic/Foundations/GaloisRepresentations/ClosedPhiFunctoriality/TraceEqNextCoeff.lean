import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IsOp2One
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotSemistableOfPotCrystallineDecompositionGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PstExact
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem exists_ext {l : ℕ} [Fact l.Prime] (L₁ : FinExt l) {d a : ℕ}
    (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) :
    ∃ L : FinExt l, L₁.1 ≤ L.1 ∧ ∀ i j k, b i j k ∈ L.1 := by
  haveI := L₁.2
  haveI : ∀ x : Fin d × Fin a × Fin a, FiniteDimensional ℚ_[l] ↥(adjExt (b x.1 x.2.1 x.2.2)).1 :=
    fun x => (adjExt _).2
  refine ⟨⟨L₁.1 ⊔ ⨆ x : Fin d × Fin a × Fin a, (adjExt (b x.1 x.2.1 x.2.2)).1,
    IntermediateField.finiteDimensional_sup _ _⟩, le_sup_left, fun i j k => ?_⟩
  exact (le_sup_right : _ ≤ L₁.1 ⊔ _)
    (le_iSup (fun x : Fin d × Fin a × Fin a => (adjExt (b x.1 x.2.1 x.2.2)).1) (i, j, k) (mem_adjExt _))

private theorem trace_eq_nextCoeff {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (f : W →ₗ[ℂ] W) : LinearMap.trace ℂ W f = -f.charpoly.nextCoeff := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ W), Matrix.trace_eq_neg_charpoly_nextCoeff,
    LinearMap.charpoly_toMatrix]

section
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {L : FinExt l} {a : ℕ} {r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)} {r' : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1}

private theorem charPol_eq [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L r'))]
    (hm : IsModel Bw r L r') (hP : IsPst P (Bw.repE L r')) (g : ↥(Weil h)) :
    (wdAt P ι Bw h hj r).charPol g = (wdRho P ι Bw h hj (Bw.repE L r') g).charpoly :=
  (UpperTheory.V.Loc.PstExact.charPol_model ι Bw h hj hm hP g).trans
    (GlobalTheory.Pst.DpstMap.charPol_wdPst P ι Bw h hj _ hP g)
private theorem wdTr_eq [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L r'))]
    (hm : IsModel Bw r L r') (hP : IsPst P (Bw.repE L r')) (g : ↥(Weil h)) :
    wdTr P ι Bw h hj r g = ι.symm (LinearMap.trace ℂ (WDSpace P ι (Bw.repE L r'))
      (wdRho P ι Bw h hj (Bw.repE L r') g)) :=
  congrArg ι.symm ((congrArg (fun p => -p.nextCoeff) (charPol_eq ι Bw h hj hm hP g)).trans
    (trace_eq_nextCoeff _).symm)

include hj in
private theorem finrank_eq [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (Bw.repE L r'))]
    (hm : IsModel Bw r L r') (hP : IsPst P (Bw.repE L r')) (g : ↥(Weil h)) :
    Module.finrank ℂ (WDSpace P ι (Bw.repE L r')) = a := by
  rw [← LinearMap.charpoly_natDegree (wdRho P ι Bw h hj (Bw.repE L r') g),
    ← charPol_eq ι Bw h hj hm hP g, WD.charPol_natDegree, GlobalTheory.PstLaws.lpDim_wdAt]
end
theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.tie_holds :
    TieRep2 → Tie2 := by
  intro hT l _ ι P AI T E Ω _ _ _ _ _ w A h O _ _ _ Bw hj g n₁ n₂ hα a d r hcr ρ b e hR s V hV
  obtain ⟨L₁, r₁, hm₁, hc₁⟩ := id hcr
  obtain ⟨L, hL, hb⟩ := exists_ext L₁ b
  have hm := hm₁.enlarge hL
  generalize mapRep (IntermediateField.inclusion hL).toRingHom r₁ = r' at hm
  have hc := (hm.isCrysAt_iff P).1 hcr
  have hP : IsPst P (Bw.repE L r') := GlobalTheory.PstOfCrys.isPst_of_isCrys T _ hc
  haveI := hP.finite
  have hr : ∀ x i j, (((r' x).val i j : ↥L.1) : Om l) = (r x).val i j := fun x i j => by
    rw [← hm.2]; rfl
  let b' : Fin d → Matrix (Fin a) (Fin a) ↥L.1 := fun i => Matrix.of fun j k => ⟨b i j k, hb i j k⟩
  have H1 : ∀ g j (k : Fin a), Bw.repE L r' g (fun i => b' j i k) =
      ∑ i, ((ρ g).val i j : ℚ_[l]) • fun i' => b' i i' k := fun g j k => by
    funext i'
    apply Subtype.ext
    have := congrFun (congrFun (hR.equi g j) i') k
    rw [GlobalTheory.ConjLocal.repE_apply]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul] at this ⊢
    rw [AddSubmonoidClass.coe_finset_sum, AddSubmonoidClass.coe_finset_sum]
    refine (Finset.sum_congr rfl fun x _ => ?_).trans (this.trans (Finset.sum_congr rfl fun x _ => ?_))
    · rw [MulMemClass.coe_mul, hr]
      rfl
    · rw [Algebra.smul_def, MulMemClass.coe_mul]
      rfl
  have H2 : ∑ i, (e i : ℚ_[l]) • b' i = 1 := by
    ext j k
    have := congrFun (congrFun hR.one j) k
    have h1 : (((1 : Matrix (Fin a) (Fin a) ↥L.1) j k : ↥L.1) : Om l) = (1 : Matrix (Fin a) (Fin a) (Om l)) j k := by
      by_cases hjk : j = k
      · subst hjk
        rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
        rfl
      · rw [Matrix.one_apply_ne hjk, Matrix.one_apply_ne hjk]
        rfl
    rw [h1, ← this, Matrix.sum_apply, Matrix.sum_apply, AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.smul_apply, Matrix.smul_apply, Algebra.smul_def, smul_eq_mul, MulMemClass.coe_mul]
    rfl
  have key := hT l ι P AI T E Ω w A h O Bw hj g n₁ n₂ hα L a d (Bw.repE L r')
    (finrank_eq ι Bw h hj hm hP g) ρ b' e H1 H2 s V hV
  have e1 : (fun i => (((b' i).trace : ↥L.1) : Om l)) = fun i => (b i).trace := by
    funext i
    simp [Matrix.trace, b']
  have e2 := wdTr_eq ι Bw h hj hm hP g
  have fin : ∀ (x : Fin d → Om l) (y z : Om l), x = (fun i => (b i).trace) → y = z →
      IsTr (uB T) s (V *ᵥ fun i => Per.zB l (e i)) x y → IsTr (uB T) s (V *ᵥ fun i => Per.zB l (e i)) (fun i => (b i).trace) z := by
    rintro x y z rfl rfl hh
    exact hh
  exact fin _ _ _ e1 e2.symm key
