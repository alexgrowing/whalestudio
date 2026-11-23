import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapEqOfMemNabStd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StdWeylLatticesFgAndSpanCoeffSpace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMulAddEqOneOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TensorLatSpan
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.BvvInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem lca_span {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    nabStd K lam ≤ Submodule.span (𝓞 K) (MvPolynomial.map (Rat.castHom K) '' (nabStd ℚ lam : Set (Pol ℚ ι n))) := by
  have h1 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K ℚ ι (Rat.castHom K)
    (RingOfIntegers.mapRingHom (Rat.castHom K)) (fun r => rfl) n lam).1
  have h2 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1
  rw [h1, ← h2]
  intro x hx
  exact Submodule.subset_span ⟨x, hx, MvPolynomial.map_id x⟩

private theorem lca_coord {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ} (φ : K →+* ℂ)
    (lam : ι → DomWeight n) (x : Pol K ι n) (hx : x ∈ nabStd K lam) :
    ∃ v : VV ℂ lam, (v : Pol ℂ ι n) = MvPolynomial.map φ x ∧ ∀ i, ∃ o : 𝓞 K, (bVV ℂ lam).repr v i = φ (o : K) := by
  have hx' := lca_span lam hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    have hyV : y ∈ VV ℚ lam := by
      rw [← (GlobalTheory.StdLatSpan.std_fg_span ℚ ι n lam).2.2.1]
      exact Submodule.subset_span hy
    obtain ⟨Q, hQ⟩ := GlobalTheory.LocInt.exists_map_eq_of_mem_nabStd lam hy
    refine ⟨GlobalTheory.CoefModel.mapVV (φ.comp (Rat.castHom K)) lam ⟨y, hyV⟩, ?_, fun i => ?_⟩
    · rw [GlobalTheory.CoefModel.mapVV_coe, MvPolynomial.map_map]
    · obtain ⟨z, hz⟩ := UpperTheory.WildA.bvvInt lam (GlobalTheory.CoefModel.mapVV (φ.comp (Rat.castHom K)) lam ⟨y, hyV⟩) (fun m => by
        refine ⟨Rat.ringOfIntegersEquiv (MvPolynomial.coeff m Q), ?_⟩
        rw [GlobalTheory.CoefModel.mapVV_coe, MvPolynomial.coeff_map]
        have h2 : MvPolynomial.coeff m y = ((MvPolynomial.coeff m Q : 𝓞 ℚ) : ℚ) := by
          rw [← hQ]; exact MvPolynomial.coeff_map _ _ _
        change (φ.comp (Rat.castHom K)) (MvPolynomial.coeff m y) = _
        have h3 : ((MvPolynomial.coeff m Q : 𝓞 ℚ) : ℚ) = ((Rat.ringOfIntegersEquiv (MvPolynomial.coeff m Q) : ℤ) : ℚ) :=
          (Rat.ringOfIntegersEquiv_apply_coe _).symm
        rw [h2, h3, map_intCast]) i
      refine ⟨(z : 𝓞 K), ?_⟩
      rw [hz]
      simp
  | zero => exact ⟨0, by simp, fun i => ⟨0, by simp⟩⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, ha'⟩ := hy
    obtain ⟨b, hb, hb'⟩ := hz
    refine ⟨a + b, by simp [ha, hb], fun i => ?_⟩
    obtain ⟨o, ho⟩ := ha' i
    obtain ⟨p, hp⟩ := hb' i
    exact ⟨o + p, by simp [ho, hp]⟩
  | smul c y _ hy =>
    obtain ⟨a, ha, ha'⟩ := hy
    refine ⟨φ (c : K) • a, ?_, fun i => ?_⟩
    · ext m
      rw [Submodule.coe_smul, ha]
      simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map]
      change φ (c : K) * φ (y.coeff m) = φ ((c : K) * y.coeff m)
      rw [map_mul]
    · obtain ⟨o, ho⟩ := ha' i
      exact ⟨c * o, by simp [ho]⟩

private theorem lca_dual {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} {n : ℕ}
    (emb : ι → E →+* K) (τ : ι) :
    dualFr (tauLat emb τ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E))) =
      colLat (1 : GL (Fin n) K) := by
  classical
  apply le_antisymm
  · intro f hf
    have h1 : ∀ a, ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = f a := fun a => by
      have := hf (Pi.single a 1) (Submodule.subset_span ⟨Pi.single a 1, fun j _ => by
        by_cases h : j = a
        · subst h; simpa using Submodule.mem_one.2 ⟨1, map_one _⟩
        · simp [h], by
        funext j
        by_cases h : j = a
        · subst h; simp
        · simp [h]⟩)
      rw [dotProduct_single, mul_one] at this
      exact Submodule.mem_one.1 this
    choose o ho using h1
    have e : f = ∑ j, o j • fun a : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a j := by
      funext a
      rw [Finset.sum_apply, Finset.sum_eq_single a]
      · simp [Algebra.smul_def, ho]
      · intro b _ hb
        simp [Matrix.one_apply, Ne.symm hb]
      · simp
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩ x hx
    have e : (fun a : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a j) ⬝ᵥ x = x j := by
      simp [dotProduct, Matrix.one_apply]
    beta_reduce
    rw [e]
    clear e
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hy j (Set.mem_univ _))
      exact Submodule.mem_one.2 ⟨RingOfIntegers.mapRingHom (emb τ) o, by beta_reduce; rw [← ho]; rfl⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul c y _ hy => exact Submodule.smul_mem _ c hy

theorem UpperTheory.WildA.latCoordA :
    ∀ (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal →
      ∀ Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E), Formalism.MainNotions.TaylorLogMetric.EqAt D l Λ (Formalism.MainNotions.StandardLatticesGL3.stdL D n) → ∀ (a : ℝ) (v : VV ℂ lam),
      InLat lam w a Λ v → ∀ i, LossLe w ((bVV ℂ lam).repr v i) a := by
  intro D n lam w l _ hw Λ hΛ a v hv i
  obtain ⟨N, hN, h1, h2⟩ := hΛ
  obtain ⟨u, s, huv, hs0, hsa, hsu⟩ := hv
  have hNw := GlobalTheory.GO.natCast_notMem_of_coprime hN w hw
  have h1' : ∀ x ∈ Λ, N • x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D n := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact h1 x hx
  have h2' : ∀ x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D n, N • x ∈ Λ := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact h2 x hx
  have hB : ∀ τ, IsBasisAt w (dualFr (tauLat (labLL D) τ Λ)) ((1 : D.what₂.Tau → GL (Fin n) D.what₂.LL) τ) := fun τ => by
    unfold IsBasisAt
    rw [Pi.one_apply, ← lca_dual (labLL D) τ]
    exact le_antisymm (GlobalTheory.GO.localization_dualFr_tauLat_le (labLL D) τ h2' w hNw)
      (GlobalTheory.GO.localization_dualFr_tauLat_le (labLL D) τ h1' w hNw)
  have h3 : ((s • u : VV D.what₂.LL lam) : Pol D.what₂.LL D.what₂.Tau n) ∈
      transLat lam (nabStd D.what₂.LL lam) (fun τ => dualFr (tauLat (labLL D) τ Λ)) := hsu
  unfold transLat at h3
  simp only [Submodule.mem_iInf] at h3
  have h4 : actP lam (1 : D.what₂.Tau → GL (Fin n) D.what₂.LL)⁻¹ ((s • u : VV D.what₂.LL lam) : Pol D.what₂.LL D.what₂.Tau n) ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd D.what₂.LL lam) := h3 w 1 hB
  have h5 : ∀ F : Pol D.what₂.LL D.what₂.Tau n, actP lam (1 : D.what₂.Tau → GL (Fin n) D.what₂.LL)⁻¹ F = F := fun F => by
    rw [inv_one]
    simp [actP, detTwK_one, trAct_one]
  rw [h5] at h4
  obtain ⟨c, hc, hcF⟩ := h4
  have hc' : c ∉ w.asIdeal := hc
  have hc0 : (c : D.what₂.LL) ≠ 0 := by
    intro h0
    have : c = 0 := RingOfIntegers.ext h0
    exact hc' (this ▸ w.asIdeal.zero_mem)
  obtain ⟨v', hv', ho⟩ := lca_coord D.what₂.embLL lam _ hcF
  obtain ⟨o, ho⟩ := ho i
  have e : v' = D.what₂.embLL ((c : D.what₂.LL) * s) • v := by
    rw [← huv, ← LinearMap.map_smulₛₗ]
    apply Subtype.ext
    rw [hv', GlobalTheory.CoefModel.mapVV_coe, mul_smul]
    rfl
  have hcs : (c : D.what₂.LL) * s ≠ 0 := mul_ne_zero hc0 hs0
  refine ⟨((c : D.what₂.LL) * s)⁻¹ * o, ?_, ?_⟩
  · rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul] at ho
    rw [map_mul, ← ho, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hcs, map_one, one_mul]
  · by_cases h0 : (o : D.what₂.LL) = 0
    · left; rw [h0, mul_zero]
    · right
      have h6 := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w o
      rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (inv_ne_zero hcs) h0, Formalism.DivisionValues.ValuationRepresentative.vw_inv, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hc0 hs0,
        GlobalTheory.LocInt.vw_eq_zero_of_notMem w hc', zero_add]
      have h7 : (0 : ℝ) ≤ (vw w (o : D.what₂.LL) : ℝ) := by exact_mod_cast h6
      push_cast
      linarith
