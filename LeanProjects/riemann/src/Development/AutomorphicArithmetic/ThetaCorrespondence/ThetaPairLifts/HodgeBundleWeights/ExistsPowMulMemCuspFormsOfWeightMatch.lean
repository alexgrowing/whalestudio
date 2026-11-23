import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerCuspMultiplierGap
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsInverseIntegralInvariant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsFlatUnitSection
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsPowMulUnitMemCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerCuspMultiplierGapStatement

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.WtMatchBar
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
set_option maxHeartbeats 800000 in
theorem exists_pow_mul_mem_cuspForms_of_weight_match : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → ∀ f ∈ Y.V (wtOf _ la 0), ∃ (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g h : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), Dom a n ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n ∧ f ^ (k + 1) * g ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n ∧ t ≠ 0 ∧ g * h = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v h := by
  intro hP D T j Y e o hY hE hp hq la hla hbar f hf
  obtain ⟨u, u', t₁, hu, ht₁, huu, hu'⟩ := _root_.GlobalTheory.T.inverse_invariant_integral hP D T j Y e o hY hE
  obtain ⟨N, hN, hU2⟩ := _root_.GlobalTheory.T.detLine_flat_unit_exists hP D T j Y e o hY hE
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 4 * (Module.finrank ℚ D.host.E * D.R.r) + 3 + 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ := _root_.GlobalTheory.T.exists_pow_mul_unit_mem_cusp hP D T j Y e o hY hE la f hf (u ^ M) (u' ^ M) (t₁ ^ M) _ (pow_mem_secZ hu M)
    (pow_ne_zero _ ht₁) (by rw [← mul_pow, huu, smul_pow, one_pow])
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = max K (2 * M + N) := ⟨_, rfl⟩
  obtain ⟨w, a, hDom, hex⟩ := GlobalTheory.T.exists_dominant_exponents_matching_weight_bar_gap _ _ _ la hp hq hla hbar N M k hN (by omega)
  obtain ⟨φ, φ', t₂, hφ, ht₂, hφφ, hφ', hφb⟩ := hU2 w
  refine ⟨k, a, 2 * M, u ^ M * φ, u' ^ M * φ', t₁ ^ M * t₂, hDom, by omega, ?_, mul_ne_zero (pow_ne_zero _ ht₁) ht₂, ?_, ?_⟩
  · refine hK k (hk ▸ le_max_left _ _) φ φ' t₂ _ hφ ht₂ hφφ hφb a (2 * M) hDom ?_
    rw [← GlobalTheory.AllWt.secZ_nat, hex]
    have h1 : f ^ (k + 1) ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ ((k + 1) • GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0) :=
      pow_mem_secZ (GlobalTheory.AllWt.cuspW_le_secZ _ hf) (k + 1)
    have h2 := GlobalTheory.AllWt.mul_mem_secZ h1 (GlobalTheory.AllWt.mul_mem_secZ (pow_mem_secZ hu M) hφ)
    convert h2 using 2
    rw [nsmul_exOf_zero_one, ← GlobalTheory.AllWt.exOf_add, zero_add, add_zero]
  · rw [mul_mul_mul_comm, ← mul_pow, huu, hφφ, smul_pow, one_pow, smul_mul_smul_comm, one_mul]
  · intro la' v hv
    have hV := isVal_valSet la' v hv
    rw [hV.mul]
    rw [hM]
    exact add_nonneg (val_pow_succ_nonneg hV (hu' la' v hv) _) (hφ' la' v hv)
end GlobalTheory.WtMatchBar
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_match_pow_mul_cuspidal : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → ∀ f ∈ Y.V (wtOf _ la 0), ∃ (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g h : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), Dom a n ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n ∧ f ^ (k + 1) * g ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n ∧ t ≠ 0 ∧ g * h = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v h := by
  first | exact @_root_.GlobalTheory.WtMatchBar.exists_pow_mul_mem_cuspForms_of_weight_match | exact _root_.GlobalTheory.WtMatchBar.exists_pow_mul_mem_cuspForms_of_weight_match | (intros; apply _root_.GlobalTheory.WtMatchBar.exists_pow_mul_mem_cuspForms_of_weight_match <;> assumption)
end
