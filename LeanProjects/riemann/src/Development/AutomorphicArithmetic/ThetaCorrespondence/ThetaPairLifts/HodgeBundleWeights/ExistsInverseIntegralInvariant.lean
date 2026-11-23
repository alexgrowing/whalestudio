import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvertibleSectionValuationNonneg
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvertibleSectionValuationNonnegStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.KeyInvInt
open GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FlatLine
set_option maxHeartbeats 800000 in
theorem exists_inverse_integral_invariant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1) ∧ t ≠ 0 ∧ u * u' = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v u' := by
  intro _hP D T j Y e o hY _hE
  have hσ := goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom
  obtain ⟨hr, -, -, -, -, g, ee, F, -⟩ := hY.unf _ hσ
  have h1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  obtain ⟨K, hK, hKv⟩ := GlobalTheory.KeyFourth.exists_unit_secZ_keyRule κ k₁ k₂ k₆ _ _ _ _ _ _ g ee hpq
  obtain ⟨ρ, hρ⟩ := GlobalTheory.KeyRoot.exists_keySec_pow_four κ k₁ k₂ k₆ k₄ _ _ _ _ _ _ g ee _ _ (Y.U _) K hσ
    (hY.unf _ hσ) hY.geo hpq hK hKv
  choose a ha hZ using hρ
  have hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  have hKint : ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 Y.d.c₂.F)),
      ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) w, 0 ≤ v (K : Rul Y.d.Xo₂ Y.d.c₂) := by
    by_cases hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p
    · exact fun w v hv => (GlobalTheory.KeyIntegralVal.key_valuation_bounds κ hkr _ _ _ _ _ _ g ee K hpq hg hK hKv w v hv).1
    · exact GlobalTheory.T.thetaKeyRule_valuation_nonneg_integral_framed_point κ hkr _ _ _ _ _ _ g ee K hpq hK hKv
  obtain ⟨t, ht, hint⟩ := GlobalTheory.T.exists_constant_smul_integral_of_fourth_power _ _ _ _ _ _ (K : Rul Y.d.Xo₂ Y.d.c₂) (ρ.ρ : Rul Y.d.Xo₂ Y.d.c₂) a ha hZ hKint
  have hwt : ∀ (m : ℤ) (τ : D.host.E →+* ℂ) (i : ℕ), i < (T.Q.Dw j).mult τ → (wtOf (T.Q.Dw j) 0 m).1 (τ, i) = -m :=
    GlobalTheory.KeyRootTw.wtOf_zero_fst _ _ (T.Q.Dw j)
  have hex : GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1 = -keyEx (T.Q.Dw j) := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · rfl
    · simp only [GlobalTheory.AllWt.exOf, exZ, keyEx, Pi.neg_apply]
      exact hwt 1 τ i i.2
  refine ⟨((ρ.ρ⁻¹ : (Rul Y.d.Xo₂ Y.d.c₂)ˣ) : Rul Y.d.Xo₂ Y.d.c₂), t • (ρ.ρ : Rul Y.d.Xo₂ Y.d.c₂), t, ?_, ht, ?_, hint⟩
  · rw [hex]
    exact GlobalTheory.AllWt.inv_mem_secZ ρ.mem
  · rw [mul_smul_comm, Units.inv_mul]
end GlobalTheory.KeyInvInt
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_invariant_integral : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1) ∧ t ≠ 0 ∧ u * u' = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v u' := by
  first | exact @_root_.GlobalTheory.KeyInvInt.exists_inverse_integral_invariant | exact _root_.GlobalTheory.KeyInvInt.exists_inverse_integral_invariant | (intros; apply _root_.GlobalTheory.KeyInvInt.exists_inverse_integral_invariant <;> assumption)
end
