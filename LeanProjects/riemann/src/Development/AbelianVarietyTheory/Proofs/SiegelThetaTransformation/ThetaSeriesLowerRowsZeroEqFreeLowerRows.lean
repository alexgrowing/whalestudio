import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaVacuumUnitaryColumnChangeUnitFactorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaHeisenbergUnitaryColumnChangeStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRowHighestHarmonicPolyDerivUnitaryActionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCmFieldGeneratorAtPrimesDividingStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticeDiagonalUnitaryPatchedStandardStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SumMovedVacuumTranslatesEqFreeRowTestFunctionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.DiagFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem vset_one {M : ℕ} {Λ : Lt E n} (h : Λ ∈ Vset E n M) : Λ ∈ Vset E n 1 := by
  obtain ⟨hfg, hdual, s, hs, -, h1, h2⟩ := h
  exact ⟨hfg, hdual, s, hs, Nat.coprime_one_right s, h1, h2⟩

theorem conjI_mono {P Q : Ideal (𝓞 E)} (h : P ≤ Q) : conjI P ≤ conjI Q := by
  unfold conjI
  exact Ideal.span_mono fun _ ⟨b, hb, e⟩ => ⟨b, h hb, e⟩

theorem isSB_smul (c : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (c • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x fun h0 => hx ?_, fun x y hy => ?_⟩
  · simp [h0]
  · simp [h2 x y hy]

theorem thA_sum (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (f : T → TF n g) (hf : ∀ i, IsSB (f i)) :
    thA X bas idx (∑ i ∈ s, f i) x = ∑ i ∈ s, thA X bas idx (f i) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have h0 := GlobalTheory.SW.UnAct.thA_smul (bas := bas) idx x (0 : ℂ) (0 : TF n g)
    simpa using h0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      GlobalTheory.SW.UnAct.thA_add idx hs hx (hf a) (GlobalTheory.SW.RecSum.isSB_sum s f hf), ih]

theorem isSB_unitv_projA (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {w : E}
    (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) {L : Lt E r} (hL : SelfD X L) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n 1) {φ : TF n g} (hφ : IsSB φ) :
    IsSB (unitv (projA X bas w (tens Λ L) φ)) := by
  unfold unitv projA
  refine isSB_smul _ (isSB_smul _ ?_)
  refine finsum_mem_induction (fun ψ => IsSB ψ) isSB_zero
    (fun a b ha hb => (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) a b ha hb).1) ?_
  rintro _ ⟨y, -, rfl⟩
  exact isSB_smul _ ((heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ).1

private theorem thA_finset_sum_smul (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (a : T → ℂ) (ψ : T → TF n g)
    (hψ : ∀ i, IsSB (ψ i)) (z : Fin n → Fin g → ℂ) :
    thA X bas idx (∑ i ∈ s, a i • ψ i) x z = ∑ i ∈ s, a i * thA X bas idx (ψ i) x z := by
  rw [thA_sum idx hs hx s _ (fun i => isSB_smul (a i) (hψ i)), Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.SW.UnAct.thA_smul (bas := bas) idx x (a i) (ψ i)]
  rfl

theorem thP_phi_eq_thP_phiF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 : Ideal (𝓞 E)), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ∀ Λ ∈ Vset E n M, ∀ P ∈ Harm.rowHighest ℂ k k', ∃ Λ' ∈ Vset E n M, ∃ P' ∈ Harm.rowHighest ℂ k k', ∀ L ∈ D.lats, ∀ x ∈ X.dom, thP X hr bas idx (D.phi bas hn v₀ L Λ) P x = thP X hr bas idx (phiF bas D 𝔐 hn v₀ L Λ') P' x := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn D hrn M 𝔐 𝔍 hM hMm hsplit hcop v₀ hv₀ k k' Λ hΛ P hP
  have hle : D.𝔪 ≤ 𝔍 := by
    rw [hsplit]
    exact Ideal.mul_le_inf.trans inf_le_right
  have h𝔍 : 𝔍 ≠ ⊥ := by
    intro h0
    apply D.ne_bot
    rw [hsplit, h0, Ideal.mul_bot]
  have hMJ : ((M : ℕ) : 𝓞 E) ∈ 𝔍 := hle hMm
  have hcopJ : IsCoprime 𝔍 (conjI 𝔍) := by
    have h1 := D.cop
    rw [Ideal.isCoprime_iff_sup_eq] at h1 ⊢
    exact top_unique (h1.symm.le.trans (sup_le_sup hle (conjI_mono hle)))
  obtain ⟨α, 𝔞, hα, hspan, hcopa⟩ := GlobalTheory.T.exists_cmField_generator_at_primes_dividing E 𝔍 M h𝔍 hM
  set H : Matrix (Fin n) (Fin n) E :=
    Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) with hHdef
  obtain ⟨hunit, hmove⟩ := GlobalTheory.T.selfDual_lattice_diagonal_unitary_patched_standard E n r M 𝔍 𝔞 α hM hMJ hcopJ hα hspan hcopa H hHdef
  obtain ⟨Λ', hΛ', Λ'', hΛ'', hmv, hle1, hle2⟩ := hmove Λ hΛ
  obtain ⟨t, ht0, ht⟩ := GlobalTheory.T.sum_moved_vacuum_translates_eq_freeRow_testFunction E r X g bas idx n hs hn D hrn M 𝔐 𝔍 𝔞 α hM hMm hsplit hcop hα
    hspan hcopa v₀ hv₀ H hHdef Λ hΛ Λ' hΛ' Λ'' hΛ'' hmv hle1 hle2
  obtain ⟨t', ht'1, ht'⟩ := GlobalTheory.T.thetaVacuum_unitary_column_change_unit_factor E r X g bas idx n hs hn D.w D.w_int D.w_tr H hunit Λ
    (vset_one hΛ) Λ'' hΛ'' hmv
  obtain ⟨P', hP', hPd⟩ := GlobalTheory.T.exists_rowHighest_harmonic_polyDeriv_unitaryAction E r X g q0 hr bas idx n hs hn H hunit k k' P hP
  have ht'0 : t' ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at ht'1
    exact zero_ne_one ht'1
  refine ⟨Λ', hΛ', (t / t') • P', Submodule.smul_mem _ _ hP', fun L hL x hx => ?_⟩
  have hSh : SelfD X (D.sh L) := ((GlobalTheory.T.level_structure_properties E r X g bas idx n hs hn D hrn).2.2.2.1 L hL).1
  have hv := hv₀ L hL
  have hφ := isSB_unitv_projA idx hs hn D.w_int D.w_tr hSh (vset_one hΛ) hv.1
  have hφ'' := isSB_unitv_projA idx hs hn D.w_int D.w_tr hSh hΛ'' hv.1
  have hheis : ∀ (y : Matrix (Fin n) (Fin r) E) (ψ : TF n g), IsSB ψ → IsSB (heisG X bas y ψ) :=
    fun y ψ hψ => ((heisG_laws E r X g bas idx n hs hn).2.2.2 y ψ hψ).1
  obtain ⟨s, hs1, hs2⟩ := ht L hL
  have hphiF : IsSB (phiF bas D 𝔐 hrn v₀ L Λ') := by
    have h2 : phiF bas D 𝔐 hrn v₀ L Λ' = t⁻¹ • (t • phiF bas D 𝔐 hrn v₀ L Λ') := by
      rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [h2, ← hs2]
    exact isSB_smul _ (GlobalTheory.SW.RecSum.isSB_sum s _ fun y => isSB_smul _ (hheis _ _ hφ''))
  have hDphi : IsSB (D.phi bas hrn v₀ L Λ) := by
    rw [hs1]
    exact GlobalTheory.SW.RecSum.isSB_sum s _ fun y => isSB_smul _ (hheis _ _ hφ)
  have key : ∀ z, t * thA X bas idx (phiF bas D 𝔐 hrn v₀ L Λ') x (GlobalTheory.Dict.hAct X idx H z) =
      t' * thA X bas idx (D.phi bas hrn v₀ L Λ) x z := by
    intro z
    have e1 := congrFun (GlobalTheory.SW.UnAct.thA_smul (bas := bas) idx x t (phiF bas D 𝔐 hrn v₀ L Λ'))
      (GlobalTheory.Dict.hAct X idx H z)
    rw [Pi.smul_apply, smul_eq_mul] at e1
    rw [← e1, ← hs2, thA_finset_sum_smul idx hs hx s _ _ (fun y => hheis _ _ hφ''), hs1,
      thA_finset_sum_smul idx hs hx s _ _ (fun y => hheis _ _ hφ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [GlobalTheory.T.theta_heisenberg_unitary_column_change E r X g bas idx n hs hn H hunit _ _ hφ hφ'' t' x hx
      (fun z => ht' (D.sh L) hSh (v₀ L) hv x hx z) y z]
    ring
  have hana := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn k k' _ hphiF P' hP').2.2.2 x hx
  have hdiff := ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff (GlobalTheory.SW.ThetaHol.differentiable_thA idx hs hDphi hx)
  have hfun : (fun z => thA X bas idx (phiF bas D 𝔐 hrn v₀ L Λ') x (GlobalTheory.Dict.hAct X idx H z)) =
      (t' / t) • thA X bas idx (D.phi bas hrn v₀ L Λ) x := by
    funext z
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination key z
  unfold GlobalTheory.SW.thP
  rw [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul, ← hPd _ hana, hfun,
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul_fun _ _ hdiff]
  field_simp

end GlobalTheory.Dict.DiagFree
