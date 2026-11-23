import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerRepK
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceTransposePow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiPositiveDefiniteCholeskyFormulaStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesCentreEigenfunctionsDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiPolarDecompositionEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeExtendsHolomorphicComplexifiedKStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantsScalarOnLowestKTypeCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKTypeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneLargeGapsStatement

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.DSId.LowCharGap
open GlobalTheory.Dec.FormF
variable {n : ℕ}

private theorem mul_mem_UJset' {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (hh : inUJ ε h) : g * h ∈ UJset ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hh' : hᴴ * Jm ε * h = Jm ε := hh
  show (g * h)ᴴ * Jm ε * (g * h) = Jm ε
  calc (g * h)ᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg', hh']

private theorem eword_congr_on_UJset {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g ∈ UJset ε, f g = f' g) (w : List (Fin n × Fin n)) :
    ∀ g ∈ UJset ε, Eword ε w f g = Eword ε w f' g := by
  induction w with
  | nil => intro g hg; exact h g hg
  | cons p w ih =>
    intro g hg
    have key : ∀ X, inG ε X → Rd X (Eword ε w f) g = Rd X (Eword ε w f') g := by
      intro X hX
      show deriv (fun t : ℝ => Eword ε w f (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
        deriv (fun t : ℝ => Eword ε w f' (g * NormedSpace.exp ((t : ℂ) • X))) 0
      congr 1
      funext t
      exact ih _ (mul_mem_UJset' hg (expUJ n ε X hX t))
    show Rd (cpart1 ε (Matrix.single p.1 p.2 1)) (Eword ε w f) g +
        Complex.I * Rd (cpart2 ε (Matrix.single p.1 p.2 1)) (Eword ε w f) g =
      Rd (cpart1 ε (Matrix.single p.1 p.2 1)) (Eword ε w f') g +
        Complex.I * Rd (cpart2 ε (Matrix.single p.1 p.2 1)) (Eword ε w f') g
    rw [key _ (cpartMem n ε _).1, key _ (cpartMem n ε _).2.1]

lemma gelf_congr {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    (h : ∀ g ∈ UJset ε, f g = f' g) (m : ℕ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    gelf ε m f g = gelf ε m f' g := by
  unfold gelf
  exact Finset.sum_congr rfl (fun a _ => eword_congr_on_UJset h _ g hg)

private theorem star_mem_Kset_of_mem {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    star k ∈ Kset ε := by
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  have h := congrArg star hk'.2
  simp only [star_mul] at h
  have hJ : star (Jm ε) = Jm ε := by rw [Matrix.star_eq_conjTranspose, Jm_conjTranspose]
  rw [hJ] at h
  show star k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ star k * Jm ε = Jm ε * star k
  exact ⟨Unitary.star_mem hk'.1, h.symm⟩

private theorem posDef_conjTranspose_mul_exp_mul {ε : Fin n → Bool} {m X : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ Kset ε)
    (hX : inP ε X) : (mᴴ * NormedSpace.exp X * m).PosDef := by
  have hm' : m ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ m * Jm ε = Jm ε * m := hm
  have hu : mᴴ * m = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mul_self_of_mem hm'.1
  apply Matrix.PosDef.conjTranspose_mul_mul_same (exp_posDef hX)
  intro a b hab
  have := congrArg (fun x => (mᴴ).mulVec x) hab
  simpa only [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec] using this
set_option maxHeartbeats 1000000 in

lemma compress_of_formula (hF : FormulaGap) {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hlam : IsHCParam lam) (hσ : IsDS ε lam σ)
    {h : ℝ} (hgap : GapAtLeast ε lam h) (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h)
    (hS : IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ)) {w : lowKSub ε lam σ}
    (hw : IsHighestUnit ε lam σ (w : H))
    {τ : Matrix (Fin n) (Fin n) ℂ → (lowKSub ε lam σ →L[ℂ] lowKSub ε lam σ)} (hτ : IsTau ε (lowK ε lam) τ w)
    (hτσ : ∀ k ∈ Kset ε, ∀ v : lowKSub ε lam σ, (τ k v : H) = σ (k.map star) v) :
    ∀ g ∈ UJset ε, ∀ u v : lowKSub ε lam σ,
      ⟪(v : H), σ g u⟫_ℂ = ⟪v, Psi ε lam τ w (g.map star) u⟫_ℂ := by
  intro g hg u v
  obtain ⟨-, -, hU, -, -, -, -⟩ := id hσ
  have hKU : IsURepOn (Kset ε) σ := URep_K hU
  obtain ⟨⟨-, hmul⟩, -, hcont⟩ := id hU
  obtain ⟨hfin, hstab, -, -, -⟩ := id hS
  obtain ⟨k, X, hk, hX, rfl⟩ := (polar n ε).1 g hg
  have hsk : star k ∈ Kset ε := star_mem_Kset_of_mem hk
  have hkb : k.map star ∈ Kset ε := K_star hk
  have hXb : inP ε (X.map star) := P_star hX
  have hXg : inG ε X := hX.1
  have hexp : NormedSpace.exp X ∈ UJset ε := by
    have h1 := expUJ n ε X hXg 1
    simp only [Complex.ofReal_one, one_smul] at h1
    exact h1
  have hv'mem : σ (star k) (v : H) ∈ lowKSub ε lam σ := hstab _ hsk _ v.2
  have hcontτ : ∀ y : lowKSub ε lam σ, ContinuousOn (fun m => τ m y) (Kset ε) := by
    intro y
    have h1 : ContinuousOn (fun m : Matrix (Fin n) (Fin n) ℂ => σ (m.map star) (y : H)) (Kset ε) :=
      (hcont (y : H)).comp (continuous_id.matrix_map continuous_star).continuousOn
        (fun m hm => K_UJ (K_star hm))
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact h1.congr (fun m hm => hτσ m hm y)
  have hF' := hF n ε lam H σ hlam hσ h hgap hh (w : H) hw X hX (u : H) u.2 (σ (star k) (v : H)) hv'mem
  have hP := psEntry GlobalTheory.T.phi_positive_definite_cholesky_formula n ε lam (lowKSub ε lam σ) τ w hfin hcontτ
    (NormedSpace.exp (X.map star)) (exp_posDef hXb) u ⟨σ (star k) (v : H), hv'mem⟩
  have hC := muConj n ε (fun m => Phi lam (m⁻¹ * NormedSpace.exp (X.map star) * m) *
    (⟪(⟨σ (star k) (v : H), hv'mem⟩ : lowKSub ε lam σ), τ m w⟫_ℂ * ⟪τ m w, u⟫_ℂ))
  try simp only [] at hC
  have hconj : (k * NormedSpace.exp X).map star = k.map star * NormedSpace.exp (X.map star) := by
    rw [map_star_mul, exp_star]
  rw [hconj, (GlobalTheory.T.psi_polar_decomposition_equivariance n ε lam (lowKSub ε lam σ) τ w hlam hτ).1 _ hkb _ hXb,
    ContinuousLinearMap.comp_apply, hmul k (K_UJ hk) _ hexp, ContinuousLinearMap.comp_apply]
  have e1 : ⟪(v : H), σ k (σ (NormedSpace.exp X) (u : H))⟫_ℂ =
      ⟪σ (star k) (v : H), σ (NormedSpace.exp X) (u : H)⟫_ℂ := by
    rw [inner_rep_K hKU hsk, star_star]
  have e2 : ⟪v, τ (k.map star) (ps ε lam τ w (NormedSpace.exp (X.map star)) u)⟫_ℂ =
      ⟪(⟨σ (star k) (v : H), hv'mem⟩ : lowKSub ε lam σ), ps ε lam τ w (NormedSpace.exp (X.map star)) u⟫_ℂ := by
    rw [Submodule.coe_inner, Submodule.coe_inner, hτσ _ hkb, map_star_star]
    have h5 := inner_rep_K hKU hsk (v : H) ((ps ε lam τ w (NormedSpace.exp (X.map star)) u : lowKSub ε lam σ) : H)
    rw [star_star] at h5
    exact h5.symm
  rw [e1, e2, hF', hP, ← hC]
  congr 1
  congr 1
  funext k'
  have hm : toMK k' ∈ Kset ε := by rw [← range_toMK ε]; exact Set.mem_range_self k'
  have hmb := K_star hm
  rw [Submodule.coe_inner, Submodule.coe_inner, hτσ _ hmb, map_star_star]
  rw [K_inv hmb, K_inv hm, map_star_ct, ← exp_star, ← map_star_mul, ← map_star_mul, Phi_star]
  have hpos := (GlobalTheory.T.phi_positive_definite_cholesky_formula n lam _ (posDef_conjTranspose_mul_exp_mul hm hX)).2.1
  have him : (Phi lam ((toMK k')ᴴ * NormedSpace.exp X * toMK k')).im = 0 := by
    have h2 := (Complex.lt_def.mp hpos).2
    rw [Complex.zero_im] at h2
    linarith
  have hreal : star (Phi lam ((toMK k')ᴴ * NormedSpace.exp X * toMK k')) =
      Phi lam ((toMK k')ᴴ * NormedSpace.exp X * toMK k') :=
    Complex.ext (by simp [Complex.star_def]) (by simp [Complex.star_def, him])
  rw [hreal]
  try rfl

lemma two_mul_lt_gap {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hgap : GapAtLeast ε lam h)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) (a b : Fin n) (hab : ε a ≠ ε b) :
    2 * (n : ℝ) < |lam a - lam b| := by
  have h1 := hgap a b hab
  have hn : (0:ℝ) < n := by exact_mod_cast (Fin.pos a)
  have ht : ∃ x, ε x = true := by
    cases h : ε a
    · exact ⟨b, by cases hb : ε b <;> simp_all⟩
    · exact ⟨a, h⟩
  have hf : ∃ x, ε x = false := by
    cases h : ε a
    · exact ⟨a, h⟩
    · exact ⟨b, by cases hb : ε b <;> simp_all⟩
  obtain ⟨x, hx⟩ := ht
  obtain ⟨y, hy⟩ := hf
  have hq1 : 1 ≤ rkR ε := by
    unfold rkR
    apply le_min
    · exact Finset.card_pos.mpr ⟨x, by simp [hx]⟩
    · exact Finset.card_pos.mpr ⟨y, by simp [hy]⟩
  have hq : (1:ℝ) ≤ ((rkR ε : ℕ) : ℝ) := by exact_mod_cast hq1
  have hp : (1:ℝ) ≤ ((rkR ε : ℕ) : ℝ) ^ ((3:ℝ)/2) := Real.one_le_rpow hq (by norm_num)
  nlinarith

theorem lowChar_of_formula (hF : FormulaGap) (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hlam : IsHCParam lam) (hσ : IsDS ε lam σ) (h : ℝ) (hgap : GapAtLeast ε lam h)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h)
    (hS : IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ)) :
    ∀ s ∈ lowKSub ε lam σ, ∀ y : H, IsZEigen ε (fun a => (lam a : ℂ)) (fun g => ⟪y, σ g s⟫_ℂ) := by
  haveI : CompleteSpace H := hσ.1
  obtain ⟨-, -, hU, -, -, -, -⟩ := id hσ
  have hKU : IsURepOn (Kset ε) σ := URep_K hU
  obtain ⟨⟨hσ1, -⟩, -, -⟩ := id hU
  obtain ⟨c, hc⟩ := GlobalTheory.T.gelfandInvariants_scalar_on_lowestKType_coefficients n ε lam H σ hU hS
  obtain ⟨-, -, -, ⟨v0, hv0S, hv0, hv0w⟩, -⟩ := id hS
  obtain ⟨w, hwdef⟩ : ∃ w : H, w = ((‖v0‖ : ℂ))⁻¹ • v0 := ⟨_, rfl⟩
  have hwS : w ∈ lowKSub ε lam σ := by rw [hwdef]; exact (lowKSub ε lam σ).smul_mem _ hv0S
  have hwn : ‖w‖ = 1 := by rw [hwdef]; exact norm_smul_inv_norm (𝕜 := ℂ) hv0
  have hww : IsWtOn (Kset ε) σ (lowK ε lam) w := by
    intro θ hθ
    rw [hwdef, map_smul, hv0w θ hθ]
    exact smul_comm _ _ _
  obtain ⟨τ, hτ, hτσ⟩ := GlobalTheory.T.kType_extends_holomorphic_complexifiedK n ε (lowK ε lam) H σ (lowKSub ε lam σ) ⟨w, hwS⟩ hKU hS hwn hww
  have hhw : IsHighestUnit ε lam σ ((⟨w, hwS⟩ : lowKSub ε lam σ) : H) := by
    show _ ∧ _ ∧ _
    exact ⟨hwn, hwS, hww⟩
  have hcomp := compress_of_formula hF hlam hσ hgap hh hS hhw hτ hτσ
  have h1UJ : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := K_UJ (one_K ε)
  have hPE := GlobalTheory.T.psiEntries_centreEigenfunctions_discreteSeries n ε lam (lowKSub ε lam σ) τ ⟨w, hwS⟩ hlam hτ ⟨w, hwS⟩ ⟨w, hwS⟩
  have hEC := eigConj n ε _ _ hPE.1 hPE.2
  have hfs : SmoothOnG ε (fun g => ⟪w, σ g w⟫_ℂ) := (hc w hwS w).1
  have hone : ⟪w, σ 1 w⟫_ℂ = 1 := by
    rw [hσ1, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hwn]
    simp
  have hcm : ∀ m, c m = gelfVal (fun a => (lam a : ℂ)) (m + 1) := by
    intro m
    have h1 := (hc w hwS w).2 m 1 h1UJ
    have h2 := gelf_congr hfs (fun g hg => hcomp g hg ⟨w, hwS⟩ ⟨w, hwS⟩) m h1UJ
    have h3 := hEC.2.2 m 1 h1UJ
    have h4 := hcomp 1 h1UJ ⟨w, hwS⟩ ⟨w, hwS⟩
    have h5 : c m * ⟪w, σ 1 w⟫_ℂ = gelfVal (fun a => -(-(lam a : ℂ))) (m + 1) * ⟪w, σ 1 w⟫_ℂ := by
      rw [← h1, h2, h3]
      exact congrArg _ h4.symm
    rw [hone, mul_one, mul_one] at h5
    simpa only [neg_neg] using h5
  intro s hs y
  show _ ∧ _
  refine ⟨(hc s hs y).1, fun m g hg => ?_⟩
  rw [(hc s hs y).2 m g hg, hcm m]

theorem lowChar : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ → ∀ h : ℝ, GapAtLeast ε lam h → 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h → ∀ s ∈ lowKSub ε lam σ, ∀ y : H, IsZEigen ε (fun a => (lam a : ℂ)) (fun g => ⟪y, σ g s⟫_ℂ) := fun n ε lam H _ _ σ hlam hσ h hgap hh =>
  lowChar_of_formula GlobalTheory.T.lowestKType_compressionFormula_of_strictLowestKType n ε lam H σ hlam hσ h hgap hh
    (GlobalTheory.T.lowestKType_isKType_of_large_gaps n ε lam H σ hlam hσ (fun a b hab => two_mul_lt_gap hgap hh a b hab))

end GlobalTheory.DSId.LowCharGap
