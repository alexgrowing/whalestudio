import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientModelTopClassesMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianGrowthConjTorsionTranslatesVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstJetOperatorNormCauchyBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyParameterSizesTestChoicesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

noncomputable section

namespace GlobalTheory.KerConjMean

theorem pow_le_exp_posLog (x : ℝ) (g : ℕ) : x ^ g ≤ Real.exp (g * Real.posLog x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases g with _ | g
    · simp
    · rw [zero_pow (Nat.succ_ne_zero g)]; exact (Real.exp_pos _).le
  · calc x ^ g ≤ |x ^ g| := le_abs_self _
      _ = |x| ^ g := abs_pow x g
      _ = Real.exp (g * Real.log |x|) := by
          rw [← Real.log_pow, Real.exp_log (pow_pos (abs_pos.2 hx) g)]
      _ ≤ Real.exp (g * Real.posLog x) := by
          gcongr
          rw [Real.log_abs]; unfold Real.posLog; exact le_max_right _ _

theorem max_pow_le_exp_posLog (A : ℝ) (hA : 0 < A) (d : ℕ) :
    max 1 A⁻¹ ^ d ≤ Real.exp (d * Real.posLog A⁻¹) := by
  have h1 : max 1 A⁻¹ ≤ Real.exp (Real.posLog A⁻¹) := by
    refine max_le ?_ ?_
    · exact Real.one_le_exp (by unfold Real.posLog; exact le_max_left _ _)
    · calc A⁻¹ = Real.exp (Real.log A⁻¹) := (Real.exp_log (inv_pos.2 hA)).symm
        _ ≤ Real.exp (Real.posLog A⁻¹) := by gcongr; unfold Real.posLog; exact le_max_right _ _
  calc max 1 A⁻¹ ^ d ≤ Real.exp (Real.posLog A⁻¹) ^ d := pow_le_pow_left₀ (by positivity) h1 d
    _ = Real.exp (d * Real.posLog A⁻¹) := (Real.exp_nat_mul _ d).symm

theorem size_bound (K f N b rd Kx W1 W2 a bb c : ℝ) (g : ℕ) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hcf : c ≤ f) (hb3 : 3 ≤ b) (hN1 : 1 ≤ N) (hNb : N ≤ b)
    (hf1 : 1 ≤ f) (hfb : f ≤ b) (hrd0 : 0 ≤ rd) (hrd : rd ≤ b) (ha0 : 0 ≤ a) (haN : a ≤ N) (hbb0 : 0 ≤ bb)
    (hbN : bb ≤ N) (hW1 : W1 ≤ f * N * (8 * b)) (hW2 : W2 ≤ f * N * (8 * b)) (hW10 : 0 ≤ W1) (hW20 : 0 ≤ W2)
    (hg : (g : ℝ) = f * a * bb) (hKx : 0 < Kx)
    (hlogKx : Real.log Kx ≤ K * (W1 + W2 + c * (a + bb) ^ 2 + 1) * Real.log (2 + W1 + W2 + a + bb + c)) :
    Real.log (3 * (2 * (g : ℝ) * rd + 1) ^ g * Kx) ≤ (6 + 126 * K) * f * N * b * Real.log b ∧
      (g : ℝ) ≤ f * N * b := by
  have hb0 : 0 < b := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hlogb : 1 ≤ Real.log b := by
    have : Real.exp 1 ≤ b := by linarith [Real.exp_one_lt_d9]
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hfN1 : 1 ≤ f * N := one_le_mul_of_one_le_of_one_le hf1 hN1
  have hfNb : 1 ≤ f * N * b := by nlinarith
  have hab : a * bb ≤ N * N := mul_le_mul haN hbN hbb0 hN0
  have hfNN : f * a * bb ≤ f * N * N := by
    have := mul_le_mul_of_nonneg_left hab hf0
    linarith
  have hNN : f * N * N ≤ f * N * b := mul_le_mul_of_nonneg_left hNb (by positivity)
  have hgG : (g : ℝ) ≤ f * N * b := by rw [hg]; linarith
  have hfNb3 : f * N * b ≤ b ^ 3 := by
    have h1 := mul_le_mul hfb hNb hN0 hb0.le
    have h2 := mul_le_mul_of_nonneg_right h1 hb0.le
    calc f * N * b ≤ b * b * b := h2
      _ = _ := by ring
  have hg3 : (g : ℝ) ≤ b ^ 3 := hgG.trans hfNb3
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hrdpos : 0 < 2 * (g : ℝ) * rd + 1 := by have := mul_nonneg (mul_nonneg zero_le_two hg0) hrd0; linarith
  have hq : 2 * (g : ℝ) * rd + 1 ≤ 3 * b ^ 4 := by
    have h1 := mul_le_mul hg3 hrd hrd0 (by positivity)
    have h2 : (1 : ℝ) ≤ b ^ 4 := one_le_pow₀ (by linarith)
    have h3 : b ^ 3 * b = b ^ 4 := by ring
    linarith
  have hl3 : Real.log 3 ≤ Real.log b := Real.log_le_log (by norm_num) hb3
  have hlq : Real.log (2 * (g : ℝ) * rd + 1) ≤ 5 * Real.log b := by
    calc _ ≤ Real.log (3 * b ^ 4) := Real.log_le_log hrdpos hq
      _ = Real.log 3 + 4 * Real.log b := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ _ := by linarith
  have hlq0 : 0 ≤ Real.log (2 * (g : ℝ) * rd + 1) := Real.log_nonneg (by
    have := mul_nonneg (mul_nonneg zero_le_two hg0) hrd0; linarith)
  have hY0 : 0 ≤ f * N * b * Real.log b := by positivity
  have hgl : (g : ℝ) * Real.log (2 * (g : ℝ) * rd + 1) ≤ 5 * (f * N * b * Real.log b) := by
    have := mul_le_mul hgG hlq hlq0 (by positivity); linarith
  have hKb : Real.log Kx ≤ 126 * K * (f * N * b * Real.log b) := by
    have hsq : (a + bb) ^ 2 ≤ (2 * N) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hab2 : c * (a + bb) ^ 2 ≤ 4 * (f * N * b) := by
      have := mul_le_mul hcf hsq (by positivity) hf0
      have e : f * (2 * N) ^ 2 = 4 * (f * N * N) := by ring
      linarith
    have hQ1 : W1 + W2 + c * (a + bb) ^ 2 + 1 ≤ 21 * (f * N * b) := by linarith
    have hQ1' : 0 ≤ W1 + W2 + c * (a + bb) ^ 2 + 1 := by positivity
    have hArg0 : 0 < 2 + W1 + W2 + a + bb + c := by linarith
    have hb27 : (27 : ℝ) ≤ b ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hb3 3; norm_num at this; linarith
    have hbb3 : b ≤ b ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have hArg : 2 + W1 + W2 + a + bb + c ≤ 27 * b ^ 3 := by linarith
    have hQ2 : Real.log (2 + W1 + W2 + a + bb + c) ≤ 6 * Real.log b := by
      calc _ ≤ Real.log (27 * b ^ 3) := Real.log_le_log hArg0 hArg
        _ = 3 * Real.log 3 + 3 * Real.log b := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
              show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
        _ ≤ _ := by linarith
    have hQ20 : 0 ≤ Real.log (2 + W1 + W2 + a + bb + c) := Real.log_nonneg (by linarith)
    have := mul_le_mul (mul_le_mul_of_nonneg_left hQ1 hK0) hQ2 hQ20 (by positivity)
    refine hlogKx.trans (this.trans (le_of_eq ?_))
    ring
  refine ⟨?_, hgG⟩
  rw [Real.log_mul (by positivity) hKx.ne', Real.log_mul (by norm_num) (pow_pos hrdpos g).ne', Real.log_pow]
  have hlY : Real.log b ≤ f * N * b * Real.log b := le_mul_of_one_le_left (by linarith) hfNb
  have e : (6 + 126 * K) * f * N * b * Real.log b =
      f * N * b * Real.log b + 5 * (f * N * b * Real.log b) + 126 * K * (f * N * b * Real.log b) := by ring
  rw [e]; linarith

theorem main_of : (GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b =>
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.top j)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.top (j + 1)))),
    (∀ u, ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ,
      ∃ (ρ' : Qbar →ₐ[ℚ] ℂ) (e0 : VC D (ch.G.V (.top j)).rank (ch.G.V (.top (j + 1))).rank → ℂ)
        (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.V (.top j)).rank → D.host.E))
        (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.V (.top (j + 1))).rank → D.host.E)) (κ : ℂ) (k n : ℕ) (r : Fin n → Qbar)
        (s : Fin n → VC D (ch.G.V (.top j)).rank (ch.G.V (.top (j + 1))).rank),
        Even ((ch.G.V (.top j)).rank * (ch.G.V (.top (j + 1))).rank) ∧
        oddE0 D D.host.ccK ch.S.Z.δ ch.S.Z.t0 _ _ e0 ∧ SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ 0 < k ∧
        (∀ i, k • s i ∈ La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) ∧ (∀ ρ₁ : Qbar →+* ℂ, ∑ i, ‖ρ₁ (r i)‖ ≤ 1) ∧
        lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ) = lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ) ∧
        (∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ)) t) ∧
        Formalism.L2.Ker.JetInVV ℂ (wt ch.G (.top j)) (wt ch.G (.top (j + 1))) (nuEnd ch.G (.top A.μ0 j)) ∧
        ∀ u, GlobalTheory.CoefModel.mapVV σ _ (f u) =
          Formalism.L2.Ker.jetOp (wt ch.G (.top j)) (wt ch.G (.top (j + 1)))
            (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fnConj D Qbar ρ' fun z => κ * ∑ i, (r i : ℂ) *
              U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) (Iop D (tor0 D D.host.ccK ch.S.Z.δ)
                (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) e0) z))
            (nuEnd ch.G (.top A.μ0 j)) (GlobalTheory.CoefModel.mapVV σ _ u)) → (∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
  ∀ (a b : ℕ) (e0 : VC D a b → ℂ), Even (a * b) → oddE0 D cc δ t0 a b e0 →
  ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
  ∀ (κ : ℂ), Mod1All κ → ∀ (k n : ℕ) (r : Fin n → Qbar) (s : Fin n → VC D a b), 0 < k →
  (∀ i, k • s i ∈ La D (tor0 D cc δ) Ls Lt) → (∀ ρ₁ : Qbar →+* ℂ, ∑ i, ‖ρ₁ (r i)‖ ≤ 1) →
  ∀ (ρ : Qbar →ₐ[ℚ] ℂ) (t' : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t' →
    0 < area (lamConj Qbar ρ (lamOf D cc δ)) ∧
    CoefIn D (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) Qbar ∧
    Differentiable ℂ (fnConj D Qbar ρ fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) ∧
    ∀ z, ‖fnConj D Qbar ρ (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) z‖ ^ 2 ≤
      3 * (2 * ((fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * b) *
        nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t') ^ (fF D * a * b) *
        Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ)))) → (∃ K : ℝ, 0 ≤ K ∧ ∀ (D : D7) (a b : ℕ) (lam : D.what₂.Tau → DomWeight a) (lam' : D.what₂.Tau → DomWeight b)
  (n : D.what₂.Tau → ℕ), Formalism.L2.Ker.JetInVV ℂ lam lam' n → (∀ v, 0 ≤ nrm lam (fun _ => 1) v) ∧
  ∃ Kx : ℝ, 0 < Kx ∧ Real.log Kx ≤ K * ((∑ τ, ∑ i, ((lam τ).natW i : ℝ)) + (∑ τ, ∑ i, ((lam' τ).natW i : ℝ)) +
      (Fintype.card D.what₂.Tau : ℝ) * ((a : ℝ) + b) ^ 2 + 1) *
      Real.log (2 + (∑ τ, ∑ i, ((lam τ).natW i : ℝ)) + (∑ τ, ∑ i, ((lam' τ).natW i : ℝ)) + a + b + Fintype.card D.what₂.Tau) ∧
    ∀ (H : VC D a b → ℂ) (S A : ℝ), 0 < A → 0 ≤ S → Differentiable ℂ H →
      (∀ z, ‖H z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → ∀ v,
      nrm lam' (fun _ => 1) (Formalism.L2.Ker.jetOp lam lam' (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) H) n v) ≤
        S * Kx * max 1 A⁻¹ ^ (∑ τ, ∑ i, (lam' τ).natW i) * nrm lam (fun _ => 1) v) → (BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b => 3 ≤ b ∧ 1 ≤ bigN D ∧ (bigN D : ℝ) ≤ b ∧ 1 ≤ D.R.f ∧ (D.R.f : ℝ) ≤ b ∧
  Fintype.card D.what₂.Tau ≤ D.R.f ∧ 0 ≤ D.host.rdE ∧ D.host.rdE ≤ b ∧ ∀ j : ℕ, j ≤ D.R.m →
    (ch.G.V (.top j)).rank ≤ bigN D ∧ ∀ τ i, ((wt ch.G (.top j) τ).natW i : ℝ) ≤ 8 * b) → GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → ∀ C1 : ℝ, 0 < C1 → BigC fun _ ch C b => ConjTopAt ch C b C1 := by
  intro tA tB tC tD hPr hInp hDict hDepth C1 hC1
  obtain ⟨K, hK0, hFock⟩ := tC
  obtain ⟨CF0, h⟩ := BigC.and (tA hPr hInp hDict hDepth) tD
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF hCF
  refine ⟨max C0 (2 * (6 + 126 * K) + 9 * C1), fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C ((le_max_left _ _).trans hC)
  refine ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ?_⟩
  obtain ⟨hA, hb3, hN1, hNb, hf1, hfb, hcard, hrd0, hrd, hj⟩ := h D large₂ he hx Γ Pl0 T A Ks R F hS ch h1 h2 h3
  have hCb : 2 * (6 + 126 * K) + 9 * C1 ≤ C := (le_max_right _ _).trans hC
  have hlogb : 1 ≤ Real.log large₂.sc.b := by
    have : Real.exp 1 ≤ large₂.sc.b := by linarith [Real.exp_one_lt_d9]
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hN1' : (1 : ℝ) ≤ (bigN D : ℝ) := by exact_mod_cast hN1
  have hf1' : (1 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf1
  have hfNb : 1 ≤ (D.R.f : ℝ) * (bigN D : ℝ) * large₂.sc.b := by
    have : 1 ≤ (D.R.f : ℝ) * (bigN D : ℝ) := one_le_mul_of_one_le_of_one_le hf1' hN1'
    nlinarith
  have hX : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by positivity
  refine ⟨(6 + 126 * K) * D.R.f * bigN D * large₂.sc.b * Real.log large₂.sc.b, 8 * D.R.f * bigN D * large₂.sc.b,
    D.R.f * bigN D * large₂.sc.b, by positivity, by positivity, by positivity, ?_, ?_⟩
  · have hsig : 0 ≤ sig ch.G :=
      Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    have hC0 : 0 ≤ C := by linarith
    have h2 : 0 ≤ C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G := by positivity
    have h3 := mul_le_mul_of_nonneg_right hCb hX
    unfold aOne
    nlinarith
  · intro Φ β d hocc c j fm hfm σ ρ hρ u B hu
    obtain ⟨ρ', e0, Ls, Lt, κ, k, n, r, s, hev, he0, hLs, hLt, hκ, hk, hs, hr, hlam, ⟨t, ht⟩, hJ, hfeq⟩ :=
      hA Φ β d hocc c j fm hfm σ ρ hρ
    have htc : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ)) (tc D ch.S.Z.δ ch.S.Z.t0 ρ) := by
      rw [hlam]; unfold tc; rw [dif_pos ⟨t, ht⟩]; exact Exists.choose_spec _
    obtain ⟨harea, -, hdiff, hgr⟩ := tB D (hInp D) D.host.ccK ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 _ _ e0 hev he0
      Ls Lt hLs hLt κ hκ k n r s hk hs hr ρ' _ htc
    obtain ⟨hpos, Kx, hKx, hlogKx, hop⟩ := hFock D _ _ (wt ch.G (.top j)) (wt ch.G (.top (j + 1))) _ hJ
    have eA : hArea D ch.S.Z.δ ch.S.Z.t0 ρ = Real.posLog (area (lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ)))⁻¹ := by
      unfold hArea; rw [hlam]
    have eT : hTh D ch.S.Z.δ ch.S.Z.t0 ρ = Real.posLog (nrm1Sq (lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ))
        (GL3Theta.th0 (lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ)) (tc D ch.S.Z.δ ch.S.Z.t0 ρ))) := by
      unfold hTh; rw [hlam]
    set L := lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ) with hL
    set X := nrm1Sq L (GL3Theta.th0 L (tc D ch.S.Z.δ ch.S.Z.t0 ρ)) with hXdef
    set a := (ch.G.V (.top j)).rank with ha
    set bb := (ch.G.V (.top ((j : ℕ) + 1))).rank with hbb
    set g := fF D * a * bb with hg
    set P := 3 * (2 * ((g : ℕ) : ℝ) * D.host.rdE + 1) ^ g with hP
    set deg := ∑ τ, ∑ i, (wt ch.G (.top ((j : ℕ) + 1)) τ).natW i with hdeg
    have hS : 0 ≤ P * X ^ g := by
      have h0 := hgr 0
      have : (∑ τ, ∑ i, ∑ j, ‖(0 : VC D a bb) τ i j‖ ^ 2) = 0 := by simp
      rw [this, mul_zero, zero_div, Real.exp_zero, mul_one] at h0
      exact le_trans (sq_nonneg _) h0
    have hop' := hop _ (P * X ^ g) _ harea hS hdiff hgr (GlobalTheory.CoefModel.mapVV σ _ u)
    have hM0 : 0 ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg :=
      mul_nonneg (mul_nonneg hS hKx.le) (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
    have hrdpos : 0 < 2 * ((g : ℕ) : ℝ) * D.host.rdE + 1 := by
      have := mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg g)) hrd0; linarith
    have hPpos : 0 < P := by rw [hP]; exact mul_pos (by norm_num) (pow_pos hrdpos g)

    have hW : ∀ jj : ℕ, jj ≤ D.R.m → (∑ τ, ∑ i, ((wt ch.G (.top jj) τ).natW i : ℝ)) ≤
        (D.R.f : ℝ) * (bigN D : ℝ) * (8 * large₂.sc.b) := by
      intro jj hjj
      calc (∑ τ, ∑ i, ((wt ch.G (.top jj) τ).natW i : ℝ)) ≤
            ∑ τ : D.what₂.Tau, ∑ i : Fin (ch.G.V (.top jj)).rank, (8 * large₂.sc.b) :=
            Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => (hj jj hjj).2 τ i
        _ = (Fintype.card D.what₂.Tau : ℝ) * (((ch.G.V (.top jj)).rank : ℝ) * (8 * large₂.sc.b)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ (D.R.f : ℝ) * ((bigN D : ℝ) * (8 * large₂.sc.b)) := by
            have h1 : (Fintype.card D.what₂.Tau : ℝ) ≤ D.R.f := by exact_mod_cast hcard
            have h2 : ((ch.G.V (.top jj)).rank : ℝ) ≤ bigN D := by exact_mod_cast (hj jj hjj).1
            exact mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity) (by positivity)
        _ = _ := by ring
    have hW0 : ∀ jj : ℕ, 0 ≤ (∑ τ, ∑ i, ((wt ch.G (.top jj) τ).natW i : ℝ)) := fun jj =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have haN : (a : ℝ) ≤ bigN D := by exact_mod_cast (hj j j.2.le).1
    have hbN : (bb : ℝ) ≤ bigN D := by exact_mod_cast (hj ((j : ℕ) + 1) (Nat.succ_le_of_lt j.2)).1
    have hgc : (g : ℝ) = (D.R.f : ℝ) * a * bb := by rw [hg]; push_cast; rfl
    obtain ⟨hc0, hgG⟩ := size_bound K D.R.f (bigN D) large₂.sc.b D.host.rdE Kx _ _ a bb (Fintype.card D.what₂.Tau) g hK0 (Nat.cast_nonneg _) (by exact_mod_cast hcard) hb3 hN1' hNb hf1' hfb
      hrd0 hrd (Nat.cast_nonneg _) haN (Nat.cast_nonneg _) hbN (hW j j.2.le) (hW _ (Nat.succ_le_of_lt j.2))
      (hW0 _) (hW0 _) hgc hKx hlogKx
    have hc : Real.log (P * Kx) ≤ (6 + 126 * K) * D.R.f * bigN D * large₂.sc.b * Real.log large₂.sc.b := by
      rw [hP]; exact hc0
    have hdN : (deg : ℝ) ≤ 8 * D.R.f * bigN D * large₂.sc.b := by
      have e : (deg : ℝ) = ∑ τ, ∑ i, ((wt ch.G (.top ((j : ℕ) + 1)) τ).natW i : ℝ) := by rw [hdeg]; push_cast; rfl
      rw [e]; refine (hW _ (Nat.succ_le_of_lt j.2)).trans (le_of_eq ?_); ring
    have hpA : 0 ≤ Real.posLog (area L)⁻¹ := by unfold Real.posLog; exact le_max_left _ _
    have hpX : 0 ≤ Real.posLog X := by unfold Real.posLog; exact le_max_left _ _
    have hMexp : P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg ≤ Real.exp ((6 + 126 * K) * D.R.f * bigN D * large₂.sc.b *
        Real.log large₂.sc.b + 8 * D.R.f * bigN D * large₂.sc.b * hArea D ch.S.Z.δ ch.S.Z.t0 ρ +
        D.R.f * bigN D * large₂.sc.b * hTh D ch.S.Z.δ ch.S.Z.t0 ρ) := by
      have hXg := pow_le_exp_posLog X g
      have hMd := max_pow_le_exp_posLog (area L) harea deg
      have step1 : P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg ≤
          (P * Kx) * (Real.exp (g * Real.posLog X) * Real.exp (deg * Real.posLog (area L)⁻¹)) := by
        have := mul_le_mul hXg hMd (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (Real.exp_pos _).le
        calc P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg = (P * Kx) * (X ^ g * max 1 (area L)⁻¹ ^ deg) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left this (mul_nonneg hPpos.le hKx.le)
      refine step1.trans ?_
      have eq : (P * Kx) * (Real.exp (g * Real.posLog X) * Real.exp (deg * Real.posLog (area L)⁻¹)) =
          Real.exp (Real.log (P * Kx) + g * Real.posLog X + deg * Real.posLog (area L)⁻¹) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (mul_pos hPpos hKx)]; ring
      rw [eq, Real.exp_le_exp, eA, eT]
      linarith [mul_le_mul_of_nonneg_right hgG hpX, mul_le_mul_of_nonneg_right hdN hpA]
    rw [hfeq u]
    calc _ ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg * nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV σ _ u) := hop'
      _ ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg * B := mul_le_mul_of_nonneg_left hu hM0
      _ ≤ _ := mul_le_mul_of_nonneg_right hMexp (le_trans (hpos _) hu)

theorem conjTopK : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → ∀ C1 : ℝ, 0 < C1 → BigC fun _ ch C b => ConjTopAt ch C b C1 :=
  main_of GlobalTheory.T.coefficient_model_top_classes_map GlobalTheory.T.gaussianGrowth_conj_torsionTranslates_vacuum GlobalTheory.T.exists_const_jetOperatorNorm_cauchyBound GlobalTheory.T.eventually_parameterSizes_testChoices

end GlobalTheory.KerConjMean

end
