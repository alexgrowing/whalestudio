import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuadAOf
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.PhiReg
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.OOConv

noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

namespace G

set_option maxHeartbeats 800000 in
theorem quadA_of (hSch : SchurH) (hNIs : CompanionTheory.D.Upq.BesselFunctionalConstruction.NormIdSm) (hNI : NormInv) (hGG : GrowthG)
    (hDD : CompanionTheory.D.Upq.BesselFunctionalConstruction.DecDD) (hBC : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv) (hIn : CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs) {k r : ℕ} {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)} {w0 : H}
    {u u' : Fin k → ℝ} {νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hS1 : Side k r ε lam h σ w0 D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq)
    (hS2 : Side k r ε lam h σ w0 D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN D.μG νq')
    {l : H → Wp} {l' : H → Wq}
    (hbe : ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be D.z Formalism.QuantumDeterminants.cStd D.π σ D.μW D.μN x y = (innerSL ℂ (l y)).smulRight (l x))
    (hbe' : ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be D.z' Formalism.QuantumDeterminants.cStd D.π' σ D.μW' D.μN x y = (innerSL ℂ (l' y)).smulRight (l' x))
    {γ : Mx k r} (hγ : γ ∈ Formalism.FourierDecayAlt.JF.Om k r D.z D.z') :
    ∫⁻ zz, ∫⁻ zz', ∫⁻ s, ∫⁻ s',
      ((‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖₊ : ℝ≥0) : ℝ≥0∞) *
        ((‖l (σ (Matrix.of zz) w0)‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l' (σ (Matrix.of zz') w0)‖₊ : ℝ≥0) : ℝ≥0∞)
      ∂(muSof D.μW' D.μN) ∂(muSof D.μW D.μN) ∂νq' ∂νq < ⊤ := by
  have hS1' := hS1
  obtain ⟨hl, hds, -, hG, hw0, hz1, hT, -, hπ, hW, hN, hGm, hq⟩ := hS1'
  have hS2' := hS2
  obtain ⟨-, -, -, -, -, hz2, hT', -, hπ', hW', -, -, hq'⟩ := hS2'
  have : SigmaFinite D.μW := hW.1
  have : SigmaFinite D.μN := hN.1
  have : SigmaFinite D.μW' := hW'.1
  have : SigmaFinite D.μG := hGm.1
  have hGc : ∀ᵐ x ∂D.μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hGm.2.2.1
  have hw0DD := cmHalfIntegralGenerator_mem_algebraicClosure hds w0
  have hf1 := DDSmoothness.muSof_facts hW hN
  have hf2 := DDSmoothness.muSof_facts hW' hN
  have hae1 := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hf1.1 hf1.2 hq
  have hae2 := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hf2.1 hf2.2 hq'
  have hγU : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := hγ.1

  by_cases hA : ∃ v ∈ DDsp σ w0, l v ≠ 0
  swap
  · push Not at hA
    calc _ ≤ ∫⁻ zz, (0 : ℝ≥0∞) ∂νq := by
          apply lintegral_mono_ae
          filter_upwards [hae1] with zz hzz
          simp [hA _ (dd_stable hds hzz w0 hw0DD)]
      _ < ⊤ := by simp
  by_cases hA' : ∃ v ∈ DDsp σ w0, l' v ≠ 0
  swap
  · push Not at hA'
    calc _ ≤ ∫⁻ zz, (0 : ℝ≥0∞) ∂νq := by
          apply lintegral_mono
          intro zz
          calc _ ≤ ∫⁻ zz', (0 : ℝ≥0∞) ∂νq' := by
                apply lintegral_mono_ae
                filter_upwards [hae2] with zz' hzz'
                simp [hA' _ (dd_stable hds hzz' w0 hw0DD)]
            _ = 0 := by simp
      _ < ⊤ := by simp
  obtain ⟨v, hv, hlv⟩ := hA
  obtain ⟨v', hv', hlv'⟩ := hA'
  obtain ⟨e0, he0, hee0⟩ := coef_ext hds w0 w0
  obtain ⟨e1, he1, hee1⟩ := coef_ext hds v w0
  obtain ⟨e2, he2, hee2⟩ := coef_ext hds v' w0
  obtain ⟨C0, hC0⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD
    w0 hw0DD
  obtain ⟨C1, hC1⟩ := hDD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS1 w0 hw0DD v hv
  obtain ⟨C2, hC2⟩ := hDD hIn k r ε lam h H σ w0 Wq D.z' Formalism.QuantumDeterminants.cStd u' D.π' D.μW' D.μN D.μG νq' hS2 w0 hw0DD
    v' hv'
  have hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee0 y hy]; exact hC0 y hy
  have hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee1 y hy]; exact hC1 y hy
  have hb2 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e2 y‖ ≤ C2 * B.gN y ^ (-aOf r h) :=
    fun y hy => by rw [hee2 y hy]; exact hC2 y hy
  have h4 := gap4 hG
  have hAG := ag_nonneg k r
  have hn2 : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hb0 : 0 < aOf r h - AG k r - 1 := by linarith
  have hba : aOf r h - AG k r - 1 ≤ aOf r h := by linarith
  have hab : aOf r h - (aOf r h - AG k r - 1) = AG k r + 1 := by ring
  have hThrb : JF.TransportedAlt k r (aOf r h - AG k r - 1) 0 := by
    unfold JF.TransportedAlt
    have hpos : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hpos]
    linarith
  have hKg : ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(aOf r h - (aOf r h - AG k r - 1)))‖ₑ ∂D.μG < ⊤ :=
    (hGG k r D.μG _ hGm (by rw [hab]; linarith)).hasFiniteIntegral
  have hLa0 := la_fin hNI D hThrb hb0.ne' hγ
  obtain ⟨La, hLadef⟩ : ∃ La : ℝ≥0∞, La = ∫⁻ p, ∫⁻ q, ‖B.gN ((Matrix.of p.1 * Matrix.of p.2) * γ *
    (Matrix.of q.1 * Matrix.of q.2)⁻¹) ^ (-(aOf r h - AG k r - 1))‖ₑ ∂(D.μW'.prod D.μN) ∂(D.μW.prod D.μN) :=
    ⟨_, rfl⟩
  have hLa : La < ⊤ := by
    have hmG := meas_G (k := k) (r := r) γ (aOf r h - AG k r - 1)
    have e : La = ∫⁻ pp, ‖B.gN (Matrix.of pp.1.1 * Matrix.of pp.1.2 * γ * (Matrix.of pp.2.2)⁻¹ *
        (Matrix.of pp.2.1)⁻¹) ^ (-(aOf r h - AG k r - 1))‖ₑ ∂D.μSS := by
      rw [show D.μSS = (D.μW.prod D.μN).prod (D.μW'.prod D.μN) from rfl, lintegral_prod _ hmG.aemeasurable, hLadef]
      apply lintegral_congr; intro p; apply lintegral_congr; intro q
      rw [Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
    rw [e]; exact hLa0
  have hpUH : ∀ᵐ p ∂(D.μW.prod D.μN), Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    (prod_ae hW hN).mono fun p hp => DDSmoothness.uh_mul hp.1.1 hp.2.1
  have hqUH : ∀ᵐ q ∂(D.μW'.prod D.μN), Matrix.of q.1 * Matrix.of q.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    (prod_ae hW' hN).mono fun q hq => DDSmoothness.uh_mul hq.1.1 hq.2.1
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ≥0∞, K1 = ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ := ⟨_, rfl⟩
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ≥0∞, K2 = ‖((‖l' v'‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l' v'‖ₑ := ⟨_, rfl⟩
  have hK : K1 * K2 ≠ ⊤ := by rw [hK1, hK2]; simp [ENNReal.mul_eq_top]
  have hA1m := Aext_meas he1
  have hA2m := Aext_meas he2
  have hI2m := Iint_meas hA2m (D.μW'.prod D.μN)
  have hLm := meas_lam he0 γ (D.μW.prod D.μN) (D.μW'.prod D.μN)
  obtain ⟨LL, hLL⟩ : ∃ LL : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞,
      LL = abelian₂ e0 γ (D.μW.prod D.μN) (D.μW'.prod D.μN) := ⟨_, rfl⟩
  have hLLm : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => LL t.1 t.2) := by rw [hLL]; exact hLm

  have step1 : ∀ᵐ zz ∂νq, ∀ᵐ zz' ∂νq', ∫⁻ s, ∫⁻ s',
      ((‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖₊ : ℝ≥0) : ℝ≥0∞) *
        ((‖l (σ (Matrix.of zz) w0)‖₊ : ℝ≥0) : ℝ≥0∞) * ((‖l' (σ (Matrix.of zz') w0)‖₊ : ℝ≥0) : ℝ≥0∞)
      ∂(muSof D.μW' D.μN) ∂(muSof D.μW D.μN) ≤
      (K1 * K2) * (Iint (Aext e1) (D.μW.prod D.μN) zz * (Iint (Aext e2) (D.μW'.prod D.μN) zz' * LL zz zz')) := by
    filter_upwards [hae1] with zz hzz
    filter_upwards [hae2] with zz' hzz'
    have bl : ‖l (σ (Matrix.of zz) w0)‖ₑ ≤ K1 * Iint (Aext e1) (D.μW.prod D.μN) zz := by
      rw [hK1]; exact l_le_I (c := Formalism.QuantumDeterminants.cStd) hds hT hπ hW hN hbe hv hlv hw0DD hee1 hzz
    have bl' : ‖l' (σ (Matrix.of zz') w0)‖ₑ ≤ K2 * Iint (Aext e2) (D.μW'.prod D.μN) zz' := by
      rw [hK2]; exact l_le_I (c := Formalism.QuantumDeterminants.cStd) hds hT' hπ' hW' hN hbe' hv' hlv' hw0DD hee2 hzz'
    have hc : ‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l' (σ (Matrix.of zz') w0)‖ₑ ≠ ⊤ :=
      ENNReal.mul_ne_top enorm_ne_top enorm_ne_top
    have hqi := quad_inner hds w0 he0 hee0 hγU hf1.2 hf2.2 hzz hzz'
    rw [← hLL] at hqi
    simp only [← enorm_eq_nnnorm]
    calc ∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ *
          ‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l' (σ (Matrix.of zz') w0)‖ₑ ∂(muSof D.μW' D.μN) ∂(muSof D.μW D.μN)
        = ∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ *
          (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l' (σ (Matrix.of zz') w0)‖ₑ) ∂(muSof D.μW' D.μN) ∂(muSof D.μW D.μN) :=
          lintegral_congr fun s => lintegral_congr fun s' => mul_assoc _ _ _
      _ = (∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ
            ∂(muSof D.μW' D.μN) ∂(muSof D.μW D.μN)) *
          (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l' (σ (Matrix.of zz') w0)‖ₑ) := by
          rw [← lintegral_mul_const' _ _ hc]
          apply lintegral_congr; intro s
          rw [lintegral_mul_const' _ _ hc]
      _ = LL zz zz' * (‖l (σ (Matrix.of zz) w0)‖ₑ * ‖l' (σ (Matrix.of zz') w0)‖ₑ) := by rw [hqi]
      _ ≤ LL zz zz' * ((K1 * Iint (Aext e1) (D.μW.prod D.μN) zz) * (K2 * Iint (Aext e2) (D.μW'.prod D.μN) zz')) := by
          gcongr
      _ = (K1 * K2) * (Iint (Aext e1) (D.μW.prod D.μN) zz * (Iint (Aext e2) (D.μW'.prod D.μN) zz' * LL zz zz')) := by
          ring
  have hinvR : ∀ zz, ∀ᵐ z ∂νq', ∀ᵐ q ∂(D.μW'.prod D.μN),
      LL zz (fun i j => (Matrix.of q.1 * Matrix.of q.2 * Matrix.of z) i j) = LL zz z := by
    intro zz
    rw [hLL]
    exact Filter.Eventually.of_forall fun z => (prod_ae hW' hN).mono
      fun q hq0 => lam_right he0 γ hW' hN hz2 (D.μW.prod D.μN) hq0.1 hq0.2 zz z
  have hinvL : ∀ᵐ z ∂νq, ∀ᵐ p ∂(D.μW.prod D.μN),
      (∫⁻ y, Aext e2 y * LL (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) y ∂D.μG) =
        ∫⁻ y, Aext e2 y * LL z y ∂D.μG := by
    rw [hLL]
    exact Filter.Eventually.of_forall fun z => (prod_ae hW hN).mono
      fun p hp0 => lintegral_congr fun y => by rw [lam_left he0 γ hW hN hz1 (D.μW'.prod D.μN) hp0.1 hp0.2 z y]
  have hLz : ∀ zz, Measurable (fun y => LL zz y) := fun zz => hLLm.comp (measurable_const.prodMk measurable_id)
  have hΦm : Measurable (fun x => ∫⁻ y, Aext e2 y * LL x y ∂D.μG) :=
    ((hA2m.comp measurable_snd).mul hLLm).lintegral_prod_right'
  obtain ⟨bb, hbbdef⟩ : ∃ bb : ℝ, bb = aOf r h - AG k r - 1 := ⟨_, rfl⟩
  rw [← hbbdef] at hba hb0 hLadef
  obtain ⟨Fx, hFx⟩ : ∃ Fx : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, Fx = fun x => ‖B.gN (Matrix.of x) ^ (-(aOf r h - bb))‖ₑ :=
    ⟨_, rfl⟩
  have hFxm : Measurable Fx := by
    rw [hFx]; exact (((gN_cont.comp mt_cont).measurable).pow_const _).enorm
  have hKg' : ∫⁻ x, Fx x ∂D.μG < ⊤ := by rw [hFx, hbbdef]; exact hKg
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ≥0∞, c = ENNReal.ofReal |C1| * ENNReal.ofReal |C2| * (ENNReal.ofReal |C0| * La) :=
    ⟨_, rfl⟩
  have hc : c ≠ ⊤ := by
    rw [hcdef]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLa.ne)
  have hgpos : ∀ x : Mx k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → 0 < B.gN x :=
    fun x hx => lt_of_lt_of_le one_pos ((hNI k r).2 x hx).2
  have hpt : ∀ᵐ x ∂D.μG, Aext e1 x * ∫⁻ y, Aext e2 y * LL x y ∂D.μG ≤ ∫⁻ y, c * (Fx x * Fx y) ∂D.μG := by
    filter_upwards [hGc] with x hx
    rw [← lintegral_const_mul' (Aext e1 x) _ (by unfold Aext; exact enorm_ne_top)]
    apply lintegral_mono_ae
    filter_upwards [hGc] with y hy
    have hL := lam_bound hNI hb0e hb0.le hba hγU hpUH hqUH hx hy
    rw [← hLL, ← hLadef] at hL
    have hx0 := hgpos _ hx
    have hy0 := hgpos _ hy
    have w1 := e_weight (b := bb) hb1 hx hx0
    have w2 := e_weight (b := bb) hb2 hy hy0
    have split : ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ bb) =
        ENNReal.ofReal |C0| * (ENNReal.ofReal (B.gN (Matrix.of x) ^ bb) * ENNReal.ofReal (B.gN (Matrix.of y) ^ bb)) := by
      rw [Real.mul_rpow hx0.le hy0.le, ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg hx0.le _)]
    have hFxx : Fx x = ‖B.gN (Matrix.of x) ^ (-(aOf r h - bb))‖ₑ := by rw [hFx]
    have hFxy : Fx y = ‖B.gN (Matrix.of y) ^ (-(aOf r h - bb))‖ₑ := by rw [hFx]
    calc Aext e1 x * (Aext e2 y * LL x y)
        ≤ Aext e1 x * (Aext e2 y * (ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ bb) * La)) := by
          gcongr
      _ = (Aext e1 x * ENNReal.ofReal (B.gN (Matrix.of x) ^ bb)) *
            (Aext e2 y * ENNReal.ofReal (B.gN (Matrix.of y) ^ bb)) * (ENNReal.ofReal |C0| * La) := by
          rw [split]; ring
      _ ≤ (ENNReal.ofReal |C1| * Fx x) * (ENNReal.ofReal |C2| * Fx y) * (ENNReal.ofReal |C0| * La) := by
          rw [hFxx, hFxy]
          exact mul_le_mul' (mul_le_mul' w1 w2) le_rfl
      _ = c * (Fx x * Fx y) := by rw [hcdef]; ring
  calc _ ≤ ∫⁻ zz, ∫⁻ zz', (K1 * K2) * (Iint (Aext e1) (D.μW.prod D.μN) zz *
          (Iint (Aext e2) (D.μW'.prod D.μN) zz' * LL zz zz')) ∂νq' ∂νq :=
        lintegral_mono_ae (step1.mono fun zz h => lintegral_mono_ae h)
    _ = (K1 * K2) * ∫⁻ zz, Iint (Aext e1) (D.μW.prod D.μN) zz *
          ∫⁻ zz', Iint (Aext e2) (D.μW'.prod D.μN) zz' * LL zz zz' ∂νq' ∂νq :=
        pull2 _ _ _ hK (fun zz => hI2m.mul (hLz zz))
    _ = (K1 * K2) * ∫⁻ zz, Iint (Aext e1) (D.μW.prod D.μN) zz * ∫⁻ y, Aext e2 y * LL zz y ∂D.μG ∂νq := by
        congr 1; apply lintegral_congr; intro zz; congr 1
        exact unfold_Iint hq' hA2m (hLz zz) (hinvR zz)
    _ = (K1 * K2) * ∫⁻ x, Aext e1 x * ∫⁻ y, Aext e2 y * LL x y ∂D.μG ∂D.μG := by
        congr 1
        exact unfold_Iint hq hA1m hΦm hinvL
    _ ≤ (K1 * K2) * ∫⁻ x, ∫⁻ y, c * (Fx x * Fx y) ∂D.μG ∂D.μG := by
        gcongr 1
        exact lintegral_mono_ae hpt
    _ = (K1 * K2) * (c * ((∫⁻ x, Fx x ∂D.μG) * ∫⁻ y, Fx y ∂D.μG)) := by rw [final2 Fx hFxm hc]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK)
          (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) (ENNReal.mul_lt_top hKg' hKg'))

end G

end Formalism.FourierDecayAlt.P.S3dx4

end
