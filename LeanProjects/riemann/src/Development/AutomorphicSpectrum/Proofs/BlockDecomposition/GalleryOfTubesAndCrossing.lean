import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAffLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChamberPairThreeFour
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StripEntireOfFac

noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisGal

section Help

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W]
  [NormedSpace ℂ W]

lemma LeftGood_mono {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {f : ℂ → X} {a a' : ℝ}
    (hf : LeftGood f a) (h : a' ≤ a) : LeftGood f a' :=
  ⟨hf.1.mono fun _ hz => lt_of_lt_of_le hz h, fun b c hc => hf.2 b c (lt_of_lt_of_le hc h)⟩

lemma IsHt_restrict {Γ K P Q : Subgroup G} {η : G → ℝ} (h : IsHt Γ K Q η) (hPQ : P ≤ Q) :
    IsHt Γ K P η :=
  ⟨fun p hp g => h.left p (hPQ hp) g, h.right, fun γ hγ hp => h.rat γ hγ (hPQ hp), h.cont⟩

lemma IsHt_lin {Γ K P : Subgroup G} {η₁ η₂ η : G → ℝ} (h₁ : IsHt Γ K P η₁) (h₂ : IsHt Γ K P η₂)
    (s t : ℝ) (e : ∀ g, η g = s * η₁ g + t * η₂ g) : IsHt Γ K P η := by
  have he : η = fun g => s * η₁ g + t * η₂ g := funext e
  subst he
  refine ⟨fun p hp g => ?_, fun g k hk => ?_, fun γ hγ hp => ?_, ?_⟩
  · simp only [h₁.left p hp g, h₂.left p hp g]; ring
  · simp only [h₁.right g k hk, h₂.right g k hk]
  · simp only [h₁.rat γ hγ hp, h₂.rat γ hγ hp]; ring
  · have c₁ := h₁.cont
    have c₂ := h₂.cont
    fun_prop

lemma eis_congr {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {Λ Λ' : G → ℂ} {s s' : ℂ}
    (g : G) (w : W) (hs : s = s') (e : ∀ x, Λ x = Λ' x) :
    s • eis Γ K P c ρ Λ g w = s' • eis Γ K P c ρ Λ' g w := by
  have he : Λ = Λ' := funext e
  rw [hs, he]

variable [CompleteSpace W]

lemma series_first {Γ K S : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {h : G → ℝ}
    {H : ℂ → G → (secSp K S c ρ) →L[ℂ] W} {a₀ : ℂ}
    (hH : ∀ g (w : secSp K S c ρ), H 0 g w = a₀ • sec K S c ρ g w) (z : ℂ) (g : G)
    (hs : Summable fun r : Cos (Γ ⊓ S) Γ =>
      ‖Complex.exp (z * h (rep r * g)) • H 0 (rep r * g)‖) (w : secSp K S c ρ) :
    outer Γ (Γ ⊓ S) h H (0, z) g w = a₀ • eis Γ K S c ρ (fun x => z * h x) g w := by
  rw [outer_apply h H (0, z) g hs w]
  simp only [hH]
  rw [tsum_cos_inf Γ S fun u => Complex.exp (z * h (u * g)) • a₀ • sec K S c ρ (u * g) w]
  simp only [eis]
  rw [← tsum_const_smul'' a₀]
  congr 1
  ext q
  rw [smul_comm]

lemma series_last {Γ K S : Subgroup G} {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]
    {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {h : G → ℝ}
    {H : ℂ → G → L →L[ℂ] W} {N : ℂ} {T : L →L[ℂ] secSp K S c ρ}
    (hT : ∀ g w, H N g w = Complex.exp (h g) • sec K S c ρ g (T w)) (u : ℂ) (g : G)
    (hs : Summable fun r : Cos (Γ ⊓ S) Γ =>
      ‖Complex.exp (u * h (rep r * g)) • H N (rep r * g)‖) (w : L) :
    outer Γ (Γ ⊓ S) h H (N, u) g w = eis Γ K S c ρ (fun x => h x + u * h x) g (T w) := by
  rw [outer_apply h H (N, u) g hs w]
  simp only [hT]
  rw [tsum_cos_inf Γ S fun v => Complex.exp (u * h (v * g)) •
    Complex.exp (h (v * g)) • sec K S c ρ (v * g) (T w)]
  simp only [eis]
  congr 1
  ext q
  rw [smul_smul, ← Complex.exp_add, add_comm]

end Help

section Re

variable (N : ℝ) (l : ℂ × ℂ)

lemma mc_re₁ : (mc N l).1.re = l.1.re + l.2.re + 1 - N := by
  simp [chg, aff]; ring
lemma mc_re₂ : (mc N l).2.re = l.2.re + 1 := by simp [chg, aff]
lemma ma_re₁ : (ma N l).1.re = l.1.re + 2 * l.2.re + 1 - N := by
  simp [chg, aff]; ring
lemma ma_re₂ : (ma N l).2.re = l.2.re + 1 := by simp [chg, aff]
lemma mb_fst : (mb N l).1 = l.2 := by simp [chg, aff]
lemma mb_re₂ : (mb N l).2.re = 2 * N - 1 - l.1.re - l.2.re := by
  simp [chg, aff]; ring
lemma ml_fst : (ml N l).1 = nz N l := rfl
lemma nz_eq : nz N l = N - l.1 := by simp [aff]; ring
lemma ml_re₁ : (ml N l).1.re = N - l.1.re := by simp [chg, aff]; ring
lemma ml_re₂ : (ml N l).2.re = N - 1 - l.2.re := by simp [chg, aff]; ring

end Re

lemma isOpen_coneC (r : ℝ) : IsOpen (coneC r) :=
  (open_convex2 (-1) 1 0 1 1 0 r fun x => by
    simp only [coneC, affR, Set.mem_setOf_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith).1

lemma isOpen_coneA (r : ℝ) : IsOpen (coneA r) :=
  (open_convex2 (-1) 1 0 0 1 0 r fun x => by
    simp only [coneA, affR, Set.mem_setOf_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith).1

lemma tube_coneI_iff {r : ℝ} {m : ℂ × ℂ} : m ∈ tube (coneI r) ↔ r < m.2.re ∧ r < m.2.re + m.1.re :=
  Iff.rfl

lemma tube_coneC_iff {r : ℝ} {m : ℂ × ℂ} :
    m ∈ tube (coneC r) ↔ r < m.2.re - m.1.re ∧ r < m.2.re + m.1.re := Iff.rfl

lemma tube_coneA_iff {r : ℝ} {m : ℂ × ℂ} : m ∈ tube (coneA r) ↔ r < m.2.re - m.1.re ∧ r < m.2.re :=
  Iff.rfl

theorem gallery : SecLaw → IdTube → TubeChain → Cross → Gallery := by
  intro _ hId hTC hCross G _ _ _ _ _ W _ _ _ K ρ hK hρ hFC Γ S A B Q₁ Q₂ c h a b N hAS hBS hAQ hBQ
    pS pA pB hS hQa hQb hconv hFirst hWc hWa hWb hLast
  haveI := hFC
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨Rv, cS, cA, cB⟩ := hconv
  obtain ⟨R₀, D₀, Op₀, H₀, W₀, ⟨a₀, ha₀, hH₀⟩, O, hO, hOp⟩ := hFirst
  obtain ⟨Rc, Dc, Opc, Hc, Wc⟩ := hWc
  obtain ⟨Ra, Da, Opa, Ha, Wa⟩ := hWa
  obtain ⟨Rb, Db, Opb, Hb, Wb⟩ := hWb
  obtain ⟨Rl, Dl, Opl, Hl, Wl, ⟨d, hd, hdN, hDl⟩, T, hT⟩ := hLast
  have p₀ := W₀.pos
  have pc := Wc.pos
  have pa := Wa.pos
  have pb := Wb.pos
  have pl := Wl.pos
  obtain ⟨R, hRdef⟩ : ∃ R, R = |Rv| + R₀ + Rc + Ra + Rb + Rl + |N| + 1 := ⟨_, rfl⟩
  have hv₁ := abs_nonneg Rv
  have hv₂ := le_abs_self Rv
  have hv₃ := abs_nonneg N
  have hN : |N| + 1 ≤ R := by linarith
  have hRv : Rv ≤ R := by linarith
  have h₀ : R₀ ≤ R := by linarith
  have hc : Rc ≤ R := by linarith
  have ha : Ra ≤ R := by linarith
  have hb : Rb ≤ R := by linarith
  have hl : Rl ≤ R := by linarith
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hN₁ := hN'.1
  have hN₂ := hN'.2
  have hR1 : 1 ≤ R := by linarith
  have hAa := IsHt_restrict hQa hAQ
  have hAh := IsHt_restrict hS hAS
  have hBhb := IsHt_restrict hQb hBQ
  have hBh := IsHt_restrict hS hBS
  have hBb : IsHt Γ K B b := IsHt_lin hBhb hBh 1 (-1) fun g => by ring
  have hBβ : IsHt Γ K B fun g => h g + N * b g := IsHt_lin hBh hBb 1 N fun g => by ring
  have hBn : IsHt Γ K B fun g => -b g := IsHt_lin hBb hBb (-1) 0 fun g => by ring
  have hAβ : IsHt Γ K A fun g => N * a g - h g := IsHt_lin hAa hAh N (-1) fun g => by ring
  have hAd : IsHt Γ K A fun g => h g - a g := IsHt_lin hAh hAa 1 (-1) fun g => by ring
  have hAe : IsHt Γ K A fun g => (N - 1) * (h g - a g) := IsHt_lin hAd hAd (N - 1) 0 fun g => by ring
  have cA' : ∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g :=
    fun z y h₁ h₂ => cA z y (by linarith) (by linarith)
  have cB' : ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g :=
    fun z y h₁ h₂ => cB z y (by linarith) (by linarith)
  obtain ⟨g₀, s₀, -, l₀⟩ := hCross G W K ρ hK hρ Γ S A B c a b (fun g => h g + N * b g) h _ R₀ D₀ Op₀ H₀
    (coneI (10 * R)) hAS hBS pA pB hAa hBb hBβ hS W₀ (oc_coneI _).1 (cond_first hN h₀ cA' cB')
  obtain ⟨gc, -, rc, lc⟩ := hCross G W K ρ hK hρ Γ Q₂ B B c (fun g => -b g) (fun g => -b g)
    (fun g => -b g) (fun g => h g + b g) _ Rc Dc Opc Hc (coneC (10 * R)) hBQ hBQ pB pB hBn hBn hBn hQb
    Wc (isOpen_coneC _) (cond_c hN hc cB')
  obtain ⟨ga, -, ra, la⟩ := hCross G W K ρ hK hρ Γ S B A c b a (fun g => N * a g - h g) h _ Ra Da Opa Ha
    (coneA (10 * R)) hBS hAS pB pA hBb hAa hAβ hS Wa (isOpen_coneA _) (cond_a hN ha cA' cB')
  obtain ⟨gb, -, rb, lb⟩ := hCross G W K ρ hK hρ Γ Q₁ A A c (fun g => h g - a g) (fun g => h g - a g)
    (fun g => (N - 1) * (h g - a g)) a _ Rb Db Opb Hb (coneC (10 * R)) hAQ hAQ pA pA hAd hAd hAe hQa
    Wb (isOpen_coneC _) (cond_b hN hb cA')
  obtain ⟨gl, sl, rl, -⟩ := hCross G W K ρ hK hρ Γ S A B c a b (fun g => h g + N * b g) h _ Rl Dl Opl Hl
    (coneI (10 * R)) hAS hBS pA pB hAa hBb hBβ hS Wl (oc_coneI _).1 (cond_first hN hl cA' cB')
  have J₀ : ∀ l ∈ tube (chamberPairOneTwo (100 * R)), ∀ g, Dc (yv N l) • outer Γ (Γ ⊓ S) h H₀ l g =
      (outer Γ (Γ ⊓ Q₂) (fun g => h g + b g) Hc (mc N l) g).comp (Op₀ l.1) := by
    intro l hl g
    have hl' : l.1.re < -(100 * R) ∧ 100 * R < l.1.re + l.2.re := hl
    obtain ⟨x₁, x₂⟩ := hl'
    have t₁ : l ∈ tube (coneI (10 * R)) := tube_coneI_iff.2 ⟨by linarith, by linarith⟩
    have t₂ : mc N l ∈ tube (coneC (10 * R)) := tube_coneC_iff.2 (by
      rw [mc_re₁, mc_re₂]; constructor <;> linarith)
    have cv := cB' (N - l.1.re) (l.1.re + l.2.re + 1 - N) (by linarith) (by linarith)
    have e₁ := l₀ l t₁ (by linarith) (conv_congr cv fun x => by ring) g
    have e₂ := rc (mc N l) t₂ (by rw [mc_re₁]; linarith)
      (conv_congr cv fun x => by rw [mc_re₁, mc_re₂]; ring) g
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    rw [e₁, e₂]
    exact eis_congr g _ rfl fun x => by simp only [chg, aff]; push_cast; ring
  have J₁ : ∀ l ∈ tube (chamberPairTwoThree (100 * R)), ∀ g,
      Da (zv N l) • outer Γ (Γ ⊓ Q₂) (fun g => h g + b g) Hc (mc N l) g =
        (outer Γ (Γ ⊓ S) h Ha (ma N l) g).comp (Opc (yv N l)) := by
    intro l hl g
    have hl' : l.1.re + l.2.re < -(100 * R) ∧ 100 * R < l.1.re + 2 * l.2.re := hl
    obtain ⟨x₁, x₂⟩ := hl'
    have t₁ : mc N l ∈ tube (coneC (10 * R)) := tube_coneC_iff.2 (by
      rw [mc_re₁, mc_re₂]; constructor <;> linarith)
    have t₂ : ma N l ∈ tube (coneA (10 * R)) := tube_coneA_iff.2 (by
      rw [ma_re₁, ma_re₂]; constructor <;> linarith)
    have cv := cB' (l.1.re + 2 * l.2.re + 1 - N) (N - l.1.re - l.2.re) (by linarith) (by linarith)
    have e₁ := lc (mc N l) t₁ (by rw [mc_re₁]; linarith)
      (conv_congr cv fun x => by rw [mc_re₁, mc_re₂]; ring) g
    have e₂ := ra (ma N l) t₂ (by rw [ma_re₁]; linarith)
      (conv_congr cv fun x => by rw [ma_re₁, ma_re₂]; ring) g
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    rw [e₁, e₂]
    exact eis_congr g _ rfl fun x => by simp only [chg, aff]; push_cast; ring
  have J₂ : ∀ l ∈ tube (chamberPairThreeFour (100 * R)), ∀ g, Db l.2 • outer Γ (Γ ⊓ S) h Ha (ma N l) g =
      (outer Γ (Γ ⊓ Q₁) a Hb (mb N l) g).comp (Opa (zv N l)) := by
    intro l hl g
    have hl' : l.1.re + 2 * l.2.re < -(100 * R) ∧ 100 * R < l.2.re := hl
    obtain ⟨x₁, x₂⟩ := hl'
    have t₁ : ma N l ∈ tube (coneA (10 * R)) := tube_coneA_iff.2 (by
      rw [ma_re₁, ma_re₂]; constructor <;> linarith)
    have t₂ : mb N l ∈ tube (coneC (10 * R)) := tube_coneC_iff.2 (by
      rw [mb_fst, mb_re₂]; constructor <;> linarith)
    have cv := cA' (N - (l.1.re + 2 * l.2.re + 1 - N)) l.2.re (by linarith) (by linarith)
    have e₁ := la (ma N l) t₁ (by rw [ma_re₁]; linarith)
      (conv_congr cv fun x => by rw [ma_re₁, ma_re₂]; ring) g
    have e₂ := rb (mb N l) t₂ (by rw [mb_fst]; linarith)
      (conv_congr cv fun x => by rw [mb_fst, mb_re₂]; ring) g
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    rw [e₁, e₂]
    exact eis_congr g _ (by rw [mb_fst]) fun x => by simp only [chg, aff]; push_cast; ring
  have J₃ : ∀ l ∈ tube (chamberPairFourLast (100 * R)), ∀ g,
      (-d (nz N l)) • (outer Γ (Γ ⊓ Q₁) a Hb (mb N l) g).comp
        ((Opa (zv N l)).comp ((Opc (yv N l)).comp (Op₀ l.1))) =
      (outer Γ (Γ ⊓ S) h Hl (ml N l) g).comp
        ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1)))) := by
    intro l hl g
    have hl' : l.2.re < -(100 * R) ∧ l.1.re < -(100 * R) := hl
    obtain ⟨x₁, x₂⟩ := hl'
    have t₁ : mb N l ∈ tube (coneC (10 * R)) := tube_coneC_iff.2 (by
      rw [mb_fst, mb_re₂]; constructor <;> linarith)
    have t₂ : ml N l ∈ tube (coneI (10 * R)) := tube_coneI_iff.2 (by
      rw [ml_re₁, ml_re₂]; constructor <;> linarith)
    have cv := cA' (N - l.1.re) (N - 1 - l.2.re) (by linarith) (by linarith)
    have hz := hOp l.1 (by linarith)
    have e₁ := lb (mb N l) t₁ (by rw [mb_fst]; linarith)
      (conv_congr cv fun x => by rw [mb_fst, mb_re₂]; ring) g
    have e₂ := rl (ml N l) t₂ (by rw [ml_re₁]; linarith)
      (conv_congr cv fun x => by rw [ml_re₁, ml_re₂]) g
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    rw [hz]
    simp only [ContinuousLinearMap.smul_apply, map_smul]
    rw [e₁, e₂, mb_fst, smul_smul, hDl]
    exact eis_congr g _ (by rw [ml_fst, nz_eq]; push_cast; ring)
      fun x => by simp only [chg, aff]; push_cast; ring
  obtain ⟨Φ, hΦ, eR, eL⟩ := core hId hTC N R hN g₀ gc ga gb gl Wc.dEnt Wa.dEnt Wb.dEnt hd
    (LeftGood_mono W₀.op (by linarith)) hO (LeftGood_mono Wc.op (by linarith))
    (LeftGood_mono Wa.op (by linarith)) (LeftGood_mono Wb.op (by linarith)) J₀ J₁ J₂ J₃
  have hdN' : d N ≠ 0 := hdN
  have hsl := slice_good hΦ
  have hOpa' : LeftGood Opa (-R) := LeftGood_mono Wa.op (by linarith)
  have hOpb' : LeftGood Opb (-R) := LeftGood_mono Wb.op (by linarith)
  have hOpc' : LeftGood Opc (-R) := LeftGood_mono Wc.op (by linarith)
  refine ⟨20 * R,
    fun y => Complex.exp ((0 : ℂ) ^ 2 + y ^ 2) * (Dc (yv N (0, y)) * Da (zv N (0, y)) * Db y) * a₀,
    fun y => (Complex.exp ((0 : ℂ) ^ 2 + y ^ 2) * (-(d N)⁻¹)) •
      T.comp ((Opb y).comp ((Opa (aff 0 2 (1 - N) (0, y))).comp
        ((Opc (aff 0 1 (1 - N) (0, y))).comp (O 0)))),
    fun y g => Φ (0, y) g, ?_⟩
  refine
    { le := le_rfl
      pos := by linarith
      convR := fun x hx => cS x (by linarith)
      convL := fun x hx => conv_congr (cS (N - x) (by linarith)) fun g => by ring
      dEnt := ?_
      dNe := ?_
      op := ?_
      hol := hsl.1
      cont := hsl.2.1
      bdd := hsl.2.2
      eqR := ?_
      eqL := ?_ }
  · exact stripEntire_of_fac (A := fun l => Complex.exp (l.1 ^ 2 + l.2 ^ 2) *
      (Dc (yv N l) * Da (zv N l) * Db l.2) * a₀)
      (Fac_mul (Fac_mul (Fac_exp _) (Fac_mul (Fac_mul (Fac_strip Wc.dEnt _ _ _ _)
        (Fac_strip Wa.dEnt _ _ _ _)) (Fac_strip_snd Wb.dEnt _))) (Fac_const _ _)) fun _ => rfl
  · have d₁ : Differentiable ℂ fun y : ℂ => Dc (yv N (0, y)) :=
      (stripEntire_of_fac (A := fun l => Dc (yv N l)) (Fac_strip Wc.dEnt _ _ _ _) fun _ => rfl).1
    have d₂ : Differentiable ℂ fun y : ℂ => Da (zv N (0, y)) :=
      (stripEntire_of_fac (A := fun l => Da (zv N l)) (Fac_strip Wa.dEnt _ _ _ _) fun _ => rfl).1
    obtain ⟨y₁, hy₁⟩ := exists_ne_mul d₁ d₂ (exists_ne_aff Wc.dNe 1 1 (1 - N) one_ne_zero)
      (exists_ne_aff Wa.dNe 1 2 (1 - N) two_ne_zero)
    obtain ⟨y, hy⟩ := exists_ne_mul (f := fun y : ℂ => Dc (yv N (0, y)) * Da (zv N (0, y)))
      (d₁.mul d₂) Wb.dEnt.1 ⟨y₁, hy₁⟩ Wb.dNe
    exact ⟨y, mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) hy) ha₀⟩
  · refine leftGood_of_fac (A := fun l => (Complex.exp (l.1 ^ 2 + l.2 ^ 2) * (-(d N)⁻¹)) •
      T.comp ((Opb l.2).comp ((Opa (aff 0 2 (1 - N) l)).comp
        ((Opc (aff 0 1 (1 - N) l)).comp (O 0))))) ?_ fun _ => rfl
    refine Fac_smul (Fac_mul (Fac_exp _) (Fac_const _ _)) (Fac_comp (Fac_const _ _) (Fac_comp
      (Fac_left_snd hOpb' fun x hx => ?_) (Fac_comp (Fac_left hOpa' _ _ _ fun x hx => ?_)
        (Fac_comp (Fac_left hOpc' _ _ _ fun x hx => ?_) (Fac_const _ _)))))
    · have : x.2 < -(20 * R) := hx
      linarith
    · have : x.2 < -(20 * R) := hx
      simp only [affR]; linarith
    · have : x.2 < -(20 * R) := hx
      simp only [affR]; linarith
  · intro z hz g w
    have hm : ((0 : ℂ), z) ∈ tube (coneI (10 * R)) :=
      tube_coneI_iff.2 (by simp only [Complex.zero_re, add_zero]; constructor <;> linarith)
    have e₂ := series_first hH₀ z g (s₀ (0, z) hm g) w
    change Φ (0, z) g w = _
    rw [eR (0, z) hm g]
    simp only [ContinuousLinearMap.smul_apply]
    rw [e₂]
    simp only [smul_smul]
    congr 1
    ring
  · intro y hy g w
    have hm : ((0 : ℂ), y) ∈ tube (Om4 N (10 * R)) := by
      refine mem_Om4.2 ⟨⟨?_, ?_⟩, ?_⟩
      · show 10 * R < N - 1 - y.re
        linarith
      · show 10 * R < 2 * N - 1 - y.re - (0 : ℂ).re
        simp only [Complex.zero_re]; linarith
      · show (0 : ℂ).re < 1 / 2
        simp
    have e := eL (0, y) hm g
    have ez : nz N ((0 : ℂ), y) = N := by simp [aff]
    have ez₁ : zv N ((0 : ℂ), y) = aff 0 2 (1 - N) (0, y) := by simp [aff]
    have ez₂ : yv N ((0 : ℂ), y) = aff 0 1 (1 - N) (0, y) := by simp [aff]
    obtain ⟨u, hu, hu'⟩ : ∃ u : ℂ, ml N ((0 : ℂ), y) = ((N : ℂ), u) ∧ u = N - 1 - y :=
      ⟨_, Prod.ext (by simp [chg, aff]) rfl, by simp [chg, aff]; ring⟩
    have hm₂ : ml N ((0 : ℂ), y) ∈ tube (coneI (10 * R)) := tube_coneI_iff.2 (by
      rw [ml_re₁, ml_re₂]
      simp only [Complex.zero_re]
      constructor <;> linarith)
    have hs := sl _ hm₂ g
    rw [hu] at hs e
    rw [ez, ez₁, ez₂] at e
    set w' := (Opb y) ((Opa (aff 0 2 (1 - N) (0, y))) ((Opc (aff 0 1 (1 - N) (0, y))) (O 0 w)))
      with hw'
    have e' := DFunLike.congr_fun e w
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply] at e'
    rw [series_last hT u g hs w'] at e'
    have hinv : (Φ (0, y) g) w = (-(d N))⁻¹ • ((-d N) • (Φ (0, y) g) w) := by
      rw [smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 hdN'), one_smul]
    change (Φ (0, y) g) w = eis Γ K S c ρ (fun x => (N * h x : ℝ) - y * h x) g
      (((Complex.exp ((0 : ℂ) ^ 2 + y ^ 2) * (-(d N)⁻¹)) • T w' : secSp K S c ρ) : W)
    rw [hinv, e', Submodule.coe_smul, eis_smul, smul_smul]
    refine eis_congr g _ ?_ fun x => ?_
    · field_simp
    · rw [hu']; push_cast; ring

end GlobalTheory.CompanionTheory.RgEisGal
