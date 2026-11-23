import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.CmpOfMemX
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeMembershipPolynomialGamma
import Formalism.SharpRestriction.LevelLetterCocycles.KillerLevCoreOf

set_option linter.unusedVariables false

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Polynomial

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def LemGPair [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (b : ZMod n → ℕ)
    (S η : ℕ) (i : ZMod n) (x la : W.DD T) : Prop :=
  x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x ∧
    Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la ∧
    ∃ z ∈ W.N T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z ∧
      Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • (W.γ T la - la) =
        (W.π₀ * Formalism.MainNotions.LiftingTheory.qp W ^ (⌈aR PD.p (hpar n b S + η)⌉₊ + b i)) • z

def WachGammaDerivation [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (dop : W.DD T₂ →ₗ[O] W.DD T₂), (∀ z, W.π₀ • dop z = W.γ T₂ z - z) →
    ∀ (cc : ℤ → O),
      (∀ x : ℤ, (-((PD.p : ℕ) : O)) * cc x = (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) - 1) →
    ∀ x la : W.DD T₂, LemGPair W T₂ b S η i x la →
      ∃ w, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i w ∧
        aeval dop (∏ j ∈ Finset.Icc ((b i : ℤ) - ⌈aR PD.p (hpar n b S + η)⌉₊ + 1) (b i : ℤ),
          (X - C (cc j))) x = Formalism.MainNotions.LiftingTheory.qp W ^ ⌈aR PD.p (hpar n b S + η)⌉₊ • w

section Res

variable (W : LocWach PD LL O v n)
  (hAq : ∀ (i : ZMod n) (g : LetA O n), g ∈ W.AΔ → (letE i : LetA O n) * g = g →
    ∃ (o : O) (g' : LetA O n), g' ∈ W.AΔ ∧
      g = algebraMap O (LetA O n) o * letE i + Formalism.MainNotions.LiftingTheory.qp W * g')
  (hqc : ∀ (i : ZMod n) (o : O) (g : LetA O n), g ∈ W.AΔ → (letE i : LetA O n) * g = g →
    algebraMap O (LetA O n) o * letE i = Formalism.MainNotions.LiftingTheory.qp W * g → o = 0)

theorem letE_mem_AΔ (i : ZMod n) : (letE i : LetA O n) ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W i

theorem letE_idem (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := Formalism.MainNotions.LiftingTheory.frame_letE_idem i

theorem letE_mul_mem {i : ZMod n} {g : LetA O n} (hg : g ∈ W.AΔ) : (letE i : LetA O n) * g ∈ W.AΔ := W.AΔ.mul_mem (letE_mem_AΔ W i) hg

include hAq in

def resq (i : ZMod n) (g : LetA O n) : O :=
  if h : g ∈ W.AΔ then
    Classical.choose (hAq i ((letE i : LetA O n) * g) (letE_mul_mem W h)
      (by rw [← mul_assoc, letE_idem]))
  else 0

include hAq in
theorem resq_spec (i : ZMod n) {g : LetA O n} (hg : g ∈ W.AΔ) :
    ∃ g' ∈ W.AΔ, (letE i : LetA O n) * g =
      algebraMap O (LetA O n) (resq W hAq i g) * letE i + Formalism.MainNotions.LiftingTheory.qp W * g' := by
  obtain ⟨g', hg', he⟩ := Classical.choose_spec (hAq i ((letE i : LetA O n) * g) (letE_mul_mem W hg)
    (by rw [← mul_assoc, letE_idem]))
  refine ⟨g', hg', ?_⟩
  unfold resq
  rw [dif_pos hg]
  exact he

include hAq hqc in
theorem resq_eq (i : ZMod n) {g : LetA O n} (hg : g ∈ W.AΔ) {o : O} {g' : LetA O n} (hg' : g' ∈ W.AΔ)
    (he : (letE i : LetA O n) * g = algebraMap O (LetA O n) o * letE i + Formalism.MainNotions.LiftingTheory.qp W * g') :
    resq W hAq i g = o := by
  obtain ⟨g₁, hg₁, he₁⟩ := resq_spec W hAq i hg
  set e : LetA O n := letE i with he_def
  set r := resq W hAq i g with hr_def
  have hE : e * e = e := letE_idem i
  have key : algebraMap O (LetA O n) (r - o) * e = Formalism.MainNotions.LiftingTheory.qp W * (g' - g₁) := by
    rw [map_sub]
    linear_combination he₁.symm.trans he
  have hmem : e * (g' - g₁) ∈ W.AΔ := letE_mul_mem W (W.AΔ.sub_mem hg' hg₁)
  have hfix : e * (e * (g' - g₁)) = e * (g' - g₁) := by rw [← mul_assoc, hE]
  have heq : algebraMap O (LetA O n) (r - o) * e = Formalism.MainNotions.LiftingTheory.qp W * (e * (g' - g₁)) := by
    linear_combination e * key - algebraMap O (LetA O n) (r - o) * hE
  exact sub_eq_zero.mp (hqc i (r - o) _ hmem hfix heq)

theorem qp_mem_AΔ' (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := by
  unfold Formalism.MainNotions.LiftingTheory.qp
  exact W.AΔ.add_mem (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) (W.AΔ.natCast_mem _)

include hqc in
theorem resq_alg (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (i : ZMod n) (o : O) :
    resq W hAq i (algebraMap O (LetA O n) o) = o := by
  refine resq_eq W hAq hqc i (W.AΔ.algebraMap_mem o) (W.AΔ.zero_mem) ?_
  rw [mul_zero, add_zero, mul_comm]

include hqc in
theorem resq_add (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (i : ZMod n) {g h : LetA O n} (hg : g ∈ W.AΔ)
    (hh : h ∈ W.AΔ) : resq W hAq i (g + h) = resq W hAq i g + resq W hAq i h := by
  obtain ⟨g₁, hg₁, e₁⟩ := resq_spec W hAq i hg
  obtain ⟨h₁, hh₁, e₂⟩ := resq_spec W hAq i hh
  refine resq_eq W hAq hqc i (W.AΔ.add_mem hg hh) (W.AΔ.add_mem hg₁ hh₁) ?_
  rw [mul_add, e₁, e₂, map_add]
  ring

include hqc in
theorem resq_mul (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (i : ZMod n) {g h : LetA O n} (hg : g ∈ W.AΔ)
    (hh : h ∈ W.AΔ) : resq W hAq i (g * h) = resq W hAq i g * resq W hAq i h := by
  obtain ⟨g₁, hg₁, e₁⟩ := resq_spec W hAq i hg
  obtain ⟨h₁, hh₁, e₂⟩ := resq_spec W hAq i hh
  have hE : (letE i : LetA O n) * letE i = letE i := letE_idem i
  have hq := qp_mem_AΔ' W hR
  have he := letE_mem_AΔ W i
  have ha := W.AΔ.algebraMap_mem (resq W hAq i g)
  have hb := W.AΔ.algebraMap_mem (resq W hAq i h)
  refine resq_eq W hAq hqc i (W.AΔ.mul_mem hg hh)
    (g' := algebraMap O (LetA O n) (resq W hAq i g) * letE i * h₁
      + g₁ * (algebraMap O (LetA O n) (resq W hAq i h) * letE i) + Formalism.MainNotions.LiftingTheory.qp W * g₁ * h₁)
    (W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.mul_mem ha he) hh₁)
      (W.AΔ.mul_mem hg₁ (W.AΔ.mul_mem hb he))) (W.AΔ.mul_mem (W.AΔ.mul_mem hq hg₁) hh₁)) ?_
  have h2 : (letE i : LetA O n) * (g * h) = ((letE i : LetA O n) * g) * ((letE i : LetA O n) * h) := by
    linear_combination (-(g * h)) * hE
  rw [h2, e₁, e₂, map_mul]
  linear_combination (algebraMap O (LetA O n) (resq W hAq i g) *
    algebraMap O (LetA O n) (resq W hAq i h)) * hE

include hqc in
theorem resq_qp_mul (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (i : ZMod n) {g : LetA O n} (hg : g ∈ W.AΔ) :
    resq W hAq i (Formalism.MainNotions.LiftingTheory.qp W * g) = 0 := by
  refine resq_eq W hAq hqc i (W.AΔ.mul_mem (qp_mem_AΔ' W hR) hg) (letE_mul_mem W (i := i) hg) ?_
  rw [map_zero, zero_mul, zero_add]
  ring

include hqc in
theorem residue_pi0_eq_neg_prime (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (i : ZMod n) :
    resq W hAq i W.π₀ = -((PD.p : ℕ) : O) := by
  refine resq_eq W hAq hqc i (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) (letE_mem_AΔ W i) ?_
  rw [map_neg, map_natCast]
  unfold Formalism.MainNotions.LiftingTheory.qp
  ring

include hAq in
theorem mem_of_resq_zero (i : ZMod n) {g : LetA O n} (hg : g ∈ W.AΔ) (h0 : resq W hAq i g = 0) :
    ∃ g' ∈ W.AΔ, (letE i : LetA O n) * g = Formalism.MainNotions.LiftingTheory.qp W * g' := by
  obtain ⟨g', hg', he⟩ := resq_spec W hAq i hg
  refine ⟨g', hg', ?_⟩
  rw [he, h0, map_zero, zero_mul, zero_add]

end Res

section StringRepresentationDecomposition

variable (W : LocWach PD LL O v n)

theorem dop_smulA (T : LocLat G Qp LL O) (hπU : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    (dop : W.DD T →ₗ[O] W.DD T) (hdop : ∀ z, W.π₀ • dop z = W.γ T z - z) {r r' : LetA O n}
    (hr : W.γA W.gam r - r = W.π₀ * r') (y : W.DD T) :
    dop (r • y) = W.γA W.gam r • dop y + r' • y := by
  have hγ : W.γ T (r • y) = W.γA W.gam r • W.γ T y := Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T W.gam r y
  apply (hπU.smul_left_cancel).mp
  rw [algebraMap_smul, algebraMap_smul, hdop, smul_add, smul_smul W.π₀ (W.γA W.gam r), mul_comm,
    ← smul_smul, hdop, smul_smul W.π₀ r', ← hr, hγ, smul_sub, sub_smul]
  abel

theorem one_add_pi0_mul_pow {t : LetA O n} (ht : t ∈ W.AΔ) (k : ℕ) :
    ∃ T ∈ W.AΔ, (1 + W.π₀ * t) ^ k = 1 + W.π₀ * T := by
  induction k with
  | zero => exact ⟨0, W.AΔ.zero_mem, by rw [pow_zero, mul_zero, add_zero]⟩
  | succ k ih =>
    obtain ⟨T, hT, hk⟩ := ih
    refine ⟨T + t + W.π₀ * T * t, W.AΔ.add_mem (W.AΔ.add_mem hT ht)
      (W.AΔ.mul_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) hT) ht), ?_⟩
    rw [pow_succ, hk]
    ring

end StringRepresentationDecomposition

section G56Main

variable (W : LocWach PD LL O v n)

theorem resq_pow (hAq : ∀ (i : ZMod n) (g : LetA O n), g ∈ W.AΔ → (letE i : LetA O n) * g = g →
      ∃ (o : O) (g' : LetA O n), g' ∈ W.AΔ ∧
        g = algebraMap O (LetA O n) o * letE i + Formalism.MainNotions.LiftingTheory.qp W * g')
    (hqc : ∀ (i : ZMod n) (o : O) (g : LetA O n), g ∈ W.AΔ → (letE i : LetA O n) * g = g →
      algebraMap O (LetA O n) o * letE i = Formalism.MainNotions.LiftingTheory.qp W * g → o = 0)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (i : ZMod n) {g : LetA O n} (hg : g ∈ W.AΔ) (k : ℕ) :
    resq W hAq i (g ^ k) = resq W hAq i g ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, ← map_one (algebraMap O (LetA O n))]
    exact resq_alg W hAq hqc hR i 1
  | succ k ih =>
    rw [pow_succ, pow_succ, resq_mul W hAq hqc hR i (W.AΔ.pow_mem hg k) hg, ih]

theorem gamma_structure_of [NeZero n] [IsDomain O] (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hπU : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    (hqU : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)))
    (hγg : ∀ g ∈ W.AΔ, ∃ g' ∈ W.AΔ, W.γA W.gam g - g = W.π₀ * Formalism.MainNotions.LiftingTheory.qp W * g')
    (hγq : ∃ r ∈ W.AΔ, W.γA W.gam (Formalism.MainNotions.LiftingTheory.qp W) =
      (algebraMap O (LetA O n) (W.χΓ W.gam : O) + Formalism.MainNotions.LiftingTheory.qp W * r) * Formalism.MainNotions.LiftingTheory.qp W)
    (hγp : ∃ r ∈ W.AΔ, W.γA W.gam (Formalism.MainNotions.LiftingTheory.pk W 1) =
      (1 + W.π₀ * Formalism.MainNotions.LiftingTheory.qp W * r) * Formalism.MainNotions.LiftingTheory.pk W 1)
    (hAq : ∀ (i : ZMod n) (g : LetA O n), g ∈ W.AΔ → (letE i : LetA O n) * g = g →
      ∃ (o : O) (g' : LetA O n), g' ∈ W.AΔ ∧
        g = algebraMap O (LetA O n) o * letE i + Formalism.MainNotions.LiftingTheory.qp W * g')
    (hqc : ∀ (i : ZMod n) (o : O) (g : LetA O n), g ∈ W.AΔ → (letE i : LetA O n) * g = g →
      algebraMap O (LetA O n) o * letE i = Formalism.MainNotions.LiftingTheory.qp W * g → o = 0) : WachGammaDerivation W := by
  intro d T₁ T₂ F b S η m hset i hi dop hdop cc hcc x la hP
  obtain ⟨hxN, hxD, hrel, z, hzN, hzD, hzrel⟩ := hP
  have hset' := hset
  obtain ⟨hCA, hl, hn, -, -, hSur, -, -, -, -⟩ := hset'
  obtain ⟨hbij, hs, hp2⟩ := hCA
  have hK1 : Module.finrank K₀ K = 1 := Formalism.MainNotions.UnusedSlot80.SatW.finrank_one_of_bij' hbij
  obtain ⟨-, -, h9₂⟩ := h9 T₂ hSur.2.1 hs hp2
  obtain ⟨hR, hmod₂⟩ := h9₂ hK1
  set qp := Formalism.MainNotions.LiftingTheory.qp W with hqpdef
  set a : ℕ := ⌈aR PD.p (hpar n b S + η)⌉₊ with ha
  set bb : ℕ := b i with hbb
  set hh : ℕ := b (i - 1) + S with hhh
  have hq : qp ∈ W.AΔ := qp_mem_AΔ' W hR
  have hπ : W.π₀ ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := p_ne_zero_O W
  have hqcan : ∀ u v : LetA O n, qp * u = qp * v → u = v := fun u v h => by
    apply W.EE_inj; apply hqU.mul_left_cancel; rw [← map_mul, ← map_mul, h]
  have hresq_sub : ∀ {g h : LetA O n}, g ∈ W.AΔ → h ∈ W.AΔ →
      resq W hAq i (g - h) = resq W hAq i g - resq W hAq i h := by
    intro g h hg hh'
    have := resq_add W hAq hqc hR i (W.AΔ.sub_mem hg hh') hh'
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  obtain ⟨rq, hrqΔ, hVq⟩ := hγq
  obtain ⟨rp, hrpΔ, hVp⟩ := hγp
  set χO : O := (W.χΓ W.gam : O) with hχO
  set Vq : LetA O n := algebraMap O (LetA O n) χO + qp * rq with hVqdef
  have hVqΔ : Vq ∈ W.AΔ := W.AΔ.add_mem (W.AΔ.algebraMap_mem _) (W.AΔ.mul_mem hq hrqΔ)
  obtain ⟨gq', hgq'Δ, hgq'⟩ := hγg qp hq
  have hVq1 : Vq = 1 + W.π₀ * gq' := by
    apply hqcan
    have e1 : W.γA W.gam qp = Vq * qp := hVq
    have e2 : W.γA W.gam qp = qp + W.π₀ * qp * gq' := by rw [← hgq']; ring
    calc qp * Vq = Vq * qp := mul_comm _ _
      _ = qp + W.π₀ * qp * gq' := by rw [← e1, e2]
      _ = qp * (1 + W.π₀ * gq') := by ring
  have hVqU : IsUnit Vq := by
    rw [hVq1, Pi.isUnit_iff]
    intro j
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp only [Pi.add_apply, Pi.mul_apply, Pi.one_apply, map_add, map_mul, map_one]
    rw [show W.π₀ j = W.π₀₁ from rfl, Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR, zero_mul, add_zero]
    exact isUnit_one
  obtain ⟨VqU, hVqU'⟩ := hVqU
  set Vqi : LetA O n := ((VqU⁻¹ : (LetA O n)ˣ) : LetA O n) with hVqi
  have hVqiVq : Vqi * Vq = 1 := by rw [hVqi, ← hVqU', Units.inv_mul]
  have hVqiΔ : Vqi ∈ W.AΔ := by
    intro δ hδ
    have h1 : W.γA δ Vqi * Vq = 1 := by
      rw [← hVqΔ δ hδ, ← map_mul, hVqiVq, map_one]
    calc W.γA δ Vqi = W.γA δ Vqi * (Vq * Vqi) := by rw [mul_comm Vq, hVqiVq, mul_one]
      _ = Vqi := by rw [← mul_assoc, h1, one_mul]
  set Vp : LetA O n := 1 + W.π₀ * qp * rp with hVpdef
  have hVpΔ : Vp ∈ W.AΔ := W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hπ hq) hrpΔ)

  have e3 : Formalism.MainNotions.LiftingTheory.pk W 1 ^ hh • W.γ T₂ la = qp ^ bb • (x + (W.π₀ * qp ^ a) • z) := by
    have : Formalism.MainNotions.LiftingTheory.pk W 1 ^ hh • W.γ T₂ la = Formalism.MainNotions.LiftingTheory.pk W 1 ^ hh • la +
        Formalism.MainNotions.LiftingTheory.pk W 1 ^ hh • (W.γ T₂ la - la) := by rw [← smul_add]; congr 1; abel
    rw [this, ← hrel, hzrel, smul_add, smul_smul, pow_add]
    congr 2
    ring
  have hE1 : Vq ^ bb • W.γ T₂ x = Vp ^ hh • (x + (W.π₀ * qp ^ a) • z) := by
    have h1 := congrArg (W.γ T₂) hrel
    have eL : W.γ T₂ (qp ^ bb • x) = qp ^ bb • (Vq ^ bb • W.γ T₂ x) := by
      show W.γD T₂ W.gam (qp ^ bb • x) = _
      rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', map_pow, hVq, mul_pow, mul_comm, mul_smul]
      rfl
    have eR : W.γ T₂ (Formalism.MainNotions.LiftingTheory.pk W 1 ^ hh • la) =
        qp ^ bb • (Vp ^ hh • (x + (W.π₀ * qp ^ a) • z)) := by
      show W.γD T₂ W.gam (Formalism.MainNotions.LiftingTheory.pk W 1 ^ hh • la) = _
      rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', map_pow, hVp, mul_pow, mul_smul]
      show Vp ^ hh • (Formalism.MainNotions.LiftingTheory.pk W 1 ^ hh • W.γ T₂ la) = _
      rw [e3, smul_comm]
    rw [eL, eR] at h1
    have hU' : IsUnit (algebraMap (LetA O n) W.EE (qp ^ bb)) := by rw [map_pow]; exact hqU.pow bb
    exact Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T₂ hU' h1
  have hγx : W.γ T₂ x = x + W.π₀ • dop x := by rw [hdop]; abel
  obtain ⟨A1, hA1Δ, orbitMap_conj_smul_one⟩ := one_add_pi0_mul_pow W (W.AΔ.mul_mem hq hrpΔ) hh
  obtain ⟨A2, hA2Δ, orbitMap_conj_smul_two⟩ := one_add_pi0_mul_pow W hgq'Δ bb
  have hVp_pow : Vp ^ hh = 1 + W.π₀ * A1 := by
    rw [← orbitMap_conj_smul_one, hVpdef]; ring
  have hVq_pow : Vq ^ bb = 1 + W.π₀ * A2 := by rw [hVq1, orbitMap_conj_smul_two]
  set D : LetA O n := A1 - A2 with hD
  have hπD : W.π₀ * D = Vp ^ hh - Vq ^ bb := by rw [hVp_pow, hVq_pow, hD]; ring
  have hdx0 : W.π₀ • (Vq ^ bb • dop x) = W.π₀ • (D • x + (Vp ^ hh * qp ^ a) • z) := by
    have h := hE1
    rw [hγx, smul_add, smul_comm (Vq ^ bb) W.π₀] at h
    have h2 : W.π₀ • (Vq ^ bb • dop x) = Vp ^ hh • (x + (W.π₀ * qp ^ a) • z) - Vq ^ bb • x := by
      rw [← h]; abel
    have hs : Vp ^ hh * (W.π₀ * qp ^ a) = W.π₀ * (Vp ^ hh * qp ^ a) := by ring
    rw [h2]
    simp only [smul_add, smul_smul, hs, hπD, sub_smul]
    abel
  have hdx1 : Vq ^ bb • dop x = D • x + (Vp ^ hh * qp ^ a) • z :=
    Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T₂ hπU hdx0
  have hdx : dop x = (Vqi ^ bb * D) • x + (Vqi ^ bb * Vp ^ hh * qp ^ a) • z := by
    have h := congrArg (fun y => Vqi ^ bb • y) hdx1
    rw [smul_smul, ← mul_pow, hVqiVq, one_pow, one_smul] at h
    rw [h, smul_add, smul_smul, smul_smul, mul_assoc]
  set e₁ : LetA O n := Vqi ^ bb * D with he₁
  have he₁Δ : e₁ ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem hVqiΔ _) (W.AΔ.sub_mem hA1Δ hA2Δ)

  have hresVq : resq W hAq i Vq = χO :=
    resq_eq W hAq hqc i hVqΔ (letE_mul_mem W hrqΔ) (by rw [hVqdef]; ring)
  have hresVqi : resq W hAq i Vqi * χO = 1 := by
    rw [← hresVq, ← resq_mul W hAq hqc hR i hVqiΔ hVqΔ, hVqiVq, ← map_one (algebraMap O (LetA O n)),
      resq_alg W hAq hqc hR i]
  have hresVp : resq W hAq i Vp = 1 :=
    resq_eq W hAq hqc i hVpΔ (letE_mul_mem W (W.AΔ.mul_mem hπ hrpΔ)) (by rw [map_one, hVpdef]; ring)
  have hresD : -((PD.p : ℕ) : O) * resq W hAq i D = 1 - χO ^ bb := by
    have := congrArg (resq W hAq i) hπD
    rw [resq_mul W hAq hqc hR i hπ (W.AΔ.sub_mem hA1Δ hA2Δ), residue_pi0_eq_neg_prime W hAq hqc hR i,
      hresq_sub (W.AΔ.pow_mem hVpΔ _) (W.AΔ.pow_mem hVqΔ _), resq_pow W hAq hqc hR i hVpΔ,
      resq_pow W hAq hqc hR i hVqΔ, hresVp, hresVq, one_pow] at this
    exact this
  have hVqi_val : resq W hAq i Vqi = (((W.χΓ W.gam)⁻¹ : Oˣ) : O) := by
    have h1 : (((W.χΓ W.gam)⁻¹ : Oˣ) : O) * χO = 1 := by rw [hχO, Units.inv_mul]
    calc resq W hAq i Vqi = resq W hAq i Vqi * (χO * (((W.χΓ W.gam)⁻¹ : Oˣ) : O)) := by
          rw [mul_comm χO, h1, mul_one]
      _ = _ := by rw [← mul_assoc, hresVqi, one_mul]
  have hrese₁ : resq W hAq i e₁ = cc bb := by
    have h1 : -((PD.p : ℕ) : O) * resq W hAq i e₁ = -((PD.p : ℕ) : O) * cc bb := by
      rw [he₁, resq_mul W hAq hqc hR i (W.AΔ.pow_mem hVqiΔ _) (W.AΔ.sub_mem hA1Δ hA2Δ),
        resq_pow W hAq hqc hR i hVqiΔ, mul_left_comm, hresD, hcc, hVqi_val]
      rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, mul_sub, mul_one, ← mul_pow]
      rw [show (((W.χΓ W.gam)⁻¹ : Oˣ) : O) * χO = 1 by rw [hχO, Units.inv_mul], one_pow]
    exact mul_left_cancel₀ (neg_ne_zero.2 hp0) h1

  have hxi : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i x := ⟨⟨hxN, hxD.2⟩, mem_Nl W T₂ hxN hxD.1⟩
  have hzi : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i z := ⟨⟨hzN, hzD.2⟩, mem_Nl W T₂ hzN hzD.1⟩
  have hi_add : ∀ {y y'}, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y' →
      Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i (y + y') := fun hy hy' =>
    ⟨(W.NΔ T₂).add_mem hy.1 hy'.1, (W.Nl T₂ i).add_mem hy.2 hy'.2⟩
  have hi_smulA : ∀ {g : LetA O n} {y}, g ∈ W.AΔ → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y →
      Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i (g • y) := fun hg hy =>
    ⟨Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T₂ hg hy.1, (W.Nl T₂ i).smul_mem _ hy.2⟩
  have hi_smulO : ∀ (o : O) {y}, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i (o • y) :=
    fun o y hy => by
      rw [← algebraMap_smul (LetA O n)]
      exact hi_smulA (W.AΔ.algebraMap_mem o) hy
  have hi_sub : ∀ {y y'}, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y' →
      Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i (y - y') := by
    intro y y' hy hy'
    have := hi_add hy (hi_smulO (-1) hy')
    rwa [neg_one_smul, ← sub_eq_add_neg] at this

  have hdopi : ∀ {y}, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i y → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i (dop y) := by
    intro y hy
    obtain ⟨y', hy'Δ, hy'e⟩ := hmod₂.2 y hy.1
    have hdy : dop y = y' := Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T₂ hπU (by rw [hdop]; exact hy'e)
    rw [hdy]
    refine ⟨hy'Δ, mem_Nl W T₂ hy'Δ.1 ?_⟩
    apply Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T₂ hπU
    have hyl : (letE i : LetA O n) • y = y := Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T₂ i hy.2
    rw [smul_comm, ← hy'e, smul_sub, hyl]
    congr 1
    show (letE i : LetA O n) • W.γD T₂ W.gam y = W.γD T₂ W.gam y
    conv_rhs => rw [← hyl]
    rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', Formalism.MainNotions.UnusedSlot80.KL.γA_letE W]

  obtain ⟨Ta, hTaΔ, eTa⟩ := one_add_pi0_mul_pow W hgq'Δ a
  have hγqa : W.γA W.gam (qp ^ a) - qp ^ a = W.π₀ * (qp ^ a * Ta) := by
    have hVqa : Vq ^ a = 1 + W.π₀ * Ta := by rw [hVq1, eTa]
    rw [map_pow, hVq, mul_pow, hVqa]; ring
  have hdopq : ∀ {nn}, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i nn → ∃ nn', Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i nn' ∧
      dop (qp ^ a • nn) = qp ^ a • nn' := by
    intro nn hnn
    refine ⟨(Vq ^ a) • dop nn + Ta • nn, hi_add (hi_smulA (W.AΔ.pow_mem hVqΔ _) (hdopi hnn))
      (hi_smulA hTaΔ hnn), ?_⟩
    rw [dop_smulA W T₂ hπU dop hdop hγqa, map_pow, hVq, mul_pow, smul_add, smul_smul, smul_smul,
      mul_comm (Vq ^ a)]

  let V : ℕ → W.DD T₂ → Prop := fun k y => ∃ g ∈ W.AΔ, ∃ nn, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i nn ∧
    y = (qp ^ k * g) • x + qp ^ a • nn
  have hstep : ∀ (k : ℕ) (y : W.DD T₂), V k y → V (k + 1) (dop y - cc ((bb : ℤ) - k) • y) := by
    intro k y ⟨g, hg, nn, hnn, hy⟩
    subst hy
    obtain ⟨gg', hgg'Δ, hgg'⟩ := hγg g hg
    obtain ⟨Tk, hTkΔ, eTk⟩ := one_add_pi0_mul_pow W hgq'Δ k
    have hVqk : Vq ^ k = 1 + W.π₀ * Tk := by rw [hVq1, eTk]
    set r' : LetA O n := qp ^ k * (Tk * W.γA W.gam g + qp * gg') with hr'
    have hγr : W.γA W.gam (qp ^ k * g) - qp ^ k * g = W.π₀ * r' := by
      have e1 : W.γA W.gam g = g + W.π₀ * qp * gg' := by linear_combination hgg'
      rw [map_mul, map_pow, hVq, mul_pow, hVqk, hr', e1]; ring
    obtain ⟨nn', hnn', hdn⟩ := hdopq hnn
    set c : O := cc ((bb : ℤ) - k) with hc
    set Y : LetA O n := Vq ^ k * W.γA W.gam g * e₁ + Tk * W.γA W.gam g + qp * gg' -
      algebraMap O (LetA O n) c * g with hY
    have hγgΔ : W.γA W.gam g ∈ W.AΔ := fun δ hδ => by
      rw [Formalism.MainNotions.UnusedSlot80.KL.γA_comm W, hg δ hδ]
    have hYΔ : Y ∈ W.AΔ := W.AΔ.sub_mem (W.AΔ.add_mem (W.AΔ.add_mem
      (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hVqΔ _) hγgΔ) he₁Δ) (W.AΔ.mul_mem hTkΔ hγgΔ))
      (W.AΔ.mul_mem hq hgg'Δ)) (W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) hg)

    have hresγg : resq W hAq i (W.γA W.gam g) = resq W hAq i g := by
      have e1 : W.γA W.gam g = g + qp * (W.π₀ * gg') := by linear_combination hgg'
      rw [e1, resq_add W hAq hqc hR i hg (W.AΔ.mul_mem hq (W.AΔ.mul_mem hπ hgg'Δ)),
        resq_qp_mul W hAq hqc hR i (W.AΔ.mul_mem hπ hgg'Δ), add_zero]
    have hresTk : -((PD.p : ℕ) : O) * resq W hAq i Tk = χO ^ k - 1 := by
      have e1 : W.π₀ * Tk = Vq ^ k - 1 := by rw [hVqk]; ring
      have := congrArg (resq W hAq i) e1
      rw [resq_mul W hAq hqc hR i hπ hTkΔ, residue_pi0_eq_neg_prime W hAq hqc hR i,
        hresq_sub (W.AΔ.pow_mem hVqΔ _) W.AΔ.one_mem, resq_pow W hAq hqc hR i hVqΔ, hresVq,
        ← map_one (algebraMap O (LetA O n)), resq_alg W hAq hqc hR i] at this
      exact this
    have hresY : resq W hAq i Y = 0 := by
      have h1 : -((PD.p : ℕ) : O) * resq W hAq i Y = 0 := by
        rw [hY, hresq_sub (W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.mul_mem
          (W.AΔ.pow_mem hVqΔ _) hγgΔ) he₁Δ) (W.AΔ.mul_mem hTkΔ hγgΔ)) (W.AΔ.mul_mem hq hgg'Δ))
          (W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) hg),
          resq_add W hAq hqc hR i (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.mul_mem
          (W.AΔ.pow_mem hVqΔ _) hγgΔ) he₁Δ) (W.AΔ.mul_mem hTkΔ hγgΔ)) (W.AΔ.mul_mem hq hgg'Δ),
          resq_add W hAq hqc hR i (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hVqΔ _) hγgΔ) he₁Δ)
            (W.AΔ.mul_mem hTkΔ hγgΔ),
          resq_mul W hAq hqc hR i (W.AΔ.mul_mem (W.AΔ.pow_mem hVqΔ _) hγgΔ) he₁Δ,
          resq_mul W hAq hqc hR i (W.AΔ.pow_mem hVqΔ _) hγgΔ, resq_mul W hAq hqc hR i hTkΔ hγgΔ,
          resq_qp_mul W hAq hqc hR i hgg'Δ, resq_mul W hAq hqc hR i (W.AΔ.algebraMap_mem _) hg,
          resq_alg W hAq hqc hR i, resq_pow W hAq hqc hR i hVqΔ, hresVq, hresγg, hrese₁]
        have hc' := hcc ((bb : ℤ) - k)
        have hb' := hcc (bb : ℤ)
        rw [← hc] at hc'
        have hχk : χO ^ k * (((W.χΓ W.gam) ^ (-(bb : ℤ)) : Oˣ) : O) =
            (((W.χΓ W.gam) ^ (-((bb : ℤ) - k)) : Oˣ) : O) := by
          rw [hχO, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
          congr 2
          ring
        linear_combination (resq W hAq i g) * (χO ^ k * hb' + hresTk - hc' + hχk)
      exact (mul_eq_zero.1 h1).resolve_left (neg_ne_zero.2 hp0)
    obtain ⟨Y', hY'Δ, hY'⟩ := mem_of_resq_zero W hAq i hYΔ hresY
    have hrΔ : qp ^ k * g ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem hq _) hg
    have hγrΔ : W.γA W.gam (qp ^ k * g) ∈ W.AΔ := fun δ hδ => by
      rw [Formalism.MainNotions.UnusedSlot80.KL.γA_comm W, hrΔ δ hδ]
    refine ⟨Y', hY'Δ, (W.γA W.gam (qp ^ k * g) * (Vqi ^ bb * Vp ^ hh)) • z + nn' - c • nn,
      hi_sub (hi_add (hi_smulA (W.AΔ.mul_mem hγrΔ
        (W.AΔ.mul_mem (W.AΔ.pow_mem hVqiΔ _) (W.AΔ.pow_mem hVpΔ _))) hzi) hnn') (hi_smulO c hnn), ?_⟩
    have hxc0 : W.γA W.gam (qp ^ k * g) * e₁ + r' - algebraMap O (LetA O n) c * (qp ^ k * g) =
        qp ^ k * Y := by
      rw [hY, hr', map_mul, map_pow, hVq, mul_pow]
      ring
    have hxc : (W.γA W.gam (qp ^ k * g) * e₁ + r' - algebraMap O (LetA O n) c * (qp ^ k * g)) • x =
        (qp ^ (k + 1) * Y') • x := by
      rw [hxc0]
      calc (qp ^ k * Y) • x = (qp ^ k * Y) • ((letE i : LetA O n) • x) := by rw [hxD.1]
        _ = (qp ^ k * ((letE i : LetA O n) * Y)) • x := by rw [smul_smul]; congr 1; ring
        _ = (qp ^ (k + 1) * Y') • x := by rw [hY', pow_succ]; congr 1; ring
    rw [map_add, dop_smulA W T₂ hπU dop hdop hγr, hdx, hdn]
    simp only [← algebraMap_smul (LetA O n) c]
    have e1 : W.γA W.gam (qp ^ k * g) * (Vqi ^ bb * Vp ^ hh * qp ^ a) =
        qp ^ a * (W.γA W.gam (qp ^ k * g) * (Vqi ^ bb * Vp ^ hh)) := by ring
    have e2 : algebraMap O (LetA O n) c * qp ^ a = qp ^ a * algebraMap O (LetA O n) c := by ring
    rw [← hxc]
    simp only [smul_add, smul_sub, add_smul, sub_smul, smul_smul, e1, e2]
    abel

  have hprod : ∀ k : ℕ, V k (aeval dop (∏ j ∈ (Finset.range k).image (fun t : ℕ => (bb : ℤ) - t),
      (X - C (cc j))) x) := by
    intro k
    induction k with
    | zero => exact ⟨1, W.AΔ.one_mem, 0, ⟨(W.NΔ T₂).zero_mem, (W.Nl T₂ i).zero_mem⟩, by simp⟩
    | succ k ih =>
      rw [Finset.range_add_one, Finset.image_insert, Finset.prod_insert (by
        simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
        intro t ht h; omega), map_mul]
      have e : (aeval dop (X - C (cc ((bb : ℤ) - k))) * aeval dop (∏ j ∈ (Finset.range k).image
          (fun t : ℕ => (bb : ℤ) - t), (X - C (cc j)))) x =
          dop (aeval dop (∏ j ∈ (Finset.range k).image (fun t : ℕ => (bb : ℤ) - t), (X - C (cc j))) x) -
          cc ((bb : ℤ) - k) • aeval dop (∏ j ∈ (Finset.range k).image (fun t : ℕ => (bb : ℤ) - t),
            (X - C (cc j))) x := by
        simp [Module.End.mul_apply, Module.algebraMap_end_apply]
      rw [e]
      exact hstep k _ ih
  have hIcc : Finset.Icc ((bb : ℤ) - a + 1) (bb : ℤ) = (Finset.range a).image (fun t : ℕ => (bb : ℤ) - t) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(bb - j).toNat, by omega, by omega⟩
    · rintro ⟨t, ht, rfl⟩
      omega
  obtain ⟨g, hg, nn, hnn, he⟩ := hprod a
  refine ⟨g • x + nn, hi_add (hi_smulA hg hxi) hnn, ?_⟩
  rw [hIcc, he, smul_add, smul_smul]

end G56Main

end Formalism.MainNotions.N.Pv.LocalLengthBound
