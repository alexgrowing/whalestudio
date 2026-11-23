import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaSystemFixedExponent
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenfunctionalZeroProjection
import Development.AbelianVarietyTheory.Definitions.Foundations.PieceEqPieceT
import Development.AbelianVarietyTheory.Definitions.Foundations.HtCoLOfEq
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleHodgeTateZetaClassParams
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleNewformZetaData
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFROfIsLamF
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Definitions.Foundations.ActWBOfInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPrimitiveRootEOmLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFunctionalOddWeightOddPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBActSgDDiamIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombination
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeDiamondAction
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Thdiam
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFR2

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.KZ GlobalTheory.Ord2 GlobalTheory.K4

namespace GlobalTheory.LambdaValuationPowers.ZetaCoef

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem norm_algebraMap_le (a : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']
  exact a.2

theorem exists_isLamG [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (hl : l ≠ 2) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) {s : G ℚ Ω}
    (hs : cycMod ℚ Ω l m s = 1) :
    ∃ tt : ZMod (l ^ n), GlobalTheory.Glue.IsLamG ε l n m s tt ∧ ∃ v u : Qbar l, ‖v‖ ≤ 1 ∧ ‖u‖ ≤ 1 ∧
      ((tt.val : ℕ) : Qbar l) = lamv l m s * (1 + (l : Qbar l) ^ m * v) + (l : Qbar l) ^ n * u := by
  have hp : l.Prime := Fact.out
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 hp.ne_zero⟩
  obtain ⟨a, ha, hlam⟩ := exists_lamv_eq hs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have h3 : 3 ≤ l := by have := hp.two_le; omega
  obtain ⟨y, hy⟩ := ZMod.exists_one_add_mul_pow_prime_pow_eq (R := ℤ_[l]) (u := (l : ℤ_[l]) ^ m * a) (v := (l : ℤ_[l]) ^ m) hp
    (dvd_mul_right _ _) (by
      obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le h3
      obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm
      refine ⟨((l : ℤ_[l]) ^ (1 + m') * a) ^ q * a ^ 2 * (l : ℤ_[l]) ^ m', ?_⟩
      rw [show ((l : ℤ_[l]) ^ (1 + m') * a) ^ l = ((l : ℤ_[l]) ^ (1 + m') * a) ^ (3 + q) by rw [← hq]]
      ring) 1 k
  set T : ℤ_[l] := a * (1 + (l : ℤ_[l]) ^ m * y) with hT
  set tt : ZMod (l ^ (m + k)) := PadicInt.toZModPow (m + k) T with htt
  have h2 : ((tt.val : ℕ) : ℤ_[l]) - T ∈ RingHom.ker (PadicInt.toZModPow (m + k) : ℤ_[l] →+* ZMod (l ^ (m + k))) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, htt, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨u, hu⟩ := h2
  refine ⟨tt, ?_, algebraMap ℤ_[l] (Qbar l) y, algebraMap ℤ_[l] (Qbar l) u, norm_algebraMap_le _, norm_algebraMap_le _, ?_⟩
  · have hz := GlobalTheory.Glue.Roots.isPrimitiveRoot_zt ε hp.ne_zero (2 * (m + k))
    have hn : GlobalTheory.Glue.zt ε l (m + k) = GlobalTheory.Glue.zt ε l (2 * (m + k)) ^ l ^ (m + k) := by
      rw [two_mul, GlobalTheory.Glue.Roots.zt_add_pow ε hp.ne_zero]
    change (s ^ (l ^ (m + k - m))) (GlobalTheory.Glue.zt ε l (2 * (m + k))) =
      GlobalTheory.Glue.zt ε l (m + k) ^ tt.val * GlobalTheory.Glue.zt ε l (2 * (m + k))
    have h1 : (s ^ (l ^ k)) (GlobalTheory.Glue.zt ε l (2 * (m + k))) = GlobalTheory.Glue.zt ε l (2 * (m + k)) ^
        (PadicInt.toZModPow (2 * (m + k)) ((cycZ ℚ Ω l (s ^ (l ^ k)) : ℤ_[l]ˣ) : ℤ_[l])).val :=
      cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω (s ^ (l ^ k))) _ hz.pow_eq_one
    have h4 : ((cycZ ℚ Ω l (s ^ (l ^ k)) : ℤ_[l]ˣ) : ℤ_[l]) =
        ((l ^ (m + k) * tt.val + 1 : ℕ) : ℤ_[l]) - ((l ^ (2 * (m + k)) : ℕ) : ℤ_[l]) * u := by
      rw [map_pow, Units.val_pow_eq_pow_val, ha]
      rw [mul_one] at hy
      rw [hy]
      push_cast
      rw [eq_add_of_sub_eq hu, hT]
      ring
    rw [Nat.add_sub_cancel_left, h1, h4, map_sub, map_mul, map_natCast, map_natCast, ZMod.natCast_self, zero_mul, sub_zero,
      ZMod.val_natCast, ← pow_eq_pow_mod _ hz.pow_eq_one, hn, ← pow_mul, pow_succ]
  · have := congrArg (algebraMap ℤ_[l] (Qbar l)) (eq_add_of_sub_eq hu)
    rw [map_natCast] at this
    rw [this, hlam, hT]
    simp only [map_add, map_mul, map_pow, map_natCast, map_one]
    ring

abbrev pushB {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N] (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l)
    (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ m))ˣ) : X.Fn l :=
  GlobalTheory.KA.push (redM l n m (N * N)) (fun (s' : Ω ≃ₐ[ℚ] Ω) (y' : (ZMod (topM l n m (N * N)))ˣ) =>
    X.galB l (repM (topM l n m (N * N)) y')
      (bB ((repM (topM l n m (N * N)) y')⁻¹ * s' * repM (topM l n m (N * N)) (y' * (cycM (topM l n m (N * N)) s')⁻¹)))) s y

theorem pushB_spec [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {N : ℕ} [NeZero N] (w n m : ℕ)
    (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (hgal : ∀ s : Ω ≃ₐ[ℚ] Ω, ∀ b ∈ X.B N l w, X.galB l s b ∈ X.B N l w) (hadd : ∀ b b', pr (b + b') = pr b + pr b')
    (heq : ∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l w → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b)
    (bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l) (hB : ∀ σ ∈ fixMu Ω (topMu l n m N), bB σ ∈ X.B N l w) (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ m))ˣ) :
    pushB X l n m N bB s y ∈ X.B N l w ∧ pr (pushB X l n m N bB s y) = YfB X l pr W e ψ n m N bB s y := by
  have hmem : ∀ y' : (ZMod (topM l n m (N * N)))ˣ,
      bB ((repM (topM l n m (N * N)) y')⁻¹ * s * repM (topM l n m (N * N)) (y' * (cycM (topM l n m (N * N)) s)⁻¹)) ∈
        X.B N l w := fun y' => hB _ (shArg_mem_fixMu (topM l n m (N * N)) s y')
  refine ⟨Submodule.sum_mem _ fun y' _ => hgal _ _ (hmem y'), ?_⟩
  refine (map_sum (AddMonoidHom.mk' pr hadd) _ _).trans ?_
  exact Finset.sum_congr rfl fun y' _ => heq _ _ (hmem y')

theorem cycMod_one_of {m : ℕ} (hm : 1 ≤ m) {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) : cycMod ℚ Ω l 1 s = 1 := by
  obtain ⟨a, ha, -⟩ := exists_lamv_eq hs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  ext
  change PadicInt.toZModPow 1 ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1
  have e : (l : ℤ_[l]) ^ (1 + k) * a = ((l ^ 1 : ℕ) : ℤ_[l]) * ((l : ℤ_[l]) ^ k * a) := by push_cast; ring
  rw [ha, e, map_add, map_one, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero]

theorem cg_per {per : ℕ → Qbar l} (h : ∀ n, Cg n (per (n + 1)) (per n)) {m n : ℕ} (hmn : m ≤ n) : Cg m (per n) (per m) := by
  induction n, hmn using Nat.le_induction with
  | base => simp [Cg]
  | succ n hn ih =>
    have h1 : Cg m (per (n + 1)) (per n) := GlobalTheory.KummerEisensteinGalois.cg_mono hn (h n)
    unfold Cg at *
    rw [← sub_add_sub_cancel _ (per n)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ih)

theorem chain {Y P F pn pm E t a v u C lc μ ν : Qbar l} (hμ : ‖μ‖ < 1) (hlc : ‖lc‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hC : ‖C‖ ≤ 1)
    (hv : ‖v‖ ≤ 1) (hu : ‖u‖ ≤ 1) (hpn : ‖pn‖ = 1) (hpm : ‖pm‖ = 1) (ht : t = a * (1 + μ * v) + ν * u)
    (h1 : ‖Y - P‖ ≤ ‖μ‖) (h2 : ‖F - pn * P‖ ≤ ‖μ‖) (h3 : ‖lc * F - (lc * (E * t) + C)‖ ≤ ‖μ‖) (h4 : ‖pn - pm‖ ≤ ‖μ‖)
    (h5 : ‖E * ν‖ ≤ ‖μ‖) : ‖lc * Y - (lc * (pm⁻¹ * E) * a + pn⁻¹ * C)‖ ≤ ‖μ‖ := by
  have add : ∀ {r : ℝ} {x y : Qbar l}, ‖x‖ ≤ r → ‖y‖ ≤ r → ‖x + y‖ ≤ r := fun hx hy =>
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  have mul : ∀ {r : ℝ} {x y : Qbar l}, ‖x‖ ≤ 1 → ‖y‖ ≤ r → ‖x * y‖ ≤ r := fun hx hy => by
    rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans hy
  have neg : ∀ {r : ℝ} {x : Qbar l}, ‖x‖ ≤ r → ‖-x‖ ≤ r := fun hx => by rwa [norm_neg]
  have hunit : ‖1 + μ * v‖ = 1 := by
    have h : ‖μ * v‖ < ‖(1 : Qbar l)‖ := by
      rw [norm_one, mul_comm]; exact (mul hv le_rfl).trans_lt hμ
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le, norm_one]
  have hG : ‖lc * E * a‖ ≤ 1 := by
    have e : lc * E * a * (1 + μ * v) = lc * ((F - pn * P) + pn * P) + -C + -(lc * F - (lc * (E * t) + C)) +
        -(lc * (u * (E * ν))) := by rw [ht]; ring
    have h := add (add (add (mul hlc (add (h2.trans hμ.le) (mul hpn.le hP))) (neg hC)) (neg (h3.trans hμ.le)))
      (neg (mul hlc (mul hu (h5.trans hμ.le))))
    rwa [← e, norm_mul, hunit, mul_one] at h
  have hn0 : pn ≠ 0 := fun h => by simp [h] at hpn
  have hm0 : pm ≠ 0 := fun h => by simp [h] at hpm
  have e : pn * (pm * (lc * Y - (lc * (pm⁻¹ * E) * a + pn⁻¹ * C))) =
      pm * (pn * (lc * (Y - P))) + -(pm * (lc * (F - pn * P))) + pm * (lc * F - (lc * (E * t) + C)) +
        pm * (lc * E * a * (v * μ)) + pm * (lc * (u * (E * ν))) + -(lc * E * a * (pn - pm)) := by
    rw [ht]; field_simp; ring
  have h := add (add (add (add (add (mul hpm.le (mul hpn.le (mul hlc h1))) (neg (mul hpm.le (mul hlc h2)))) (mul hpm.le h3))
    (mul hpm.le (mul hG (mul hv le_rfl)))) (mul hpm.le (mul hlc (mul hu h5)))) (neg (mul hG h4))
  rwa [← e, norm_mul, norm_mul, hpn, hpm, one_mul, one_mul] at h

theorem diam_diam {ε : Ω →+* ℂ} (X : Tower Ω ε) {N w a b k : ℕ} (ha : Nat.Coprime a N) (hb : Nat.Coprime b N)
    (hk : k ≡ a * b [MOD N]) {f : X.Fn l} (hf : f ∈ X.B N l w) : X.diam N l b (X.diam N l a f) = X.diam N l k f := by
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have h := isDiam_mul (isDiam_sgD_of_coprime (l := l) hl0 ha) (isDiam_sgD_of_coprime (l := l) hl0 hb)
  have h' : IsDiam N l k (sgD N l a * sgD N l b) :=
    ⟨h.1, h.2.trans ((ZMod.natCast_eq_natCast_iff _ _ _).2 (by rw [mul_comm]; exact hk.symm))⟩
  rw [Tower.diam, Tower.diam, Tower.diam, Tower.act_act Ω ε X l _ _ (hpos _) (hpos _) f, ← X.act_isDiam_eq hf h',
    Matrix.SpecialLinearGroup.coe_mul]

theorem inChi_avg {ε : Ω →+* ℂ} (X : Tower Ω ε) {N : ℕ} [NeZero N] (hNl : Nat.Coprime N l) {w : ℕ} {χ : ℕ → ℤ_[l]}
    (hχ : ∀ a b k : ℕ, Nat.Coprime a N → Nat.Coprime b N → k ≡ a * b [MOD N] → χ k = χ a * χ b)
    (u : (ZMod N)ˣ → ℤ_[l]) (hu : ∀ δ, u δ * χ (δ : ZMod N).val = 1) {f : X.Fn l} (hf : f ∈ X.B N l w) :
    GlobalTheory.KummerEisensteinGalois.InChi X N w χ (∑ δ : (ZMod N)ˣ, u δ • X.diam N l (δ : ZMod N).val f) := by
  refine ⟨Submodule.sum_mem _ fun δ _ => Submodule.smul_mem _ _
    (GlobalTheory.CyclotomicQExpansion.ThnEx.diam_B X N l w _ (NeZero.pos N) hNl (ZMod.val_coe_unit_coprime δ) f hf), fun d hd => ?_⟩
  rw [map_sum, Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulRight (ZMod.unitOfCoprime d hd))
    (fun δ => χ d • u δ • X.diam N l (δ : ZMod N).val f)]
  refine Finset.sum_congr rfl fun δ _ => ?_
  have hk : ((δ * ZMod.unitOfCoprime d hd : (ZMod N)ˣ) : ZMod N).val ≡ (δ : ZMod N).val * d [MOD N] := by
    rw [← ZMod.natCast_eq_natCast_iff]; simp
  have h1 := hχ _ _ _ (ZMod.val_coe_unit_coprime δ) hd hk
  have h2 := hu (δ * ZMod.unitOfCoprime d hd)
  have h3 : χ d * u (δ * ZMod.unitOfCoprime d hd) = u δ := by
    rw [h1] at h2
    linear_combination (-(χ d * u (δ * ZMod.unitOfCoprime d hd))) * hu δ + u δ * h2
  rw [map_smul, diam_diam X (ZMod.val_coe_unit_coprime δ) hd hk hf, Equiv.coe_mulRight, smul_smul, h3]

theorem exists_isThB_sum [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {A : ValuationSubring Ω} {j : Ω →+* Qbar l}
    (hj : ∀ z : Ω, z ∈ A ↔ ‖j z‖ ≤ 1) (hnon : (l : Ω) ∈ A.nonunits) {N w n : ℕ} {ι : Type} (T : Finset ι) (hT : T.Nonempty)
    (u : ι → ℤ_[l]) (f : ι → X.Fn l) (φ : ι → HahnSeries ℚ Ω) (hf : ∀ i, f i ∈ X.B N l w)
    (hφ : ∀ i, GlobalTheory.Glue.IsThB X A N l n (f i) (φ i)) :
    ∃ Φ : HahnSeries ℚ Ω, GlobalTheory.Glue.IsThB X A N l n (∑ i ∈ T, u i • f i) Φ ∧
      ∀ r, Cg n (j (Φ.coeff r)) (∑ i ∈ T, algebraMap ℤ_[l] (Qbar l) (u i) * j ((φ i).coeff r)) := by
  have hint : ∀ {b : X.Fn l} {Φ : HahnSeries ℚ Ω}, GlobalTheory.Glue.IsThB X A N l n b Φ → ∀ r, ‖j (Φ.coeff r)‖ ≤ 1 :=
    fun ⟨_, _, _, _, h, _⟩ r => (hj _).1 (h r)
  have happ : ∀ (a : ℤ_[l]) (z : Qbar l), ‖z‖ ≤ 1 →
      ‖((a.appr n : ℕ) : Qbar l) * z - algebraMap ℤ_[l] (Qbar l) a * z‖ ≤ ‖(l : Qbar l) ^ n‖ := fun a z hz => by
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n a)
    have h := congrArg (algebraMap ℤ_[l] (Qbar l)) hq
    rw [map_sub, map_natCast, map_mul, map_pow, map_natCast] at h
    rw [← sub_mul, norm_mul, norm_sub_rev, h]
    refine (mul_le_of_le_one_right (norm_nonneg _) hz).trans ?_
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_algebraMap_le q)
  have key : ∀ (a a' : ℤ_[l]) {b b' : X.Fn l} {Φ Φ' : HahnSeries ℚ Ω}, b ∈ X.B N l w → b' ∈ X.B N l w →
      GlobalTheory.Glue.IsThB X A N l n b Φ → GlobalTheory.Glue.IsThB X A N l n b' Φ' →
      ∃ Ψ, GlobalTheory.Glue.IsThB X A N l n (a • b + a' • b') Ψ ∧ ∀ r, ‖j (Ψ.coeff r) -
        (algebraMap ℤ_[l] (Qbar l) a * j (Φ.coeff r) + algebraMap ℤ_[l] (Qbar l) a' * j (Φ'.coeff r))‖ ≤ ‖(l : Qbar l) ^ n‖ := by
    intro a a' b b' Φ Φ' hb hb' h h'
    refine ⟨_, GlobalTheory.ThAdd.isThB_add Ω ε X A N l n w b b' hnon hb hb' a a' Φ Φ' h h', fun r => ?_⟩
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, smul_eq_mul, map_add, map_mul, map_natCast]
    rw [add_sub_add_comm]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (happ _ _ (hint h r)) (happ _ _ (hint h' r)))
  induction hT using Finset.Nonempty.cons_induction with
  | singleton i =>
    obtain ⟨Ψ, h1, h2⟩ := key (u i) 0 (hf i) (hf i) (hφ i) (hφ i)
    exact ⟨Ψ, by simpa using h1, fun r => by simpa [Cg] using h2 r⟩
  | cons i T hi _ ih =>
    obtain ⟨Φ, h1, h2⟩ := ih
    obtain ⟨Ψ, h3, h4⟩ := key (u i) 1 (hf i) (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hf i)) (hφ i) h1
    refine ⟨Ψ, by simpa [Finset.sum_cons, -Finset.cons_eq_insert] using h3, fun r => ?_⟩
    rw [Finset.sum_cons]
    unfold Cg
    rw [← sub_add_sub_cancel _ (algebraMap ℤ_[l] (Qbar l) (u i) * j ((φ i).coeff r) + algebraMap ℤ_[l] (Qbar l) 1 * j (Φ.coeff r))]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h4 r) ?_)
    rw [add_sub_add_left_eq_sub, map_one, one_mul]
    exact h2 r

theorem htCoL_of_fintype {A : ValuationSubring Ω} {c : Coef l} {j : Ω →+* Qbar l}
    {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} {m c₀ : ℕ} {y : (ZMod (l ^ m))ˣ} {h : Qbar l} {ι : Type} [Fintype ι]
    (o : ι → Qbar l) (w : ι → Ω) (how : ∀ i, ‖o i‖ ≤ 1 ∧ FixIc c (o i) ∧ ‖j (w i)‖ ≤ 1)
    (H : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
      Cg m ((l : Qbar l) ^ c₀ * Z m s y) ((l : Qbar l) ^ c₀ * h * lamv l m s + ∑ i, o i * (j (s (w i)) - j (w i)))) :
    HTCoL A c j Z m c₀ y h :=
  ⟨Fintype.card ι, fun i => o ((Fintype.equivFin ι).symm i), fun i => w ((Fintype.equivFin ι).symm i), fun _ => how _,
    fun s hs hc => by
      rw [(Fintype.equivFin ι).symm.sum_comp fun i => o i * (j (s (w i)) - j (w i))]
      exact H s hs hc⟩

theorem norm_pow_mul_le {a : Qbar l} {k : ℕ} (h : ‖a‖ ≤ (l : ℝ) ^ k) : ‖(l : Qbar l) ^ k * a‖ ≤ 1 := by
  have h2 := GlobalTheory.KummerEisensteinGalois.l_pow_mul_norm (l := l) (le_refl k)
  rw [Nat.sub_self, pow_zero, norm_one] at h2
  rw [norm_mul, mul_comm, ← h2]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

end GlobalTheory.LambdaValuationPowers.ZetaCoef

namespace GlobalTheory.LambdaValuationPowers

open ZetaCoef

end GlobalTheory.LambdaValuationPowers
