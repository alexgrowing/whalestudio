import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCoset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UniformizerPowerTorusMemNormalUnitarySubgroupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormalHyp

theorem unip_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ N : Subgroup (Formalism.UG.GU σ n), N.Normal → Formalism.UG.KU σ n ≤ N → ∀ u : Formalism.UG.GU σ n, Formalism.UG.IsUnipU u → u ∈ N := by
  intro L _ _ ϖ σ q n hU N hN hK u hu
  obtain ⟨hσσ, hσv, hσϖ, hϖ, -, -, -⟩ := hU
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  set U := (((u : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hUdef
  obtain ⟨M, hM⟩ := GlobalTheory.UnitarySwap.exists_pow_mem hϖ' U
  let b : Fin n → ℤ := fun i => (M : ℤ) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))
  have hb : ∀ i : Fin n, b i.rev = -b i := by
    intro i
    have := i.isLt
    simp only [b, Fin.val_rev]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  obtain ⟨s, hs, hs'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ b i) (fun i => by
    rw [map_zpow₀, hσϖ, hb, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])
  have hpow : ∀ k : ℤ, 0 ≤ k → Valued.v (ϖ ^ k) ≤ 1 := by
    intro k hk
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, map_pow]
    exact pow_le_one₀ zero_le hϖ1
  set k := s * u * s⁻¹ with hkdef
  have hkm : (((k : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ϖ ^ b i) * U * Matrix.diagonal (fun i => (ϖ ^ b i)⁻¹) := by
    rw [hkdef, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hs, hs']
  have hI : Formalism.UG.P.fIwasawaInt (((k : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    intro i j
    rw [hkm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases lt_trichotomy i j with hij | rfl | hij
    · have hle : (M : ℤ) ≤ b i - b j := by
        have : (i.val : ℤ) + 1 ≤ j.val := by exact_mod_cast hij
        simp only [b]
        nlinarith
      have e : ϖ ^ b i * U i j * (ϖ ^ b j)⁻¹ = ϖ ^ (b i - b j - M) * (ϖ ^ M * U i j) := by
        rw [zpow_sub₀ h0, zpow_sub₀ h0, zpow_natCast]
        field_simp
      rw [e, map_mul]
      exact mul_le_one' (hpow _ (by omega)) (hM i j)
    · have e1 : U i i = 1 := hu.2 i
      rw [e1, mul_one, mul_inv_cancel₀ (zpow_ne_zero _ h0), map_one]
    · have e1 : U i j = 0 := hu.1 i j hij
      rw [e1, mul_zero, zero_mul, map_zero]; exact zero_le
  have hkK : k ∈ Formalism.UG.KU σ n := by
    have := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ k) hI
    have e : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ k) = k := Subtype.ext (Units.ext rfl)
    rwa [e] at this
  have := hN.conj_mem k (hK hkK) s⁻¹
  have e : s⁻¹ * k * s⁻¹⁻¹ = u := by rw [hkdef]; group
  rwa [e] at this

theorem diag_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ N : Subgroup (Formalism.UG.GU σ n), N.Normal → Formalism.UG.KU σ n ≤ N → (∀ u : Formalism.UG.GU σ n, Formalism.UG.IsUnipU u → u ∈ N) → ∀ t : Formalism.UG.GU σ n, (∀ i j : Fin n, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) → t ∈ N := by
  intro L _ _ ϖ σ q n hU N hN hK hu t ht
  have hU' := hU
  obtain ⟨hσσ, hσv, hσϖ, hϖ, -, -, -⟩ := hU'
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  set T := (((t : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTdef
  have hTd : T = Matrix.diagonal (fun i => T i i) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · rw [Matrix.diagonal_apply_ne _ h]; exact ht i j h
  have hunit : ∀ i : Fin n, σ (T i i) * T i.rev i.rev = 1 := by
    intro i
    have := congrFun (congrFun (Formalism.UG.P.fIwasawa_mem_un σ t) i) i.rev
    rw [Formalism.UG.P.fIwasawa_gram, Formalism.UG.P.fIwasawa_antiJ, if_pos rfl] at this
    unfold Formalism.UG.P.fIwasawaH at this
    rw [Finset.sum_eq_single i.rev] at this
    · rw [Fin.rev_rev] at this; exact this
    · intro j _ hj
      show σ (T j.rev i) * T j i.rev = 0
      rw [ht j i.rev (fun h => hj h), mul_zero]
    · simp
  have hne : ∀ i, T i i ≠ 0 := by
    intro i h; have := hunit i; rw [h, map_zero, zero_mul] at this; exact zero_ne_one this
  have hv0 : ∀ i, Valued.v (T i i) ≠ 0 := fun i => by simpa using hne i
  let c : Fin n → ℤ := fun i => - WithZero.log (Valued.v (T i i))
  have hvrev : ∀ i, Valued.v (T i.rev i.rev) = (Valued.v (T i i))⁻¹ := by
    intro i
    have := congrArg Valued.v (hunit i)
    rw [map_mul, map_one, hσv] at this
    exact (eq_inv_of_mul_eq_one_right this)
  have hc : ∀ i : Fin n, c i.rev = -c i := by
    intro i
    simp only [c]
    rw [hvrev, WithZero.log_inv]
  obtain ⟨s, hs, hs'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ c i) (fun i => by
    rw [map_zpow₀, hσϖ, hc, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])
  have hsN : s ∈ N := GlobalTheory.T.uniformizerPowerTorus_mem_normal_unitarySubgroup L ϖ σ q n hU N hN hK hu c hc s hs
  have hvpow : ∀ i, Valued.v (ϖ ^ c i) = Valued.v (T i i) := by
    intro i
    rw [map_zpow₀, hϖ', ← WithZero.exp_zsmul, ← WithZero.exp_log (hv0 i)]
    simp [c]
  have hε : (((s⁻¹ * t : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => (ϖ ^ c i)⁻¹ * T i i) := by
    rw [Subgroup.coe_mul, Units.val_mul, hs', ← hTdef, hTd, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; simp
  have hI : Formalism.UG.P.fIwasawaInt (((s⁻¹ * t : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    intro i j
    rw [hε]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, map_mul, map_inv₀, hvpow, inv_mul_cancel₀ (hv0 i)]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero]; exact zero_le
  have hkK : s⁻¹ * t ∈ Formalism.UG.KU σ n := by
    have := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ (s⁻¹ * t)) hI
    have e : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ (s⁻¹ * t)) = s⁻¹ * t := Subtype.ext (Units.ext rfl)
    rwa [e] at this
  have e : t = s * (s⁻¹ * t) := by group
  rw [e]
  exact N.mul_mem hsN (hK hkK)

theorem borel_eq_diag_mul_unip : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (b : Formalism.UG.GU σ n), Formalism.UG.IsBorelU b → ∃ d u : Formalism.UG.GU σ n, (∀ i j : Fin n, i ≠ j → ((d : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) ∧ Formalism.UG.IsUnipU u ∧ b = d * u := by
  intro L _ _ σ n b hb
  obtain ⟨d, hd, hd'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ)
    (fun i => (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)
    (Formalism.UG.P.fSatake_unit_diag hb)
  have hne : ∀ i, (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
    intro i h0; have := Formalism.UG.P.fSatake_unit_diag hb i; rw [h0, map_zero, zero_mul] at this; exact zero_ne_one this
  have hu : (((d⁻¹ * b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ((((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)⁻¹) *
        (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [Subgroup.coe_mul, Units.val_mul, hd']
  refine ⟨d, d⁻¹ * b, fun i j hij => by rw [hd, Matrix.diagonal_apply_ne _ hij], ⟨fun i j hji => ?_, fun i => ?_⟩, by group⟩
  · rw [hu, Matrix.diagonal_mul, hb i j hji, mul_zero]
  · rw [hu, Matrix.diagonal_mul, inv_mul_cancel₀ (hne i)]

open Formalism.UG in
theorem frame {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q n : ℕ}
    (hU : IsUnramInv ϖ σ q) {J : GL (Fin n) L} (hJ : J ∈ GLint (Fin n) (intL L))
    (hh : ∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) :
    ∃ P ∈ GLint (Fin n) (intL L), cT σ (P : Matrix (Fin n) (Fin n) L) * (J : Matrix (Fin n) (Fin n) L) * P = antiJ L n := by
  obtain ⟨U, rfl⟩ := hJ
  let c := GlobalTheory.UnramDoubleCoset.intConj hU.2.1
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hU.1 x)
  let ι := (intL L).subtype
  let B : Matrix (Fin n) (Fin n) (intL L) := U
  have hB : cT c B = B := by
    ext i j
    show σ ((B j i : intL L) : L) = (B i j : L)
    exact hh j i
  obtain ⟨p, hp⟩ := GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hc (GlobalTheory.UnramDoubleCoset.exists_dvd_norm_sub_X hU) hB U.isUnit
  have hu : IsUnit B := U.isUnit
  have h2 : IsUnit (Polynomial.aeval B p) := isUnit_of_mul_isUnit_right (by rw [hp]; exact hu)
  obtain ⟨h, hh', eh⟩ := GlobalTheory.UnramDoubleCoset.exists_antiJ_frame hU n
  set K : GL (Fin n) L := bc ι h2.unit with hKdef
  have hK : (K : Matrix (Fin n) (Fin n) L) = (Polynomial.aeval B p).map ι := rfl
  have hJ : ((bc ι U : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = cT σ (K : Matrix (Fin n) (Fin n) L) * K := by
    rw [hK, GlobalTheory.UnitaryDoubleCoset.cT_map ι (c := c) (fun _ => rfl), ← Matrix.map_mul, hp]; rfl
  refine ⟨K⁻¹ * h, mul_mem (inv_mem ⟨_, rfl⟩) hh', ?_⟩
  rw [hJ, Units.val_mul, cT_mul, ← eh, Matrix.mul_one]
  have e1 : cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * cT σ (K : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  have e2 : (K : Matrix (Fin n) (Fin n) L) * ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv K
  calc cT σ (h : Matrix (Fin n) (Fin n) L) * cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (cT σ (K : Matrix (Fin n) (Fin n) L) * K) * (((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * h)
      = cT σ (h : Matrix (Fin n) (Fin n) L) * (cT σ ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * cT σ (K : Matrix (Fin n) (Fin n) L)) * ((K : Matrix (Fin n) (Fin n) L) * ((K⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) * h := by
        simp only [Matrix.mul_assoc]
    _ = cT σ (h : Matrix (Fin n) (Fin n) L) * h := by rw [e1, e2, Matrix.mul_one, Matrix.mul_one]

open Formalism.UG in
theorem antiJ_case {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q n : ℕ}
    (hU : IsUnramInv ϖ σ q) (N : Subgroup (GU σ n)) (hN : N.Normal) (hK : KU σ n ≤ N) : N = ⊤ := by
  have h2 := unip_mem L ϖ σ q n hU N hN hK
  have h3 := diag_mem L ϖ σ q n hU N hN hK h2
  rw [eq_top_iff]
  intro g _
  obtain ⟨b, k, hb, hk, rfl⟩ := Formalism.UG.P.fIwasawa_iwasawa σ hU.1 hU.2.1 g
  obtain ⟨d, u, hd, hu, rfl⟩ := borel_eq_diag_mul_unip L σ n b hb
  exact N.mul_mem (N.mul_mem (h3 d hd) (h2 u hu)) (hK hk)

theorem normal_closure_hyp : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (J : GL (Fin n) L), Formalism.UG.IsUnramInv ϖ σ q → Odd q → J ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) → ∀ N : Subgroup (Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L)), N.Normal → (∀ g : Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L), (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → g ∈ N) → N = ⊤ := by
  intro L _ _ _ ϖ σ q n J hU hq hJ hh N hN hK
  obtain ⟨P, hP, eP⟩ := frame hU hJ hh
  have memφ : ∀ g : Formalism.UG.GU σ n, P * (g : GL (Fin n) L) * P⁻¹ ∈ Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L) := by
    intro g
    simpa using GlobalTheory.InertDoubleCoset.conj_mem_UJ σ (GlobalTheory.InertDoubleCoset.inv_frame σ eP) g.2
  have memψ : ∀ g : Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L), P⁻¹ * (g : GL (Fin n) L) * P ∈ Formalism.UG.GU σ n :=
    fun g => GlobalTheory.InertDoubleCoset.conj_mem_UJ σ eP g.2
  let φ : Formalism.UG.GU σ n →* Formalism.UG.UJ σ (J : Matrix (Fin n) (Fin n) L) :=
    { toFun := fun g => ⟨P * (g : GL (Fin n) L) * P⁻¹, memφ g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hK' : Formalism.UG.KU σ n ≤ N.comap φ := by
    intro k hk
    show φ k ∈ N
    apply hK
    show P * (k : GL (Fin n) L) * P⁻¹ ∈ _
    exact mul_mem (mul_mem hP (Subgroup.mem_subgroupOf.1 hk).2) (inv_mem hP)
  have htop := antiJ_case hU (N.comap φ) (hN.comap φ) hK'
  rw [eq_top_iff]
  intro g _
  have hm : (⟨P⁻¹ * (g : GL (Fin n) L) * P, memψ g⟩ : Formalism.UG.GU σ n) ∈ N.comap φ := by rw [htop]; trivial
  have e : φ ⟨P⁻¹ * (g : GL (Fin n) L) * P, memψ g⟩ = g := Subtype.ext (by
    show P * (P⁻¹ * (g : GL (Fin n) L) * P) * P⁻¹ = g
    group)
  rw [← e]
  exact hm

end GlobalTheory.NormalHyp
