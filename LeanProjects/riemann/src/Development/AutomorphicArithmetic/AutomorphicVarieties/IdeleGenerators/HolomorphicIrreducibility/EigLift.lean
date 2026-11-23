import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DelSerre
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HeckeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FinDim

open Formalism.ConjugateSelfDual CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped MatrixGroups ModularForm

noncomputable section

namespace UpperTheory.V.Sd

private theorem one_mem_per (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, ?_, ?_⟩
  · rw [SetLike.mem_coe, Gamma1_mem]
    simp [ModularGroup.T]
  · ext i j
    change ((ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (fun x : ℤ => (x : ℝ)) i j = _
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

private theorem coef_smul {N : ℕ} {k : ℤ} (c : ℂ) (f : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (c • f : CuspForm (Gamma1 N) k) n = c * coef f n := by
  unfold coef
  rw [CuspForm.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_per N) c f, map_smul, smul_eq_mul]

private theorem coef_add {N : ℕ} {k : ℤ} (f g : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (f + g : CuspForm (Gamma1 N) k) n = coef f n + coef g n := by
  unfold coef
  rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_per N) f g, map_add]

private theorem norm_chi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (a : ZMod N) : ‖ι.symm (χ a)‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have hn : 0 < Fintype.card (ZMod N)ˣ := Fintype.card_pos
    have h1 : (χ (u : ZMod N)) ^ Fintype.card (ZMod N)ˣ = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    have h2 : ‖ι.symm (χ (u : ZMod N))‖ ^ Fintype.card (ZMod N)ˣ = 1 := by
      rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
    rw [pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne'] at h2
    exact h2.le
  · rw [MulChar.map_nonunit χ ha, map_zero, norm_zero]
    exact zero_le_one

private def fT {K : Type} [Field K] (p : ℕ) (e : K) : Module.End K (ℕ → K) where
  toFun c n := c (p * n) + e * (if p ∣ n then c (n / p) else 0)
  map_add' c d := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring
  map_smul' a c := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring

private theorem fT_apply {K : Type} [Field K] (p : ℕ) (e : K) (c : ℕ → K) (n : ℕ) :
    fT p e c n = c (p * n) + e * (if p ∣ n then c (n / p) else 0) := rfl

private theorem fT_comm {K : Type} [Field K] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (e e' : K)
    (c : ℕ → K) : fT p e (fT q e' c) = fT q e' (fT p e c) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hqp : ∀ n, q ∣ p * n ↔ q ∣ n := fun n =>
    ⟨fun h => hcop.symm.dvd_of_dvd_mul_left h, fun h => h.mul_left p⟩
  have hpq' : ∀ n, p ∣ q * n ↔ p ∣ n := fun n =>
    ⟨fun h => hcop.dvd_of_dvd_mul_left h, fun h => h.mul_left q⟩
  have hdiv1 : ∀ n, p ∣ n → (q ∣ n / p ↔ q ∣ n) := by
    rintro n ⟨k, rfl⟩
    rw [Nat.mul_div_cancel_left k hp.pos, hqp]
  have hdiv2 : ∀ n, q ∣ n → (p ∣ n / q ↔ p ∣ n) := by
    rintro n ⟨k, rfl⟩
    rw [Nat.mul_div_cancel_left k hq.pos, hpq']
  funext n
  simp only [fT_apply, hqp, hpq']
  rw [show q * (p * n) = p * (q * n) by ring]
  by_cases hp' : p ∣ n <;> by_cases hq' : q ∣ n
  · simp only [hp', hq', (hdiv1 n hp').2 hq', (hdiv2 n hq').2 hp', if_true]
    rw [Nat.mul_div_assoc p hq', Nat.mul_div_assoc q hp', Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
      mul_comm q p]
    ring
  · have : ¬ q ∣ n / p := fun h => hq' ((hdiv1 n hp').1 h)
    simp only [hp', hq', this, if_true, if_false, mul_zero, add_zero]
    rw [Nat.mul_div_assoc q hp']
  · have : ¬ p ∣ n / q := fun h => hp' ((hdiv2 n hq').1 h)
    simp only [hp', hq', this, if_true, if_false, mul_zero, add_zero]
    rw [Nat.mul_div_assoc p hq']
  · simp only [hp', hq', if_false, mul_zero, add_zero]

private theorem eq_zero_of_eig {K : Type} [Field K] (e b : Nat.Primes → K) (c : ℕ → K) (h0 : c 0 = 0) (h1 : c 1 = 0)
    (h : ∀ p : Nat.Primes, fT p.1 (e p) c = b p • c) : c = 0 := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have ih' : ∀ m < n, c m = 0 := fun m hm => by simpa using ih m hm
    rw [Pi.zero_apply]
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact h0
      · exact h1
    · have hpp : n.minFac.Prime := Nat.minFac_prime (by omega)
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, mul_zero] at hm
          omega
        · exact h
      have hm_lt : m < n := by
        have := hpp.two_le
        nlinarith
      have key := congr_fun (h ⟨n.minFac, hpp⟩) m
      simp only [fT_apply, Pi.smul_apply, smul_eq_mul] at key
      have hz : (if n.minFac ∣ m then c (m / n.minFac) else 0) = 0 := by
        split_ifs
        · exact ih' _ (lt_of_le_of_lt (Nat.div_le_self _ _) hm_lt)
        · rfl
      rw [ih' m hm_lt, hz, mul_zero, add_zero, mul_zero] at key
      rw [hm]
      exact key

private def Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (N : ℕ) (k : ℤ) :
    CuspForm (Gamma1 N) k →ₛₗ[(ι.symm : ℂ →+* Qbar l)] (ℕ → Qbar l) where
  toFun g n := if n = 0 then 0 else ι.symm (coef g n)
  map_add' f g := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_add, Pi.add_apply, map_add, add_zero]
  map_smul' a f := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_smul, Pi.smul_apply, map_mul, smul_eq_mul, mul_zero]
    rfl

private theorem Phi_apply {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k) (n : ℕ) :
    Phi ι N k g n = if n = 0 then 0 else ι.symm (coef g n) := rfl

private def chSub (N k : ℕ) (χ : DirichletCharacter ℂ N) : Submodule ℂ (CuspForm (Gamma1 N) (k : ℤ)) where
  carrier := {g | HasChar k χ g}
  add_mem' := by
    intro f g hf hg γ hγ
    rw [show ((f + g : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = (f : ℍ → ℂ) + g from rfl, SlashAction.add_slash,
      hf γ hγ, hg γ hγ, smul_add]
  zero_mem' := by
    intro γ _
    rw [show ((0 : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = 0 from rfl, SlashAction.zero_slash, smul_zero]
  smul_mem' := by
    intro c f hf γ hγ
    rw [show ((c • f : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl, ModularForm.SL_smul_slash,
      hf γ hγ, smul_comm]

private theorem fT_Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k)
    {p : ℕ} (hp : p.Prime) (e : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    fT p (ι.symm e) (Phi ι N k g) n = ι.symm (coef g (p * n) + e * (if p ∣ n then coef g (n / p) else 0)) := by
  rw [fT_apply, Phi_apply, if_neg (Nat.mul_ne_zero hp.ne_zero (by omega))]
  split_ifs with h
  · rw [Phi_apply, if_neg (Nat.div_pos (Nat.le_of_dvd hn h) hp.pos).ne', map_add, map_mul]
  · simp

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.eigLift :
    UpperTheory.V.Sd.EigLift := by
  unfold EigLift
  intro l _ ι N k _ hk χ f hchar hint hone a hA
  haveI : FiniteDimensional ℂ (CuspForm (Gamma1 N) (k : ℤ)) := (finDim N k).1
  let V : Submodule (Qbar l) (ℕ → Qbar l) := (chSub N k χ).map (Phi ι N k)
  have hV : FiniteDimensional (Qbar l) V := by
    have : (chSub N k χ).FG := Module.Finite.iff_fg.mp inferInstance
    exact Module.Finite.iff_fg.mpr (this.map _)
  have hstab : ∀ p : Nat.Primes, ∀ v ∈ V, fT p.1 (ι.symm (χ p.1 * (p.1 : ℂ) ^ (k - 1))) v ∈ V := by
    intro p v hv
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨g', hg'c, hg'⟩ := heckeEx N k hk χ g hg p.1 p.2
    refine Submodule.mem_map.mpr ⟨g', hg'c, ?_⟩
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Phi_apply, fT_apply]
    · rw [fT_Phi ι N k g p.2 _ hn, Phi_apply, if_neg hn.ne', hg' n hn]
  let T : Nat.Primes → Module.End (Qbar l) V := fun p =>
    (fT p.1 (ι.symm (χ p.1 * (p.1 : ℂ) ^ (k - 1)))).restrict (hstab p)
  have hT : ∀ p (v : V), ((T p v : V) : ℕ → Qbar l) =
      fT p.1 (ι.symm (χ p.1 * (p.1 : ℂ) ^ (k - 1))) v := fun p v => rfl
  have hep : ∀ p : Nat.Primes, ‖ι.symm (χ p.1 * (p.1 : ℂ) ^ (k - 1))‖ ≤ 1 := by
    intro p
    have h1 : ‖ι.symm (χ (p.1 : ZMod N))‖ ≤ 1 := norm_chi ι χ _
    have h2 : ‖ι.symm ((p.1 : ℂ) ^ (k - 1))‖ ≤ 1 := by
      rw [map_pow ι.symm, map_natCast ι.symm, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
    rw [map_mul ι.symm, norm_mul]
    exact mul_le_one₀ h1 (norm_nonneg _) h2
  have hcomm : ∀ i j : Nat.Primes, T i * T j = T j * T i := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · refine LinearMap.ext fun v => Subtype.ext ?_
      show fT i.1 _ (fT j.1 _ (v : ℕ → Qbar l)) = fT j.1 _ (fT i.1 _ (v : ℕ → Qbar l))
      exact fT_comm i.2 j.2 (fun h => hij (Subtype.ext h)) _ _ _
  have hbd : ∀ j (v : V), (∀ n, ‖(v : ℕ → Qbar l) n‖ ≤ 1) → ∀ n, ‖((T j v : V) : ℕ → Qbar l) n‖ ≤ 1 := by
    intro j v hv n
    rw [hT, fT_apply]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hv _) ?_)
    rw [norm_mul]
    refine mul_le_one₀ (hep j) (norm_nonneg _) ?_
    split_ifs
    · exact hv _
    · simp
  have hbd' : ∀ j (v : V), (∀ n, ‖(v : ℕ → Qbar l) n‖ < 1) → ∀ n, ‖((T j v : V) : ℕ → Qbar l) n‖ < 1 := by
    intro j v hv n
    rw [hT, fT_apply]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hv _) ?_)
    rw [norm_mul]
    split_ifs
    · exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hep j)) (hv _)
    · simp
  have hfmem : (f : CuspForm (Gamma1 N) (k : ℤ)) ∈ chSub N k χ := hchar
  let F : V := ⟨Phi ι N k f, Submodule.mem_map_of_mem hfmem⟩
  have hF : ((F : V) : ℕ → Qbar l) = Phi ι N k f := rfl
  have hf1 : ∀ n, ‖((F : V) : ℕ → Qbar l) n‖ ≤ 1 := by
    intro n
    rw [hF, Phi_apply]
    split_ifs
    · simp
    · exact hint n
  have hf2 : ∃ n, ‖((F : V) : ℕ → Qbar l) n‖ = 1 := ⟨1, by rw [hF, Phi_apply, if_neg one_ne_zero]; exact hone⟩
  have hcong : ∀ (j : Nat.Primes) n, ‖((T j F : V) : ℕ → Qbar l) n - ι.symm (a j.1) * ((F : V) : ℕ → Qbar l) n‖ < 1 := by
    intro j n
    rw [hT, hF]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Phi_apply, fT_apply]
    · rw [fT_Phi ι N k f j.2 _ hn, Phi_apply, if_neg hn.ne', ← map_mul, ← map_sub]
      exact (hA j.1 j.2).2 n hn
  obtain ⟨h, b, hne, -, heig, hclose⟩ := delSerre l ℕ Nat.Primes V hV T hcomm hbd hbd' F
    (fun p => ι.symm (a p.1)) hf1 hf2 (fun p => (hA p.1 p.2).1) hcong
  obtain ⟨g0, hg0, hPg⟩ := Submodule.mem_map.mp h.2
  have heig' : ∀ p : Nat.Primes,
      fT p.1 (ι.symm (χ p.1 * (p.1 : ℂ) ^ (k - 1))) (Phi ι N k g0) = b p • Phi ι N k g0 := by
    intro p
    have := congr_arg Subtype.val (heig p)
    rw [hT, Submodule.coe_smul] at this
    rw [hPg]
    exact this
  have hc1 : coef g0 1 ≠ 0 := by
    intro hz
    apply hne
    have hzero : Phi ι N k g0 = 0 :=
      eq_zero_of_eig (fun p => ι.symm (χ p.1 * (p.1 : ℂ) ^ (k - 1))) b _
        (by rw [Phi_apply, if_pos rfl])
        (by rw [Phi_apply, if_neg one_ne_zero, hz, map_zero]) heig'
    exact Subtype.ext (by rw [Submodule.coe_zero, ← hPg, hzero])
  have hrel : ∀ p (hp : p.Prime) n, 1 ≤ n →
      coef g0 (p * n) + χ p * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef g0 (n / p) else 0)
        = ι (b ⟨p, hp⟩) * coef g0 n := by
    intro p hp n hn
    have := congr_fun (heig' ⟨p, hp⟩) n
    dsimp only at this
    rw [fT_Phi ι N k g0 hp _ hn, Pi.smul_apply, Phi_apply, if_neg (show n ≠ 0 by omega), smul_eq_mul] at this
    apply ι.symm.injective
    rw [this, map_mul, RingEquiv.symm_apply_apply]
  set c := coef g0 1 with hcdef
  have hp1 : ∀ p (hp : p.Prime), coef g0 p = ι (b ⟨p, hp⟩) * c := by
    intro p hp
    have := hrel p hp 1 le_rfl
    rwa [mul_one, if_neg (fun h => hp.one_lt.ne' (Nat.dvd_one.mp h)), mul_zero, add_zero] at this
  have hcanc : ∀ x : ℂ, c⁻¹ * (x * c) = x := fun x => by
    rw [mul_comm, mul_assoc, mul_inv_cancel₀ hc1, mul_one]
  let G : CuspForm (Gamma1 N) (k : ℤ) := c⁻¹ • g0
  have hGc : ∀ n, coef G n = c⁻¹ * coef g0 n := fun n => coef_smul _ _ _
  refine ⟨⟨G, (chSub N k χ).smul_mem _ hg0, ?_, ?_⟩, ?_⟩
  · rw [hGc]
    exact inv_mul_cancel₀ hc1
  · intro p hp
    unfold IsEigAt
    intro n hn
    have := hrel p hp n hn
    simp only [hGc]
    rw [hp1 p hp, hcanc]
    split_ifs at this ⊢
    · linear_combination c⁻¹ * this
    · linear_combination c⁻¹ * this
  · intro p hp
    show ‖ι.symm (coef G p - a p)‖ < 1
    rw [hGc, hp1 p hp, hcanc, map_sub, RingEquiv.symm_apply_apply]
    exact hclose ⟨p, hp⟩
