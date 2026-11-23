import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EigLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DelSerre
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HeckeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FinDim

open Formalism.ConjugateSelfDual CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd
open scoped MatrixGroups ModularForm

noncomputable section

namespace UpperTheory.V.Z.Sym.Unl

private theorem one_mem_per (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
  show (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods
  rw [strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

private theorem coef_smul {N : ℕ} {k : ℤ} (c : ℂ) (f : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (c • f : CuspForm (Gamma1 N) k) n = c * coef f n := by
  unfold coef
  rw [show ((c • f : CuspForm (Gamma1 N) k) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl,
    ModularForm.qExpansion_smul one_pos (one_mem_per N) c f]
  simp

private theorem coef_add {N : ℕ} {k : ℤ} (f g : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (f + g : CuspForm (Gamma1 N) k) n = coef f n + coef g n := by
  show PowerSeries.coeff n (qExpansion 1 ⇑(f + g)) =
    PowerSeries.coeff n (qExpansion 1 ⇑f) + PowerSeries.coeff n (qExpansion 1 ⇑g)
  rw [show ⇑(f + g) = ⇑f + ⇑g from rfl, ModularForm.qExpansion_add one_pos (one_mem_per N) f g, map_add]

private theorem norm_chi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (a : ZMod N) : ‖ι.symm (χ a)‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have hpos : 0 < orderOf u := orderOf_pos u
    have hpow : (χ u) ^ orderOf u = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
    have h1 : ‖ι.symm (χ u)‖ ^ orderOf u = 1 := by
      rw [← norm_pow, ← map_pow, hpow, map_one, norm_one]
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').mp h1)
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
  funext n
  simp only [fT_apply]
  have hqp : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  have dq : ∀ m, q ∣ p * m ↔ q ∣ m := fun m =>
    ⟨fun h => (hq.dvd_mul.mp h).resolve_left hqp, fun h => dvd_mul_of_dvd_right h p⟩
  have dp : ∀ m, p ∣ q * m ↔ p ∣ m := fun m =>
    ⟨fun h => (hp.dvd_mul.mp h).resolve_left hpq', fun h => dvd_mul_of_dvd_right h q⟩
  have hc : q * (p * n) = p * (q * n) := Nat.mul_left_comm q p n
  have hdd : n / p / q = n / q / p := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [hc, hdd]
  simp only [dq, dp]
  by_cases hpn : p ∣ n <;> by_cases hqn : q ∣ n
  · have h1 : q ∣ n / p := (dq _).mp (by rwa [Nat.mul_div_cancel' hpn])
    have h2 : p ∣ n / q := (dp _).mp (by rwa [Nat.mul_div_cancel' hqn])
    simp only [hpn, hqn, h1, h2, ↓reduceIte, Nat.mul_div_assoc p hqn, Nat.mul_div_assoc q hpn]
    ring
  · have h1 : ¬ q ∣ n / p := fun h => hqn (by
      rw [← Nat.mul_div_cancel' hpn]
      exact dvd_mul_of_dvd_right h p)
    simp only [hpn, hqn, h1, ↓reduceIte, Nat.mul_div_assoc q hpn]
    ring
  · have h2 : ¬ p ∣ n / q := fun h => hpn (by
      rw [← Nat.mul_div_cancel' hqn]
      exact dvd_mul_of_dvd_right h q)
    simp only [hpn, hqn, h2, ↓reduceIte, Nat.mul_div_assoc p hqn]
    ring
  · simp only [hpn, hqn, ↓reduceIte]
    ring

private theorem eq_zero_of_eig {K : Type} [Field K] (e b : Nat.Primes → K) (c : ℕ → K) (h0 : c 0 = 0) (h1 : c 1 = 0)
    (h : ∀ p : Nat.Primes, fT p.1 (e p) c = b p • c) : c = 0 := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    show c n = 0
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact h0
      · exact h1
    · have hp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hp2 := hp.two_le
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h' | h'
        · rw [h', mul_zero] at hm
          omega
        · exact h'
      have hmn : m < n := by
        have : 1 * m < Nat.minFac n * m := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        omega
      have hcm : c m = 0 := ih m hmn
      have hcmp : c (m / n.minFac) = 0 := ih _ (lt_of_le_of_lt (Nat.div_le_self _ _) hmn)
      have he := congrFun (h ⟨n.minFac, hp⟩) m
      simp only [fT_apply, Pi.smul_apply, smul_eq_mul, hcm, mul_zero, hcmp, ite_self, add_zero] at he
      rw [hm]
      exact he

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

private theorem coef_zero' {N : ℕ} {k : ℤ} (n : ℕ) : coef (0 : CuspForm (Gamma1 N) k) n = 0 := by
  show PowerSeries.coeff n (qExpansion 1 (0 : ℍ → ℂ)) = 0
  rw [qExpansion_zero]
  simp

private def cjSub (N k : ℕ) (χ : DirichletCharacter ℂ N) : Submodule ℂ (CuspForm (Gamma1 N) (k : ℤ)) where
  carrier := {g | HasChar k χ g ∧ Cj k N χ g}
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨(chSub N k χ).add_mem hf hg, fun σ => ?_⟩
    obtain ⟨f', a1, a2⟩ := hf' σ
    obtain ⟨g', b1, b2⟩ := hg' σ
    refine ⟨f' + g', (chSub N k (cj σ χ)).add_mem a1 b1, fun n hn => ?_⟩
    rw [coef_add, coef_add, a2 n hn, b2 n hn, map_add]
  zero_mem' := by
    refine ⟨(chSub N k χ).zero_mem, fun σ => ⟨0, (chSub N k (cj σ χ)).zero_mem, fun n _ => ?_⟩⟩
    rw [coef_zero', map_zero]
  smul_mem' := by
    rintro c f ⟨hf, hf'⟩
    refine ⟨(chSub N k χ).smul_mem c hf, fun σ => ?_⟩
    obtain ⟨f', a1, a2⟩ := hf' σ
    refine ⟨σ c • f', (chSub N k (cj σ χ)).smul_mem _ a1, fun n hn => ?_⟩
    rw [coef_smul, coef_smul, a2 n hn, map_mul]

private theorem heckeC (N k : ℕ) [NeZero N] (hk : 1 ≤ k) (χ : DirichletCharacter ℂ N)
    (g : CuspForm (Gamma1 N) (k : ℤ)) (hg : g ∈ cjSub N k χ) (p : ℕ) (hp : p.Prime) :
    ∃ g' ∈ cjSub N k χ, ∀ n, 1 ≤ n → coef g' n =
      coef g (p * n) + χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef g (n / p) else 0) := by
  obtain ⟨hgc, hgj⟩ := hg
  obtain ⟨g', hg'c, hg'n⟩ := heckeEx N k hk χ g hgc p hp
  refine ⟨g', ⟨hg'c, fun σ => ?_⟩, hg'n⟩
  obtain ⟨f', hf'c, hf'n⟩ := hgj σ
  obtain ⟨f'', hf''c, hf''n⟩ := heckeEx N k hk (cj σ χ) f' hf'c p hp
  refine ⟨f'', hf''c, fun n hn => ?_⟩
  have hpn : 1 ≤ p * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne_zero (by omega))
  have hcj : (cj σ χ) (p : ZMod N) = σ (χ p) := rfl
  rw [hf''n n hn, hg'n n hn]
  by_cases hd : p ∣ n
  · have hq : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
    simp only [hd, if_true, hf'n _ hq, hf'n _ hpn, hcj, map_add, map_mul, map_pow, map_natCast]
  · simp only [hd, if_false, hf'n _ hpn, hcj, map_add, map_mul, mul_zero, map_zero]

private theorem fT_Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k)
    {p : ℕ} (hp : p.Prime) (e : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    fT p (ι.symm e) (Phi ι N k g) n = ι.symm (coef g (p * n) + e * (if p ∣ n then coef g (n / p) else 0)) := by
  have hn0 : n ≠ 0 := by omega
  have hpn : p * n ≠ 0 := Nat.mul_ne_zero hp.ne_zero hn0
  rw [fT_apply, Phi_apply, if_neg hpn]
  by_cases hd : p ∣ n
  · have hq : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos).ne'
    rw [if_pos hd, if_pos hd, Phi_apply, if_neg hq, map_add, map_mul]
  · rw [if_neg hd, if_neg hd]
    simp

end UpperTheory.V.Z.Sym.Unl

set_option maxHeartbeats 1000000 in
open UpperTheory.V.Z.Sym.Unl in
theorem UpperTheory.V.Z.Sym.Unl.eigLiftC :
    UpperTheory.V.Z.Sym.Unl.EigLiftC := by
  intro l _ ι N k _ hk χ f hfc hfj hfI hf1 a ha
  obtain ⟨e, he_def⟩ : ∃ e : Nat.Primes → Qbar l,
      ∀ p, e p = ι.symm (χ (p.1 : ZMod N) * (p.1 : ℂ) ^ (k - 1)) := ⟨_, fun _ => rfl⟩
  have hfW : f ∈ cjSub N k χ := ⟨hfc, hfj⟩
  have hfd : FiniteDimensional (Qbar l) ((cjSub N k χ).map (Phi ι N k)) := by
    haveI := (finDim N k).1
    exact Module.Finite.iff_fg.mpr ((IsNoetherian.noetherian (cjSub N k χ)).map _)
  have hinv : ∀ p : Nat.Primes, ∀ v ∈ (cjSub N k χ).map (Phi ι N k),
      fT p.1 (e p) v ∈ (cjSub N k χ).map (Phi ι N k) := by
    intro p v hv
    obtain ⟨g, hg, rfl⟩ := hv
    obtain ⟨g', hg', hg'n⟩ := heckeC N k hk χ g hg p.1 p.2
    refine ⟨g', hg', ?_⟩
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Phi_apply, fT_apply]
    · show Phi ι N k g' n = fT p.1 (e p) (Phi ι N k g) n
      rw [he_def p, fT_Phi ι N k g p.2 _ hn, Phi_apply, if_neg (show n ≠ 0 by omega), hg'n n hn]
  have he : ∀ p : Nat.Primes, ‖e p‖ ≤ 1 := by
    intro p
    rw [he_def p, map_mul ι.symm, map_pow ι.symm, map_natCast ι.symm, norm_mul, norm_pow]
    exact mul_le_one₀ (norm_chi ι χ _) (by positivity)
      (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one (Qbar l) _))
  have key : ∀ (p : Nat.Primes) (v : ℕ → Qbar l) (n : ℕ),
      ‖fT p.1 (e p) v n‖ ≤ max ‖v (p.1 * n)‖ (if p.1 ∣ n then ‖v (n / p.1)‖ else 0) := by
    intro p v n
    rw [fT_apply]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max le_rfl ?_)
    split_ifs
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (he p)
    · simp
  let T : Nat.Primes → Module.End (Qbar l) ((cjSub N k χ).map (Phi ι N k)) :=
    fun p => (fT p.1 (e p)).restrict (hinv p)
  have hT : ∀ p v, ((T p v : ↥((cjSub N k χ).map (Phi ι N k))) : ℕ → Qbar l) = fT p.1 (e p) v := fun _ _ => rfl
  have hcomm : ∀ i j, T i * T j = T j * T i := by
    intro i j
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hT, hT, hT, hT]
    by_cases hij : i = j
    · rw [hij]
    · exact fT_comm i.2 j.2 (fun h => hij (Subtype.ext h)) _ _ _
  have hle : ∀ (j : Nat.Primes) (v : ↥((cjSub N k χ).map (Phi ι N k))), (∀ n, ‖(v : ℕ → Qbar l) n‖ ≤ 1) →
      ∀ n, ‖((T j v : ↥((cjSub N k χ).map (Phi ι N k))) : ℕ → Qbar l) n‖ ≤ 1 := by
    intro j v hv n
    rw [hT]
    refine (key j v n).trans (max_le (hv _) ?_)
    split_ifs
    · exact hv _
    · exact zero_le_one
  have hlt : ∀ (j : Nat.Primes) (v : ↥((cjSub N k χ).map (Phi ι N k))), (∀ n, ‖(v : ℕ → Qbar l) n‖ < 1) →
      ∀ n, ‖((T j v : ↥((cjSub N k χ).map (Phi ι N k))) : ℕ → Qbar l) n‖ < 1 := by
    intro j v hv n
    rw [hT]
    refine lt_of_le_of_lt (key j v n) (max_lt (hv _) ?_)
    split_ifs
    · exact hv _
    · exact zero_lt_one
  have hfint : ∀ n, ‖Phi ι N k f n‖ ≤ 1 := by
    intro n
    rw [Phi_apply]
    split_ifs
    · simp
    · exact hfI n
  have hf1' : ‖Phi ι N k f 1‖ = 1 := by
    rw [Phi_apply, if_neg one_ne_zero]
    exact hf1
  let f0 : ↥((cjSub N k χ).map (Phi ι N k)) := ⟨Phi ι N k f, Submodule.mem_map_of_mem hfW⟩
  have happ : ∀ (j : Nat.Primes) (n : ℕ),
      ‖((T j f0 : ↥((cjSub N k χ).map (Phi ι N k))) : ℕ → Qbar l) n - ι.symm (a j.1) * (f0 : ℕ → Qbar l) n‖ < 1 := by
    intro j n
    rw [hT]
    show ‖fT j.1 (e j) (Phi ι N k f) n - ι.symm (a j.1) * Phi ι N k f n‖ < 1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Phi_apply, fT_apply]
    · rw [he_def j, fT_Phi ι N k f j.2 _ hn, Phi_apply, if_neg (show n ≠ 0 by omega), ← map_mul ι.symm, ← map_sub ι.symm]
      exact (ha j.1 j.2).2 n hn
  obtain ⟨h, b, hne, -, hhe, hb⟩ := delSerre l ℕ Nat.Primes ((cjSub N k χ).map (Phi ι N k)) hfd T hcomm hle hlt
    f0 (fun p => ι.symm (a p.1)) hfint ⟨1, hf1'⟩ (fun p => (ha p.1 p.2).1) happ
  obtain ⟨g, hgW, hgh⟩ := h.2
  have hev : ∀ p : Nat.Primes, fT p.1 (e p) (Phi ι N k g) = b p • Phi ι N k g := by
    intro p
    rw [hgh, ← hT]
    exact congrArg Subtype.val (hhe p)
  have hc1 : coef g 1 ≠ 0 := by
    intro hz
    apply hne
    apply Subtype.ext
    show (h : ℕ → Qbar l) = 0
    rw [← hgh]
    refine eq_zero_of_eig e b _ ?_ ?_ hev
    · rw [Phi_apply, if_pos rfl]
    · rw [Phi_apply, if_neg one_ne_zero, hz, map_zero]
  have heig : ∀ p (hp : p.Prime) n, 1 ≤ n →
      coef g (p * n) + χ p * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef g (n / p) else 0) =
        ι (b ⟨p, hp⟩) * coef g n := by
    intro p hp n hn
    have h1 := congrFun (hev ⟨p, hp⟩) n
    change fT p (e ⟨p, hp⟩) (Phi ι N k g) n = b ⟨p, hp⟩ * Phi ι N k g n at h1
    rw [he_def ⟨p, hp⟩, fT_Phi ι N k g hp _ hn, Phi_apply, if_neg (show n ≠ 0 by omega)] at h1
    have h2 := congrArg ι h1
    rwa [RingEquiv.apply_symm_apply, map_mul ι, RingEquiv.apply_symm_apply] at h2
  have hlam : ∀ p (hp : p.Prime), (coef g 1)⁻¹ * coef g p = ι (b ⟨p, hp⟩) := by
    intro p hp
    have h1 := heig p hp 1 le_rfl
    rw [mul_one, if_neg hp.not_dvd_one, mul_zero, add_zero] at h1
    rw [h1, mul_comm, mul_assoc, mul_inv_cancel₀ hc1, mul_one]
  have hg1W : (coef g 1)⁻¹ • g ∈ cjSub N k χ := (cjSub N k χ).smul_mem _ hgW
  refine ⟨⟨(coef g 1)⁻¹ • g, hg1W.1, ?_, ?_⟩, hg1W.2, fun p hp => ?_⟩
  · rw [coef_smul]
    exact inv_mul_cancel₀ hc1
  · intro p hp n hn
    simp only [coef_smul]
    rw [hlam p hp]
    have hr : (coef g 1)⁻¹ * coef g (p * n) + χ p * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then (coef g 1)⁻¹ * coef g (n / p) else 0) =
        (coef g 1)⁻¹ * (coef g (p * n) + χ p * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then coef g (n / p) else 0)) := by
      split_ifs <;> ring
    rw [hr, heig p hp n hn]
    ring
  · show ‖ι.symm (coef ⇑((coef g 1)⁻¹ • g) p - a p)‖ < 1
    rw [coef_smul, hlam p hp, map_sub ι.symm, RingEquiv.symm_apply_apply]
    exact hb ⟨p, hp⟩
