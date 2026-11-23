import Formalism.LocalToGlobal.InertKernelTheory.DefsFrONB
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.KappaSelfDualFourthPowerLattice
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.CurveIdealPrimeReduction
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgGr
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ReBase
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.FinalFree
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.MemLatticeFourfoldOfMemDualLattice
import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfTrace
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert

open Formalism.MainNotions Formalism.L2.Ker
open Formalism.L2.Th1.H (matH stdH stdLat pow4 imgLat relIdx blk4 IsIsom slice)

namespace FrRat

variable (D : D7)

theorem lamOf_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    ∀ w ∈ TaylorLogMetric.lamOf D cc δ, ∃ c ∈ cc, w = δ * D.host.φ₀ (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) := by
  intro w hw
  let S : AddSubgroup ℂ :=
    { carrier := {w | ∃ c ∈ cc, w = δ * D.host.φ₀ (((c : 𝓞 D.host.K) : D.host.K) : D.host.E)}
      add_mem' := fun {a b} ha hb => by
        obtain ⟨c, hc, rfl⟩ := ha
        obtain ⟨c', hc', rfl⟩ := hb
        exact ⟨c + c', cc.add_mem hc hc', by push_cast; rw [map_add]; ring⟩
      zero_mem' := ⟨0, cc.zero_mem, by simp⟩
      neg_mem' := fun {a} ha => by
        obtain ⟨c, hc, rfl⟩ := ha
        exact ⟨-c, cc.neg_mem hc, by push_cast; rw [map_neg]; ring⟩ }
  have hle : TaylorLogMetric.lamOf D cc δ ≤ S := by
    unfold TaylorLogMetric.lamOf
    rw [AddSubgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩
  exact hle hw

theorem okE (c : 𝓞 D.host.K) : IsIntegral ℤ (((c : D.host.K) : D.host.E)) := by
  have h := (RingOfIntegers.isIntegral_coe c).map (IsScalarTower.toAlgHom ℤ D.host.K D.host.E)
  simpa using h

theorem order_ideal_smul_mem (c : 𝓞 D.host.K) {a : D.host.E} (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    ((c : D.host.K) : D.host.E) * a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  have h := Submodule.smul_mem _ (⟨((c : D.host.K) : D.host.E), okE D c⟩ : 𝓞 D.host.E) ha
  exact h

theorem lamMM_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    ∀ z ∈ lamMM D (TaylorLogMetric.lamOf D cc δ), ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      z = fun τ => δ * TaylorLogMetric.embT D τ a := by
  intro z hz
  let S : AddSubgroup (D.what₂.Tau → ℂ) :=
    { carrier := {z | ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), z = fun τ => δ * TaylorLogMetric.embT D τ a}
      add_mem' := fun {x y} hx hy => by
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨a', ha', rfl⟩ := hy
        refine ⟨a + a', Submodule.add_mem _ ha ha', ?_⟩
        funext τ; simp only [Pi.add_apply, map_add]; ring
      zero_mem' := ⟨0, Submodule.zero_mem _, by funext τ; simp⟩
      neg_mem' := fun {x} hx => by
        obtain ⟨a, ha, rfl⟩ := hx
        refine ⟨-a, Submodule.neg_mem _ ha, ?_⟩
        funext τ; simp only [Pi.neg_apply, map_neg]; ring }
  have hle : lamMM D (TaylorLogMetric.lamOf D cc δ) ≤ S := by
    show AddSubgroup.closure _ ≤ S
    rw [AddSubgroup.closure_le]
    rintro _ ⟨w, hw, a, ha, rfl⟩
    obtain ⟨c, -, rfl⟩ := lamOf_mem D cc δ w hw
    refine ⟨((c : D.host.K) : D.host.E) * a, order_ideal_smul_mem D c ha, ?_⟩
    funext τ
    rw [map_mul, IntegralOrthonormalChange.embT_K D τ _ (SetLike.coe_mem _)]
    ring
  exact hle hz

theorem order_ideal_mem_one_by_one {a : D.host.E} (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    (fun _ _ => a : Matrix (Fin 1) (Fin 1) D.host.E) ∈ TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) := by
  apply Submodule.subset_span
  refine ⟨a, ha, 1, Submodule.subset_span (fun x hx => by simpa using hx), ?_⟩
  ext i j
  fin_cases i; fin_cases j
  simp

theorem blockFourfold_hOne_eq_hOne (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] :
    blk4 (hOne L n) = hOne L (Fin 4 × n) := by
  ext ⟨a, i⟩ ⟨c, j⟩
  simp only [blk4, hOne, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
  by_cases hac : a = c <;> by_cases hij : i = j <;> simp [hac, hij]

theorem matH_hOne (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] :
    matH (hOne L n) = Formalism.L2.Th1.H.stdH L n := rfl

theorem stdH_apply' (L : PeriodPair) {N : Type*} [Fintype N] [DecidableEq N] (z w : N → ℂ) :
    Formalism.L2.Th1.H.stdH L N z w = ∑ i, z i * ((Formalism.L2.Th1.F.area L : ℝ) : ℂ)⁻¹ * conj (w i) := by
  simp only [Formalism.L2.Th1.H.stdH, matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem ne_zero_of_coprime {n p : ℕ} (hp : p.Prime) (h : Nat.Coprime n p) : n ≠ 0 := by
  rintro rfl
  rw [Nat.coprime_zero_left] at h
  exact hp.one_lt.ne' h

end FrRat

open FrRat in

theorem rational_coordinates : RatCoord := by
  intro D cc δ B hcc hδ p _ h5 hj g₁ hI hN hM b hb
  have hp : p.Prime := Fact.out
  obtain ⟨cc', δ', hcc', hδ', hcop, hlat⟩ := curve_ideal_prime D cc δ hcc hδ p hj
  set N := relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
    (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) with hNdef
  have hNc : Nat.Coprime N p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hN)
  set A : ℕ := Ideal.absNorm cc' with hAdef
  have hAmem : ((A : ℕ) : 𝓞 D.host.K) ∈ cc' := Ideal.absNorm_mem cc'
  have hL : B.L.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc' δ' := B.lat.trans hlat
  have hωmem : δ' * (A : ℂ) ∈ B.L.lattice := by
    have h : δ' * (A : ℂ) ∈ TaylorLogMetric.lamOf D cc' δ' :=
      AddSubgroup.subset_closure ⟨((A : ℕ) : 𝓞 D.host.K), hAmem, by simp⟩
    rw [← hL] at h
    exact h
  have hδ0 : δ' ≠ 0 := by
    rintro rfl
    have hω1 : B.L.ω₁ ∈ TaylorLogMetric.lamOf D cc' 0 := by
      rw [← hL]; exact B.L.ω₁_mem_lattice
    obtain ⟨c, -, hc⟩ := lamOf_mem D cc' 0 _ hω1
    have hω0 : B.L.ω₁ ≠ 0 := by simpa using B.L.indep.ne_zero 0
    exact hω0 (by rw [hc]; ring)
  have hNA0 : N * A ≠ 0 := ne_zero_of_coprime hp (Nat.Coprime.mul hNc hcop)
  have hlamM : B.lamM = lamMM D (TaylorLogMetric.lamOf D cc' δ') := by
    show lamMM D (TaylorLogMetric.lamOf D cc δ) = _
    rw [hlat]

  have hkey : ∀ (w : Fin 4 × D.what₂.Tau) (i' : Fin 4), ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      ∀ τ, g₁.symm (Pi.single w 1) (i', τ) = TaylorLogMetric.embT D τ (a / ((N * A : ℕ) : D.host.E)) := by
    intro w i'
    have hz : (δ' * (A : ℂ)) • (Pi.single w 1 : Fin 4 × D.what₂.Tau → ℂ) ∈ stdLat B.L (Fin 4 × D.what₂.Tau) := by
      intro x _
      by_cases hx : x = w
      · subst hx; simpa using hωmem
      · simp [hx]
    have hm := Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.idx_smul_symm_mem B.L (hOne B.L D.what₂.Tau) B.lamM
      (Kap.kap_selfDual_lamM B hcc hδ) g₁ hI hz
    have hs : slice i' (g₁.symm (N • (δ' * (A : ℂ)) • (Pi.single w 1 : Fin 4 × D.what₂.Tau → ℂ)))
        ∈ lamMM D (TaylorLogMetric.lamOf D cc' δ') := by
      rw [← hlamM]; exact hm i'
    obtain ⟨a, ha, hae⟩ := lamMM_mem D cc' δ' _ hs
    refine ⟨a, ha, fun τ => ?_⟩
    have h1 := congrFun hae τ
    have e : g₁.symm (N • (δ' * (A : ℂ)) • (Pi.single w 1 : Fin 4 × D.what₂.Tau → ℂ)) =
        ((N : ℂ) * (δ' * (A : ℂ))) • g₁.symm (Pi.single w 1) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, map_smul]
    rw [e] at h1
    simp only [slice, Pi.smul_apply, smul_eq_mul] at h1
    rw [map_div₀, map_natCast, eq_div_iff (by exact_mod_cast hNA0)]
    apply mul_left_cancel₀ hδ0
    push_cast
    linear_combination h1
  choose a ha hau using hkey
  have hY : ∀ (w : Fin 4 × D.what₂.Tau) (i' : Fin 4), ∃ s : ℕ, Nat.Coprime s p ∧
      ∃ d : Fin (Fintype.card D.what₂.Tau) → 𝓞 D.host.K,
      (s : D.host.E) • (fun _ _ => a w i' : Matrix (Fin 1) (Fin 1) D.host.E) =
        ∑ m, (((d m : D.host.K) : D.host.E)) • b m :=
    fun w i' => hb.2.2 _ (order_ideal_mem_one_by_one D (ha w i'))
  choose s hs d hd using hY
  set c : Fin 4 × D.what₂.Tau → Fin 4 → Fin (Fintype.card D.what₂.Tau) → D.host.K :=
    fun w i' m => (d w i' m : D.host.K) / ((s w i' * N * A : ℕ) : D.host.K) with hcdef
  have hS : ∀ w i', Nat.Coprime (s w i' * N * A) p := fun w i' =>
    Nat.Coprime.mul (Nat.Coprime.mul (hs w i') hNc) hcop

  have hX : ∀ w i', ∑ m, ((c w i' m : D.host.K) : D.host.E) * b m 0 0 = a w i' / ((N * A : ℕ) : D.host.E) := by
    intro w i'
    have h00 := congrFun (congrFun (hd w i') 0) 0
    simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Matrix.sum_apply] at h00
    have hs0 : ((s w i' : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast ne_zero_of_coprime hp (hs w i')
    have hNA : ((N * A : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hNA0
    simp only [hcdef]
    push_cast
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, ← h00]
    push_cast
    field_simp
  have hc1 : ∀ w i' τ, g₁.symm (Pi.single w 1) (i', τ) =
      ∑ m, D.host.φ₀ ((c w i' m : D.host.K) : D.host.E) * TaylorLogMetric.embT D τ (b m 0 0) := by
    intro w i' τ
    rw [hau w i' τ, ← hX w i', map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, IntegralOrthonormalChange.embT_K D τ _ (SetLike.coe_mem _)]
  refine ⟨c, hc1, ?_, ?_⟩
  · intro w i' m
    refine ⟨s w i' * N * A, hS w i', ?_⟩
    have hS0 : ((s w i' * N * A : ℕ) : D.host.K) ≠ 0 := by exact_mod_cast ne_zero_of_coprime hp (hS w i')
    simp only [hcdef]
    rw [mul_div_cancel₀ _ hS0]
    exact RingOfIntegers.isIntegral_coe _
  · intro w w'
    have hH : ∑ x, g₁.symm (Pi.single w 1) x * conj (g₁.symm (Pi.single w' 1) x) = if w = w' then 1 else 0 := by
      have h := hI (g₁.symm (Pi.single w 1)) (g₁.symm (Pi.single w' 1))
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h
      rw [FrRat.blockFourfold_hOne_eq_hOne, FrRat.matH_hOne] at h
      rw [FrRat.stdH_apply', FrRat.stdH_apply'] at h
      have ha : ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Formalism.L2.Th1.F.PeriodAreaSignLemmas.area_pos B.L).ne'
      have e2 : ∑ x, g₁.symm (Pi.single w 1) x * conj (g₁.symm (Pi.single w' 1) x) =
          ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) * ∑ x, g₁.symm (Pi.single w 1) x *
            ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ)⁻¹ * conj (g₁.symm (Pi.single w' 1) x) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_; field_simp
      rw [e2, ← h, Finset.sum_eq_single w (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)]
      by_cases hw : w = w'
      · subst hw; simp [ha]
      · simp [hw, Pi.single_apply, Ne.symm hw]
    have hemb : ∀ w i' τ, TaylorLogMetric.embT D τ (∑ m, ((c w i' m : D.host.K) : D.host.E) * b m 0 0) =
        g₁.symm (Pi.single w 1) (i', τ) := by
      intro w i' τ
      rw [hc1, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, IntegralOrthonormalChange.embT_K D τ _ (SetLike.coe_mem _)]
    have hG : ∀ i', D.host.φ₀ (∑ m, ∑ n, ((c w i' m : D.host.K) : D.host.E) *
        ((TaylorLogMetric.hYY D (b m) (b n) : D.host.K) : D.host.E) * D.host.conj ((c w' i' n : D.host.K) : D.host.E)) =
        ∑ τ, g₁.symm (Pi.single w 1) (i', τ) * conj (g₁.symm (Pi.single w' 1) (i', τ)) := by
      intro i'
      have hcomb := IntegralOrthonormalChange.hYY_comb D b (fun m => ((c w i' m : D.host.K) : D.host.E))
        (fun m => ((c w' i' m : D.host.K) : D.host.E)) (fun m => SetLike.coe_mem _) (fun m => SetLike.coe_mem _)
      have e3 : ∑ m, ∑ n, ((c w i' m : D.host.K) : D.host.E) * ((TaylorLogMetric.hYY D (b m) (b n) : D.host.K) : D.host.E) *
          D.host.conj ((c w' i' n : D.host.K) : D.host.E) =
          ((TaylorLogMetric.hYY D (∑ m, ((c w i' m : D.host.K) : D.host.E) • b m)
            (∑ m, ((c w' i' m : D.host.K) : D.host.E) • b m) : D.host.K) : D.host.E) := by
        rw [hcomb]
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
        ring
      rw [e3]
      unfold TaylorLogMetric.hYY
      rw [← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.sum_tau_trace]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [Fin.sum_univ_one, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      rw [map_mul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.emb_conj, hemb, hemb]
    have e4 := hH
    rw [Fintype.sum_prod_type] at e4
    apply D.host.φ₀.injective
    rw [map_sum, Finset.sum_congr rfl (fun i' _ => hG i'), e4]
    split_ifs <;> simp

end Formalism.L2.KerInert
