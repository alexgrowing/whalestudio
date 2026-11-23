import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Matrix

variable (D : D7)

def vol {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : IdE D :=
  Submodule.span (𝓞 D.host.E)
    {x | ∃ U : Matrix (Fin N) (Fin N) D.host.E, (∀ j, (fun i => U i j) ∈ L) ∧ x = U.det}

theorem mulVec_col {N : ℕ} (A U : Matrix (Fin N) (Fin N) D.host.E) (j : Fin N) :
    A *ᵥ (fun i => U i j) = fun i => (A * U) i j := by
  funext i
  first
  | rfl
  | simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]

theorem detId_mul_vol_le {N : ℕ} (L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) :
    detId D L L' * vol D L ≤ vol D L' := by
  unfold detId vol
  rw [Submodule.span_mul_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, ⟨A, hA, rfl⟩, y, ⟨U, hU, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨A * U, fun j => ?_, (Matrix.det_mul A U).symm⟩
  have h := hA _ (hU j)
  rwa [mulVec_col] at h

theorem cS_span_le (S : Set D.host.E) :
    CU.cS D (Submodule.span (𝓞 D.host.E) S) ≤ Submodule.span (𝓞 D.host.E) (D.host.conj '' S) := by
  intro x hx
  have hx' : D.host.conj x ∈ Submodule.span (𝓞 D.host.E) S := hx
  have key : ∀ y ∈ Submodule.span (𝓞 D.host.E) S,
      D.host.conj y ∈ Submodule.span (𝓞 D.host.E) (D.host.conj '' S) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [CU.conj_smul]; exact Submodule.smul_mem _ _ ha
  have h := key _ hx'
  rwa [Formalism.HC.HostRaw.conj_conj] at h

theorem cS_cS (𝔞 : IdE D) : CU.cS D (CU.cS D 𝔞) = 𝔞 := by
  ext x
  show D.host.conj (D.host.conj x) ∈ 𝔞 ↔ x ∈ 𝔞
  rw [Formalism.HC.HostRaw.conj_conj]

theorem vol_mul_cS_le {N : ℕ} (L L' : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; ∀ x ∈ L, ∀ w ∈ L,
      stdH D.host.E N w x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    vol D L' * CU.cS D (vol D L) ≤ detId D L L' := by
  let _ := D.host.cmStar
  refine (mul_le_mul' (le_refl _) (cS_span_le D _)).trans ?_
  unfold vol detId
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨V, hV, rfl⟩, _, ⟨_, ⟨W, hW, rfl⟩, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨V * Wᴴ, fun x hx => ?_, ?_⟩
  · have hc : ∀ i, ∃ r : 𝓞 D.host.E, algebraMap _ _ r = (Wᴴ *ᵥ x) i := by
      intro i
      obtain ⟨r, hr⟩ := hL x hx _ (hW i)
      refine ⟨r, hr.trans ?_⟩
      simp [stdH, Matrix.mulVec, dotProduct, conjTranspose_apply]
    choose r hr using hc
    have e : (V * Wᴴ) *ᵥ x = ∑ i, r i • (fun k => V k i) := by
      rw [← mulVec_mulVec]
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hr i, mul_comm]
      rfl
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hV i)
  · rw [det_mul, det_conjTranspose, CU.star_conj]

theorem vol_mul_cS_le_one {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; ∀ x ∈ L, ∀ w ∈ L,
      stdH D.host.E N w x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    vol D L * CU.cS D (vol D L) ≤ 1 := by
  let _ := D.host.cmStar
  refine (mul_le_mul' (le_refl _) (cS_span_le D _)).trans ?_
  unfold vol
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨V, hV, rfl⟩, _, ⟨_, ⟨W, hW, rfl⟩, rfl⟩, rfl⟩
  have hc : ∀ i j, ∃ r : 𝓞 D.host.E, algebraMap _ _ r = (Wᴴ * V) i j := by
    intro i j
    obtain ⟨r, hr⟩ := hL _ (hV j) _ (hW i)
    refine ⟨r, hr.trans ?_⟩
    simp [stdH, Matrix.mul_apply, conjTranspose_apply]
  choose r hr using hc
  have e : Wᴴ * V = (Matrix.of r).map (algebraMap (𝓞 D.host.E) D.host.E) := by
    ext i j; simp [hr]
  show _ ∈ (1 : IdE D)
  rw [Submodule.mem_one, ← CU.star_conj, ← det_conjTranspose]
  refine ⟨(Matrix.of r).det, ?_⟩
  have h2 : algebraMap (𝓞 D.host.E) D.host.E (Matrix.of r).det = (Wᴴ * V).det := by
    rw [e, RingHom.map_det]; rfl
  rw [h2, det_mul]
  exact mul_comm _ _

theorem sd_int {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) :
    letI := D.host.cmStar; ∀ x ∈ L, ∀ w ∈ L,
      stdH D.host.E N w x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  intro x hx w hw
  exact (hL.2.2 x).1 hx w hw

def UnitDisc (D : D7) : Prop :=
  let _ := D.host.cmStar
  ∀ N (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), IsSDLat D.host.E N L →
    1 ≤ vol D L * CU.cS D (vol D L)

theorem determinant_norm_one_of_unit_disc (hU : UnitDisc D) : DetIdealsKernelNormOne D := by
  intro N L L' _ hL hL'
  have mulc : ∀ 𝔞 𝔟 : IdE D, CU.cS D 𝔞 * CU.cS D 𝔟 ≤ CU.cS D (𝔞 * 𝔟) := by
    intro 𝔞 𝔟
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    show D.host.conj (x * y) ∈ 𝔞 * 𝔟
    rw [map_mul]
    exact Submodule.mul_mem_mul hx hy
  have mono : ∀ 𝔞 𝔟 : IdE D, 𝔞 ≤ 𝔟 → CU.cS D 𝔞 ≤ CU.cS D 𝔟 := fun 𝔞 𝔟 h x hx => h hx
  have mm : ∀ a b c d : IdE D, a ≤ b → c ≤ d → a * c ≤ b * d := fun a b c d h h' =>
    Submodule.mul_le.2 fun x hx y hy => Submodule.mul_mem_mul (h hx) (h' hy)
  have h1 : 1 ≤ vol D L * CU.cS D (vol D L) := hU N L hL
  have h1' : 1 ≤ vol D L' * CU.cS D (vol D L') := hU N L' hL'
  have h2 : vol D L' * CU.cS D (vol D L') ≤ 1 := vol_mul_cS_le_one D L' (sd_int D hL')
  have h3 : vol D L' * CU.cS D (vol D L) ≤ detId D L L' := vol_mul_cS_le D L L' (sd_int D hL)
  have h4 : detId D L L' * vol D L ≤ vol D L' := detId_mul_vol_le D L L'
  refine ⟨CU.cS D (detId D L L'), fun x => Iff.rfl, le_antisymm ?_ ?_⟩
  · calc detId D L L' * CU.cS D (detId D L L')
          = detId D L L' * CU.cS D (detId D L L') * 1 := (mul_one _).symm
      _ ≤ detId D L L' * CU.cS D (detId D L L') * (vol D L * CU.cS D (vol D L)) :=
          mm _ _ _ _ le_rfl h1
      _ = (detId D L L' * vol D L) * (CU.cS D (detId D L L') * CU.cS D (vol D L)) := by ring
      _ ≤ vol D L' * CU.cS D (detId D L L' * vol D L) := mm _ _ _ _ h4 (mulc _ _)
      _ ≤ vol D L' * CU.cS D (vol D L') := mm _ _ _ _ le_rfl (mono _ _ h4)
      _ ≤ 1 := h2
  · calc (1 : IdE D) = 1 * 1 := (mul_one _).symm
      _ ≤ (vol D L' * CU.cS D (vol D L')) * (vol D L * CU.cS D (vol D L)) :=
          mm _ _ _ _ h1' h1
      _ = (vol D L' * CU.cS D (vol D L)) * (CU.cS D (vol D L') * vol D L) := by ring
      _ = (vol D L' * CU.cS D (vol D L)) * (CU.cS D (vol D L') * CU.cS D (CU.cS D (vol D L))) := by
          rw [cS_cS]
      _ ≤ (vol D L' * CU.cS D (vol D L)) * CU.cS D (vol D L' * CU.cS D (vol D L)) :=
          mm _ _ _ _ le_rfl (mulc _ _)
      _ ≤ detId D L L' * CU.cS D (detId D L L') := mm _ _ _ _ h3 (mono _ _ h3)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Matrix

variable (D : D7)

theorem adj_step {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (U : Matrix (Fin N) (Fin N) D.host.E) (hU : ∀ j, (fun i => U i j) ∈ L) (t : Fin N → D.host.E)
    (ht : ∀ i, ∀ b ∈ CU.cS D (vol D L), t i * b ∈ (1 : IdE D)) :
    D.host.conj U.det ^ (N - 1) * ∏ i, t i ∈ vol D L := by
  let _ := D.host.cmStar
  refine Submodule.subset_span ⟨(adjugate U)ᴴ * diagonal t, fun i => ?_, ?_⟩
  · refine (hL.2.2 _).2 fun x hx => ?_
    have hdet : (U.updateCol i x).det ∈ vol D L := by
      refine Submodule.subset_span ⟨U.updateCol i x, fun j => ?_, rfl⟩
      by_cases hj : j = i
      · subst hj; convert hx using 1; funext k; simp
      · convert hU j using 1; funext k; simp [hj]
    have hb : star (U.updateCol i x).det ∈ CU.cS D (vol D L) := by
      rw [CU.mem_cS, ← CU.star_conj, star_star]; exact hdet
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (ht i _ hb)
    refine ⟨r, hr.trans ?_⟩
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    simp only [stdH, Matrix.mulVec, dotProduct, star_sum, star_mul, mul_diagonal,
      conjTranspose_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · rw [det_mul, det_diagonal, det_conjTranspose, det_adjugate, Fintype.card_fin, star_pow,
      CU.star_conj]

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Matrix nonZeroDivisors

open FractionalIdeal in

theorem spanPow {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) (S : Set K)
    (hIS : (I : Submodule R K) = Submodule.span R S) (k : ℕ) :
    (I : Submodule R K) ^ k ≤ Submodule.span R ((fun s => s ^ k) '' S) := by
  have mmR : ∀ A B C : FractionalIdeal R⁰ K, A ≤ B → A * C ≤ B * C := by
    intro A B C h
    rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_mul]
    exact Submodule.mul_le.2 fun x hx y hy =>
      Submodule.mul_mem_mul (FractionalIdeal.coe_le_coe.2 h hx) hy
  have hJle : Submodule.span R ((fun s => s ^ k) '' S) ≤
      ((I ^ k : FractionalIdeal R⁰ K) : Submodule R K) := by
    rw [FractionalIdeal.coe_pow, Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    have hsI : s ∈ (I : Submodule R K) := by
      rw [hIS]
      exact Submodule.subset_span hs
    first
    | exact Submodule.pow_mem_pow hsI k
    | exact Submodule.pow_mem_pow _ hsI k
  let J : FractionalIdeal R⁰ K := ⟨_, FractionalIdeal.isFractional_of_le hJle⟩
  have hJ : (J : Submodule R K) = Submodule.span R ((fun s => s ^ k) '' S) := rfl
  rw [← hJ, ← FractionalIdeal.coe_pow, FractionalIdeal.coe_le_coe]
  have hIk : I ^ k ≠ 0 := pow_ne_zero _ hI
  have hJIk : J ≤ I ^ k := hJle
  have hC1 : J * (I ^ k)⁻¹ ≤ 1 := by
    calc J * (I ^ k)⁻¹ ≤ I ^ k * (I ^ k)⁻¹ := mmR _ _ _ hJIk
      _ = 1 := mul_inv_cancel₀ hIk
  by_cases h1 : J * (I ^ k)⁻¹ = 1
  · refine le_of_eq ?_
    calc I ^ k = J * (I ^ k)⁻¹ * I ^ k := by rw [h1, one_mul]
      _ = J := by rw [mul_assoc, inv_mul_cancel₀ hIk, mul_one]
  · exfalso
    obtain ⟨𝔠, h𝔠⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hC1
    have h𝔠top : 𝔠 ≠ ⊤ := by
      rintro rfl
      apply h1
      rw [← h𝔠, FractionalIdeal.coeIdeal_top]
    obtain ⟨P, hPmax, hcP⟩ := Ideal.exists_le_maximal 𝔠 h𝔠top
    haveI := hPmax.isPrime
    have key : ∀ s ∈ S, FractionalIdeal.spanSingleton R⁰ s ≤ (P : FractionalIdeal R⁰ K) * I := by
      intro s hs
      have hsI : FractionalIdeal.spanSingleton R⁰ s ≤ I := by
        rw [FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.mem_coe, hIS]
        exact Submodule.subset_span hs
      have hA1 : FractionalIdeal.spanSingleton R⁰ s * I⁻¹ ≤ 1 := by
        calc FractionalIdeal.spanSingleton R⁰ s * I⁻¹ ≤ I * I⁻¹ := mmR _ _ _ hsI
          _ = 1 := mul_inv_cancel₀ hI
      obtain ⟨a, ha⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hA1
      have hak : a ^ k ≤ P := by
        have h2 : ((a ^ k : Ideal R) : FractionalIdeal R⁰ K) ≤ (𝔠 : FractionalIdeal R⁰ K) := by
          rw [FractionalIdeal.coeIdeal_pow, ha, h𝔠, mul_pow, FractionalIdeal.spanSingleton_pow,
            inv_pow]
          refine mmR _ _ _ ?_
          rw [FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.mem_coe]
          exact Submodule.subset_span ⟨s, hs, rfl⟩
        exact le_trans ((FractionalIdeal.coeIdeal_le_coeIdeal K).1 h2) hcP
      have haP : a ≤ P := by
        first
        | exact Ideal.IsPrime.le_of_pow_le hak
        | exact hPmax.isPrime.le_of_pow_le hak
      calc FractionalIdeal.spanSingleton R⁰ s
            = FractionalIdeal.spanSingleton R⁰ s * I⁻¹ * I := by
              rw [mul_assoc, inv_mul_cancel₀ hI, mul_one]
        _ = (a : FractionalIdeal R⁰ K) * I := by rw [ha]
        _ ≤ (P : FractionalIdeal R⁰ K) * I :=
            mmR _ _ _ ((FractionalIdeal.coeIdeal_le_coeIdeal K).2 haP)
    have hIle : I ≤ (P : FractionalIdeal R⁰ K) * I := by
      rw [← FractionalIdeal.coe_le_coe, hIS, Submodule.span_le]
      intro s hs
      exact FractionalIdeal.spanSingleton_le_iff_mem.1 (key s hs)
    have hPI : (P : FractionalIdeal R⁰ K) * I ≤ I := by
      calc (P : FractionalIdeal R⁰ K) * I ≤ 1 * I := mmR _ _ _ FractionalIdeal.coeIdeal_le_one
        _ = I := one_mul _
    have heq : (P : FractionalIdeal R⁰ K) * I = 1 * I := by
      rw [one_mul]
      exact le_antisymm hPI hIle
    have hP1 : (P : FractionalIdeal R⁰ K) = 1 := mul_right_cancel₀ hI heq
    rw [FractionalIdeal.coeIdeal_eq_one] at hP1
    exact hPmax.ne_top (hP1.trans Ideal.one_eq_top)

variable (D : D7)

theorem cS_span (S : Set D.host.E) :
    CU.cS D (Submodule.span (𝓞 D.host.E) S) = Submodule.span (𝓞 D.host.E) (D.host.conj '' S) := by
  refine le_antisymm (cS_span_le D S) ?_
  refine Submodule.span_le.2 ?_
  rintro _ ⟨s, hs, rfl⟩
  show D.host.conj (D.host.conj s) ∈ Submodule.span (𝓞 D.host.E) S
  rw [Formalism.HC.HostRaw.conj_conj]
  exact Submodule.subset_span hs

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Matrix nonZeroDivisors FractionalIdeal

variable (D : D7)

theorem unitDisc : UnitDisc D := by
  intro N L hL
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : (1 : D.host.E) ∈ vol D L :=
      Submodule.subset_span ⟨1, fun j => j.elim0, Matrix.det_one.symm⟩
    have h2 : (1 : D.host.E) ∈ CU.cS D (vol D L) := by
      show D.host.conj 1 ∈ vol D L
      rw [map_one]
      exact h1
    rw [Submodule.one_le]
    simpa using Submodule.mul_mem_mul h1 h2
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  obtain ⟨U0, hU0, hdet⟩ : ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) D.host.E,
      (∀ j, (fun i => U i j) ∈ L) ∧ U.det ≠ 0 := by
    obtain ⟨b, hbL, hbspan, hbli⟩ := exists_linearIndependent D.host.E (L : Set (Fin (n + 1) → D.host.E))
    have hsp : ⊤ ≤ Submodule.span D.host.E (Set.range ((↑) : b → (Fin (n + 1) → D.host.E))) := by
      rw [Subtype.range_coe, hbspan]
      exact hL.2.1.ge
    let B := Module.Basis.mk hbli hsp
    let e := B.indexEquiv (Pi.basisFun D.host.E (Fin (n + 1)))
    let B' := B.reindex e
    refine ⟨fun i j => B' j i, fun j => ?_, ?_⟩
    · have hBj : B' j = ((e.symm j : b) : Fin (n + 1) → D.host.E) := by
        simp [B', B, Module.Basis.reindex_apply, Module.Basis.mk_apply]
      show B' j ∈ L
      rw [hBj]
      exact hbL (e.symm j).2
    · have h := (Pi.basisFun D.host.E (Fin (n + 1))).isUnit_det B'
      rw [Module.Basis.det_apply] at h
      have hm : (Pi.basisFun D.host.E (Fin (n + 1))).toMatrix B' = fun i j => B' j i := by
        ext i j
        simp [Module.Basis.toMatrix_apply]
      rw [hm] at h
      exact h.ne_zero
  have hfrac : IsFractional (𝓞 D.host.E)⁰ (CU.cS D (vol D L)) := by
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) U0.det
    have hd0 : U0.det ∈ vol D L := Submodule.subset_span ⟨U0, hU0, rfl⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_div] at hxy
      exact hdet hxy.symm
    have hyne : algebraMap (𝓞 D.host.E) D.host.E y ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    refine ⟨x, mem_nonZeroDivisors_of_ne_zero hx0, fun c hc => ?_⟩
    have hdc : U0.det * c ∈ (1 : IdE D) :=
      vol_mul_cS_le_one D L (sd_int D hL) (Submodule.mul_mem_mul hd0 hc)
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hdc
    refine ⟨y * r, ?_⟩
    rw [Algebra.smul_def, map_mul, hr, ← hxy]
    field_simp
  let I'F : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E := ⟨CU.cS D (vol D L), hfrac⟩
  have hne : I'F ≠ 0 := by
    intro h0
    have hm : D.host.conj U0.det ∈ (I'F : Submodule (𝓞 D.host.E) D.host.E) := by
      show D.host.conj (D.host.conj U0.det) ∈ vol D L
      rw [Formalism.HC.HostRaw.conj_conj]
      exact Submodule.subset_span ⟨U0, hU0, rfl⟩
    rw [h0, FractionalIdeal.coe_zero, Submodule.mem_bot] at hm
    exact hdet (by simpa using hm)
  have hI' : (I'F : Submodule (𝓞 D.host.E) D.host.E) =
      Submodule.span (𝓞 D.host.E) (D.host.conj '' {x | ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) D.host.E, (∀ j, (fun i => U i j) ∈ L) ∧ x = U.det}) := cS_span D _
  have hinv : ∀ t ∈ ((I'F⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E),
      ∀ c ∈ CU.cS D (vol D L), t * c ∈ (1 : IdE D) := by
    intro t ht c hc
    have h := (FractionalIdeal.mem_inv_iff hne).1 (FractionalIdeal.mem_coe.1 ht) c
      (FractionalIdeal.mem_coe.1 (show c ∈ (I'F : Submodule (𝓞 D.host.E) D.host.E) from hc))
    have h2 := FractionalIdeal.mem_coe.2 h
    rwa [FractionalIdeal.coe_one] at h2
  have hclaim : ∀ U : Matrix (Fin (n + 1)) (Fin (n + 1)) D.host.E, (∀ j, (fun i => U i j) ∈ L) →
      ∀ x ∈ ((I'F⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ^ (n + 1),
      D.host.conj U.det ^ (n + 1 - 1) * x ∈ vol D L := by
    intro U hU x hx
    rw [Submodule.pow_eq_span_pow_set] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, rfl⟩ := Set.mem_pow.1 hy
      rw [List.prod_ofFn]
      exact adj_step D L hL U hU (fun i => (f i : D.host.E)) (fun i => hinv _ (f i).2)
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ r ha
  have hA := spanPow I'F hne _ hI' (n + 1 - 1)
  have hC : (I'F : Submodule (𝓞 D.host.E) D.host.E) ^ (n + 1 - 1) *
      ((I'F⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) ^ (n + 1)
        ≤ vol D L := by
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    have hx' := hA hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, ⟨d, ⟨U, hU, rfl⟩, rfl⟩, rfl⟩ := hz
      exact hclaim U hU y hy
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha
  have hD : ((I'F⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)
      ≤ vol D L := by
    have heq : I'F ^ (n + 1 - 1) * I'F⁻¹ ^ (n + 1) = I'F⁻¹ := by
      rw [Nat.add_sub_cancel, pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hne, one_pow,
        one_mul]
    rw [← heq, FractionalIdeal.coe_mul, FractionalIdeal.coe_pow, FractionalIdeal.coe_pow]
    exact hC
  calc (1 : IdE D)
        = ((I'F⁻¹ * I'F : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) := by
          rw [inv_mul_cancel₀ hne, FractionalIdeal.coe_one]
    _ = ((I'F⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) *
          (I'F : Submodule (𝓞 D.host.E) D.host.E) := FractionalIdeal.coe_mul _ _
    _ ≤ vol D L * CU.cS D (vol D L) :=
        Submodule.mul_le.2 fun x hx y hy => Submodule.mul_mem_mul (hD hx) hy

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.DN

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem relative_determinant_norm_one (D : D7) : DetIdealsKernelNormOne D := DN.determinant_norm_one_of_unit_disc D (DN.unitDisc D)

theorem character_unit_on_determinant (D : D7) (χ : IdE D → ℂ) (hχ : IsChi D χ) : ChiUnitDet D χ :=
  chi_unit_of_det_norm_one D (relative_determinant_norm_one D) χ hχ

theorem LinkThIndep_of_IopIso
    (hI : ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      IopIso D (tor0 D cc δ)) :
    LinkThIndep :=
  theta_norm_indep_of_det_norm_one hI relative_determinant_norm_one

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
