import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLPrincipalCongruenceOfColsCong
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfAdelicIntegralAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevFrame

open Matrix GlobalTheory.CplPt
open scoped TensorProduct

section Inv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_coprime_dvd (q : ℕ) : ∀ N : ℕ, 0 < N → ∃ s e : ℕ, Nat.Coprime s q ∧ N ∣ s * q ^ e := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    by_cases hc : Nat.Coprime N q
    · exact ⟨N, 0, hc, by simp⟩
    · set g := Nat.gcd N q with hg
      have hg1 : 1 < g := by
        have : g ≠ 0 := by rw [hg]; exact Nat.gcd_ne_zero_left hN.ne'
        have h2 : g ≠ 1 := hc
        omega
      have hgN : g ∣ N := Nat.gcd_dvd_left N q
      have hgq : g ∣ q := Nat.gcd_dvd_right N q
      obtain ⟨N₁, hN₁⟩ := hgN
      have hN₁pos : 0 < N₁ := by
        rcases Nat.eq_zero_or_pos N₁ with h | h
        · rw [h, mul_zero] at hN₁; omega
        · exact h
      have hlt : N₁ < N := by
        rw [hN₁]
        calc N₁ = 1 * N₁ := (one_mul _).symm
          _ < g * N₁ := Nat.mul_lt_mul_of_pos_right hg1 hN₁pos
      obtain ⟨s, e, hs, hd⟩ := ih N₁ hlt hN₁pos
      refine ⟨s, e + 1, hs, ?_⟩
      rw [hN₁, pow_succ]
      have : s * (q ^ e * q) = (s * q ^ e) * q := by ring
      rw [this, mul_comm g N₁]
      exact Nat.mul_dvd_mul hd hgq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem intAtA_neg' {P : HeightOneSpectrum (𝓞 E)} {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) :
    IntAtA (F := F) P (-a) := by
  have := intAtA_mul (intAtA_int (F := F) (P := P) (-1)) h
  simpa using this

theorem natCast_notMem (P : HeightOneSpectrum (𝓞 E)) (s : ℕ) (hs : Nat.Coprime s (qOf P)) :
    ((s : ℕ) : 𝓞 E) ∉ P.asIdeal := by
  intro hm
  have hq : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hc : IsCoprime (s : ℤ) (qOf P : ℤ) := Nat.isCoprime_iff_coprime.2 hs
  obtain ⟨u, v, huv⟩ := hc.map (Int.castRingHom (𝓞 E))
  have h1 : (1 : 𝓞 E) ∈ P.asIdeal := by
    rw [← huv]
    simp only [eq_intCast, Int.cast_natCast]
    exact add_mem (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hq)
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem exists_pow_intAtA (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (hn : 1 ≤ n) (b : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    ∃ m : ℕ, IntAtA (F := F) P (iA F E (((qOf P : ℕ) : E) ^ n) ^ m * b) := by
  obtain ⟨N, hN, hNb⟩ := GlobalTheory.PlaceDatum.exists_den_adele (F := F) (E := E) b
  obtain ⟨s, e, hs, hd⟩ := exists_coprime_dvd (qOf P) N hN
  have hd' : N ∣ s * qOf P ^ (n * e) := by
    refine hd.trans (Nat.mul_dvd_mul_left s (Nat.pow_dvd_pow _ ?_))
    calc e = 1 * e := (one_mul e).symm
      _ ≤ n * e := Nat.mul_le_mul_right e hn
  obtain ⟨t, ht⟩ := hd'
  refine ⟨e, (s : 𝓞 E), natCast_notMem P s hs, ?_⟩
  have e1 : iA F E (algebraMap (𝓞 E) E ((s : ℕ) : 𝓞 E)) * (iA F E (((qOf P : ℕ) : E) ^ n) ^ e * b) =
      (t : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * ((N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * b) := by
    have h2 : iA F E (algebraMap (𝓞 E) E ((s : ℕ) : 𝓞 E)) * iA F E (((qOf P : ℕ) : E) ^ n) ^ e =
        ((s * qOf P ^ (n * e) : ℕ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) := by
      rw [map_natCast, map_natCast, ← map_pow, ← pow_mul, map_pow, map_natCast]
      push_cast
      ring
    rw [← mul_assoc, h2, ht]
    push_cast
    ring
  rw [e1]
  exact mul_mem (natCast_mem _ t) hNb

theorem intAtA_pow' {P : HeightOneSpectrum (𝓞 E)} {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) (m : ℕ) :
    IntAtA (F := F) P (a ^ m) := by
  induction m with
  | zero => simpa using intAtA_int (F := F) (P := P) 1
  | succ m ih => rw [pow_succ]; exact intAtA_mul ih h

theorem congAt_inv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N n : ℕ) (P : HeightOneSpectrum (𝓞 E))
    (k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hn : 1 ≤ n) (hk : CongAt P n k) : CongAt P n k⁻¹ := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set c := iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ with hc
  set d := iA F E (((qOf P : ℕ) : E) ^ n) with hdd
  have hdc : d * c = 1 := by
    rw [hc, hdd, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
  have hd : IntAtA (F := F) P d := by
    have := intAtA_int (F := F) (P := P) (((qOf P : ℕ) : 𝓞 E) ^ n)
    simpa [hdd] using this
  set K : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) with hK
  set B : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((k⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) with hB
  have hBK : B * K = 1 := by rw [hB, hK, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hA : ∀ a b, IntAtA (F := F) P (c * (K - 1) a b) := hk

  have hB1 : B = 1 - B * (K - 1) := by rw [Matrix.mul_sub, hBK, Matrix.mul_one]; abel
  have step : ∀ m : ℕ, (∀ a l, IntAtA (F := F) P (d ^ (m + 1) * B a l)) → ∀ a l, IntAtA (F := F) P (d ^ m * B a l) := by
    intro m hm a l
    have hBal : B a l = (1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a l - ∑ j, B a j * (K - 1) j l := by
      conv_lhs => rw [hB1]
      rw [Matrix.sub_apply, Matrix.mul_apply]
    have e : d ^ m * B a l = d ^ m * (1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a l + -(∑ j, (d ^ (m + 1) * B a j) * (c * (K - 1) j l)) := by
      rw [hBal, mul_sub, Finset.mul_sum, sub_eq_add_neg]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      linear_combination (-(d ^ m * B a j * (K - 1) j l)) * hdc
    rw [e]
    refine intAtA_add (intAtA_mul (intAtA_pow' hd m) ?_) (intAtA_neg' (intAtA_sum _ _ fun j _ => intAtA_mul (hm a j) (hA j l)))
    rw [Matrix.one_apply]
    split_ifs
    · simpa using intAtA_int (F := F) (P := P) 1
    · simpa using intAtA_int (F := F) (P := P) 0
  have desc : ∀ m : ℕ, (∀ a l, IntAtA (F := F) P (d ^ m * B a l)) → ∀ a l, IntAtA (F := F) P (B a l) := by
    intro m
    induction m with
    | zero => intro hm a l; simpa using hm a l
    | succ m ih => intro hm; exact ih (step m hm)
  have hup : ∀ (m m' : ℕ) (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F), m ≤ m' → IntAtA (F := F) P (d ^ m * x) →
      IntAtA (F := F) P (d ^ m' * x) := by
    intro m m' x hmm h
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmm
    rw [pow_add, mul_comm (d ^ m) (d ^ r), mul_assoc]
    exact intAtA_mul (intAtA_pow' hd r) h
  choose mm hmm using fun (p : Fin N × Fin N) => exists_pow_intAtA (F := F) P n hn (B p.1 p.2)
  set M := ∑ p : Fin N × Fin N, mm p with hM
  have hbig : ∀ a l, IntAtA (F := F) P (d ^ M * B a l) := by
    intro a l
    exact hup (mm (a, l)) M _ (Finset.single_le_sum (fun p _ => Nat.zero_le (mm p)) (Finset.mem_univ (a, l))) (hmm (a, l))
  have hBint := desc M hbig
  intro a b
  have e : iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * (((k⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b =
      -(∑ l, B a l * (c * (K - 1) l b)) := by
    have h2 : ((k⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 = -(B * (K - 1)) := by
      rw [Matrix.mul_sub, hBK, Matrix.mul_one]; abel
    rw [h2, Matrix.neg_apply, Matrix.mul_apply, ← hc, mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [e]
  exact intAtA_neg' (intAtA_sum _ _ fun l _ => intAtA_mul (hBint a l) (hA l b))

end Inv

theorem intAt_of_seam {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) (z : X.E)
    (h : IntAt (seamP s P) (s.iE z)) : IntAt P z := by
  obtain ⟨r, c, hc, e⟩ := h
  set f := RingOfIntegers.mapRingEquiv s.iE
  refine ⟨f.symm r, f.symm c, fun hm => hc ?_, ?_⟩
  · have := (mem_seamP s P (f.symm c)).2 hm
    rwa [show (RingOfIntegers.mapRingEquiv s.iE) (f.symm c) = c from f.apply_symm_apply c] at this
  · apply s.iE.injective
    rw [map_mul]
    have h1 : ∀ w : 𝓞 D.host.E, s.iE (algebraMap (𝓞 X.E) X.E (f.symm w)) = algebraMap (𝓞 D.host.E) D.host.E w := by
      intro w
      have h2 : ∀ x : 𝓞 X.E, s.iE (algebraMap (𝓞 X.E) X.E x) = algebraMap (𝓞 D.host.E) D.host.E (f x) := fun x => rfl
      rw [h2, f.apply_symm_apply]
    rw [h1, h1, e]

theorem cols_of_congAt {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (c : ℕ)
    (m : Sp X.E n ≃ₗ[X.E] Sp X.E n) (h : CongAt (F := D.host.F) (seamP s P) c (ratA D.host.F (seamGL s m))) (j l : Fin n) :
    IntAt P (((qOf P : X.E) ^ c)⁻¹ * (m (Pi.single j (1 : X.E)) l - (Pi.single j (1 : X.E) : Sp X.E n) l)) := by
  refine intAt_of_seam s P _ (GlobalTheory.RatInt.intAt_of_intAtA (F := D.host.F) _ _ ?_)
  have e1 : ((seamGL s m : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) l j = s.iE (m (Pi.single j 1) l) := by
    show ((LinearMap.toMatrix' m.toLinearMap).map (s.iE : X.E →+* D.host.E)) l j = _
    rw [Matrix.map_apply, LinearMap.toMatrix'_apply]
    rfl
  convert h l j using 1
  rw [Matrix.sub_apply, GlobalTheory.CplPt.ratA_apply, e1, map_mul, map_inv₀, map_pow, map_natCast, map_sub, MidIndep.qOf_seamP,
    map_mul, map_sub]
  congr 2
  rw [Matrix.one_apply, Pi.single_apply]
  split_ifs <;> simp

set_option maxHeartbeats 1000000 in

theorem frame_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (κ : ((St i hi).K β).lev.U),
    x₁.1 = x.1 * κ.1 → ∀ p p₁, IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ →
    ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ (dep : SB t μ → ℕ), dep P = 1 → ∀ (Gg : GLint t.X.E (D.R.N i) P.1),
      InFrame t.seam (A.fb i hi β) dep P κ.1 Gg.1 →
      ∃ k : GLint t.X.E (D.R.N i) P.1, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 ∧
        redGL _ P.1 k = redGL _ P.1 Gg) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ i hi β x x₁ κ hx p p₁ hp hp₁ P hP dep hdep Gg hin
  have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hP
  set y := ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P) with hy
  set c := (ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P) with hc
  have hy₁ : ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P) = y * c := by
    rw [hx, hy, hc]; group
  have ha : CongAt (seamP t.seam P.1) 1 (y⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p P))) := by
    have h0 := hp.frame P
    rw [hD] at h0
    exact h0
  have hb : CongAt (seamP t.seam P.1) 1 ((y * c)⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p₁ P))) := by
    have h0 := hp₁.frame P
    rw [hD, hy₁] at h0
    exact h0
  have he : CongAt (seamP t.seam P.1) 1 (c⁻¹ * ratA D.host.F (seamGL t.seam Gg.1)) := by
    have h0 := hin
    unfold InFrame NearAt at h0
    rw [hdep] at h0
    exact h0
  set m := (frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P * (Gg⁻¹).1 with hm
  have hM : CongAt (seamP t.seam P.1) 1 (ratA D.host.F (seamGL t.seam m)) := by
    have hGi := GlobalTheory.CplPt.seamGL_int t.seam Gg⁻¹
    have h1 := congAt_inv _ _ _ 1 _ _ le_rfl ha
    have h2 := GlobalTheory.CplPt.congAt_conj 1 (GlobalTheory.CplPt.congAt_mul 1 (congAt_inv _ _ _ 1 _ _ le_rfl he) hb) hGi
    have e : ratA D.host.F (seamGL t.seam m) = (y⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p P)))⁻¹ *
        ((ratA D.host.F (seamGL t.seam (Gg⁻¹).1))⁻¹ * ((c⁻¹ * ratA D.host.F (seamGL t.seam Gg.1))⁻¹ *
          ((y * c)⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p₁ P)))) * ratA D.host.F (seamGL t.seam (Gg⁻¹).1)) := by
      simp only [hm, InvMemClass.coe_inv, map_mul, map_inv]
      group
    rw [e]
    exact GlobalTheory.CplPt.congAt_mul 1 h1 h2
  obtain ⟨hmG, hmC⟩ := GlobalTheory.CongOne.mem_glint_prinCong_of_cols P.1 1 m le_rfl (cols_of_congAt t.seam P.1 1 m hM)
  refine ⟨⟨m, hmG⟩ * Gg, ?_, ?_⟩
  · show _ = _ * (m * Gg.1)
    simp only [hm, InvMemClass.coe_inv]
    group
  · rw [map_mul, redGL_of_prinCong Nat.one_pos hmC, one_mul]

end GlobalTheory.LevFrame
