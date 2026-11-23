import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIffOfCarries
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfOfIsIdemSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.AdForm.DeepMove

section Val
variable {R Γ : Type} [CommRing R] [LinearOrderedCommGroupWithZero Γ] (v : Valuation R Γ)

theorem one_entry_le {n : ℕ} (r s : Fin n) : v ((1 : Matrix (Fin n) (Fin n) R) r s) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem inv_entry_le {n : ℕ} (X Y : Matrix (Fin n) (Fin n) R) (hXY : X * Y = 1) {ε : Γ} (hε : ε < 1)
    (hX : ∀ r s, v ((X - 1) r s) ≤ ε) : ∀ r s, v ((Y - 1) r s) ≤ ε := by
  have hY : Y - 1 = -((X - 1) * Y) := by
    rw [Matrix.sub_mul, hXY, Matrix.one_mul, neg_sub]
  have hb : ∀ r s, v (Y r s) ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨r, s, hrs⟩ := hcon
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun p : Fin n × Fin n => v (Y p.1 p.2))
      ⟨(r, s), Finset.mem_univ _⟩
    have hm : 1 < v (Y p.1 p.2) := lt_of_lt_of_le hrs (hp (r, s) (Finset.mem_univ _))
    have h2 : v ((Y - 1) p.1 p.2) < v (Y p.1 p.2) := by
      rw [hY, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
      refine lt_of_le_of_lt (Valuation.map_sum_le _ (g := ε * v (Y p.1 p.2)) fun k _ => ?_) ?_
      · rw [map_mul]
        exact mul_le_mul' (hX _ _) (hp (k, p.2) (Finset.mem_univ _))
      · exact mul_lt_of_lt_one_left (zero_lt_one.trans hm) hε
    have e : Y p.1 p.2 = (1 : Matrix (Fin n) (Fin n) R) p.1 p.2 + (Y - 1) p.1 p.2 := by
      rw [Matrix.sub_apply]; ring
    have h3 : v (Y p.1 p.2) < v (Y p.1 p.2) := by
      calc v (Y p.1 p.2) = v ((1 : Matrix (Fin n) (Fin n) R) p.1 p.2 + (Y - 1) p.1 p.2) := by rw [← e]
        _ ≤ max (v ((1 : Matrix (Fin n) (Fin n) R) p.1 p.2)) (v ((Y - 1) p.1 p.2)) := Valuation.map_add _ _ _
        _ < v (Y p.1 p.2) := max_lt ((one_entry_le v _ _).trans_lt hm) h2
    exact lt_irrefl _ h3
  intro r s
  rw [hY, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  calc _ ≤ ε * 1 := mul_le_mul' (hX _ _) (hb _ _)
    _ = ε := mul_one _

theorem moved_entry_le {a b : ℕ} (X : Matrix (Fin a) (Fin a) R) (Y : Matrix (Fin b) (Fin b) R) (M : Matrix (Fin b) (Fin a) R)
    {ε : Γ} (hε : ε ≤ 1) (hX : ∀ r s, v ((X - 1) r s) ≤ ε) (hY : ∀ r s, v ((Y - 1) r s) ≤ ε)
    (hM : ∀ r s, v (M r s) ≤ 1) : ∀ r s, v ((Y * M * X - M) r s) ≤ ε := by
  have hXb : ∀ r s, v (X r s) ≤ 1 := fun r s => by
    have e : X r s = (1 : Matrix (Fin a) (Fin a) R) r s + (X - 1) r s := by rw [Matrix.sub_apply]; ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le (one_entry_le v _ _) ((hX r s).trans hε))
  have e : Y * M * X - M = (Y - 1) * M * X + M * (X - 1) := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]; abel
  have h1 : ∀ r s, v (((Y - 1) * M : Matrix (Fin b) (Fin a) R) r s) ≤ ε := fun r s => by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul]
    calc _ ≤ ε * 1 := mul_le_mul' (hY _ _) (hM _ _)
      _ = ε := mul_one _
  intro r s
  rw [e, Matrix.add_apply]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul]
    calc _ ≤ ε * 1 := mul_le_mul' (h1 _ _) (hXb _ _)
      _ = ε := mul_one _
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul]
    calc _ ≤ 1 * ε := mul_le_mul' (hM _ _) (hX _ _)
      _ = ε := one_mul _

end Val

theorem exists_exp_le_natCast {E : Type} [Field E] [NumberField E] (L : ℕ) (hL : 0 < L) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ P : HeightOneSpectrum (𝓞 E),
      WithZero.exp (-(N₀ : ℤ)) ≤ Valued.v ((L : ℕ) : P.adicCompletion E) := by
  set m := Ideal.absNorm (Ideal.span {((L : ℕ) : 𝓞 E)}) with hm
  have hL0 : ((L : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast hL.ne'
  have hm0 : m ≠ 0 := by
    rw [hm, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hL0
  refine ⟨m, Nat.one_le_iff_ne_zero.2 hm0, fun P => ?_⟩
  have e1 : ((L : ℕ) : P.adicCompletion E) = algebraMap E _ (algebraMap (𝓞 E) E ((L : ℕ) : 𝓞 E)) := by simp
  rw [e1, GlobalTheory.Mem.Col2.valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  by_contra h
  push_neg at h
  have hd := (HeightOneSpectrum.intValuation_le_pow_iff_dvd P _ m).1 h.le
  have h2 : Ideal.absNorm (P.asIdeal ^ m) ∣ m := map_dvd Ideal.absNorm hd
  rw [map_pow] at h2
  have hP1 : Ideal.absNorm P.asIdeal ≠ 1 := fun h1 => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)
  have hP0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hP2 : 2 ≤ Ideal.absNorm P.asIdeal := by omega
  have h3 : 2 ^ m ≤ m := (Nat.pow_le_pow_left hP2 m).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h2)
  exact absurd h3 (not_le.2 (Nat.lt_two_pow_self))

end GlobalTheory.AdForm.DeepMove

namespace GlobalTheory.AdForm.DeepMove

theorem map_sub_one_apply {R R' : Type} [CommRing R] [CommRing R'] {n : ℕ} (f : R →+* R') (A : Matrix (Fin n) (Fin n) R)
    (r s : Fin n) : f ((A - 1) r s) = (A.map f - 1) r s := by
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply, map_sub]
  split_ifs <;> simp

theorem exists_den_mat {D : D7} {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) : ∃ d : ℕ, 0 < d ∧
    ∀ r s, toEAf D ((d : AE D) * M r s) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E := by
  choose x y hy e using fun r s => GlobalTheory.AdeleBaseChange.exists_approx (F := D.host.F) (E := D.host.E) (toEAf D (M r s))
  obtain ⟨d, hd, hint⟩ := GlobalTheory.AdeleBaseChange.exists_nat_mul_integral
    (Finset.image (fun p : Fin m × Fin n => x p.1 p.2) Finset.univ)
  refine ⟨d, hd, fun r s => ?_⟩
  obtain ⟨z, hz⟩ := hint (x r s) (Finset.mem_image.2 ⟨(r, s), Finset.mem_univ _, rfl⟩)
  rw [map_mul, map_natCast, e r s, mul_add]
  refine add_mem ?_ (mul_mem (natCast_mem _ d) (hy r s))
  have hc : ((d : ℕ) : Formalism.L2.DIV.AfE D.host.F D.host.E) =
      ((d : ℕ) : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    (map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (A := D.host.E)
      (B := FiniteAdeleRing (𝓞 D.host.F) D.host.F)) d).symm
  have e2 : ((d : ℕ) : Formalism.L2.DIV.AfE D.host.F D.host.E) * (x r s ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
      (algebraMap (𝓞 D.host.E) D.host.E z) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    rw [hc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hz, nsmul_eq_mul]
  rw [e2]
  exact GlobalTheory.AdForm.CongAtIdem.tmul_one_mem_rInt z.isIntegral_coe

theorem actO_deep : ∀ (D : D7) (S T : HSp D) {a b : ℕ} (ha : S.rank = a) (hb : T.rank = b) (e : AE D) (M : WO S T), IsHalf e M → ∀ (k : ℕ), 0 < k → ∃ N₀ : ℕ, ∀ (w : GA D S) (w' : GA D T), w ∈ GfC S → w' ∈ GfC T → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (r s : Fin a), Valued.v (adAt D.host.F P (finM S ha w r s - (1 : Matrix (Fin a) (Fin a) (EF D)) r s)) ≤ WithZero.exp (-(N₀ : ℤ))) → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (r s : Fin b), Valued.v (adAt D.host.F P (finM T hb w' r s - (1 : Matrix (Fin b) (Fin b) (EF D)) r s)) ≤ WithZero.exp (-(N₀ : ℤ))) → ∃ t : WO S T, t ∈ stdHom S T ∧ IsHalf e t ∧ actO S T w⁻¹ w'⁻¹ M = M + k • t := by
  intro D S T a b ha hb e M hM k hk
  subst ha
  subst hb
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.AdForm.exists_nsmul_mem_stdHom S T
  obtain ⟨d, hd, hdM⟩ := exists_den_mat (D := D) M
  obtain ⟨N₀, hN₀, hN⟩ := exists_exp_le_natCast (E := D.host.E) (d * (k * K)) (Nat.mul_pos hd (Nat.mul_pos hk hK))
  refine ⟨N₀, fun w w' hw hw' hA hB => ?_⟩
  have hc0 : (((k * K : ℕ) : D.host.E)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hk hK).ne'
  have hact : actO S T w⁻¹ w'⁻¹ M = ((Formalism.L2.Theta.mt T w'⁻¹ * (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w⁻¹⁻¹ : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := rfl
  rw [inv_inv] at hact
  obtain ⟨Dm, hDm⟩ : ∃ Dm : WO S T, Dm = actO S T w⁻¹ w'⁻¹ M - M := ⟨_, rfl⟩
  let t₀ : WO S T := Matrix.of fun i j => incA D (((k * K : ℕ) : D.host.E))⁻¹ * Dm i j
  have hent : ∀ i j, Dm i j = (((k * K : ℕ) : AE D)) * t₀ i j := fun i j => by
    have h1 : (((k * K : ℕ) : AE D)) = incA D (((k * K : ℕ) : D.host.E)) := (map_natCast (incA D) _).symm
    have h2 : incA D (((k * K : ℕ) : D.host.E)) * incA D (((k * K : ℕ) : D.host.E))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
    show Dm i j = (((k * K : ℕ) : AE D)) * (incA D (((k * K : ℕ) : D.host.E))⁻¹ * Dm i j)
    rw [h1, ← mul_assoc, h2, one_mul]
  have hkt : k • (K • t₀) = Dm := by
    ext i j
    rw [hent i j]
    simp only [Matrix.smul_apply, nsmul_eq_mul]
    push_cast
    ring
  refine ⟨K • t₀, hKm t₀ ?_ ?_, ?_, ?_⟩
  ·
    have hY : (Formalism.L2.Theta.mt S w).map (infPart D) = 1 :=
      (GlobalTheory.FinPl.KOpen.map_eq_one_iff _ _).2 ((GlobalTheory.FinPl.KOpen.mem_GfC_iff S w).1 hw)
    have hX : (Formalism.L2.Theta.mt T w'⁻¹).map (infPart D) = 1 :=
      (GlobalTheory.FinPl.KOpen.map_eq_one_iff _ _).2 ((GlobalTheory.FinPl.KOpen.mem_GfC_iff T w'⁻¹).1 (inv_mem hw'))
    have h0 : Dm.map (infPart D) = 0 := by
      have e3 : (((Formalism.L2.Theta.mt T w'⁻¹ * (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w : Matrix (Fin T.rank) (Fin S.rank) (AE D))).map (infPart D) = M.map (infPart D) := by
        rw [Matrix.map_mul, Matrix.map_mul, hX, hY, Matrix.one_mul, Matrix.mul_one]
      rw [hDm, hact]
      ext i j
      have e5 := congrFun (congrFun e3 i) j
      simp only [Matrix.map_apply] at e5
      simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, e5, sub_self, Matrix.zero_apply]
    ext i j
    have := congrFun (congrFun h0 i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at this ⊢
    simp only [t₀, Matrix.of_apply, map_mul, this, mul_zero]
  ·
    intro i j
    refine (mem_rInt_iff _ _ _).2 fun P => ?_
    show Valued.v (adAt D.host.F P (toEAf D (t₀ i j))) ≤ 1
    let φ : AE D →+* P.adicCompletion D.host.E := (adAt D.host.F P).comp (toEAf D)
    have hε : WithZero.exp (-(N₀ : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hXw : ∀ r s, Valued.v (((Formalism.L2.Theta.mt S w).map φ - 1) r s) ≤ WithZero.exp (-(N₀ : ℤ)) := fun r s => by
      have h := hA P r s
      rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl] at h
      rw [← map_sub_one_apply]
      simpa [φ, Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply, apply_ite] using h
    have hXw' : ∀ r s, Valued.v (((Formalism.L2.Theta.mt T w').map φ - 1) r s) ≤ WithZero.exp (-(N₀ : ℤ)) := fun r s => by
      have h := hB P r s
      rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl] at h
      rw [← map_sub_one_apply]
      simpa [φ, Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply, apply_ite] using h
    have hinv : (Formalism.L2.Theta.mt T w').map φ * (Formalism.L2.Theta.mt T w'⁻¹).map φ = 1 := by
      rw [← Matrix.map_mul, ← GlobalTheory.AdForm.CongAtIdem.mt_mul', mul_inv_cancel, GlobalTheory.AdForm.CongAtIdem.mt_one',
        Matrix.map_one _ (map_zero _) (map_one _)]
    have hY' := inv_entry_le Valued.v _ _ hinv hε hXw'
    let Md : Matrix (Fin T.rank) (Fin S.rank) (AE D) := Matrix.of fun r s => (d : AE D) * M r s
    have hMd : ∀ r s, Valued.v (Md.map φ r s) ≤ 1 := fun r s => by
      have := (mem_rInt_iff _ _ _).1 (hdM r s) P
      exact this
    have hmv := moved_entry_le Valued.v _ _ _ hε.le hXw hY' hMd i j
    have hDmd : (d : AE D) * Dm i j = (((Formalism.L2.Theta.mt T w'⁻¹ * Md : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w : Matrix (Fin T.rank) (Fin S.rank) (AE D)) - Md) i j := by
      have hs : Md = (d : AE D) • (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by ext r s; simp [Md]
      rw [hDm, hact, hs, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
      simp [Matrix.smul_apply]
    have hφ : φ ((d : AE D) * Dm i j) = ((Formalism.L2.Theta.mt T w'⁻¹).map φ * Md.map φ * (Formalism.L2.Theta.mt S w).map φ - Md.map φ) i j := by
      have e4 : (((Formalism.L2.Theta.mt T w'⁻¹ * Md : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w : Matrix (Fin T.rank) (Fin S.rank) (AE D))).map φ =
          (Formalism.L2.Theta.mt T w'⁻¹).map φ * Md.map φ * (Formalism.L2.Theta.mt S w).map φ := by
        rw [Matrix.map_mul, Matrix.map_mul]
      rw [hDmd, ← e4, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, map_sub]
    rw [← hφ, hent i j, ← mul_assoc, ← Nat.cast_mul, map_mul, map_natCast, map_mul] at hmv
    have hL := hN P
    have hL0 : Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E) ≠ 0 := fun h0 => by
      rw [h0] at hL
      exact WithZero.exp_ne_zero (le_antisymm hL zero_le')
    have h2 : Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E) * Valued.v (φ (t₀ i j)) ≤
        Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E) * 1 := by
      rw [mul_one]; exact hmv.trans hL
    calc Valued.v (φ (t₀ i j))
        = (Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E))⁻¹ *
          (Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E) * Valued.v (φ (t₀ i j))) := (inv_mul_cancel_left₀ hL0 _).symm
      _ ≤ (Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E))⁻¹ *
          (Valued.v (((d * (k * K) : ℕ)) : P.adicCompletion D.host.E) * 1) := mul_le_mul' le_rfl h2
      _ = 1 := inv_mul_cancel_left₀ hL0 _
  ·
    have hMe : e • (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = M := by ext r s; exact hM r s
    have hDe : ∀ i j, e * Dm i j = Dm i j := fun i j => by
      have h3 : e • (((Formalism.L2.Theta.mt T w'⁻¹ * (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w : Matrix (Fin T.rank) (Fin S.rank) (AE D))) = (((Formalism.L2.Theta.mt T w'⁻¹ * (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) * Formalism.L2.Theta.mt S w : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by
        rw [← Matrix.smul_mul, ← Matrix.mul_smul]
        congr 2
      have h4 := congrFun (congrFun h3 i) j
      rw [Matrix.smul_apply, smul_eq_mul] at h4
      rw [hDm, hact, Matrix.sub_apply, mul_sub, h4, hM i j]
    intro i j
    simp only [t₀, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    calc e * ((K : AE D) * (incA D (((k * K : ℕ) : D.host.E))⁻¹ * Dm i j))
        = (K : AE D) * (incA D (((k * K : ℕ) : D.host.E))⁻¹ * (e * Dm i j)) := by ring
      _ = _ := by rw [hDe i j]
  · rw [hkt, hDm]
    abel

end GlobalTheory.AdForm.DeepMove
