import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.DCos

theorem exists_dvd_coprime_mul_pow (M : ℕ) (N : ℕ) (hN : 0 < N) :
    ∃ s k : ℕ, 0 < s ∧ s.Coprime M ∧ N ∣ s * M ^ k := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases h : N.Coprime M
    · exact ⟨N, 0, hN, h, by simp⟩
    · obtain ⟨N', hN'⟩ := Nat.gcd_dvd_left N M
      have hg : 0 < Nat.gcd N M := Nat.gcd_pos_of_pos_left _ hN
      have hg1 : 1 < Nat.gcd N M := by
        have : Nat.gcd N M ≠ 1 := h
        omega
      have hp : 0 < N' := Nat.pos_of_ne_zero (by rintro rfl; omega)
      have hlt : N' < N := by
        calc N' = 1 * N' := (one_mul _).symm
          _ < Nat.gcd N M * N' := Nat.mul_lt_mul_of_pos_right hg1 hp
          _ = N := hN'.symm
      obtain ⟨s, k, hs, hc, hd⟩ := ih N' hlt hp
      refine ⟨s, k + 1, hs, hc, ?_⟩
      rw [hN', pow_succ, ← mul_assoc, mul_comm]
      exact mul_dvd_mul hd (Nat.gcd_dvd_right N M)

theorem evalV_single_same (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (singleV F v 1) = 1 := by
  classical
  exact RestrictedProduct.single_eq_same
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v 1

theorem evalV_single_ne (F : Type) [Field F] [NumberField F] (v v' : HeightOneSpectrum (𝓞 F))
    (h : v' ≠ v) : evalV F v' (singleV F v 1) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) 1 h

theorem af_ext {F : Type} [Field F] [NumberField F] {a b : Af F} (h : ∀ v, evalV F v a = evalV F v b) :
    a = b := RestrictedProduct.ext _ _ h

theorem exists_idem (F : Type) [Field F] [NumberField F] (M : ℕ) (hM : 0 < M) :
    ∃ P : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∈ P, (M : 𝓞 F) ∈ v.asIdeal) ∧
      ∃ β ∈ intAf F, ∑ v ∈ P, singleV F v 1 + β * M = 1 ∧ (∑ v ∈ P, singleV F v 1) * β = 0 := by
  classical
  have hM0 : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hfin : {v : HeightOneSpectrum (𝓞 F) | (M : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h := Ideal.finite_factors (I := Ideal.span {(M : 𝓞 F)}) (by simpa using hM.ne')
    refine h.subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have e1 : ∀ w ∈ hfin.toFinset, evalV F w (∑ v ∈ hfin.toFinset, singleV F v 1) = 1 := fun w hw => by
    rw [map_sum, Finset.sum_eq_single_of_mem w hw fun b _ hb => evalV_single_ne F b w hb.symm,
        evalV_single_same]
  have e0 : ∀ w ∉ hfin.toFinset, evalV F w (∑ v ∈ hfin.toFinset, singleV F v 1) = 0 := fun w hw => by
    rw [map_sum, Finset.sum_eq_zero fun b hb => evalV_single_ne F b w fun h => hw (h ▸ hb)]
  refine ⟨hfin.toFinset, fun v hv => by simpa using hv,
    algebraMap F (Af F) (M : F)⁻¹ * (1 - ∑ v ∈ hfin.toFinset, singleV F v 1), fun w => ?_, ?_, ?_⟩
  · rw [map_mul, map_sub, map_one, AlgHom.commutes]
    by_cases hw : w ∈ hfin.toFinset
    · rw [e1 w hw, sub_self, mul_zero]
      exact zero_mem _
    · rw [e0 w hw, sub_zero, mul_one, HeightOneSpectrum.mem_adicCompletionIntegers]
      have h1 : w.valuation F (algebraMap (𝓞 F) F M) = 1 :=
        (w.valuation_eq_one_iff_notMem (K := F)).2 (by simpa using hw)
      rw [map_natCast] at h1
      have h2 : Valued.v (algebraMap F (Fv F w) (M : F)⁻¹) = w.valuation F (M : F)⁻¹ :=
        w.valuedAdicCompletion_eq_valuation' _
      rw [h2, map_inv₀, h1, inv_one]
  · have h2 : algebraMap F (Af F) (M : F)⁻¹ * (M : Af F) = 1 := by
      rw [← map_natCast (algebraMap F (Af F)) M, ← map_mul, inv_mul_cancel₀ hM0, map_one]
    rw [mul_right_comm, h2, one_mul, add_sub_cancel]
  · refine af_ext fun w => ?_
    rw [map_mul, map_mul, map_sub, map_one, map_zero]
    by_cases hw : w ∈ hfin.toFinset
    · rw [e1 w hw, sub_self, mul_zero, mul_zero]
    · rw [e0 w hw, zero_mul]

section Generic

variable {R : Type} [CommRing R] {k : ℕ}

def CongH (H : AddSubgroup (Fin k → R)) (M : ℕ) (m : Matrix (Fin k) (Fin k) R) : Prop :=
  (∀ u, u ∈ H ↔ ∃ u₀ ∈ H, u = m *ᵥ u₀) ∧ ∀ u ∈ H, ∃ u' ∈ H, m *ᵥ u - u = M • u'

theorem CongH.conj {H : AddSubgroup (Fin k → R)} {M : ℕ} {m : Matrix (Fin k) (Fin k) R} (c : R →+* R)
    (hc : ∀ z, c (c z) = z) (hH : ∀ u ∈ H, (fun i => c (u i)) ∈ H) (h : CongH H M m) :
    CongH H M (m.map c) := by
  let cV : (Fin k → R) →+ (Fin k → R) := c.toAddMonoidHom.compLeft _
  have cc : ∀ u, cV (cV u) = u := fun u => funext fun _ => hc _
  have cm : ∀ u, cV (m *ᵥ u) = m.map c *ᵥ cV u := fun u => funext fun i => RingHom.map_mulVec c m u i
  have mem : ∀ {u}, u ∈ H → cV u ∈ H := fun {u} hu => hH u hu
  refine ⟨fun u => ⟨fun hu => ?_, ?_⟩, fun u hu => ?_⟩
  · obtain ⟨u₀, h₀, e⟩ := (h.1 _).1 (mem hu)
    exact ⟨cV u₀, mem h₀, by rw [← cm, ← e, cc]⟩
  · rintro ⟨u₀, h₀, rfl⟩
    have := mem ((h.1 _).2 ⟨_, mem h₀, rfl⟩)
    rwa [cm, cc] at this
  · obtain ⟨u', h', e⟩ := h.2 _ (mem hu)
    refine ⟨cV u', mem h', ?_⟩
    have := congrArg cV e
    rwa [map_sub, cm, cc, map_nsmul] at this

theorem idem_conj {e : R} {a a' b d : Matrix (Fin k) (Fin k) R} (h : a * a' = 1)
    (ha : ∀ i j, e * a i j = e * (1 : Matrix (Fin k) (Fin k) R) i j)
    (hb : ∀ i j, e * b i j = e * (1 : Matrix (Fin k) (Fin k) R) i j) :
    e • (a' * d * b) = e • d := by
  have ha1 : e • a = e • (1 : Matrix (Fin k) (Fin k) R) := by ext i j; exact ha i j
  have hb1 : e • b = e • (1 : Matrix (Fin k) (Fin k) R) := by ext i j; exact hb i j
  have h2 : e • a' = e • (1 : Matrix (Fin k) (Fin k) R) := by
    rw [← h, ← Matrix.smul_mul, ha1, Matrix.smul_mul, Matrix.one_mul]
  rw [← Matrix.mul_smul, hb1, Matrix.mul_smul, Matrix.mul_one, ← Matrix.smul_mul, h2, Matrix.smul_mul,
    Matrix.one_mul]

theorem mov_iff {H A B : AddSubgroup (Fin k → R)} {a a' b b' d : Matrix (Fin k) (Fin k) R}
    (ha : a * a' = 1) (hA : ∀ u, u ∈ A ↔ ∃ u₀ ∈ H, u = a *ᵥ u₀)
    (hB : ∀ u, u ∈ B ↔ ∃ u₀ ∈ H, u = b *ᵥ u₀) (hb : b * b' = 1) {d' : Matrix (Fin k) (Fin k) R}
    (hd : d' * d = 1) :
    (∀ u, u ∈ H ↔ ∃ u₀ ∈ H, u = (a' * d * b) *ᵥ u₀) ↔ ∀ u, u ∈ B ↔ d *ᵥ u ∈ A := by
  have ha' : a' * a = 1 := mul_eq_one_comm.1 ha
  have hb' : b' * b = 1 := mul_eq_one_comm.1 hb
  have hd' : d * d' = 1 := mul_eq_one_comm.1 hd
  have mA : ∀ u, u ∈ A ↔ a' *ᵥ u ∈ H := fun u => by
    rw [hA]
    constructor
    · rintro ⟨u₀, h₀, rfl⟩; rwa [Matrix.mulVec_mulVec, ha', Matrix.one_mulVec]
    · intro h; exact ⟨_, h, by rw [Matrix.mulVec_mulVec, ha, Matrix.one_mulVec]⟩
  constructor
  · intro h u
    rw [hB, mA, h]
    refine exists_congr fun u₀ => and_congr_right fun _ => ⟨?_, fun e => ?_⟩
    · rintro rfl; simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · have := congrArg (fun w => (d' * a) *ᵥ w) e
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc] at this
      simp only [← Matrix.mul_assoc a, ha, Matrix.one_mul, hd, ← Matrix.mul_assoc d', Matrix.one_mulVec] at this
      exact this
  · intro h u
    constructor
    · intro hu
      have h1 : (d' * a) *ᵥ u ∈ B := by
        rw [h, hA]
        exact ⟨u, hu, by rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hd', Matrix.one_mul]⟩
      obtain ⟨u₀, h₀, e⟩ := (hB _).1 h1
      refine ⟨u₀, h₀, ?_⟩
      rw [← Matrix.mulVec_mulVec, ← e, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mul_assoc d, hd',
        Matrix.one_mul, ha', Matrix.one_mulVec]
    · rintro ⟨u₀, h₀, rfl⟩
      have := (mA _).1 ((h _).1 ((hB _).2 ⟨u₀, h₀, rfl⟩))
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this

variable {E : Type} [Field E] [NumberField E]

theorem cong_iff (ι : E →+* R) {H : AddSubgroup (Fin k → R)} {M : ℕ} (hM : 0 < M) {e b : R}
    (h1 : e + b * M = 1) (h0 : e * b = 0) (hb : ∀ u ∈ H, (fun i => b * u i) ∈ H)
    (hstd : ∀ v : Fin k → E, (fun i => ι (v i)) ∈ H ↔ v ∈ stdL E k)
    (hint : ∀ y : Matrix (Fin k) (Fin k) E, IntM y → ∀ u ∈ H, y.map ι *ᵥ u ∈ H)
    {m : Matrix (Fin k) (Fin k) R} {δ : Matrix (Fin k) (Fin k) E} (hm : e • m = e • δ.map ι)
    (hmH : ∀ u ∈ H, m *ᵥ u ∈ H) :
    (∀ u ∈ H, ∃ u' ∈ H, m *ᵥ u - u = M • u') ↔
      ∃ s : ℕ, 0 < s ∧ s.Coprime M ∧
        ∃ y : Matrix (Fin k) (Fin k) E, IntM y ∧ (s : E) • (δ - 1) = (M : E) • y := by
  have hb' : ∀ u ∈ H, b • u ∈ H := hb
  have hn : ∀ (n : ℤ), ∀ u ∈ H, (n : R) • u ∈ H := fun n u hu => by
    rw [Int.cast_smul_eq_zsmul]; exact H.zsmul_mem hu n
  have hn' : ∀ (n : ℕ), ∀ u ∈ H, (n : R) • u ∈ H := fun n u hu => by
    simpa using hn n u hu
  have he : ∀ u ∈ H, e • u ∈ H := fun u hu => by
    have : e = 1 - b * M := eq_sub_of_add_eq h1
    rw [this, sub_smul, one_smul, mul_smul]
    exact H.sub_mem hu (hb' _ (hn' _ _ hu))
  have hz : ∀ u, e • (m *ᵥ u - u) = e • ((δ - 1).map ι *ᵥ u) := fun u => by
    rw [smul_sub, ← Matrix.smul_mulVec, hm, Matrix.map_sub _ (map_sub ι), Matrix.map_one _ (map_zero ι) (map_one ι),
      Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub, Matrix.smul_mulVec]
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  constructor
  · intro h
    let w : Matrix (Fin k) (Fin k) E := (M : E)⁻¹ • (δ - 1)
    obtain ⟨N, hN0, hN⟩ : ∃ N : ℕ, 0 < N ∧ ∀ i j, IsIntegral ℤ ((N : E) * w i j) := by
      obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := E)
        (Finset.univ.image fun p : Fin k × Fin k => w p.1 p.2)
      refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i j => ?_⟩
      have := h (w i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
      rw [zsmul_eq_mul] at this
      rcases Int.natAbs_eq y with e | e
      · rw [e] at this; simpa using this
      · rw [e] at this; simpa using this.neg
    obtain ⟨s, n, hs, hc, t, ht⟩ := exists_dvd_coprime_mul_pow M N hN0
    refine ⟨s, hs, hc, (s : E) • w, fun i j => ?_, ?_⟩
    · have hj : (fun i => ι ((Pi.single j 1 : Fin k → E) i)) ∈ H :=
        (hstd _).2 (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨u', hu', e1⟩ := h _ hj
      have e2 := hz (fun i => ι ((Pi.single j 1 : Fin k → E) i))
      rw [e1] at e2
      have e3 : e • (fun i => ι (w i j)) = e • u' := by
        funext i
        have := congrFun e2 i
        rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, ← Function.comp_def, ← RingHom.map_mulVec] at this
        simp only [Matrix.mulVec_single_one, smul_eq_mul, nsmul_eq_mul, Matrix.col_apply] at this
        have hMi : ι (M : E)⁻¹ * (M : R) = 1 := by
          rw [← map_natCast ι, ← map_mul, inv_mul_cancel₀ hM0, map_one]
        change e * ι ((M : E)⁻¹ * (δ - 1) i j) = e * u' i
        rw [map_mul]
        linear_combination (-ι (M : E)⁻¹) * this + e * u' i * hMi
      have hNw : (fun i => ι ((N : E) * w i j)) ∈ H :=
        (hstd fun i => (N : E) * w i j).2 ((SW.Base.mem_stdL _).2 fun i => hN i j)
      have hpow : ∀ n : ℕ, e + b ^ (n + 1) * (M : R) ^ (n + 1) = 1 := by
        intro n
        induction n with
        | zero => simpa using h1
        | succ n ih => linear_combination (b * M) * ih + h1 - (M : R) * h0
      have hbp : ∀ n : ℕ, ∀ u ∈ H, b ^ n • u ∈ H := by
        intro n
        induction n with
        | zero => intro u hu; simpa using hu
        | succ n ih => intro u hu; rw [pow_succ, mul_smul]; exact ih _ (hb' _ hu)
      have ht' : (s : R) * (M : R) ^ n = N * t := by exact_mod_cast congrArg (Nat.cast : ℕ → R) ht
      have key : (fun i => ι ((s : E) * w i j)) = (s : R) • e • (fun i => ι (w i j)) +
          b ^ (n + 1) • ((t * M : ℕ) : R) • (fun i => ι ((N : E) * w i j)) := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Nat.cast_mul]
        linear_combination (-(s : R) * ι (w i j)) * hpow n + (b ^ (n + 1) * M * ι (w i j)) * ht'
      have : (fun i => ι ((s : E) * w i j)) ∈ H := by
        rw [key, e3]
        exact H.add_mem (hn' _ _ (he _ hu')) (hbp _ _ (hn' _ _ hNw))
      exact (SW.Base.mem_stdL _).1 ((hstd fun i => (s : E) * w i j).1 this) i
    · rw [smul_comm, smul_smul (M : E), mul_inv_cancel₀ hM0, one_smul]
  · rintro ⟨s, hs, hc, y, hy, e1⟩ u hu
    obtain ⟨p, q, hpq⟩ : IsCoprime (s : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.2 hc
    have hpq' : (p : R) * s + q * M = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → R) hpq
    have hzH : m *ᵥ u - u ∈ H := H.sub_mem (hmH u hu) hu
    have e2 : (s : R) • ((δ - 1).map ι *ᵥ u) = (M : R) • (y.map ι *ᵥ u) := by
      rw [← Matrix.smul_mulVec, ← Matrix.smul_mulVec]
      congr 1
      ext i j
      have := congrArg ι (congrFun (congrFun e1 i) j)
      simpa using this
    have e3 := hz u
    generalize m *ᵥ u - u = z at *
    refine ⟨(p : R) • e • (y.map ι *ᵥ u) + (p : R) • (s : R) • b • z + (q : R) • z,
      H.add_mem (H.add_mem (hn _ _ (he _ (hint y hy u hu))) (hn _ _ (hn' _ _ (hb' _ hzH)))) (hn _ _ hzH), ?_⟩
    funext i
    have a2 := congrFun e2 i
    have a3 := congrFun e3 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at a2 a3 ⊢
    linear_combination (-z i) * hpq' - (p * s * z i) * h1 + (p * s) * a3 + (p * e) * a2

end Generic

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {k : ℕ}

theorem tmul_mem {L : Set (Fin k → E)} {a : Af F} (ha : a ∈ intAf F)
    {x : Fin k → E} (hx : x ∈ L) : (fun i => a ⊗ₜ[F] x i) ∈ latHat F E L :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem map_mem_latHat {L L' : Set (Fin k → E)} (f : (Fin k → Af F ⊗[F] E) →+ (Fin k → Af F ⊗[F] E))
    (h : ∀ a ∈ intAf F, ∀ x ∈ L, f (fun i => a ⊗ₜ[F] x i) ∈ latHat F E L') {u : Fin k → Af F ⊗[F] E}
    (hu : u ∈ latHat F E L) : f u ∈ latHat F E L' := by
  have : latHat F E L ≤ (latHat F E L').comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, hx, rfl⟩
    exact h a ha x hx
  exact this hu

theorem mul_mem_latHat {L : Set (Fin k → E)} {a : Af F} (ha : a ∈ intAf F)
    {u : Fin k → Af F ⊗[F] E} (hu : u ∈ latHat F E L) :
    (fun i => (a ⊗ₜ[F] (1 : E) : Af F ⊗[F] E) * u i) ∈ latHat F E L := by
  refine map_mem_latHat ((AddMonoidHom.mulLeft (a ⊗ₜ[F] (1 : E) : Af F ⊗[F] E)).compLeft _)
    (fun b hb x hx => ?_) hu
  have : a * b ∈ intAf F := fun v => by rw [map_mul]; exact mul_mem (ha v) (hb v)
  convert tmul_mem this hx using 1
  funext i
  change (a ⊗ₜ[F] (1 : E) : Af F ⊗[F] E) * b ⊗ₜ[F] x i = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem mulVec_mem_latHat {L L' : Set (Fin k → E)} {δ : Matrix (Fin k) (Fin k) E}
    (h : ∀ v ∈ L, δ *ᵥ v ∈ L') {u : Fin k → Af F ⊗[F] E} (hu : u ∈ latHat F E L) :
    δ.map (inclR (F := F) (Af F)) *ᵥ u ∈ latHat F E L' := by
  refine map_mem_latHat (Matrix.mulVecLin (δ.map (inclR (F := F) (Af F)))).toAddMonoidHom
    (fun b hb x hx => ?_) hu
  convert tmul_mem hb (h x hx) using 1
  funext i
  change ∑ j, ((1 : Af F) ⊗ₜ[F] δ i j : Af F ⊗[F] E) * b ⊗ₜ[F] x j = b ⊗ₜ[F] ∑ j, δ i j * x j
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem conj_mem_latHat [NumberField E] (σ : E →ₐ[F] E) {u : Fin k → Af F ⊗[F] E}
    (hu : u ∈ latHat F E (stdL E k : Set (Fin k → E))) :
    (fun i => sigR (Af F) σ (u i)) ∈ latHat F E (stdL E k : Set (Fin k → E)) := by
  refine map_mem_latHat ((sigR (Af F) σ).toAddMonoidHom.compLeft _) (fun b hb x hx => ?_) hu
  have hx' : (fun i => σ (x i)) ∈ stdL E k := by
    rw [SetLike.mem_coe] at hx
    rw [SW.Base.mem_stdL] at hx ⊢
    exact fun a => (hx a).map (σ : E →+* E).toIntAlgHom
  exact tmul_mem hb hx'

theorem idem_sub {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {ε : R}
    {m : Matrix (Fin k) (Fin k) R} {i j : Fin k} (h : ε * (m - 1) i j = 0) :
    φ ε * φ (m i j) = φ ε * (1 : Matrix (Fin k) (Fin k) R') i j := by
  have := congrArg φ h
  rw [map_mul, map_zero, Matrix.sub_apply, map_sub, mul_sub, sub_eq_zero] at this
  rw [this]
  by_cases hij : i = j
  · subst hij; simp only [Matrix.one_apply_eq, map_one]
  · simp only [Matrix.one_apply_ne hij, map_zero]

end Adelic

end GlobalTheory.Ker.DCos

end
