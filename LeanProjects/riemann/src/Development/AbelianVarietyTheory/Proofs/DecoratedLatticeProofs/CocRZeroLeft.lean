import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThCLeftStab
open NumberField IsDedekindDomain Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.SemiTwist

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}
  (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ)

def cocR (x y : Formalism.L2.Col.HomE E a b) : ℝ :=
  (Real.sqrt d * (HV (ι := ι) sc (embH emb δ x) (embH emb δ y)).re +
    Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2

theorem cocR_add_left (x y z : Formalism.L2.Col.HomE E a b) :
    cocR emb δ d sc (x + y) z = cocR (ι := ι) emb δ d sc x z + cocR emb δ d sc y z := by
  simp only [cocR, Formalism.L2.Th1.H.altE, map_add, LinearMap.add_apply, Complex.add_re, Complex.add_im]; ring

theorem cocR_zero_left (z : Formalism.L2.Col.HomE E a b) : cocR (ι := ι) emb δ d sc 0 z = 0 := by
  simp [cocR, Formalism.L2.Th1.H.altE]

theorem hv_embH_smul (hconj : ∀ τ x, emb τ (star x) = starRingEnd ℂ (emb τ x)) (r : E) (x y : Formalism.L2.Col.HomE E a b) :
    HV (ι := ι) sc (embH emb δ (r • x)) (embH emb δ y) = HV sc (embH emb δ x) (embH emb δ (star r • y)) := by
  simp only [HV, LinearMap.mk₂'ₛₗ_apply, embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, map_mul, hconj, Complex.conj_conj]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem cocR_smul (hconj : ∀ τ x, emb τ (star x) = starRingEnd ℂ (emb τ x)) (r : E) (x y : Formalism.L2.Col.HomE E a b) :
    cocR (ι := ι) emb δ d sc (r • x) y = cocR emb δ d sc x (star r • y) := by
  simp only [cocR, Formalism.L2.Th1.H.altE, hv_embH_smul emb δ sc hconj]

theorem semiChar_twO : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → 0 < c → (∀ Q, e (Formalism.L2.Col.conjPrime₂ Q) = -e Q) → (∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ (twist₂ M c e)) (alV d sc) := by
  intro E _ _ _ ι _ _ a b emb δ d sc M c e _ hconj hc he _ _ hM
  have hH : Formalism.L2.Th1.H.IsHerm (HV (ι := ι) (a := a) (b := b) sc) := fun x y => by
    simp [Formalism.L2.Ker.HV, map_sum, mul_comm]
  have h0 : ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, cocR emb δ d sc x y = n := fun x hx y hy =>
    (GlobalTheory.KerLaw.semi_iff hH (Real.sqrt d) _).1 hM (embH emb δ x) ⟨x, hx, rfl⟩ (embH emb δ y) ⟨y, hy, rfl⟩
  refine (GlobalTheory.KerLaw.semi_iff hH (Real.sqrt d) _).2 ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  change ∃ n : ℤ, cocR emb δ d sc x y = n
  let I : Ideal (𝓞 E) :=
    { carrier := {r | ∀ s : 𝓞 E, ∃ n : ℤ, cocR emb δ d sc ((s * r) • x) y = n}
      zero_mem' := fun s => ⟨0, by simp [cocR_zero_left]⟩
      add_mem' := fun {r r'} hr hr' s => by
        obtain ⟨n, hn⟩ := hr s
        obtain ⟨m, hm⟩ := hr' s
        exact ⟨n + m, by rw [mul_add, add_smul, cocR_add_left, hn, hm, Int.cast_add]⟩
      smul_mem' := fun t r hr s => by
        rw [smul_eq_mul, ← mul_assoc]
        exact hr _ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 E) :=
      ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
    obtain ⟨u, hu, hx⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((GlobalTheory.KerLaw.mem_tw _ _ _ _).1 hx Q)
    obtain ⟨v, hv, hy⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((GlobalTheory.KerLaw.mem_tw _ _ _ _).1 hy (Formalism.L2.Col.conjPrime₂ Q))
    rw [he, zpow_neg, inv_inv] at hy
    have hmem : u * Formalism.L2.Col.cO E v ∈ I := by
      intro s
      obtain ⟨n, hn⟩ := h0 _ (Submodule.smul_mem _ s hx) _ hy
      refine ⟨n, ?_⟩
      rw [← hn]
      have e1 : (s * (u * Formalism.L2.Col.cO E v)) • x =
          (star (algebraMap (𝓞 E) E v) * (c : E) ^ e Q) • (s • u • ((c : E) ^ e Q)⁻¹ • x) := by
        rw [← algebraMap_smul E s, ← algebraMap_smul E u, ← algebraMap_smul E (s * _), smul_smul, smul_smul, smul_smul,
          map_mul, map_mul, Formalism.L2.Col.algebraMap_cO]
        congr 1
        have hk : (c : E) ^ e Q ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 hc.ne')
        field_simp
      rw [e1, cocR_smul emb δ d sc hconj, star_mul', star_star, star_zpow₀, star_natCast, mul_smul, algebraMap_smul]
    rcases hm.isPrime.mem_or_mem (hle hmem) with h' | h'
    · exact hu h'
    · exact hv h'
  have : (1 : 𝓞 E) ∈ I := hI ▸ Submodule.mem_top
  simpa using this 1

end GlobalTheory.SemiTwist
