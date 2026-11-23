import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StandardHermitianFormHostFieldInhabitantStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLatticeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalUnitarySplitDenominatorStatement
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.Move

section General

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem fv_mulVec (γ : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    fv F (γ *ᵥ v) = fm F γ *ᵥ fv F v := by
  funext i
  simp only [fv, fm, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, TensorProduct.tmul_sum]

theorem fv_smul (s : E) (v : Fin n → E) :
    fv F (s • v) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] s : RA F E) • fv F v := by
  funext i
  simp only [fv, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem fv_sub (x y : Fin n → E) : fv F (x - y) = fv F x - fv F y := by
  funext i
  simp [fv, TensorProduct.tmul_sub]

theorem nsmul_cancel {M : ℕ} (hM : 0 < M) {x y : Fin n → RA F E} (h : M • x = M • y) : x = y := by
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  have := congrArg (fun z => (M : F)⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ hM'] using this

end General

section Ideals

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem span_smul_le (s : 𝓞 E) (A B : Submodule (𝓞 E) (Fin n → E)) :
    Ideal.span {s} • A ≤ B ↔ ∀ v ∈ A, s • v ∈ B := by
  rw [Submodule.ideal_span_singleton_smul]
  constructor
  · intro h v hv
    exact h (Submodule.smul_mem_pointwise_smul v _ A hv)
  · intro h x hx
    obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact h v hv

theorem exists_nat_coprime (s : 𝓞 E) (N : ℕ)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → (N : 𝓞 E) ∉ P) :
    ∃ k : ℕ, k.Coprime N ∧ s ∣ (k : 𝓞 E) := by
  set I : Ideal ℤ := (Ideal.span {s}).comap (algebraMap ℤ (𝓞 E)) with hI
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I).principal
  have haI : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
  refine ⟨a.natAbs, ?_, ?_⟩
  · refine Nat.coprime_of_dvd fun p hp hpa hpN => ?_
    have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    haveI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp'.ne_zero).2 hp'
    have hle : I ≤ Ideal.span {(p : ℤ)} := by
      rw [ha]
      exact Ideal.span_singleton_le_span_singleton.2 (Int.natCast_dvd.2 hpa)
    obtain ⟨Q, hQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(p : ℤ)})
      (Ideal.span {s}) hle
    refine h Q hQp (hQ (Ideal.mem_span_singleton_self s)) ?_
    have : ((N : ℕ) : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      rw [hQc, Ideal.mem_span_singleton]; exact_mod_cast hpN
    simpa using this
  · have h1 : s ∣ ((a : ℤ) : 𝓞 E) := by
      have := haI
      rw [hI, Ideal.mem_comap, Ideal.mem_span_singleton] at this
      simpa using this
    have h2 : ((a : ℤ) : 𝓞 E) ∣ ((a.natAbs : ℤ) : 𝓞 E) :=
      map_dvd (Int.castRingHom (𝓞 E)) (Int.dvd_natAbs.2 dvd_rfl)
    rw [Int.cast_natCast] at h2
    exact h1.trans h2

theorem smul_mem_of_dvd {s t : 𝓞 E} (h : s ∣ t) {B : Submodule (𝓞 E) (Fin n → E)} {v : Fin n → E}
    (hv : s • v ∈ B) : t • v ∈ B := by
  obtain ⟨c, rfl⟩ := h
  rw [mul_comm, mul_smul]
  exact B.smul_mem c hv

end Ideals

section Unimod

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem hermE_one (x y : Fin n → E) :
    hermE (IsCMField.complexConj E) 1 x y = ∑ j, IsCMField.complexConj E (y j) * x j := by
  simp [hermE, Matrix.one_apply, mul_comm]

theorem unimod_move (γ : GL (Fin n) E) (hγ : IsUnE (IsCMField.complexConj E) 1 γ.1) (Λ Λ' : GenLat E n)
    (h : ∀ v, v ∈ Λ.La ↔ γ.1 *ᵥ v ∈ Λ'.La) (hU : Λ.Unimod) : Λ'.Unimod := by
  have hs : ∀ v : Fin n → E, ∃ u, v = γ.1 *ᵥ u := fun v =>
    ⟨(γ⁻¹).1 *ᵥ v, by rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
  intro v
  obtain ⟨u, rfl⟩ := hs v
  rw [← h, hU u]
  constructor
  · intro H w hw
    obtain ⟨x, rfl⟩ := hs w
    rw [← hermE_one, hγ, hermE_one]
    exact H x ((h x).2 hw)
  · intro H x hx
    have := H _ ((h x).1 hx)
    rwa [← hermE_one, hγ, hermE_one] at this

end Unimod

theorem exists_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n M bad : ℕ) (Λ : GenLat E n), 0 < M → 0 < bad → Λ.Unimod → Λ.TrivAt M → ∃ (γ : GL (Fin n) E) (Λ' : GenLat E n), (∀ i j, ∑ b, (IsCMField.complexConj E) (γ.1 b i) * γ.1 b j = if i = j then 1 else 0) ∧ CongAt (stdLat E n) M M γ.1 ∧ (∀ v, v ∈ Λ.La ↔ γ.1 *ᵥ v ∈ Λ'.La) ∧ Λ'.Unimod ∧ Λ'.TrivAt bad ∧ Λ'.TrivAt M ∧ GenLat.SplitSupp H Λ' ∧ (Odd M → 2 ∣ bad → ∃ N, Λ'.LevOK N M) := by
  intro E _ _ _ H n M bad Λ hM hbad hU hT
  obtain ⟨hherm, hrk, hfg, hsp, -, -, hmov, hun⟩ := GlobalTheory.T.standardHermitianForm_hostField_inhabitant E H n
  obtain ⟨g, hg, hΛ, hgc⟩ := GlobalTheory.T.exists_adelic_unitary_translate_standardLattice E H n M Λ hM hU hT
  obtain ⟨γ, hγ, ⟨t₁, ht₁, hc₁⟩, s, ⟨hs0, hs⟩, hint⟩ := GlobalTheory.T.exists_rational_unitary_split_denominator (maximalRealSubfield E) E
    (IsCMField.complexConj E) n 1 hherm hrk (stdLat E n) hfg hsp g (bad * M) hg (Nat.mul_pos hbad hM)
  obtain ⟨t₂, ht₂, hc₂⟩ := hgc M hM
  have hrat := (hat_rational_points_and_approx (maximalRealSubfield E) E n (stdLat E n) hfg hsp).1
  have hmem : ∀ v, v ∈ Λ.La ↔ ∃ z ∈ hat (maximalRealSubfield E) (stdLat E n : Set (Fin n → E)),
      g.1 *ᵥ z = fv (maximalRealSubfield E) v := by
    intro v
    rw [← SetLike.mem_coe, hΛ]
    rfl
  have hinv : ∀ v : Fin n → E, (γ⁻¹).1 *ᵥ (γ.1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv' : ∀ v : Fin n → E, γ.1 *ᵥ ((γ⁻¹).1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  let Λ' : GenLat E n := ⟨Λ.La.comap ((Matrix.mulVecLin (γ⁻¹).1).restrictScalars (𝓞 E))⟩
  have hΛ' : ∀ v, v ∈ Λ'.La ↔ (γ⁻¹).1 *ᵥ v ∈ Λ.La := fun v => Iff.rfl
  have hmove : ∀ v, v ∈ Λ.La ↔ γ.1 *ᵥ v ∈ Λ'.La := fun v => by rw [hΛ', hinv]
  have hsE : ∀ v : Fin n → E, s • v = (s : E) • v := fun v => rfl
  have h1 : ∀ v ∈ Λ'.La, s • v ∈ stdLat E n := by
    intro v hv
    obtain ⟨z, hz, hzv⟩ := (hmem _).1 ((hΛ' v).1 hv)
    have := (hint z hz).1
    rw [← Matrix.mulVec_mulVec, hzv, ← fv_mulVec, hinv', ← fv_smul] at this
    rw [hsE]
    exact (hrat _).1 this
  have h2 : ∀ v ∈ stdLat E n, s • v ∈ Λ'.La := by
    intro v hv
    have := (hint _ ((hrat v).2 hv)).2
    rw [hΛ', hmem]
    refine ⟨_, this, ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mul, ← fv_mulVec, ← fv_smul, hsE, Matrix.mulVec_smul]
  obtain ⟨k, hk, hsk⟩ := exists_nat_coprime s (bad * M) fun P hP hsP => (hs P hP hsP).2
  have htriv : ∀ m, k.Coprime m → Λ'.TrivAt m := fun m hm =>
    ⟨k, hm, (span_smul_le _ _ _).2 fun v hv => smul_mem_of_dvd hsk (h1 v hv),
      (span_smul_le _ _ _).2 fun v hv => smul_mem_of_dvd hsk (h2 v hv)⟩
  refine ⟨γ, Λ', (hun _).1 hγ, ?_, hmove, unimod_move γ hγ Λ Λ' hmove hU,
    htriv _ hk.coprime_mul_right_right, htriv _ hk.coprime_mul_left_right,
    ⟨s, hs0, (span_smul_le _ _ _).2 h1, (span_smul_le _ _ _).2 h2,
      fun P hP hsP => (hmov P hP).1 (hs P hP hsP).1⟩, ?_⟩
  · obtain ⟨j, hj, -, hj2⟩ := hT
    refine ⟨t₁ * t₂ * j, (ht₁.coprime_mul_left_right.mul_left ht₂).mul_left hj, fun v hv => ?_⟩
    have hjv : j • v ∈ Λ.La := by
      have := (span_smul_le _ _ _).1 hj2 v hv
      rwa [Nat.cast_smul_eq_nsmul] at this
    obtain ⟨z, hz, hzv⟩ := (hmem _).1 hjv
    obtain ⟨w₁, hw₁, e₁⟩ := hc₁ z hz
    obtain ⟨w₂, hw₂, e₂⟩ := hc₂ z hz
    have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
    have key : (t₁ * t₂ * j) • (γ.1 *ᵥ v - v) = M • ((M : E)⁻¹ • ((t₁ * t₂ * j) • (γ.1 *ᵥ v - v))) := by
      rw [← Nat.cast_smul_eq_nsmul E M, smul_smul, mul_inv_cancel₀ hME, one_smul]
    refine ⟨_, ?_, key⟩
    rw [← hrat]
    have e : fv (maximalRealSubfield E) ((M : E)⁻¹ • ((t₁ * t₂ * j) • (γ.1 *ᵥ v - v)))
        = (t₂ * bad) • w₁ - t₁ • w₂ := by
      refine nsmul_cancel _ hM ?_
      rw [← cap_fv_nsmul, ← key, mul_smul, smul_sub j, ← Matrix.mulVec_smul, cap_fv_nsmul, fv_sub, fv_mulVec,
        ← hzv, Matrix.mulVec_mulVec]
      have a1 : M • ((t₂ * bad) • w₁) = t₂ • ((bad * M) • w₁) := by
        rw [smul_smul, smul_smul]; congr 1; ring
      have a2 : M • (t₁ • w₂) = t₁ • (M • w₂) := smul_comm _ _ _
      rw [smul_sub M, a1, a2, ← e₁, ← e₂, smul_smul, smul_smul, mul_comm t₂ t₁, ← smul_sub, sub_sub_sub_cancel_right]
    rw [e]
    exact sub_mem (nsmul_mem hw₁ _) (nsmul_mem hw₂ _)
  · intro hodd h2b
    refine ⟨k * M, ?_, Dvd.intro_left _ rfl, (span_smul_le _ _ _).2 fun v hv => ⟨?_, (stdLat E n).smul_mem _ hv⟩⟩
    · exact (Nat.coprime_two_right.1 (hk.coprime_mul_right_right.coprime_dvd_right h2b)).mul hodd
    · refine smul_mem_of_dvd (hsk.trans ?_) (h2 v hv)
      rw [Nat.cast_mul]
      exact Dvd.intro _ rfl

end GlobalTheory.UnRep.Move
