import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormula
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmQuadraticCharacterEqProdRealSigns
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRealSpanEqConjFixedPrimeMulRelNorm

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF

namespace PositivityTheory.ThKW.AutEtaA

section Abstract

variable {E : Type} [Field E] [NumberField E]

theorem hom_fix (Fx : HeightOneSpectrum (𝓞 E) → Prop) {G : Type} [CommGroup G]
    (w : HeightOneSpectrum (𝓞 E) → G →* WithZero (Multiplicative ℤ)) (i : Eˣ →* G) (ψ : G →* Circle)
    (lam : ℕ →* ℂ) (hi : ∀ Q k, w Q (i k) = Q.valuation E (k : E))
    (h1 : ∀ y, (∀ Q, Fx Q → w Q y = 1) → ψ y = 1)
    (h3 : ∀ P, Fx P → ∃ z, w P z = WithZero.exp (-1 : ℤ) ∧ (∀ Q, Q ≠ P → w Q z = 1) ∧ (ψ z : ℂ) = -1)
    (h5 : ∀ P : HeightOneSpectrum (𝓞 E), (Fx P →
        lam (Ideal.absNorm P.asIdeal) = -(Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)) ∧
      (¬ Fx P → lam (Ideal.absNorm P.asIdeal) = (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)))
    (u : 𝓞 E) (k : Eˣ) (hk : (k : E) = u) :
    lam (Ideal.absNorm (Ideal.span {u})) = (ψ (i k) : ℂ) * (Real.sqrt (Ideal.absNorm (Ideal.span {u})) : ℂ) := by
  let Gen : Ideal (𝓞 E) → G → Prop := fun B y =>
    ∀ Q : HeightOneSpectrum (𝓞 E), Fx Q → w Q y = WithZero.exp (-multiplicity Q.asIdeal B : ℤ)
  have gmul : ∀ {A B y z}, A ≠ ⊥ → B ≠ ⊥ → Gen A y → Gen B z → Gen (A * B) (y * z) := by
    intro A B y z hA hB hy hz Q hQ
    rw [map_mul, hy Q hQ, hz Q hQ, GlobalTheory.EtaProduct.mult_mul Q hA hB, ← WithZero.exp_add]
    push_cast
    rw [neg_add]
  have guniq : ∀ {B y z}, Gen B y → Gen B z → ψ y = ψ z := by
    intro B y z hy hz
    have := h1 (y * z⁻¹) fun Q hQ => by
      rw [map_mul, map_inv, hy Q hQ, hz Q hQ, mul_inv_cancel₀ WithZero.exp_ne_zero]
    rwa [map_mul, map_inv, mul_inv_eq_one] at this
  have gspan : ∀ (u : 𝓞 E) (k : Eˣ), (k : E) = u → Gen (Ideal.span {u}) (i k) := by
    intro u k hk Q _
    have hu : u ≠ 0 := by
      rintro rfl
      exact k.ne_zero (by simpa using hk)
    rw [hi, hk, GlobalTheory.EtaProduct.val_int Q hu]
  have gone : Gen ⊤ 1 := fun Q _ => by
    rw [map_one, ← Ideal.one_eq_top, multiplicity_eq_zero.2 Q.prime.not_dvd_one]
    simp
  have gmov : ∀ P : HeightOneSpectrum (𝓞 E), ¬ Fx P → Gen P.asIdeal 1 := fun P hP Q hQ => by
    rw [map_one, GlobalTheory.EtaProduct.mult_ne (P := P) (Q := Q) (fun h => hP (h ▸ hQ))]
    simp
  have gfix : ∀ (P : HeightOneSpectrum (𝓞 E)) z, w P z = WithZero.exp (-1 : ℤ) → (∀ Q, Q ≠ P → w Q z = 1) →
      Gen P.asIdeal z := by
    intro P z a1 a3 Q _
    by_cases hQ : Q = P
    · rw [hQ, a1, multiplicity_self]; simp
    · rw [a3 Q hQ, GlobalTheory.EtaProduct.mult_ne hQ]; simp
  have gprime : ∀ P : HeightOneSpectrum (𝓞 E), ∃ z, Gen P.asIdeal z := by
    intro P
    by_cases hP : Fx P
    · obtain ⟨z, a1, a3, -⟩ := h3 P hP
      exact ⟨z, gfix P z a1 a3⟩
    · exact ⟨1, gmov P hP⟩
  have gex : ∀ B : Ideal (𝓞 E), B ≠ ⊥ → ∃ z, Gen B z := by
    intro B
    induction B using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h; exact absurd rfl h
    | h₂ B hB => intro _; rw [Ideal.isUnit_iff.1 hB]; exact ⟨1, gone⟩
    | h₃ C P hC hP ih =>
      intro _
      obtain ⟨a, a1⟩ := gprime ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩
      obtain ⟨b, b1⟩ := ih hC
      exact ⟨a * b, gmul hP.ne_zero hC a1 b1⟩
  have vprime : ∀ (P : HeightOneSpectrum (𝓞 E)) y, Gen P.asIdeal y →
      lam (Ideal.absNorm P.asIdeal) = (ψ y : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) := by
    intro P y hy
    by_cases hP : Fx P
    · obtain ⟨z, a1, a3, a4⟩ := h3 P hP
      rw [guniq hy (gfix P z a1 a3), a4, (h5 P).1 hP, neg_one_mul]
    · rw [guniq hy (gmov P hP), map_one, (h5 P).2 hP]
      simp
  have main : ∀ B : Ideal (𝓞 E), B ≠ ⊥ → ∀ y, Gen B y →
      lam (Ideal.absNorm B) = (ψ y : ℂ) * (Real.sqrt (Ideal.absNorm B) : ℂ) := by
    intro B
    induction B using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h; exact absurd rfl h
    | h₂ B hB =>
      intro _ y hy
      rw [Ideal.isUnit_iff.1 hB] at hy ⊢
      rw [guniq hy gone, Ideal.absNorm_top, map_one, map_one]
      simp
    | h₃ C P hC hP ih =>
      intro _ y hy
      obtain ⟨a, a1⟩ := gprime ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩
      obtain ⟨b, b1⟩ := gex C hC
      have v1 := vprime ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩ a a1
      rw [guniq hy (gmul hP.ne_zero hC a1 b1), map_mul, map_mul, map_mul, v1, ih hC b b1, Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, Circle.coe_mul]
      ring
  refine main _ ?_ _ (gspan u k hk)
  rw [Ne, Ideal.span_singleton_eq_bot]
  rintro rfl
  exact k.ne_zero (by simpa using hk)

end Abstract

section Half

open GlobalTheory.SplitDetCharF

theorem exists_half_abstract' {F T T' : Type} [Field F] [NumberField F] [CommRing T] [CommRing T']
    (j : AF F →+* T) (c : T →+* T) (p : T →+* T') (δ : T) (d : 𝓞 F) (hd0 : (d : F) ≠ 0) (hinj : Function.Injective j)
    (hcj : ∀ a, c (j a) = j a) (hcδ : c δ = -δ) (hδ2 : δ * δ = j (algebraMap F (AF F) (d : F)))
    (hdec : ∀ z, ∃ a b, z = j a + j b * δ) (hinf : ∀ α, p (j (pairA F 0 α)) = 0) :
    ∃ (ε : T) (ι : Af F), ε * ε = ε ∧ ε * c ε = 0 ∧ p ε = 0 ∧ ε + c ε = j (pairA F 0 ι) ∧
      (∀ v, (evalV F v ι = 1 ∧ IsSquare (algebraMap F (Fv F v) (d : F))) ∨
        (evalV F v ι = 0 ∧ ¬ IsSquare (algebraMap F (Fv F v) (d : F)))) ∧
      ∀ e, (e * e = e ∧ e * c e = 0 ∧ ∃ v η, IsPlaceIdemF F v η ∧ e + c e = j η) →
        (ε * e = e ∧ ε * c e = 0) ∨ (ε * e = 0 ∧ ε * c e = c e) := by
  obtain ⟨s, ι, hsι⟩ := exists_sqrt_adele F d
  have hsq : ∀ v, (evalV F v ι = 1 ∧ IsSquare (algebraMap F (Fv F v) (d : F))) ∨
      (evalV F v ι = 0 ∧ ¬ IsSquare (algebraMap F (Fv F v) (d : F))) := fun v =>
    (hsι v).imp (fun h => ⟨h.1, ⟨_, h.2.symm⟩⟩) (fun h => ⟨h.1, fun ⟨r, hr⟩ => h.2.2 r hr.symm⟩)
  obtain ⟨h, hh⟩ : ∃ h : AF F, h * (2 * algebraMap F (AF F) (d : F)) = 1 := by
    have hd : (2 * (d : F)) ≠ 0 := mul_ne_zero two_ne_zero hd0
    have := congrArg (algebraMap F (AF F)) (inv_mul_cancel₀ hd)
    rw [map_mul, map_mul, map_ofNat, map_one] at this
    exact ⟨_, this⟩
  have hH : j h * (2 * j (algebraMap F (AF F) (d : F))) = 1 := by
    have := congrArg j hh
    rwa [map_mul, map_mul, map_ofNat, map_one] at this
  have hII : j (pairA _ 0 ι) * j (pairA _ 0 ι) = j (pairA _ 0 ι) := by
    rw [← map_mul, pair_mul]
    congr 2
    refine af_ext' _ fun w => ?_
    rw [map_mul]
    rcases hsι w with h | h <;> simp [h.1]
  have hIS : j (pairA _ 0 ι) * j (pairA _ 0 s) = j (pairA _ 0 s) := by
    rw [← map_mul, pair_mul]
    congr 2
    refine af_ext' _ fun w => ?_
    rw [map_mul]
    rcases hsι w with h | h
    · simp [h.1]
    · simp [h.2.1]
  have hSS : j (pairA _ 0 s) * j (pairA _ 0 s) = j (pairA _ 0 ι) * j (algebraMap F (AF F) (d : F)) := by
    rw [← map_mul, ← map_mul, pair_mul, pair_mul']
    congr 2
    refine af_ext' _ fun w => ?_
    rw [map_mul, map_mul, evalV_snd_algebraMap]
    rcases hsι w with h | h
    · rw [h.1, h.2, one_mul]
    · rw [h.1, h.2.1, zero_mul, zero_mul]
  obtain ⟨ε, hε⟩ : ∃ ε : T, ε = j h * (j (pairA _ 0 ι) * j (algebraMap F (AF F) (d : F)) - j (pairA _ 0 s) * δ) :=
    ⟨_, rfl⟩
  have hcε : c ε = j h * (j (pairA _ 0 ι) * j (algebraMap F (AF F) (d : F)) + j (pairA _ 0 s) * δ) := by
    rw [hε, map_mul, map_sub, map_mul, map_mul, hcj, hcj, hcj, hcj, hcδ]; ring
  have hinfε : p ε = 0 := by
    rw [hε, map_mul, map_sub, map_mul, map_mul, hinf, hinf]; simp
  generalize hI : j (pairA _ 0 ι) = I at hII hIS hSS hε hcε
  generalize hS : j (pairA _ 0 s) = S at hIS hSS hε hcε
  generalize hD : j (algebraMap F (AF F) (d : F)) = D at hH hSS hε hcε hδ2
  generalize hHH : j h = H at hH hε hcε
  have h2 : ε * c ε = 0 := by
    rw [hcε, hε]
    linear_combination H * H * D * D * hII - H * H * δ * δ * hSS - H * H * I * D * hδ2
  have h3 : ε + c ε = I := by
    rw [hcε, hε]
    linear_combination I * hH
  have h4 : I * ε = ε := by
    rw [hε]
    linear_combination H * D * hII - H * δ * hIS
  have h1 : ε * ε = ε := by
    linear_combination ε * h3 - h2 + h4
  refine ⟨ε, ι, h1, h2, hinfε, h3.trans hI.symm, hsq, ?_⟩
  rintro e ⟨he1, he2, v, η, ⟨α, rfl, hα1, hα0⟩, he3⟩
  obtain ⟨a, b, hab⟩ := hdec e
  have hce : c e = j a - j b * δ := by
    rw [hab, map_add, map_mul, hcj, hcj, hcδ]; ring
  have he4 : c e * c e = c e := by rw [← map_mul, he1]
  obtain ⟨B, hB⟩ : ∃ B : AF F, B = 2 * algebraMap F (AF F) (d : F) * b := ⟨_, rfl⟩
  have hjB : j B = δ * (e - c e) := by
    rw [hB, map_mul, map_mul, map_ofNat, hD, hce]
    linear_combination -δ * hab - 2 * j b * hδ2
  have hB1 : pairA _ 0 α * B = B := hinj (by
    rw [map_mul, ← he3, hjB]
    linear_combination δ * he1 - δ * he4)
  have hB2 : B * B = pairA _ 0 α * algebraMap F (AF F) (d : F) := hinj (by
    rw [map_mul, map_mul, hD, ← he3, hjB]
    linear_combination δ * δ * he1 + δ * δ * he4 - 2 * δ * δ * he2 + (e + c e) * hδ2)
  have hB3 : evalV _ v (sndA _ B) * evalV _ v (sndA _ B) = algebraMap F (Fv F v) (d : F) := by
    rw [← map_mul, ← map_mul, hB2, map_mul, map_mul, evalV_snd_algebraMap]
    change evalV _ v α * _ = _
    rw [hα1, one_mul]
  rcases hsι v with ⟨hι, hs⟩ | ⟨-, -, hn⟩
  swap
  · exact absurd hB3 (hn _)
  have hNI : (e + c e) * I = e + c e := by
    rw [he3, ← hI, ← map_mul, pair_mul, place_ext _ hα0 (y := 1) (by rw [hι, map_one]), mul_one]
  rcases mul_self_eq_mul_self_iff.1 (hB3.trans hs.symm) with hp | hp
  · right
    have : j B = (e + c e) * S := by
      rw [he3, ← hS, ← map_mul, ← hB1, pair_mul, pair_mul', place_ext _ hα0 hp]
    have h5 : c e = (e + c e) * ε := by
      rw [hε]
      linear_combination -H * D * hNI - H * δ * this + H * δ * hjB + H * (e - c e) * hδ2 - c e * hH
    constructor
    · linear_combination -e * h5 + (1 - ε) * he2 - ε * he1
    · linear_combination -(c e) * h5 + (1 - ε) * he4 - ε * he2
  · left
    have : j B = -((e + c e) * S) := by
      rw [he3, ← hS, ← map_mul, ← hB1, pair_mul, pair_mul', ← map_neg, pair_neg, ← mul_neg,
        place_ext _ hα0 (y := -s) (by rw [hp, map_neg])]
    have h5 : e = (e + c e) * ε := by
      rw [hε]
      linear_combination -H * D * hNI + H * δ * this - H * δ * hjB - H * (e - c e) * hδ2 - e * hH
    constructor
    · linear_combination -e * h5 + (1 - ε) * he1 - ε * he2
    · linear_combination -(c e) * h5 + (1 - ε) * he2 - ε * he4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_half {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ (θ : E) (d : 𝓞 F) (ε : AEF F E) (ι : Af F), (d : F) ≠ 0 ∧ σ θ = -θ ∧ θ * θ = algebraMap F E (d : F) ∧
      (∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ) ∧
      ε * ε = ε ∧ ε * cAF σ ε = 0 ∧ infPartF F E ε = 0 ∧ ε + cAF σ ε = algebraMap (AF F) (AEF F E) (pairA F 0 ι) ∧
      (∀ v, (evalV F v ι = 1 ∧ IsSquare (algebraMap F (Fv F v) (d : F))) ∨
        (evalV F v ι = 0 ∧ ¬ IsSquare (algebraMap F (Fv F v) (d : F)))) ∧
      ∀ e, IsSplitIdemF σ e → (ε * e = e ∧ ε * cAF σ e = 0) ∨ (ε * e = 0 ∧ ε * cAF σ e = cAF σ e) := by
  obtain ⟨θ, d, hd0, hσθ, hθθ, hdec⟩ := exists_int_basis h
  have hs : ∀ (a : AF F) (x : E), cAF σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := fun _ _ => rfl
  obtain ⟨ε, ι, h1, h2, h3, h5, h6, h4⟩ := exists_half_abstract' (algebraMap (AF F) (AEF F E)) (cAF σ) (infPartF F E)
    ((1 : AF F) ⊗ₜ[F] θ) d hd0 tensor_inj
    (fun a => by
      rw [Algebra.TensorProduct.algebraMap_apply, hs, map_one])
    (by rw [hs, hσθ, TensorProduct.tmul_neg])
    (by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hθθ, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_eq_smul_one (A := E), TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one (A := AF F),
        TensorProduct.smul_tmul']
      congr 1
      exact (algebraMap_smul (AF F) (d : F) (1 : AF F)).symm)
    (tensor_decomp θ hdec)
    (fun α => by
      show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (algebraMap (AF F) (AEF F E) (pairA F 0 α)) = 0
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul, Algebra.algebraMap_self,
        RingHom.id_apply, show fstA F (pairA F 0 α) = 0 from rfl, TensorProduct.zero_tmul])
  exact ⟨θ, d, ε, ι, hd0, hσθ, hθθ, hdec, h1, h2, h3, h5, h6, fun e he => h4 e he⟩

end Half

end PositivityTheory.ThKW.AutEtaA

end
