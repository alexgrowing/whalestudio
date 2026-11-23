import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace PositivityTheory.PfDR.h_smooth

private theorem rayRel_of_mul_left' {F : Type} [Field F] [NumberField F] {𝔣 𝔠 I J : Ideal (𝓞 F)}
    (h𝔠 : 𝔠 ≠ 0) (h : RayRel F 𝔣 (𝔠 * I) (𝔠 * J)) : RayRel F 𝔣 I J := by
  obtain ⟨a, b, ha, hb, ha1, hb1, hpos, heq⟩ := h
  refine ⟨a, b, ha, hb, ha1, hb1, hpos, ?_⟩
  apply mul_left_cancel₀ h𝔠
  calc 𝔠 * (Ideal.span {a} * I) = Ideal.span {a} * (𝔠 * I) := by ring
    _ = Ideal.span {b} * (𝔠 * J) := heq
    _ = 𝔠 * (Ideal.span {b} * J) := by ring

private theorem ne_zero_of_totPos' {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {x : F}
    (hx : TotPos F x) : x ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have h := hx (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
  intro h0
  rw [h0, map_zero] at h
  exact lt_irrefl _ h

theorem smoothed_of
    (hcv : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J]
      (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime →
      (∀ j i, v j i ∉ 𝔠 * 𝔟) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ →
        (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
          (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) →
        ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) ∧
          ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → ¬ l ∣ Ideal.absNorm 𝔟 → 0 ≤ padicValRat l q)
    (hcp : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
      ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
        ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
          ClassParam 𝔣 𝔞 𝔟 r' y v' ∧ 𝔟 ⊔ 𝔣 = ⊤)
    (hnd : ∀ {F : Type} [Field F] [NumberField F] {l : ℕ}, l.Prime → ∀ {𝔟 : Ideal (𝓞 F)},
      𝔟 ⊔ Ideal.span {(l : 𝓞 F)} = ⊤ → ¬ l ∣ Ideal.absNorm 𝔟) :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ (S : Finset (Ideal (𝓞 F))), (∀ a ∈ S, CoprimeTo F 𝔣 a) → (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) →
      (∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) → ∀ Z : S → ℂ → ℂ, (∀ c, IsRayZeta 𝔣 c.1 (Z c)) →
      ∃ W : Finset (𝓞 F), (∀ x ∈ W, x ≠ 0) ∧ ∀ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → 𝔠 ⊔ 𝔣 = ⊤ →
        (∀ x ∈ W, x ∉ 𝔠) → ∃ τ : Equiv.Perm S, (∀ c, RayRel F 𝔣 (𝔠 * (τ c).1) c.1) ∧
          ∀ k : ℕ, 1 ≤ k → ∀ c, ∃ q : ℚ,
            ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ k * Z (τ c) (1 - (k : ℂ)) - Z c (1 - (k : ℂ)) = (q : ℂ) ∧
            ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → 𝔣 ≤ Ideal.span {(l : 𝓞 F)} → 0 ≤ padicValRat l q := by
  intro F _ _ _ 𝔣 h𝔣 S hSc hSinj hScov Z hZ
  classical
  have hdat := fun c : S => hcp F 𝔣 h𝔣 c.1 (hSc c.1 c.2)
  choose 𝔟 J hJ r y v hP hb using hdat
  have vne : ∀ c j i, v c j i ≠ 0 := fun c j i h =>
    ne_zero_of_totPos' ((hP c).2.2.1 j i).2 (by simp [h])
  let W : Finset (𝓞 F) := Finset.univ.biUnion
    (fun c : S => (Finset.univ : Finset (Σ j : J c, Fin (r c j))).image (fun p => v c p.1 p.2))
  have memW : ∀ c j i, v c j i ∈ W := fun c j i =>
    Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_image.2 ⟨⟨j, i⟩, Finset.mem_univ _, rfl⟩⟩
  refine ⟨W, ?_, ?_⟩
  · intro x hx
    simp only [W, Finset.mem_biUnion, Finset.mem_image] at hx
    obtain ⟨c, -, ⟨j, i⟩, -, rfl⟩ := hx
    exact vne c j i
  intro 𝔠 h𝔠p h𝔠N h𝔠f hW
  have h𝔠ne : 𝔠 ≠ ⊥ := fun h => by
    rw [h, ← Submodule.zero_eq_bot, map_zero] at h𝔠N
    exact Nat.not_prime_zero h𝔠N
  have h𝔠0 : 𝔠 ≠ 0 := by rw [Ne, Submodule.zero_eq_bot]; exact h𝔠ne
  have hN0 : ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h𝔠N.ne_zero
  have hcopI : ∀ I, CoprimeTo F 𝔣 I → CoprimeTo F 𝔣 (𝔠 * I) := by
    intro I hI
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.mul_eq_bot]
      push_neg
      exact ⟨h𝔠ne, hI.1⟩
    · rw [sup_comm, Ideal.sup_mul_eq_of_coprime_left (by rw [sup_comm]; exact h𝔠f), sup_comm]
      exact hI.2
  have hσ : ∀ c : S, ∃ a : S, RayRel F 𝔣 (𝔠 * c.1) a.1 := fun c => by
    obtain ⟨a, ha, h⟩ := hScov _ (hcopI _ (hSc _ c.2))
    exact ⟨⟨a, ha⟩, h⟩
  choose σ hσ using hσ
  have σinj : Function.Injective σ := by
    intro c d h
    have h1 := hσ c
    have h2 := hσ d
    rw [h] at h1
    have h3 := rayRel_of_mul_left' h𝔠0 (GlobalTheory.RayZeta.rayRel_trans h1 (GlobalTheory.RayZeta.rayRel_symm h2))
    exact Subtype.ext (hSinj _ c.2 _ d.2 h3)
  have σbij := Finite.injective_iff_bijective.mp σinj
  set τ : Equiv.Perm S := (Equiv.ofBijective σ σbij).symm with hτdef
  have hτ : ∀ c : S, RayRel F 𝔣 (𝔠 * (τ c).1) c.1 := by
    intro c
    have h := hσ (τ c)
    have e : σ (τ c) = c := Equiv.ofBijective_apply_symm_apply σ σbij c
    rw [e] at h
    exact h
  refine ⟨τ, hτ, ?_⟩
  intro k hk c
  have hd1 : Differentiable ℂ (fun s : ℂ => ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s)) :=
    Differentiable.const_cpow differentiable_neg (Or.inl hN0)
  have hdiff : DifferentiableOn ℂ (fun s => ((Ideal.absNorm 𝔠 : ℕ) : ℂ) * ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s)
      * Z (τ c) s - Z c s) {1}ᶜ :=
    (((differentiableOn_const _).mul hd1.differentiableOn).mul (hZ (τ c)).1).sub (hZ c).1
  have hsum : ∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1} =>
      (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s))
      (((Ideal.absNorm 𝔠 : ℕ) : ℂ) * ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) * Z (τ c) s - Z c s) := by
    intro s hs
    have hA := (hZ c).2 s hs
    have hB := (hZ (τ c)).2 s hs
    let m : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I (τ c).1} →
        {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1} := fun I' =>
      ⟨𝔠 * I'.1, hcopI _ I'.2.1,
        GlobalTheory.RayZeta.rayRel_trans (GlobalTheory.RayZeta.rayRel_mul_left 𝔠 I'.2.2) (hτ c)⟩
    have minj : Function.Injective m := fun a b h =>
      Subtype.ext (mul_left_cancel₀ h𝔠0 (Subtype.ext_iff.1 h))
    let f : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1} → ℂ := fun I =>
      if I.1 ≤ 𝔠 then ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) else 0
    have hf : HasSum f (((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) * Z (τ c) s) := by
      rw [← minj.hasSum_iff]
      · have e : f ∘ m = fun I' => ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) * ((Ideal.absNorm I'.1 : ℕ) : ℂ) ^ (-s) := by
          funext I'
          simp only [Function.comp, f, m]
          rw [if_pos Ideal.mul_le_left, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
        rw [e]
        exact hB.mul_left _
      · intro I hI
        simp only [f]
        rw [if_neg]
        intro hle
        apply hI
        obtain ⟨I', hI'⟩ := Ideal.dvd_iff_le.2 hle
        have h1 : RayRel F 𝔣 (𝔠 * I') c.1 := by
          rw [← hI']
          exact I.2.2
        have hle' : I.1 ≤ I' := by
          rw [hI']
          exact Ideal.mul_le_right
        refine ⟨⟨I', ⟨fun h => I.2.1.1 (by rw [hI', h, Ideal.mul_bot]), ?_⟩, ?_⟩, Subtype.ext hI'.symm⟩
        · exact top_le_iff.1 (I.2.1.2.ge.trans (sup_le_sup_right hle' _))
        · exact rayRel_of_mul_left' h𝔠0 (GlobalTheory.RayZeta.rayRel_trans h1 (GlobalTheory.RayZeta.rayRel_symm (hτ c)))
    have hC := (hf.mul_left ((Ideal.absNorm 𝔠 : ℕ) : ℂ)).sub hA
    have e2 : (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1} =>
        (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s))
        = fun I => ((Ideal.absNorm 𝔠 : ℕ) : ℂ) * f I - ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
      funext I
      simp only [f, classWeight]
      split_ifs <;> push_cast <;> ring
    rw [e2, show ((Ideal.absNorm 𝔠 : ℕ) : ℂ) * ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) * Z (τ c) s - Z c s
      = ((Ideal.absNorm 𝔠 : ℕ) : ℂ) * (((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) * Z (τ c) s) - Z c s by ring]
    exact hC
  obtain ⟨q, hq, hql⟩ := hcv F 𝔣 c.1 (𝔟 c) 𝔠 (J c) (r c) (y c) (v c) (hP c) h𝔠p h𝔠N
    (fun j i hv => hW (v c j i) (memW c j i) (Ideal.mul_le_left hv)) _ hdiff hsum k hk
  refine ⟨q, ?_, fun l hl hlc hfl => hql l hl hlc (hnd hl ?_)⟩
  · have hpow : ((Ideal.absNorm 𝔠 : ℕ) : ℂ) * ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-(1 - (k : ℂ)))
        = ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ k := by
      have he : -(1 - (k : ℂ)) = ((k - 1 : ℕ) : ℂ) := by
        push_cast [Nat.cast_sub hk]
        ring
      rw [he, Complex.cpow_natCast, ← pow_succ', Nat.sub_add_cancel hk]
    rw [← hpow]
    exact hq
  · exact top_le_iff.1 ((hb c).ge.trans (sup_le_sup_left hfl _))

end PositivityTheory.PfDR.h_smooth
