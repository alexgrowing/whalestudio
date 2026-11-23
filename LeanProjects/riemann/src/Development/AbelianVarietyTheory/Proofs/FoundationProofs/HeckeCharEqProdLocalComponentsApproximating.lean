import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharLocProd

noncomputable def evalAt {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    FiniteAdeleRing (𝓞 E) E →+* P.adicCompletion E where
  toFun x := x P
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem val_algebraMap {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (P.adicCompletion E) a) = P.valuation E a :=
  P.valuedAdicCompletion_eq_valuation' a

theorem evalAt_algebraMap {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    evalAt P (algebraMap E (FiniteAdeleRing (𝓞 E) E) a) = algebraMap E (P.adicCompletion E) a := rfl

theorem eq_prod_of_components {E : Type} [Field E] [NumberField E] {R A B : Type} [CommRing R] [CommRing A]
    [CommRing B] (p : R →+* A) (q : R →+* B) (inc : E →+* R)
    (ev : ∀ P : HeightOneSpectrum (𝓞 E), B →+* P.adicCompletion E)
    (hinc : ∀ P a, ev P (q (inc a)) = algebraMap E _ a)
    (I : AddSubgroup B) (hint : ∀ y, y ∈ I ↔ ∀ P, Valued.v (ev P y) ≤ 1)
    (e : HeightOneSpectrum (𝓞 E) → R) (hinf : ∀ P, p (e P) = 0) (h1 : ∀ P, ev P (q (e P)) = 1)
    (h0 : ∀ P P', P' ≠ P → ev P' (q (e P)) = 0) (c : Rˣ →* Circle) (N : ℕ) (hN : 0 < N)
    (hker : ∀ x : Rˣ, (p x = 1 ∧ q x ∈ I ∧ q (x⁻¹ : Rˣ) ∈ I) → (∃ y ∈ I, q x - 1 = N • y) → c x = 1)
    (x : Rˣ) (hx : p x = 1) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : HeightOneSpectrum (𝓞 E) → Eˣ)
    (l : HeightOneSpectrum (𝓞 E) → Rˣ) (hl : ∀ P, (l P : R) = 1 + e P * (inc (k P) - 1))
    (hS : ∀ P ∈ S, Valued.v (ev P (q x)) = P.valuation E (k P : E) ∧
      Valued.v (ev P (q x) - algebraMap E _ (k P : E)) ≤ P.valuation E (N : E) * P.valuation E (k P : E))
    (hS' : ∀ P, P ∉ S → Valued.v (ev P (q x)) = 1 ∧ (N : 𝓞 E) ∉ P.asIdeal) :
    c x = ∏ P ∈ S, c (l P) := by
  classical
  obtain ⟨u, hud⟩ : ∃ u : Rˣ, u = ∏ P ∈ S, l P := ⟨_, rfl⟩
  have hu : (u : R) = ∏ P ∈ S, (l P : R) := by
    simp only [hud, Units.coe_prod]
  have huinf : p u = 1 := by
    rw [hu, map_prod]
    refine Finset.prod_eq_one fun P _ => ?_
    simp [hl, hinf]
  have hloc1 : ∀ P, ev P (q (l P)) = algebraMap E _ (k P : E) := by
    intro P
    simp only [hl, map_add, map_mul, map_sub, map_one, h1, hinc]
    ring
  have hloc0 : ∀ P Q, Q ≠ P → ev Q (q (l P)) = 1 := by
    intro P Q hQ
    simp only [hl, map_add, map_mul, map_sub, map_one, h0 P Q hQ]
    ring
  have huS : ∀ P ∈ S, ev P (q u) = algebraMap E _ (k P : E) := by
    intro P hP
    rw [hu, map_prod, map_prod, Finset.prod_eq_single P, hloc1]
    · intro Q _ hQ; exact hloc0 Q P hQ.symm
    · intro h; exact absurd hP h
  have huS' : ∀ P, P ∉ S → ev P (q u) = 1 := by
    intro P hP
    rw [hu, map_prod, map_prod]
    refine Finset.prod_eq_one fun Q hQ => hloc0 Q P ?_
    rintro rfl; exact hP hQ
  obtain ⟨y, hy⟩ : ∃ y : Rˣ, y = x * u⁻¹ := ⟨_, rfl⟩
  have hxu : x = y * u := by rw [hy, inv_mul_cancel_right]
  have hyu : (y : R) * u = x := by
    rw [← Units.val_mul, hxu]
  have hyinf : p y = 1 := by
    have := congrArg p hyu
    rwa [map_mul, huinf, hx, mul_one] at this
  have hyev : ∀ P, ev P (q y) * ev P (q u) = ev P (q x) := by
    intro P
    rw [← map_mul, ← map_mul, hyu]
  have hk0 : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E (k P : E) ≠ 0 :=
    fun P => (Valuation.ne_zero_iff _).2 (k P).ne_zero
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hyv : ∀ P, Valued.v (ev P (q y)) = 1 := by
    intro P
    have := congrArg Valued.v (hyev P)
    rw [map_mul] at this
    by_cases hP : P ∈ S
    · rw [huS P hP, val_algebraMap, (hS P hP).1] at this
      exact mul_right_cancel₀ (hk0 P) (by rw [this, one_mul])
    · rwa [huS' P hP, map_one, mul_one, (hS' P hP).1] at this
  have hyv' : ∀ P, Valued.v (ev P (q (y⁻¹ : Rˣ))) = 1 := by
    intro P
    have : Valued.v (ev P (q y)) * Valued.v (ev P (q (y⁻¹ : Rˣ))) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, map_one]
    rwa [hyv, one_mul] at this
  have hcong : ∀ P, Valued.v (ev P (q y) - 1) ≤ P.valuation E (N : E) := by
    intro P
    by_cases hP : P ∈ S
    · have h2 := (hS P hP).2
      rw [← hyev P, huS P hP, ← sub_one_mul, map_mul, val_algebraMap] at h2
      exact le_of_mul_le_mul_right h2 (zero_lt_iff.2 (hk0 P))
    · have h2 : P.valuation E (N : E) = 1 := by
        have := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P
          (r := (N : 𝓞 E))).2 (hS' P hP).2
        simpa using this
      rw [h2]
      exact Valuation.map_sub_le _ (hyv P).le (by rw [map_one])
  have hcy : c y = 1 := by
    refine hker y ⟨hyinf, (hint _).2 fun P => (hyv P).le, (hint _).2 fun P => (hyv' P).le⟩
      ⟨q (inc (N : E)⁻¹) * (q y - 1), (hint _).2 fun P => ?_, ?_⟩
    · rw [map_mul, map_mul, hinc, val_algebraMap, map_sub, map_one, map_inv₀]
      have hv : 0 < P.valuation E (N : E) :=
        zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hN0)
      exact (inv_mul_le_one₀ hv).2 (hcong P)
    · rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (q.comp inc) N,
        RingHom.comp_apply, ← map_mul, ← map_mul, mul_inv_cancel₀ hN0, map_one, map_one, one_mul]
  rw [hxu, map_mul, hcy, one_mul, hud, map_prod]

theorem char_eq_prod_locK : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → ∀ (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → ∃ N : ℕ, 0 < N ∧ ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k : HeightOneSpectrum (𝓞 D.host.E) → D.host.Eˣ), (∀ P ∈ S, Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) ∧ Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤ P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k P : D.host.E)) → (∀ P, P ∉ S → Valued.v (ι (finPart D (x : AE D)) P) = 1 ∧ (N : 𝓞 D.host.E) ∉ P.asIdeal) → ((c x : Circle) : ℂ) = ∏ P ∈ S, ((χ.locK P (k P) : ℂˣ) : ℂ) := by
  intro D ι hι hint hidem c χ hc
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc.1.1
  refine ⟨N, hN, fun x hx S k hS hS' => ?_⟩
  choose e he hinf h1 h0 using hidem
  have key := eq_prod_of_components (infPart D) (finPart D) (incA D)
    (fun P => (evalAt P).comp ι.toRingHom)
    (fun P a => (congrArg (evalAt P) (hι a)).trans (evalAt_algebraMap P a))
    (intAE D) hint e hinf h1 h0 c N hN hker x hx S k (fun P => locU (he P).1 (k P)) (fun _ => rfl) hS hS'
  rw [key]
  exact (map_prod Circle.coeHom _ _).trans
    (Finset.prod_congr rfl fun P _ => hc.2 P (e P) (he P) (k P) _ rfl)

end GlobalTheory.CharLocProd
