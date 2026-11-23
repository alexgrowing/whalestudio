import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFrLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFifth

noncomputable section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace EntryDatum

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}

theorem phiT_add {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG') (hd' : d'.Ok)
    (c : 𝓞 E) (hc : ∀ P ∈ ST, c ∈ P.asIdeal) (x z : HomE E a b)
    (hz : ∀ P ∈ ST, ∀ y ∈ d.at P, z y ∈ d'.at P) : phiT K d d' (x + c • z) = phiT K d d' x := by
  have key : ∀ (x z : HomE E a b), (∀ P ∈ ST, ∀ y ∈ d.at P, z y ∈ d'.at P) →
      (∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) →
      ∀ P : ST, ∀ y ∈ d.at P.1, (x + c • z) y ∈ d'.at P.1 ∧ d'.f P ((x + c • z) y) = d.f P y := by
    intro x z hz h P y hy
    obtain ⟨h1, h2⟩ := h P y hy
    have h3 := hz P.1 P.2 y hy
    have h4 : c • z y ∈ d'.at P.1 := Submodule.smul_mem _ c h3
    have e : (x + c • z) y = x y + c • z y := rfl
    rw [e]
    refine ⟨add_mem h1 h4, ?_⟩
    rw [hd'.f_add P _ h1 _ h4, hd'.f_smul P c _ h3, Ideal.Quotient.eq_zero_iff_mem.2 (hc P.1 P.2), zero_mul, add_zero, h2]
  have hiff : (∀ P : ST, ∀ y ∈ d.at P.1, (x + c • z) y ∈ d'.at P.1 ∧ d'.f P ((x + c • z) y) = d.f P y) ↔
      (∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) := by
    refine ⟨fun h => ?_, key x z hz⟩
    have h' := key (x + c • z) (-z) (fun P hP y hy => neg_mem (hz P hP y hy)) h
    have e : x + c • z + c • (-z) = x := by rw [smul_neg, add_neg_cancel_right]
    rwa [e] at h'
  unfold phiT
  by_cases h : ∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y
  · rw [if_pos h, if_pos (hiff.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

theorem phiT_support {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (x : HomE E a b) (hx : phiT K d d' x ≠ 0) : ∀ P ∈ ST, ∀ y ∈ d.at P, x y ∈ d'.at P := by
  intro P hP y hy
  unfold phiT at hx
  split_ifs at hx with h
  · exact (h ⟨P, hP⟩ y hy).1
  · exact absurd rfl hx

theorem norm_phiT_le {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (σ : K →+* ℂ) (x : HomE E a b) : ‖σ (phiT K d d' x)‖ ≤ 1 := by
  unfold phiT
  split_ifs <;> simp

theorem inFr_maps_iff (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
    {M M₀ : Submodule (𝓞 E) (Sp E a)} {M' M₀' : Submodule (𝓞 E) (Sp E b)}
    (hf : ∀ x, f x ∈ M ↔ x ∈ M₀) (hf' : ∀ x, f' x ∈ M' ↔ x ∈ M₀') (x : HomE E a b) :
    (∀ y ∈ M₀, inFr f f' x y ∈ M₀') ↔ ∀ y ∈ M, x y ∈ M' := by
  have e : ∀ y, f' (inFr f f' x y) = x (f y) := fun y => by simp [inFr]
  constructor
  · intro h y hy
    have h1 : f.symm y ∈ M₀ := (hf _).1 (by simpa using hy)
    have h2 := (hf' _).2 (h _ h1)
    rw [e] at h2
    simpa using h2
  · intro h y hy
    rw [← hf', e]
    exact h _ ((hf y).2 hy)

theorem inFr_add_smul (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x z : HomE E a b) (q k : ℕ) :
    inFr f f' (x + ((q * k : ℕ) : 𝓞 E) • z) = inFr f f' x + (q : E) • inFr f f' ((k : 𝓞 E) • z) := by
  have e : ∀ n : ℕ, ((n : ℕ) : 𝓞 E) • z = (n : E) • z := fun n => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [e, e]
  refine LinearMap.ext fun y => ?_
  simp [inFr, mul_smul]

theorem smallDatum_prod {ST SG SG' SB S : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (hd' : d'.Ok) (fr : Frs E a SB) (fr' : Frs E b SB)
    (hfr : ∀ (P : SB) x, fr P x ∈ d.at P.1 ↔ x ∈ stdAt E a P.1) (hfr' : ∀ (P : SB) x, fr' P x ∈ d'.at P.1 ↔ x ∈ stdAt E b P.1)
    (hS : ∀ P, P ∈ S ↔ P ∈ ST ∨ P ∈ SB) (c : ℕ) (hc : ∀ P ∈ ST, (c : 𝓞 E) ∈ P.asIdeal) (q : SB → ℕ) (hq : ∀ P, q P ∣ c)
    (Φ : SB → HomE E a b → K) (β : SB → ℝ) (hΦ : ∀ P : SB, LocSmall (q P) (stdAt E a P.1) (stdAt E b P.1) (Φ P) (β P)) :
    SmallDatum S d.N d'.N c (fun x => phiT K d d' x * ∏ P : SB, Φ P (inFr (fr P) (fr' P) x)) (∏ P : SB, β P) := by
  refine ⟨fun x hx P hP => ?_, fun x y hy => ?_, fun σ x => ?_⟩
  · rcases (hS P).1 hP with h | h
    · exact phiT_support d d' x (left_ne_zero_of_mul hx) P h
    · have h1 := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) ⟨P, h⟩ (Finset.mem_univ _)
      exact (inFr_maps_iff _ _ (hfr ⟨P, h⟩) (hfr' ⟨P, h⟩) x).1 ((hΦ ⟨P, h⟩).1 _ h1)
  · obtain ⟨z, hz, rfl⟩ := hy
    have e : ((c : 𝓞 E) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) z = (c : 𝓞 E) • z := rfl
    rw [e]
    show phiT K d d' _ * _ = phiT K d d' _ * _
    rw [phiT_add d d' hd' _ hc x z (fun P hP => hz P ((hS P).2 (Or.inl hP)))]
    congr 1
    refine Finset.prod_congr rfl fun P _ => ?_
    obtain ⟨k, hk⟩ := hq P
    rw [hk, inFr_add_smul]
    refine (hΦ P).2.1 _ _ ?_
    refine (inFr_maps_iff _ _ (hfr P) (hfr' P) _).2 fun y hy => ?_
    exact Submodule.smul_mem _ (k : 𝓞 E) (hz P.1 ((hS P.1).2 (Or.inr P.2)) y hy)
  · show ‖σ (phiT K d d' x * _)‖ ≤ _
    rw [map_mul, norm_mul, map_prod, norm_prod]
    have h1 : ∏ P : SB, ‖σ (Φ P (inFr (fr P) (fr' P) x))‖ ≤ ∏ P : SB, β P :=
      Finset.prod_le_prod (fun P _ => norm_nonneg _) fun P _ => (hΦ P).2.2 σ _
    have h0 : 0 ≤ ∏ P : SB, ‖σ (Φ P (inFr (fr P) (fr' P) x))‖ := Finset.prod_nonneg fun P _ => norm_nonneg _
    exact (mul_le_of_le_one_left h0 (norm_phiT_le d d' σ x)).trans h1

end EntryDatum

end GlobalTheory.ColNorms
