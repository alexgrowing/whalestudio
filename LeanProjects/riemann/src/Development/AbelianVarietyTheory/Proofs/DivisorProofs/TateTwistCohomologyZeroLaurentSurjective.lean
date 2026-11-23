import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPrimitiveVectorCompactRescale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijective

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.MultiplicativeGroupGlobalSections

open LaurentPolynomial in

theorem laurent_ringHom_ext {R S : Type} [CommRing R] [CommRing S] {f g : LaurentPolynomial R →+* S}
    (hC : f.comp C = g.comp C) (hT : f (T 1) = g (T 1)) : f = g := by
  have h1 : f (T 1) * f (T (-1)) = 1 := by rw [← map_mul, ← T_add]; simp
  have h2 : g (T 1) * g (T (-1)) = 1 := by rw [← map_mul, ← T_add]; simp
  have hTm : f (T (-1)) = g (T (-1)) :=
    calc f (T (-1)) = f (T (-1)) * (g (T 1) * g (T (-1))) := by rw [h2, mul_one]
      _ = (f (T 1) * f (T (-1))) * g (T (-1)) := by rw [← hT]; ring
      _ = g (T (-1)) := by rw [h1, one_mul]
  have hTn : ∀ n : ℤ, f (T n) = g (T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp [T_zero]
    | succ n ih => rw [T_add, map_mul, map_mul, ih, hT]
    | pred n ih => rw [sub_eq_add_neg, T_add, map_mul, map_mul, ih, hTm]
  apply AddMonoidAlgebra.ringHom_ext
  · intro b
    rw [single_eq_C]
    exact congrArg (fun φ : R →+* S => φ b) hC
  · intro n
    exact hTn n

theorem pull_spMap_id (q : ℕ) (A : Type) [CommRing A] (n i : ℤ) (x : Ht q (sp A) n i) :
    pull _ (spMap (RingHom.id A)) _ n x = x := by
  have h : spMap (RingHom.id A) = 𝟙 (sp A) := by
    simp only [spMap]
    rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]
  rw [h, pull_id]

open LaurentPolynomial GmPhiNat in

theorem exists_ht_zero_pull_laurent_eq (q : ℕ) [NeZero q] (R : Type) [CommRing R] (hq : IsUnit (q : R)) (i : ℤ)
    (y : Ht q (sp (LaurentPolynomial R)) 0 i) :
    ∃ z : Ht q (sp R) 0 i, pull _ (spMap (LaurentPolynomial.C : R →+* LaurentPolynomial R)) _ 0 z = y := by
  let ev₁ : LaurentPolynomial R →+* R := eval₂ (RingHom.id R) 1
  have hev : ev₁.comp C = RingHom.id R := RingHom.ext fun a => eval₂_C _ _ a
  refine ⟨pull _ (spMap ev₁) _ 0 y, ?_⟩
  symm
  rw [← sub_eq_zero]
  have hqL : IsUnit (q : LaurentPolynomial R) := by simpa using hq.map (C : R →+* LaurentPolynomial R)
  apply GlobalTheory.EtC.GeomZero.eq_zero_of_geom q (LaurentPolynomial R) hqL i
  intro K _ _ f
  set y' := y - pull _ (spMap (C : R →+* LaurentPolynomial R)) _ 0 (pull _ (spMap ev₁) _ 0 y) with hy'

  have h0 : pull _ (spMap ev₁) _ 0 y' = 0 := by
    rw [hy', map_sub, ← pull_spMap_comp, hev, pull_spMap_id, sub_self]
  let f₀ : R →+* K := f.comp C
  have hT1 : IsUnit (f (T 1)) := by
    refine isUnit_iff_exists_inv.2 ⟨f (T (-1)), ?_⟩
    rw [← map_mul, ← T_add]; simp
  let u : Kˣ := hT1.unit
  let evu : LaurentPolynomial K →+* K := eval₂ (RingHom.id K) u
  have hf : f = evu.comp (laurentMap f₀) := by
    apply laurent_ringHom_ext
    · rw [RingHom.comp_assoc, laurentMap_C, ← RingHom.comp_assoc]
      ext a
      simp [evu, f₀, eval₂_C]
    · simp [evu, laurentMap_T, eval₂_T, u]
  let ev₁K : LaurentPolynomial K →+* K := eval₂ (RingHom.id K) 1
  have hevK : ev₁K.comp C = RingHom.id K := RingHom.ext fun a => eval₂_C _ _ a
  have hcomm : ev₁K.comp (laurentMap f₀) = f₀.comp ev₁ := by
    apply laurent_ringHom_ext
    · rw [RingHom.comp_assoc, laurentMap_C, ← RingHom.comp_assoc, hevK, RingHom.comp_assoc, hev]
      rfl
    · simp [ev₁K, ev₁, laurentMap_T, eval₂_T]
  have hqK : IsUnit (q : K) := by simpa using hq.map f₀
  have hζ : ∃ ζ : K, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
    have hdeg : (Polynomial.cyclotomic q K).degree ≠ 0 := by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨ζ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζ
  have hbij := GlobalTheory.EtC.h_zero_pull_bijective q K (LaurentPolynomial K) (C : K →+* LaurentPolynomial K) hqK hζ
    inferInstance (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he) (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he) i
  have hw : pull _ (spMap (laurentMap f₀)) _ 0 y' = 0 := by
    obtain ⟨v, hv⟩ := hbij.2 (pull _ (spMap (laurentMap f₀)) _ 0 y')
    have hv0 : v = 0 := by
      have e1 : pull _ (spMap ev₁K) _ 0 (pull _ (spMap (C : K →+* LaurentPolynomial K)) _ 0 v) = v := by
        rw [← pull_spMap_comp, hevK, pull_spMap_id]
      rw [← e1, hv, ← pull_spMap_comp, hcomm, pull_spMap_comp, h0, map_zero]
    rw [← hv, hv0, map_zero]
  rw [hf, pull_spMap_comp, hw, map_zero]

end GlobalTheory.EtC.MultiplicativeGroupGlobalSections

end
