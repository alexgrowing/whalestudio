import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLevelFamilyIff
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.GeoFin

theorem nrmL_mem_KGL {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (hL : IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) (GlobalTheory.LFun.KGL w n)) {y : GLw n w}
    (hy : y ∈ GlobalTheory.LFun.KGL w n) : nrmL n w y ∈ GlobalTheory.LFun.KGL w n := by
  have ht := hL.2.2 y hy
  unfold nrmL
  unfold thL at ht
  split_ifs with hs
  · exact hy
  · rw [if_neg hs] at ht
    exact mul_mem hy ht

theorem charpoly_coeff_of_mem_KGL {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E)
    {z : GL (Fin n) (w.adicCompletion E)} (hz : z ∈ GlobalTheory.LFun.KGL w n) :
    (∀ i, Valued.v (z.val.charpoly.coeff i) ≤ 1) ∧ 1 ≤ Valued.v (z.val.charpoly.coeff 0) := by
  obtain ⟨g, rfl⟩ := hz
  set f := (Ov E w).subtype
  have hcp : (Formalism.UG.bc f g).val.charpoly = g.val.charpoly.map f := by
    rw [← Matrix.charpoly_map]
    rfl
  have hint : ∀ a : Ov E w, Valued.v (f a) ≤ 1 := fun a => a.2
  refine ⟨fun i => ?_, ?_⟩
  · rw [hcp, Polynomial.coeff_map]
    exact hint _
  · rw [hcp, Polynomial.coeff_map]
    have hdet : IsUnit (g.val.charpoly.coeff 0) := by
      have h1 : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
      rw [Matrix.det_eq_sign_charpoly_coeff] at h1
      exact isUnit_of_mul_isUnit_right h1
    obtain ⟨u, hu⟩ := hdet
    have hmul : f (u : Ov E w) * f ((u⁻¹ : (Ov E w)ˣ) : Ov E w) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 : Valued.v (f (u : Ov E w)) * Valued.v (f ((u⁻¹ : (Ov E w)ˣ) : Ov E w)) = 1 := by
      rw [← map_mul, hmul, map_one]
    rw [← hu]
    calc (1 : _) = Valued.v (f (u : Ov E w)) * Valued.v (f ((u⁻¹ : (Ov E w)ˣ) : Ov E w)) := h2.symm
      _ ≤ Valued.v (f (u : Ov E w)) * 1 := mul_le_mul' le_rfl (hint _)
      _ = Valued.v (f (u : Ov E w)) := mul_one _

theorem charpoly_nrmL_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) (GlobalTheory.LFun.KGL w n) → ∀ y ∈ GlobalTheory.LFun.KGL w n,
      (∀ i, Valued.v ((nrmL n w y).val.charpoly.coeff i) ≤ 1) ∧ 1 ≤ Valued.v ((nrmL n w y).val.charpoly.coeff 0) :=
  fun _ _ _ _ n w hL y hy => charpoly_coeff_of_mem_KGL n w (nrmL_mem_KGL n w hL hy)

end GlobalTheory.BCT.GeoFin
