import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AevalSurjectiveOfSpanCotangent

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem aeval_surjective_of_dUnit_span {K A : Type} [Field K] [CommRing A] [Bialgebra K A]
    [Module.Finite K A] (hconn : ∀ a ∈ augIdeal K A, IsNilpotent a) {d : ℕ} (x : Fin d → A)
    (hx : ∀ i, Coalgebra.counit (R := K) (x i) = 0)
    (hspan : ∀ c : Cot K A, ∃ l : Fin d → K, c = ∑ i, l i • dUnit K (x i)) :
    Function.Surjective (MvPolynomial.aeval (R := K) x) := by
  haveI : IsNoetherianRing A := isNoetherian_of_tower K inferInstance
  have hxm : ∀ i, x i ∈ RingHom.ker (counitAlgHom K A) := fun i => by
    rw [RingHom.mem_ker]; exact hx i
  have hnil : IsNilpotent (RingHom.ker (counitAlgHom K A)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro a ha
    exact mem_nilradical.2 (hconn a ha)
  refine GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent (counitAlgHom K A) hnil x hxm ?_
  intro y hy
  obtain ⟨l, hl⟩ := hspan (dUnit K y)
  refine ⟨l, ?_⟩
  have hmem : y - ∑ i, l i • x i ∈ RingHom.ker (counitAlgHom K A) :=
    sub_mem hy (Ideal.sum_mem _ fun i _ => by
      rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (hxm i))
  have h0 : dUnit K (y - ∑ i, l i • x i) = 0 := by
    have e : dUnit K (y - ∑ i, l i • x i) = dUnit K y - ∑ i, l i • dUnit K (x i) := by
      simp only [dUnit, map_sub, map_sum, map_smul]
    rw [e, ← hl, sub_self]
  rwa [dUnit, AugCot.d_of_mem _ hmem, Ideal.toCotangent_eq_zero] at h0

theorem exists_coords_generate (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) (hG : G.IsConn) :
    ∃ x : ∀ n, Fin (Module.finrank K G.omega) → G.A n,
      (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := K) (x n i) = 0) ∧
        ∀ n, Function.Surjective (MvPolynomial.aeval (R := K) (x n)) := by
  haveI : Module.Finite K (Cot K (G.A 1)) :=
    Module.Finite.of_surjective (AugCot.d (counitAlgHom K (G.A 1))) (AugCot.d_surjective _)
  haveI : Module.Finite K G.omega :=
    Module.Finite.equiv (LinearEquiv.ofBijective _ (G.omegaLevel_one_bijective h)).symm
  set d := Module.finrank K G.omega with hd
  let b := Module.finBasis K G.omega
  have h1 : ∀ i, ∃ a : G.A 1, Coalgebra.counit (R := K) a = 0 ∧ dUnit K a = (b i).1 1 := by
    intro i
    obtain ⟨a, ha⟩ := AugCot.d_surjective (counitAlgHom K (G.A 1)) ((b i).1 1)
    refine ⟨a - algebraMap K _ (Coalgebra.counit (R := K) a), ?_, ?_⟩
    · have e : Coalgebra.counit (R := K) (algebraMap K (G.A 1) (Coalgebra.counit (R := K) a)) =
          Coalgebra.counit (R := K) a := by
        have := (counitAlgHom K (G.A 1)).commutes (Coalgebra.counit (R := K) a)
        simpa using this
      rw [map_sub, e, sub_self]
    · rw [dUnit, map_sub, AugCot.d_algebraMap, sub_zero]; exact ha
  choose x1 hx1c hx1d using h1
  let z : (n : ℕ) → Fin d → G.A (n + 1) := fun n =>
    Nat.rec (motive := fun n => Fin d → G.A (n + 1)) x1
      (fun n zn i => Function.surjInv (G.res_surjective (n + 1)) (zn i)) n
  let x : ∀ n, Fin d → G.A n := fun n =>
    Nat.rec (motive := fun n => Fin d → G.A n) (fun i => G.res 0 (x1 i)) (fun n _ => z n) n
  have hres : ∀ n i, G.res n (x (n + 1) i) = x n i := by
    intro n i
    cases n with
    | zero => rfl
    | succ n => exact Function.surjInv_eq (G.res_surjective (n + 1)) (z n i)
  have hcou1 : ∀ n i, Coalgebra.counit (R := K) (x (n + 1) i) = 0 := by
    intro n
    induction n with
    | zero => exact hx1c
    | succ n ih =>
      intro i
      rw [← ih i, ← hres (n + 1) i, CoalgHomClass.counit_comp_apply]
  have hcou : ∀ n i, Coalgebra.counit (R := K) (x n i) = 0 := by
    intro n i
    cases n with
    | zero => rw [← hres 0 i, CoalgHomClass.counit_comp_apply]; exact hcou1 0 i
    | succ n => exact hcou1 n i
  have hdu : ∀ n i, dUnit K (x (n + 1) i) = (b i).1 (n + 1) := by
    intro n
    induction n with
    | zero => exact hx1d
    | succ n ih =>
      intro i
      obtain ⟨u, hu⟩ := G.omegaLevel_surjective (n + 2) (dUnit K (x (n + 2) i))
      rw [omegaLevel_apply] at hu
      have hn : (u - b i).1 (n + 1) = 0 := by
        change u.1 (n + 1) - (b i).1 (n + 1) = 0
        rw [← ih i, ← cotMap_res_omega, hu, cotMap_d, hres, sub_self]
      have h1' : G.omegaLevel 1 (u - b i) = 0 :=
        G.omega_val_eq_zero_of_le (by omega) hn
      have hub : u = b i := sub_eq_zero.1
        ((G.omegaLevel_one_bijective h).1 (h1'.trans (map_zero _).symm))
      rw [← hu, hub]
  have hspan : ∀ n (c : Cot K (G.A n)), ∃ l : Fin d → K, c = ∑ i, l i • dUnit K (x n i) := by
    intro n c
    cases n with
    | zero => exact ⟨0, by rw [G.cot_zero_eq_zero c]; simp⟩
    | succ n =>
      obtain ⟨w, rfl⟩ := G.omegaLevel_surjective (n + 1) c
      refine ⟨b.repr w, ?_⟩
      conv_lhs => rw [← b.sum_repr w]
      simp only [map_sum, map_smul, omegaLevel_apply, hdu]
      rfl
  exact ⟨x, hres, hcou, fun n =>
    aeval_surjective_of_dUnit_span (hG n) (x n) (hcou n) (hspan n)⟩

end GlobalTheory.PDivGroup
