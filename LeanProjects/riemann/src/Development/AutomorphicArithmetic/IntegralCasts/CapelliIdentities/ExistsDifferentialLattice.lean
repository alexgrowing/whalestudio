import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

open NumberField in
private theorem UpperTheory.Reformulated.B.ExistsNatMultipleBasisVectorMemLattice.aux {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V)
    (h : Submodule.span E (L : Set V) = ⊤) (x : V) : ∃ d : ℕ, 0 < d ∧ (d : E) • x ∈ L := by
  obtain ⟨⟨t, m, hm, rfl⟩, ht⟩ := multiple_mem_span_of_mem_localization_span
    (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) E (L : Set V) x (h ▸ Submodule.mem_top)
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  have h1 : m • x ∈ L := by simpa [Submonoid.smul_def, Int.cast_smul_eq_zsmul] using ht
  refine ⟨(m * m).toNat, by have := mul_self_pos.mpr hm0; omega, ?_⟩
  rw [Nat.cast_smul_eq_nsmul, ← natCast_zsmul, Int.toNat_of_nonneg (mul_self_nonneg m), mul_smul]
  exact L.smul_of_tower_mem m h1

theorem UpperTheory.Reformulated.B.ExistsNatMultipleBasisVectorMemLattice.exists_dL :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    ∃ (dL : ℕ),
      (0 : ℕ) < dL ∧
        ∀ (i : Fin X.B.I.n),
          (↑dL : X.B.I.E) • Pi.single i (1 : X.B.I.E) ∈
            X.B.I.L := by
  intro D X
  choose d hd hL using fun i : Fin X.B.I.n =>
    UpperTheory.Reformulated.B.ExistsNatMultipleBasisVectorMemLattice.aux X.B.I.L X.B.I.L_span (Pi.single i (1 : X.B.I.E))
  refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  rw [hc, mul_comm, Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
  exact X.B.I.L.smul_of_tower_mem c (hL i)
