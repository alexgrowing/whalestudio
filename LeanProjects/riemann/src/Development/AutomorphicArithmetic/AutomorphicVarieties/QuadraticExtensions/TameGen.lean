import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationApplyOfWild

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.tameGen :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ¬ A.valuation (l : Ω) < 1 →
      ∃ γ : Ine (F := F) A, ∀ φ : Ine (F := F) A → ZMod l, IsLocallyConstant φ → (∀ a b, φ (a * b) = φ a + φ b) → φ γ = 0 → ∀ σ, φ σ = 0 := by
  intro F Ω _ _ _ _ _ l _ A hvl
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt_of_valuationSubring (E := F) A
  refine ⟨⟨γ, hγ.1⟩, fun t ht hm h0 => ?_⟩
  have hl : l.Prime := Fact.out
  have t1 : t 1 = 0 := by simpa using hm 1 1
  have tinv : ∀ a, t a⁻¹ = -t a := fun a => by
    have := hm a⁻¹ a
    rw [inv_mul_cancel, t1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have tpow : ∀ a (n : ℕ), t (a ^ n) = n • t a := fun a n => by
    induction n with
    | zero => simp [t1]
    | succ n ih => rw [pow_succ, hm, ih, succ_nsmul]
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  let T : Subgroup (Ine (F := F) A) :=
    { carrier := t ⁻¹' {0}
      one_mem' := t1
      mul_mem' := fun {a b} ha hb => by
        show t (a * b) = 0
        rw [hm, show t a = 0 from ha, show t b = 0 from hb, add_zero]
      inv_mem' := fun {a} ha => by
        show t a⁻¹ = 0
        rw [tinv, show t a = 0 from ha, neg_zero] }
  have ho : IsOpen (t ⁻¹' {0}) := ht _
  refine GlobalTheory.TameCharUnique.mem_of_tameGen hγ T (T.isClosed_of_isOpen ho) h0 fun σ hσ => ?_
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.1 ho
  have hV1 : (1 : G F Ω) ∈ V := by
    have : (1 : Ine (F := F) A) ∈ t ⁻¹' {0} := t1
    rw [← hVU] at this
    exact this
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff F Ω _).mp (hV.mem_nhds hV1)
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ.1
  obtain ⟨a, m, hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  have hτ : σ.1 ^ m ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro x hx
    refine GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ.1 ^ m)
      (GlobalTheory.WildInertiaChar.wild_pow A σ.1 hσ m) (l ^ a) ?_ x ?_
    · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
    · rw [← pow_mul, mul_comm]; exact hmem x hx
  have h2 : σ ^ m ∈ t ⁻¹' {0} := by
    rw [← hVU]
    exact hsub hτ
  have h4 : t (σ ^ m) = 0 := h2
  rw [tpow, nsmul_eq_mul] at h4
  exact (mul_eq_zero.1 h4).resolve_left fun h => hm' ((ZMod.natCast_eq_zero_iff m l).1 h)
