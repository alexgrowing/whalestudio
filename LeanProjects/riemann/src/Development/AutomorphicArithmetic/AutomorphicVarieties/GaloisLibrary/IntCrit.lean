import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange

noncomputable section

open Polynomial

namespace UpperTheory.V.Lib

private theorem move {F : Type} [Field F] [Countable F] (l : ℕ) [Fact l.Prime] (f : F →+* ℂ) (g : F →+* PadicAlgCl l) :
    ∃ ι : PadicAlgCl l ≃+* ℂ, ∀ a, ι.symm (f a) = g a := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  obtain ⟨ι₀⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨e, he⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_over F ℂ (PadicAlgCl l) Cardinal.mk_le_aleph0
    (Cardinal.mk_complex ▸ Cardinal.aleph0_lt_continuum) (Cardinal.mk_congr ι₀.symm.toEquiv)
  exact ⟨e.symm, he⟩

private theorem move_transc (l : ℕ) [Fact l.Prime] {z : ℂ} (hz : Transcendental ℚ z) {t : PadicAlgCl l}
    (ht : Transcendental ℚ t) : ∃ ι : PadicAlgCl l ≃+* ℂ, ι.symm z = t := by
  let F := FractionRing (Polynomial ℚ)
  have hzi : Function.Injective ((Polynomial.aeval z : Polynomial ℚ →ₐ[ℚ] ℂ).toRingHom) :=
    transcendental_iff_injective.1 hz
  have hti : Function.Injective ((Polynomial.aeval t : Polynomial ℚ →ₐ[ℚ] PadicAlgCl l).toRingHom) :=
    transcendental_iff_injective.1 ht
  have hP : Countable (Polynomial ℚ) := by
    have := Polynomial.cardinalMk_le_max (R := ℚ)
    rw [Cardinal.mkRat, max_self] at this
    exact Cardinal.mk_le_aleph0_iff.1 this
  have hF : Countable F := by
    have hs : Function.Surjective
        (fun q : Polynomial ℚ × nonZeroDivisors (Polynomial ℚ) => IsLocalization.mk' F q.1 q.2) := by
      intro w
      obtain ⟨a, h⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (Polynomial ℚ)) w
      exact ⟨a, h⟩
    exact hs.countable
  obtain ⟨e, he⟩ := move (F := F) l (IsFractionRing.lift hzi) (IsFractionRing.lift hti)
  refine ⟨e, ?_⟩
  have h := he (algebraMap (Polynomial ℚ) F Polynomial.X)
  rw [IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap] at h
  simpa using h

open IntermediateField in
private theorem move_alg (l : ℕ) [Fact l.Prime] {z : ℂ} (hz : IsIntegral ℚ z) {t : PadicAlgCl l}
    (ht : t ∈ (minpoly ℚ z).aroots (PadicAlgCl l)) : ∃ ι : PadicAlgCl l ≃+* ℂ, ι.symm z = t := by
  have := adjoin.finiteDimensional hz
  have : Countable ℚ⟮z⟯ := Countable.of_equiv _ (Module.finBasis ℚ ℚ⟮z⟯).equivFun.toEquiv.symm
  obtain ⟨e, he⟩ := move (F := ℚ⟮z⟯) l (algebraMap _ ℂ) ((algHomAdjoinIntegralEquiv ℚ hz).symm ⟨t, ht⟩).toRingHom
  exact ⟨e, (he (AdjoinSimple.gen ℚ z)).trans (algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hz ⟨t, ht⟩)⟩

private theorem norm_rat (l : ℕ) [Fact l.Prime] (q : ℚ) : ‖(q : PadicAlgCl l)‖ = ‖(q : ℚ_[l])‖ := by
  rw [← map_ratCast (algebraMap ℚ_[l] (PadicAlgCl l))]
  exact norm_algebraMap' _ _

theorem isIntegral_of_norm_le (x : ℂ) (h : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ), ‖ι.symm x‖ ≤ 1) :
    IsIntegral ℤ x := by
  have halg : IsAlgebraic ℚ x := by
    by_contra hx
    obtain ⟨ι₀⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
    have ht : Transcendental ℚ (ι₀.symm x + ((1 / 4 : ℚ) : PadicAlgCl 2)) := fun h1 => hx (by
      have h2 : IsAlgebraic ℚ (ι₀.symm x) := by
        simpa using h1.sub (isAlgebraic_rat ℚ (1 / 4 : ℚ))
      simpa using h2.algHom ι₀.toRingHom.toRatAlgHom)
    obtain ⟨ι, hι⟩ := move_transc 2 hx ht
    have h1 := h 2 ι
    have h2 := h 2 ι₀
    rw [hι] at h1
    have h3 := norm_sub_le (ι₀.symm x + ((1 / 4 : ℚ) : PadicAlgCl 2)) (ι₀.symm x)
    rw [add_sub_cancel_left, norm_rat] at h3
    have h4 : ‖((1 / 4 : ℚ) : ℚ_[2])‖ = 4 := by
      have := Padic.norm_p_zpow (p := 2) (-2)
      norm_num at this ⊢
      rw [← this]
    linarith
  have hx := halg.isIntegral
  have hm := minpoly.monic hx
  have hc : ∀ i, (minpoly ℚ x).coeff i ∈ Set.range (algebraMap ℤ ℚ) := by
    intro i
    set q := (minpoly ℚ x).coeff i with hq
    refine ⟨q.num, Rat.coe_int_num_of_den_eq_one ?_⟩
    by_contra hd
    obtain ⟨l, hl, hld⟩ := Nat.exists_prime_and_dvd hd
    haveI := Fact.mk hl
    let S : Subring (PadicAlgCl l) := (NormedField.valuation (K := PadicAlgCl l)).integer
    have hS : ∀ y, y ∈ S ↔ ‖y‖ ≤ 1 := fun y => Iff.rfl
    have h1 : (minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl l)) ∈ lifts S.subtype := by
      rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hm.map _)]
      refine Subsemiring.multiset_prod_mem _ _ fun y hy => ?_
      obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hy
      obtain ⟨ι, hι⟩ := move_alg l hx ht
      exact ⟨X - C ⟨t, (hS t).2 (hι ▸ h l ι)⟩, by simp⟩
    obtain ⟨y, hy⟩ := (lifts_iff_coeff_lifts _).1 h1 i
    have h2 : ‖(q : ℚ_[l])‖ ≤ 1 := by
      rw [← norm_rat, ← hS]
      rw [coeff_map] at hy
      exact (show (q : PadicAlgCl l) = y from hy.symm) ▸ y.2
    have h3 := PadicInt.isUnit_den q h2
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff] at h3
    exact (Nat.Prime.coprime_iff_not_dvd hl).1 h3 hld
  obtain ⟨f, hf, -, hfm⟩ := lifts_and_natDegree_eq_and_monic ((lifts_iff_coeff_lifts _).2 hc) hm
  exact ⟨f, hfm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ, hf, minpoly.aeval]⟩

open scoped Matrix in

theorem norm_root_eq_one {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField k] {n : ℕ}
    (r : Γ →* GL (Fin n) k) (hr : Continuous r) (g : Γ) (b : k)
    (hb : (r g : Matrix (Fin n) (Fin n) k).charpoly.IsRoot b) : ‖b‖ = 1 := by
  rw [IsRoot, Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff] at hb
  obtain ⟨v, hv, e⟩ := hb
  have e1 : (r g : Matrix (Fin n) (Fin n) k) *ᵥ v = b • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at e
    rw [← e]; ext i; simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  let f : Γ → ℝ := fun s => ‖(r s : Matrix (Fin n) (Fin n) k) *ᵥ v‖
  have hf : Continuous f := ((Units.continuous_val.comp hr).matrix_mulVec continuous_const).norm
  have hpos : ∀ s, 0 < f s := fun s => norm_pos_iff.2 fun h0 => hv (by
    have := congrArg (fun y => (r s⁻¹ : Matrix (Fin n) (Fin n) k) *ᵥ y) h0
    simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_zero] using this)
  have hm : ∀ s, f (s * g) = ‖b‖ * f s := fun s => by
    simp only [f, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, e1, Matrix.mulVec_smul, norm_smul]
  obtain ⟨s, -, hs⟩ := isCompact_univ.exists_isMaxOn ⟨1, trivial⟩ hf.continuousOn
  obtain ⟨t, -, ht⟩ := isCompact_univ.exists_isMinOn ⟨1, trivial⟩ hf.continuousOn
  have h1 : f (s * g) ≤ f s := hs trivial
  have h2 : f t ≤ f (t * g) := ht trivial
  rw [hm] at h1 h2
  have := hpos s
  have := hpos t
  apply le_antisymm <;> nlinarith

end UpperTheory.V.Lib
