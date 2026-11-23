import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqPowOfWeilDegreeEqSmooth

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.FrobSemisimple

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem minpoly_eval_zero_ne_zero {f : End ℂ V} (hf : IsUnit f) : (minpoly ℂ f).eval 0 ≠ 0 := by
  intro h0
  have h1 : f.HasEigenvalue 0 := End.hasEigenvalue_iff_isRoot.mpr h0
  exact spectrum.zero_notMem ℂ hf (End.hasEigenvalue_iff_mem_spectrum.mp h1)

theorem isSemisimple_of_pow {g : End ℂ V} (hg : IsUnit g) {m : ℕ} (hm : 0 < m)
    (hs : (g ^ m).IsSemisimple) : g.IsSemisimple := by
  have hsep : (minpoly ℂ (g ^ m)).Separable :=
    PerfectField.separable_iff_squarefree.mpr hs.minpoly_squarefree
  have h0 := minpoly_eval_zero_ne_zero (hg.pow m)
  set p := minpoly ℂ (g ^ m) with hp
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := expand ℂ m p)
    (Separable.squarefree ?_) ?_
  · rw [Separable, derivative_expand]
    refine IsCoprime.mul_right (IsCoprime.map hsep (expand ℂ m).toRingHom)
      (IsCoprime.mul_right ?_ (IsCoprime.pow_right ?_))
    · have : IsUnit ((m : ℕ) : ℂ[X]) := by
        rw [← C_eq_natCast]
        exact isUnit_C.mpr (Ne.isUnit (Nat.cast_ne_zero.mpr hm.ne'))
      exact (isCoprime_mul_unit_left_right this _ 1).mpr isCoprime_one_right |>.of_mul_right_left
    · refine ((irreducible_X.coprime_iff_not_dvd).mpr ?_).symm
      rw [X_dvd_iff, coeff_zero_eq_eval_zero, expand_eval, zero_pow hm.ne']
      exact h0
  · rw [expand_aeval]
    exact minpoly.aeval ℂ _

end GlobalTheory.WeilDeligne.FrobSemisimple

namespace GlobalTheory.WeilDeligne

open NumberField IsDedekindDomain Polynomial Module in
private theorem isSemisimple_of_mul_eq_one' {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {f g : End ℂ V} (hf : f.IsSemisimple) (hgf : g * f = 1) :
    g.IsSemisimple := by
  apply _root_.GlobalTheory.WeilDeligne.isSemisimple_of_iSup_eigenspace
  have htop : ⨆ α, f.eigenspace α = ⊤ :=
    hf.iSup_maxGenEigenspace_eq_top_iff.1 (Module.End.iSup_maxGenEigenspace_eq_top f)
  rw [eq_top_iff, ← htop]
  refine iSup_le fun α => le_trans ?_ (le_iSup _ α⁻¹)
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h1 : v = α • g v := by
    have := congrArg g hv
    rwa [← Module.End.mul_apply, hgf, Module.End.one_apply, map_smul] at this
  by_cases hα : α = 0
  · subst hα
    rw [zero_smul] at h1
    simp [h1]
  · conv_rhs => rw [h1]
    rw [smul_smul, inv_mul_cancel₀ hα, one_smul]

open NumberField IsDedekindDomain Polynomial Module in
private theorem isSemisimple_of_isUnit_of_pow_isSemisimple {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] {f : End ℂ V} (hf : IsUnit f) {m : ℕ} (hm : 0 < m)
    (hfm : (f ^ m).IsSemisimple) : f.IsSemisimple := by
  have hint : IsIntegral ℂ (f ^ m) := Algebra.IsIntegral.isIntegral _
  have hX : ¬ X ∣ minpoly ℂ (f ^ m) := by
    rintro ⟨q, hq⟩
    have h0 : aeval (f ^ m) q = 0 := by
      have h1 := minpoly.aeval ℂ (f ^ m)
      rw [hq, map_mul, aeval_X] at h1
      exact (hf.pow m).mul_right_eq_zero.1 h1
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact minpoly.ne_zero hint (by simpa using hq)
    have hdeg := natDegree_le_of_dvd (minpoly.dvd ℂ (f ^ m) h0) hq0
    rw [hq, natDegree_mul X_ne_zero hq0, natDegree_X] at hdeg
    omega
  have hsep : (minpoly ℂ (f ^ m)).Separable :=
    PerfectField.separable_iff_squarefree.2 hfm.minpoly_squarefree
  have hXe : ¬ X ∣ expand ℂ m (minpoly ℂ (f ^ m)) := by
    rw [X_dvd_iff, coeff_expand hm]
    rw [X_dvd_iff] at hX
    simpa using hX
  have hunit : IsUnit ((m : ℂ[X])) := by
    rw [← map_natCast C]
    exact isUnit_C.2 (Ne.isUnit (by exact_mod_cast hm.ne'))
  have hP : (expand ℂ m (minpoly ℂ (f ^ m))).Separable := by
    rw [separable_def, derivative_expand]
    refine IsCoprime.mul_right
      (((separable_def _).1 hsep).map (expand ℂ m).toRingHom) (IsCoprime.mul_right ?_ ?_)
    · exact isCoprime_one_right.of_isCoprime_of_dvd_right (hunit.dvd)
    · exact IsCoprime.pow_right ((Irreducible.coprime_iff_not_dvd irreducible_X).2 hXe).symm
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hP.squarefree
  rw [expand_aeval]
  exact minpoly.aeval ℂ (f ^ m)

open NumberField IsDedekindDomain Polynomial Module in

theorem _root_.GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type)
      [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (_root_.GlobalTheory.WeilDeligne.Weil h) V),
      _root_.GlobalTheory.WeilDeligne.IsSmooth ρ → ∀ φ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.GlobalTheory.WeilDeligne.deg φ = 1 →
      End.IsSemisimple (ρ φ) → ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, End.IsSemisimple (ρ σ) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ hρ φ hφ hss σ
  have hunit : IsUnit (ρ σ) := (Group.isUnit σ).map ρ
  obtain ⟨τ, hτdeg, hτ⟩ : ∃ τ : _root_.GlobalTheory.WeilDeligne.Weil h,
      _root_.GlobalTheory.WeilDeligne.deg τ = _root_.GlobalTheory.WeilDeligne.deg σ ∧ End.IsSemisimple (ρ τ) := by
    rcases le_or_gt 0 (_root_.GlobalTheory.WeilDeligne.deg σ) with hd | hd
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hd
      refine ⟨φ ^ k, by rw [_root_.GlobalTheory.WeilDeligne.deg_pow, hφ, hk]; ring, ?_⟩
      rw [map_pow]
      exact hss.of_mem_adjoin_singleton (pow_mem (Algebra.self_mem_adjoin_singleton ℂ _) k)
    · obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat hd.le
      have hinv : End.IsSemisimple (ρ φ⁻¹) :=
        isSemisimple_of_mul_eq_one' hss (by rw [← map_mul, inv_mul_cancel, map_one])
      refine ⟨φ⁻¹ ^ k, ?_, ?_⟩
      · rw [_root_.GlobalTheory.WeilDeligne.deg_pow, ← zpow_neg_one, _root_.GlobalTheory.WeilDeligne.deg_zpow, hφ, hk]
        ring
      · rw [map_pow]
        exact hinv.of_mem_adjoin_singleton (pow_mem (Algebra.self_mem_adjoin_singleton ℂ _) k)
  obtain ⟨m, hm, hpow⟩ :=
    _root_.GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq E Ω A w h V ρ hρ σ τ hτdeg.symm
  apply isSemisimple_of_isUnit_of_pow_isSemisimple hunit hm
  rw [hpow]
  exact hτ.of_mem_adjoin_singleton (pow_mem (Algebra.self_mem_adjoin_singleton ℂ _) m)

end GlobalTheory.WeilDeligne
