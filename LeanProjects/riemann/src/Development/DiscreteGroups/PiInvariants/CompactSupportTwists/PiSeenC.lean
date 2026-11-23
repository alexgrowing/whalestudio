import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenB

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal Pointwise

namespace DiscreteGroups.T1.G.Dcy

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem eq_zero_of_ae (D : Dom E n 0) {π : CuspSub E n} {φ : Sm E n} (hφ : φ ∈ π.V)
    (h : ∀ᵐ x ∂D.ν, φ.1 x.1 = 0) : φ = 0 := by
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  have := D.haar.1
  haveI := D.haar.2.2.1
  have : MeasurableConstSMul (ratH E n 0) (H E n 0) := ⟨fun γ => measurable_const_mul (γ : H E n 0)⟩
  have : SMulInvariantMeasure (ratH E n 0) (H E n 0) D.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have := countable_ratH' (E := E) (n := n)
  set Z : Set (H E n 0) := {x | φ.1 x.1 ≠ 0} with hZ
  have hφc := continuous_of_mem π hφ
  have hZo : IsOpen Z := isOpen_ne_fun (hφc.comp (continuous_fst (X := GA E n) (Y := GA E 0))) continuous_const
  have hνZ : D.ν Z = 0 := ae_iff.1 h
  have hμZF : D.μ (Z ∩ D.F) = 0 := by
    rw [← Measure.restrict_apply hZo.measurableSet]
    exact hνZ
  have hinv : ∀ γ : ratH E n 0, γ • Z = Z := by
    intro γ
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    obtain ⟨p, hp⟩ := (γ⁻¹).2
    have h1 : ((γ⁻¹ • y : H E n 0)).1 = ratGL E n p.1 * y.1 := by
      rw [Subgroup.smul_def, smul_eq_mul, Prod.fst_mul, ← hp]
      rfl
    simp only [hZ, Set.mem_setOf_eq, h1, (π.cusp φ hφ).1.left]
  have hμZ : D.μ Z = 0 := D.fd.measure_zero_of_invariant Z hinv hμZF
  have hZe : Z = ∅ := (hZo.measure_eq_zero_iff D.μ).1 hμZ
  refine Subtype.ext (funext fun g => ?_)
  by_contra hg
  have : ((g, 1) : H E n 0) ∈ Z := hg
  rw [hZe] at this
  exact this

theorem piSeen_holds : PiSeen := by
  intro E _ _ _ n hn D π hθ W hWle hWfd
  haveI := hWfd
  set r := Module.finrank ℂ W with hr
  set b := Module.finBasis ℂ W with hb
  set e : ℕ ≃ ℕ × ℕ × ℕ := (Denumerable.eqv (ℕ × ℕ × ℕ)).symm with he
  refine ⟨fun j => if h : (e j).1 < r then ((b ⟨(e j).1, h⟩ : W) : Sm E n) else 0,
    fun j s => ((chi (e j).2.1 s * s ^ (e j).2.2 : ℝ) : ℂ), fun j => ⟨?_, ?_, ?_⟩, ?_⟩
  · dsimp only
    split_ifs
    · exact hWle (b _).2
    · exact π.V.zero_mem
  · exact Complex.continuous_ofReal.comp ((continuous_chi _).mul (continuous_pow _))
  · exact (hasCompactSupport_chi_pow _ _).comp_left Complex.ofReal_zero
  intro φ hφ z hz
  have hφV : φ ∈ π.V := hWle hφ

  have hbv : ∀ (a : Fin r) (N k : ℕ), ∫ x, starRingEnd ℂ (((b a : W) : Sm E n).1 x.1 *
      ((chi N (ldet x) * ldet x ^ k : ℝ) : ℂ)) * (φ.1 x.1 * Complex.exp (z * ldet x)) ∂D.ν = 0 := by
    intro a N k
    have h := hz (e.symm (a.1, N, k))
    simp only [Equiv.apply_symm_apply, dif_pos a.2, Fin.eta] at h
    exact h
  have hrep : ∀ g, φ.1 g = ∑ a, (b.repr ⟨φ, hφ⟩ a) * ((b a : W) : Sm E n).1 g := by
    intro g
    have h := congrArg (fun w : W => ((w : Sm E n) : GA E n → ℂ) g) (b.sum_repr ⟨φ, hφ⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm

  have hself : ∀ N k : ℕ, ∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * ldet x ^ k : ℝ) : ℂ) *
      Complex.exp (z * ldet x) ∂D.ν = 0 := by
    intro N k
    have hpt : ∀ x : H E n 0, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * ldet x ^ k : ℝ) : ℂ) *
        Complex.exp (z * ldet x) = ∑ a, starRingEnd ℂ (b.repr ⟨φ, hφ⟩ a) *
          (starRingEnd ℂ (((b a : W) : Sm E n).1 x.1 * ((chi N (ldet x) * ldet x ^ k : ℝ) : ℂ)) *
            (φ.1 x.1 * Complex.exp (z * ldet x))) := by
      intro x
      rw [← conj_sum_mul Finset.univ (fun a => b.repr ⟨φ, hφ⟩ a) (fun a => ((b a : W) : Sm E n).1 x.1)
        (((chi N (ldet x) * ldet x ^ k : ℝ) : ℂ)) (φ.1 x.1 * Complex.exp (z * ldet x)), ← hrep x.1,
        map_mul, Complex.conj_ofReal, ← conj_self]
      ring
    simp_rw [hpt]
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero fun a _ => ?_
      rw [integral_const_mul, hbv a N k, mul_zero]
    · intro a _
      refine Integrable.const_mul ?_ _
      exact integrable_pair hn D hθ (hWle (b a).2) hφV (fun s => ((chi N s * s ^ k : ℝ) : ℂ))
        (fun s => Complex.exp (z * s)) (Complex.continuous_ofReal.comp ((continuous_chi N).mul (continuous_pow k)))
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)) ((N : ℝ) + 1)
        (fun s hs => by simp [chi_zero_of hs])
  have hT : ∀ N : ℕ, ∫ x, ‖φ.1 x.1‖ ^ 2 * chi N (ldet x) ∂D.ν = 0 := fun N =>
    sq_zero hn D hθ hφV z N (poly_vanish hn D hθ hφV z N (hself N))
  have hae : ∀ N : ℕ, (fun x : H E n 0 => ‖φ.1 x.1‖ ^ 2 * chi N (ldet x)) =ᵐ[D.ν] 0 := by
    intro N
    have hΦ := integrable_sq hn D hθ hφV (fun s => ((chi N s : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp (continuous_chi N)) ((N : ℝ) + 1) (fun s hs => by simp [chi_zero_of hs])
    have hr : Integrable (fun x : H E n 0 => ‖φ.1 x.1‖ ^ 2 * chi N (ldet x)) D.ν := by
      refine hΦ.norm.congr (Eventually.of_forall fun x => ?_)
      show ‖((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ)‖ = ‖φ.1 x.1‖ ^ 2 * chi N (ldet x)
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), abs_of_nonneg (chi_nonneg _ _)]
    exact (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (by positivity) (chi_nonneg _ _)) hr).1 (hT N)
  have hall : ∀ᵐ x ∂D.ν, ∀ N : ℕ, ‖φ.1 x.1‖ ^ 2 * chi N (ldet x) = 0 := ae_all_iff.2 hae
  refine eq_zero_of_ae D hφV (hall.mono fun x hx => ?_)
  have h1 := hx ⌈|ldet x|⌉₊
  rw [chi_eq_one (Nat.le_ceil _), mul_one] at h1
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)

end DiscreteGroups.T1.G.Dcy

end
