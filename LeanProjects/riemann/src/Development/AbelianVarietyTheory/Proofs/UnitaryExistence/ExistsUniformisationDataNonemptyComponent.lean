import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyFrPtComplex
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

namespace DefiniteData

open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_std (x y : Fin r → E) :
    herm (1 : Matrix (Fin r) (Fin r) E) x y = ∑ a, x a * cc (y a) := by
  simp [herm, Matrix.one_apply]

theorem emb_herm_self (φ : E →+* ℂ) (x : Fin r → E) :
    φ (herm (1 : Matrix (Fin r) (Fin r) E) x x) = ((∑ a, ‖φ (x a)‖ ^ 2 : ℝ) : ℂ) := by
  rw [herm_std, map_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, emb_cc, Complex.mul_conj, Complex.normSq_eq_norm_sq]

def stdLat (E : Type) [Field E] [NumberField E] (r : ℕ) : Submodule (𝓞 E) (Fin r → E) :=
  LinearMap.range ((Algebra.linearMap (𝓞 E) E).compLeft (Fin r))

omit [IsCMField E] in
theorem mem_stdLat (x : Fin r → E) : x ∈ stdLat E r ↔ ∀ a, IsIntegral ℤ (x a) := by
  constructor
  · rintro ⟨y, rfl⟩ a
    exact (y a).isIntegral_coe
  · intro h
    exact ⟨fun a => ⟨x a, h a⟩, rfl⟩

omit [IsCMField E] in
theorem single_mem_stdLat (b : Fin r) : (Pi.single b 1 : Fin r → E) ∈ stdLat E r := by
  rw [mem_stdLat]
  intro a
  by_cases h : a = b
  · subst h; simpa using isIntegral_one
  · simpa [h] using isIntegral_zero

theorem stab_finite :
    {γ : GL (Fin r) E | IsUStab (1 : Matrix (Fin r) (Fin r) E) (stdLat E r) γ}.Finite := by
  have hfin := NumberField.Embeddings.finite_of_norm_le (K := E) (A := ℂ) 1
  have hpi := Set.Finite.pi' (fun _ : Fin r => Set.Finite.pi' (fun _ : Fin r => hfin))
  refine Set.Finite.of_finite_image (hpi.subset ?_) ?_
    (f := fun γ : GL (Fin r) E => fun a b => (γ : Matrix (Fin r) (Fin r) E) a b)
  · rintro _ ⟨γ, ⟨hh, hl⟩, rfl⟩ a b
    have hv : ∀ i, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (Pi.single b 1) i =
        (γ : Matrix (Fin r) (Fin r) E) i b := by
      intro i; simp
    refine ⟨?_, fun φ => ?_⟩
    · have := (mem_stdLat _).1 ((hl _).1 (single_mem_stdLat b)) a
      rwa [hv] at this
    · have h1 := congrArg φ (hh (Pi.single b 1) (Pi.single b 1))
      rw [emb_herm_self, emb_herm_self] at h1
      have h2 := Complex.ofReal_injective h1
      have h3 : ∑ i, ‖φ ((Pi.single b 1 : Fin r → E) i)‖ ^ 2 = 1 := by
        rw [Finset.sum_eq_single b]
        · simp
        · intro i _ hi; simp [hi]
        · simp
      rw [h3] at h2
      simp only [hv] at h2
      have h4 : ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ^ 2 ≤ 1 := by
        rw [← h2]
        exact Finset.single_le_sum (f := fun i => ‖φ ((γ : Matrix (Fin r) (Fin r) E) i b)‖ ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ a)
      nlinarith [norm_nonneg (φ ((γ : Matrix (Fin r) (Fin r) E) a b))]
  · intro γ _ δ _ h
    apply Units.ext
    ext a b
    exact congrFun (congrFun h a) b

theorem eq_zero_of_herm_self {x : Fin r → E}
    (h : herm (1 : Matrix (Fin r) (Fin r) E) x x = 0) : x = 0 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 := emb_herm_self φ x
  rw [h, map_zero] at h1
  have h2 : ∑ a, ‖φ (x a)‖ ^ 2 = 0 := by exact_mod_cast h1.symm
  funext a
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 h2 a (Finset.mem_univ a)
  have h4 : φ (x a) = 0 := by simpa using h3
  exact (map_eq_zero_iff φ φ.injective).1 h4

theorem nonempty_data (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) :
    Nonempty (FD.Data E r) := by
  classical
  let X : FD.Data E 1 := inhab
  exact ⟨
  { Ψ := X.Ψ
    cmType := X.cmType
    Gm := 1
    Gm_herm := by
      intro a b
      by_cases h : a = b
      · subst h; simp [cc_one]
      · simp [h, Ne.symm h, cc_zero]
    Gm_det := by simp
    p0 := r
    p0_le := le_rfl
    signature := by
      intro τ
      refine ⟨1, by simp, ?_⟩
      ext a b
      by_cases h : a = b
      · subst h
        simp [gram, hermC, col, sgn, Matrix.one_apply, apply_ite]
      · simp [gram, hermC, col, sgn, Matrix.one_apply, apply_ite, h, Ne.symm h]
    Λ := stdLat E r
    Λ_fg := by
      unfold stdLat
      rw [LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map _
    Λ_span := by
      rw [eq_top_iff]
      intro x _
      rw [pi_eq_sum_univ' x]
      exact Submodule.sum_mem _ fun b _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_stdLat b))
    den := 1
    den_ne := one_ne_zero
    Λ_int := by
      intro x hx y hy
      rw [herm_std, show ((1 : 𝓞 E) : E) = 1 by simp, one_mul]
      exact IsIntegral.sum _ fun a _ =>
        ((mem_stdLat x).1 hx a).mul (isIntegral_cc ((mem_stdLat y).1 hy a))
    Γ := ⊥
    Γ_stab := by
      intro γ hγ
      rw [Subgroup.mem_bot] at hγ
      subst hγ
      simp [IsUStab]
    Γ_index := ⟨(stab_finite (E := E) (r := r)).toFinset, fun γ hγ =>
      ⟨γ, (Set.Finite.mem_toFinset _).2 hγ, by simp⟩⟩
    Γ_free := fun γ hγ _ _ _ _ _ => Subgroup.mem_bot.mp hγ
    χ := fun _ _ => 1
    χ_mul := by intros; simp
    χ_add := by intros; simp
    χ_fin := fun _ => ⟨1, one_pos, by intros; simp⟩
    ξ0 := X.ξ0
    ξ0_im := X.ξ0_im
    ξ0_ne := X.ξ0_ne
    κ0 := X.κ0
    κ0_xi := X.κ0_xi
    κ0_sign := X.κ0_sign
    m := 1
    m_pos := one_pos
    transv := by
      intro ξ _ hiso s _ _
      have hξ := eq_zero_of_herm_self hiso
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      ext a b
      simp [transvMat, hξ, Matrix.one_apply] }⟩

end DefiniteData

theorem exists_unf_nonempty_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ σ : c.F →+* ℂ, ∃ U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q), Nonempty U.Comp := by
  intro E _ _ _ H Dw l Xo c h σ
  obtain ⟨X⟩ := DefiniteData.nonempty_data E (Dw.p + Dw.q)
  obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws
    GlobalTheory.firstFiveLaws.2.1.secTwist E H Dw l Xo c h σ
  exact ⟨{ Comp := Unit, X := fun _ => X, un := fun _ _ => y }, ⟨()⟩⟩

end GlobalTheory
