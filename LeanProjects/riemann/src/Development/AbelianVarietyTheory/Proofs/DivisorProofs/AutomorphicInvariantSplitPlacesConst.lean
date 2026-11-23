import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSplitPlaceSkewHermitianUnitar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceSplitsCompletelyNotMemEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNormOneIdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationDetOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDetNormOneBisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleDotMulVecSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneCharacterSplitPlaces
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst

noncomputable section

namespace GlobalTheory.HermConstLift

theorem conj_mem_UAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n : ℕ} {V : Spc F E n} {R : Type} [Zero R] {ev : AF F → R} {k : UA σ V.J} (hk : k ∈ UAt σ V ev) (g : UA σ V.J) :
    g⁻¹ * k * g ∈ UAt σ V ev := by
  intro u hu
  have h : u • (mat k - 1) = 0 := hk u hu
  have h1 : mat g⁻¹ * mat g = 1 := by
    rw [← show mat (g⁻¹ * g) = mat g⁻¹ * mat g from rfl, inv_mul_cancel]; rfl
  have e : mat (g⁻¹ * k * g) - 1 = mat g⁻¹ * (mat k - 1) * mat g := by
    rw [show mat (g⁻¹ * k * g) = mat g⁻¹ * mat k * mat g from rfl, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  show u • (mat (g⁻¹ * k * g) - 1) = 0
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_zero, Matrix.zero_mul]

theorem constant_of_invariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (V : Spc F E n) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s → ∀ (T : Finset (Pl F)) (φ : UA σ V.J → ℂ), Continuous φ →
    (∀ γ ∈ ratU σ V.J, ∀ g, φ (γ * g) = φ g) →
    (∀ v : Pl F, v ∉ T → SplitsFully E v → ∀ g, ∀ k ∈ UAt σ V (evFin F v), φ (g * k) = φ g) → ∀ g g', φ g = φ g' := by
  intro hKP F E _ _ _ _ _ σ B n V r s hB hV T φ hφ hrat hloc
  have hA : ∀ y g : UA σ V.J, (mat y).det = 1 → φ (y * g) = φ g := by
    intro y g hy
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hy1 : y = 1 := by
        apply Subtype.ext; apply Units.ext
        change mat y = 1
        interval_cases n
        · ext i; exact i.elim0
        · ext i j
          have hi : i = 0 := Subsingleton.elim _ _
          have hj : j = 0 := Subsingleton.elim _ _
          subst hi hj
          rw [Matrix.det_unique] at hy
          simpa using hy
      rw [hy1, one_mul]
    · obtain ⟨v, hvT, hvs, hτ⟩ := GlobalTheory.SplitAway.exists_splitsFully_notMem F E T
      have hcl := GlobalTheory.T.strong_approximation_det_one hKP.base.strongApproxSU F E σ B n V r s hB hV hn v hτ y hy
      have hf : Continuous fun x : UA σ V.J => φ (x * g) := hφ.comp (continuous_mul_right g)
      have hmem : y ∈ {x | φ (x * g) = φ g} := by
        refine (isClosed_eq hf continuous_const).closure_subset_iff.2 ?_ hcl
        rintro x ⟨γ, hγ, k, hk, rfl⟩
        show φ (γ * k * g) = φ g
        rw [mul_assoc, hrat γ hγ, show k * g = g * (g⁻¹ * k * g) by group]
        exact hloc v hvT hvs g _ (conj_mem_UAt hk g)
      exact hmem
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro g g'
    congr 1
    apply Subtype.ext; apply Units.ext; ext i; exact i.elim0
  obtain ⟨sec, hsc, hdet, hsrat, hsloc⟩ := GlobalTheory.T.norm_one_idele_section F E σ B n V r s hB hV hn
  let D : UA σ V.J →* (AE F E)ˣ := Matrix.GeneralLinearGroup.det.comp (Subgroup.subtype _)
  have hD : ∀ x : UA σ V.J, ((D x : (AE F E)ˣ) : AE F E) = (mat x).det := fun x => rfl
  have hDm : ∀ x : UA σ V.J, D x ∈ GlobalTheory.NormOneIdele.N1 F E σ := fun x => by
    rw [GlobalTheory.NormOneIdele.mem_normOneIdeles, hD]; exact GlobalTheory.T.unitary_det_norm_one_bis F E σ B n V r s hV x
  let dt : UA σ V.J → GlobalTheory.NormOneIdele.N1 F E σ := fun x => ⟨D x, hDm x⟩
  have key : ∀ g, φ g = φ (sec (dt g)) := by
    intro g
    have hsd : D (sec (dt g)) = D g := Units.ext (by rw [hD, hdet])
    have hy : (mat (g * (sec (dt g))⁻¹)).det = 1 := by
      rw [← hD, map_mul, map_inv, hsd, mul_inv_cancel, Units.val_one]
    have h := hA (g * (sec (dt g))⁻¹) (sec (dt g)) hy
    rw [inv_mul_cancel_right] at h
    exact h
  have hψ := GlobalTheory.T.norm_one_character_split_places hKP F E σ hB.cm hB.galois T (fun z => φ (sec z)) (hφ.comp hsc)
    (fun γ z hγ => by
      show φ (sec (γ * z)) = φ (sec z)
      rw [map_mul]; exact hrat _ (hsrat γ hγ) _)
    (fun v hvT hvs z k hk => by
      show φ (sec (z * k)) = φ (sec z)
      rw [map_mul]; exact hloc v hvT hvs _ _ (hsloc v k hk))
  intro g g'
  rw [key g, key g']
  exact hψ _ _

end GlobalTheory.HermConstLift
