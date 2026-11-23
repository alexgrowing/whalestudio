import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.ExistsAdmissibleEquivariantFormsRep
import Development.AutomorphicArithmetic.DivisorFrames.SpanHighestWeightRepUnitaryGroupRealPointsImageE
import Development.AutomorphicArithmetic.DivisorFrames.HasWeightAtOfNeZeroIntertwining
import Development.AutomorphicArithmetic.DivisorFrames.ExistsInvariantNondegeneratePairingWeightRepNabl
import Development.AutomorphicArithmetic.DivisorFrames.FiniteDimensionalNablaTAndContinuousWtOp
import Development.AutomorphicArithmetic.DivisorFrames.IsAutFormUOfVectorValuedInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

private theorem cont_cEmb {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (τ : E →+* ℂ) :
    Continuous (cEmb (E := E) (n := n) τ) := by
  have c0 : Continuous (coord τ) := by
    unfold coord
    split_ifs
    · exact continuous_apply _
    · exact Complex.continuous_conj.comp (continuous_apply _)
  have c2 : Continuous (infEq E).symm := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  have c3 : Continuous (pInf E) := c2.comp continuous_fst
  have c4 : Continuous fun a => coord τ (pInf E a) := c0.comp c3
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map c4
  · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map c4

theorem UpperTheory.exists_unitaryAutomorphicForm_of_weightVectorValued :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (emb : ι → (E →+* ℂ)), Function.Injective (fun τ => InfinitePlace.mk (emb τ)) →
        ∀ (mu : ι → ℕ → ℕ) (sh : ι → ℤ) (lam : ι → DomWeight n), (∀ τ (a : Fin n), (lam τ).w a = (mu τ a : ℤ) + sh τ) →
        ∀ (B : (UA E n → ℂ) →ₗ⋆[ℂ] (UA E n → ℂ) →ₗ[ℂ] ℂ), (∀ φ, IsAutFormU φ → φ ≠ 0 → 0 < (B φ φ).re) →
        (∀ k ∈ finU E n, ∀ φ ψ, IsAutFormU φ → IsAutFormU ψ → B (RU E n k φ) (RU E n k ψ) = B φ ψ) →
        ∀ F1 : UA E n → NablaT ℂ n mu, F1 ≠ 0 →
        (∀ γ ∈ ratU E n, ∀ g, F1 (γ * g) = wtOp ℂ n mu sh (fun τ => cEmb (emb τ) γ) (F1 g)) →
        (∀ x ∈ infU E n, ∀ g, F1 (g * x) = F1 g) → (∀ᶠ y in nhds (1 : UA E n), ∀ g, F1 (g * y) = F1 g) →
        ∃ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π ∧ (∀ τ, HasWeightAt π (emb τ) (lam τ)) ∧ ∃ φ ∈ π, φ ≠ 0 ∧
          ∀ (κ : Type) (s : Finset κ) (y : κ → UA E n) (c : ℂ), (∀ i ∈ s, y i ∈ finU E n) →
            (∀ g, ∑ i ∈ s, F1 (g * y i) = c • F1 g) → ∑ i ∈ s, RU E n (y i) φ = c • φ := by
  intro E _ _ _ n ι _ _ emb hinj mu sh lam hl B hpos hinv F1 hF0 hrat hinf hev
  let C : UA E n →* (ι → GL (Fin n) ℂ) := MonoidHom.pi fun τ => cEmb (E := E) (n := n) (emb τ)
  let R : UA E n →* Module.End ℂ (NablaT ℂ n mu) := (wtHom ℂ n mu sh).comp C
  have hR : ∀ g, R g = wtOp ℂ n mu sh (C g) := fun _ => rfl
  have hRfin : ∀ k ∈ finU E n, R k = 1 := fun k hk => by
    have h1 : C k = 1 := by
      funext τ
      change Matrix.GeneralLinearGroup.map (coord (emb τ)) (cInf k) = 1
      rw [MonoidHom.mem_ker.1 hk, map_one]
    rw [hR, h1, wtOp_one]
  obtain ⟨hfd, hcont⟩ := UpperTheory.finiteDimensional_nablaT_and_continuous_wtOp n ι mu sh
  have hC : Continuous C := continuous_pi fun τ => cont_cEmb (emb τ)
  obtain ⟨P, hP0, hP⟩ := UpperTheory.exists_invariant_nondegenerate_pairing_weightRep_nablaT n ι mu sh lam hl
  let f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] (UA E n → ℂ) :=
    { toFun := fun v g => P v (R g⁻¹ (F1 g))
      map_add' := fun a b => funext fun g => by simp
      map_smul' := fun a b => funext fun g => by simp }
  have hf : ∀ v g, f v g = P v (R g⁻¹ (F1 g)) := fun _ _ => rfl
  have hRU : ∀ (x : UA E n) (φ : UA E n → ℂ) (g : UA E n), RU E n x φ g = φ (g * x) := fun _ _ _ => rfl
  have hfa : ∀ v, IsAutFormU (f v) := fun v =>
    UpperTheory.isAutFormU_of_vectorValued_invariant E n (NablaT ℂ n mu) R hRfin (fun ℓ u => (hcont ℓ u).comp hC) F1 hrat hinf hev (P v)
  have hfe : ∀ x ∈ infU E n, ∀ v, f (Formalism.L2.DIV.rhoK lam (C x) v) = RU E n x (f v) := fun x hx v => by
    funext g
    rw [hRU, hf, hf, hinf x hx, ← hP (C x) v (R (g * x)⁻¹ (F1 g)), ← hR, ← Module.End.mul_apply, ← map_mul,
      mul_inv_rev, mul_inv_cancel_left]
  have hf0 : f ≠ 0 := fun h0 => hF0 (funext fun g => by
    have h1 : R g⁻¹ (F1 g) = 0 := hP0 _ fun v => by rw [← hf, h0]; rfl
    have h2 := congrArg (R g) h1
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero] at h2
    exact h2)
  haveI : Nontrivial (Formalism.L2.DIV.VV ℂ lam) := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hf0 (LinearMap.ext fun v => by rw [Subsingleton.elim v 0, map_zero, map_zero])
  haveI : ∀ v, Finite (Formalism.GradedWeylDivisibility.ssIdx n n (lam v).natW) := fun _ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  haveI : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam) := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam)
  obtain ⟨π, hπ, f', hf'0, hf'π, hf'e, hsum⟩ := UpperTheory.exists_admissible_equivariantFormsRep E n (Formalism.L2.DIV.VV ℂ lam)
    ((Formalism.L2.DIV.rhoK (K := ℂ) lam).comp (C.comp (infU E n).subtype)) (UpperTheory.span_highestWeightRep_unitaryGroup_realPoints_image_eq_top E n ι emb hinj lam) B hpos hinv
    f hf0 hfa (fun x v => hfe x.1 x.2 v)
  obtain ⟨v, hv⟩ : ∃ v, f' v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf'0 (LinearMap.ext hc)
  refine ⟨π, hπ, UpperTheory.hasWeightAt_of_ne_zero_intertwining E n ι emb hinj lam π f' hf'0 hf'π (fun x hx v => hf'e ⟨x, hx⟩ v), f' v, hf'π v, hv,
    fun κ s y c hy hs => hsum κ s y c hy (fun w => ?_) v⟩
  funext g
  rw [Finset.sum_apply, Pi.smul_apply, hf, ← map_smul, ← map_smul, ← hs g, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hRU, hf, mul_inv_rev, map_mul, hRfin _ ((finU E n).inv_mem (hy i hi)), one_mul]
