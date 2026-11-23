import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorTestFamilyPreservesLevelForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenProductOfLocalLevelsUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorPreservesEquivariantRightInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantDoubleCosetSectionMemEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantFunctionEqFinsumDoubleCosetSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorEquivariantDoubleCosetSectionBasePoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRationalPointsConjInSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProductOfLocalFunctionsUnitaryNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteUnitaryRationalOfIsOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefiniteUnitaryRationalInfConjLevelTer

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

section Assembly
variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem trOn_eqvM (ι : H →* G) (hι : Function.Injective ι) (ρ : Representation ℂ H V) (K K' : Subgroup G) (F : G → ℂ)
    (hF : ∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x) (hsupp : {q : G ⧸ K' | F q.out ≠ 0}.Finite)
    (hdc : Finite (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G)))
    (hst : ∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G)) :
    trOn (eqvM ι ρ K') (levOp (rightReg ℂ G V) K K' F LinearMap.id) =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G),
        ((stabCard ι K' (Quotient.out q) : ℂ))⁻¹ *
          ∑ᶠ h : H, F ((Quotient.out q)⁻¹ * ι h * Quotient.out q) * LinearMap.trace ℂ V (ρ h) := by
  classical
  have hR : ∀ k ∈ K', ∀ x, F (x * k) = F x := fun k hk x => (hF k hk x).2
  have hmaps := GlobalTheory.T.heckeOperator_preserves_equivariantRightInvariant G H V ι ρ K K' F hF
  unfold trOn
  rw [dif_pos hmaps]
  haveI : Fintype (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G)) := Fintype.ofFinite _
  set T := levOp (rightReg ℂ G V) K K' F LinearMap.id with hT
  set M := eqvM ι ρ K' with hM
  let x : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G) → G := fun q => Quotient.out q
  let e : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G) → (M →ₗ[ℂ] V) :=
    fun q => (LinearMap.proj (R := ℂ) (φ := fun _ : G => V) (x q)).comp M.subtype
  let s : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G) → (V →ₗ[ℂ] M) :=
    fun q => (secM ι ρ K' (x q)).codRestrict M (fun v => GlobalTheory.T.equivariantDoubleCosetSection_mem_equivariant G H V ι ρ K' (x q) v)
  have hid : ∑ q, s q ∘ₗ e q = LinearMap.id := by
    ext φ : 1
    apply Subtype.ext
    have := GlobalTheory.T.equivariantFunction_eq_finsum_doubleCosetSections G H V ι hι ρ K' hdc hst φ.1 φ.2
    rw [finsum_eq_sum_of_fintype] at this
    simpa [s, e, x] using this
  have h1 : ∀ φ : M, φ = ∑ q, s q (e q φ) := fun φ => by
    conv_lhs => rw [← LinearMap.id_apply (R := ℂ) φ, ← hid]
    simp
  haveI : Module.Finite ℂ M := by
    refine Module.Finite.of_injective (LinearMap.pi e) fun a b hab => ?_
    rw [h1 a, h1 b]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show e q a = e q b from congrFun hab q]
  have htr : LinearMap.trace ℂ M (T.restrict hmaps) =
      ∑ q, LinearMap.trace ℂ V (e q ∘ₗ T.restrict hmaps ∘ₗ s q) := by
    have hsum : T.restrict hmaps ∘ₗ (∑ q, s q ∘ₗ e q) = ∑ q, (T.restrict hmaps ∘ₗ s q) ∘ₗ e q := by
      ext φ : 1
      simp [LinearMap.sum_apply, map_sum]
    conv_lhs => rw [← LinearMap.comp_id (T.restrict hmaps), ← hid, hsum, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [LinearMap.trace_comp_comm']
  rw [htr, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hfin := GlobalTheory.T.finite_rationalPoints_conj_in_support G H ι hι K' F hR hsupp (x q) (hst _)
  have hsub : ∀ {β : Type} [AddCommMonoid β] (g : H → β), (∀ h, F ((x q)⁻¹ * ι h * x q) = 0 → g h = 0) →
      Function.support g ⊆ hfin.toFinset := fun g hg h hh => by
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    exact fun h0 => hh (hg h h0)
  have hA : e q ∘ₗ T.restrict hmaps ∘ₗ s q = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ((stabCard ι K' (x q) : ℂ))⁻¹ •
      ∑ h ∈ hfin.toFinset, F ((x q)⁻¹ * ι h * x q) • ρ h := by
    ext v
    have := GlobalTheory.T.heckeOperator_equivariantDoubleCosetSection_basePoint G H V ι hι ρ K K' F hR hsupp (x q) (hst _) hfin v
    rw [finsum_eq_sum_of_support_subset _ (hsub _ fun h h0 => by simp [h0])] at this
    simpa [e, s, LinearMap.restrict_apply, LinearMap.sum_apply] using this
  rw [hA, LinearMap.map_smul, LinearMap.map_smul, map_sum, smul_eq_mul, smul_eq_mul,
    finsum_eq_sum_of_support_subset _ (hsub (fun h => F ((x q)⁻¹ * ι h * x q) * LinearMap.trace ℂ V (ρ h))
      fun h h0 => by simp [h0])]
  simp only [map_smul, smul_eq_mul, x]

end Assembly

end GlobalTheory.BCT.TraceBlocks

namespace GlobalTheory.BCT.TraceBlocks

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finPtHom_injective : Function.Injective (finPtHom (E := E) (n := n)) := by
  intro a b h
  have h1 : finGL E n (ratF E n a.1) = finGL E n (ratF E n b.1) := by
    have := congrArg (fun k : finU E n => (k : UA E n).1) h
    simpa only [finPtHom_apply, FinPtLoc.finPt_eq] using this
  have h2 : ratF E n a.1 = ratF E n b.1 := by
    have := congrArg (GeneralLinearGroup.map (pFin E)) h1
    simpa using this
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩⟩
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact (algebraMap E (Af E)).injective (congrArg (fun g : GL (Fin n) (Af E) => g.val i j) h2)

theorem finPtHom_range : (finPtHom (E := E) (n := n)).range = ratFinU E n := by
  ext k
  constructor
  · rintro ⟨γ, rfl⟩
    refine ⟨γ.1, γ.2, ?_⟩
    have := FinPtLoc.finPt_eq γ
    exact (congrArg Subtype.val this).symm
  · rintro ⟨g, hg, he⟩
    refine ⟨⟨g, hg⟩, Subtype.ext (Subtype.ext ?_)⟩
    rw [finPtHom_apply, FinPtLoc.finPt_eq]
    exact he

end GlobalTheory.BCT.TraceBlocks

open GlobalTheory.BCT.TraceBlocks in

theorem GlobalTheory.BCT.TrKer.trOn_vecM_hopM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (GlobalTheory.BCT.TrKer.vecM S lam K') (GlobalTheory.BCT.TrKer.hopM S lam K' f) = (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ * ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (globLev S K' : Set (finU E n)), ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU E n)) : ℂ))⁻¹ * ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q) * LinearMap.trace ℂ _ (GlobalTheory.BCT.TrKer.wAt lam γ⁻¹) := by
  intro E _ _ _ hU n _ S hS lam K' hK f hf
  have hV : GlobalTheory.BCT.TrKer.vecM S lam K' = eqvM finPtHom (wDual lam) (globLev S K') := rfl
  have hT : GlobalTheory.BCT.TrKer.hopM S lam K' f =
      levOp (rightReg ℂ (finU E n) (Module.Dual ℂ (GlobalTheory.BCT.TrKer.Wsp lam))) (globLev S (KL n)) (globLev S K')
        (globFn S f) LinearMap.id := rfl
  have hF := globFn_inv S K' f fun w => (hf.1 w).2
  have hdc : Finite (DoubleCoset.Quotient ((finPtHom (E := E) (n := n)).range : Set (finU E n))
      (globLev S K' : Set (finU E n))) := by
    rw [finPtHom_range]
    exact GlobalTheory.T.finite_doubleCoset_definiteUnitaryRational_of_isOpen E n _ (GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hU n S K' hK)
  have hst : ∀ x : finU E n, Finite ((finPtHom (E := E) (n := n)).range ⊓
      (globLev S K').map (MulAut.conj x).toMonoidHom : Subgroup (finU E n)) := fun x => by
    rw [finPtHom_range]
    exact GlobalTheory.T.finite_definiteUnitary_rational_inf_conj_level E hU n S hS K' hK x
  rw [hV, hT, trOn_eqvM finPtHom finPtHom_injective (wDual lam) _ _ _ hF (GlobalTheory.T.finite_productOfLocalFunctionsUnitary_ne_zero E hU n S K' hK f hf) hdc hst]
  have htr : ∀ γ : UE E n, LinearMap.trace ℂ _ (wDual lam γ) = LinearMap.trace ℂ _ (GlobalTheory.BCT.TrKer.wAt lam γ⁻¹) :=
    fun γ => LinearMap.trace_transpose' _
  simp only [htr, finPtHom_apply, stabCard]
  rw [finPtHom_range]
