import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsCounitEqOneMulEqZeroOfIsNilpotent

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
open scoped TensorProduct

namespace PositivityTheory.HtPt.Rf

theorem exists_pt_of_gen {C R A : Type} [Field C] [CommRing R] [IsDomain R] [Algebra R C]
    [IsFractionRing R C] [IsIntegrallyClosed R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (φ : A →ₐ[R] C) : ∃ ψ : A →ₐ[R] R, ∀ a, algebraMap R C (ψ a) = φ a := by
  have h : ∀ a : A, ∃ r : R, algebraMap R C r = φ a := fun a =>
    IsIntegrallyClosed.isIntegral_iff.1 ((Algebra.IsIntegral.isIntegral (R := R) a).map φ)
  choose f hf using h
  have inj := IsFractionRing.injective R C
  let ψ : A →ₐ[R] R :=
    { toFun := f,
      map_one' := inj (by rw [hf, map_one, map_one]),
      map_mul' := fun a b => inj (by rw [hf, map_mul, map_mul, hf, hf]),
      map_zero' := inj (by rw [hf, map_zero, map_zero]),
      map_add' := fun a b => inj (by rw [hf, map_add, map_add, hf, hf]),
      commutes' := fun r => inj (by rw [hf, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]) }
  exact ⟨ψ, fun a => hf a⟩

noncomputable def evGen (C : Type) {R A : Type} [Field C] [CommRing R] [Algebra R C]
    [CommRing A] [Algebra R A] {N : Type} (pt : N → (A →ₐ[R] R)) : C ⊗[R] A →ₐ[C] (N → C) :=
  AlgHom.pi fun x => Algebra.TensorProduct.lift (AlgHom.id C C) ((Algebra.ofId R C).comp (pt x))
    fun _ _ => Commute.all _ _

theorem evGen_tmul (C : Type) {R A : Type} [Field C] [CommRing R] [Algebra R C]
    [CommRing A] [Algebra R A] {N : Type} (pt : N → (A →ₐ[R] R)) (c : C) (a : A) (x : N) :
    evGen C pt (c ⊗ₜ a) x = c * algebraMap R C (pt x a) := by
  simp [evGen, Algebra.ofId_apply]

theorem evGen_bij {C R A : Type} [Field C] [IsAlgClosed C] [CharZero C] [CommRing R] [IsDomain R]
    [Algebra R C] [IsFractionRing R C] [IsIntegrallyClosed R] [CommRing A] [HopfAlgebra R A]
    [Module.Finite R A] {N : Type} [Fintype N] (pt : N → (A →ₐ[R] R)) (hpt : Function.Bijective pt) :
    Function.Bijective (evGen C pt) := by
  classical
  have inj : Function.Injective (algebraMap R C) := IsFractionRing.injective R C
  have key : ∀ χ : C ⊗[R] A →ₐ[C] C, ∃ x, ∀ b, χ b = evGen C pt b x := by
    intro χ
    obtain ⟨ψ, hψ⟩ := exists_pt_of_gen ((χ.restrictScalars R).comp Algebra.TensorProduct.includeRight)
    obtain ⟨x, rfl⟩ := hpt.2 ψ
    refine ⟨x, fun b => ?_⟩
    have h : χ = (Pi.evalAlgHom C (fun _ : N => C) x).comp (evGen C pt) := by
      apply Algebra.TensorProduct.ext (Subsingleton.elim _ _)
      ext a
      show χ (1 ⊗ₜ a) = evGen C pt (1 ⊗ₜ a) x
      rw [evGen_tmul, one_mul]
      exact (hψ a).symm
    rw [h]
    rfl
  constructor
  · rw [injective_iff_map_eq_zero]
    intro b hb
    haveI : IsReduced (C ⊗[R] A) := GlobalTheory.isReduced_of_hopfAlgebra_of_isAlgClosed C _
    haveI : IsArtinianRing (C ⊗[R] A) := IsArtinianRing.of_finite C _
    apply (IsArtinianRing.equivPi (C ⊗[R] A)).injective
    rw [map_zero]
    funext m
    rw [IsArtinianRing.equivPi_apply]
    haveI := m.isMaximal
    letI : Field ((C ⊗[R] A) ⧸ m.asIdeal) := Ideal.Quotient.field _
    have bij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := C) (K := (C ⊗[R] A) ⧸ m.asIdeal)
    let e := AlgEquiv.ofBijective (Algebra.ofId C ((C ⊗[R] A) ⧸ m.asIdeal)) bij
    obtain ⟨x, hx⟩ := key (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C m.asIdeal))
    have h1 := hx b
    rw [hb] at h1
    have h2 : e.symm (Ideal.Quotient.mk m.asIdeal b) = 0 := h1
    have h3 := congrArg e h2
    rw [AlgEquiv.apply_symm_apply, map_zero] at h3
    exact h3
  · by_contra hns
    have hlt : LinearMap.range (evGen C pt).toLinearMap < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      apply hns
      exact LinearMap.range_eq_top.1 h
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
    have hfE : ∀ b, f (evGen C pt b) = 0 := fun b => by
      have h : f (evGen C pt b) ∈ (LinearMap.range (evGen C pt).toLinearMap).map f := ⟨evGen C pt b, ⟨b, rfl⟩, rfl⟩
      rw [hf] at h
      exact (Submodule.mem_bot C).1 h
    let M : N → (C ⊗[R] A →* C) := fun x => ((Pi.evalAlgHom C (fun _ : N => C) x).comp (evGen C pt)).toRingHom.toMonoidHom
    have hM : ∀ x b, M x b = evGen C pt b x := fun _ _ => rfl
    have hMinj : Function.Injective M := by
      intro x y hxy
      apply hpt.1
      ext a
      apply inj
      have h := congrArg (fun g : C ⊗[R] A →* C => g (1 ⊗ₜ a)) hxy
      simp only [hM, evGen_tmul, one_mul] at h
      exact h
    have hli := (linearIndependent_monoidHom (C ⊗[R] A) C).comp M hMinj
    have hsingle : ∀ (x : N) (c : C), (Pi.single x c : N → C) = c • Pi.single x 1 := by
      intro x c
      ext j
      by_cases h : j = x
      · subst h; simp
      · simp [Pi.single_apply, h]
    have hc := Fintype.linearIndependent_iff.1 hli (fun x => f (Pi.single x 1)) (by
      funext b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Function.comp_apply, hM]
      rw [← hfE b]
      conv_rhs => rw [← Finset.univ_sum_single (evGen C pt b)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hsingle x (evGen C pt b x), map_smul, smul_eq_mul, mul_comm])
    apply hf0
    apply LinearMap.pi_ext
    intro x c
    rw [hsingle x c, map_smul, hc x, smul_zero]
    rfl

theorem hopfalg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Free R A], ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ pt : N → (A →ₐ[R] R), Function.Bijective pt → (∀ x y a, pt (x + y) a = Algebra.TensorProduct.lift (pt x) (pt y) (fun _ _ => Commute.all _ _) (Coalgebra.comul (R := R) a)) → (∀ a : A, (∀ x, pt x a = 0) → a = 0) ∧ Fintype.card N = Module.finrank R A ∧ ∃ AA : HopfOrder (C := C) R N, ∀ g, g ∈ AA.carrier ↔ ∃ a : A, g = fun x => algebraMap R C (pt x a) := by
  intro p _ C _ _ _ v R _ _ hv hp A _ _ _ _ _ N _ _ _ pt hbij hadd
  classical
  haveI : IsDomain R := hv.hom_inj.isDomain
  haveI : IsFractionRing R C := hv.isFractionRing
  haveI : ValuationRing R := ValuationRing.of_integers v hv
  have hB := evGen_bij (C := C) pt hbij
  have hinjA : Function.Injective (fun a : A => (1 : C) ⊗ₜ[R] a) := by
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R C) hv.hom_inj
    intro a b hab
    apply (TensorProduct.lid R A).symm.injective
    apply h1
    simpa [TensorProduct.lid_symm_apply] using hab
  have sep : ∀ a : A, (∀ x, pt x a = 0) → a = 0 := by
    intro a ha
    apply hinjA
    apply hB.1
    funext x
    simp only [evGen_tmul, ha x, map_zero, mul_zero, TensorProduct.tmul_zero, Pi.zero_apply]
  have card : Fintype.card N = Module.finrank R A := by
    have h1 := (LinearEquiv.ofBijective (evGen C pt).toLinearMap hB).finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_baseChange] at h1
    exact h1.symm
  have hP : ∀ x y, WithConv.toConv (pt (x + y)) = WithConv.toConv (pt x) * WithConv.toConv (pt y) := by
    intro x y
    apply WithConv.ofConv_injective
    ext a
    rw [hadd, AlgHom.convMul_apply]
  have h0 : WithConv.toConv (pt 0) = (1 : WithConv (A →ₐ[R] R)) := by
    have h := hP 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := WithConv.toConv (pt 0)) (by rw [mul_one, ← h])
  have hS : ∀ x a, pt (-x) a = pt x (HopfAlgebra.antipode R a) := by
    intro x a
    have hn : WithConv.toConv (pt (-x)) = (WithConv.toConv (pt x))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hP, neg_add_cancel, h0]
    have h := congrArg (fun f : WithConv (A →ₐ[R] R) => (WithConv.ofConv f) a) hn
    exact h
  let E : A →ₗ[R] (N → C) := LinearMap.pi (fun x => (Algebra.linearMap R C).comp (pt x).toLinearMap)
  have hE : ∀ a x, E a x = algebraMap R C (pt x a) := fun _ _ => rfl
  refine ⟨sep, card, ⟨{ carrier := LinearMap.range E, lat := ?_, le_int := ?_, one_mem := ?_, mul_mem := ?_, comul := ?_, antipode := ?_ }, ?_⟩⟩
  · have hc : Fintype.card N = Fintype.card (Module.Free.ChooseBasisIndex R A) := by
      rw [card, Module.finrank_eq_card_chooseBasisIndex]
    let b : Module.Basis N R A := (Module.Free.chooseBasis R A).reindex (Fintype.equivOfCardEq hc).symm
    let bc : Module.Basis N C (C ⊗[R] A) := Algebra.TensorProduct.basis C b
    let le := LinearEquiv.ofBijective (evGen C pt).toLinearMap hB
    refine ⟨LinearMap.toMatrix bc (Pi.basisFun C N) le, LinearEquiv.isUnit_det le bc (Pi.basisFun C N), ?_⟩
    have hcol : (fun j x => LinearMap.toMatrix bc (Pi.basisFun C N) le x j) = E ∘ b := by
      funext j x
      rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
      show evGen C pt (bc j) x = _
      rw [Algebra.TensorProduct.basis_apply, evGen_tmul, one_mul]
      rfl
    rw [hcol, Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]
  · rintro g ⟨a, rfl⟩ x
    exact ⟨pt x a, rfl⟩
  · refine ⟨1, ?_⟩
    funext x
    simp [hE]
  · rintro f g ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a * b, ?_⟩
    funext x
    simp [hE]
  · rintro f ⟨a, rfl⟩
    have gen : ∀ t : A ⊗[R] A, (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) t)) ∈ tensorSpan R (LinearMap.range E) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero =>
        have h : (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) (0 : A ⊗[R] A))) = 0 := by
          funext q
          simp
        rw [h]
        exact zero_mem _
      | tmul a b =>
        apply Submodule.subset_span
        refine ⟨E a, ⟨a, rfl⟩, E b, ⟨b, rfl⟩, ?_⟩
        funext q
        simp [hE]
      | add s t hs ht =>
        have h : (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) (s + t))) = (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) s)) + (fun q : N × N => algebraMap R C (Algebra.TensorProduct.lift (pt q.1) (pt q.2) (fun _ _ => Commute.all _ _) t)) := by
          funext q
          simp
        rw [h]
        exact add_mem hs ht
    have h := gen (Coalgebra.comul a)
    convert h using 1
    funext q
    show E a (q.1 + q.2) = _
    rw [hE, hadd]
  · rintro f ⟨a, rfl⟩
    refine ⟨HopfAlgebra.antipode R a, ?_⟩
    funext x
    rw [hE, hE, hS]
  · intro g
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩

end PositivityTheory.HtPt.Rf
