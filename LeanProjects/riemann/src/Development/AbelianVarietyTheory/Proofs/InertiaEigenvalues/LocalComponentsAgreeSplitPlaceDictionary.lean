import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryAutFormEqZeroOfFinitePointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocUniqueOfIsSplitAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfSupportedAtSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.SplitDict
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => maximalRealSubfield L

theorem under_w (s : SplitPlace L) : s.w.under (𝓞 L⁺) = s.v := by
  ext1
  exact s.w_under

theorem exists_basis : ∃ b : Module.Basis (Fin 2) L⁺ L, b 0 = 1 := by
  obtain ⟨e, hne⟩ : ∃ e : L, e ≠ IsCMField.complexConj L e := by
    by_contra hcon
    push Not at hcon
    exact IsCMField.complexConj_ne_one L (AlgEquiv.ext fun x => (hcon x).symm)
  have hli : LinearIndependent L⁺ ![(1 : L), e] := by
    rw [LinearIndependent.pair_iff]
    intro a t h
    have h' := congrArg (IsCMField.complexConj L) h
    simp only [Algebra.smul_def, map_add, map_mul, AlgEquiv.commutes, map_one, map_zero] at h h'
    have hd : algebraMap L⁺ L t * (e - IsCMField.complexConj L e) = 0 := by
      linear_combination h - h'
    have ht : t = 0 := by
      rcases mul_eq_zero.1 hd with h0 | h0
      · simpa using h0
      · exact absurd (sub_eq_zero.1 h0) hne
    subst ht
    simpa using h
  have hcard : Fintype.card (Fin 2) = Module.finrank L⁺ L := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two L⁺ L]; simp
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, by simp⟩

theorem kappa_eq_zero (F : FinIso L n) (u : HeightOneSpectrum (𝓞 L)) (z : AL L)
    (hz : compAt L (u.under (𝓞 L⁺)) z = 0) : F.κ z u = 0 := by
  obtain ⟨i', -, hi'⟩ := F.right u (u.under (𝓞 L⁺)) rfl
  obtain ⟨b, hb0⟩ := exists_basis (L := L)
  obtain ⟨A, B, hAB⟩ := GlobalTheory.tensor_exists_decomp b z
  rw [hb0] at hAB
  have hAB0 : A (u.under (𝓞 L⁺)) = 0 ∧ B (u.under (𝓞 L⁺)) = 0 := by
    rw [hAB] at hz
    apply GlobalTheory.tensor_decomp_eq_zero b
    rw [hb0]
    simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul] at hz
    exact hz
  have h2 : b 1 ⊗ₜ[L⁺] B = (b 1 ⊗ₜ[L⁺] (1 : AFplus L)) * ((1 : L) ⊗ₜ[L⁺] B) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hAB, h2, map_add, map_mul]
  change F.κ (1 ⊗ₜ A) u + F.κ (b 1 ⊗ₜ 1) u * F.κ (1 ⊗ₜ B) u = 0
  rw [hi', hi', hAB0.1, hAB0.2, map_zero, mul_zero, add_zero]

theorem j_mem_locU (F : FinIso L n) (s : SplitPlace L) (y : GAf L n) (hy : TrivOutside {s.v} y) :
    F.j y ∈ locU n s.w := by
  refine Subgroup.mem_inf.2 ⟨F.fin y, ?_⟩
  rw [Subgroup.mem_iInf]
  intro u
  rw [Subgroup.mem_iInf]
  intro hu
  rw [MonoidHom.mem_ker]
  rw [under_w] at hu
  refine Units.ext (Matrix.ext fun a c => ?_)
  rw [F.loc]
  have h1 := congrFun (congrFun (hy (u.under (𝓞 L⁺)) hu) a) c
  simp only [Matrix.map_apply] at h1
  have h2 : compAt L (u.under (𝓞 L⁺)) (((y : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) a c -
      (1 : Matrix (Fin n) (Fin n) (AL L)) a c) = 0 := by
    rw [map_sub, h1]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have h3 := kappa_eq_zero F u _ h2
  rw [map_sub] at h3
  change F.κ _ u - F.κ _ u = 0 at h3
  rw [sub_eq_zero] at h3
  rw [h3]
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp
end GlobalTheory.SplitDict

namespace GlobalTheory.SplitDict
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => maximalRealSubfield L

theorem kappa_split (F : FinIso L n) (s : SplitPlace L) (i : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L)
    (hic : Continuous i) (hi : ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) (z : AL L) :
    F.κ z s.w = i (s.proj z) := by
  obtain ⟨i', hic', hi'⟩ := F.right s.w s.v s.w_under
  have hL : ∀ k : L⁺, i' (algebraMap L⁺ (s.v.adicCompletion L⁺) k) =
      algebraMap L (s.w.adicCompletion L) (algebraMap L⁺ L k) := fun k => by
    have h1 := hi' (algebraMap L⁺ (AFplus L) k)
    have h2 : (1 : L) ⊗ₜ[L⁺] algebraMap L⁺ (AFplus L) k = algebraMap L⁺ L k ⊗ₜ[L⁺] (1 : AFplus L) := by
      rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]
    rw [h2, F.left] at h1
    exact h1.symm
  have hR : ∀ k : L⁺, i (algebraMap L⁺ (s.v.adicCompletion L⁺) k) =
      algebraMap L (s.w.adicCompletion L) (algebraMap L⁺ L k) := fun k => by
    rw [← hi, AlgHom.commutes]
  have heq : ∀ a : s.v.adicCompletion L⁺, i' a = i a := fun a =>
    (HeightOneSpectrum.denseRange_algebraMap L⁺ s.v).induction_on (p := fun a => i' a = i a) a
      (isClosed_eq hic' hic) fun k => by rw [hL, hR]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    change F.κ x s.w + F.κ y s.w = _
    rw [hx, hy]
  | tmul l a =>
    have h2 : l ⊗ₜ[L⁺] a = (l ⊗ₜ[L⁺] (1 : AFplus L)) * ((1 : L) ⊗ₜ[L⁺] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [GlobalTheory.SplitLift.proj_tmul, map_mul, hi, h2, map_mul]
    change F.κ (l ⊗ₜ 1) s.w * F.κ (1 ⊗ₜ a) s.w = _
    rw [hi', heq, F.left]
    rfl

theorem cLoc_j (F : FinIso L n) (s : SplitPlace L) (i : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L)
    (hic : Continuous i) (hi : ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) (y : GAf L n) :
    cLoc s.w (F.j y) = Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n y) := by
  refine Units.ext (Matrix.ext fun a c => ?_)
  rw [F.loc, kappa_split F s i hic hi]
  rfl

theorem isSplitAt_w (F : FinIso L n) (s : SplitPlace L) (i : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L)
    (hic : Continuous i) (hi : ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) : IsSplitAt s.w := by
  by_contra hns
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  set δ : L := y - IsCMField.complexConj L y with hδdef
  have hδ : IsCMField.complexConj L δ = -δ := by
    rw [hδdef, map_sub, IsCMField.complexConj_apply_apply]; ring
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hfix : IsCMField.complexConj L (δ * δ) = δ * δ := by rw [map_mul, hδ]; ring
  let d : L⁺ := ⟨δ * δ, (IsCMField.complexConj_eq_self_iff L _).1 hfix⟩
  have hd : δ * δ = algebraMap L⁺ L d := rfl
  have hr : s.i δ ≠ 0 := (map_ne_zero _).2 hδ0
  have hk : F.κ (GlobalTheory.SplitLift.Em s δ) = 0 := by
    ext1 u
    change F.κ (GlobalTheory.SplitLift.Em s δ) u = 0
    by_cases hu : u = s.w
    · subst hu
      rw [kappa_split F s i hic hi, GlobalTheory.SplitLift.proj_Em s δ d hd hr, map_zero]
    · apply kappa_eq_zero
      apply GlobalTheory.SplitLift.compAt_Em
      rw [← under_w s]
      exact fun h => hns ⟨u, hu, h⟩
  have h0 : GlobalTheory.SplitLift.Em s δ = 0 := F.κ.injective (hk.trans (map_zero _).symm)
  have h1 := GlobalTheory.SplitLift.proj_Ep s δ d hd hr
  rw [← GlobalTheory.SplitLift.conj_Em s δ hδ, h0, map_zero, map_zero] at h1
  exact zero_ne_one h1
end GlobalTheory.SplitDict

namespace GlobalTheory.SplitDict

theorem locComp_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n)
    (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (s : SplitPlace L) (σ : SmIrr (GL (Fin n) (s.w.adicCompletion L))),
    IsCompAlong U (locU n s.w) ((cLoc s.w).comp (locU n s.w).subtype) σ.ρ →
    ∃ τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS π.S s τ ∧ Nonempty (τ.ρ.Equiv σ.ρ) := by
  intro L _ _ _ n F π U hD s σ hσ
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class L n π s
  refine ⟨τ, hτ, ?_⟩
  obtain ⟨i, T, hic, hi, hTinj, hTS, hTeq⟩ := hτ
  have hsplit : IsSplitAt s.w := isSplitAt_w F s i hic hi
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL L n s.w hsplit
  obtain ⟨sec, hsecT, hsecL⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc L n s
  have hlift : ∀ x : locU n s.w, ∃ y, TrivOutside {s.v} y ∧ F.j y = x := by
    intro x
    refine ⟨sec (Matrix.GeneralLinearGroup.map i.symm.toRingHom (cLoc s.w (x : UA L n))), hsecT _, ?_⟩
    have hm := j_mem_locU F s _ (hsecT (Matrix.GeneralLinearGroup.map i.symm.toRingHom (cLoc s.w (x : UA L n))))
    have h1 : e ⟨_, hm⟩ = e x := by
      rw [he, he, cLoc_j F s i hic hi, hsecL]
      refine Units.ext (Matrix.ext fun a c => ?_)
      simp
    exact congrArg Subtype.val (e.injective h1)
  let R : U →ₗ[ℂ] (GAf L n → ℂ) := (LinearMap.funLeft ℂ ℂ F.j).comp U.subtype
  have hRinj : Function.Injective R := by
    refine (injective_iff_map_eq_zero R).2 fun φ hφ => ?_
    have h0 : ∀ y ∈ finU L n, (φ : UA L n → ℂ) y = 0 := fun y hy => by
      obtain ⟨x, rfl⟩ := F.onto y hy
      exact congrFun hφ x
    exact Subtype.ext (GlobalTheory.T.definiteUnitaryAutForm_eq_zero_of_finitePoints L n φ (hD.1.aut φ φ.2) h0)
  have hRrange : LinearMap.range R = U.map (LinearMap.funLeft ℂ ℂ F.j) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  obtain ⟨hnt, -⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 τ.irr
  obtain ⟨a0, ha0⟩ := exists_ne (0 : τ.V)
  have hTa0 : T a0 ≠ 0 := fun h => ha0 (hTinj (h.trans (map_zero T).symm))
  obtain ⟨g0, hg0⟩ : ∃ g0, T a0 g0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hTa0 (funext hc)
  obtain ⟨lam, hlam⟩ : ∃ lam : Module.Dual ℂ π.W, lam (T a0 g0) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hg0 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  let T' : τ.V →ₗ[ℂ] (GAf L n → ℂ) := (LinearMap.compLeft lam (GAf L n)).comp T
  have hT'mem : ∀ a, T' a ∈ LinearMap.range R := fun a => by
    rw [hRrange, hD.2]
    exact Submodule.subset_span ⟨T a, hTS a, lam, rfl⟩
  let eR := LinearEquiv.ofInjective R hRinj
  let f : τ.V →ₗ[ℂ] (UA L n → ℂ) := U.subtype ∘ₗ eR.symm.toLinearMap ∘ₗ T'.codRestrict _ hT'mem
  have hfU : ∀ a, f a ∈ U := fun a => (eR.symm _).2
  have hf : ∀ a y, f a (F.j y) = lam (T a y) := fun a y => by
    have h1 := congrArg Subtype.val (eR.apply_symm_apply ⟨T' a, hT'mem a⟩)
    exact congrFun h1 y
  have hcomp : IsCompAlong U (locU n s.w) ((cLoc s.w).comp (locU n s.w).subtype) τ.ρ := by
    refine ⟨τ.irr, f, fun h => hlam ?_, hfU, fun x a => ?_⟩
    · have h1 := hf a0 g0
      rw [h] at h1
      exact h1.symm
    · obtain ⟨y, hyT, hyx⟩ := hlift x
      have hm2 : RU L n (x : UA L n) (f a) ∈ U := hD.1.stable _ _ (hfU a)
      have h1 : R ⟨_, hfU (τ.ρ (((cLoc s.w).comp (locU n s.w).subtype) x) a)⟩ = R ⟨_, hm2⟩ := by
        funext g
        change f _ (F.j g) = f a (F.j g * x)
        rw [hf, ← hyx, ← map_mul, hf]
        have h2 := hTeq y hyT a
        rw [← cLoc_j F s i hic hi, hyx] at h2
        change lam (T (τ.ρ (cLoc s.w (x : UA L n)) a) g) = _
        rw [h2]
        rfl
      exact congrArg Subtype.val (hRinj h1)
  let P : GlobalTheory.DefU.AutSub L n := ⟨U, hD.1⟩
  let τ' : SmIrr (GL (Fin n) (s.w.adicCompletion L)) := ⟨τ.V, τ.ρ, τ.smooth, τ.irr⟩
  have h1 : (GlobalTheory.DefU.AU.mk P).IsLoc s.w (Quotient.mk _ τ') := hcomp
  have h2 : (GlobalTheory.DefU.AU.mk P).IsLoc s.w (Quotient.mk _ σ) := hσ
  have h3 := GlobalTheory.DefU.AU.isLoc_unique_of_isSplitAt L n _ s.w _ _ hsplit h1 h2
  obtain ⟨φ⟩ := Quotient.exact h3
  exact ⟨φ⟩

end GlobalTheory.SplitDict
