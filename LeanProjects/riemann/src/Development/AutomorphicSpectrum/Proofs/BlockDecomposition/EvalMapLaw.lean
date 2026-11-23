import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.Frob

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

def evalMap {π : Representation ℂ (GL (Fin (a + b)) k) V} {σ : Representation ℂ (GL (Fin a) k) W}
    {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ)) :
    V →ₗ[ℂ] TensorProduct ℂ W W' :=
  φ.toLinearMap ∘ₗ (twKer π (unipRad k (two (stdSum (rfl : a + b = a + b)))) 1).mkQ

theorem evalMap_law {π : Representation ℂ (GL (Fin (a + b)) k) V}
    {σ : Representation ℂ (GL (Fin a) k) W} {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ))
    (q : parab k (two (stdSum (rfl : a + b = a + b)))) (w : V) :
    evalMap φ (π q w) =
      (deltaHalf k (Two (Fin a) (Fin b)) (leviProj k _ q) : ℂ) •
        extTensor σ ρ ((leviTwo k (Fin a) (Fin b)).symm (leviProj k _ q)) (evalMap φ w) := by
  set xy := (leviTwo k (Fin a) (Fin b)).symm (leviProj k _ q) with hxy
  have hL : leviProj k (two (stdSum (rfl : a + b = a + b))) q = leviTwo k _ _ xy :=
    (MulEquiv.apply_symm_apply _ _).symm
  obtain ⟨u, hu, hpu⟩ := exists_levi_mul_unip k (two (stdSum (rfl : a + b = a + b))) q
  rw [hL] at hpu ⊢
  have hpu' : (q : GL (Fin (a + b)) k) =
      leviEmb k (two (stdSum (rfl : a + b = a + b))) (leviTwo k _ _ xy) * u := hpu
  have hmk : (Submodule.Quotient.mk (π u w) :
      Jacquet π (unipRad k (two (stdSum (rfl : a + b = a + b))))) = Submodule.Quotient.mk w := by
    rw [Submodule.Quotient.eq]
    refine Submodule.subset_span ⟨⟨u, hu⟩, w, ?_⟩
    simp
  have key : ∀ (M : Levi k (Two (Fin a) (Fin b))) (x : V),
      (Submodule.Quotient.mk (π (leviEmb k (two (stdSum (rfl : a + b = a + b))) M) x) :
        Jacquet π (unipRad k (two (stdSum (rfl : a + b = a + b))))) =
        (deltaHalf k (Two (Fin a) (Fin b)) M : ℂ) •
          jac (two (stdSum (rfl : a + b = a + b))) π M (Submodule.Quotient.mk x) := by
    intro M x
    rw [jac_mk, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  have hint := Representation.IntertwiningMap.isIntertwining _ _ φ xy
    (Submodule.Quotient.mk w : Jacquet π (unipRad k (two (stdSum (rfl : a + b = a + b)))))
  simp only [evalMap, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
  rw [hpu', map_mul, Module.End.mul_apply, key, hmk, map_smul]
  change _ • φ (jac₂ (stdSum (rfl : a + b = a + b)) π xy (Submodule.Quotient.mk w)) = _
  rw [hint]
  rfl

def frobMap {π : Representation ℂ (GL (Fin (a + b)) k) V} (hs : IsSmooth π)
    {σ : Representation ℂ (GL (Fin a) k) W} {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ)) :
    π.IntertwiningMap (prod₂ σ ρ) :=
  { toFun := fun v => ⟨⟨fun x => evalMap φ (π x v), fun q x => by
        show evalMap φ (π (q * x) v) = _
        rw [map_mul, Module.End.mul_apply]
        exact evalMap_law φ q (π x v)⟩,
      mem_smoothPart_of_nhds (Filter.mem_of_superset ((hs v).mem_nhds (by simp)) fun h hh => by
        have hh' : π h v = v := hh
        refine Subtype.ext (funext fun x => ?_)
        show evalMap φ (π (x * h) v) = evalMap φ (π x v)
        rw [map_mul, Module.End.mul_apply, hh'])⟩
    map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by
      show evalMap φ (π x (v + w)) = evalMap φ (π x v) + evalMap φ (π x w)
      rw [map_add, map_add]))
    map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by
      show evalMap φ (π x (c • v)) = c • evalMap φ (π x v)
      rw [map_smul, map_smul]))
    isIntertwining' := fun h => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
      show evalMap φ (π x (π h v)) = evalMap φ (π (x * h) v)
      rw [map_mul, Module.End.mul_apply])) }

theorem frobMap_one {π : Representation ℂ (GL (Fin (a + b)) k) V} (hs : IsSmooth π)
    {σ : Representation ℂ (GL (Fin a) k) W} {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ)) (v : V) :
    (frobMap hs φ v).1.1 1 = φ (Submodule.Quotient.mk v) := by
  show evalMap φ (π 1 v) = _
  rw [map_one]
  rfl

theorem exists_injective_of_jac₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (V W W' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (π : Representation ℂ (GL (Fin (a + b)) k) V) (σ : Representation ℂ (GL (Fin a) k) W)
    (ρ : Representation ℂ (GL (Fin b) k) W'), IsSmooth π → π.IsIrreducible →
    ∀ φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ), φ ≠ 0 →
      ∃ ψ : π.IntertwiningMap (prod₂ σ ρ), Function.Injective ψ := by
  intro k _ _ _ _ a b V W W' _ _ _ _ _ _ π σ ρ hs hπ φ hφ
  refine ⟨frobMap hs φ, ?_⟩
  haveI := hπ
  refine (Representation.IsIrreducible.injective_or_eq_zero (frobMap hs φ)).resolve_right fun h0 => hφ ?_
  ext v
  show φ (Submodule.Quotient.mk v) = 0
  rw [← frobMap_one hs φ v, h0]
  rfl

end GlobalTheory.CompanionTheory.Frob
