import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.PolyBij
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {n d : ℕ}

theorem cone_empty_nonneg {g : Gam n d} (hg : g ∈ (cone ∅ : AddSubmonoid (Gam n d))) (e : E n d) : 0 ≤ g e := by
  have hg' : (∀ l : Fin n, 0 ≤ g (Sum.inl l)) ∧ (∀ j ∉ (∅ : Finset (Fin d)), 0 ≤ g (Sum.inr j)) ∧
      0 ≤ tdeg g := hg
  rcases e with l | j
  · exact hg'.1 l
  · exact hg'.2.1 j (Finset.notMem_empty j)

theorem coe_mem_cone (f : E n d →₀ ℕ) :
    (fun e => (f e : ℤ) : Gam n d) ∈ (cone ∅ : AddSubmonoid (Gam n d)) := by
  show (∀ l : Fin n, (0 : ℤ) ≤ (f (Sum.inl l) : ℤ)) ∧
    (∀ j ∉ (∅ : Finset (Fin d)), (0 : ℤ) ≤ (f (Sum.inr j) : ℤ)) ∧ 0 ≤ tdeg (fun e => (f e : ℤ) : Gam n d)
  refine ⟨fun l => Int.natCast_nonneg _, fun j _ => Int.natCast_nonneg _, ?_⟩
  exact Finset.sum_nonneg fun j _ => Int.natCast_nonneg _

def expEquiv : (E n d →₀ ℕ) ≃+ (cone ∅ : AddSubmonoid (Gam n d)) where
  toFun f := ⟨fun e => (f e : ℤ), coe_mem_cone f⟩
  invFun g := Finsupp.equivFunOnFinite.symm fun e => (g.1 e).toNat
  left_inv f := by
    ext e
    simp
  right_inv g := by
    refine Subtype.ext (funext fun e => ?_)
    simpa using cone_empty_nonneg g.2 e
  map_add' f f' := by
    refine Subtype.ext (funext fun e => ?_)
    simp

def polyEquiv (K : Type) [Field K] : Bp K n d ≃ₐ[K] R0 K n d (∅ : Finset (Fin d)) :=
  AddMonoidAlgebra.domCongr K K expEquiv

theorem expEquiv_single (e : E n d) :
    (expEquiv (Finsupp.single e 1) : (cone ∅ : AddSubmonoid (Gam n d))) = ⟨oneE e, oneE_mem ∅ e⟩ := by
  refine Subtype.ext (funext fun e' => ?_)
  change ((Finsupp.single e 1 : E n d →₀ ℕ) e' : ℤ) = (Pi.single e (1 : ℤ) : E n d → ℤ) e'
  by_cases h : e' = e
  · subst h
    simp
  · simp [Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]

theorem poly_eq_polyEquiv (K : Type) [Field K] :
    poly n K (∅ : Finset (Fin d)) = (polyEquiv K).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro e
  rw [poly_X, polyEquiv,
    MvPolynomial.X, ← MvPolynomial.single_eq_monomial]
  erw [AddMonoidAlgebra.domCongr_single, expEquiv_single]
  rfl

theorem poly_bijective {K : Type} [Field K] {n d : ℕ} :
    Function.Bijective (poly n K (∅ : Finset (Fin d))) := by
  rw [poly_eq_polyEquiv]
  exact (polyEquiv K).bijective

end GlobalTheory.CompanionTheory.SurjectionOntoH4.PolyBij
