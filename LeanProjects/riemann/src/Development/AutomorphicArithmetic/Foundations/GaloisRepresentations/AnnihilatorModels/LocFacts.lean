import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.AdmissibleOfCrystalline
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.HkOfPush
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6

noncomputable section

open CategoryTheory AlgebraicGeometry Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Module CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

namespace UpperTheory.Gal.crystallineComparison.Br

def LocFacts : Prop := ∀ (A : Type) [CommRing A] (a t : A), (∃ r : ℕ, a ∣ t ^ r) →
  (∀ x : Formalism.Per6.Loc2 a t, ∃ (r : ℕ) (y : A), Formalism.Per6.Loc2.mk₀ a t t ^ r * x = Formalism.Per6.Loc2.mk₀ a t y) ∧
    ∀ y : A, Formalism.Per6.Loc2.mk₀ a t y = 0 → ∃ r : ℕ, t ^ r * y = 0

def ActEq : Prop := ∀ (l : ℕ) [Fact l.Prime], (∀ (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (g : K.fixingSubgroup) (x : Acris l),
    galA g x = GroundTheory.PAdicHodge.ACris.galCris (Formalism.Per6.toBot g.1) x) ∧ ∀ z : ℤ_[l], Formalism.Per6.zB l z = Formalism.Per6.cB l (zA l z)

def PBTied : Prop := ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ K : FinExt l,
  ∃ (B : PB l K.1) (e : P.R.B ≃ₐ[ℚ_[l]] B.C), (∀ (g : ↥(GK K)) b, e (P.actQ (g : GQ l) b) = B.σ g (e b)) ∧ (∀ b, e (P.φB b) = B.φ (e b)) ∧
    Function.Injective B.φ

def AnnDrop : Prop := ∀ (F G B C : Type) [Field F] [Group G] [CommRing B] [Algebra F B] [CommRing C] [Algebra F C] (σ : G → End F B)
  (φ : B →ₐ[F] B) (s : G → (C →ₐ[F] C)) (ψ : C →ₐ[F] C) (e : B ≃ₐ[F] C), (∀ g b, e (σ g b) = s g (e b)) → (∀ b, e (φ b) = ψ (e b)) →
  Function.Injective ψ → ∀ (V : Type 1) [AddCommGroup V] [Module F V] (V₀ : Type) [AddCommGroup V₀] [Module F V₀] (i : V ≃ₗ[F] V₀)
    (act : G → End F V) (ρ : Representation F G V₀), (∀ g v, ρ g (i v) = i (act g v)) → ∀ (f q n N : ℕ) (A : Fin (n + 1) → End F V)
    (T : ℕ → End F V₀), (∀ (j : Fin (n + 1)) v, T j (i v) = i (A j v)) →
    (∀ x : V ⊗[F] C, (∀ g, TensorProduct.map (act g) (s g).toLinearMap x = x) →
      ∑ j : Fin (n + 1), ((-1) ^ (j : ℕ) * (q : ℤ) ^ ((j : ℕ).choose 2)) • TensorProduct.map (A j) (ψ.toLinearMap ^ (f * (n - j + N))) x = 0) →
    AnnD σ (φ.toLinearMap ^ f) q n ρ T

def FinAll : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
  [IsDomain (OK l K)] [IsDiscreteValuationRing (OK l K)] (f : ℕ), 0 < f → Nat.card (IsLocalRing.ResidueField (OK l K)) = l ^ f →
  ∀ (ϖ : OK l K), Irreducible ϖ → ∀ (M : Model l K), M.Sm → ∀ (n j : ℕ) (T : Fin (n + 1) → Corr l M.X)
    (hr : ∀ i, (T i).r ≫ M.p = (T i).p ≫ M.p), PtId l (l ^ f) n (fn M.p ϖ) T →
  ∀ A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j), (∀ i, IsHk M (T i) (hr i) j (A i)) → ∀ B₀ : PB l K, ∃ N : ℕ, ∀ x, IsInv B₀ M j x →
    ∑ i : Fin (n + 1), ((-1) ^ (i : ℕ) * ((l ^ f : ℕ) : ℤ) ^ ((i : ℕ).choose 2)) •
      TensorProduct.map (A i) (B₀.φ.toLinearMap ^ (f * (n - i + N))) x = 0

def AnnModel : Prop := FinAll → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (K : FinExt l)
  [IsDomain (OK l K.1)] [IsDiscreteValuationRing (OK l K.1)] (f : ℕ), 0 < f → Nat.card (IsLocalRing.ResidueField (OK l K.1)) = l ^ f →
  ∀ (ϖ : OK l K.1), Irreducible ϖ → ∀ (M : Model l K.1), M.Sm → ∀ (n j : ℕ) (T : Fin (n + 1) → Corr l M.X)
    (hr : ∀ i, (T i).r ≫ M.p = (T i).p ≫ M.p), PtId l (l ^ f) n (fn M.p ϖ) T →
  ∀ A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j), (∀ i, IsHk M (T i) (hr i) j (A i)) →
  ∀ (V₀ : Type) [AddCommGroup V₀] [Module ℚ_[l] V₀] (i : M.V j ≃ₗ[ℚ_[l]] V₀) (ρ : Representation ℚ_[l] ↥(GK K) V₀),
    (∀ g v, ρ g (i v) = i (M.act j g v)) → ∀ T₀ : ℕ → End ℚ_[l] V₀, (∀ (a : Fin (n + 1)) v, T₀ a (i v) = i (A a v)) →
    AnnD (σCr P K) (ψCr P f) (l ^ f) n ρ T₀

end UpperTheory.Gal.crystallineComparison.Br
