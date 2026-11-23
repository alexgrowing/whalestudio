import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AbsInvOf

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison TensorProduct

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

def CIn (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (r : Res l K) (f : ℕ) : Prop :=
  ∃ (Amp : ∀ M : Model l K, E.LineData M.X → Prop) (N : ℕ) (F : Pb.Fac r N), (per l K).Facts ∧ EtSide (l := l) (K := K) Model.Sm ∧
    (dat Amp).Laws Model.Sm ∧ Nonempty (BMap Model.Sm (dat Amp)) ∧ Nonempty (PMap Model.Sm (dat Amp)) ∧ f ∣ N ∧ Pb.Mid.TeichmullerCongruence r N ∧
    ∀ M : Model l K, M.Sm → ∀ j, Pin F M j ∧ BIn M j

def Final : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
  [IsDomain (OK l K)] [IsDiscreteValuationRing (OK l K)] (r : Res l K) (f : ℕ), 0 < f → (∀ x : r.k, x ^ l ^ f = x) → CIn l K r f →
  ∀ (ϖ : OK l K), Irreducible ϖ → ∀ (M : Model l K), M.Sm → ∀ (n j : ℕ) (T : Fin (n + 1) → Corr l M.X)
    (hr : ∀ i, (T i).r ≫ M.p = (T i).p ≫ M.p), PtId l (l ^ f) n (fn M.p ϖ) T →
  ∀ A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j), (∀ i, IsHk M (T i) (hr i) j (A i)) → ∀ B₀ : PB l K, ∃ N : ℕ, ∀ x, IsInv B₀ M j x →
    ∑ i : Fin (n + 1), ((-1) ^ (i : ℕ) * ((l ^ f : ℕ) : ℤ) ^ ((i : ℕ).choose 2)) •
      TensorProduct.map (A i) (B₀.φ.toLinearMap ^ (f * (n - i + N))) x = 0

end UpperTheory.Ru.crystallineComparison
