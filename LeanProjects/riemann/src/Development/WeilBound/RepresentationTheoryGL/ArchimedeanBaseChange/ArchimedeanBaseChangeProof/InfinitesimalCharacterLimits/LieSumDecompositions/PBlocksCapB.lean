import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksAlg
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDeterminantPolynomialCoefficients

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem rel_expand (G : Sm E (r + s)) (hu : ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), G.1 (unip x * g) = G.1 g)
    (τ : E →+* ℂ) (c : ℂ → ℂ) (hcap : ∀ u, cap τ u G = c u • G) {k : ℕ} (b : Fin k → Sm E r) (q : Fin k → Sm E s)
    (hG : ∀ p, G.1 (lev (Ad E) r s p) = ∑ i, (b i).1 p.1 * (q i).1 p.2) (u : ℂ) (p : GA E r × GA E s) :
    ∑ i, (cap τ (u - (s : ℂ) / 2) (b i)).1 p.1 * (cap τ (u + (r : ℂ) / 2) (q i)).1 p.2 =
      c u * ∑ i, (b i).1 p.1 * (q i).1 p.2 := by
  have h1 := CapFactor.cap_levi E r s τ u G hu p
  rw [hcap] at h1
  have hH : ∀ p', (capR r s τ (u - (s : ℂ) / 2) G).1 (lev (Ad E) r s p') =
      ∑ i, (cap τ (u - (s : ℂ) / 2) (b i)).1 p'.1 * (q i).1 p'.2 :=
    fun p' => capR_expand (n := ![r, s]) τ _ G b q hG p'
  have h2 := capS_expand (n := ![r, s]) τ (u + (r : ℂ) / 2) (capR r s τ (u - (s : ℂ) / 2) G)
    (fun i => cap τ (u - (s : ℂ) / 2) (b i)) q hH p
  rw [← hG p]
  change c u * G.1 _ = _ at h1
  rw [h1]
  exact h2.symm

theorem tensL_apply (N : ℕ) (f : ℕ → Module.End ℂ (Sm E r)) (u : ℂ) {k : ℕ} (b : Fin k → Sm E r) (q : Fin k → Sm E s) :
    (∑ j ∈ Finset.range N, u ^ j • tensOp (f j) LinearMap.id) (fun p : GA E r × GA E s => ∑ i, (b i).1 p.1 * (q i).1 p.2) =
      fun p => ∑ i, ((∑ j ∈ Finset.range N, u ^ j • f j) (b i)).1 p.1 * (q i).1 p.2 := by
  funext p
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, tensOp_sum, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, LinearMap.id_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem tensR_apply (N : ℕ) (f : ℕ → Module.End ℂ (Sm E s)) (u : ℂ) {k : ℕ} (b : Fin k → Sm E r) (q : Fin k → Sm E s) :
    (∑ j ∈ Finset.range N, u ^ j • tensOp LinearMap.id (f j)) (fun p : GA E r × GA E s => ∑ i, (b i).1 p.1 * (q i).1 p.2) =
      fun p => ∑ i, (b i).1 p.1 * ((∑ j ∈ Finset.range N, u ^ j • f j) (q i)).1 p.2 := by
  funext p
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, tensOp_sum, Pi.smul_apply, smul_eq_mul,
    Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, LinearMap.id_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem fd_tens2 (Z₁ : Submodule ℂ (Sm E r)) (Z₂ : Submodule ℂ (Sm E s)) [FiniteDimensional ℂ Z₁]
    [FiniteDimensional ℂ Z₂] : FiniteDimensional ℂ (tens2 Z₁ Z₂) := by
  classical
  let B₁ := Module.finBasis ℂ Z₁
  let B₂ := Module.finBasis ℂ Z₂
  let f : Fin (Module.finrank ℂ Z₁) × Fin (Module.finrank ℂ Z₂) → (GA E r × GA E s → ℂ) :=
    fun ij m => (B₁ ij.1).1.1 m.1 * (B₂ ij.2).1.1 m.2
  have hle : tens2 Z₁ Z₂ ≤ Submodule.span ℂ (Set.range f) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    have e₁ := B₁.sum_repr ⟨φ₁, h₁⟩
    have e₂ := B₂.sum_repr ⟨φ₂, h₂⟩
    have e : (fun m : GA E r × GA E s => φ₁.1 m.1 * φ₂.1 m.2) =
        ∑ ij : Fin (Module.finrank ℂ Z₁) × Fin (Module.finrank ℂ Z₂), (B₁.repr ⟨φ₁, h₁⟩ ij.1 * B₂.repr ⟨φ₂, h₂⟩ ij.2) • f ij := by
      funext m
      have a₁ := congrArg (fun x : Z₁ => x.1.1 m.1) e₁
      have a₂ := congrArg (fun x : Z₂ => x.1.1 m.2) e₂
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at a₁ a₂
      change φ₁.1 m.1 * φ₂.1 m.2 = _
      rw [← a₁, ← a₂, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact Submodule.sum_mem _ fun ij _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij, rfl⟩)
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) := FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  exact Submodule.finiteDimensional_of_le hle

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

end
