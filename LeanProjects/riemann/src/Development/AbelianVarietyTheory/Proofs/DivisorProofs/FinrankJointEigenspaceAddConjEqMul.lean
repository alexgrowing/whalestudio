import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEigSp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRingOfIntegersActionSumEmbeddingsEigenspaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRingOfIntegersActionLatticeEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section

namespace GlobalTheory.UPel.HT.LieType.DimSum

theorem finrank_eq_two_mul_of_period {La : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] {g : ℕ}
    (Q : La →+ (Fin g → ℂ)) (hinj : Function.Injective Q) (hdisc : DiscreteTopology Q.range)
    (hspan : Submodule.span ℝ (Set.range Q) = ⊤) : Module.finrank ℤ La = 2 * g := by
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Q.range
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨by
    have : (L : Set (Fin g → ℂ)) = Set.range Q := by ext x; simp [L]
    rw [this]; exact hspan⟩
  have h1 := ZLattice.rank ℝ L
  have e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective Q.toIntLinearMap hinj |>.trans
    (LinearEquiv.ofEq _ _ (by ext x; simp [L]))
  rw [e.finrank_eq, h1, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, Finset.sum_const, mul_comm]

theorem trace_real_restrict (g : ℕ) (M : Matrix (Fin g) (Fin g) ℂ) :
    LinearMap.trace ℝ (Fin g → ℂ) ((Matrix.toLin' M).restrictScalars ℝ) = 2 * M.trace.re := by
  classical
  let b := Pi.basisFun ℂ (Fin g)
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower b)]
  have : M.trace = LinearMap.trace ℂ _ (Matrix.toLin' M) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b]; simp [b]
  rw [this, LinearMap.trace_eq_matrix_trace ℂ b]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_prod_type, Finset.mul_sum, two_mul,
    Finset.sum_add_distrib]

theorem trace_int_eq_of_period {La : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] {g : ℕ}
    (Q : La →+ (Fin g → ℂ)) (M : Matrix (Fin g) (Fin g) ℂ) (A : La →+ La) (hinj : Function.Injective Q)
    (hdisc : DiscreteTopology Q.range) (hspan : Submodule.span ℝ (Set.range Q) = ⊤)
    (hA : ∀ x, Q (A x) = M *ᵥ Q x) :
    ((LinearMap.trace ℤ La A.toIntLinearMap : ℤ) : ℂ) = M.trace + (starRingEnd ℂ) M.trace := by
  classical
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Q.range
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨by
    have : (L : Set (Fin g → ℂ)) = Set.range Q := by ext x; simp [L]
    rw [this]; exact hspan⟩
  let e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective Q.toIntLinearMap hinj |>.trans
    (LinearEquiv.ofEq _ _ (by ext x; simp [L]))
  have he : ∀ x, ((e x : L) : Fin g → ℂ) = Q x := fun x => rfl
  let b := Module.Free.chooseBasis ℤ La
  let bL := b.map e
  let bR := bL.ofZLatticeBasis ℝ L
  have hbR : ∀ i, bR i = Q (b i) := by
    intro i; simp [bR, bL, Module.Basis.ofZLatticeBasis_apply, he]
  have hmat : LinearMap.toMatrix bR bR ((Matrix.toLin' M).restrictScalars ℝ) =
      (LinearMap.toMatrix b b A.toIntLinearMap).map (Int.cast : ℤ → ℝ) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have h1 : (Matrix.toLin' M).restrictScalars ℝ (bR j) = Q (A (b j)) := by
      rw [hbR, hA]; rfl
    rw [h1]
    have h2 : Q (A (b j)) = ∑ k, (b.repr (A (b j)) k : ℝ) • bR k := by
      conv_lhs => rw [← b.sum_repr (A (b j))]
      simp only [map_sum, map_zsmul, hbR]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℝ]
    rw [h2, bR.repr_sum_self]
    rfl
  have htr : (LinearMap.trace ℝ _ ((Matrix.toLin' M).restrictScalars ℝ)) =
      ((LinearMap.trace ℤ La A.toIntLinearMap : ℤ) : ℝ) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ bR, hmat, LinearMap.trace_eq_matrix_trace ℤ b]
    simp [Matrix.trace]
  rw [trace_real_restrict] at htr
  have : ((LinearMap.trace ℤ La A.toIntLinearMap : ℤ) : ℂ) = (((LinearMap.trace ℤ La A.toIntLinearMap : ℤ) : ℝ) : ℂ) :=
    (Complex.ofReal_intCast _).symm
  rw [this, ← htr, Complex.add_conj]

theorem coeff_eq_zero_of_sum_embeddings {F : Type} [Field F] [NumberField F] (a : (F →+* ℂ) → ℂ)
    (h : ∀ c : 𝓞 F, ∑ τ : F →+* ℂ, a τ * τ (c : F) = 0) (τ : F →+* ℂ) : a τ = 0 := by
  let r : (F →+* ℂ) → (𝓞 F →* ℂ) := fun σ => (σ.comp (algebraMap (𝓞 F) F)).toMonoidHom
  have hr : Function.Injective r := by
    intro σ σ' hs
    have : σ.comp (algebraMap (𝓞 F) F) = σ'.comp (algebraMap (𝓞 F) F) := by
      ext x; exact DFunLike.congr_fun hs x
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) this
  have hli : LinearIndependent ℂ (fun σ : F →+* ℂ => ((r σ : 𝓞 F →* ℂ) : 𝓞 F → ℂ)) :=
    (linearIndependent_monoidHom (𝓞 F) ℂ).comp r hr
  have hsum : ∑ σ, a σ • ((r σ : 𝓞 F →* ℂ) : 𝓞 F → ℂ) = 0 := by
    funext c
    simpa [r, Finset.sum_apply] using h c
  exact (Fintype.linearIndependent_iff.mp hli) a hsum τ

theorem _root_.GlobalTheory.UPel.HT.LieType.finrank_eigSp_add_conj_eq (p : ℕ) [Fact p.Prime] (D : Datum p) (D' : PLat D.O D.inv)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q : D'.La →+ (Fin D.g → ℂ)) (hQ : IsPeriod D' ρ Q)
    (τ : D.F →+* ℂ) :
    Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ) +
      Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) ((starRingEnd ℂ).comp τ)) = D.m * D.n := by
  set φ := ρ.comp (algebraMap (𝓞 D.F) D.O) with hφ
  let d : (D.F →+* ℂ) → ℕ := fun σ => Module.finrank ℂ (eigSp φ σ)
  obtain ⟨hlin, hinj, hdisc, hspan, -⟩ := hQ

  have hrank : Module.finrank ℤ D'.La = (D.m * D.n) * Module.finrank ℚ D.F := by
    rw [finrank_eq_two_mul_of_period Q hinj hdisc hspan]
    have h2 : Module.finrank ℚ D.F = 2 * InfinitePlace.nrComplexPlaces D.F := IsTotallyComplex.finrank D.F
    unfold Datum.g
    rw [h2]
    rw [show D.m * D.n * (2 * InfinitePlace.nrComplexPlaces D.F) = 2 * (D.m * D.n * InfinitePlace.nrComplexPlaces D.F) by ring]
    rw [Nat.mul_div_cancel_left _ (by norm_num)]

  let cj : (D.F →+* ℂ) ≃ (D.F →+* ℂ) :=
    { toFun := fun σ => (starRingEnd ℂ).comp σ
      invFun := fun σ => (starRingEnd ℂ).comp σ
      left_inv := fun σ => by ext x; simp
      right_inv := fun σ => by ext x; simp }
  have key : ∀ c : 𝓞 D.F, ∑ σ : D.F →+* ℂ, (((d σ + d (cj σ) : ℕ) : ℂ) - ((D.m * D.n : ℕ) : ℂ)) * σ (c : D.F) = 0 := by
    intro c
    let A : D'.La →+ D'.La := DistribMulAction.toAddMonoidHom D'.La (algebraMap (𝓞 D.F) D.O c)
    have hA : ∀ x, Q (A x) = φ c *ᵥ Q x := fun x => hlin _ x
    have h1 := trace_int_eq_of_period Q (φ c) A hinj hdisc hspan hA
    have h2 := GlobalTheory.T.trace_ringOfIntegers_action_lattice_eq D.F D.O D'.La (D.m * D.n) hrank c
    have h3 := GlobalTheory.T.trace_ringOfIntegers_action_sum_embeddings_eigenspace D.F D.g φ c
    have hconj : (starRingEnd ℂ) (φ c).trace = ∑ σ : D.F →+* ℂ, (d (cj σ) : ℂ) * σ (c : D.F) := by
      rw [h3, map_sum]
      simp only [map_mul, Complex.conj_natCast]
      exact (Fintype.sum_equiv cj _ _ (fun σ => by
        show (d σ : ℂ) * (starRingEnd ℂ) (σ (c : D.F)) = (d (cj (cj σ)) : ℂ) * (cj σ) (c : D.F)
        have : cj (cj σ) = σ := cj.left_inv σ
        rw [this]; rfl))
    have : ∑ σ : D.F →+* ℂ, ((d σ + d (cj σ) : ℕ) : ℂ) * σ (c : D.F) = ((D.m * D.n : ℕ) : ℂ) * ∑ σ : D.F →+* ℂ, σ (c : D.F) := by
      rw [← h2, h1, hconj, h3, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun σ _ => ?_
      push_cast; ring
    rw [Finset.mul_sum] at this
    simp only [sub_mul, Finset.sum_sub_distrib, this]
    simp
  have := coeff_eq_zero_of_sum_embeddings _ key τ
  have h' : ((d τ + d (cj τ) : ℕ) : ℂ) = ((D.m * D.n : ℕ) : ℂ) := sub_eq_zero.mp this
  exact_mod_cast h'

end GlobalTheory.UPel.HT.LieType.DimSum
