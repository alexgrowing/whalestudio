import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.ThetaSupremumBounds.StatementE

open NumberField IsDedekindDomain MvPolynomial

noncomputable section

namespace Formalism.L2.Ker.Shape

open Formalism.BasicNotions Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Col

section Alg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

def jetCoef (m : DVar ι a b →₀ ℕ) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K →ₗ[K] Pol K ι b :=
  jetLin (fun m' => if m' = m then (1 : K) else 0)

def dPart (s : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) : DVar ι a b →₀ ℕ :=
  s.comapDomain Sum.inr Sum.inr_injective.injOn

private theorem jetLin_monomial' (J : (DVar ι a b →₀ ℕ) → K)
    (s : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (r : K) :
    jetLin J (MvPolynomial.monomial s r) =
      r • MvPolynomial.monomial (s.comapDomain Sum.inl Sum.inl_injective.injOn) (J (dPart s)) := by
  have h1 : MvPolynomial.monomial s r = r • MvPolynomial.monomial s (1 : K) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h1, LinearMap.map_smul]
  congr 1
  unfold jetLin
  rw [show (MvPolynomial.monomial s (1 : K)) = MvPolynomial.basisMonomials _ K s by
    simp [MvPolynomial.coe_basisMonomials], Module.Basis.constr_basis]
  all_goals rfl

theorem map_jetLin {L : Type} [Field L] (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    MvPolynomial.map σ (jetLin J Q) = jetLin (fun m => σ (J m)) (MvPolynomial.map σ Q) := by
  refine MvPolynomial.induction_on' Q (fun s r => ?_) (fun p q hp hq => ?_)
  · rw [MvPolynomial.map_monomial, jetLin_monomial', jetLin_monomial', MvPolynomial.smul_monomial,
      MvPolynomial.smul_monomial, MvPolynomial.map_monomial, smul_eq_mul, smul_eq_mul, map_mul]
  · rw [map_add, map_add, map_add, map_add, hp, hq]

theorem map_frDet {L : Type} [Field L] (σ : K →+* L) (τ : ι) :
    MvPolynomial.map σ (frDet K a τ) = frDet L a τ := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext α s
  simp [RingHom.mapMatrix_apply, MvPolynomial.map_X]

theorem map_subD {L : Type} [Field L] (σ : K →+* L) (P : Pol K ι a) :
    MvPolynomial.map σ (subD K ι a b P) = subD L ι a b (MvPolynomial.map σ P) := by
  have h : (MvPolynomial.map σ).comp (subD K ι a b).toRingHom =
      (subD L ι a b).toRingHom.comp (MvPolynomial.map σ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [subD]
    · intro v
      show MvPolynomial.map σ (subD K ι a b (MvPolynomial.X v)) = subD L ι a b (MvPolynomial.map σ (MvPolynomial.X v))
      rw [MvPolynomial.map_X]
      simp only [subD, MvPolynomial.aeval_X]
      split_ifs <;> simp
  exact RingHom.congr_fun h P

theorem map_jetMap {L : Type} [Field L] (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    MvPolynomial.map σ (jetMap J n P) =
      jetLin (fun m => σ (J m)) (subD L ι a b (MvPolynomial.map σ P * ∏ τ, frDet L a τ ^ n τ)) := by
  simp only [jetMap, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulRight_apply]
  rw [map_jetLin, map_subD, map_mul, map_prod]
  simp only [map_pow, map_frDet]

end Alg

section Scale

variable {ι : Type} [Fintype ι] {a b : ℕ}

end Scale

section Lift

end Lift

section Base

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
  (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
  (c : ℕ) (x : HomE X.E a b)

def unitSc : ℂ := ((Real.sqrt (Real.pi * A.sc) : ℝ) : ℂ)

def thUnit : VCx X.Tau a b → ℂ := fun u => A.thInd Sall N N' c x ((unitSc A)⁻¹ • u)

def lamUnit (τ : X.Tau) : ℂ := A.cD τ * unitSc A

def cUnit (m : DVar X.Tau a b →₀ ℕ) : ℂ := derivAt0 (thUnit A Sall N N' c x) m / (Formalism.DimensionVariation.mfact (⇑m) : ℂ)

def kapBase : ℂ :=
  A.σ₀ (muInvDet sel SB mU mI N fr * (muInvDet sel SB mU mI N' fr')⁻¹) * (A.chiF a b N N')⁻¹

def rcBase (m : DVar X.Tau a b →₀ ℕ) : Pol ℂ X.Tau a →ₗ[ℂ] Pol ℂ X.Tau b :=
  kapBase A SB sel mU mI N fr N' fr' •
    (jetCoef m ∘ₗ (subD ℂ X.Tau a b).toLinearMap ∘ₗ LinearMap.mulRight ℂ (∏ τ, frDet ℂ a τ ^ n τ))

end Base

end Formalism.L2.Ker.Shape
