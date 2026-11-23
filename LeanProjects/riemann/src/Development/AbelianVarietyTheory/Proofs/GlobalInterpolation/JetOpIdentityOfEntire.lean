import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubDSharpInDeg

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.JetIdentity

open MvPolynomial

section Lin

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

omit [Fintype ι] in
theorem jetLin_add (J J' : (DVar ι a b →₀ ℕ) → K) : jetLin (J + J') = jetLin J + jetLin J' := by
  refine (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext fun m => ?_
  simp only [jetLin, LinearMap.add_apply, Module.Basis.constr_basis, Pi.add_apply, map_add]

omit [Fintype ι] in
theorem jetLin_smul (c : K) (J : (DVar ι a b →₀ ℕ) → K) : jetLin (c • J) = c • jetLin J := by
  refine (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext fun m => ?_
  simp only [jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, Pi.smul_apply, smul_monomial]

def jetOpL (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) :
    ((DVar ι a b →₀ ℕ) → K) →ₗ[K] (Formalism.L2.DIV.VV K lam →ₗ[K] Formalism.L2.DIV.VV K lam') where
  toFun J := jetOp lam lam' J n
  map_add' J J' := by
    ext1 F
    simp only [jetOp, jetMap, jetLin_add, LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' c J := by
    ext1 F
    simp only [jetOp, jetMap, jetLin_smul, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

theorem jetOp_sum (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) {I : Type} [Fintype I] (ξ : I → K)
    (J : I → (DVar ι a b →₀ ℕ) → K) :
    ∑ i, ξ i • jetOp lam lam' (J i) n = jetOp lam lam' (∑ i, ξ i • J i) n := by
  have := map_sum (jetOpL (K := K) lam lam' n) (fun i => ξ i • J i) Finset.univ
  simp only [map_smul] at this
  exact this.symm

omit [Fintype ι] in
theorem jetLin_congr (J J' : (DVar ι a b →₀ ℕ) → K) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K)
    (h : ∀ μ ∈ Q.support, J (μ.comapDomain Sum.inr Sum.inr_injective.injOn) =
      J' (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) : jetLin J Q = jetLin J' Q := by
  rw [Q.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have e : (monomial μ (coeff μ Q) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) =
      coeff μ Q • basisMonomials _ K μ := by
    simp [coe_basisMonomials, smul_monomial]
  rw [e, map_smul, map_smul]
  simp only [jetLin, Module.Basis.constr_basis, h μ hμ]

theorem jetOp_congr (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) (J J' : (DVar ι a b →₀ ℕ) → K)
    (h : ∀ m : DVar ι a b →₀ ℕ, (∀ τ, ((∑ β : Fin b, ∑ α : Fin a, m (τ, β, α) : ℕ) : ℤ) =
      ∑ s : Fin a, ((lam τ).w s - (lam τ).detShift + (n τ : ℤ))) → J m = J' m) :
    jetOp lam lam' J n = jetOp lam lam' J' n := by
  classical
  ext1 F
  simp only [jetOp, jetMap, LinearMap.comp_apply]
  congr 1
  refine jetLin_congr J J' _ fun μ hμ => h _ fun τ => ?_
  have h1 := GlobalTheory.JetDeg.subD_hom (b := b) τ (GlobalTheory.JetDeg.sharp_hom n τ (GlobalTheory.JetDeg.VV_hom lam τ F.2)) (mem_support_iff.mp hμ)
  rw [GlobalTheory.JetDeg.weight_derW] at h1
  simp only [Finsupp.comapDomain_apply]
  rw [h1]
  push_cast
  simp [GlobalTheory.JetDeg.natW_cast, Finset.sum_add_distrib, mul_comm]

end Lin

section An

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem jetC_sum (cD : ι → ℂ) {I : Type} [Fintype I] (c : I → ℂ) (G : I → VCx ι a b → ℂ)
    (hG : ∀ i, AnalyticOnNhd ℂ (G i) Set.univ) (m : DVar ι a b →₀ ℕ) :
    jetC cD (fun z => ∑ i, c i * G i z) m = ∑ i, c i * jetC cD (G i) m := by
  have hc : ∀ i (k : ℕ), ContDiff ℂ k (G i) := fun i k => (hG i).contDiff
  have e : (fun z => ∑ i, c i * G i z) = fun z => ∑ i, (c i • G i) z := by
    funext z; simp
  unfold jetC derivAt0
  rw [e, iteratedFDeriv_sum (f := fun i => c i • G i) (fun i _ => (hc i _).const_smul (c i))]
  simp only [Finset.sum_apply, ContinuousMultilinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_const_smul_apply (hc i _).contDiffAt]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem map_desc {K : Type} [Field K] (σ : K →+* ℂ) {z : ℂ} (h : ∃ k : K, σ k = z) : σ (desc σ z) = z := by
  rw [desc, dif_pos h]
  exact h.choose_spec

end An

end GlobalTheory.JetIdentity

open GlobalTheory.JetIdentity in

theorem GlobalTheory.jetOp_identity_of_entire : ∀ (X : Fields) (a b : ℕ) (σ : X.K →+* ℂ) (cD : X.Tau → ℂ) (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ) (I₁ I₂ : Type) [Fintype I₁] [Fintype I₂] (ξ₁ : I₁ → X.K) (ξ₂ : I₂ → X.K) (G₁ : I₁ → VCx X.Tau a b → ℂ) (G₂ : I₂ → VCx X.Tau a b → ℂ) (u₁ u₂ : ℂ) (r : X.K), (∀ i, AnalyticOnNhd ℂ (G₁ i) Set.univ) → (∀ i, AnalyticOnNhd ℂ (G₂ i) Set.univ) → (∀ i (m : DVar X.Tau a b →₀ ℕ), (∀ τ, (degAt m τ : ℤ) = degNu lam n τ) → ∃ k : X.K, σ k = u₁ * jetC cD (G₁ i) m) → (∀ i (m : DVar X.Tau a b →₀ ℕ), (∀ τ, (degAt m τ : ℤ) = degNu lam n τ) → ∃ k : X.K, σ k = u₂ * jetC cD (G₂ i) m) → (∀ z, ∑ i, σ (ξ₁ i) * (u₁ * G₁ i z) = σ r * ∑ i, σ (ξ₂ i) * (u₂ * G₂ i z)) → ∑ i, ξ₁ i • jetOp lam lam' (fun m => desc σ (u₁ * jetC cD (G₁ i) m)) n = r • ∑ i, ξ₂ i • jetOp lam lam' (fun m => desc σ (u₂ * jetC cD (G₂ i) m)) n := by
  intro X a b σ cD lam lam' n I₁ I₂ _ _ ξ₁ ξ₂ G₁ G₂ u₁ u₂ r hG₁ hG₂ hr₁ hr₂ hz
  rw [jetOp_sum, jetOp_sum]
  refine Eq.trans ?_ ((jetOpL lam lam' n).map_smul r _)
  refine jetOp_congr lam lam' n _ _ fun m hm => ?_
  apply σ.injective
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_mul, map_sum]
  have h1 := jetC_sum cD (fun i => σ (ξ₁ i) * u₁) G₁ hG₁ m
  have h2 := jetC_sum cD (fun i => σ r * (σ (ξ₂ i) * u₂)) G₂ hG₂ m
  have e : (fun z => ∑ i, σ (ξ₁ i) * u₁ * G₁ i z) = fun z => ∑ i, σ r * (σ (ξ₂ i) * u₂) * G₂ i z := by
    funext z
    have := hz z
    rw [Finset.mul_sum] at this
    simpa only [mul_assoc] using this
  rw [e, h2] at h1
  rw [Finset.mul_sum]
  simp only [fun i => map_desc σ (hr₁ i m hm), fun i => map_desc σ (hr₂ i m hm)]
  simpa only [mul_assoc] using h1.symm

end
