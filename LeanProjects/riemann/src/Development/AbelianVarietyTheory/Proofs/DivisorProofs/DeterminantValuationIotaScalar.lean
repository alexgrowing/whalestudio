import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfElementThetaCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrEmbeddingRingHomPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerMapSubsetImMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantValuationOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIotaScalarExactPairStatement

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem lead_det_all : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (ψ : RL p O Λ →+* RL p O Λ) (Φ : FreeForm D N ψ) (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → D.lieRank σ ≤ N ∧ ∃ c : C, c ≠ 0 ∧ Lead ((algebraMap O C).comp f) (inA (xi ε)) Φ.F.det (D.lieRank σ) c := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D ψ Φ σ f hf
  obtain ⟨-, -, hker, hsurj, hnu, hxi, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  have hA : ∀ a : Ainf p O, f (inA a) = WittVector.fontaineTheta O p a := by
    intro a
    show f (algebraMap (Ainf p O) (RL p O Λ) a) = _
    rw [Algebra.TensorProduct.algebraMap_apply, hf]
    simp
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  set g : RL p O Λ →+* C := (algebraMap O C).comp f with hg
  have hgf : ∀ r, g r = algebraMap O C (f r) := fun r => rfl
  have hf0 : ∀ r, g r = 0 → f r = 0 := fun r hr => hinj (by rw [← hgf, hr, map_zero])
  have hgxi : g (inA (xi ε)) = 0 := by
    rw [hgf, hA]
    have : xi ε ∈ RingHom.ker (WittVector.fontaineTheta O p) := by
      rw [hker]; exact Ideal.subset_span rfl
    rw [RingHom.mem_ker.mp this, map_zero]
  have hgnu : g (inA (nu ε)) ≠ 0 := by
    intro h0; apply hnu; rw [← hA]; exact hf0 _ h0
  have hfs : ∀ o : O, ∃ r, f r = o := by
    intro o; obtain ⟨a, rfl⟩ := hsurj o; exact ⟨inA a, hA a⟩
  have hmu : (inA (mu ε) : RL p O Λ) = (inA (xi ε) : RL p O Λ) * inA (nu ε) := by
    rw [← map_mul, xi_mul_nu]
  have hFG : Φ.F * Φ.G = ((inA (xi ε) : RL p O Λ) * inA (nu ε)) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ)) := by
    rw [Φ.F_mul_G, hmu]
  have hGF : Φ.G * Φ.F = ((inA (xi ε) : RL p O Λ) * inA (nu ε)) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ)) := by
    rw [Φ.G_mul_F, hmu]
  have hαβ : Φ.F.map g * Φ.G.map g = 0 := by
    rw [← Matrix.map_mul, hFG]
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_mul, hgxi, zero_mul, zero_mul,
      Matrix.zero_apply]
  have hβα : Φ.G.map g * Φ.F.map g = 0 := by
    rw [← Matrix.map_mul, hGF]
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_mul, hgxi, zero_mul, zero_mul,
      Matrix.zero_apply]
  have hξreg : (inA (xi ε) : RL p O Λ) ∈ nonZeroDivisors (RL p O Λ) :=
    GlobalTheory.T.ainf_element_theta_compatible p C v O hv ε hε Λ (xi ε) hxi
  have hquot : ∀ c : C, ∃ s t : RL p O Λ, g s ≠ 0 ∧ c * g s = g t := by
    intro c
    by_cases hc : v c ≤ 1
    · obtain ⟨o, ho⟩ := hv.exists_of_le_one hc
      obtain ⟨t, ht⟩ := hfs o
      exact ⟨1, t, by simp, by rw [map_one, mul_one, hgf, ht, ho]⟩
    · by_cases hc0 : c = 0
      · exact ⟨1, 0, by simp, by simp [hc0]⟩
      have h1 : v c⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hc))
      obtain ⟨o, ho⟩ := hv.exists_of_le_one h1
      obtain ⟨s, hs⟩ := hfs o
      refine ⟨s, 1, ?_, ?_⟩
      · rw [hgf, hs, ho]; exact inv_ne_zero hc0
      · rw [hgf, hs, ho, map_one, mul_inv_cancel₀ hc0]
  have hK : ∃ s : RL p O Λ, g s ≠ 0 ∧ ∀ r, g r = 0 → (inA (xi ε) : RL p O Λ) ∣ s * r := by
    obtain ⟨s, hs1, -, hs3⟩ := GlobalTheory.T.dvr_embedding_ring_hom_property p C v O hv ε hε Λ σ
    refine ⟨s, ?_, fun r hr => hs3 f hf r (hf0 r hr)⟩
    intro h0; exact hs1 f hf (hf0 s h0)
  have hexact : ∀ x : Fin N → C, Φ.F.map g *ᵥ x = 0 → ∃ y, x = Φ.G.map g *ᵥ y :=
    ker_map_subset_im_map (RL p O Λ) C g (inA (xi ε) : RL p O Λ) (inA (nu ε)) N Φ.F Φ.G hξreg hgnu hquot hK hGF
  obtain ⟨lam, hlam, hiota⟩ := GlobalTheory.T.exists_iota_scalar_exact_pair C N (Φ.F.map g) (Φ.G.map g) hαβ hβα hexact
  have hlead := GlobalTheory.LeadDet.lead_det (RL p O Λ) C g (inA (xi ε) : RL p O Λ) (inA (nu ε)) N Φ.F Φ.G lam hFG hiota
  have hrank : (Φ.G.map g).rank = D.lieRank σ :=
    GlobalTheory.T.determinant_valuation_order p C v O hv ε hε Λ N h hh D ψ Φ σ f hf
  rw [hrank] at hlead
  refine ⟨?_, lam * g (inA (nu ε)) ^ D.lieRank σ, mul_ne_zero hlam (pow_ne_zero _ hgnu), hlead⟩
  rw [← hrank]
  exact Matrix.rank_le_width _

end GlobalTheory.DetInv
