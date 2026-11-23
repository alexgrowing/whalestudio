import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTieNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTieLatticeCompatibilityStatement
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.DetInv.FinrankMapAddFinrankInf

theorem finrank_map_add_finrank_inf {C V V' : Type} [Field C] [AddCommGroup V] [Module C V]
    [AddCommGroup V'] [Module C V'] [FiniteDimensional C V] (f : V →ₗ[C] V') (U : Submodule C V) :
    Module.finrank C U =
      Module.finrank C ↥(LinearMap.ker f ⊓ U) + Module.finrank C (U.map f) := by
  rw [← LinearMap.finrank_range_add_finrank_ker (f.domRestrict U), LinearMap.range_domRestrict,
    LinearMap.ker_domRestrict, add_comm, ← Submodule.finrank_map_subtype_eq,
    Submodule.map_comap_subtype, inf_comm]

theorem shift_eq_of_isTie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (ε : PreTilt O p) (h : ℕ) (D : Datum ε h (ℤ_[p] ⊗[ℤ] 𝓞 E)) (φ : P.V ≃ₗ[C] (Fin h → C)), IsPrimitiveRoot (root ε).untilt p → IsTie P D (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom φ → ∀ (σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O) (ψ : E →+* C) (r : NNReal), σ.comp (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom = embO P.integers ψ → IsShift C v D σ r → ∀ (a q : ℕ) (x : Fin a → P.V) (y : Fin q → P.V) (g : Matrix (Fin a) (Fin a) C) (g' : Matrix (Fin q) (Fin q) C), Module.finrank C (P.eigW (embO P.integers ψ)) = a → Module.finrank C (P.eigW ((embO P.integers ψ).comp (starRingEnd (𝓞 E)))) = q → Submodule.span O (Set.range x) = P.wRec (embO P.integers ψ) → Submodule.span O (Set.range y) = P.wRec ((embO P.integers ψ).comp (starRingEnd (𝓞 E))) → IsLatBasis C (open Classical in P.latTQuot (σ := fun φ' : E →+* C => embO P.integers φ') (isSplitting_embO P.integers) ψ) (fun i => ∑ j, g i j • x j) → IsLatBasis C (P.latTSub ((embO P.integers ψ).comp (starRingEnd (𝓞 E)))) (fun i => ∑ j, g' i j • y j) → v g.det = r * v g'.det ∧ g'.det ≠ 0 ∧ Module.finrank C (eig C (actT D) σ) = a + q := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ E _ _ _ P ε h D φ hε T σ ψ r hσ hr a q x y g g' ha hq hx hy hg hg'
  classical
  have hv := P.integers
  obtain ⟨hE1, hE2, hE3, -⟩ :=
    (PadicInclusionHoms.eig_lattices_of_isTie p C v O E P ε h D φ hε T).2.2.2 σ ψ hσ
  obtain ⟨m, k, hm, hk, hkg⟩ := GlobalTheory.T.datum_tie_lattice_compatibility p C v O E P ε h D φ hε T σ ψ hσ q y g' hq hy hg'
  haveI : FiniteDimensional C P.V := φ.symm.finiteDimensional
  have hW : ∀ z, z ∈ P.W ↔ φ z ∈ LinearMap.ker (alC C D) := T.ker
  have hxW : ∀ j, x j ∈ P.eigW (embO P.integers ψ) := by
    intro j
    have h1 := P.wRec_le _ (hx.le (Submodule.subset_span ⟨j, rfl⟩))
    refine ⟨?_, h1.2⟩
    obtain ⟨_, ⟨u, rfl⟩, hu⟩ := (T.lie _).1 h1.1
    refine (hW _).2 ?_
    rw [(ker_bC_eq_range_alC_and_ker_alC_eq_range_bC p C v O hv ε hε _ h D).2, ← hu]
    refine ⟨incl C h u, funext fun i => ?_⟩
    simp [bC, redC, incl, Datum.bb, Matrix.mulVec, dotProduct, map_sum]
  have hle : Submodule.span C (Set.range fun i => ∑ j, g i j • x j) ≤
      Submodule.span C (Set.range x) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hle' : Submodule.span C (Set.range x) ≤ P.eigW (embO P.integers ψ) :=
    Submodule.span_le.2 (Set.range_subset_iff.2 hxW)
  have hsp : Submodule.span C (Set.range fun i => ∑ j, g i j • x j) = P.eigW (embO P.integers ψ) :=
    Submodule.eq_of_le_of_finrank_eq (hle.trans hle')
      (by rw [finrank_span_eq_card hg.1, ha, Fintype.card_fin])
  have hxi : LinearIndependent C x := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, le_antisymm hle' (hsp.ge.trans hle),
      ha, Fintype.card_fin]
  have hmap : ∀ {n : ℕ} (w : Fin n → P.V), Submodule.span O (Set.range fun i => φ (w i)) =
      (Submodule.span O (Set.range w)).map ((φ : P.V →ₗ[C] (Fin h → C)).restrictScalars O) := by
    intro n w
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have b1 : IsBasisOf C (lieSub C D σ) (fun i => φ (x i)) :=
    ⟨hxi.map' (φ : P.V →ₗ[C] (Fin h → C)) φ.ker, by rw [hmap, hx, hE2]⟩
  have b2 : IsBasisOf C (wQuot C D σ) (fun i => ∑ j, g i j • φ (x j)) := by
    have e : (fun i => ∑ j, g i j • φ (x j)) = fun i => φ (∑ j, g i j • x j) := by
      funext i
      simp only [map_sum, map_smul]
    rw [e]
    refine ⟨hg.1.map' (φ : P.V →ₗ[C] (Fin h → C)) φ.ker, ?_⟩
    rw [hmap, hg.2, hsp, wQuot, ← hE3]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨z, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨z, h1, rfl⟩, (hW z).1 h2.1⟩
    · rintro _ ⟨⟨z, h1, rfl⟩, h2⟩
      refine ⟨z, ⟨h1, (hW z).2 h2, ?_⟩, rfl⟩
      obtain ⟨t, -, rfl⟩ := h1
      exact EigenSplit.proj_mem (isSplitting_embO (E := E) hv) P.actV ψ t
  have hs := hr a q _ g m k b1 b2 hm hk
  refine ⟨?_, right_ne_zero_of_mul_eq_one hkg, ?_⟩
  · rw [← hs, mul_assoc, ← map_mul, hkg, map_one, _root_.mul_one]
  · have e1 : LinearMap.ker (alC C D) ⊓ eig C (actT D) σ =
        (P.eigW (embO P.integers ψ)).map (φ : P.V →ₗ[C] (Fin h → C)) := by
      rw [← hE1]
      refine le_antisymm ?_ ?_
      · rintro _ ⟨h1, z, h2, rfl⟩
        exact ⟨z, ⟨(hW z).2 h1, h2⟩, rfl⟩
      · rintro _ ⟨z, h1, rfl⟩
        exact ⟨(hW z).1 h1.1, z, h1.2, rfl⟩
    have e2 : (eig C (actT D) σ).map (alC C D) =
        Submodule.span C (Set.range fun i => ∑ j, k i j • m j) := by
      refine le_antisymm ?_ (Submodule.span_le.2 ?_)
      · rw [← hE1]
        rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        obtain ⟨c, hc, hcz⟩ := P.exists_smul_mem_latT z
        have hc' : algebraMap O C c ≠ 0 := fun h0 => hc (hv.hom_inj (by rw [h0, map_zero]))
        have h1 := P.latTSub_le_latTQuot (σ := fun φ' : E →+* C => embO P.integers φ')
          (isSplitting_embO P.integers) ψ (x := algebraMap O C c • z)
          ((mem_eigSubLat _).2 ⟨by rwa [algebraMap_smul], Submodule.smul_mem _ _ hz⟩)
        have h2 : alC C D (φ (algebraMap O C c • z)) ∈ alQuot C D σ :=
          ⟨_, hE3.le ⟨_, h1, rfl⟩, rfl⟩
        rw [← hk.2, map_smul, map_smul] at h2
        exact (Submodule.smul_mem_iff _ hc').1 (Submodule.span_le_restrictScalars O C _ h2)
      · rintro _ ⟨i, rfl⟩
        obtain ⟨z, hz, e⟩ := hk.2.le (Submodule.subset_span ⟨i, rfl⟩)
        exact ⟨z, hz.1, e⟩
    rw [finrank_map_add_finrank_inf (alC C D), e1, e2, LinearEquiv.finrank_map_eq, ha,
      finrank_span_eq_card hk.1, Fintype.card_fin]

end GlobalTheory.DetInv.FinrankMapAddFinrankInf
