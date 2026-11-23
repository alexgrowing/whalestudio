import Formalism.LocalToGlobal.GroupLattices.FockModels.ElementaryDivisorBasis

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

theorem dualInclusionLattices : DualHeightInclusion := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w h m r lam0 hd e he
  exact ⟨lb_H_le_Re (mkG h m r lam0 hd) (0 : Fin 1) (lb_edgeLat_of_basis _ _ (restEdgeBasis _ _)) e he,
    lb_Hdual_le_Re' (mkG h m r lam0 hd) (0 : Fin 1) (lb_edgeLat_of_basis _ _ (restEdgeBasis _ _)) e he⟩

theorem hlSpans : HLSpans := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w h m lam0 hd L hL
  classical
  have h0 : ∃ (I : Type) (_ : Finite I) (b0 : Module.Basis I Kf (Vsp Kf lam0)),
      HL (O := O) ι σ lam0 L = Submodule.span O (Set.range b0) :=
    jm_HL_basis (mkG h m 0 lam0 hd) (0 : Fin 1) L hL
  obtain ⟨I, hI, x, hx⟩ := h0
  cases nonempty_fintype I
  have hcard : Fintype.card I = dimV Kf lam0 := (Module.finrank_eq_card_basis x).symm
  refine ⟨x.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [hx]
  congr 1
  simp

theorem mem_span_of_coord {O Kf V : Type} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V]
    [Module O V] [IsScalarTower O Kf V] {I : Type} [Finite I] (x : Module.Basis I Kf V) (a : I → Kf)
    (ha : ∀ i, a i ≠ 0) (F : V) (hF : ∀ i, (a i)⁻¹ * x.coord i F ∈ Set.range (algebraMap O Kf)) :
    F ∈ Submodule.span O (Set.range fun i => a i • x i) := by
  haveI := Fintype.ofFinite I
  rw [← x.sum_repr F]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨o, ho⟩ := hF i
  have e : x.repr F i • x i = o • (a i • x i) := by
    rw [← algebraMap_smul Kf o (a i • x i), ho, smul_smul, Module.Basis.coord_apply]
    congr 1
    field_simp [ha i]
  rw [e]
  exact Submodule.smul_mem _ o (Submodule.subset_span ⟨i, rfl⟩)

theorem bePerfect : BePerfect := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w h m r lam0 hd e he
  have hw := w_ne h
  have hp := p_eq h
  set c : Kf := algebraMap O Kf w with hc
  set A : ℤ := Ar r lam0 with hA
  have hpA : (p : Kf) ^ A * c ^ (-A) = c ^ A := by
    rw [hp, ← zpow_natCast c 2, ← zpow_mul, ← zpow_add₀ hw]
    congr 1
    push_cast
    ring
  have first : ∀ G, G ∈ Re' p ι σ w r lam0 e ↔
      ∀ F ∈ Re p ι σ w r lam0 e, be p r lam0 F G ∈ Set.range (algebraMap O Kf) := by
    intro G
    constructor
    · rintro ⟨ψ, hψ, rfl⟩ F ⟨z, hz, rfl⟩
      have e2 : be p r lam0 ((LinearMap.restrictScalars O ((LinearMap.lsmul Kf _) (c ^ (-A)))) z)
          ((LinearMap.restrictScalars O ((LinearMap.lsmul Kf _) (c ^ (-A)))) ψ) = ψ z := by
        show (c ^ (-A) • ψ) (((p : Kf) ^ A) • (c ^ (-A) • z)) = ψ z
        rw [LinearMap.smul_apply, map_smul, map_smul, smul_smul, smul_smul, mul_assoc, hpA,
          ← zpow_add₀ hw, neg_add_cancel, zpow_zero, one_smul]
      rw [e2]
      exact hψ z hz
    · intro hG
      refine ⟨c ^ A • G, ?_, ?_⟩
      · intro z hz
        have h1 := hG (c ^ (-A) • z) ⟨z, hz, rfl⟩
        have e2 : be p r lam0 (c ^ (-A) • z) G = (c ^ A • G) z := by
          show G (((p : Kf) ^ A) • (c ^ (-A) • z)) = (c ^ A • G) z
          rw [smul_smul, hpA, map_smul, LinearMap.smul_apply]
        rw [← e2]
        exact h1
      · show c ^ (-A) • (c ^ A • G) = G
        rw [smul_smul, ← zpow_add₀ hw, neg_add_cancel, zpow_zero, one_smul]
  refine ⟨first, fun F => ⟨fun hF G hG => (first G).1 hG F hF, fun hF => ?_⟩⟩
  obtain ⟨I, hI, x, π, -, -, -, -, c5, c6⟩ := elementary_divisor_basis h m r lam0 hd e he
  rw [← c5]
  apply mem_span_of_coord x _ (fun i => zpow_ne_zero _ hw)
  intro i
  have h1 := hF ((c ^ (-order r lam0 (π i)) * (p : Kf) ^ (-π i)) • x.coord i)
    (by rw [← c6]; exact Submodule.subset_span ⟨i, rfl⟩)
  have e2 : be p r lam0 F ((c ^ (-order r lam0 (π i)) * (p : Kf) ^ (-π i)) • x.coord i) =
      (c ^ (-order r lam0 (π i)))⁻¹ * x.coord i F := by
    show ((c ^ (-order r lam0 (π i)) * (p : Kf) ^ (-π i)) • x.coord i) (((p : Kf) ^ A) • F) = _
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    congr 1
    rw [hp, ← zpow_natCast c 2, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_neg]
    congr 1
    unfold order
    push_cast
    ring
  rw [← e2]
  exact h1

end Formalism.L2.G.Model
