import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.Invar2P

theorem index_ne_zero_of_open_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K U : Subgroup G) (hK : IsCompact (K : Set G)) (hU : IsOpen (U : Set G)) (R : Subgroup K)
    (hR : U.subgroupOf K ≤ R) : R.index ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen K U hU)
  have h0 : (U.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  intro h
  apply h0
  exact Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hR)

end PositivityTheory.Rg.BcB.G3.Invar2P

namespace PositivityTheory.Rg.BcB.G3

theorem invar2_pf : Invar2 := by
  intro E _ _ _ hU a b w K₁ K₂ hK₁ hK₂ φ hφ y g
  obtain ⟨-, -, -, -, hOa, hCa, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU a w
  obtain ⟨-, -, -, -, hOb, hCb, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU b w
  refine GlobalTheory.TwOrbConj.twOrb_twConj _ _ _ y g φ fun x => ?_
  refine Invar2P.index_ne_zero_of_open_le ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) (K₁.prod K₂)
    (by rw [Subgroup.coe_prod]; exact hCa.prod hCb) (by rw [Subgroup.coe_prod]; exact hK₁.1.prod hK₂.1) _ ?_
  intro k hk
  rw [Subgroup.mem_subgroupOf] at hk
  rw [GlobalTheory.TwOrbConj.mem_rStab]
  intro u
  have hθk : ((thL a w).prodMap (thL b w)) (k : GLw a w × GLw b w) ∈ K₁.prod K₂ :=
    Subgroup.mem_prod.2 ⟨hK₁.2.2 _ (Subgroup.mem_prod.1 hk).1, hK₂.2.2 _ (Subgroup.mem_prod.1 hk).2⟩
  have e : ((x * ((u * k : _) : GLw a w × GLw b w))⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * ((u * k : _) : GLw a w × GLw b w))) =
      (k : GLw a w × GLw b w)⁻¹ * ((x * (u : GLw a w × GLw b w))⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * (u : GLw a w × GLw b w))) *
        ((thL a w).prodMap (thL b w)) (k : GLw a w × GLw b w) := by
    simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]; group
  show φ _ = φ _
  rw [e, (hφ.2 _ hθk _).2, (hφ.2 _ ((K₁.prod K₂).inv_mem hk) _).1]

end PositivityTheory.Rg.BcB.G3
