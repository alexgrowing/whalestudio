import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.Unit2P

theorem isCompact_fst {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [T2Space G]
    (t : G × H) (h : IsCompact (closure (Subgroup.zpowers t : Set (G × H)))) :
    IsCompact (closure (Subgroup.zpowers t.1 : Set G)) := by
  have hc : IsCompact (Prod.fst '' closure (Subgroup.zpowers t : Set (G × H))) := h.image continuous_fst
  have hs : (Subgroup.zpowers t.1 : Set G) ⊆ Prod.fst '' closure (Subgroup.zpowers t : Set (G × H)) := by
    rintro x ⟨k, rfl⟩
    exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal hs hc.isClosed)

theorem isCompact_snd {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [T2Space H]
    (t : G × H) (h : IsCompact (closure (Subgroup.zpowers t : Set (G × H)))) :
    IsCompact (closure (Subgroup.zpowers t.2 : Set H)) := by
  have hc : IsCompact (Prod.snd '' closure (Subgroup.zpowers t : Set (G × H))) := h.image continuous_snd
  have hs : (Subgroup.zpowers t.2 : Set H) ⊆ Prod.snd '' closure (Subgroup.zpowers t : Set (G × H)) := by
    rintro x ⟨k, rfl⟩
    exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal hs hc.isClosed)

end PositivityTheory.Rg.BcB.G3.Unit2P

namespace PositivityTheory.Rg.BcB.G3

theorem unit_pair_of_support (h1 : LocGood) (h2 : GenUnit) (h3 : Supp) : Unit2 := by
  intro E _ _ _ hU a b P₁ hP₁ P₂ hP₂
  filter_upwards [h1 E hU a P₁ hP₁, h1 E hU b P₂ hP₂] with w hw1 hw2
  intro y z hy1 hy2 hz1 hz2 hzK
  obtain ⟨hA1, hB1, hC1⟩ := hw1 z.1 (Subgroup.mem_prod.1 hzK).1 hz1
  obtain ⟨hA2, hB2, hC2⟩ := hw2 z.2 (Subgroup.mem_prod.1 hzK).2 hz2
  set K := (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) with hK
  set θ := (thL a w).prodMap (thL b w) with hθ
  have hnt : ∀ (m : ℕ) (g y : GLw m w),
      (nrmL m w (g⁻¹ * y * thL m w g)).val.charpoly = (nrmL m w y).val.charpoly := by
    intro m g y
    rw [ThBasic.nrmL_twist hU, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  have hconjK : ∀ y' ∈ K, (nrmL a w y'.1).val.charpoly = atPl w P₁ → (nrmL b w y'.2).val.charpoly = atPl w P₂ →
      ∃ g, y' = g⁻¹ * z * θ g := by
    intro y' hy' e1 e2
    obtain ⟨g1, hg1⟩ := hC1 y'.1 (Subgroup.mem_prod.1 hy').1 e1
    obtain ⟨g2, hg2⟩ := hC2 y'.2 (Subgroup.mem_prod.1 hy').2 e2
    exact ⟨(g1, g2), Prod.ext hg1 hg2⟩
  refine ⟨?_, fun hyK => hconjK y hyK hy1 hy2⟩
  by_cases hex : ∃ g, y = g⁻¹ * z * θ g
  · rw [if_pos hex]
    obtain ⟨g, rfl⟩ := hex
    refine h2 _ θ K z ?_ hzK ?_ ?_ g
    · intro k hk
      exact Subgroup.mem_prod.2 ⟨ThBasic.thL_mem_KGL hU a w _ (Subgroup.mem_prod.1 hk).1,
        ThBasic.thL_mem_KGL hU b w _ (Subgroup.mem_prod.1 hk).2⟩
    · intro g hg
      obtain ⟨t1, ht1, k1, hk1, e1⟩ := hA1 g.1 (Subgroup.mem_prod.1 hg).1
      obtain ⟨t2, ht2, k2, hk2, e2⟩ := hA2 g.2 (Subgroup.mem_prod.1 hg).2
      refine ⟨(t1, t2), ?_, (k1, k2), Subgroup.mem_prod.2 ⟨hk1, hk2⟩, Prod.ext e1 e2⟩
      have ht1' : t1 * z.1 = z.1 * thL a w t1 := ht1
      have ht2' : t2 * z.2 = z.2 * thL b w t2 := ht2
      show (t1, t2) * z = z * θ (t1, t2)
      exact Prod.ext ht1' ht2'
    · intro t ht hc
      have ht' : t * z = z * θ t := ht
      have e1 : t.1 * z.1 = z.1 * thL a w t.1 := congrArg Prod.fst ht'
      have e2 : t.2 * z.2 = z.2 * thL b w t.2 := congrArg Prod.snd ht'
      exact Subgroup.mem_prod.2 ⟨hB1 t.1 e1 (Unit2P.isCompact_fst t hc), hB2 t.2 e2 (Unit2P.isCompact_snd t hc)⟩
  · rw [if_neg hex]
    by_contra hne
    obtain ⟨g, hg⟩ := h3 _ θ K y _ hne
    have hmem : g⁻¹ * y * θ g ∈ K := by
      by_contra hm
      exact hg (Set.indicator_of_notMem (show g⁻¹ * y * θ g ∉ (K : Set (GLw a w × GLw b w)) from hm) _)
    have c1 : (nrmL a w (g⁻¹ * y * θ g).1).val.charpoly = atPl w P₁ := by
      show (nrmL a w (g.1⁻¹ * y.1 * thL a w g.1)).val.charpoly = _
      rw [hnt]; exact hy1
    have c2 : (nrmL b w (g⁻¹ * y * θ g).2).val.charpoly = atPl w P₂ := by
      show (nrmL b w (g.2⁻¹ * y.2 * thL b w g.2)).val.charpoly = _
      rw [hnt]; exact hy2
    obtain ⟨h, hh⟩ := hconjK _ hmem c1 c2
    apply hex
    refine ⟨h * g⁻¹, ?_⟩
    calc y = g * (g⁻¹ * y * θ g) * (θ g)⁻¹ := by group
      _ = g * (h⁻¹ * z * θ h) * (θ g)⁻¹ := by rw [hh]
      _ = (h * g⁻¹)⁻¹ * z * θ (h * g⁻¹) := by rw [map_mul, map_inv]; group

end PositivityTheory.Rg.BcB.G3

end
