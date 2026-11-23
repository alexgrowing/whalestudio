import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.GenUnitP

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hR : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold avg
  rw [hR, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  rw [finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun q hq => absurd (Subsingleton.elim q 1) hq)]
  simp

theorem ind_const {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hKθ : ∀ k ∈ K, θ k ∈ K) (y x : G) :
    (fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * y * θ (x * k))) =
      fun _ => (K : Set G).indicator (1 : G → ℂ) (x⁻¹ * y * θ x) := by
  funext k
  have e : (x * (k : G))⁻¹ * y * θ (x * k) = (k : G)⁻¹ * (x⁻¹ * y * θ x) * θ k := by
    simp only [map_mul, _root_.mul_inv_rev]; group
  rw [e]
  by_cases hm : x⁻¹ * y * θ x ∈ K
  · rw [Set.indicator_of_mem (show _ ∈ (K : Set G) from
      K.mul_mem (K.mul_mem (K.inv_mem k.2) hm) (hKθ _ k.2)), Set.indicator_of_mem (show _ ∈ (K : Set G) from hm)]
    rfl
  · rw [Set.indicator_of_notMem (show _ ∉ (K : Set G) from hm), Set.indicator_of_notMem]
    intro h
    apply hm
    have := K.mul_mem (K.mul_mem k.2 h) (K.inv_mem (hKθ _ k.2))
    simpa [mul_assoc] using this

theorem summand_eq {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G)
    (hKθ : ∀ k ∈ K, θ k ∈ K) (y x : G) :
    GlobalTheory.TwOrbConj.summand θ K y ((K : Set G).indicator 1) x =
      if x⁻¹ * y * θ x ∈ K then
        (((twCent θ y ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ y)) : ℕ) : ℂ) else 0 := by
  unfold GlobalTheory.TwOrbConj.summand
  rw [ind_const θ K hKθ y x, avg_const]
  by_cases hm : x⁻¹ * y * θ x ∈ K
  · rw [Set.indicator_of_mem (show _ ∈ (K : Set G) from hm), if_pos hm]; simp
  · rw [Set.indicator_of_notMem (show _ ∉ (K : Set G) from hm), if_neg hm]; simp

end PositivityTheory.Rg.BcB.G3.GenUnitP

theorem PositivityTheory.Rg.BcB.G3.genUnit_pf : PositivityTheory.Rg.BcB.G3.GenUnit := by
  intro G _ _ _ θ K z hKθ hzK huniq hcptK g
  have hidx : ∀ x : G, (rStab fun k : K =>
      (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * z * θ (x * k))).index ≠ 0 := by
    intro x
    rw [PositivityTheory.Rg.BcB.G3.GenUnitP.ind_const θ K hKθ z x]
    have : rStab (fun _ : K => (K : Set G).indicator (1 : G → ℂ) (x⁻¹ * z * θ x)) = ⊤ := by
      ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
    rw [this, Subgroup.index_top]
    exact one_ne_zero
  rw [GlobalTheory.TwOrbConj.twOrb_twConj G θ K z g ((K : Set G).indicator 1) hidx]
  have hcpt : cptPart (twCent θ z) ≤ twCent θ z ⊓ K :=
    le_inf ((Subgroup.closure_le _).2 fun t ht => ht.1)
      ((Subgroup.closure_le _).2 fun t ht => hcptK t ht.1 ht.2)
  have hval : GlobalTheory.TwOrbConj.summand θ K z ((K : Set G).indicator 1) 1 = 1 := by
    rw [PositivityTheory.Rg.BcB.G3.GenUnitP.summand_eq θ K hKθ z 1, if_pos (by simpa using hzK),
      GlobalTheory.TwOrbConj.map_conj_self K (K.one_mem), (Subgroup.relIndex_eq_one).2 hcpt]
    simp
  rw [GlobalTheory.TwOrbConj.twOrb_eq, finsum_eq_single _ (DoubleCoset.mk (twCent θ z) K 1)]
  · obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1
      (DoubleCoset.out_eq' (twCent θ z) K (DoubleCoset.mk (twCent θ z) K 1)).symm
    rw [he, GlobalTheory.TwOrbConj.summand_rep θ K z _ 1 ht hk, hval]
  · intro q hq
    rw [PositivityTheory.Rg.BcB.G3.GenUnitP.summand_eq θ K hKθ z]
    split_ifs with hm
    · exfalso
      apply hq
      obtain ⟨t, ht, k, hk, he⟩ := huniq _ hm
      symm
      conv_rhs => rw [← DoubleCoset.out_eq' (twCent θ z) K q]
      rw [DoubleCoset.eq]
      exact ⟨t, ht, k, hk, by rw [he]; group⟩
    · rfl
