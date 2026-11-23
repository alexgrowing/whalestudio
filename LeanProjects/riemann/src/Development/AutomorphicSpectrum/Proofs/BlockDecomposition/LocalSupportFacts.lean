import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitCompactModCentralizerSeparableLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCommutingTwistedConjCompactMemTwistedCentral

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace GlobalTheory.CompanionTheory.TwistOrbit

theorem finite_of_subset_mul' {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K' : Subgroup G)
    (hK' : IsOpen (K' : Set G)) (D : Set G) (hD : IsCompact D)
    (P : G → Prop) (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set G) (K' : Set G) | P (Quotient.out q)}.Finite := by
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hD
    (show (interior (K' : Set G)).Nonempty from ⟨1, hK'.interior_eq.symm ▸ K'.one_mem⟩)
  refine (s.finite_toSet.image fun g => DoubleCoset.mk T K' g⁻¹).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  have := hs hd
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨g, hg, hgd⟩ := this
  refine ⟨g, hg, ?_⟩
  rw [← DoubleCoset.out_eq' T K' q, DoubleCoset.eq]
  exact ⟨t, ht, g * d, hgd, by simp [hx, mul_assoc]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nrmL_twConj' (hU : Unr E) (n : ℕ) (w : Pl E) (x y : GLw n w) :
    nrmL n w (x⁻¹ * y * thL n w x) = x⁻¹ * nrmL n w y * x := by
  by_cases hs : IsSplitAt w
  · have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    simp only [nrmL, if_pos hs, h1, MonoidHom.id_apply]
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have h2 := (GlobalTheory.BCT.thL_continuous_involutive E hU n w).2
    rw [h1] at h2
    simp only [nrmL, if_neg hs, h1, map_mul, map_inv, h2]
    group

theorem continuous_nrmL' (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = fun u => u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have hc := (GlobalTheory.BCT.thL_continuous_involutive E hU n w).1
    rw [h1] at hc
    have e : nrmL n w = fun u => u * thetaGL n (cj w) u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id.mul hc

theorem proper' (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hy : (nrmL n w y).val.charpoly.Separable)
    (C : Set (GLw n w)) (hC : IsCompact C) : ∃ D : Set (GLw n w), IsCompact D ∧
      ∀ x : GLw n w, x⁻¹ * y * thL n w x ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, x = t * d := by
  have hθ := (GlobalTheory.BCT.thL_continuous_involutive E hU n w).1
  obtain ⟨D₁, hD₁, h₁⟩ := GlobalTheory.T.orbit_compact_mod_centralizer_separable_local E hU n w (nrmL n w y) hy _ (hC.image (continuous_nrmL' hU n w))
  set C₂ := (fun p : GLw n w × GLw n w × GLw n w => p.1 * p.2.1 * (thL n w p.2.2)⁻¹) '' (D₁ ×ˢ C ×ˢ D₁)
  have hC₂ : IsCompact C₂ := (hD₁.prod (hC.prod hD₁)).image (by fun_prop)
  obtain ⟨D₂, hD₂, h₂⟩ := GlobalTheory.NormOneProper.main E hU n w y hy C₂ hC₂
  refine ⟨(fun p : GLw n w × GLw n w => p.1 * p.2) '' (D₂ ×ˢ D₁), (hD₂.prod hD₁).image (by fun_prop), ?_⟩
  intro x hx
  obtain ⟨z, hz, d, hd, rfl⟩ := h₁ x ⟨_, hx, by rw [nrmL_twConj' hU]⟩
  have hz2 : z⁻¹ * y * thL n w z ∈ C₂ := ⟨(d, (z * d)⁻¹ * y * thL n w (z * d), d), ⟨hd, hx, hd⟩, by
    simp only [map_mul]; group⟩
  obtain ⟨t, ht, d₂, hd₂, rfl⟩ := h₂ z hz hz2
  exact ⟨t, ht, d₂ * d, ⟨(d₂, d), ⟨hd₂, hd⟩, rfl⟩, by group⟩

theorem continuous_thPair (hU : Unr E) (a b : ℕ) (w : Pl E) :
    Continuous ((thL a w).prodMap (thL b w)) := by
  have h1 := (GlobalTheory.BCT.thL_continuous_involutive E hU a w).1
  have h2 := (GlobalTheory.BCT.thL_continuous_involutive E hU b w).1
  exact (h1.comp continuous_fst).prodMk (h2.comp continuous_snd)

theorem isOpen_isCompact_pair_integral_points (a b : ℕ) (w : Pl E) :
    IsOpen (K2 a b w : Set (GLw a w × GLw b w)) ∧ IsCompact (K2 a b w : Set (GLw a w × GLw b w)) := by
  obtain ⟨o₁, c₁⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨o₂, c₂⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  rw [K2, Subgroup.coe_prod]
  exact ⟨o₁.prod o₂, c₁.prod c₂⟩

theorem proper_pair (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable)
    (C : Set (GLw a w × GLw b w)) (hC : IsCompact C) :
    ∃ D : Set (GLw a w × GLw b w), IsCompact D ∧ ∀ x : GLw a w × GLw b w,
      x⁻¹ * y * ((thL a w).prodMap (thL b w)) x ∈ C →
        ∃ t ∈ twCent ((thL a w).prodMap (thL b w)) y, ∃ d ∈ D, x = t * d := by
  obtain ⟨D₁, hD₁, p₁⟩ := proper' hU a w y.1 h₁ _ (hC.image continuous_fst)
  obtain ⟨D₂, hD₂, p₂⟩ := proper' hU b w y.2 h₂ _ (hC.image continuous_snd)
  refine ⟨D₁ ×ˢ D₂, hD₁.prod hD₂, fun x hx => ?_⟩
  obtain ⟨t₁, ht₁, d₁, hd₁, e₁⟩ := p₁ x.1 ⟨_, hx, rfl⟩
  obtain ⟨t₂, ht₂, d₂, hd₂, e₂⟩ := p₂ x.2 ⟨_, hx, rfl⟩
  refine ⟨(t₁, t₂), ?_, (d₁, d₂), ⟨hd₁, hd₂⟩, Prod.ext e₁ e₂⟩
  exact Prod.ext ht₁ ht₂

theorem finite_doubleCosets (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable)
    (C : Set (GLw a w × GLw b w)) (hC : IsCompact C) :
    {q : DoubleCoset.Quotient (twCent ((thL a w).prodMap (thL b w)) y : Set (GLw a w × GLw b w))
        (K2 a b w : Set (GLw a w × GLw b w)) |
      ∃ k ∈ K2 a b w, (Quotient.out q * k)⁻¹ * y * ((thL a w).prodMap (thL b w)) (Quotient.out q * k) ∈ C}.Finite := by
  obtain ⟨hKo, hKc⟩ := isOpen_isCompact_pair_integral_points (E := E) a b w
  obtain ⟨D, hD, hp⟩ := proper_pair hU a b w y h₁ h₂ C hC
  have hD' : IsCompact ((fun p : (GLw a w × GLw b w) × (GLw a w × GLw b w) => p.1 * p.2⁻¹) ''
      (D ×ˢ (K2 a b w : Set (GLw a w × GLw b w)))) :=
    (hD.prod hKc).image (continuous_fst.mul continuous_snd.inv)
  refine finite_of_subset_mul' _ (K2 a b w) hKo _ hD'
    (fun x => ∃ k ∈ K2 a b w, (x * k)⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * k) ∈ C) ?_
  rintro x ⟨k, hk, hx⟩
  obtain ⟨t, ht, d, hd, e⟩ := hp _ hx
  refine ⟨t, ht, d * k⁻¹, ⟨(d, k), ⟨hd, hk⟩, rfl⟩, ?_⟩
  rw [← mul_assoc, ← e, mul_inv_cancel_right]

theorem rStab_index_ne_zero (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (K' : Subgroup (GLw a w × GLw b w)) (f : GLw a w × GLw b w → ℂ) (ho : IsOpen (K' : Set (GLw a w × GLw b w)))
    (hf : IsHecke K' f) (x : K2 a b w) :
    (rStab fun k : K2 a b w => f (((x * k : K2 a b w) : GLw a w × GLw b w)⁻¹ * y *
      ((thL a w).prodMap (thL b w)) ((x : GLw a w × GLw b w) * k))).index ≠ 0 := by
  obtain ⟨-, hKc⟩ := isOpen_isCompact_pair_integral_points (E := E) a b w
  have hθ := continuous_thPair hU a b w
  set θ := (thL a w).prodMap (thL b w) with hθdef
  set W : Subgroup (GLw a w × GLw b w) := K' ⊓ K'.comap θ with hW
  have hWo : IsOpen (W : Set (GLw a w × GLw b w)) := by
    rw [hW, Subgroup.coe_inf]
    exact ho.inter (ho.preimage hθ)
  haveI : CompactSpace (K2 a b w) := isCompact_iff_compactSpace.mp hKc
  have hWo' : IsOpen ((W.subgroupOf (K2 a b w) : Subgroup (K2 a b w)) : Set (K2 a b w)) :=
    hWo.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hWo'
  haveI : (W.subgroupOf (K2 a b w)).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hle : W.subgroupOf (K2 a b w) ≤ rStab fun k : K2 a b w => f (((x * k : K2 a b w) : GLw a w × GLw b w)⁻¹ * y *
      θ ((x : GLw a w × GLw b w) * k)) := by
    intro k' hk' k
    have hk'W : (k' : GLw a w × GLw b w) ∈ W := Subgroup.mem_subgroupOf.mp hk'
    have hl : (k' : GLw a w × GLw b w)⁻¹ ∈ K' := K'.inv_mem hk'W.1
    have hr : θ (k' : GLw a w × GLw b w) ∈ K' := hk'W.2
    have e : (((x * (k * k') : K2 a b w) : GLw a w × GLw b w)⁻¹ * y * θ ((x : GLw a w × GLw b w) * (k * k' : K2 a b w))) =
        (k' : GLw a w × GLw b w)⁻¹ * ((((x * k : K2 a b w) : GLw a w × GLw b w)⁻¹ * y *
          θ ((x : GLw a w × GLw b w) * k)) * θ (k' : GLw a w × GLw b w)) := by
      simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
    show f _ = f _
    rw [e, (hf.2 _ hl _).1, (hf.2 _ hr _).2]
  exact (Subgroup.finiteIndex_of_le hle).index_ne_zero

theorem locSupp : PositivityTheory.Rg.BcB.G8.Fin.LocSupp := by
  intro E _ _ _ hU a b w y h₁ h₂
  exact ⟨fun C hC => finite_doubleCosets hU a b w y h₁ h₂ C hC,
    fun K' f ho _ hf x => rStab_index_ne_zero hU a b w y K' f ho hf x⟩

end GlobalTheory.CompanionTheory.TwistOrbit

end
