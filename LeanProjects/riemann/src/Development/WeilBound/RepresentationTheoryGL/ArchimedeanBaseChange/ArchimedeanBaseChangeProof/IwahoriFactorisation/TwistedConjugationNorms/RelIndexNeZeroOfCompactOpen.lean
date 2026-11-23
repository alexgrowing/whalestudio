import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevelStatement

open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

section Gen

variable {G : Type} [Group G]

theorem coe_map_conj [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (x : G) :
    (H.map (MulAut.conj x).toMonoidHom : Set G) =
      ((Homeomorph.mulLeft x).trans (Homeomorph.mulRight x⁻¹)) '' (H : Set G) := by
  rw [Subgroup.coe_map]
  rfl

theorem inf_map_conj_le_cptPart [TopologicalSpace G] [IsTopologicalGroup G] (T K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (x : G) :
    T ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart T := by
  intro t ht
  have ht' := Subgroup.mem_inf.1 ht
  unfold cptPart
  apply Subgroup.subset_closure
  refine ⟨ht'.1, ?_⟩
  have hC : IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
    rw [coe_map_conj]; exact hKc.image (Homeomorph.continuous _)
  have hCo : IsOpen ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
    rw [coe_map_conj]; exact (Homeomorph.isOpenMap _) _ hKo
  have hCcl := Subgroup.isClosed_of_isOpen _ hCo
  refine hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hCcl)
  intro y hy
  exact (Subgroup.zpowers_le.2 ht'.2) hy

theorem cptPart_le_comap_conj [TopologicalSpace G] [IsTopologicalGroup G] (T : Subgroup G) {c : G}
    (hc : c ∈ T) : cptPart T ≤ (cptPart T).comap (MulAut.conj c).toMonoidHom := by
  unfold cptPart
  refine (Subgroup.closure_le _).2 ?_
  rintro t ⟨htT, htc⟩
  simp only [Subgroup.coe_comap, Set.mem_preimage]
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact T.mul_mem (T.mul_mem hc htT) (T.inv_mem hc)
  · have hz : (Subgroup.zpowers ((MulAut.conj c).toMonoidHom t) : Set G) =
        ((Homeomorph.mulLeft c).trans (Homeomorph.mulRight c⁻¹)) '' (Subgroup.zpowers t : Set G) := by
      rw [← MonoidHom.map_zpowers, coe_map_conj]
    rw [hz, ← Homeomorph.image_closure]
    exact htc.image (Homeomorph.continuous _)

theorem relIndex_ne_zero_of_compact_open [TopologicalSpace G] [IsTopologicalGroup G] {C U : Subgroup G}
    (hC : IsCompact (C : Set G)) (hU : IsOpen (U : Set G)) : U.relIndex C ≠ 0 := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have : Finite (C ⧸ U.subgroupOf C) :=
    Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem twOrb_indicator_eq_inv_index [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G)
    (K I : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hθK : ∀ k ∈ K, θ k ∈ K)
    (hI : IsLevel θ K I) (δ : G) (X : Set G) (hXI : ∀ i ∈ I, ∀ x, (i * x ∈ X ↔ x ∈ X) ∧ (x * i ∈ X ↔ x ∈ X))
    (hXc : HasCompactSupport (X.indicator (1 : G → ℂ))) (p0 : G)
    (hP : ∀ p : G, p⁻¹ * δ * θ p ∈ X ↔ ∃ c ∈ twCent θ δ, ∃ i ∈ I, p = c * p0 * i)
    (hcpt : cptPart (twCent θ δ) ≤ I.map (MulAut.conj p0).toMonoidHom) :
    twOrb θ K δ (X.indicator 1) = ((I.relIndex K : ℕ) : ℂ)⁻¹ := by
  obtain ⟨hIo, hIK, hθI⟩ := hI
  have hIcl : IsClosed (I : Set G) := I.isClosed_of_isOpen hIo
  have hIc : IsCompact (I : Set G) := hKc.of_isClosed_subset hIcl hIK
  have hcpT : cptPart (twCent θ δ) ≤ twCent θ δ := (Subgroup.closure_le _).2 fun t ht => ht.1
  have hH : IsHecke I (X.indicator (1 : G → ℂ)) := by
    refine ⟨hXc, fun k hk x => ⟨?_, ?_⟩⟩
    · simp only [Set.indicator_apply, (hXI k hk x).1, Pi.one_apply]
    · simp only [Set.indicator_apply, (hXI k hk x).2, Pi.one_apply]
  have hb : ∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧
      (twCent θ δ ⊓ I.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0 := by
    intro x
    refine ⟨inf_map_conj_le_cptPart _ K hKo hKc x, ?_⟩
    have hC : IsCompact ((I.map (MulAut.conj p0).toMonoidHom : Subgroup G) : Set G) := by
      rw [coe_map_conj]; exact hIc.image (Homeomorph.continuous _)
    have hO : IsOpen ((I.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
      rw [coe_map_conj]; exact (Homeomorph.isOpenMap _) _ hIo
    have h1 := relIndex_ne_zero_of_compact_open hC hO
    have h2 : (I.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0 :=
      fun h => h1 (Subgroup.relIndex_eq_zero_of_le_right hcpt h)
    rw [← Subgroup.inf_relIndex_right]
    have e : twCent θ δ ⊓ I.map (MulAut.conj x).toMonoidHom ⊓ cptPart (twCent θ δ) =
        I.map (MulAut.conj x).toMonoidHom ⊓ cptPart (twCent θ δ) :=
      le_antisymm (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (le_inf (le_inf (inf_le_right.trans hcpT) inf_le_left) inf_le_right)
    rw [e, Subgroup.inf_relIndex_right]
    exact h2
  have hq : ∀ q : DoubleCoset.Quotient (twCent θ δ : Set G) (I : Set G),
      X.indicator (1 : G → ℂ) ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) ≠ 0 →
        q = DoubleCoset.mk (twCent θ δ) I p0 := by
    intro q hq
    have hm : (Quotient.out q)⁻¹ * δ * θ (Quotient.out q) ∈ X := by
      by_contra h
      exact hq (Set.indicator_of_notMem h _)
    obtain ⟨c, hc, i, hi, he⟩ := (hP _).1 hm
    rw [← DoubleCoset.out_eq' (twCent θ δ) I q, DoubleCoset.eq]
    exact ⟨c⁻¹, (twCent θ δ).inv_mem hc, i⁻¹, I.inv_mem hi, by rw [he]; group⟩
  have hfin : {q : DoubleCoset.Quotient (twCent θ δ : Set G) (I : Set G) |
      X.indicator (1 : G → ℂ) ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) ≠ 0}.Finite :=
    (Set.finite_singleton (DoubleCoset.mk (twCent θ δ) I p0)).subset
      fun q hq' => Set.mem_singleton_iff.2 (hq q hq')
  have hcl : ∀ c ∈ twCent θ δ, ∀ i ∈ I,
      cptPart (twCent θ δ) ≤ I.map (MulAut.conj (c * p0 * i)).toMonoidHom := by
    intro c hc i hi y hy
    have h1 : c⁻¹ * y * c ∈ cptPart (twCent θ δ) := by
      have := cptPart_le_comap_conj (twCent θ δ) ((twCent θ δ).inv_mem hc) hy
      simpa [MulAut.conj_apply] using this
    obtain ⟨j, hj, hj'⟩ := Subgroup.mem_map.1 (hcpt h1)
    refine Subgroup.mem_map.2 ⟨i⁻¹ * j * i, I.mul_mem (I.mul_mem (I.inv_mem hi) hj) hi, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hj' ⊢
    calc c * p0 * i * (i⁻¹ * j * i) * (c * p0 * i)⁻¹ = c * (p0 * j * p0⁻¹) * c⁻¹ := by group
      _ = y := by rw [hj']; group
  have key := GlobalTheory.T.twistedOrbitalIntegral_eq_sum_smallerLevel G θ K hKo hKc hθK I ⟨hIo, hIK, hθI⟩ δ (X.indicator 1) hH hb hfin
  rw [key.1, key.2]
  rw [finsum_eq_single _ (DoubleCoset.mk (twCent θ δ) I p0)]
  · obtain ⟨h, hh, k, hk, hq0⟩ := (DoubleCoset.eq (twCent θ δ) I _ _).1
      (DoubleCoset.out_eq' (twCent θ δ) I (DoubleCoset.mk (twCent θ δ) I p0))
    have ho : Quotient.out (DoubleCoset.mk (twCent θ δ) I p0) = h⁻¹ * p0 * k⁻¹ :=
      calc Quotient.out (DoubleCoset.mk (twCent θ δ) I p0)
          = h⁻¹ * (h * Quotient.out (DoubleCoset.mk (twCent θ δ) I p0) * k) * k⁻¹ := by group
        _ = h⁻¹ * p0 * k⁻¹ := by rw [← hq0]
    have hX1 : X.indicator (1 : G → ℂ) ((Quotient.out (DoubleCoset.mk (twCent θ δ) I p0))⁻¹ * δ *
        θ (Quotient.out (DoubleCoset.mk (twCent θ δ) I p0))) = 1 :=
      Set.indicator_of_mem ((hP _).2 ⟨h⁻¹, (twCent θ δ).inv_mem hh, k⁻¹, I.inv_mem hk, ho⟩) _
    have hle := hcl h⁻¹ ((twCent θ δ).inv_mem hh) k⁻¹ (I.inv_mem hk)
    rw [← ho] at hle
    have hR : (twCent θ δ ⊓ I.map (MulAut.conj (Quotient.out (DoubleCoset.mk (twCent θ δ) I p0))).toMonoidHom).relIndex
        (cptPart (twCent θ δ)) = 1 := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf_eq_top.2 (le_inf hcpT hle), Subgroup.index_top]
    rw [hX1, hR]
    simp
  · intro q hne
    have h0 : X.indicator (1 : G → ℂ) ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) = 0 := by
      by_contra h
      exact hne (hq q h)
    rw [h0, mul_zero]

theorem twConj_equivalence (θ : G →* G) : Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) := by
  refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp only [inv_inv, map_inv]; group⟩
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by simp only [map_mul]; group⟩

theorem rep_mk_eq (θ : G →* G) (x : G) :
    ∃ g : G, TwCl.rep (Quot.mk (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) x : TwCl θ) = g⁻¹ * x * θ g := by
  have e : Quot.mk (fun x y : G => ∃ g, y = g⁻¹ * x * θ g)
      (Quot.out (Quot.mk (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) x)) =
      Quot.mk (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) x := Quot.out_eq _
  exact (twConj_equivalence θ).symm ((twConj_equivalence θ).eqvGen_iff.1 (Quot.eqvGen_exact e))

theorem clSum_eq_single (θ : G →* G) [TopologicalSpace G] (K : Subgroup G) (S : Set G) (wt f : G → ℂ) (δ0 : G)
    (hS0 : ∀ g : G, g⁻¹ * δ0 * θ g ∈ S)
    (hinv : ∀ g : G, wt (g⁻¹ * δ0 * θ g) * twOrb θ K (g⁻¹ * δ0 * θ g) f = wt δ0 * twOrb θ K δ0 f)
    (hone : ∀ c : TwCl θ, c.rep ∈ S → wt c.rep * twOrb θ K c.rep f ≠ 0 → ∃ g : G, c.rep = g⁻¹ * δ0 * θ g) :
    clSum θ K S wt f = wt δ0 * twOrb θ K δ0 f := by
  unfold clSum
  refine (finsum_eq_single _ (Quot.mk (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) δ0 : TwCl θ) ?_).trans ?_
  · intro c hc
    by_contra hne
    split_ifs at hne with hcS
    · obtain ⟨g, hg⟩ := hone c hcS hne
      apply hc
      have e1 : Quot.mk (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) (Quot.out c) = c := Quot.out_eq c
      rw [← e1]
      change Quot.mk _ (TwCl.rep c) = _
      rw [hg]
      exact (Quot.sound ⟨g, rfl⟩).symm
    · exact hne rfl
  · obtain ⟨g, hg⟩ := rep_mk_eq θ δ0
    rw [hg, if_pos (hS0 g), hinv g]

end Gen

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
