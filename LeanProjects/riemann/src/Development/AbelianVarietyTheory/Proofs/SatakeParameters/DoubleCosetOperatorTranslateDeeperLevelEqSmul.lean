import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeAverage

open Classical in

theorem finsum_translate_eq {G : Type} [Group G] (J J' : Subgroup G) (h : G)
    (hconj : ∀ κ ∈ J', h⁻¹ * κ * h ∈ J)
    (hfin : {c : G ⧸ J' | ∃ x ∈ (J : Set G), (x : G ⧸ J') = c}.Finite) :
    ∃ m : ℕ, 0 < m ∧ ∀ (W : Type) [AddCommGroup W] (f : G → W), (∀ κ ∈ J, ∀ g, f (g * κ) = f g) → ∀ g : G,
      (∑ᶠ c : G ⧸ J', if hc : ∃ x ∈ (J : Set G), (x : G ⧸ J') = c then f (g * hc.choose * h) else 0) =
      m • ∑ᶠ d : G ⧸ J, if hd : ∃ x ∈ {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * h * u'}, (x : G ⧸ J) = d
        then f (g * hd.choose) else 0 := by
  let φ : G ⧸ J' → G ⧸ J := fun c => ((c.out * h : G) : G ⧸ J)
  have hφ : ∀ x : G, φ (x : G ⧸ J') = ((x * h : G) : G ⧸ J) := by
    intro x
    have h1 : ((x : G ⧸ J').out)⁻¹ * x ∈ J' := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    refine QuotientGroup.eq.2 ?_
    have := hconj _ h1
    convert this using 1
    group
  have hφs : ∀ (u : G) (c : G ⧸ J'), φ (u • c) = u • φ c := by
    intro u c
    induction c using QuotientGroup.induction_on with
    | H x =>
      rw [MulAction.Quotient.smul_mk, hφ, hφ, MulAction.Quotient.smul_mk]
      simp [mul_assoc]
  let S : Finset (G ⧸ J') := hfin.toFinset
  have hS : ∀ c, c ∈ S ↔ ∃ x ∈ (J : Set G), (x : G ⧸ J') = c := fun c => hfin.mem_toFinset
  have hSs : ∀ u ∈ J, ∀ c ∈ S, u • c ∈ S := by
    intro u hu c hc
    obtain ⟨x, hx, rfl⟩ := (hS c).1 hc
    exact (hS _).2 ⟨u * x, J.mul_mem hu hx, rfl⟩
  have hT : ∀ d, d ∈ S.image φ ↔ ∃ x ∈ {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * h * u'}, (x : G ⧸ J) = d := by
    intro d
    rw [Finset.mem_image]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hS c).1 hc
      exact ⟨x * h, ⟨x, hx, 1, J.one_mem, by simp⟩, (hφ x).symm⟩
    · rintro ⟨_, ⟨u, hu, u', hu', rfl⟩, rfl⟩
      refine ⟨(u : G ⧸ J'), (hS _).2 ⟨u, hu, rfl⟩, ?_⟩
      rw [hφ]
      exact QuotientGroup.eq.2 (by simpa [mul_assoc] using hu')
  have hcard : ∀ d ∈ S.image φ, (S.filter (fun c => φ c = d)).card =
      (S.filter (fun c => φ c = (h : G ⧸ J))).card := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hd
    obtain ⟨u, hu, rfl⟩ := (hS c).1 hc
    have e : φ (u : G ⧸ J') = u • (h : G ⧸ J) := by rw [hφ]; rfl
    symm
    refine Finset.card_nbij' (fun c => u • c) (fun c => u⁻¹ • c) ?_ ?_ ?_ ?_
    · intro c hc
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hc ⊢
      exact ⟨hSs u hu c hc.1, by rw [hφs, hc.2, e]⟩
    · intro c hc
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hc ⊢
      exact ⟨hSs u⁻¹ (J.inv_mem hu) c hc.1, by rw [hφs, hc.2, e, inv_smul_smul]⟩
    · intro c _
      simp
    · intro c _
      simp
  refine ⟨(S.filter (fun c => φ c = (h : G ⧸ J))).card, ?_, ?_⟩
  · refine Finset.card_pos.2 ⟨((1 : G) : G ⧸ J'), Finset.mem_filter.2 ⟨(hS _).2 ⟨1, J.one_mem, rfl⟩, ?_⟩⟩
    rw [hφ, one_mul]
  intro W _ f hf g
  let F : G ⧸ J → W := fun d => f (g * d.out)
  have hF : ∀ y : G, F (y : G ⧸ J) = f (g * y) := by
    intro y
    have h1 : ((y : G ⧸ J).out)⁻¹ * y ∈ J := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    have := hf _ h1 (g * (y : G ⧸ J).out)
    show f (g * (y : G ⧸ J).out) = _
    rw [← this]
    congr 1
    group
  rw [finsum_eq_sum_of_support_subset (s := S), finsum_eq_sum_of_support_subset (s := S.image φ)]
  · have e1 : (∑ c ∈ S, if hc : ∃ x ∈ (J : Set G), (x : G ⧸ J') = c then f (g * hc.choose * h) else 0) =
        ∑ c ∈ S, F (φ c) := by
      refine Finset.sum_congr rfl fun c hc => ?_
      have hc' := (hS c).1 hc
      rw [dif_pos hc']
      conv_rhs => rw [← hc'.choose_spec.2, hφ, hF]
      rw [mul_assoc]
    have e2 : (∑ d ∈ S.image φ, if hd : ∃ x ∈ {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * h * u'}, (x : G ⧸ J) = d
        then f (g * hd.choose) else 0) = ∑ d ∈ S.image φ, F d := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd' := (hT d).1 hd
      rw [dif_pos hd']
      conv_rhs => rw [← hd'.choose_spec.2, hF]
    rw [e1, e2, Finset.sum_comp F φ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [← hcard d hd]
  · intro d hd
    by_contra hn
    exact hd (dif_neg fun h' => hn (Finset.mem_coe.2 ((hT d).2 h')))
  · intro c hc
    by_contra hn
    exact hc (dif_neg fun h' => hn (Finset.mem_coe.2 ((hS c).2 h')))

theorem heckeD_rt_eq_smul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J J' : Subgroup (GAf L n)) (h : GAf L n), J' ≤ J → (∀ κ ∈ J', h⁻¹ * κ * h ∈ J) → {c : GAf L n ⧸ J' | ∃ x ∈ (J : Set (GAf L n)), (x : GAf L n ⧸ J') = c}.Finite → ∃ m : ℕ, 0 < m ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ J, NG.rt L n κ f = f) → NG.heckeD J' (J : Set (GAf L n)) (NG.rt L n h f) = (m : ℂ) • NG.heckeD J {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * h * u'} f := by
  intro L _ _ _ n J J' h _ hconj hfin
  obtain ⟨m, hm, H⟩ := finsum_translate_eq J J' h hconj hfin
  refine ⟨m, hm, fun W _ _ f hf => ?_⟩
  funext g
  have := H W f (fun κ hκ g => congrFun (hf κ hκ) g) g
  rw [Pi.smul_apply, Nat.cast_smul_eq_nsmul]
  exact this

end GlobalTheory.HeckeAverage
