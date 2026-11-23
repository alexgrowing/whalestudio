import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.LocRootsY
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArithFrobeniusAbsGalois
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc

variable {l : ℕ} [Fact l.Prime]

private theorem iqb_unit (x : integralClosure ℤ_[l] (PadicAlgCl l)) (h : ‖(x : PadicAlgCl l)‖ = 1) : IsUnit x := by
  have h0 : (x : PadicAlgCl l) ≠ 0 := by
    intro e; rw [e, norm_zero] at h; exact zero_ne_one h
  refine IsUnit.of_mul_eq_one ⟨(x : PadicAlgCl l)⁻¹, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 ?_⟩
    (Subtype.ext (mul_inv_cancel₀ h0))
  rw [norm_inv, h, inv_one]

private theorem iqb_local : IsLocalRing (integralClosure ℤ_[l] (PadicAlgCl l)) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  have hx : ‖(x : PadicAlgCl l)‖ ≤ 1 := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1 x.2
  rcases hx.eq_or_lt with h | h
  · exact Or.inl (iqb_unit x h)
  · refine Or.inr (iqb_unit _ ?_)
    have : ‖(1 : PadicAlgCl l)‖ ≠ ‖-(x : PadicAlgCl l)‖ := by rw [norm_one, norm_neg]; exact h.ne'
    have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm this
    rw [norm_one, norm_neg, max_eq_left hx] at h2
    simpa [sub_eq_add_neg] using h2

private theorem iqb_frob : ∃ g : GQ l, IsFrob g := by
  haveI := iqb_local (l := l)
  have e : IsLocalRing.ResidueField ℤ_[l] ≃+* ZMod l := PadicInt.residueField
  obtain ⟨g, hg⟩ := GlobalTheory.exists_arithFrobenius_absGalois ℤ_[l] ℚ_[l] (Finite.of_equiv _ e.symm.toEquiv) (PadicAlgCl l)
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨y, hy, hm⟩ := hg ⟨x, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 hx⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod] at hm
  have hle := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1
    (y - (⟨x, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 hx⟩ : integralClosure ℤ_[l] (PadicAlgCl l)) ^ l).2
  have hne := mt (iqb_unit _) hm
  have := lt_of_le_of_ne hle hne
  simpa [hy] using this

private theorem iqb_norm (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := KStar.IdealValuations.norm_aut_and_roots.1 g x

private theorem iqb_sub {x y : Om l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by rwa [norm_neg]))

private theorem iqb_mem (g : GQ l) : g ∈ Iq l ↔ ∀ x : Om l, ‖x‖ ≤ 1 → ‖g x - x‖ < 1 := by
  rw [Iq, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg x hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact iqb_sub (by rwa [iqb_norm]) hlt
    · obtain ⟨m, ζ, hm, hζ, hxζ⟩ := KStar.IdealValuations.exists_root_congr heq
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
      have h1 : g ζ = ζ := hg ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩)
      have h2 : g x - x = g (x - ζ) - (x - ζ) := by rw [map_sub, h1]; ring
      rw [h2]
      exact iqb_sub (by rwa [iqb_norm]) hxζ
  · intro hg x hx
    have hle : MaximalUnramifiedExtension l ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
      rw [MaximalUnramifiedExtension, IntermediateField.adjoin_le_iff]
      rintro ζ ⟨m, hm0, hm, hζ⟩
      have hn : ‖ζ‖ = 1 := by
        have h1 : ‖ζ‖ ^ m = 1 := by rw [← norm_pow, hζ, norm_one]
        exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0.ne').mp h1
      have h1 : g ζ = ζ := KStar.IdealValuations.norm_aut_and_roots.2 m _ _ hm (by rw [← map_pow, hζ, map_one]) hζ
        (hg ζ hn.le)
      have h2 : Subgroup.zpowers g ≤ MulAction.stabilizer (GQ l) ζ :=
        (Subgroup.zpowers_le (G := GQ l)).2 h1
      exact (IntermediateField.mem_fixedField_iff _ _).2 fun f hf => h2 hf
    exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) g (Subgroup.mem_zpowers g)

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.iqBasic :
    ∀ (v : ℕ) [Fact v.Prime], (Iq v).Normal ∧ IsClosed (Iq v : Set (GQ v)) ∧ (∀ g : GQ v, g ∈ Iq v ↔ ∀ x : Om v, ‖x‖ ≤ 1 → ‖g x - x‖ < 1) ∧ (∃ σ : GQ v, IsFrob σ) ∧ ∀ σ σ' : GQ v, IsFrob σ → (IsFrob σ' ↔ σ⁻¹ * σ' ∈ Iq v) := by
  intro v _
  refine ⟨⟨fun n hn g => ?_⟩, ?_, iqb_mem, iqb_frob, fun σ σ' hσ => ?_⟩
  · rw [iqb_mem] at hn ⊢
    intro x hx
    have h := hn (g⁻¹ x) (by rwa [iqb_norm])
    have e : (g * n * g⁻¹) x - x = g (n (g⁻¹ x) - g⁻¹ x) := by
      rw [map_sub, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g g⁻¹ x, mul_inv_cancel,
        AlgEquiv.one_apply]
    rwa [e, iqb_norm]
  · have : IsGalois ℚ_[v] (Om v) := {}
    exact InfiniteGalois.fixingSubgroup_isClosed (MaximalUnramifiedExtension v)
  · have e : ∀ x : Om v, ‖(σ⁻¹ * σ') x - x‖ = ‖σ' x - σ x‖ := fun x => by
      rw [← iqb_norm σ, map_sub, ← AlgEquiv.mul_apply, mul_inv_cancel_left]
    rw [iqb_mem]
    simp only [e]
    constructor
    · intro h x hx
      have h2 : σ' x - σ x = (σ' x - x ^ v) - (σ x - x ^ v) := by ring
      rw [h2]
      exact iqb_sub (h x hx) (hσ x hx)
    · intro h x hx
      have h2 : σ' x - x ^ v = (σ' x - σ x) - -(σ x - x ^ v) := by ring
      rw [h2]
      exact iqb_sub (h x hx) (by rw [norm_neg]; exact hσ x hx)
