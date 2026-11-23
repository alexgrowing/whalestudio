import Mathlib
import Formalism.PeriodIntegrals.CharIdem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Development

open CategoryTheory

namespace PI.CharIdemW

open PI.CharIdem

section General

variable {G : Type} [Group G] [Fintype G]

theorem act_single (W : FDRep ℂ G) (g : G) (c : ℂ) :
    act W (MonoidAlgebra.single g c) = c • W.ρ g := by
  rw [PI.CharIdem.act, MonoidAlgebra.lift_single]

theorem act_charIdem (V W : FDRep ℂ G) :
    act W (charIdem V) = ∑ g : G,
      (((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) * V.character g⁻¹) • W.ρ g := by
  rw [PI.CharIdem.charIdem, map_sum]
  simp only [act_single]

theorem comm_of_class (W : FDRep ℂ G) (f : G → ℂ) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (h : G) : W.ρ h * (∑ g : G, f g • W.ρ g) = (∑ g : G, f g • W.ρ g) * W.ρ h := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ (fun g => ?_)
  show W.ρ h * (f g • W.ρ g) = f (h * g * h⁻¹) • W.ρ (h * g * h⁻¹) * W.ρ h
  rw [hf g h, smul_mul_assoc, mul_smul_comm, ← map_mul W.ρ h g, ← map_mul W.ρ (h * g * h⁻¹) h,
    inv_mul_cancel_right]

private theorem nontrivial_of_simple_fdRep (W : FDRep ℂ G) [Simple W] : Nontrivial W := by
  by_contra hW
  rw [not_nontrivial_iff_subsingleton] at hW
  have : Invertible ((Nat.card G : ℂ)) := invertibleOfNonzero
    (Nat.cast_ne_zero.mpr (by rw [Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero))
  have horth := FDRep.char_orthonormal W W
  have h0 : ∀ g : G, W.character g = 0 := fun g => by
    have hz : W.ρ g = 0 := LinearMap.ext fun x => Subsingleton.elim _ _
    show LinearMap.trace ℂ W (W.ρ g) = 0
    rw [hz, map_zero]
  have hne : Nonempty (W ≅ W) := ⟨Iso.refl W⟩
  simp [h0, hne] at horth

theorem end_one_ne_zero (W : FDRep ℂ G) [Simple W] : (1 : Module.End ℂ W) ≠ 0 := by
  have := nontrivial_of_simple_fdRep W
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  apply hx
  simpa using LinearMap.congr_fun h x

theorem nontrivial_of_simple (W : FDRep ℂ G) [Simple W] : Nontrivial W := nontrivial_of_simple_fdRep W

theorem schur_scalar (W : FDRep ℂ G) [Simple W] (T : Module.End ℂ W)
    (hT : ∀ g : G, W.ρ g * T = T * W.ρ g) : ∃ c : ℂ, T = c • 1 := by
  let f : W ⟶ W :=
    { hom := FGModuleCat.ofHom T
      comm := fun g => by
        ext x
        exact (LinearMap.congr_fun (hT g) x).symm }
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ f
  refine ⟨c, ?_⟩
  ext x
  have hx := congrArg (fun φ : W ⟶ W => φ.hom.hom.hom x) hc
  exact hx.symm

theorem act_charIdem_eq_smul (V W : FDRep ℂ G) [Simple W] :
    ∃ c : ℂ, act W (charIdem V) = c • 1 := by
  apply schur_scalar W
  intro g
  rw [act_charIdem]
  refine comm_of_class W
    (fun x => (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * V.character x⁻¹) ?_ g
  intro x h
  rw [show (h * x * h⁻¹)⁻¹ = h * x⁻¹ * h⁻¹ by group, FDRep.char_conj]

open scoped Classical in
theorem trace_act_charIdem (V W : FDRep ℂ G) [Simple V] [Simple W] :
    LinearMap.trace ℂ W (act W (charIdem V)) =
      (Module.finrank ℂ V : ℂ) * (if Nonempty (W ≅ V) then (1 : ℂ) else 0) := by
  have : Invertible ((Nat.card G : ℂ)) := invertibleOfNonzero
    (Nat.cast_ne_zero.mpr (by rw [Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero))
  have horth := FDRep.char_orthonormal W V
  rw [Nat.card_eq_fintype_card] at horth
  rw [act_charIdem, map_sum]
  simp only [map_smul, smul_eq_mul]
  have h1 : ∀ x : G, (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * V.character x⁻¹ *
      LinearMap.trace ℂ W (W.ρ x) = (Module.finrank ℂ V : ℂ) *
        ((Fintype.card G : ℂ)⁻¹ * (W.character x * V.character x⁻¹)) := fun x => by
    rw [show LinearMap.trace ℂ W (W.ρ x) = W.character x from rfl]
    ring
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.mul_sum, ← Finset.mul_sum, horth]

end General

theorem scalar : Scalar := by
  intro G _ _ V W hV hW
  have := hV
  have := hW
  obtain ⟨c, hc⟩ := act_charIdem_eq_smul V W
  have htr := trace_act_charIdem V W
  rw [hc, map_smul, LinearMap.trace_one, smul_eq_mul] at htr
  have hWpos : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    have := nontrivial_of_simple W
    exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  constructor
  · rintro ⟨e⟩
    have hWV : Nonempty (W ≅ V) := ⟨e.symm⟩
    have hdim : (Module.finrank ℂ V : ℂ) = Module.finrank ℂ W := by
      have := congr_fun (FDRep.char_iso e) 1
      rwa [FDRep.char_one, FDRep.char_one] at this
    rw [if_pos hWV, hdim, mul_one] at htr
    have hc1 : c = 1 := mul_right_cancel₀ hWpos (htr.trans (one_mul _).symm)
    rw [hc, hc1, one_smul]
  · intro hE
    have hn : ¬ Nonempty (W ≅ V) := fun ⟨e⟩ => hE.false e.symm
    rw [if_neg hn, mul_zero] at htr
    rw [hc, (mul_eq_zero.mp htr).resolve_right hWpos, zero_smul]

end PI.CharIdemW
