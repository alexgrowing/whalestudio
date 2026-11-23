import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.DecompTypeI
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSymOfModEq

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits

section Generic

variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]

theorem exists_lift [IsGalois ℚ L] (ι : E →ₐ[ℚ] L) (σ : E ≃ₐ[ℚ] E) :
    ∃ τ : L ≃ₐ[ℚ] L, ∀ x, ι (σ x) = τ (ι x) := by
  let _ : Algebra E L := ι.toRingHom.toAlgebra
  have : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  exact ⟨σ.liftNormal L, fun x => (AlgEquiv.liftNormal_commutes σ L x).symm⟩

theorem exists_emb_lift (ι : E →ₐ[ℚ] L) (ψ : E →+* ℂ) : ∃ Ψ : L →+* ℂ, ∀ x, Ψ (ι x) = ψ x := by
  let _ : Algebra E L := ι.toRingHom.toAlgebra
  have : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  have : Algebra.IsAlgebraic E L := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  exact ⟨ComplexEmbedding.lift L ψ, fun x => ComplexEmbedding.lift_algebraMap_apply L ψ x⟩

end Generic

section Cyc

variable (N : ℕ) [NeZero N]

def tauN : (ZMod N)ˣ ≃* (Cond.Cyc N ≃ₐ[ℚ] Cond.Cyc N) :=
  (IsCyclotomicExtension.Rat.galEquivZMod N (Cond.Cyc N)).symm

theorem tauN_root (u : (ZMod N)ˣ) (w : Cond.Cyc N) (hw : w ^ N = 1) : tauN N u w = w ^ (u : ZMod N).val := by
  rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N (Cond.Cyc N) _ hw, tauN, MulEquiv.apply_symm_apply]

theorem cyc_isGalois : IsGalois ℚ (Cond.Cyc N) := IsCyclotomicExtension.isGalois {N} ℚ _

theorem tauN_neg_one (Ψ : Cond.Cyc N →+* ℂ) (x : Cond.Cyc N) : Ψ (tauN N (-1) x) = starRingEnd ℂ (Ψ x) := by
  have key : (Ψ.comp (tauN N (-1) : Cond.Cyc N →+* Cond.Cyc N)).toRatAlgHom =
      ((starRingEnd ℂ).comp Ψ).toRatAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top (Cond.z_spec N)) ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show Ψ (tauN N (-1) (Cond.z N)) = starRingEnd ℂ (Ψ (Cond.z N))
    have hz := (Cond.z_spec N).pow_eq_one
    have h1 : ‖Ψ (Cond.z N)‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hz, map_one]) (NeZero.ne N)
    have h2 : Cond.z N ^ ((-1 : (ZMod N)ˣ) : ZMod N).val * Cond.z N = 1 := by
      rw [← pow_succ, (Cond.z_spec N).pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val]
      simp
    rw [tauN_root N _ _ hz, ← Complex.inv_eq_conj h1]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, h2, map_one]
  exact DFunLike.congr_fun key x

end Cyc

variable {φ : Frame} (H : HostRaw φ)

instance neZero_condN : NeZero H.condN :=
  ⟨by have := H.QS_pos; have := H.hyp.1.pos; have := H.hyp.2.1.pos; positivity⟩

def emb : H.E →ₐ[ℚ] Cond.Cyc H.condN := H.cycEmb

theorem emb_art (u : (ZMod H.condN)ˣ) (x : H.E) :
    emb H (H.gal.symm (H.art u) x) = tauN H.condN u (emb H x) :=
  H.art_spec u (tauN H.condN u) (tauN_root H.condN u _ H.cycZeta_prim.pow_eq_one) x

theorem gal_eq_art_iff (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ) :
    H.gal σ = H.art u ↔ ∀ x, emb H (σ x) = tauN H.condN u (emb H x) := by
  constructor
  · intro h x
    rw [← emb_art, ← h, MulEquiv.symm_apply_apply]
  · intro h
    have h1 : σ = H.gal.symm (H.art u) :=
      AlgEquiv.ext fun x => (emb H).injective (by show emb H _ = emb H _; rw [h, emb_art])
    rw [h1, MulEquiv.apply_symm_apply]

theorem art_surj : Function.Surjective H.art := by
  intro g
  have := cyc_isGalois H.condN
  obtain ⟨τ, hτ⟩ := exists_lift (emb H) (H.gal.symm g)
  obtain ⟨u, rfl⟩ := (tauN H.condN).surjective τ
  exact ⟨u, by rw [← (gal_eq_art_iff H _ u).mpr hτ, MulEquiv.apply_symm_apply]⟩

theorem gal_conj : H.gal H.conj = φ.cc := H.gal.apply_symm_apply _

theorem conj_apply (ψ : H.E →+* ℂ) (x : H.E) : ψ (H.conj x) = starRingEnd ℂ (ψ x) := by
  obtain ⟨Ψ, hΨ⟩ := exists_emb_lift (emb H) ψ
  rw [← hΨ, ← hΨ, ← tauN_neg_one, (gal_eq_art_iff H H.conj (-1)).mp ((gal_conj H).trans H.art_neg_one.symm)]

theorem conj_iff : ∀ (ψ : H.E →+* ℂ) (σ : H.E ≃ₐ[ℚ] H.E),
    (∀ x, ψ (σ x) = starRingEnd ℂ (ψ x)) ↔ H.gal σ = φ.cc := by
  intro ψ σ
  constructor
  · intro h
    have h1 : σ = H.conj := AlgEquiv.ext fun x => ψ.injective (by rw [h, conj_apply])
    rw [h1, gal_conj]
  · intro h x
    have h1 : σ = H.conj := H.gal.injective (h.trans (gal_conj H).symm)
    rw [h1, conj_apply]

theorem sqd_ne_zero : H.sqd ≠ 0 := by
  intro h
  have h1 := H.sqd_sq
  rw [h] at h1
  have h2 : (H.d : H.E) = 0 := by simpa using h1.symm
  exact H.hyp.2.1.ne_zero (by exact_mod_cast h2)

theorem conj_sqd : H.conj H.sqd = -H.sqd := by
  rw [H.gal_sqd, gal_conj]
  simp [Frame.cc, c0]

theorem cm : IsCMField H.E := by
  have := H.galois
  have hTC : IsTotallyComplex H.E := by
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]
    intro hw
    have h2 := RingHom.congr_fun hw H.sqd
    rw [ComplexEmbedding.conjugate_coe_eq, ← conj_apply, conj_sqd, map_neg] at h2
    have h3 : (2 : ℂ) * w.embedding H.sqd = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact (map_ne_zero _).2 (sqd_ne_zero H) h4
  refine IsCMField.of_forall_isConj H.E (σ := H.conj) (fun ψ => ?_)
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact (conj_apply H ψ x).symm

theorem finrank_E : Module.finrank ℚ H.E = 4 * φ.ord := by
  have := H.galois
  rw [← IsGalois.card_aut_eq_finrank, ← φ.natCard_GG]
  exact Nat.card_congr H.gal.toEquiv

theorem finrank_F : Module.finrank ℚ H.F = 2 * φ.ord := by
  have := cm H
  have h0 := Module.finrank_mul_finrank ℚ H.F H.E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two H.F H.E, finrank_E] at h0
  omega

theorem mem_F : ∀ x : H.E, x ∈ H.F ↔ H.conj x = x := by
  intro x
  rw [mem_maximalRealSubfield_iff]
  constructor
  · intro hx
    let ψ : H.E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    apply ψ.injective
    rw [conj_apply]
    exact hx ψ
  · intro hx ψ
    have := conj_apply H ψ x
    rw [hx] at this
    exact this.symm

theorem d_mod_four : H.d % 4 = 3 := D7.d4 H.hyp

theorem art_ch : ∀ u : (ZMod H.condN)ˣ,
    (((H.art u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d := by
  intro u
  have hd : H.d ∣ H.condN := dvd_mul_left _ _
  have h1 := D7.sqrt_act H.hyp.2.1 (d_mod_four H) hd u (tauN H.condN u) (tauN_root H.condN u) (emb H H.sqd)
    (by rw [← map_pow, H.sqd_sq, map_neg, map_natCast])
  rw [← emb_art, H.gal_sqd, MulEquiv.apply_symm_apply, map_mul, map_intCast, D7.sgnN_val] at h1
  have h2 := mul_right_cancel₀ ((map_ne_zero (emb H)).mpr (sqd_ne_zero H)) h1
  exact_mod_cast h2

theorem gal_mem_Psi_iff (σ : H.E ≃ₐ[ℚ] H.E) : H.gal σ ∈ φ.Psi ↔ σ H.sqd = H.sqd := by
  rw [Frame.mem_Psi_iff, H.gal_sqd σ]
  rcases Int.units_eq_one_or (H.gal σ).1.2 with h | h
  · simp [h]
  · rw [h]
    refine iff_of_false (by decide) fun h1 => sqd_ne_zero H ?_
    have h2 : (2 : H.E) * H.sqd = 0 := by
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] at h1
      linear_combination -h1
    simpa using h2

end Formalism.HC.Der

end
