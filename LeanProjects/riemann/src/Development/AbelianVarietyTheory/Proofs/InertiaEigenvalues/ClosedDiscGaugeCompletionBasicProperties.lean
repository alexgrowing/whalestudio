import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscBasic

variable (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)

theorem norm_add_le_max_disc (x y : Disc l u ρ) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  refine (denseRange_ofPre l u ρ).induction_on₂ (p := fun x y => ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (isClosed_le (by fun_prop) (by fun_prop)) (fun a b => ?_) x y
  rw [← map_add, norm_ofPre, norm_ofPre, norm_ofPre]
  exact gauge_add_le_max l u ρ a b

theorem isUltrametricDist_disc : IsUltrametricDist (Disc l u ρ) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (norm_add_le_max_disc l u ρ)

theorem norm_l_disc_le : ‖((l : ℕ) : Disc l u ρ)‖ ≤ 1 / l := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  rw [← map_natCast (ofPre l u ρ), norm_ofPre]
  refine gauge_le l u ρ (by positivity) (Submodule.subset_span ⟨1, 0, 0, ?_, ?_⟩)
  · field_simp; simp
  · simp

theorem norm_inv_disc_le : ‖ofPre l u ρ (IsLocalization.Away.invSelf (l : A))‖ ≤ l := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  rw [norm_ofPre]
  refine gauge_le l u ρ hl0 (Submodule.subset_span ⟨0, 0, 1, ?_, ?_⟩)
  · simp
  · simp

theorem inv_mul_l_disc : ofPre l u ρ (IsLocalization.Away.invSelf (l : A)) * ((l : ℕ) : Disc l u ρ) = 1 := by
  rw [← map_natCast (ofPre l u ρ), ← map_mul, ← map_one (ofPre l u ρ)]
  congr 1
  rw [mul_comm, ← map_natCast (algebraMap A (PreDisc l u ρ))]
  exact IsLocalization.Away.mul_invSelf _

theorem norm_l_mul (y : Disc l u ρ) : ‖((l : ℕ) : Disc l u ρ) * y‖ = ‖y‖ / l := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  apply le_antisymm
  · calc ‖((l : ℕ) : Disc l u ρ) * y‖ ≤ ‖((l : ℕ) : Disc l u ρ)‖ * ‖y‖ := norm_mul_le _ _
      _ ≤ 1 / l * ‖y‖ := mul_le_mul_of_nonneg_right (norm_l_disc_le l u ρ) (norm_nonneg _)
      _ = ‖y‖ / l := by ring
  · rw [div_le_iff₀ hl0]
    calc ‖y‖ = ‖ofPre l u ρ (IsLocalization.Away.invSelf (l : A)) * (((l : ℕ) : Disc l u ρ) * y)‖ := by
          rw [← mul_assoc, inv_mul_l_disc, one_mul]
      _ ≤ ‖ofPre l u ρ (IsLocalization.Away.invSelf (l : A))‖ * ‖((l : ℕ) : Disc l u ρ) * y‖ := norm_mul_le _ _
      _ ≤ l * ‖((l : ℕ) : Disc l u ρ) * y‖ :=
          mul_le_mul_of_nonneg_right (norm_inv_disc_le l u ρ) (norm_nonneg _)
      _ = _ := by ring

theorem addHom_ext (N : Type) [NormedAddCommGroup N] (hN : ∀ z : N, l • z = 0 → z = 0)
    (F G : Disc l u ρ →+ N) (hF : Continuous F) (hG : Continuous G)
    (h : ∀ a, F (toDisc l u ρ a) = G (toDisc l u ρ a)) : F = G := by
  have hN' : ∀ n : ℕ, ∀ z : N, (l ^ n) • z = 0 → z = 0 := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih => intro z hz; exact ih z (hN _ (by rw [← mul_smul, ← pow_succ']; exact hz))
  have hpre : ∀ y : PreDisc l u ρ, F (ofPre l u ρ y) = G (ofPre l u ρ y) := by
    intro y
    obtain ⟨n, a, hy⟩ := IsLocalization.Away.surj (l : A) y
    have e : ((l ^ n : ℕ) : Disc l u ρ) * ofPre l u ρ y = toDisc l u ρ a := by
      rw [toDisc, RingHom.comp_apply, ← hy, map_mul, mul_comm (ofPre l u ρ y), ← map_natCast (ofPre l u ρ),
        ← map_natCast (algebraMap A (PreDisc l u ρ)), Nat.cast_pow, map_pow, map_pow]
    refine sub_eq_zero.1 (hN' n _ ?_)
    rw [smul_sub, ← map_nsmul F, ← map_nsmul G, nsmul_eq_mul, e, h, sub_self]
  ext x
  exact (denseRange_ofPre l u ρ).induction_on x (isClosed_eq hF hG) hpre

theorem isDiscMap_comp {A' A'' : Type} [CommRing A'] [CommRing A''] {u' : A'} {u'' : A''} {ρ' ρ'' : ℝ≥0}
    {f : A →+* A'} {f' : A' →+* A''} {F : Disc l u ρ →+* Disc l u' ρ'} {F' : Disc l u' ρ' →+* Disc l u'' ρ''}
    (hF : IsDiscMap f F) (hF' : IsDiscMap f' F') : IsDiscMap (f'.comp f) (F'.comp F) :=
  ⟨fun a => by rw [RingHom.comp_apply, hF.ext, hF'.ext, RingHom.comp_apply],
    fun x => (hF'.norm_le _).trans (hF.norm_le x)⟩

theorem disc_basic : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (u : A) (ρ : ℝ≥0), IsUltrametricDist (Disc l u ρ) ∧ (∀ y : Disc l u ρ, ‖((l : ℕ) : Disc l u ρ) * y‖ = ‖y‖ / l) ∧ (∀ (N : Type) [NormedAddCommGroup N], (∀ z : N, l • z = 0 → z = 0) → ∀ F G : Disc l u ρ →+ N, Continuous F → Continuous G → (∀ a, F (toDisc l u ρ a) = G (toDisc l u ρ a)) → F = G) ∧ ∀ (A' A'' : Type) [CommRing A'] [CommRing A''] (u' : A') (u'' : A'') (ρ' ρ'' : ℝ≥0) (f : A →+* A') (f' : A' →+* A'') (F : Disc l u ρ →+* Disc l u' ρ') (F' : Disc l u' ρ' →+* Disc l u'' ρ''), IsDiscMap f F → IsDiscMap f' F' → IsDiscMap (f'.comp f) (F'.comp F) :=
  fun l _ A _ u ρ => ⟨isUltrametricDist_disc l u ρ, norm_l_mul l u ρ,
    fun N _ hN F G hF hG h => addHom_ext l u ρ N hN F G hF hG h,
    fun _ _ _ _ _ _ _ _ _ _ _ _ hF hF' => isDiscMap_comp l u ρ hF hF'⟩

end GlobalTheory.BSP.DiscBasic
