import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnFactRowDivDiag
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnPtEmpty
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.CoeffTransposeVariables
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnInterlacedLowerTri
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def qn_InZ (n : ℕ) (ν : Fin n → ℕ) (x : MvPolynomial (Fin n × Fin n) ℚ) : Prop :=
  ∃ Y ∈ dualWeyl ℤ n n ν, transposeVariables ℚ n x = map (Int.castRingHom ℚ) Y

theorem qn_eval_map (n : ℕ) (Y : MvPolynomial (Fin n × Fin n) ℤ) :
    eval (idFrame ℚ n n) (map (Int.castRingHom ℚ) Y) = ((eval (idFrame ℤ n n) Y : ℤ) : ℚ) := by
  have h : (eval (idFrame ℚ n n)).comp (map (Int.castRingHom ℚ)) =
      (Int.castRingHom ℚ).comp (eval (idFrame ℤ n n)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro v
      simp only [RingHom.coe_comp, Function.comp_apply, map_X, eval_X, idFrame]
      split_ifs <;> simp
  exact congrArg (fun φ => φ Y) h

theorem qn_InZ_UZ (n : ℕ) (ν : Fin n → ℕ) (u : Module.End ℚ (MvPolynomial (Fin n × Fin n) ℚ))
    (hu : u ∈ UZmon (glOps ℚ n (rowLetters n) Set.univ)) :
    ∀ x, qn_InZ n ν x → qn_InZ n ν (u x) := by
  unfold UZmon at hu
  induction hu using Submonoid.closure_induction with
  | mem g hg =>
    rintro x ⟨Y, hY, hx⟩
    rcases hg with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · exact ⟨rowDiv ℤ a b k Y, rowDivStable ℤ n n ν a b k Y hY, by
        rw [qn_T_divPowE n a b hab, hx, lclosedeq_rowDiv_map]⟩
    · exact ⟨rowDiv ℤ a a k Y, rowDivStable ℤ n n ν a a k Y hY, by
        rw [qn_T_binomE, hx, lclosedeq_rowDiv_map]⟩
  | one => intro x hx; exact hx
  | mul g h _ _ ihg ihh => intro x hx; exact ihg _ (ihh x hx)

theorem qn_InZ_span (n : ℕ) (ν : Fin n → ℕ) {ι : Type} (P : ι → MvPolynomial (Fin n × Fin n) ℤ)
    (h1 : ∀ i, transposeVariables ℤ n (P i) ∈ dualWeyl ℤ n n ν) (x : MvPolynomial (Fin n × Fin n) ℚ)
    (hx : x ∈ Submodule.span ℤ (Set.range fun i => map (Int.castRingHom ℚ) (P i))) : qn_InZ n ν x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨_, h1 i, qn_T_map n (P i)⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨Y1, h1, e1⟩ := hx
    obtain ⟨Y2, h2, e2⟩ := hy
    exact ⟨Y1 + Y2, Submodule.add_mem _ h1 h2, by rw [map_add, map_add, e1, e2]⟩
  | smul c x _ hx =>
    obtain ⟨Y1, h1, e1⟩ := hx
    exact ⟨c • Y1, Submodule.smul_mem _ _ h1, by rw [map_zsmul, map_zsmul, e1]⟩

theorem qn_main (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) {ι : Type}
    (P : ι → MvPolynomial (Fin n × Fin n) ℤ) (i0 : ι)
    (h1 : ∀ i, transposeVariables ℤ n (P i) ∈ dualWeyl ℤ n n ν)
    (h2 : dualWeyl ℤ n n ν ≤ Submodule.span ℤ (Set.range fun i => transposeVariables ℤ n (P i)))
    (h3 : eval (idFrame ℤ n n) (transposeVariables ℤ n (P i0)) = 1) :
    (Submodule.span ℤ (Set.range fun i => map (Int.castRingHom ℚ) (P i)) :
        Set (MvPolynomial (Fin n × Fin n) ℚ)) =
      {x | x ∈ Submodule.span ℚ (Set.range fun i => map (Int.castRingHom ℚ) (P i)) ∧
        x ∈ Nabla (O := ℤ) (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ))
          (map (Int.castRingHom ℚ) (P i0))} := by
  classical
  set v := map (Int.castRingHom ℚ) (P i0) with hv
  have hTv : transposeVariables ℚ n v = map (Int.castRingHom ℚ) (transposeVariables ℤ n (P i0)) := qn_T_map n (P i0)
  have hTvmem : transposeVariables ℚ n v ∈ dualWeyl ℚ n n ν := by
    rw [hTv]; exact dualWeylMap ℤ ℚ _ n n ν _ (h1 i0)
  have hTvev : eval (idFrame ℚ n n) (transposeVariables ℚ n v) = 1 := by
    rw [hTv, qn_eval_map, h3, Int.cast_one]
  ext x
  simp only [SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨Submodule.span_le_restrictScalars ℤ ℚ _ hx, ?_⟩
    intro u hu
    obtain ⟨Y, hY, hy⟩ := qn_InZ_UZ n ν u hu x (qn_InZ_span n ν P h1 x hx)
    refine ⟨eval (idFrame ℤ n n) Y, ?_⟩
    apply qn_mem_otherWts'
    have hYQ : transposeVariables ℚ n (u x) ∈ dualWeyl ℚ n n ν := by
      rw [hy]; exact dualWeylMap ℤ ℚ _ n n ν _ hY
    rw [map_sub, map_smul, map_sub, map_smul, qn_comp n ν hν _ hYQ, qn_comp n ν hν _ hTvmem, hTvev, hy,
      qn_eval_map, one_smul, eq_intCast, sub_self]
  · rintro ⟨hxQ, hxN⟩
    have hxD : transposeVariables ℚ n x ∈ dualWeyl ℚ n n ν := by
      have hle : Submodule.span ℚ (Set.range fun i => map (Int.castRingHom ℚ) (P i)) ≤
          (dualWeyl ℚ n n ν).comap (transposeVariables ℚ n).toLinearMap := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        show transposeVariables ℚ n (map (Int.castRingHom ℚ) (P i)) ∈ dualWeyl ℚ n n ν
        rw [qn_T_map]
        exact dualWeylMap ℤ ℚ _ n n ν _ (h1 i)
      exact hle hxQ
    set W : Set (MvPolynomial (Fin n × Fin n) ℚ) :=
      {F | ∃ y, F = transposeVariables ℚ n y ∧ transposeVariables ℚ n y ∈ dualWeyl ℚ n n ν ∧
        y ∈ Nabla (O := ℤ) (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ)) v} with hWdef
    have hW : ∀ F ∈ W, ∀ (a b : Fin n) (k : ℕ), a ≠ b → rowDiv ℚ a b k F ∈ W := by
      rintro F ⟨y, rfl, hyD, hyN⟩ a b k hab
      refine ⟨divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k y, (qn_T_divPowE n a b hab k y).symm, ?_, ?_⟩
      · rw [qn_T_divPowE n a b hab]
        exact rowDivStable ℚ n n ν a b k _ hyD
      · intro u hu
        have hg : divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k ∈
            UZmon (glOps ℚ n (rowLetters n) Set.univ) :=
          Submonoid.subset_closure (Or.inl ⟨a, b, k, hab, rfl⟩)
        exact hyN (u * divPowE (glOps ℚ n (rowLetters n) Set.univ) a b k) (Submonoid.mul_mem _ hu hg)
    have hev : ∀ F ∈ W, ∃ z : ℤ, eval (idFrame ℚ n n) F = z := by
      rintro F ⟨y, rfl, hyD, hyN⟩
      obtain ⟨c, hc⟩ := hyN 1 (Submonoid.one_mem _)
      refine ⟨c, ?_⟩
      have h := qn_otherWts_coeff' n ν _ hc
      rw [Module.End.one_apply, map_sub, map_smul, coeff_sub, coeff_smul,
        ← qn_eval_eq_coeff n ν _ (qn_colHom ℚ n ν _ hyD), ← qn_eval_eq_coeff n ν _ (qn_colHom ℚ n ν _ hTvmem),
        hTvev, smul_eq_mul, mul_one, eq_intCast, sub_eq_zero] at h
      exact h
    have hcol : ∀ F ∈ W, IsWeightedHomogeneous (colW n n) F ν := by
      rintro F ⟨y, rfl, hyD, _⟩
      exact qn_colHom ℚ n ν _ hyD
    have htri := qn_tri n ν W hW hev hcol (transposeVariables ℚ n x) ⟨x, rfl, hxD, hxN⟩
    obtain ⟨Q', hQ'⟩ := qn_lowerTriIntegral n n ν (transposeVariables ℚ n x) hxD htri
    have hQ'' : transposeVariables ℚ n x = map (Int.castRingHom ℚ) Q' := hQ'
    have hQmem : Q' ∈ dualWeyl ℤ n n ν := (dualWeylIntRat n n ν Q').mpr (hQ'' ▸ hxD)
    have hQs := h2 hQmem
    set φ : MvPolynomial (Fin n × Fin n) ℤ →ₗ[ℤ] MvPolynomial (Fin n × Fin n) ℚ :=
      (intQ n n).comp (transposeVariables ℤ n).toLinearMap with hφ
    have hφx : φ Q' = x := by
      show map (Int.castRingHom ℚ) (transposeVariables ℤ n Q') = x
      rw [← qn_T_map, ← hQ'', transposeVariables_involutive]
    have hx := Submodule.mem_map_of_mem (f := φ) hQs
    rw [Submodule.map_span, hφx] at hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    show _ = map (Int.castRingHom ℚ) (transposeVariables ℤ n (transposeVariables ℤ n (P i)))
    rw [transposeVariables_involutive]

end Formalism.InvariantFactorPaths.ColumnFamilies
