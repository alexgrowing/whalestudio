import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VLtOneOfOrdLEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagTMemIwGL
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DoubleCosetSeparation

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open GlobalTheory.CompanionTheory.IwahoriContraction in

private theorem conj_diag {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (ϖ : (w.adicCompletion E)ˣ)
    (hϖ : ordL (ϖ : w.adicCompletion E) = 1) (n : ℕ) (y : Fin n → ℤ) (hy : StrictAnti y) (δ : GLw n w)
    (hδ : dcos n w (tdiag ϖ y) δ ≠ 0) :
    ∃ m t : GLw n w, ((∀ i j : Fin n, i ≠ j → t.val i j = 0) ∧ ∀ i, Valued.v (t.val i i) = 1) ∧
      m⁻¹ * δ * m = tdiag ϖ y * t := by
  have hd : ∃ a ∈ iwGL n w, ∃ b ∈ iwGL n w, δ = a * tdiag ϖ y * b := by
    by_contra h
    exact hδ (if_neg h)
  obtain ⟨a, ha, b, hb, hab⟩ := hd
  obtain ⟨⟨U, hU⟩, -, hcpt, -⟩ := GlobalTheory.CompanionTheory.TfLoc.Iw.iwahori_compact_open_galois.1 (w.adicCompletion E) n
  have hcomp : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hequiv := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v
  have h0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  have hid : ∀ g : GL (Fin n) (w.adicCompletion E),
      Matrix.GeneralLinearGroup.map ((RingEquiv.refl (w.adicCompletion E) : _ ≃+* _) : _ →+* _) g = g := by
    intro g
    apply Units.ext
    ext i j
    rfl
  have hlt : ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) < 1 :=
    (GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w _).2 (v_lt_one_of_ordL_eq_one w h0 hϖ)
  have hmax : ∀ x : w.adicCompletion E, ValuativeRel.valuation (w.adicCompletion E) x < 1 →
      ValuativeRel.valuation (w.adicCompletion E) x ≤
        ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) := fun x hx =>
    (hequiv.le_iff_le).2 (v_le_of_ordL_eq_one w h0 hϖ ((GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w _).1 hx))
  let e : Fin n → w.adicCompletion E := fun i => ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E)
  have hgap : ∀ i l, i < l → ValuativeRel.valuation (w.adicCompletion E) (e i) ≤
      ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) *
        ValuativeRel.valuation (w.adicCompletion E) (e l) := fun i l h => by
    obtain ⟨c, hc⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ y i - y l - 1 by have := hy h; omega)
    have hyi : y i = y l + ((c + 1 : ℕ) : ℤ) := by push_cast; omega
    have hei : e i = e l * (ϖ : w.adicCompletion E) ^ (c + 1) := by
      show ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        ((ϖ ^ y l : (w.adicCompletion E)ˣ) : w.adicCompletion E) * _
      rw [hyi, _root_.zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
    rw [hei, map_mul, map_pow, mul_comm]
    refine mul_le_mul' ?_ le_rfl
    calc ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) ^ (c + 1)
        ≤ ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) ^ 1 :=
          pow_le_pow_right_of_le_one' hlt.le (Nat.succ_le_succ (Nat.zero_le c))
      _ = _ := pow_one _
  have hx : ((tdiag ϖ y : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal e := by
    rw [tdiag, GlobalTheory.SmGL.val_diagT]
  have hmem : δ ∈ PositivityTheory.Rg.Tf.Loc.iwDouble (w.adicCompletion E) (tdiag ϖ y : GLw n w) :=
    ⟨a, (mem_iwGL_iff w n a).1 ha, b, (mem_iwGL_iff w n b).1 hb, hab⟩
  obtain ⟨m, -, t, ht, h⟩ := GlobalTheory.CompanionTheory.TwContraction.contraction U hU hcpt (RingEquiv.refl _)
    (fun _ => rfl) (fun g hg => by rw [hid]; exact hg) _ hlt hmax e (fun i => Units.ne_zero _) hgap _ hx δ hmem
  rw [hid] at h
  exact ⟨m, t, torusO_subset_TO w n t ht, h⟩

private theorem sep_of_dcos {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (ϖ : (w.adicCompletion E)ˣ)
    (hϖ : ordL (ϖ : w.adicCompletion E) = 1) (n : ℕ) (y : Fin n → ℤ) (hy : StrictAnti y) (δ : GLw n w)
    (hδ : dcos n w (tdiag ϖ y) δ ≠ 0) : δ.val.charpoly.Separable := by
  obtain ⟨m, t, ⟨hoff, hdiag⟩, h⟩ := conj_diag w ϖ hϖ n y hy δ hδ
  let d : Fin n → w.adicCompletion E := fun i => ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E) * t.val i i
  have ht0 : ∀ i, t.val i i ≠ 0 := fun i h0 => by
    have := hdiag i
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hord : ∀ i, ordL (d i) = y i := fun i => by
    simp only [d]
    rw [GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (Units.ne_zero _) (ht0 i),
      GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow, hϖ,
      GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_congr (b := (1 : w.adicCompletion E)) (by rw [hdiag i, map_one]),
      GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_one]
    simp
  have hinj : Function.Injective d := fun i j hij => hy.injective (by rw [← hord i, ← hord j, hij])
  have hmat : (m⁻¹ * δ * m : GLw n w).val = Matrix.diagonal d := by
    rw [h, Units.val_mul, tdiag, GlobalTheory.SmGL.val_diagT]
    ext i j
    rw [Matrix.diagonal_mul]
    by_cases hij : i = j
    · subst hij
      simp [d]
    · simp [hoff i j hij, hij]
  have hcp : δ.val.charpoly = ∏ i, (X - C (d i)) := by
    have h1 : (m⁻¹ * δ * m : GLw n w).val.charpoly = δ.val.charpoly := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
      exact Matrix.charpoly_units_conj' m δ.val
    rw [← h1, hmat, Matrix.charpoly_diagonal]
  rw [hcp]
  exact separable_prod_X_sub_C_iff.2 hinj

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.dcosSep :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.DcosSep :=
  _root_.UpperTheory.Reformulated.B.DoubleCosetSeparation.dcosSep
