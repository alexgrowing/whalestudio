import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.strictNormal :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E) (q : ℕ), Cyc σ q → ∀ t t' : Fin n → Eˣ, Strict t → Strict t' → ∀ x : GL (Fin n) E,
      x⁻¹ * diagT E (Fin n) t * sg σ x = diagT E (Fin n) t' → ∃ s : Fin n → Eˣ, x = diagT E (Fin n) s := by
  intro E _ _ _ _ n σ q hσ t t' ht ht' x hx
  have hd : ∀ s : Fin n → Eˣ, (diagT E (Fin n) s : Matrix (Fin n) (Fin n) E) = diagonal (fun a => (s a : E)) :=
    fun _ => val_diagT ..
  have h1 : diagT E (Fin n) t * sg σ x = x * diagT E (Fin n) t' := by
    rw [← hx]; group

  have key : ∀ i j, (x : Matrix (Fin n) (Fin n) E) i j ≠ 0 →
      valuation E (t i : E) = valuation E (t' j : E) := by
    intro i j hij
    have h2 := congrArg (fun g : GL (Fin n) E => valuation E ((g : Matrix (Fin n) (Fin n) E) i j)) h1
    simp only [Units.val_mul, hd, diagonal_mul, mul_diagonal, map_mul] at h2
    have h3 : (sg σ x : Matrix (Fin n) (Fin n) E) i j = σ ((x : Matrix (Fin n) (Fin n) E) i j) := rfl
    rw [h3, hσ.isom, mul_comm] at h2
    exact mul_left_cancel₀ ((Valuation.ne_zero_iff _).2 hij) h2
  have hm : StrictMono fun i => valuation E (t i : E) := fun i j h => ht i j h
  have hm' : StrictMono fun i => valuation E (t' i : E) := fun i j h => ht' i j h
  have hdet : (x : Matrix (Fin n) (Fin n) E).det ≠ 0 := GeneralLinearGroup.det_ne_zero x
  obtain ⟨w, hw⟩ : ∃ w : Equiv.Perm (Fin n), ∀ j, (x : Matrix (Fin n) (Fin n) E) (w j) j ≠ 0 := by
    by_contra hcon
    apply hdet
    rw [det_apply]
    refine Finset.sum_eq_zero fun w _ => ?_
    have : ∃ j, (x : Matrix (Fin n) (Fin n) E) (w j) j = 0 := by
      by_contra h
      exact hcon ⟨w, fun j hj => h ⟨j, hj⟩⟩
    obtain ⟨j, hj⟩ := this
    rw [Finset.prod_eq_zero (f := fun i => (x : Matrix (Fin n) (Fin n) E) (w i) i) (Finset.mem_univ j) hj, smul_zero]
  have hwm : StrictMono w := by
    intro a b hab
    apply hm.lt_iff_lt.1
    simp only [key _ _ (hw a), key _ _ (hw b)]
    exact hm' hab
  have hwid : ∀ j, w j = j := by
    intro j
    have := Subsingleton.elim (hwm.orderIsoOfSurjective w w.surjective) (OrderIso.refl _)
    exact congrArg (fun e : Fin n ≃o Fin n => e j) this
  have hdiag : ∀ j, (x : Matrix (Fin n) (Fin n) E) j j ≠ 0 := fun j => by
    have := hw j
    rwa [hwid] at this
  refine ⟨fun j => Units.mk0 _ (hdiag j), Units.ext ?_⟩
  rw [hd]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [diagonal_apply_ne _ hij]
    by_contra hne
    exact hij (hm.injective ((key i j hne).trans (key j j (hdiag j)).symm))
