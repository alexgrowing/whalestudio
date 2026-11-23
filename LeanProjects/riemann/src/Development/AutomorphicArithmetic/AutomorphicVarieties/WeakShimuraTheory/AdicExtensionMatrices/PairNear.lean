import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PdMapAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicMat
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UpDiagMul

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem up_diag_mul {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) :
    (X * Y) i i = X i i * Y i i :=
  _root_.UpperTheory.Reformulated.B.Qe40.up_diag_mul hX hY i

private theorem low_inv {R : Type} [CommRing R] {n : M4 R} (h : IsLow n) : adj n * n = 1 ∧ n * adj n = 1 := by
  have h1 : adj n * n = 1 := by
    have := h.1
    rwa [IsGSp, one_smul] at this
  exact ⟨h1, mul_eq_one_comm.1 h1⟩

private def grChar {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {R : Type} [CommRing R] {a : O →+* R}
    (Q : PD Φ.ι Γ R) (h : Φ.IsPair a Q) (v : Φ.ι) (i : Fin 4) : Φ.Gv v →* R where
  toFun s := Q.ψ v i s
  map_one' := by
    show (adj (Q.n v) * Q.r 1 * Q.n v) i i = 1
    rw [map_one, mul_one, (low_inv (h.low v)).1, Matrix.one_apply_eq]
  map_mul' s t := by
    show (adj (Q.n v) * Q.r (s * t) * Q.n v) i i =
      (adj (Q.n v) * Q.r s * Q.n v) i i * (adj (Q.n v) * Q.r t * Q.n v) i i
    rw [← up_diag_mul (h.flag v s s.2) (h.flag v t t.2), map_mul]
    have e : adj (Q.n v) * Q.r s * Q.n v * (adj (Q.n v) * Q.r t * Q.n v) =
        adj (Q.n v) * Q.r s * (Q.n v * adj (Q.n v)) * Q.r t * Q.n v := by simp only [mul_assoc]
    rw [e, (low_inv (h.low v)).2]
    simp only [mul_assoc, one_mul]

private def lin (p q : ℤ) : ℤ × ℤ →+ ℤ where
  toFun w := p * w.1 + q * w.2
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add]; ring

private theorem tau_nP : ∀ i j : Fin 4, (-2) * (wt i j).1 + (-1) * (wt i j).2 ≤ 0 → wt i j ∉ nP := by decide

private theorem tau_nM : ∀ i j : Fin 4, (-1) * (wt i j).1 + (-2) * (wt i j).2 ≤ 0 → wt i j ∉ nM := by decide

theorem UpperTheory.V.Ws.sxPairNear :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (c : PD Φ.ι Γ (ResidueField Λ)) (Q : PD Φ.ι Γ R), Φ.IsRes ((residue Λ).comp a) c → Φ.Lifts a c Q → ∃ (τ : ℤ × ℤ →+ ℤ) (D : RD Φ R), Φ.Near a τ D ∧ D.r = Q.r ∧ D.Flags Q.n := by
  intro O Γ _ _ _ Φ Λ _ _ a R _ _ _ c Q hc hQ
  have hr : ∀ g i j, res Λ R (Q.r g i j) = c.r g i j := fun g i j => by
    rw [← hQ.red]; rfl
  have hτ : ∃ τ : ℤ × ℤ →+ ℤ, ∀ g i j, i ≠ j → τ (wt i j) ≤ 0 → c.r g i j = 0 := by
    rcases hc.res.shape with h | h
    · exact ⟨lin (-2) (-1), fun g i j hij ht => h.1 g i j hij (tau_nP i j ht)⟩
    · exact ⟨lin (-1) (-2), fun g i j hij ht => h g i j hij (tau_nM i j ht)⟩
  obtain ⟨τ, hτ⟩ := hτ
  refine ⟨τ, ⟨Q.r, grChar Q hQ.pair⟩, ⟨⟨hQ.pair.mult, hQ.pair.kill, hQ.pair.nrm⟩, hQ.cont, fun v i N => ?_,
    fun g i => ?_, fun g i j hij ht => ?_, fun v i s => ?_⟩, rfl,
    ⟨hQ.pair.low, hQ.pair.flag, fun _ _ _ => rfl, fun v i s hs => hQ.pair.mu v s hs i⟩⟩
  · exact ((sxAdicMat (maximalIdeal R) (fun g => Q.r g) hQ.cont).2 (adj (Q.n v)) (Q.n v) i i N).comp_continuous
      continuous_subtype_val
  · exact (hr g i i).trans (hc.res.diag g i)
  · exact (res_eq_zero_iff Λ R _).1 ((hr g i j).trans (hτ g i j hij ht))
  · have h1 := (sxPdMap ((algebraMap Λ R).comp a) (res Λ R : R →+* ResidueField Λ) Q).1 v i s
    rw [hQ.red] at h1
    exact h1.symm.trans (hc.res.char v s s.2 i)
