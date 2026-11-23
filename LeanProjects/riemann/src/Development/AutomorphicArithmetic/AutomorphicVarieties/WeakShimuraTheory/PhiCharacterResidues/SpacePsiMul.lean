import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiPsiEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∃ (ψ : ∀ v : W.Vl l T.L, Fin 4 → Dec (F := T.L) (K.s.A v) →* X.Bˣ), K.IsPsiT X n ψ := by
  intro Ω _ _ _ l _ c D T c' h K X n
  have hmem : ∀ (v : W.Vl l T.L) (g : Dec (F := T.L) (K.s.A v)),
      resLe (Tower.F_le T) (g : G T.L Ω) ∈ (T.fr ∅).Gv (K.e v) := by
    intro v g
    show _ ∈ Dec (T.pl (K.e v))
    have hg : (g : G T.L Ω) ∈ Dec (F := T.L) (T.pl (K.e v)) := K.hA v ▸ g.2
    exact hg
  have hup : ∀ (M N : GradeZeroInterpolatingElement.M4 X.A), IsUp M → IsUp N → ∀ i, (M * N) i i = M i i * N i i := by
    intro M N hM hN i
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · rw [hM i k hlt, zero_mul]
      · rw [hN k i hlt, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hleft : ∀ w, adj (X.P.n w) * X.P.n w = 1 := by
    intro w
    have h1 := (X.pair.low w).1
    simpa [IsGSp] using h1
  have hright : ∀ w, X.P.n w * adj (X.P.n w) = 1 := fun w => mul_eq_one_comm.mp (hleft w)
  have hPmul : ∀ w i, ∀ s ∈ (T.fr ∅).Gv w, ∀ t ∈ (T.fr ∅).Gv w,
      X.P.ψ w i (s * t) = X.P.ψ w i s * X.P.ψ w i t := by
    intro w i s hs t ht
    have key : adj (X.P.n w) * X.P.r (s * t) * X.P.n w
        = (adj (X.P.n w) * X.P.r s * X.P.n w) * (adj (X.P.n w) * X.P.r t * X.P.n w) := by
      rw [map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (X.P.n w) (adj (X.P.n w)), hright w, Matrix.one_mul]
    unfold PD.ψ
    rw [key]
    exact hup _ _ (X.pair.flag w s hs) (X.pair.flag w t ht) i
  have hψmul : ∀ w i, ∀ s ∈ (T.fr ∅).Gv w, ∀ t ∈ (T.fr ∅).Gv w,
      X.ψ w i (s * t) = X.ψ w i s * X.ψ w i t := by
    intro w i s hs t ht
    apply X.inj
    rw [map_mul, X.ψ_map w i _ (mul_mem hs ht), X.ψ_map w i s hs, X.ψ_map w i t ht]
    exact hPmul w i s hs t ht
  have hψone : ∀ w i, X.ψ w i 1 = 1 := by
    intro w i
    apply X.inj
    rw [map_one, X.ψ_map w i 1 (one_mem _)]
    unfold PD.ψ
    rw [map_one, Matrix.mul_one, hleft w, Matrix.one_apply_eq]
  have hψunit : ∀ w i, ∀ s ∈ (T.fr ∅).Gv w, IsUnit (X.ψ w i s) := by
    intro w i s hs
    by_contra hne
    have h0 : IsLocalRing.residue X.B (X.ψ w i s) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hne)
    have hr := X.ψ_red w i s hs
    have hu := ((((T.fr ∅).χ i s).isUnit.map (inc h)).map (IsLocalRing.residue c'.O))
    rw [← hr] at hu
    simp only [res, h0] at hu
    simp at hu
    exact hne hu
  have hsc : ∀ g g' : G T.L Ω, K.sc n (g * g') = K.sc n g * K.sc n g' := by
    intro g g'
    unfold Link.sc
    simp only [map_mul, Units.val_mul, mul_pow]
    ring
  have hsc1 : K.sc n 1 = 1 := by
    unfold Link.sc
    simp
  have hscu : ∀ g : G T.L Ω, IsUnit (K.sc n g) := by
    intro g
    exact (K.κ g).isUnit.mul ((K.β g).isUnit.pow n)
  refine ⟨fun v i => IsUnit.liftRight
    { toFun := fun g => algebraMap c'.O X.B (K.sc n (g : G T.L Ω)) *
        X.ψ (K.e v) i (resLe (Tower.F_le T) (g : G T.L Ω))
      map_one' := by
        simp only [OneMemClass.coe_one, map_one, hsc1]
        rw [one_mul]
        exact hψone (K.e v) i
      map_mul' := by
        intro g g'
        simp only [Subgroup.coe_mul]
        rw [map_mul (resLe (Tower.F_le T)), hψmul _ _ _ (hmem v g) _ (hmem v g'), hsc, map_mul]
        ring }
    (fun g => ((hscu (g : G T.L Ω)).map (algebraMap c'.O X.B)).mul (hψunit _ _ _ (hmem v g))), ?_⟩
  intro v i g
  rfl
