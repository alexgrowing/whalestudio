import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem card_one_of {R N : Type} [Ring R] [AddCommGroup N] [Module R N] (P : Submodule R N)
    (h : ∀ x ∈ P, x = 0) : Nat.card P = 1 := by
  haveI : Subsingleton P := ⟨fun a b => Subtype.ext ((h a a.2).trans (h b b.2).symm)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩

theorem UpperTheory.V.Ws.Bl.gwIneq :
    GlobalFiniteness → GreenbergWiles → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), 0 < r → l ≠ 2 → ContainsAbove S l → ContAction ρ →
          ∀ c : G ℚ Ω, IsCC c → (∀ m, ρ (toGS Ω _ c) m = -m) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) →
          ∀ (v0 : S) (s : G ℚ Ω), s ∈ Dec (F := ℚ) (Av v0) → cycZ ℚ Ω l s = 1 → (Function.Bijective fun x => ρ (toGS Ω _ s) x - x) →
          ∀ L : LocCond ρ (locFam S Av), (∀ v, v ≠ v0 → Nat.card (H0 (ρ.comp (locFam S Av v))) ≤ Nat.card (L v)) →
          Nat.card (L v0) ≤ Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := by
  intro hGF hGW Ω _ _ _ l _ r M _ _ _ _ _ S ρ hr hl2 hS hρ c hc hcneg Av hAv v0 s hsD hsz hsbij L hL
  have hcop : Nat.Coprime 2 (l ^ r) :=
    Nat.Coprime.pow_right r ((Nat.coprime_primes Nat.prime_two (Fact.out)).mpr (Ne.symm hl2))
  have hinv : ∀ m : M, m = -m → m = 0 := by
    intro m hm
    set u := ZMod.unitOfCoprime 2 hcop
    have hu : (u : ZMod (l ^ r)) = 2 := by simp [u]
    have h2 : (2 : ZMod (l ^ r)) • m = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hm]
      exact add_neg_cancel m
    calc m = ((u⁻¹ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) • ((u : ZMod (l ^ r)) • m) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = 0 := by rw [hu, h2, smul_zero]
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := r) hS
  have hcc : ∀ w : InfinitePlace ℚ, w.IsReal → IsCCAt w c := by
    intro w _
    obtain ⟨j, hj⟩ := hc
    exact ⟨j, hj, Subsingleton.elim _ _⟩
  have key := hGW ℚ Ω l r M S ρ hr hl2 hS hρ μ hμ Av hAv (fun _ => c) hcc L
  have hμs : μ (toGS Ω _ s) = 1 := by
    have h := congrArg (fun f => f s) hμ
    simp only [MonoidHom.comp_apply] at h
    rw [h]
    simp [cycMod, hsz]
  have htw : Nat.card (H0 (twDual μ ρ)) = 1 := by
    refine card_one_of _ (fun φ hφ => ?_)
    have hfix := (mem_riemannRochSpace_iff_regularAt_everywhere _ φ).mp hφ (toGS Ω _ s)
    apply TDual.ext
    intro m
    obtain ⟨x, rfl⟩ := hsbij.2 m
    have hx : φ (ρ (toGS Ω _ s) x) = φ x := by
      have h := congrArg (fun ψ : TDual (ZMod (l ^ r)) M => ψ (ρ (toGS Ω _ s) x)) hfix
      simp only [twDual_apply, hμs, Units.val_one, one_mul] at h
      rw [← h, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hsub : (φ : Module.Dual (ZMod (l ^ r)) M) (ρ (toGS Ω _ s) x - x) =
        (φ : Module.Dual (ZMod (l ^ r)) M) (ρ (toGS Ω _ s) x) - (φ : Module.Dual (ZMod (l ^ r)) M) x :=
      LinearMap.map_sub _ _ _
    show φ (ρ (toGS Ω _ s) x - x) = 0
    exact hsub.trans (by erw [hx]; exact sub_self _)
  have harch : archH0Card S ρ (fun _ => c) = 1 := by
    have h0 : InfinitePlace.nrComplexPlaces ℚ = 0 := by simp
    unfold archH0Card
    rw [h0, pow_zero, mul_one]
    refine Finset.prod_eq_one (fun w _ => ?_)
    haveI : Subsingleton {m : M // ρ (toGS Ω _ c) m = m} :=
      ⟨fun a b => Subtype.ext (by
        have ha := hinv a.1 (by rw [← hcneg a.1, a.2])
        have hb := hinv b.1 (by rw [← hcneg b.1, b.2])
        rw [ha, hb])⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨⟨0, map_zero _⟩⟩⟩
  have hv0 : Nat.card (H0 (ρ.comp (locFam S Av v0))) = 1 := by
    refine card_one_of _ (fun m hm => ?_)
    have hfix := (mem_riemannRochSpace_iff_regularAt_everywhere _ m).mp hm ⟨s, hsD⟩
    have hfix' : ρ (toGS Ω _ s) m = m := hfix
    apply hsbij.1
    show ρ (toGS Ω _ s) m - m = ρ (toGS Ω _ s) 0 - 0
    rw [hfix', sub_self, map_zero, sub_self]
  classical
  rw [htw, harch, mul_one, mul_one] at key
  obtain ⟨-, hH1, -, -⟩ := hGF ℚ Ω l r M S ρ hr hS hρ
  have hSelpos : 0 < Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := Nat.card_pos
  have hH0pos : ∀ v, 0 < Nat.card (H0 (ρ.comp (locFam S Av v))) := fun v => Nat.card_pos
  have hP := Finset.mul_prod_erase Finset.univ (fun v => Nat.card (H0 (ρ.comp (locFam S Av v)))) (Finset.mem_univ v0)
  have hQ := Finset.mul_prod_erase Finset.univ (fun v => Nat.card (L v)) (Finset.mem_univ v0)
  simp only at hP hQ
  rw [hv0, one_mul] at hP
  set P' := ∏ v ∈ Finset.univ.erase v0, Nat.card (H0 (ρ.comp (locFam S Av v)))
  set Q' := ∏ v ∈ Finset.univ.erase v0, Nat.card (L v)
  have hP'pos : 0 < P' := Finset.prod_pos (fun v _ => hH0pos v)
  have hPQ : P' ≤ Q' := Finset.prod_le_prod (fun v _ => Nat.zero_le _)
    (fun v hv => hL v (Finset.ne_of_mem_erase hv))
  rw [← hP, ← hQ] at key
  set a := Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L)
  set b := Nat.card (Sel (twDual μ ρ) (locFam S Av) _ (perpCond μ ρ (locFam S Av) _ L))
  set h0 := Nat.card (H0 ρ)
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · rw [hb, zero_mul, zero_mul] at key
      exact absurd key (Nat.mul_pos hSelpos hP'pos).ne'
    · exact hb
  have hh0 : 0 < h0 := Nat.card_pos
  have h1 : Nat.card (L v0) * Q' ≤ a * P' := by
    rw [key]
    calc Nat.card (L v0) * Q' ≤ (b * h0) * (Nat.card (L v0) * Q') :=
          Nat.le_mul_of_pos_left _ (Nat.mul_pos hbpos hh0)
      _ = _ := rfl
  have h2 : Nat.card (L v0) * P' ≤ a * P' :=
    le_trans (Nat.mul_le_mul_left _ hPQ) h1
  exact Nat.le_of_mul_le_mul_right h2 hP'pos
