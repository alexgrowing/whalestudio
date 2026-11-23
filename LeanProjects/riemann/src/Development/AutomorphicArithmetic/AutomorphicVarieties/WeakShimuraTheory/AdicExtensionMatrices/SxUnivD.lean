import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.UnivChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.UnivRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.CoprodOpt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.NearMap

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxUnivD :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ}, Φ.Std l a → ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (D : RD Φ R), Φ.RUniv a D := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hS
  haveI := Φ.fin
  haveI := hS.char
  obtain ⟨A, _, _, _, r, hr⟩ := UpperTheory.V.Ws.sxUnivRep l hS
  have hC : ∀ t : Φ.ι × Fin 4, ∃ (B : Type) (_ : CommRing B) (_ : Algebra Λ B) (_ : IsCO Λ B)
      (ψ : Φ.Gv t.1 →* B), AdicCont (maximalIdeal B) ψ ∧
        (∀ s : Φ.Gv t.1, res Λ B (ψ s) = residue Λ (a ((Φ.χ t.2) s))) ∧
        ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (ψ' : Φ.Gv t.1 →* R'),
          AdicCont (maximalIdeal R') ψ' →
            (∀ s : Φ.Gv t.1, res Λ R' (ψ' s) = residue Λ (a ((Φ.χ t.2) s))) →
              ∃! f : B →ₐ[Λ] R', ∀ s, f (ψ s) = ψ' s := by
    intro t
    haveI : CompactSpace (Φ.Gv t.1) := isCompact_iff_compactSpace.mp (hS.closed t.1).isCompact
    let χ : Φ.Gv t.1 →* ResidueField Λ :=
      ((residue Λ).comp a).toMonoidHom.comp ((Units.coeHom O).comp ((Φ.χ t.2).comp (Φ.Gv t.1).subtype))
    have hlc : IsLocallyConstant χ :=
      (hS.ok.lc t.2).comp_continuous continuous_subtype_val
    obtain ⟨B, i1, i2, i3, ψ, h1, h2, h3⟩ := UpperTheory.V.Ws.sxUnivChar l χ (hS.phiv t.1) hlc
    exact ⟨B, i1, i2, i3, ψ, h1, h2, fun R' _ _ _ ψ' h h' => h3 R' ψ' h h'⟩
  choose B iB1 iB2 iB3 ψ hψ1 hψ2 hψ3 using hC
  obtain ⟨R, _, _, _, ι0, j, hU⟩ := @UpperTheory.V.Ws.sxCoprodOpt Λ _ _ _ _ (Φ.ι × Fin 4) _ A _ _ _ B iB1 iB2 iB3
  have hmax : ∀ t (x : B t), x ∈ maximalIdeal (B t) ↔ j t x ∈ maximalIdeal R := by
    intro t x
    rw [← res_eq_zero_iff Λ, ← res_eq_zero_iff Λ, res_map]
  let D : RD Φ R :=
    { r := (Lift.map ι0 r).hom
      ψ := fun v k => (j (v, k) : B (v, k) →+* R).toMonoidHom.comp (ψ (v, k)) }
  refine ⟨R, inferInstance, inferInstance, inferInstance, D, ?_, ?_⟩
  · refine ⟨(hr R).1 ι0, fun i k => (Lift.map ι0 r).cont i k, fun v k => ?_, fun g k => ?_,
      fun g i k hik _ => ?_, fun v k s => ?_⟩
    · exact UpperTheory.V.Ws.adicCont_map (j (v, k) : B (v, k) →+* R) (J := maximalIdeal R)
        (fun x hx => Ideal.mem_comap.mpr ((hmax _ x).mp hx)) (hψ1 (v, k))
    · have := (Lift.map ι0 r).red g k k
      simp [UpperTheory.V.Ws.Fr.splitRD, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, UpperTheory.V.GradeZeroInterpolatingElement.diagRep] at this
      exact this
    · apply (res_eq_zero_iff Λ R _).mp
      have := (Lift.map ι0 r).red g i k
      simp [UpperTheory.V.Ws.Fr.splitRD, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, UpperTheory.V.GradeZeroInterpolatingElement.diagRep, Matrix.diagonal_apply_ne _ hik] at this
      exact this
    · show res Λ R (j (v, k) (ψ (v, k) s)) = _
      rw [res_map]
      exact hψ2 (v, k) s
  · intro R' _ _ _ D' hD'
    have hred : ∀ g i k, res Λ R' (D'.r g i k) = (Φ.splitRD ((residue Λ).comp a)).r g i k := by
      intro g i k
      by_cases hik : i = k
      · subst hik
        simp [UpperTheory.V.Ws.Fr.splitRD, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, UpperTheory.V.GradeZeroInterpolatingElement.diagRep]
        exact hD'.diag g i
      · simp [UpperTheory.V.Ws.Fr.splitRD, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, UpperTheory.V.GradeZeroInterpolatingElement.diagRep, Matrix.diagonal_apply_ne _ hik]
        exact (res_eq_zero_iff Λ R' _).mpr (hD'.off g i k hik (by simp))
    let r' : Lift Λ (Φ.splitRD ((residue Λ).comp a)).r R' := ⟨D'.r, hD'.cont, hred⟩
    obtain ⟨fa, hfa, hfau⟩ := (hr R').2 r' hD'.rep
    have hft : ∀ t, ∃! f : B t →ₐ[Λ] R', ∀ s, f (ψ t s) = D'.ψ t.1 t.2 s :=
      fun t => hψ3 t R' (D'.ψ t.1 t.2) (hD'.contψ t.1 t.2) (hD'.redψ t.1 t.2)
    choose f hf hfu using hft
    obtain ⟨g, ⟨hg1, hg2⟩, hgu⟩ := hU R' fa f
    refine ⟨g, ?_, ?_⟩
    · apply RD.ext
      · have h1 := congrArg Lift.hom hfa
        rw [← hg1] at h1
        ext x i k
        have h2 := congrArg (fun F => F x i k) h1
        simpa [RD.map, Lift.map, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, D, r'] using h2
      · funext v k
        ext s
        show g (j (v, k) (ψ (v, k) s)) = D'.ψ v k s
        rw [← AlgHom.comp_apply, hg2 (v, k), hf]
    · intro f' hf'
      apply hgu
      refine ⟨?_, fun t => ?_⟩
      · apply hfau
        apply Lift.ext
        ext x i k
        have h2 := congrArg (fun E => E.r x i k) hf'
        simpa [RD.map, Lift.map, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, D, r'] using h2
      · apply hfu t
        intro s
        have h2 := congrArg (fun E => E.ψ t.1 t.2 s) hf'
        simpa [RD.map, D] using h2
