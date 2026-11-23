import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.framed_origin :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) → (∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) →
      ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B), (∀ v, Φ.InH (r0.hom.comp (F.φ v)) B (ρ v)) → ∀ (WB : WPres O X B) (hB : WB.HasOrigin), (∀ v s a b, WB.origin hB ((ρ v).hom s a b) = r0.hom (F.φ v s) a b) →
      ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (i : B →ₐ[O] R) (r : Lift O rbar R) (α : F.T → Matrix ι ι R), IsUnivFramed Φ r0.hom F L ρ i r α → ∀ (W : WPres O X R) (τ : Type) (e : WB.σ ⊕ τ ≃ W.σ), (∀ s, W.z (e (.inl s)) = i (WB.z s)) →
      (∀ t, ∃ a b, (∃ s, W.z (e (.inr t)) = r.hom s a b - algebraMap O R (r0.hom s a b)) ∨ ∃ v, W.z (e (.inr t)) = (α v - 1) a b) →
      ∃ h : W.HasOrigin, r.map (W.origin h) = r0 ∧ (∀ v, (α v).map (W.origin h) = 1) ∧ (W.origin h).comp i = WB.origin hB := by
  intro O _ _ _ _ ι X _ _ _ w Φ h2 Γ _ _ _ rbar r0 hbar hr0 F L hN hLoc hL0 B _ _ _ ρ hρ WB hB hWB R _ _ _ i r α hU W τ e hWl hWr
  have hHH1 : ∀ (S : Type) [CommRing S] [Algebra O S] [IsCO O S], Φ.HH (1 : Matrix ι ι S) := by
    intro S _ _ _
    refine ⟨by simp, fun a b hab => ?_, ?_⟩
    · exact Matrix.one_apply_ne (fun h => hab (h ▸ rfl))
    · simp
  have hF : IsFramed Φ r0.hom F L ρ (WB.origin hB) r0 (fun _ => (1 : Matrix ι ι O)) := by
    refine ⟨fun s => ?_, fun q => hL0 q, fun v => hHH1 O, rfl, fun v s => ?_⟩
    · have hm : (r0.hom s⁻¹).map (algebraMap O O) = r0.hom s⁻¹ := by
        ext a b
        simp
      rw [hm, ← map_mul, mul_inv_cancel, map_one]
      exact hHH1 O
    · ext a b
      simp [Matrix.map_apply, hWB]
  obtain ⟨f, ⟨hfi, hfr, hfα⟩, -⟩ := hU.2 O (WB.origin hB) r0 (fun _ => 1) hF
  have hz : ∀ s, f (W.z s) = 0 := by
    intro s
    obtain ⟨s', rfl⟩ := e.surjective s
    rcases s' with s' | t
    · rw [hWl, ← AlgHom.comp_apply, hfi]
      simp [WPres.z, WPres.origin_π]
    · obtain ⟨a, b, ⟨s, hs⟩ | ⟨v, hv⟩⟩ := hWr t
      · rw [hs, map_sub, AlgHom.commutes, ← Lift.map_hom, hfr]
        simp
      · have hab := congrFun (congrFun (hfα v) a) b
        rw [Matrix.map_apply] at hab
        rw [hv, Matrix.sub_apply, map_sub, hab, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
  have hC : ∀ x : O, (C x : MvPowerSeries W.σ O) = algebraMap O (MvPowerSeries W.σ O) x := by
    intro x
    simp [MvPowerSeries.algebraMap_apply]
  let cc : MvPowerSeries W.σ O →ₐ[O] O :=
    AlgHom.mk (MvPowerSeries.constantCoeff (R := O) (σ := W.σ)) (fun x => by simp [MvPowerSeries.algebraMap_apply])
  have hcc : ∀ g, f (W.π g) = constantCoeff g := by
    obtain ⟨G, -, huniq⟩ := co_ev O O O W.σ (AlgHom.id O O) (fun _ => 0) (fun _ => Ideal.zero_mem _)
    have h1 : f.comp W.π = G := huniq _ ⟨fun x => by
      rw [AlgHom.comp_apply, hC, AlgHom.commutes, AlgHom.commutes]
      rfl, fun s => hz s⟩
    have h2' : cc = G := huniq _ ⟨fun x => by simp [cc], fun s => by simp [cc]⟩
    intro g
    have := congrArg (fun φ => φ g) (h1.trans h2'.symm)
    simpa [cc] using this
  have hO : W.HasOrigin := by
    intro g hg
    rw [← hcc, hg, map_zero]
  have horig : W.origin hO = f := by
    ext x
    obtain ⟨g, rfl⟩ := W.surj x
    rw [WPres.origin_π, hcc]
  refine ⟨hO, ?_, ?_, ?_⟩
  · rw [horig, hfr]
  · intro v
    rw [horig, hfα]
  · rw [horig, hfi]
