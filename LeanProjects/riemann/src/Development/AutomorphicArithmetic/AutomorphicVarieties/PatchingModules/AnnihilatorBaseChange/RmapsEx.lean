import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SinfExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.TupNOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.LamComap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpoCo

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem rm_ext {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    {D q n : ℕ} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
    (s : Sinf O Unit D q n →ₐ[O] R) (ρ : R →ₐ[O] R') (g : Sinf O Unit D q n →ₐ[O] R')
    (ha : ∀ k, s (MvPowerSeries.C (MvPowerSeries.X k)) ∈ maximalIdeal R) (hy : ∀ p, s (MvPowerSeries.X p) ∈ maximalIdeal R)
    (ea : ∀ k, g (MvPowerSeries.C (MvPowerSeries.X k)) = ρ (s (MvPowerSeries.C (MvPowerSeries.X k))))
    (ey : ∀ p, g (MvPowerSeries.X p) = ρ (s (MvPowerSeries.X p))) (z : Sinf O Unit D q n) : ρ (s z) = g z := by
  have hm : ∀ x ∈ maximalIdeal R, ρ x ∈ maximalIdeal R' := by
    intro x hx
    rw [← res_eq_zero_iff O R', res_map, res_eq_zero_iff O R]
    exact hx
  obtain ⟨f, -, huniq⟩ := sinfExt O D q n R' (fun k => g (MvPowerSeries.C (MvPowerSeries.X k)))
    (fun p => g (MvPowerSeries.X p))
    (fun k => by rw [ea]; exact hm _ (ha k)) (fun p => by rw [ey]; exact hm _ (hy p))
  have h1 : ρ.comp s = f := huniq _ ⟨fun k => (ea k).symm, fun p => (ey p).symm⟩
  have h2 : g = f := huniq _ ⟨fun _ => rfl, fun _ => rfl⟩
  exact (DFunLike.congr_fun (h1.trans h2.symm) z : _)

private noncomputable def rm_cc (O : Type) [CommRing O] (D q n : ℕ) : Sinf O Unit D q n →ₐ[O] abelian₂ O Unit D :=
  { (MvPowerSeries.constantCoeff : Sinf O Unit D q n →+* abelian₂ O Unit D) with
    commutes' := fun c => by
      rw [MvPowerSeries.algebraMap_apply]
      exact MvPowerSeries.constantCoeff_C _ }

theorem UpperTheory.V.Pa.Core.rmapsEx :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A), Adapted T (r := r) → Nonempty (RMaps W) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W hT
  haveI : IsAdicComplete (maximalIdeal O) O := IsCoef.complete (l := l)
  have hw : ∀ k : Fin D, (algebraMap O W.R) (A.b.wt.c k) *
      ↑((W.t.ψ (A.b.wt.v k) (A.b.wt.i k)) (A.b.wt.γ k)) - 1 ∈ maximalIdeal W.R := by
    intro k
    rw [← res_eq_zero_iff O W.R, map_sub, map_mul, AlgHom.commutes, map_one,
      (W.t.psi _ _).red, ResidueField.algebraMap_eq, A.b.wt_res, sub_self]
  obtain ⟨s, ⟨hsa, hsy⟩, -⟩ := sinfExt O D T.q n W.R
    (Sum.elim (fun _ => W.t.s) (fun k => (algebraMap O W.R) (A.b.wt.c k) *
      ↑((W.t.ψ (A.b.wt.v k) (A.b.wt.i k)) (A.b.wt.γ k)) - 1))
    (fun p => W.t.y p.1 p.2)
    (by rintro (_ | k); exacts [W.t.s_mem, hw k]) (fun p => W.t.y_mem _ _)
  have hsm : ∀ k, s (MvPowerSeries.C (MvPowerSeries.X k)) ∈ maximalIdeal W.R := by
    rintro (_ | k)
    · rw [hsa]; exact W.t.s_mem
    · rw [hsa]; exact hw k
  have hym : ∀ p, s (MvPowerSeries.X p) ∈ maximalIdeal W.R := fun p => by
    rw [hsy]; exact W.t.y_mem _ _
  have hρ : ∀ N, ∃ f : W.R →ₐ[O] (A.A N).R, W.t.Maps f.toRingHom ((A.A N).p.D.comap (πN0 Λ N))
      (A.A N).p.ψ ((A.A N).s (MvPowerSeries.C (MvPowerSeries.X (Sum.inl ())))) (A.A N).U
      (fun j i => (A.A N).s (MvPowerSeries.X (j, i))) := by
    intro N
    obtain ⟨t, hD, hψ, hs, hU, hy⟩ := tupN l L G0 T Λ n O r B u J D A hT N
    obtain ⟨f, hf, -⟩ := W.univ _ t
    rw [hD, hψ, hs, hU, hy] at hf
    exact ⟨f, hf⟩
  choose ρ hρ using hρ
  haveI : IsCO O (Spo A) := (spoCo l L G0 T Λ n O r B u J D A hT).1.1
  obtain ⟨t, hD, hψ, hs, hU, hy⟩ := tupPi l L G0 T Λ n O r B u J D A
  obtain ⟨π, hπ, -⟩ := W.univ _ t
  rw [hD, hψ, hs, hU, hy] at hπ
  refine ⟨⟨s, hsa (Sum.inl ()), fun k => hsa (Sum.inr k), fun j i => hsy (j, i), ρ, hρ, ?_, π, hπ, ?_⟩⟩
  · intro N z
    refine rm_ext s (ρ N) (A.A N).s hsm hym ?_ ?_ z
    · rintro (_ | k)
      · rw [hsa]; exact (hρ N).2.2.1.symm
      · rw [hsa, Sum.elim_inr, (A.A N).s_w k, map_sub, map_mul, AlgHom.commutes, map_one]
        have := congrArg (fun χ => ((χ (A.b.wt.γ k) : (A.A N).Rˣ) : (A.A N).R))
          ((hρ N).2.1 (A.b.wt.v k) (A.b.wt.i k))
        simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at this
        rw [← this]
        rfl
    · intro p
      rw [hsy]
      exact ((hρ N).2.2.2.2 p.1 p.2).symm
  · intro z
    refine rm_ext s π ((IsScalarTower.toAlgHom O B (Spo A)).comp (A.b.lam.comp (rm_cc O D T.q n)))
      hsm hym ?_ ?_ z
    · rintro (_ | k)
      · rw [hsa]
        refine Eq.trans ?_ hπ.2.2.1.symm
        simp [rm_cc, MvPowerSeries.constantCoeff_C]
      · rw [hsa, Sum.elim_inr, map_sub, map_mul, AlgHom.commutes, map_one]
        have := congrArg (fun χ => ((χ (A.b.wt.γ k) : (Spo A)ˣ) : Spo A))
          (hπ.2.1 (A.b.wt.v k) (A.b.wt.i k))
        simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at this
        change algebraMap B (Spo A) (A.b.lam (MvPowerSeries.constantCoeff
          (MvPowerSeries.C (MvPowerSeries.X (Sum.inr k))))) = _
        rw [MvPowerSeries.constantCoeff_C, A.b.segmentWeightExponent, map_sub, map_mul, map_one,
          ← IsScalarTower.algebraMap_apply]
        erw [this]
    · intro p
      rw [hsy]
      refine Eq.trans ?_ (hπ.2.2.2.2 p.1 p.2).symm
      simp [rm_cc, MvPowerSeries.constantCoeff_X]
