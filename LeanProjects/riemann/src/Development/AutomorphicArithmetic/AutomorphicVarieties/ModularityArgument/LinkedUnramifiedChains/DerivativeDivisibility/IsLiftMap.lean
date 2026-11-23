import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.AbsGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSqz

noncomputable section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.Fr

namespace UpperTheory.V.J

section Lift

variable {O R C : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
  [CommRing C] [Algebra O C] [IsCO O C]

private theorem map_max_le (f : R →ₐ[O] C) :
    (maximalIdeal R).map (f : R →+* C) ≤ maximalIdeal C := by
  refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
  show f a ∈ maximalIdeal C
  rw [← res_eq_zero_iff O C, res_map, res_eq_zero_iff]
  exact ha

private theorem adic_map {Γ : Type} [TopologicalSpace Γ] (f : R →ₐ[O] C) {u : Γ → R}
    (hu : AdicCont (maximalIdeal R) u) : AdicCont (maximalIdeal C) fun g => f (u g) := by
  intro N
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal C ^ N).comap (f : R →+* C) := by
    refine Ideal.map_le_iff_le_comap.1 ?_
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (map_max_le f) N
  exact (hu N).comp (Ideal.quotientMap (maximalIdeal C ^ N) (f : R →+* C) hle)

variable {l : ℕ} [Fact l.Prime] {F : Frame l (ResidueField O)} {n : ℕ}

private theorem isLift_map (f : R →ₐ[O] C) {ρ : NRep F n R} (h : UpperTheory.V.Fr.IsLift O ρ) :
    UpperTheory.V.Fr.IsLift O (ρ.map (f : R →+* C)) := by
  obtain ⟨hc, hb, hd⟩ := h
  have hres : ((res O C : C →ₐ[O] ResidueField O) : C →+* ResidueField O).comp (f : R →+* C) =
      ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O) := by
    ext x
    exact res_map f x
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, ?_, ?_⟩
  · exact adic_map f (hc.1 i j)
  · exact adic_map f (hc.2 v i)
  · rw [NRep.map_map, hres]
    exact hb
  · rw [NRep.map_map, hres]
    exact hd

end Lift

theorem det : Det := by
  intro l _ O _ _ _ _ F n S ξ D hD hr hψ
  haveI hc : IsAdicComplete (maximalIdeal O) O := UpperTheory.V.Fr.IsCoef.complete (l := l)
  haveI hn : IsNoetherianRing O := PrincipalIdealRing.isNoetherianRing
  haveI : IsCO O O := IsCO.self O
  haveI : IsCO O (TrivSqZeroExt O O) := co_sqz O O O (fun c => rfl)
  obtain ⟨y, hy⟩ := (der_hom O S.R O O ξ D).1 ⟨D, hD, rfl⟩
  let z : S.R →ₐ[O] TrivSqZeroExt O O := (TrivSqZeroExt.inlAlgHom O O O).comp ξ
  have key : ∀ a : S.R, D a = 0 → y a = z a := fun a ha =>
    TrivSqZeroExt.ext (hy a).1 (by rw [(hy a).2, ha]; rfl)
  have hmap : NRep.map (y : S.R →+* TrivSqZeroExt O O) S.ρ =
      NRep.map (z : S.R →+* TrivSqZeroExt O O) S.ρ := by
    apply NRep.ext
    · refine MonoidHom.ext fun g => Matrix.ext fun i j => ?_
      exact key _ (hr g i j)
    · funext v i
      refine MonoidHom.ext fun g => Units.ext ?_
      exact key _ (hψ v i g)
  obtain ⟨f, _, huniq⟩ := S.univ (TrivSqZeroExt O O) _ (isLift_map z S.lift)
  have e : y = z := (huniq y hmap).trans (huniq z rfl).symm
  ext a
  have h2 := (hy a).2
  rw [e] at h2
  rw [← h2]
  rfl

end UpperTheory.V.J

end
