import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplCo
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplDvr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem ooEx_co (O : Type) [CommRing O] [IsLocalRing O] (K : Type) [Field K] [Algebra O K]
    (h : Function.Surjective (algebraMap O K)) : IsCO O K := by
  refine { complete := ?_, isLocalHom := ?_, res_surj := ?_ }
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  · refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ maximalIdeal O := (IsLocalRing.mem_maximalIdeal a).mpr hna
    have hk : RingHom.ker (algebraMap O K) = maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ h)
    rw [← hk, RingHom.mem_ker] at hm
    rw [hm] at ha
    exact not_isUnit_zero ha
  · intro x
    obtain ⟨a, rfl⟩ := h x
    exact ⟨a, by simp⟩

private theorem ooEx_ker (O : Type) [CommRing O] [IsLocalRing O] (K : Type) [Field K] [Algebra O K]
    (h : Function.Surjective (algebraMap O K)) (π : O) (hπ : maximalIdeal O = Ideal.span {π}) :
    RingHom.ker (PowerSeries.map (algebraMap O K)) = Ideal.span {PowerSeries.C π} := by
  have hk : RingHom.ker (algebraMap O K) = maximalIdeal O :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ h)
  have hπ0 : algebraMap O K π = 0 := by
    rw [← RingHom.mem_ker, hk, hπ]
    exact Ideal.mem_span_singleton_self π
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hx
    have hc : ∀ n, ∃ c, PowerSeries.coeff n x = π * c := by
      intro n
      have h1 : algebraMap O K (PowerSeries.coeff n x) = 0 := by
        have := congrArg (PowerSeries.coeff n) hx
        simpa using this
      have h2 : PowerSeries.coeff n x ∈ maximalIdeal O := by
        rw [← hk, RingHom.mem_ker]
        exact h1
      rw [hπ, Ideal.mem_span_singleton] at h2
      exact h2
    choose c hc using hc
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    simp [PowerSeries.coeff_C_mul, hc]
  · rintro ⟨y, rfl⟩
    rw [map_mul, PowerSeries.map_C, hπ0, map_zero, zero_mul]

private theorem ooEx_ev (K O B : Type) [Field K] [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra O K] [CommRing B] [Algebra O B] [IsCO O B]
    (f : B →ₐ[O] PowerSeries K) (s : B) (h : Function.Surjective (algebraMap O K)) (hs : f s = PowerSeries.X) :
    ∃ F : PowerSeries O →+* B, (∀ c : O, F (PowerSeries.C c) = algebraMap O B c) ∧ F PowerSeries.X = s ∧
      ∀ x, f (F x) = PowerSeries.map (algebraMap O K) x := by
  haveI hOO : IsCO O O :=
    { complete := inferInstance
      isLocalHom := ⟨fun a h => by simpa using h⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hK : IsCO O K := ooEx_co O K h
  haveI hPK : IsCO O (MvPowerSeries Unit K) := co_mvps O K Unit
  have hsm : s ∈ maximalIdeal B := by
    by_contra hns
    have hu : IsUnit s := by
      by_contra h'
      exact hns ((IsLocalRing.mem_maximalIdeal s).mpr h')
    have hX : IsUnit (PowerSeries.X : PowerSeries K) := hs ▸ hu.map f
    rw [PowerSeries.isUnit_iff_constantCoeff] at hX
    simp at hX
  obtain ⟨G, ⟨hGC, hGX⟩, -⟩ := co_ev O O B Unit (Algebra.ofId O B) (fun _ => s) (fun _ => hsm)
  refine ⟨G.toRingHom, ?_, ?_, ?_⟩
  · intro c
    exact hGC c
  · exact hGX ()
  · let M : MvPowerSeries Unit O →ₐ[O] MvPowerSeries Unit K :=
      { MvPowerSeries.map (algebraMap O K) with
        commutes' := fun c => by
          simp only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
          exact MvPowerSeries.map_C _ _ }
    have hXm : MvPowerSeries.X () ∈ maximalIdeal (MvPowerSeries Unit K) := by
      refine (IsLocalRing.mem_maximalIdeal _).mpr ?_
      intro hu
      rw [MvPowerSeries.isUnit_iff_constantCoeff] at hu
      simp at hu
    obtain ⟨H, -, hU⟩ := co_ev O O (MvPowerSeries Unit K) Unit (Algebra.ofId O _)
      (fun _ => MvPowerSeries.X ()) (fun _ => hXm)
    have e1 : (f.comp G : MvPowerSeries Unit O →ₐ[O] MvPowerSeries Unit K) = H := by
      refine hU _ ⟨fun x => ?_, fun u => ?_⟩
      · simp [hGC]
      · simp only [AlgHom.comp_apply, hGX, hs]
        rfl
    have e2 : M = H := by
      refine hU _ ⟨fun x => ?_, fun u => ?_⟩
      · simp [M, MvPowerSeries.algebraMap_apply]
      · simp [M]
    intro x
    have := congrArg (fun φ : MvPowerSeries Unit O →ₐ[O] MvPowerSeries Unit K => φ x) (e1.trans e2.symm)
    exact this

theorem UpperTheory.V.Pa.ooEx :
    ∀ (K O B Bh : Type) [Field K] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite K] [Algebra O K] [CommRing B] [Algebra O B] [IsCO O B] [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] (f : B →ₐ[O] PowerSeries K) (s : B) (rF : Bh →+* FractionRing (PowerSeries K)), Function.Surjective (algebraMap O K) → f s = PowerSeries.X → IsCplAt B (RingHom.ker f) Bh → (∀ b, rF (algebraMap B Bh b) = algebraMap (PowerSeries K) _ (f b)) → ∃ (OO : Type) (_ : CommRing OO) (_ : IsDomain OO) (_ : IsDiscreteValuationRing OO) (_ : IsAdicComplete (maximalIdeal OO) OO) (_ : Algebra OO Bh) (_ : IsCO OO Bh), (∀ a : PowerSeries K, ∃ (o : OO) (b : B), algebraMap OO Bh o = algebraMap B Bh b ∧ f b = a) ∧ (∀ c : O, ∃ o : OO, algebraMap OO Bh o = algebraMap B Bh (algebraMap O B c)) ∧ (∃ o : OO, algebraMap OO Bh o = algebraMap B Bh s) ∧ Function.Surjective (rF.comp (algebraMap OO Bh)) := by
  intro K O B Bh _ _ _ _ _ _ _ _ _ _ _ _ _ f s rF hsur hs hcpl hrF
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ := hπirr.maximalIdeal_eq
  obtain ⟨F, hFC, hFX, hfF⟩ := ooEx_ev K O B f s hsur hs
  have hker := ooEx_ker O K hsur π hπ
  have hmapsurj : Function.Surjective (PowerSeries.map (algebraMap O K)) := by
    intro a
    choose g hg using hsur
    refine ⟨PowerSeries.mk (fun n => g (PowerSeries.coeff n a)), ?_⟩
    ext n
    simp [hg]
  obtain ⟨p, hp⟩ : ∃ p : Ideal (PowerSeries O), p = Ideal.span {PowerSeries.C π} := ⟨_, rfl⟩
  rw [← hp] at hker
  haveI hpP : p.IsPrime := by
    rw [← hker]
    exact RingHom.ker_isPrime _
  have hπ0 : PowerSeries.C π ≠ 0 := by
    intro h0
    apply hπirr.ne_zero
    have := congrArg PowerSeries.constantCoeff h0
    simpa using this
  have hprime : Prime (PowerSeries.C π) := (Ideal.span_singleton_prime hπ0).mp (hp ▸ hpP)
  have hcO : IsCplAt (PowerSeries O) p (CplAt (PowerSeries O) p) := isCplAt_cplAt _ p
  obtain ⟨hdom, hdvr, -⟩ := IsCplAt.dvr (PowerSeries O) (PowerSeries.C π) hprime
    (CplAt (PowerSeries O) p) (hp ▸ hcO)
  let φ : PowerSeries O →+* Bh := (algebraMap B Bh).comp F
  have hcomapF : Ideal.comap F (RingHom.ker f) = p := by
    rw [← hker]
    ext x
    simp only [Ideal.mem_comap, RingHom.mem_ker, hfF]
  have hφ : Ideal.comap φ (maximalIdeal Bh) = p := by
    rw [← Ideal.comap_comap, hcpl.comap_eq, hcomapF]
  haveI := hcpl.complete
  obtain ⟨ψ, hψ, -⟩ := IsCplAt.existsUnique_lift (PowerSeries O) p (CplAt (PowerSeries O) p) hcO Bh φ hφ
  letI : Algebra (CplAt (PowerSeries O) p) Bh := ψ.toAlgebra
  letI : Algebra (PowerSeries O) B := F.toAlgebra
  letI : Algebra (PowerSeries O) Bh := φ.toAlgebra
  haveI : IsScalarTower (PowerSeries O) B Bh := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsScalarTower (PowerSeries O) (CplAt (PowerSeries O) p) Bh :=
    IsScalarTower.of_algebraMap_eq (fun x => (RingHom.congr_fun hψ x).symm)
  have hCO : IsCO (CplAt (PowerSeries O) p) Bh := by
    refine IsCplAt.isCO (PowerSeries O) B p (RingHom.ker f) (CplAt (PowerSeries O) p) Bh hcO hcpl ?_ ?_
    · exact hcomapF
    · intro x
      obtain ⟨a, ha⟩ := hmapsurj (f x)
      refine ⟨a, ?_⟩
      rw [RingHom.mem_ker, map_sub]
      show f x - f (F a) = 0
      rw [hfF, ha, sub_self]
  have hkey : ∀ c, rF (ψ (algebraMap (PowerSeries O) (CplAt (PowerSeries O) p) c)) =
      algebraMap (PowerSeries K) _ (PowerSeries.map (algebraMap O K) c) := by
    intro c
    have h1 := RingHom.congr_fun hψ c
    simp only [RingHom.comp_apply] at h1
    rw [h1]
    show rF (algebraMap B Bh (F c)) = _
    rw [hrF, hfF]
  refine ⟨CplAt (PowerSeries O) p, inferInstance, hdom, hdvr, hcO.complete, inferInstance, hCO, ?_, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨c, hc⟩ := hmapsurj a
    exact ⟨algebraMap _ (CplAt (PowerSeries O) p) c, F c, RingHom.congr_fun hψ c, by rw [hfF, hc]⟩
  · intro c
    refine ⟨algebraMap (PowerSeries O) (CplAt (PowerSeries O) p) (PowerSeries.C c), ?_⟩
    refine (RingHom.congr_fun hψ _).trans ?_
    show algebraMap B Bh (F (PowerSeries.C c)) = _
    rw [hFC]
  · refine ⟨algebraMap (PowerSeries O) (CplAt (PowerSeries O) p) PowerSeries.X, ?_⟩
    refine (RingHom.congr_fun hψ _).trans ?_
    show algebraMap B Bh (F PowerSeries.X) = _
    rw [hFX]
  · intro z
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (PowerSeries K) z
    obtain ⟨cx, hcx⟩ := hmapsurj x
    obtain ⟨cy, hcy⟩ := hmapsurj y
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hcyp : cy ∉ p := by
      rw [← hker, RingHom.mem_ker, hcy]
      exact hy0
    have hunit : IsUnit (algebraMap (PowerSeries O) (CplAt (PowerSeries O) p) cy) := by
      by_contra hu
      apply hcyp
      rw [← hcO.comap_eq, Ideal.mem_comap]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hu
    obtain ⟨u, hu⟩ := hunit
    refine ⟨algebraMap (PowerSeries O) (CplAt (PowerSeries O) p) cx * ↑u⁻¹, ?_⟩
    rw [map_mul, map_units_inv, RingHom.comp_apply, RingHom.comp_apply]
    show rF (ψ (algebraMap _ (CplAt (PowerSeries O) p) cx)) * (rF (ψ ↑u))⁻¹ = _
    rw [hu, hkey, hkey, hcx, hcy, div_eq_mul_inv]
