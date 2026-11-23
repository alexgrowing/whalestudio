import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.TriIwa
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.ExtFg
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

theorem UpperTheory.V.Ws.Pp.triSpec :
    ∀ {ι A F K : Type} [CommRing A] [Field F] [Field K] [IsAlgClosed K] (M : ι → M4 A) (P : ι → Fin 4 → A[X]) (φ : A →+* F) (f : A →+* K) (h : M4 F), RingHom.ker φ ≤ RingHom.ker f → SpTri M P φ h → ∃ h' : M4 K, SpTri M P f h' := by
  intro ι A F K _ _ _ _ M P φ f h hf H
  classical
  haveI := RingHom.ker_isPrime f
  have hu : ∀ y : (RingHom.ker f).primeCompl, IsUnit (φ y) := fun y => Ne.isUnit fun e => y.2 (hf e)
  obtain ⟨V, hV, hl⟩ := IsLocalRing.exists_factor_valuationRing
    (IsLocalization.lift (S := Localization.AtPrime (RingHom.ker f)) hu)
  let g₀ : Localization.AtPrime (RingHom.ker f) →+* V := (IsLocalization.lift hu).codRestrict V.toSubring hV
  haveI : IsLocalHom g₀ := hl
  let g : A →+* V := g₀.comp (algebraMap _ _)
  have hg : V.subtype.comp g = φ := RingHom.ext fun a => IsLocalization.lift_eq hu a
  have hk : RingHom.ker f = (maximalIdeal V).comap g := by
    ext a
    rw [Ideal.mem_comap,
      ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime (RingHom.ker f)) (RingHom.ker f) a,
      mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact (isUnit_map_iff g₀ _).not.symm
  obtain ⟨k, hk'⟩ := triIwa V M P g h (by rw [hg]; exact H)
  letI : Algebra A V := g.toAlgebra
  let s : Set V := Set.range (fun p : Fin 4 × Fin 4 => k p.1 p.2)
  have hs : s.Finite := Set.finite_range _
  let C := Algebra.adjoin A s
  haveI : Algebra.FiniteType A C := (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
  let Y : M4 C := fun a b => ⟨k a b, Algebra.subset_adjoin ⟨(a, b), rfl⟩⟩
  have H0 : SpTri M P (algebraMap A C) Y := SpTri.of_map C.val.toRingHom Subtype.val_injective hk'
  let q : Ideal C := (maximalIdeal V).comap C.val.toRingHom
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨ψ, hψ⟩ := extFg q f (by rw [hk]; rfl)
  exact ⟨Y.map ψ, hψ ▸ H0.map ψ⟩
