import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsInvOpenInside
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace InvOpenInside

lemma mem_range_baseChangeMap {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) (x : X)
    (hx : Disjoint ((Ideal.span {((p : ℕ) : ℤ)}).primeCompl : Set ℤ) (f.base x).asIdeal) :
    x ∈ Set.range (baseChangeMap f (ZLoc p)) := by
  have hr := PrimeSpectrum.localization_comap_range (ZLoc p)
    (Ideal.span {((p : ℕ) : ℤ)}).primeCompl
  obtain ⟨y, hy⟩ : f.base x ∈ Set.range (PrimeSpectrum.comap (algebraMap ℤ (ZLoc p))) := by
    rw [hr]; exact hx
  have e : algebraMap ℤ (ZLoc p) = Int.castRingHom (ZLoc p) := RingHom.ext_int _ _
  have hy' : f.base x = PrimeSpectrum.comap (Int.castRingHom (ZLoc p)) y :=
    hy.symm.trans (congrFun (congrArg PrimeSpectrum.comap e) y)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
    (g := Spec.map (CommRingCat.ofHom (Int.castRingHom (ZLoc p)))) x y hy'
  exact ⟨z, hz⟩

lemma exists_of_isAffineOpen {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) (W : X.Opens)
    (hW : Set.range (baseChangeMap f (ZLoc p)) ⊆ Set.range W.ι) {U : X.Opens}
    (hU : IsAffineOpen U) :
    ∃ s ∈ (Ideal.span {((p : ℕ) : ℤ)}).primeCompl,
      ∀ x ∈ U, x ∉ W → s ∈ (f.base x).asIdeal := by
  set S := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl with hS
  set T : Set (PrimeSpectrum Γ(X, U)) := hU.fromSpec.base ⁻¹' (W : Set X)ᶜ with hTdef
  have hT : IsClosed T := W.isOpen.isClosed_compl.preimage hU.fromSpec.base.hom.continuous
  have hf : ∀ P : Spec Γ(X, U),
      (f.base (hU.fromSpec.base P)).asIdeal = P.asIdeal.comap (Int.castRingHom Γ(X, U)) := by
    intro P
    have h : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (Int.castRingHom Γ(X, U))) :=
      specZIsTerminal.hom_ext _ _
    rw [← Scheme.Hom.comp_apply, h]
    rfl
  have hW' : ∀ x : X, Disjoint (S : Set ℤ) (f.base x).asIdeal → x ∈ W := by
    intro x hx
    have := hW (mem_range_baseChangeMap f p x hx)
    rwa [Scheme.Opens.range_ι] at this
  have hI : ¬ Disjoint (PrimeSpectrum.vanishingIdeal T : Set Γ(X, U))
      (S.map (Int.castRingHom Γ(X, U)) : Set Γ(X, U)) := by
    intro hd
    obtain ⟨P, hP, hIP, hPS⟩ := Ideal.exists_le_prime_disjoint _ _ hd
    obtain ⟨Q, rfl⟩ : ∃ Q : Spec Γ(X, U), Q.asIdeal = P := ⟨⟨P, hP⟩, rfl⟩
    have hQ : hU.fromSpec Q ∉ W := by
      change Q ∈ T
      rw [← hT.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact hIP
    apply hQ
    apply hW'
    rw [hf Q]
    refine Set.disjoint_left.mpr fun s hs hsP => ?_
    exact Set.disjoint_left.mp hPS hsP ⟨s, hs, rfl⟩
  obtain ⟨a, haI, ⟨s, hs, rfl⟩⟩ := Set.not_disjoint_iff.mp hI
  refine ⟨s, hs, fun x hxU hxW => ?_⟩
  have hxU' : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
  obtain ⟨Q, rfl⟩ := hxU'
  rw [hf]
  exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp haI Q hxW

theorem proof : InvOpenInside.Statement := by
  intro X f _ p W hW
  choose s hsS hs using fun U : X.affineOpens => exists_of_isAffineOpen f p W hW U.2
  have hZ : IsCompact (W : Set X)ᶜ := by
    have hX : IsCompact (Set.univ : Set X) := by
      simpa using QuasiCompact.isCompact_preimage (f := f) Set.univ isOpen_univ isCompact_univ
    exact hX.of_isClosed_subset W.isOpen.isClosed_compl (Set.subset_univ _)
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun U : X.affineOpens => ((U : X.Opens) : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩)
  set s₀ : ℤ := ∏ U ∈ t, s U with hs₀def
  have hs₀ : s₀ ∈ (Ideal.span {((p : ℕ) : ℤ)}).primeCompl :=
    Submonoid.prod_mem _ fun U _ => hsS U
  have hne : s₀ ≠ 0 := fun h => hs₀ (h ▸ Ideal.zero_mem _)
  refine ⟨s₀.natAbs, Int.natAbs_pos.mpr hne, fun h => ?_, fun x hx => ?_⟩
  · exact hs₀ (Ideal.mem_span_singleton.mpr (Int.ofNat_dvd_left.mpr h))
  · by_contra hxW
    obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht hxW)
    have h1 := hs U x hxU hxW
    have h2 : s₀ ∈ (f.base x).asIdeal := Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hUt) h1
    exact (mem_invOpen f _ x).mp hx (Ideal.mem_of_dvd _ (Int.dvd_natAbs.mpr dvd_rfl) h2)

end InvOpenInside

end

end GroundTheory.Heights₂.Heights.Model
