import Mathlib
open IsLocalRing

namespace GlobalTheory
namespace SpreadOut

lemma exists_num_den {T : Type} [CommRing T] (p : Ideal T) [p.IsPrime]
    (y : Localization.AtPrime p) :
    ∃ a s : T, s ∉ p ∧ algebraMap T _ s * y = algebraMap T _ a := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
  exact ⟨a, s, s.2, IsLocalization.mk'_spec' _ a s⟩

lemma prod_not_mem {T : Type} [CommRing T] {ι : Type} (p : Ideal T) [p.IsPrime]
    (S : Finset ι) (g : ι → T) (h : ∀ i ∈ S, g i ∉ p) : ∏ i ∈ S, g i ∉ p :=
  Submonoid.prod_mem p.primeCompl (fun i hi => h i hi)

lemma exists_kill {T : Type} [CommRing T] (p : Ideal T) [p.IsPrime] (f₀ : T)
    (z : Localization.Away f₀)
    (ι₀ : Localization.Away f₀ →ₐ[T] Localization.AtPrime p) (hz : ι₀ z = 0) :
    ∃ t : T, t ∉ p ∧ ∀ (B : Type) [CommRing B] [Algebra T B]
      (κ : Localization.Away f₀ →ₐ[T] B), IsUnit (algebraMap T B t) → κ z = 0 := by
  obtain ⟨⟨b, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f₀) z
  have hspec := IsLocalization.mk'_spec' (Localization.Away f₀) b m
  have h1 : algebraMap T (Localization.AtPrime p) b = 0 := by
    have := congrArg ι₀ hspec
    rw [map_mul, AlgHom.commutes, AlgHom.commutes, hz, mul_zero] at this
    exact this.symm
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ b).1 h1
  refine ⟨t, t.2, fun B _ _ κ hu => ?_⟩
  have h2 := congrArg κ hspec
  rw [map_mul, AlgHom.commutes, AlgHom.commutes] at h2
  have hb : algebraMap T B b = 0 := by
    apply hu.mul_left_cancel
    rw [← map_mul, ht, map_zero, mul_zero]
  have hm : IsUnit (algebraMap T B m) := by
    rw [← AlgHom.commutes κ]
    exact (IsLocalization.map_units (Localization.Away f₀) m).map κ
  rw [hb] at h2
  exact hm.mul_right_eq_zero.1 h2

theorem spread_out : ∀ (T A : Type) [CommRing T] [CommRing A] [Algebra T A]
    [Algebra.FinitePresentation T A] (p : Ideal T) [p.IsPrime]
    (φ : A →ₐ[T] Localization.AtPrime p), ∃ f : T, f ∉ p ∧
      ∃ (s : A →ₐ[T] Localization.Away f) (ι : Localization.Away f →ₐ[T] Localization.AtPrime p),
        ι.comp s = φ := by
  intro T A _ _ _ _ p _ φ
  obtain ⟨n, π, hπ, hker⟩ := Algebra.FinitePresentation.out (R := T) (A := A)
  obtain ⟨G, hG⟩ := hker
  choose a s hs hy using fun i : Fin n => exists_num_den p (φ (π (MvPolynomial.X i)))
  set f₀ : T := ∏ i, s i with hf₀
  have hf₀p : f₀ ∉ p := prod_not_mem p _ s (fun i _ => hs i)
  have hu₀ : IsUnit ((Algebra.ofId T (Localization.AtPrime p)) f₀) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨f₀, hf₀p⟩ : p.primeCompl)
  let ι₀ : Localization.Away f₀ →ₐ[T] Localization.AtPrime p :=
    IsLocalization.Away.liftAlgHom (S := Localization.Away f₀) f₀ hu₀
  have hu : ∀ i, IsUnit (algebraMap T (Localization.Away f₀) (s i)) := fun i =>
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem s (Finset.mem_univ i)))
      (IsLocalization.Away.algebraMap_isUnit f₀)
  let x : Fin n → Localization.Away f₀ := fun i =>
    algebraMap T _ (a i) * ↑(hu i).unit⁻¹
  let ψ₀ : MvPolynomial (Fin n) T →ₐ[T] Localization.Away f₀ := MvPolynomial.aeval x
  have hι0 : ∀ i, ι₀ (x i) = φ (π (MvPolynomial.X i)) := by
    intro i
    have hu' : IsUnit (algebraMap T (Localization.AtPrime p) (s i)) :=
      IsLocalization.map_units _ (⟨s i, hs i⟩ : p.primeCompl)
    apply hu'.mul_left_cancel
    rw [hy i, ← AlgHom.commutes ι₀ (s i), ← map_mul]
    simp only [x]
    rw [mul_left_comm, IsUnit.mul_val_inv, mul_one, AlgHom.commutes]
  have hφ : ι₀.comp ψ₀ = φ.comp π := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, ψ₀, MvPolynomial.aeval_X]
    exact hι0 i
  have hzero : ∀ g : G, ι₀ (ψ₀ g) = 0 := by
    intro g
    have hg : (g : MvPolynomial (Fin n) T) ∈ RingHom.ker π.toRingHom := by
      rw [← hG]; exact Ideal.subset_span g.2
    rw [RingHom.mem_ker] at hg
    have := congrArg (fun h => h (g : MvPolynomial (Fin n) T)) hφ
    simp only [AlgHom.comp_apply] at this
    rw [this]
    have hg' : π g = 0 := hg
    rw [hg', map_zero]
  choose t ht hkill using fun g : G => exists_kill p f₀ (ψ₀ g) ι₀ (hzero g)
  set f : T := f₀ * ∏ g, t g with hfdef
  have hfp : f ∉ p :=
    p.primeCompl.mul_mem hf₀p (prod_not_mem p _ t (fun g _ => ht g))
  have huj : IsUnit ((Algebra.ofId T (Localization.Away f)) f₀) :=
    isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right f₀ _)) (IsLocalization.Away.algebraMap_isUnit f)
  let j : Localization.Away f₀ →ₐ[T] Localization.Away f :=
    IsLocalization.Away.liftAlgHom (S := Localization.Away f₀) f₀ huj
  let ψ : MvPolynomial (Fin n) T →ₐ[T] Localization.Away f := j.comp ψ₀
  have hψG : ∀ g : G, ψ g = 0 := by
    intro g
    apply hkill g (Localization.Away f) j
    exact isUnit_of_dvd_unit
      (map_dvd _ (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem t (Finset.mem_univ g)) f₀))
      (IsLocalization.Away.algebraMap_isUnit f)
  have hspan : Ideal.span (G : Set (MvPolynomial (Fin n) T)) ≤
      RingHom.ker (ψ : MvPolynomial (Fin n) T →+* Localization.Away f) := by
    rw [Ideal.span_le]
    intro g hg
    rw [SetLike.mem_coe, RingHom.mem_ker]
    exact hψG ⟨g, hg⟩
  have hψker : ∀ q : MvPolynomial (Fin n) T, q ∈ RingHom.ker π → ψ q = 0 := by
    intro q hq
    have hq' : q ∈ Ideal.span (G : Set (MvPolynomial (Fin n) T)) := by
      rw [hG]; exact hq
    exact (RingHom.mem_ker).1 (hspan hq')
  let sq := Ideal.Quotient.liftₐ (RingHom.ker π) ψ hψker
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  let σ : A →ₐ[T] Localization.Away f := sq.comp e.symm.toAlgHom
  have hσ : ∀ q, σ (π q) = ψ q := by
    intro q
    have : e.symm (π q) = Ideal.Quotient.mk (RingHom.ker π) q := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    show sq (e.symm (π q)) = ψ q
    rw [this]
    simp only [sq, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    rfl
  have huι : IsUnit ((Algebra.ofId T (Localization.AtPrime p)) f) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨f, hfp⟩ : p.primeCompl)
  let ι : Localization.Away f →ₐ[T] Localization.AtPrime p :=
    IsLocalization.Away.liftAlgHom (S := Localization.Away f) f huι
  refine ⟨f, hfp, σ, ι, ?_⟩
  have hιj : ι.comp j = ι₀ :=
    (IsLocalization.algHom_subsingleton (Submonoid.powers f₀)).elim _ _
  apply AlgHom.ext
  intro y
  obtain ⟨q, rfl⟩ := hπ y
  rw [AlgHom.comp_apply, hσ q]
  have h1 := congrArg (fun h => h (ψ₀ q)) hιj
  have h2 := congrArg (fun h => h q) hφ
  simp only [AlgHom.comp_apply] at h1 h2
  simp only [ψ, AlgHom.comp_apply]
  rw [h1, h2]

end SpreadOut
end GlobalTheory
