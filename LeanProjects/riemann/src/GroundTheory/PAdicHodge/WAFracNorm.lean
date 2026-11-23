import Mathlib
import GroundTheory.PAdicHodge.BCrisRegularFinal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

section Abstract

variable {G R F : Type*} [Group G] [CommRing R] [IsDomain R] [CommRing F]

theorem isUnit_of_eigen_of_finiteIndex (A : G → R →+* R) (hA1 : A 1 = RingHom.id R)
    (hAmul : ∀ g h, A (g * h) = (A g).comp (A h)) (s : F →+* R) (hAs : ∀ g c, A g (s c) = s c)
    (hunit : ∀ x : R, x ≠ 0 → (∀ g, ∃ c, A g x = s c * x) → IsUnit x)
    (H : Subgroup G) [H.FiniteIndex] {b : R} (hb0 : b ≠ 0) (hb : ∀ σ ∈ H, ∃ c, A σ b = s c * b) :
    IsUnit b := by
  classical
  have hinj : ∀ σ, Function.Injective (A σ) := fun σ x y h => by
    have e : ∀ z, A σ⁻¹ (A σ z) = z := fun z => by
      rw [← RingHom.comp_apply, ← hAmul, inv_mul_cancel, hA1, RingHom.id_apply]
    rw [← e x, ← e y, h]
  set N := H.normalCore with hNdef
  let _ : Fintype (G ⧸ N) := Fintype.ofFinite _
  choose! lam hlam using hb
  have hN : ∀ n ∈ N, A n b = s (lam n) * b := fun n hn => hlam n (H.normalCore_le hn)
  set f : G ⧸ N → R := fun q => A q.out b with hf
  set P : R := ∏ q, f q with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun q _ h =>
    hb0 (hinj _ (by rw [map_zero]; exact h))
  have key : ∀ (g : G) (q : G ⧸ N),
      A g (f q) = s (lam (((g : G ⧸ N) * q).out⁻¹ * (g * q.out))) * f ((g : G ⧸ N) * q) := by
    intro g q
    set q' := (g : G ⧸ N) * q
    have hmem : q'.out⁻¹ * (g * q.out) ∈ N := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    have e : g * q.out = q'.out * (q'.out⁻¹ * (g * q.out)) := by group
    simp only [hf]
    rw [← RingHom.comp_apply, ← hAmul, e, hAmul, RingHom.comp_apply, hN _ hmem, map_mul, hAs,
      mul_inv_cancel_left]
  have hPeig : ∀ g : G, ∃ c, A g P = s c * P := by
    intro g
    refine ⟨∏ q : G ⧸ N, lam (((g : G ⧸ N) * q).out⁻¹ * (g * q.out)), ?_⟩
    rw [hP, map_prod]
    simp only [key]
    rw [Finset.prod_mul_distrib, map_prod]
    congr 1
    exact Fintype.prod_equiv (Equiv.mulLeft (g : G ⧸ N)) _ _ fun q => rfl
  have hPu : IsUnit P := hunit P hP0 hPeig
  have h1 : (1 : G ⧸ N).out ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.out_eq']
  have hdvd : b ∣ P := by
    have h2 : f 1 ∣ P := Finset.dvd_prod_of_mem f (Finset.mem_univ 1)
    have h3 : f 1 = s (lam (1 : G ⧸ N).out) * b := hN _ h1
    rw [h3] at h2
    exact (Dvd.intro_left _ rfl).trans h2
  exact isUnit_of_dvd_unit hdvd hPu

end Abstract

variable {p : ℕ} [hp : Fact p.Prime]

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

include hζ in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem isUnit_of_galB_eigen_of_finiteIndex [FiniteDimensional ℚ_[p] K]
    (H : Subgroup Gal(PadicAlgCl p/K)) [H.FiniteIndex] {b : BCris hε} (hb0 : b ≠ 0)
    (hb : ∀ σ ∈ H, ∃ q : ℚ_[p], galB hε σ b = algebraMap ℚ_[p] (BCris hε) q * b) : IsUnit b :=
  letI := isDomain_bCris hε hζ
  isUnit_of_eigen_of_finiteIndex (galB hε) (galB_one hε) (galB_mul hε) (algebraMap ℚ_[p] (BCris hε))
    (galB_algebraMap_padic hε) (fun _ hx h => isUnit_of_galB_eigen hε hζ hx h) H hb0 hb

end ACris

end GroundTheory.PAdicHodge
