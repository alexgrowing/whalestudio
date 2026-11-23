import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
import Formalism.PeriodIntegrals.HwIrred
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.FinalD

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

namespace BrInt

open Formalism.REAL Formalism.GradedWeylDivisibility

section fock

variable {σ : Type}

theorem fockF_add_right (f g g' : MvPolynomial σ ℂ) : fockF f (g + g') = fockF f g + fockF f g' := by
  unfold fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [MvPolynomial.coeff_add, star_add]
  ring

theorem fockF_smul_right (c : ℂ) (f g : MvPolynomial σ ℂ) : fockF f (c • g) = star c * fockF f g := by
  unfold fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring

theorem fockF_zero_right (f : MvPolynomial σ ℂ) : fockF f 0 = 0 := by
  unfold fockF
  simp

theorem fockF_sum_right {ι : Type*} (s : Finset ι) (f : MvPolynomial σ ℂ) (c : ι → ℂ)
    (g : ι → MvPolynomial σ ℂ) :
    fockF f (∑ i ∈ s, c i • g i) = ∑ i ∈ s, star (c i) * fockF f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fockF_zero_right]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockF_add_right, fockF_smul_right, ih]

private theorem fockF_eq_sum_of_support_subset (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    fockF f g = ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  apply Finset.sum_subset hS
  intro m _ hm
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]

theorem brFockF_map (f g : MvPolynomial σ ℚ) :
    fockF (map (algebraMap ℚ ℂ) f) (map (algebraMap ℚ ℂ) g) = ((fockQ f g : ℚ) : ℂ) := by
  rw [fockF_eq_sum_of_support_subset _ _ f.support (MvPolynomial.support_map_subset _ _)]
  unfold fockQ
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [MvPolynomial.coeff_map]

theorem map_ratSmul (q : ℚ) (p : MvPolynomial σ ℚ) :
    map (algebraMap ℚ ℂ) (q • p) = ((q : ℚ) : ℂ) • map (algebraMap ℚ ℂ) p := by
  ext m
  simp [MvPolynomial.coeff_map, MvPolynomial.coeff_smul]

theorem rat_of_pairings {ι : Type*} [Fintype ι] (β : ι → MvPolynomial σ ℚ) (G : MvPolynomial σ ℂ)
    (hG : G ∈ Submodule.span ℂ (Set.range fun i => map (algebraMap ℚ ℂ) (β i)))
    (hq : ∀ i, ∃ q : ℚ, fockF (map (algebraMap ℚ ℂ) (β i)) G = (q : ℂ)) :
    ∃ G0 ∈ Submodule.span ℚ (Set.range β), G = map (algebraMap ℚ ℂ) G0 := by
  classical
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hG
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ ℂ)
    (LinearMap.ker_eq_bot.mpr (algebraMap ℚ ℂ).injective)
  have hπq : ∀ q : ℚ, π (q : ℂ) = q := fun q => by
    have := LinearMap.congr_fun hπ q
    simpa using this
  choose r hr using hq
  set g : ι → MvPolynomial σ ℂ := fun i => map (algebraMap ℚ ℂ) (β i) with hg
  have hgg : ∀ j i, fockF (g j) (g i) = ((fockQ (β j) (β i) : ℚ) : ℂ) := fun j i =>
    brFockF_map (β j) (β i)
  have hrj : ∀ j, (r j : ℂ) = ∑ i, star (c i) * ((fockQ (β j) (β i) : ℚ) : ℂ) := by
    intro j
    rw [← hr j, fockF_sum_right]
    simp only [brFockF_map]
  have hrq : ∀ j, r j = ∑ i, fockQ (β j) (β i) * π (star (c i)) := by
    intro j
    have h1 := congrArg π (hrj j)
    rw [hπq, map_sum] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : star (c i) * ((fockQ (β j) (β i) : ℚ) : ℂ) = (fockQ (β j) (β i)) • star (c i) := by
      rw [Rat.smul_def, mul_comm]
    rw [this, LinearMap.map_smul, smul_eq_mul]
  set G0 : MvPolynomial σ ℚ := ∑ i, π (star (c i)) • β i with hG0
  have hG0m : map (algebraMap ℚ ℂ) G0 = ∑ i, ((π (star (c i)) : ℚ) : ℂ) • g i := by
    rw [hG0, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_ratSmul]
  set D : MvPolynomial σ ℂ := ∑ i, (c i - ((π (star (c i)) : ℚ) : ℂ)) • g i with hD
  have hDeq : ∑ i, c i • g i - map (algebraMap ℚ ℂ) G0 = D := by
    rw [hG0m, hD, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_smul]
  have hDj : ∀ j, fockF (g j) D = 0 := by
    intro j
    rw [hD, fockF_sum_right]
    simp only [hgg, star_sub]
    have hs : ∀ i, star (((π (star (c i)) : ℚ) : ℂ)) = ((π (star (c i)) : ℚ) : ℂ) := fun i => by simp
    simp only [hs, sub_mul, Finset.sum_sub_distrib]
    rw [← hrj j, hrq j]
    push_cast
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hDD : fockF D D = 0 := by
    have hjD : ∀ j, fockF D (g j) = 0 := fun j => by
      rw [fockHerm σ (g j) D, hDj j, star_zero]
    conv_lhs => arg 2; rw [hD]
    rw [fockF_sum_right]
    simp [hjD]
  have hD0 : D = 0 := by
    by_contra hne
    have := (fockPos σ D hne).1
    rw [hDD] at this
    simp at this
  refine ⟨G0, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [← sub_eq_zero, hDeq, hD0]

end fock

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  have h := lam.anti hij
  simp only [DomWeight.natW]
  omega

private theorem map_initMinor {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    MvPolynomial.map φ (initMinor R I hs) = initMinor S I hs := by
  unfold initMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

theorem map_bidet_int (R : Type) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    MvPolynomial.map (Int.castRingHom R) (bideterminant ℤ sz hsz I) = bideterminant R sz hsz I := by
  unfold bideterminant
  rw [map_prod]
  exact Finset.prod_congr rfl fun k _ => map_initMinor _ (I k) (hsz k)

theorem mapZC {σ : Type*} (f : MvPolynomial σ ℤ) :
    map (Int.castRingHom ℂ) f = map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) f) := by
  rw [MvPolynomial.map_map]
  congr 1

theorem extremal_map {N : ℕ} (lam : DomWeight N) :
    extremal ℂ N lam = map (algebraMap ℚ ℂ) (extremal ℚ N lam) := by
  unfold extremal hw
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow]
  congr 1
  unfold lpMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

theorem normFock_map {N : ℕ} (lam : DomWeight N) (a b : MvPolynomial (Fin N × Fin N) ℚ) :
    normFock lam (map (algebraMap ℚ ℂ) a) (map (algebraMap ℚ ℂ) b) = ((normFockQ lam a b : ℚ) : ℂ) := by
  unfold normFock normFockQ
  rw [brFockF_map, extremal_map, brFockF_map]
  exact (Rat.cast_div _ _).symm

private theorem fockQ_eq_sum_of_support_subset {σ : Type*} (f g : MvPolynomial σ ℚ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    fockQ f g = ∑ m ∈ S, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold fockQ
  apply Finset.sum_subset hS
  intro m _ hm
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]

theorem normFockQ_symm {N : ℕ} (lam : DomWeight N) (a b : MvPolynomial (Fin N × Fin N) ℚ) :
    normFockQ lam a b = normFockQ lam b a := by
  classical
  unfold normFockQ
  congr 1
  rw [fockQ_eq_sum_of_support_subset a b (a.support ∪ b.support) Finset.subset_union_left,
    fockQ_eq_sum_of_support_subset b a (a.support ∪ b.support) Finset.subset_union_right]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

private theorem fockF_eq_sum_lemma {σ : Type*} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    fockF f g = ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold fockF
  apply Finset.sum_subset hS
  intro m _ hm
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]

private theorem fockF_swap_eq_star {σ : Type*} [DecidableEq σ] (f g : MvPolynomial σ ℂ) :
    fockF g f = star (fockF f g) := by
  classical
  rw [fockF_eq_sum_lemma g f (f.support ∪ g.support) Finset.subset_union_right,
    fockF_eq_sum_lemma f g (f.support ∪ g.support) Finset.subset_union_left, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', star_star, star_natCast]
  ring

theorem normFock_swap {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam g f = star (normFock lam f g) := by
  unfold normFock
  rw [star_div₀, ← fockF_swap_eq_star f g, ← fockF_swap_eq_star (extremal ℂ N lam) (extremal ℂ N lam)]

theorem fockF_ext_ne {N : ℕ} (lam : DomWeight N) :
    fockF (extremal ℂ N lam) (extremal ℂ N lam) ≠ 0 := by
  rw [extremal_map, brFockF_map]
  have hne : extremal ℚ N lam ≠ 0 := by
    unfold extremal
    exact hwNe ℚ N N le_rfl lam.natW
  have hpos := (fockQPos (Fin N × Fin N) (extremal ℚ N lam) (extremal ℚ N lam)).2 hne
  exact_mod_cast hpos.ne'

end BrInt

open BrInt Formalism.REAL Formalism.GradedWeylDivisibility in
theorem brIntegral_of (h2 : Formalism.BasicNotions.FactDelDualNabla) (h3 : PI.HwIrred) : BrIntegral := by
  intro n N h lam sg hI io br hI1 hI2 hB2 hT f hf
  have hfN : f ∈ nablaSq ℤ N lam := weylLeDual ℤ N N le_rfl lam.natW (natW_anti lam) hf
  have hFd : map (Int.castRingHom ℂ) f ∈ delSq ℂ N lam := by
    rw [← (h3 N lam).1]
    exact dualWeylMap ℤ ℂ (Int.castRingHom ℂ) N N lam.natW f hfN
  have hG : br (map (Int.castRingHom ℂ) f) ∈ nablaSq ℂ n sg := by
    rw [(h3 n sg).1]
    exact hB2 _ hFd
  have hfQ : map (Int.castRingHom ℚ) f ∈ nablaSq ℚ N lam :=
    dualWeylMap ℤ ℚ (Int.castRingHom ℚ) N N lam.natW f hfN
  have hpair : ∀ s ∈ nablaSq ℤ n sg, ∃ z : ℤ,
      normFock sg (map (Int.castRingHom ℂ) s) (br (map (Int.castRingHom ℂ) f)) = (z : ℂ) := by
    intro s hs
    have hsC : map (Int.castRingHom ℂ) s ∈ nablaSq ℂ n sg :=
      dualWeylMap ℤ ℂ (Int.castRingHom ℂ) n n sg.natW s hs
    obtain ⟨fI, hfI, hio⟩ := hI1 s hs
    obtain ⟨z, hz⟩ := (h2 N lam _ hfQ).mpr ⟨f, hf, rfl⟩ fI hfI
    refine ⟨z, ?_⟩
    rw [← hT _ hsC _ hFd, hio, mapZC fI, mapZC f, normFock_map, normFockQ_symm, hz]
    push_cast
    rfl
  have : Fintype (ssIdx n n sg.natW) := (sSIdxFinite n n sg.natW).fintype
  obtain ⟨b, hWB, hb⟩ := sSBasis ℂ n n sg.natW
  have hb' : ∀ m : ssIdx n n sg.natW, ∃ p : MvPolynomial (Fin n × Fin n) ℤ,
      p ∈ nablaSq ℤ n sg ∧ map (Int.castRingHom ℂ) p = b m := by
    intro m
    obtain ⟨K, sz, hsz, I, hsh, -, hbm⟩ := (hb m).2.2
    refine ⟨bideterminant ℤ sz hsz I, ?_, ?_⟩
    · have := bidetMem ℤ n n K sz hsz I
      rw [hsh] at this
      exact this
    · rw [hbm, map_bidet_int]
  choose p hp hpb using hb'
  have hbeq : (fun m => map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) (p m))) = b := by
    funext m
    rw [← mapZC, hpb]
  have hspan : br (map (Int.castRingHom ℂ) f) ∈
      Submodule.span ℂ (Set.range fun m => map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) (p m))) := by
    rw [hbeq, hWB.2.1]
    exact hG
  have hq : ∀ m, ∃ q : ℚ, fockF (map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) (p m)))
      (br (map (Int.castRingHom ℂ) f)) = (q : ℂ) := by
    intro m
    obtain ⟨z, hz⟩ := hpair (p m) (hp m)
    refine ⟨z * fockQ (extremal ℚ n sg) (extremal ℚ n sg), ?_⟩
    unfold normFock at hz
    rw [div_eq_iff (fockF_ext_ne sg), mapZC] at hz
    rw [hz, extremal_map, brFockF_map]
    push_cast
    rfl
  obtain ⟨G0, hG0s, hG0⟩ := rat_of_pairings _ _ hspan hq
  have hG0N : G0 ∈ nablaSq ℚ n sg := by
    refine (Submodule.span_le.mpr ?_) hG0s
    rintro _ ⟨m, rfl⟩
    exact dualWeylMap ℤ ℚ (Int.castRingHom ℚ) n n sg.natW (p m) (hp m)
  obtain ⟨f0, hf0, hf0eq⟩ := (h2 n sg G0 hG0N).mp (by
    intro g hg
    obtain ⟨z, hz⟩ := hpair g hg
    refine ⟨z, ?_⟩
    apply (Rat.cast_injective (α := ℂ))
    rw [← normFock_map, ← hG0, ← mapZC, normFock_swap, hz]
    simp)
  refine ⟨f0, hf0, ?_⟩
  rw [hG0, ← hf0eq, ← mapZC]

end PI.WGL
