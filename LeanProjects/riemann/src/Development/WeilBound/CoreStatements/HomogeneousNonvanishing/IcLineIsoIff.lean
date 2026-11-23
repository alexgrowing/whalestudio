import Mathlib
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.IAlgebra
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace PositivityTheory.UnitarySelfGeneration

set_option linter.unusedSectionVars false

section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

noncomputable def icEv (z : (Σ k, ι k) → ℂ) : MRing ι →+* ℂ :=
  (eval z).comp (MvPolynomial.map (Int.castRingHom ℂ))

theorem icEv_eq (z : (Σ k, ι k) → ℂ) (f : MRing ι) : evC z f = icEv z f := rfl

def IcGood (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)) (d : K → ℤ) (r : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∃ f g : MRing ι, IsLineIso P d 0 f g ∧ ∀ z ∈ Xo, ∃ u v : MRing ι, u * f - v * g ∈ P ∧ icEv z u ≠ 0 ∧
    icEv z v ≠ 0 ∧ ‖icEv z v‖ * r z = ‖icEv z u‖

theorem ic_lineIso_iff (P : Ideal (MRing ι)) (a b : K → ℤ) (f g : MRing ι) :
    IsLineIso P a b f g ↔ IsLineIso P (a - b) 0 f g := by
  simp [IsLineIso]

theorem ic_iff {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) (hX : Xo ⊆ mcPts P)
    (A B : HermLine ι) : IsoLineOn P Xo A B ↔ IcGood P Xo (A.a - B.a) (fun z => B.h z / A.h z) := by
  constructor
  · rintro ⟨f, g, h, hd⟩
    refine ⟨f, g, (ic_lineIso_iff _ _ _ _ _).1 h, fun z hz => ?_⟩
    have hz' := hX hz
    obtain ⟨u, v, hu, hv, huv⟩ := h.2.2.2 (RingHom.ker (icEv z)) (RingHom.ker_isPrime _)
      (fun s hs => hz'.2 s hs) (fun k => by
        obtain ⟨i, hi⟩ := hz'.1 k
        refine ⟨i, fun hh => hi ?_⟩
        simpa [icEv, RingHom.mem_ker] using hh)
    rw [RingHom.mem_ker] at hu hv
    refine ⟨u, v, huv, hu, hv, ?_⟩
    have h0 := hd z hz u v huv hu
    simp only [icEv_eq] at h0
    have hA := A.pos z hz'.1
    have hB := B.pos z hz'.1
    have hu' : 0 < ‖icEv z u‖ := norm_pos_iff.2 hu
    have hv' : 0 < ‖icEv z v‖ := norm_pos_iff.2 hv
    have h1 := Real.eq_one_of_pos_of_log_eq_zero (by positivity) h0.symm
    field_simp at h1 ⊢
    linarith
  · rintro ⟨f, g, h, hd⟩
    refine ⟨f, g, (ic_lineIso_iff _ _ _ _ _).2 h, fun z hz u' v' huv' hu' => ?_⟩
    have hz' := hX hz
    obtain ⟨u, v, huv, hu, hv, he⟩ := hd z hz
    have h1 : (u * v' - u' * v) * g ∈ P := by
      have := P.sub_mem (P.mul_mem_left u' huv) (P.mul_mem_left u huv')
      convert this using 1
      ring
    have h2 : u * v' - u' * v ∈ P := (hP.1.mem_or_mem h1).resolve_right h.2.2.1
    have h3 : icEv z (u * v' - u' * v) = 0 := hz'.2 _ h2
    rw [map_sub, map_mul, map_mul, sub_eq_zero] at h3
    have h4 : ‖icEv z u‖ * ‖icEv z v'‖ = ‖icEv z u'‖ * ‖icEv z v‖ := by
      rw [← norm_mul, ← norm_mul, h3]
    simp only [icEv_eq] at hu' ⊢
    have hA := A.pos z hz'.1
    have hB := B.pos z hz'.1
    have hu1 : 0 < ‖icEv z u‖ := norm_pos_iff.2 hu
    have hu2 : 0 < ‖icEv z u'‖ := norm_pos_iff.2 hu'
    have hv1 : 0 < ‖icEv z v‖ := norm_pos_iff.2 hv
    have h5 : ‖icEv z v'‖ / ‖icEv z u'‖ = ‖icEv z v‖ / ‖icEv z u‖ := by
      rw [div_eq_div_iff hu2.ne' hu1.ne']
      linarith
    have h6 : ‖icEv z v'‖ / ‖icEv z u'‖ * B.h z / A.h z = 1 := by
      rw [h5, ← he]
      field_simp
    rw [h6, Real.log_one]

theorem ic_one {P : Ideal (MRing ι)} (Xo : Set ((Σ k, ι k) → ℂ)) (hP : IsMultiProjPrime P) :
    IcGood P Xo 0 1 :=
  ⟨1, 1, (i_algebra K ι P hP).1 0, fun z _ => ⟨1, 1, by simp, by simp, by simp, by simp⟩⟩

theorem ic_mul {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) {d d' : K → ℤ}
    {r r' : ((Σ k, ι k) → ℂ) → ℝ} (h : IcGood P Xo d r) (h' : IcGood P Xo d' r') :
    IcGood P Xo (d + d') (r * r') := by
  obtain ⟨f, g, h, hd⟩ := h
  obtain ⟨f', g', h', hd'⟩ := h'
  refine ⟨f * f', g * g', by simpa using (i_algebra K ι P hP).2.2.2.1 _ _ _ _ _ _ _ _ h h', fun z hz => ?_⟩
  obtain ⟨u, v, huv, hu, hv, he⟩ := hd z hz
  obtain ⟨u', v', huv', hu', hv', he'⟩ := hd' z hz
  refine ⟨u * u', v * v', ?_, by simp [hu, hu'], by simp [hv, hv'], ?_⟩
  · have := P.add_mem (P.mul_mem_left (u' * f') huv) (P.mul_mem_left (v * g) huv')
    convert this using 1
    ring
  · rw [map_mul, map_mul, norm_mul, norm_mul, ← he, ← he', Pi.mul_apply]
    ring

theorem ic_inv {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) {d : K → ℤ}
    {r : ((Σ k, ι k) → ℂ) → ℝ} (h : IcGood P Xo d r) : IcGood P Xo (-d) r⁻¹ := by
  obtain ⟨f, g, h, hd⟩ := h
  refine ⟨g, f, ?_, fun z hz => ?_⟩
  · have := (ic_lineIso_iff _ _ _ _ _).1 ((i_algebra K ι P hP).2.1 _ _ _ _ h)
    simpa using this
  obtain ⟨u, v, huv, hu, hv, he⟩ := hd z hz
  refine ⟨v, u, by simpa using P.neg_mem huv, hv, hu, ?_⟩
  have hr : r z ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at he
    exact hu (norm_eq_zero.1 he.symm)
  rw [← he, Pi.inv_apply]
  field_simp

theorem ic_congr {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} {d d' : K → ℤ}
    {r r' : ((Σ k, ι k) → ℂ) → ℝ} (h : IcGood P Xo d r) (hd : d = d') (hr : ∀ z ∈ Xo, r z = r' z) :
    IcGood P Xo d' r' := by
  subst hd
  obtain ⟨f, g, h, hd⟩ := h
  refine ⟨f, g, h, fun z hz => ?_⟩
  rw [← hr z hz]
  exact hd z hz

theorem ic_pow {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) {d : K → ℤ}
    {r : ((Σ k, ι k) → ℂ) → ℝ} (h : IcGood P Xo d r) (n : ℕ) : IcGood P Xo (n • d) (r ^ n) := by
  induction n with
  | zero => simpa using ic_one Xo hP
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact ic_mul hP ih h

theorem ic_zpow {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) {d : K → ℤ}
    {r : ((Σ k, ι k) → ℂ) → ℝ} (h : IcGood P Xo d r) (n : ℤ) : IcGood P Xo (n • d) (r ^ n) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using ic_pow hP h m
  · simpa using ic_inv hP (ic_pow hP h m)

theorem ic_prod {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) {J : Type}
    (s : Finset J) (d : J → K → ℤ) (r : J → ((Σ k, ι k) → ℂ) → ℝ) (h : ∀ j, IcGood P Xo (d j) (r j)) :
    IcGood P Xo (∑ j ∈ s, d j) (∏ j ∈ s, r j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ic_one Xo hP
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    exact ic_mul hP (h j) ih

end

theorem i_comb : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)), IsMultiProjPrime P → Xo ⊆ mcPts P → (∀ (J : Type) [Fintype J] (ℓ ℓ' : J → HermLine ι) (n : J → ℤ), (∀ j, IsoLineOn P Xo (ℓ j) (ℓ' j)) → IsoLineOn P Xo (Top.combLine ℓ n) (Top.combLine ℓ' n)) ∧ (∀ A B C : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B C → IsoLineOn P Xo A C) ∧ (∀ A B : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B A) ∧ ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ : K₁ → K) (v : (Σ k, ι₁ k) → Σ k, ι k) (J : Type) [Fintype J] (ℓ : J → HermLine ι₁) (ℓ' : J → HermLine ι) (n : J → ℤ), IsBlockMap κ v → (∀ j, IsPullHerm κ v (ℓ j) (ℓ' j)) → IsPullHerm κ v (Top.combLine ℓ n) (Top.combLine ℓ' n) := by
  intro K _ ι _ P Xo hP hX
  refine ⟨fun J _ ℓ ℓ' n h => ?_, fun A B C h h' => ?_, fun A B h => ?_, ?_⟩
  · rw [ic_iff hP hX]
    refine ic_congr (ic_prod hP Finset.univ _ _ fun j => ic_zpow hP ((ic_iff hP hX _ _).1 (h j)) (n j)) ?_ ?_
    · simp [Top.combLine, smul_sub, Finset.sum_sub_distrib]
    · intro z _
      simp [Top.combLine, div_zpow, Finset.prod_div_distrib]
  · rw [ic_iff hP hX] at h h' ⊢
    refine ic_congr (ic_mul hP h h') (by abel) fun z hz => ?_
    have hB := (B.pos z (hX hz).1).ne'
    have hA := (A.pos z (hX hz).1).ne'
    simp only [Pi.mul_apply]
    field_simp
  · rw [ic_iff hP hX] at h ⊢
    refine ic_congr (ic_inv hP h) (by abel) fun z _ => ?_
    simp
  · intro K₁ _ ι₁ _ κ v J _ ℓ ℓ' n hv h
    refine ⟨?_, fun z' => ?_⟩
    · funext k
      simp only [Top.combLine, Finset.sum_apply, Pi.smul_apply, fun j => (h j).1, pullDeg]
      by_cases hk : ∃ k₁, κ k₁ = k
      · obtain ⟨k₁, rfl⟩ := hk
        simp only [hv.1.extend_apply, Finset.sum_apply, Pi.smul_apply]
      · simp [Function.extend_apply' _ _ _ hk]
    · simp only [Top.combLine, fun j => (h j).2 z']

end PositivityTheory.UnitarySelfGeneration
