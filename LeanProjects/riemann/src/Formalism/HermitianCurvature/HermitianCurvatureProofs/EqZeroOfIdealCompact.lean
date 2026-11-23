import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology

namespace Formalism.FourierDecayAlt.P.A6x5

theorem roots_finite_domain {F : Type} [CommRing F] [IsDomain F] (s : ℕ) (hs : 1 ≤ s) (d : F) :
    {x : F | x ^ s = d}.Finite := by
  classical
  refine (Polynomial.nthRoots s d).toFinset.finite_toSet.subset ?_
  intro x hx
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  exact (Polynomial.mem_nthRoots hs).2 hx

theorem roots_finite {K : Type} [CommRing K] [IsArtinianRing K] [IsReduced K] (s : ℕ)
    (hs : 1 ≤ s) (d : K) : {x : K | x ^ s = d}.Finite := by
  have h1 : (Set.pi Set.univ fun I : MaximalSpectrum K =>
      {x : K ⧸ I.asIdeal | x ^ s = IsArtinianRing.equivPi K d I}).Finite :=
    Set.Finite.pi fun I => roots_finite_domain s hs _
  refine (h1.preimage ((IsArtinianRing.equivPi K).injective.injOn)).subset ?_
  intro x hx I _
  have hx' : x ^ s = d := hx
  change IsArtinianRing.equivPi K x I ^ s = IsArtinianRing.equivPi K d I
  rw [← hx', map_pow, Pi.pow_apply]

section Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem multiples_near_zero (C : Set K) (hC : IsCompact C) (i : K) (hi : ∀ a : K, a * i ∈ C)
    (W : Set K) (hW : W ∈ 𝓝 (0 : K)) : ∃ k : ℕ, ((k + 1 : ℕ) : K) * i ∈ W := by
  obtain ⟨a, _, ha⟩ := hC.exists_mapClusterPt_of_frequently (l := atTop)
    (f := fun n : ℕ => (n : K) * i) (Eventually.of_forall fun n => hi _).frequently
  have hc : Tendsto (fun p : K × K => p.2 - p.1) (𝓝 (a, a)) (𝓝 0) := by
    have : Continuous (fun p : K × K => p.2 - p.1) := continuous_snd.sub continuous_fst
    simpa using this.tendsto (a, a)
  have h1 := hc hW
  rw [nhds_prod_eq, Filter.mem_map, Filter.mem_prod_self_iff] at h1
  obtain ⟨W', hW', hsub⟩ := h1
  have hf := Filter.frequently_atTop.1 (ha.frequently hW')
  obtain ⟨n, _, hn⟩ := hf 0
  obtain ⟨m, hm, hm'⟩ := hf (n + 1)
  obtain ⟨k, rfl⟩ : ∃ k, m = n + 1 + k := ⟨m - (n + 1), by omega⟩
  refine ⟨k, ?_⟩
  have h2 : (((n : K) * i, ((n + 1 + k : ℕ) : K) * i) : K × K) ∈ W' ×ˢ W' := ⟨hn, hm'⟩
  have h3 := hsub h2
  simp only [Set.mem_preimage] at h3
  have h4 : ((n + 1 + k : ℕ) : K) * i - (n : K) * i = ((k + 1 : ℕ) : K) * i := by
    push_cast; ring
  rwa [h4] at h3

theorem eq_zero_of_ideal_compact [T2Space K] [IsReduced K] (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (C : Set K) (hC : IsCompact C) (i : K) (hi : ∀ a : K, a * i ∈ C) : i = 0 := by
  set S : Set (K × K) := Set.range fun k : ℕ =>
    (((k + 1 : ℕ) : K) * i, Ring.inverse ((k + 1 : ℕ) : K) * i) with hS
  have hSC : S ⊆ C ×ˢ C := by
    rintro _ ⟨k, rfl⟩
    exact ⟨hi _, hi _⟩
  have hcl : closure S ⊆ C ×ˢ C := closure_minimal hSC (hC.prod hC).isClosed
  have hcc : IsCompact (closure S) := (hC.prod hC).of_isClosed_subset isClosed_closure hcl
  have hmul : closure S ⊆ {p : K × K | p.1 * p.2 = i ^ 2} := by
    refine closure_minimal ?_ (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const)
    rintro _ ⟨k, rfl⟩
    change ((k + 1 : ℕ) : K) * i * (Ring.inverse ((k + 1 : ℕ) : K) * i) = i ^ 2
    have := Ring.mul_inverse_cancel _ (hn (k + 1) (by omega))
    calc ((k + 1 : ℕ) : K) * i * (Ring.inverse ((k + 1 : ℕ) : K) * i)
        = (((k + 1 : ℕ) : K) * Ring.inverse ((k + 1 : ℕ) : K)) * i ^ 2 := by ring
      _ = i ^ 2 := by rw [this, one_mul]
  have himg : Prod.fst '' closure S = closure (Prod.fst '' S) :=
    image_closure_of_isCompact hcc continuous_fst.continuousOn
  have h0 : (0 : K) ∈ closure (Prod.fst '' S) := by
    rw [mem_closure_iff_nhds]
    intro W hW
    obtain ⟨k, hk⟩ := multiples_near_zero C hC i hi W hW
    exact ⟨_, hk, ⟨_, ⟨k, rfl⟩, rfl⟩⟩
  rw [← himg] at h0
  obtain ⟨⟨x, y⟩, hp, hx⟩ := h0
  have h1 : x * y = i ^ 2 := hmul hp
  have hx' : x = 0 := hx
  rw [hx', zero_mul] at h1
  exact IsNilpotent.eq_zero ⟨2, h1.symm⟩

variable {R : Subring K} {ψ : AddChar K ℂ}

theorem eq_zero_of_forall_pow (hD : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (ϖ : Kˣ) (hϖ : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (x : K)
    (hx : ∀ N : ℕ, ∃ r ∈ R, x = (ϖ : K) ^ N * r) : x = 0 := by
  have := hD.t2
  have := hD.red
  refine eq_zero_of_ideal_compact hn (R : Set K) hD.isCompact x ?_
  intro a
  obtain ⟨m, hm⟩ := hϖ a
  obtain ⟨r, hr, hxr⟩ := hx m
  have : a * x = (ϖ : K) ^ m * a * r := by rw [hxr]; ring
  rw [this]
  exact R.mul_mem hm hr

theorem pow_small (hD : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (ϖ : Kˣ) (hϖR : (ϖ : K) ∈ R) (hϖ : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R)
    (V : Set K) (hV : V ∈ 𝓝 (0 : K)) : ∃ N : ℕ, ∀ r ∈ R, (ϖ : K) ^ N * r ∈ V := by
  have := hD.t2
  by_contra hcon
  push Not at hcon
  have hcomp : ∀ N : ℕ, IsCompact ((fun r => (ϖ : K) ^ N * r) '' (R : Set K)) := fun N =>
    hD.isCompact.image (continuous_const.mul continuous_id)
  have hne := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun N : ℕ => ((fun r => (ϖ : K) ^ N * r) '' (R : Set K)) ∩ (interior V)ᶜ) ?_ ?_ ?_ ?_
  · obtain ⟨x, hx⟩ := hne
    rw [Set.mem_iInter] at hx
    have hx0 : x = 0 := by
      refine eq_zero_of_forall_pow hD hn ϖ hϖ x ?_
      intro N
      obtain ⟨r, hr, h⟩ := (hx N).1
      exact ⟨r, hr, h.symm⟩
    exact (hx 0).2 (hx0 ▸ mem_interior_iff_mem_nhds.2 hV)
  · intro N
    refine Set.inter_subset_inter_left _ ?_
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨(ϖ : K) * r, R.mul_mem hϖR hr, by simp only [pow_succ, mul_assoc]⟩
  · intro N
    obtain ⟨r, hr, h⟩ := hcon N
    exact ⟨_, ⟨r, hr, rfl⟩, fun h' => h (interior_subset h')⟩
  · exact (hcomp 0).inter_right isOpen_interior.isClosed_compl
  · intro N
    exact (hcomp N).isClosed.inter isOpen_interior.isClosed_compl

theorem one_add_unit (hD : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (ϖ : Kˣ) (hϖR : (ϖ : K) ∈ R) (hϖ : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (r : K)
    (hr : r ∈ R) : ∃ u ∈ R, (1 + (ϖ : K) * r) * u = 1 := by
  have := hD.artin
  have hgeo : ∀ k : ℕ, (1 + (ϖ : K) * r) * ∑ j ∈ Finset.range k, (-((ϖ : K) * r)) ^ j =
      1 - (-((ϖ : K) * r)) ^ k := by
    intro k
    have := mul_neg_geom_sum (-((ϖ : K) * r)) k
    rwa [sub_neg_eq_add] at this
  have hsmall : ∀ (y : K) (N : ℕ), ∃ k : ℕ, ∃ r' ∈ R, (-((ϖ : K) * r)) ^ k * y = (ϖ : K) ^ N * r' := by
    intro y N
    obtain ⟨m, hm⟩ := hϖ y
    refine ⟨N + m, (-r) ^ (N + m) * ((ϖ : K) ^ m * y), R.mul_mem (R.pow_mem (R.neg_mem hr) _) hm, ?_⟩
    have : -((ϖ : K) * r) = (ϖ : K) * (-r) := by ring
    rw [this, mul_pow, pow_add]
    ring
  have hunit : IsUnit (1 + (ϖ : K) * r) := by
    apply IsArtinianRing.isUnit_of_mem_nonZeroDivisors
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have hy' : ∀ k : ℕ, y = (-((ϖ : K) * r)) ^ k * y := by
      intro k
      have h1 : (1 - (-((ϖ : K) * r)) ^ k) * y = 0 := by
        rw [← hgeo k]
        calc _ = (y * (1 + (ϖ : K) * r)) * ∑ j ∈ Finset.range k, (-((ϖ : K) * r)) ^ j := by ring
          _ = 0 := by rw [hy, zero_mul]
      have h2 : y - (-((ϖ : K) * r)) ^ k * y = 0 := by rw [← h1]; ring
      exact sub_eq_zero.1 h2
    refine eq_zero_of_forall_pow hD hn ϖ hϖ y ?_
    intro N
    obtain ⟨k, r', hr', h⟩ := hsmall y N
    exact ⟨r', hr', (hy' k).trans h⟩
  obtain ⟨u, hu⟩ := hunit.exists_right_inv
  refine ⟨u, ?_, hu⟩
  obtain ⟨k, r', hr', h⟩ := hsmall u 0
  have h1 : u = ∑ j ∈ Finset.range k, (-((ϖ : K) * r)) ^ j + (-((ϖ : K) * r)) ^ k * u := by
    have h2 : ((1 + (ϖ : K) * r) * u) * ∑ j ∈ Finset.range k, (-((ϖ : K) * r)) ^ j =
        (1 - (-((ϖ : K) * r)) ^ k) * u := by rw [← hgeo k]; ring
    rw [hu, one_mul] at h2
    rw [h2]; ring
  rw [h1, h, pow_zero, one_mul]
  refine R.add_mem (R.sum_mem fun j _ => R.pow_mem (R.neg_mem (R.mul_mem hϖR hr)) _) hr'

theorem image_pow_eq_preimage (ϖ : Kˣ) (N : ℕ) (S : Set K) :
    (fun r => (ϖ : K) ^ N * r) '' S = (fun x => ((ϖ⁻¹ : Kˣ) : K) ^ N * x) ⁻¹' S := by
  have h1 : ((ϖ⁻¹ : Kˣ) : K) ^ N * (ϖ : K) ^ N = 1 := by
    rw [← mul_pow, Units.inv_mul, one_pow]
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    change ((ϖ⁻¹ : Kˣ) : K) ^ N * ((ϖ : K) ^ N * r) ∈ S
    rwa [← mul_assoc, h1, one_mul]
  · intro hx
    refine ⟨_, hx, ?_⟩
    change (ϖ : K) ^ N * (((ϖ⁻¹ : Kˣ) : K) ^ N * x) = x
    rw [← mul_assoc, mul_comm ((ϖ : K) ^ N), h1, one_mul]

theorem preimage_pow_eq_image (ϖ : Kˣ) (N : ℕ) (S : Set K) :
    (fun x => (ϖ : K) ^ N * x) ⁻¹' S = (fun r => ((ϖ⁻¹ : Kˣ) : K) ^ N * r) '' S := by
  have := image_pow_eq_preimage ϖ⁻¹ N S
  rw [inv_inv] at this
  exact this.symm

def unitBox (R : Subring K) (ϖ : Kˣ) (j : ℕ) : Set K :=
  {z | ∃ y, z * y = 1 ∧ (ϖ : K) ^ j * z ∈ R ∧ (ϖ : K) ^ j * y ∈ R}

theorem unitBox_mono (ϖ : Kˣ) (hϖR : (ϖ : K) ∈ R) {j j' : ℕ} (h : j ≤ j') :
    unitBox R ϖ j ⊆ unitBox R ϖ j' := by
  rintro z ⟨y, hzy, hz, hy⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨y, hzy, ?_, ?_⟩
  · rw [pow_add, mul_comm ((ϖ : K) ^ j), mul_assoc]
    exact R.mul_mem (R.pow_mem hϖR _) hz
  · rw [pow_add, mul_comm ((ϖ : K) ^ j), mul_assoc]
    exact R.mul_mem (R.pow_mem hϖR _) hy

theorem unitBox_isCompact (hD : LocalDatum K R ψ) (ϖ : Kˣ) (j : ℕ) :
    IsCompact (unitBox R ϖ j) := by
  have := hD.t2
  have hA : IsCompact ((fun x => (ϖ : K) ^ j * x) ⁻¹' (R : Set K)) := by
    rw [preimage_pow_eq_image]
    exact hD.isCompact.image (continuous_const.mul continuous_id)
  have hP : IsCompact ((((fun x => (ϖ : K) ^ j * x) ⁻¹' (R : Set K)) ×ˢ
      ((fun x => (ϖ : K) ^ j * x) ⁻¹' (R : Set K))) ∩ {p : K × K | p.1 * p.2 = 1}) :=
    (hA.prod hA).inter_right (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const)
  have : unitBox R ϖ j = Prod.fst '' ((((fun x => (ϖ : K) ^ j * x) ⁻¹' (R : Set K)) ×ˢ
      ((fun x => (ϖ : K) ^ j * x) ⁻¹' (R : Set K))) ∩ {p : K × K | p.1 * p.2 = 1}) := by
    ext z
    constructor
    · rintro ⟨y, hzy, hz, hy⟩
      exact ⟨(z, y), ⟨⟨hz, hy⟩, hzy⟩, rfl⟩
    · rintro ⟨⟨z', y⟩, ⟨⟨hz, hy⟩, hzy⟩, rfl⟩
      exact ⟨y, hzy, hz, hy⟩
  rw [this]
  exact hP.image continuous_fst

theorem unitBox_isOpen (hD : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (ϖ : Kˣ) (hϖR : (ϖ : K) ∈ R) (hϖ : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (j : ℕ) :
    IsOpen (unitBox R ϖ j) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨y, hzy, hz, hy⟩
  have hO : IsOpen ((fun w => ((ϖ⁻¹ : Kˣ) : K) ^ (j + 1) * (w - z)) ⁻¹' (R : Set K)) :=
    hD.isOpen.preimage (continuous_const.mul (continuous_id.sub continuous_const))
  refine Filter.mem_of_superset (hO.mem_nhds ?_) ?_
  · change ((ϖ⁻¹ : Kˣ) : K) ^ (j + 1) * (z - z) ∈ R
    rw [sub_self, mul_zero]
    exact R.zero_mem
  · intro w hw
    have hw' : w - z ∈ (fun x => ((ϖ⁻¹ : Kˣ) : K) ^ (j + 1) * x) ⁻¹' (R : Set K) := hw
    rw [← image_pow_eq_preimage] at hw'
    obtain ⟨r, hr, hrw⟩ := hw'
    have hrw' : (ϖ : K) ^ (j + 1) * r = w - z := hrw
    have hwz : w = z + (ϖ : K) ^ (j + 1) * r := by rw [hrw']; ring
    obtain ⟨u, hu, hu1⟩ := one_add_unit hD hn ϖ hϖR hϖ (r * ((ϖ : K) ^ j * y)) (R.mul_mem hr hy)
    refine ⟨y * u, ?_, ?_, ?_⟩
    · calc w * (y * u) = (z * y + (ϖ : K) * (r * ((ϖ : K) ^ j * y))) * u := by rw [hwz]; ring
        _ = 1 := by rw [hzy, hu1]
    · have : (ϖ : K) ^ j * w = (ϖ : K) ^ j * z + (ϖ : K) ^ j * (ϖ : K) ^ (j + 1) * r := by
        rw [hwz]; ring
      rw [this]
      exact R.add_mem hz (R.mul_mem (R.mul_mem (R.pow_mem hϖR _) (R.pow_mem hϖR _)) hr)
    · rw [← mul_assoc]
      exact R.mul_mem hy hu

end Top

end Formalism.FourierDecayAlt.P.A6x5

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.A6x5

theorem rootsFinite : Formalism.FourierDecayAlt.A6.RootsFinite := by
  intro K _ _ _ s hs D
  refine ((roots_finite s hs (D : K)).preimage (Units.val_injective.injOn)).subset ?_
  intro z hz
  have hz' : z ^ s = D := hz
  change (z : K) ^ s = (D : K)
  rw [← hz', Units.val_pow_eq_pow_val]

theorem rootsSeparated : Formalism.FourierDecayAlt.A6.RootsSeparated := by
  intro K _ _ _ R ψ hD _ s hs Q hQ hQu
  have := hD.t2
  have := hD.artin
  have := hD.red
  have hfin : {ζ : K | ζ ^ s = 1}.Finite := roots_finite s hs 1
  have hT : {ζ : K | ζ ^ s = 1 ∧ ζ ≠ 1}.Finite := hfin.subset (fun ζ h => h.1)
  have hC : IsCompact (⋃ ζ ∈ {ζ : K | ζ ^ s = 1 ∧ ζ ≠ 1}, (fun d => (1 - ζ) ^ s * d) '' Q) :=
    hT.isCompact_biUnion (fun ζ _ => hQ.image (continuous_const.mul continuous_id))
  have h0 : (0 : K) ∉ ⋃ ζ ∈ {ζ : K | ζ ^ s = 1 ∧ ζ ≠ 1}, (fun d => (1 - ζ) ^ s * d) '' Q := by
    intro h
    simp only [Set.mem_iUnion, Set.mem_image] at h
    obtain ⟨ζ, hζ, d, hd, h⟩ := h
    have h1 : (1 - ζ) ^ s = 0 := (hQu d hd).mul_left_eq_zero.1 h
    have h2 : 1 - ζ = 0 := IsNilpotent.eq_zero ⟨s, h1⟩
    exact hζ.2 (sub_eq_zero.1 h2).symm
  refine ⟨(fun w => w ^ s) ⁻¹'
    (⋃ ζ ∈ {ζ : K | ζ ^ s = 1 ∧ ζ ≠ 1}, (fun d => (1 - ζ) ^ s * d) '' Q)ᶜ, ?_, ?_⟩
  · apply (hC.isClosed.isOpen_compl.preimage (continuous_pow s)).mem_nhds
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    rw [zero_pow (by omega)]
    exact h0
  · intro z z' hz hzz hV
    by_contra hne
    apply hV
    simp only [Set.mem_iUnion, Set.mem_image]
    refine ⟨((z' * z⁻¹ : Kˣ) : K), ⟨?_, ?_⟩, (z : K) ^ s, hz, ?_⟩
    · rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, ← hzz, mul_inv_cancel, Units.val_one]
    · intro h
      apply hne
      have h' : z' * z⁻¹ = 1 := Units.ext (by rw [h, Units.val_one])
      exact (mul_inv_eq_one.1 h').symm
    · rw [← mul_pow, sub_mul, one_mul, ← Units.val_mul, inv_mul_cancel_right]

theorem blockParametrisation : Formalism.FourierDecayAlt.A6.Param := by
  intro K _ m t c u' a b hu w hw
  have hdet : IsUnit ((t : K) • u').det := by
    rw [Matrix.det_smul, isUpUni_det _ hu, mul_one]; exact (t.isUnit.pow _)
  constructor
  · rw [fromBlocks_multiply, fromBlocks_multiply]
    have h1 : a * w * ((t : K) • u') * ((t : K) • u')⁻¹ * ((t : K) • b) = a * w * ((t : K) • b) := by
      rw [Matrix.mul_assoc (a * w), Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    rw [h1]
    congr 1 <;> simp [Matrix.mul_assoc, add_comm]
  · intro i hi
    have hi0 : ∀ j : Fin m, j ≠ i → u' j i = 0 := by
      intro j hj
      apply hu.1
      have : i.val < j.val := by
        have : j.val ≠ i.val := fun h => hj (Fin.ext h)
        omega
      exact this
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [Matrix.smul_apply, hu.2 i, Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
      · subst hw; simp [mul_comm]
      · intro k _ hk; subst hw
        have : i ≠ Fin.rev k := fun h => hk (by rw [h, Fin.rev_rev])
        simp [this]
      · simp
    · intro j _ hj; rw [Matrix.smul_apply, hi0 j hj]; simp
    · simp

theorem smallModules : Formalism.FourierDecayAlt.A6.SmallModules := by
  intro K _ _ _ R ψ hD hn V hV
  obtain ⟨ϖ, hϖR, hϖ⟩ := hD.unif
  obtain ⟨N, hN⟩ := pow_small hD hn ϖ hϖR hϖ V hV
  have hset : ((Submodule.span R {(ϖ : K) ^ N} : Submodule R K) : Set K) =
      (fun r => (ϖ : K) ^ N * r) '' (R : Set K) := by
    ext x
    simp only [SetLike.mem_coe, Submodule.mem_span_singleton, Set.mem_image]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨(a : K), a.2, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩
  refine ⟨Submodule.span R {(ϖ : K) ^ N}, ⟨?_, ?_⟩, ?_⟩
  · rw [Submodule.coe_toAddSubgroup, hset, image_pow_eq_preimage]
    exact hD.isOpen.preimage (continuous_const.mul continuous_id)
  · rw [Submodule.coe_toAddSubgroup, hset]
    exact hD.isCompact.image (continuous_const.mul continuous_id)
  · rw [hset]
    rintro _ ⟨r, hr, rfl⟩
    exact hN r hr

theorem rootStableExhaustion : Formalism.FourierDecayAlt.A6.Exhaust := by
  intro K _ _ _ R ψ hD hn s hs
  have := hD.t2
  have := hD.artin
  have := hD.red
  obtain ⟨ϖ, hϖR, hϖ⟩ := hD.unif
  have hfin : {ζ : K | ζ ^ s = 1}.Finite := roots_finite s hs 1
  have hOm : ∀ j : ℕ, {z : K | ∀ ζ : K, ζ ^ s = 1 → ζ * z ∈ unitBox R ϖ j} =
      ⋂ ζ ∈ {ζ : K | ζ ^ s = 1}, (fun z => ζ * z) ⁻¹' unitBox R ϖ j := by
    intro j
    ext z
    simp only [Set.mem_iInter, Set.mem_preimage]
    rfl
  have hsub : ∀ j : ℕ, {z : K | ∀ ζ : K, ζ ^ s = 1 → ζ * z ∈ unitBox R ϖ j} ⊆ unitBox R ϖ j := by
    intro j z hz
    have := hz 1 (one_pow s)
    rwa [one_mul] at this
  refine ⟨fun j => {z : K | ∀ ζ : K, ζ ^ s = 1 → ζ * z ∈ unitBox R ϖ j}, ?_, ?_, ?_⟩
  · intro j
    refine ⟨?_, ?_, ?_, ?_⟩
    · beta_reduce
      rw [hOm]
      exact hfin.isOpen_biInter fun ζ _ =>
        (unitBox_isOpen hD hn ϖ hϖR hϖ j).preimage (continuous_const.mul continuous_id)
    · refine (unitBox_isCompact hD ϖ j).of_isClosed_subset ?_ (hsub j)
      beta_reduce
      rw [hOm]
      exact isClosed_biInter fun ζ _ =>
        (unitBox_isCompact hD ϖ j).isClosed.preimage (continuous_const.mul continuous_id)
    · intro z hz
      obtain ⟨y, hzy, _, _⟩ := hsub j hz
      exact IsUnit.of_mul_eq_one y hzy
    · intro z hz ζ hζ ζ' hζ'
      have := hz (ζ' * ζ) (by rw [mul_pow, hζ, hζ', one_mul])
      rwa [mul_assoc] at this
  · intro j z hz ζ hζ
    exact unitBox_mono ϖ hϖR (Nat.le_succ j) (hz ζ hζ)
  · intro z
    have h1 : ∀ ζ : K, ζ ^ s = 1 → ∃ j, ζ * (z : K) ∈ unitBox R ϖ j := by
      intro ζ hζ
      obtain ⟨m₁, h₁⟩ := hϖ (ζ * (z : K))
      obtain ⟨m₂, h₂⟩ := hϖ (ζ ^ (s - 1) * ((z⁻¹ : Kˣ) : K))
      refine ⟨max m₁ m₂, ζ ^ (s - 1) * ((z⁻¹ : Kˣ) : K), ?_, ?_, ?_⟩
      · have : ζ * ζ ^ (s - 1) = 1 := by
          rw [← pow_succ', Nat.sub_add_cancel hs, hζ]
        calc ζ * (z : K) * (ζ ^ (s - 1) * ((z⁻¹ : Kˣ) : K))
            = (ζ * ζ ^ (s - 1)) * ((z : K) * ((z⁻¹ : Kˣ) : K)) := by ring
          _ = 1 := by rw [this, Units.mul_inv, one_mul]
      · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (le_max_left m₁ m₂)
        rw [hk, pow_add, mul_comm ((ϖ : K) ^ m₁), mul_assoc]
        exact R.mul_mem (R.pow_mem hϖR _) h₁
      · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (le_max_right m₁ m₂)
        rw [hk, pow_add, mul_comm ((ϖ : K) ^ m₂), mul_assoc]
        exact R.mul_mem (R.pow_mem hϖR _) h₂
    choose! f hf using h1
    refine ⟨hfin.toFinset.sup f, ?_⟩
    intro ζ hζ
    exact unitBox_mono ϖ hϖR (Finset.le_sup (f := f) (hfin.mem_toFinset.2 hζ)) (hf ζ hζ)

end Formalism.FourierDecayAlt.P
