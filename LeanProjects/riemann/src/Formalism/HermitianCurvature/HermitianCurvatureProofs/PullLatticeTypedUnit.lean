import Formalism.HermitianCurvature.StatementJ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OutsideSystemsBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AxiomsFromFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChebyshevToThreshold

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J

open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.Jx12

theorem mem_idl_shift (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (hg : 0 < g) (k ν : ℤ)
    (y : E) : y ∈ S6.zsub E (S6.idl E g k ν) ↔ (g : E) ^ 2 * y ∈ S6.zsub E (S6.idl E g (k + 2) ν) := by
  have hg0 : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  have key : S6.idl E g (k + 2) ν =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) ((g : E) ^ 2) * S6.idl E g k ν := by
    unfold S6.idl
    rw [zpow_add₀ hg0, ← FractionalIdeal.spanSingleton_mul_spanSingleton, zpow_two, sq]
    ring
  simp only [S6.zsub, Submodule.restrictScalars_mem, FractionalIdeal.mem_coe, key,
    FractionalIdeal.mem_singleton_mul]
  constructor
  · intro hy
    exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    rwa [mul_left_cancel₀ (pow_ne_zero 2 hg0) hzy]

theorem lift_per (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (hg : 0 < g) (ν : ℤ) (s : ℕ)
    (y : E) : y ∈ S6.liftLat E g ν s ↔ (g : E) ^ 2 * y ∈ S6.perLat E g (-ν) s := by
  have h1 : y ∈ S6.zsub E (S6.idl E g (-1) (-ν)) ↔ (g : E) ^ 2 * y ∈ S6.zsub E (S6.idl E g 1 (-ν)) := by
    have h := mem_idl_shift E g hg (-1) (-ν) y
    rwa [show (-1 : ℤ) + 2 = 1 by norm_num] at h
  have h2 : ∀ z : E, z ∈ S6.zsub E (S6.idl E g 0 (-ν)) ↔
      (g : E) ^ 2 * z ∈ S6.zsub E (S6.idl E g 2 (-ν)) := fun z => by
    have h := mem_idl_shift E g hg 0 (-ν) z
    rwa [zero_add] at h
  have hφ : (LinearMap.id - ((-1 : ℤ) ^ s) • S6.conjZ E : E →ₗ[ℤ] E) ((g : E) ^ 2 * y) =
      (g : E) ^ 2 * (LinearMap.id - ((-1 : ℤ) ^ s) • S6.conjZ E : E →ₗ[ℤ] E) y := by
    show (g : E) ^ 2 * y - ((-1 : ℤ) ^ s) • (IsCMField.complexConj E) ((g : E) ^ 2 * y) =
      (g : E) ^ 2 * (y - ((-1 : ℤ) ^ s) • (IsCMField.complexConj E) y)
    rw [map_mul, map_pow, map_natCast, zsmul_eq_mul, zsmul_eq_mul]
    ring
  unfold S6.liftLat S6.perLat S6.twLat
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_comap, hφ, h1, h2]

end Formalism.FourierDecayAlt.P.Jx12

namespace Formalism.FourierDecayAlt.P

private lemma unit_mul_mem_iff' {M : Type} [CommRing M] (R : Subring M) (c : Mˣ) (hc : (c : M) ∈ R)
    (hci : ((c⁻¹ : Mˣ) : M) ∈ R) (x : M) : (c : M) * x ∈ R ↔ x ∈ R := by
  constructor
  · intro h
    have h' := R.mul_mem hci h
    rwa [Units.inv_mul_cancel_left] at h'
  · intro h
    exact R.mul_mem hc h

private lemma mul_unit_mul_mem_iff {M : Type} [CommRing M] (R : Subring M) (c : Mˣ) (hc : (c : M) ∈ R)
    (hci : ((c⁻¹ : Mˣ) : M) ∈ R) (x y : M) : x * (c : M) * y ∈ R ↔ x * y ∈ R := by
  rw [show x * (c : M) * y = (c : M) * (x * y) by ring]
  exact unit_mul_mem_iff' R c hc hci _

theorem pull_lattice_typed_unit : Formalism.FourierDecayAlt.J.PullLatticeTypedUnit := by
  intro hT E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ R u c α ψ η Θ hR hc hci hu t
  refine Iff.trans ?_ (Formalism.FourierDecayAlt.P.pull_lattice_typed hT E g ν s hg hpd P hP hgP K o σ hσ R
    (c⁻¹ * u) α ψ η Θ hR (by rw [Units.val_mul, hu, Units.inv_mul_cancel_left]) t)
  show (u : K × K) * _ ∈ R ↔ ((c⁻¹ * u : (K × K)ˣ) : K × K) * _ ∈ R
  rw [hu, Units.val_mul, hu, Units.inv_mul_cancel_left, mul_assoc]
  exact unit_mul_mem_iff' R c hc hci _

theorem pull_lift_typed : Formalism.FourierDecayAlt.J.PullLiftTyped := by
  intro hT E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ R u α ψ η Θ hR hu x
  have h0 := Formalism.FourierDecayAlt.P.pull_lattice_typed hT E g (-ν) s hg hpd P hP hgP K o σ hσ R u α ψ η Θ
    hR hu ((g : E) ^ 2 * x)
  have hloc : (g : E) ^ 2 * x ∈ S6.locAt E P (S6.perLat E g (-ν) s) ↔
      x ∈ S6.locAt E P (S6.liftLat E g ν s) := by
    simp only [S6.locAt, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, ha, h⟩
      refine ⟨a, ha, (Formalism.FourierDecayAlt.P.Jx12.lift_per E g hg ν s _).2 ?_⟩
      rwa [mul_left_comm]
    · rintro ⟨a, ha, h⟩
      refine ⟨a, ha, ?_⟩
      have h' := (Formalism.FourierDecayAlt.P.Jx12.lift_per E g hg ν s _).1 h
      rwa [mul_left_comm] at h'
  refine Iff.trans ?_ (h0.trans hloc)
  have hg' : (g : K) ≠ 0 := by
    intro h
    apply Units.ne_zero u
    rw [hu, h, inv_zero, mul_zero]
    rfl
  have hs2 : ((-1 : K) ^ s) * (-1) ^ s = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hgg : (g : K)⁻¹ * (g : K)⁻¹ * (g : K) ^ 2 = 1 := by field_simp
  have hinv : ((u⁻¹ : (K × K)ˣ) : K × K) = (u : K × K) * (g : K × K) ^ 2 := by
    rw [Units.val_inv_eq_inv_val]
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [hu]
    ext
    · simp only [Prod.fst_mul, Prod.pow_fst, Prod.fst_natCast, Prod.fst_one]
      linear_combination hgg
    · simp only [Prod.snd_mul, Prod.pow_snd, Prod.snd_natCast, Prod.snd_one]
      linear_combination ((g : K)⁻¹ * (g : K)⁻¹ * (g : K) ^ 2) * hs2 + hgg
  show ((u⁻¹ : (K × K)ˣ) : K × K) * (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) x ∈ R ↔
    (u : K × K) * (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) ((g : E) ^ 2 * x) ∈ R
  rw [hinv, map_mul, map_pow, map_natCast, mul_assoc]

theorem pull_lift_typed_unit : Formalism.FourierDecayAlt.J.PullLiftTypedUnit := by
  intro hT E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ R u c α ψ η Θ hR hc hci hu x
  refine Iff.trans ?_ (pull_lift_typed hT E g ν s hg hpd P hP hgP K o σ hσ R (c⁻¹ * u) α ψ η Θ hR
    (by rw [Units.val_mul, hu, Units.inv_mul_cancel_left]) x)
  show ((u⁻¹ : (K × K)ˣ) : K × K) * _ ∈ R ↔ (((c⁻¹ * u)⁻¹ : (K × K)ˣ) : K × K) * _ ∈ R
  rw [mul_inv_rev, inv_inv, Units.val_mul]
  exact (mul_unit_mul_mem_iff R c hc hci _ _).symm

private lemma isPSD_comp_of_isPSD_image {X Y : Type} {inst : DecidableEq Y} (F : Finset X) (η : X → Y)
    (k : Y → Y → ℂ) (hk : A5.IsPSD (F.image η) k) : A5.IsPSD F (fun h h' => k (η h) (η h')) := by
  intro a
  have hmap : ∀ x ∈ F, η x ∈ F.image η := fun x hx => Finset.mem_image_of_mem η hx
  have key : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y) =
      ∑ p ∈ F.image η, ∑ q ∈ F.image η,
        (∑ x ∈ F.filter (fun x => η x = p), a x) * conj (∑ y ∈ F.filter (fun y => η y = q), a y) *
          k p q := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => enter [2, q]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun q _ => ?_
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [(Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy).2]
  have hk' := hk (fun p => ∑ x ∈ F.filter (fun x => η x = p), a x)
  beta_reduce at hk' ⊢
  rw [key]
  exact hk'

theorem top_is_local_kernel : Formalism.FourierDecayAlt.J.TopIsLocalKernel := by
  intro K _ R ψ E α _ m σ u τ₀ η Θ hΘ t c hc h h' hh hh'
  have e : (topSys R ψ σ u τ₀ η Θ).N t t h h' = Θ ((u : K) * σ t - τ₀) (η h) (η h') := by
    simp [topSys]
  rw [e, ← hc]
  exact hΘ c (η h) (η h') hh hh'

open Classical in

theorem top_unit_heads : Formalism.FourierDecayAlt.J.TopUnitHeads := by
  intro hAg hN0 K _ _ _ R ψ hLD E α _ m σ u τ₀ η F Θ hm hG hτ hA t
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => by
    have h1 := (hLD.selfDual 1).2 R.one_mem
    simpa using h1 r hr
  have h7 := hA.2.2.2.2.2.2 (by
      intro p hp
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hp
      exact hG h hh) ((u : K) * σ t - τ₀)
  have hmem : ((u : K) * σ t - τ₀ ∈ R) ↔ t ∈ (topSys R ψ σ u τ₀ η Θ).L := by
    show _ ↔ (u : K) * σ t ∈ R
    constructor
    · intro h
      simpa using R.add_mem h hτ
    · intro h
      exact R.sub_mem h hτ
  have hpull := isPSD_comp_of_isPSD_image F η _ h7
  have hF : A5.IsPSD F (fun h h' => (if t ∈ (topSys R ψ σ u τ₀ η Θ).L then (1 : ℂ) else 0) -
      (topSys R ψ σ u τ₀ η Θ).N t t h h') := by
    intro a
    have e : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((if t ∈ (topSys R ψ σ u τ₀ η Θ).L then (1 : ℂ) else 0) -
        (topSys R ψ σ u τ₀ η Θ).N t t x y) =
        ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * ((if (u : K) * σ t - τ₀ ∈ R then A5.N0 R ψ (η x) (η y) else 0) -
          Θ ((u : K) * σ t - τ₀) (η x) (η y)) := by
      refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
      have hN : (topSys R ψ σ u τ₀ η Θ).N t t x y = Θ ((u : K) * σ t - τ₀) (η x) (η y) := by
        simp [topSys]
      have h1 : A5.N0 R ψ (η x) (η y) = 1 :=
        hN0 K R ψ hψ (η x) (η y) ((hm x hx).trans (hm y hy).symm) (hG x hx) (hG y hy)
      simp only [hN, h1, hmem]
    have hp := hpull a
    beta_reduce at hp ⊢
    rw [e]
    exact hp
  exact ((hAg α F _).1.trans (hAg α F _).2.symm).2 hF

theorem diagonal_phase_conj : Formalism.FourierDecayAlt.J.DiagPhase := by
  classical
  intro α F k d hk
  unfold TB.PSDOn at hk ⊢
  have h := Matrix.PosSemidef.mul_mul_conjTranspose_same hk (Matrix.diagonal fun x : F => d x)
  convert h using 1
  ext x y
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_conjTranspose] <;> ring

theorem block_diagonal_psd : Formalism.FourierDecayAlt.J.BlockDiagPSD := by
  classical
  intro α β _ F c k hb
  unfold TB.PSDOn at hb ⊢
  let Fb : β → Finset α := fun b => F.filter fun x => c x = b
  let Q : ∀ b, Matrix F (Fb b) ℂ := fun b => Matrix.of fun x z => if (x : α) = (z : α) then 1 else 0
  have hQM : ∀ b (x : F) (w : Fb b),
      (Q b * Matrix.of (fun x y : Fb b => k x y)) x w = if c x = b then k x w else 0 := by
    intro b x w
    rw [Matrix.mul_apply]
    simp only [Q, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_coe_sort (Fb b) (fun z => if (x : α) = z then k z w else 0), Finset.sum_ite_eq]
    simp [Fb, x.2]
  have hA : ∀ b (x y : F), (Q b * Matrix.of (fun x y : Fb b => k x y) * Matrix.conjTranspose (Q b)) x y =
      if c x = b ∧ c y = b then k x y else 0 := by
    intro b x y
    rw [Matrix.mul_apply]
    simp only [hQM, Matrix.conjTranspose_apply, Q, Matrix.of_apply, apply_ite star, star_one, star_zero,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_coe_sort (Fb b) (fun w => if (y : α) = w then (if c x = b then k x w else 0) else 0),
      Finset.sum_ite_eq]
    by_cases hx : c x = b <;> by_cases hy : c y = b <;> simp [Fb, hx, hy, y.2]
  have hsum : (Matrix.of fun x y : F => if c x = c y then k x y else 0) =
      ∑ b ∈ F.image c, Q b * Matrix.of (fun x y : Fb b => k x y) * Matrix.conjTranspose (Q b) := by
    ext x y
    rw [Matrix.sum_apply]
    simp only [hA, Matrix.of_apply]
    rw [Finset.sum_eq_single (c x)]
    · by_cases h : c x = c y
      · simp [h]
      · simp [h, Ne.symm h]
    · intro b _ hb'
      simp [Ne.symm hb']
    · intro h
      exact absurd (Finset.mem_image_of_mem c x.2) h
  beta_reduce
  rw [hsum]
  exact Matrix.posSemidef_sum _ fun b _ => (hb b).mul_mul_conjTranspose_same (Q b)

end Formalism.FourierDecayAlt.P
