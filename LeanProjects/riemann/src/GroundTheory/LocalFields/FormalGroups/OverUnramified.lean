import Mathlib
import GroundTheory.LocalFields.FormalGroups.FrobeniusTwist
import GroundTheory.LocalFields.FormalGroups.TwistedLift

namespace GroundTheory.LocalField.FormalGroup

open MvPowerSeries IsLocalRing

theorem powerSeries_constantCoeff_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : PowerSeries R) :
    PowerSeries.constantCoeff (PowerSeries.map φ f) = φ (PowerSeries.constantCoeff f) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem pair_eq_substEach {R : Type*} [CommRing R] (k : PowerSeries R) :
    (![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) k,
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) k] : Fin 2 → MvPowerSeries (Fin 2) R) =
      substEach k := by
  funext i
  fin_cases i <;> rfl

namespace Hom

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {F G : FormalGroup R}

noncomputable def map (h : Hom F G) : Hom (F.map φ) (G.map φ) where
  toPowerSeries := PowerSeries.map φ h.toPowerSeries
  constantCoeff_eq_zero := by
    rw [powerSeries_constantCoeff_map, h.constantCoeff_eq_zero, map_zero]
  map_add := by
    have := congrArg (MvPowerSeries.map φ) h.map_add
    rw [pair_eq_substEach, PowerSeries.map_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
      MvPowerSeries.map_subst (hasSubst_substEach h.constantCoeff_eq_zero)] at this
    rw [pair_eq_substEach, FormalGroup.map_toPowerSeries, FormalGroup.map_toPowerSeries, this]
    congr 1
    funext i
    exact map_substEach φ _ i

theorem map_toPowerSeries (h : Hom F G) :
    (h.map φ).toPowerSeries = PowerSeries.map φ h.toPowerSeries :=
  rfl

end Hom

section Fixed

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (σ : B →ₐ[A] B)

theorem map_sigma_map_algebraMap {ι : Type*} (Φ : MvPowerSeries ι A) :
    MvPowerSeries.map (σ : B →+* B) (MvPowerSeries.map (algebraMap A B) Φ) =
      MvPowerSeries.map (algebraMap A B) Φ := by
  ext n
  simp [coeff_map]

theorem powerSeries_map_sigma_map_algebraMap (f : PowerSeries A) :
    PowerSeries.map (σ : B →+* B) (PowerSeries.map (algebraMap A B) f) =
      PowerSeries.map (algebraMap A B) f :=
  map_sigma_map_algebraMap σ f

theorem map_C_mul_X {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a : R) :
    MvPowerSeries.map φ (PowerSeries.C a * PowerSeries.X : PowerSeries R) =
      PowerSeries.C (φ a) * PowerSeries.X := by
  change PowerSeries.map φ (PowerSeries.C a * PowerSeries.X) = _
  simp

theorem coeff_one_C_mul_X {R : Type*} [CommRing R] (a : R) :
    PowerSeries.coeff 1 (PowerSeries.C a * PowerSeries.X) = a := by
  simp

theorem constantCoeff_C_mul_X {R : Type*} [CommRing R] (a : R) :
    constantCoeff (PowerSeries.C a * PowerSeries.X : MvPowerSeries Unit R) = 0 := by
  change PowerSeries.constantCoeff (PowerSeries.C a * PowerSeries.X) = 0
  simp

theorem C_unit_eq {R : Type*} [CommRing R] (a : R) :
    (MvPowerSeries.C a : MvPowerSeries Unit R) = PowerSeries.C a :=
  rfl

end Fixed

section Hypotheses

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (ResidueField A)]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  (σ : B →ₐ[A] B)

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] in

theorem bijective_twistOp [IsAdicComplete (maximalIdeal B) B] {π : A}
    (hπB : Irreducible (algebraMap A B π)) {v : B} (hv : IsUnit v) {d : ℕ} (hd : 2 ≤ d) :
    Function.Bijective (twistOp (σ : B →+* B) v (algebraMap A B π) d) := by
  set ϖ := algebraMap A B π
  have hσc : ∀ x, (σ : B →+* B) x = σ x := fun _ => rfl
  have hσϖ : ∀ (n : ℕ) (t : B), σ (ϖ ^ n * t) = ϖ ^ n * σ t := by
    intro n t
    rw [map_mul, map_pow, AlgHom.commutes]
  have hadd : ∀ x y, twistOp (σ : B →+* B) v ϖ d x - twistOp (σ : B →+* B) v ϖ d y =
      twistOp (σ : B →+* B) v ϖ d (x - y) := by
    intro x y
    simp only [twistOp, map_sub]
    ring
  have hpow : ϖ ^ (d - 1) = ϖ ^ (d - 2) * ϖ := by
    rw [← pow_succ]
    congr 1
    omega
  constructor
  · intro x y hxy
    rw [← sub_eq_zero]
    by_contra hz0
    have hz : v * (x - y) = ϖ ^ (d - 1) * σ (x - y) := by
      have := hadd x y
      rw [hxy, sub_self] at this
      simp only [twistOp, hσc] at this
      linear_combination -this
    obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz0 hπB
    rw [hw, map_mul, map_pow, AlgHom.commutes] at hz
    have h1 : v * w = ϖ ^ (d - 1) * σ w :=
      mul_right_cancel₀ (pow_ne_zero n hπB.ne_zero) (by linear_combination hz)
    have hunit : IsUnit (ϖ ^ (d - 1) * σ w) := h1 ▸ hv.mul w.isUnit
    have hdvd : ϖ ∣ ϖ ^ (d - 1) * σ w := by
      rw [hpow, mul_assoc]
      exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
    exact hπB.not_isUnit (isUnit_of_dvd_unit hdvd hunit)
  · intro c
    obtain ⟨x, hx, -⟩ := exists_eq_zero_of_approx (maximalIdeal B)
      (fun x => twistOp (σ : B →+* B) v ϖ d x - c)
      (fun n x y hxy => by
        rw [mem_maximalIdeal_pow_iff hπB] at hxy ⊢
        obtain ⟨t, ht⟩ := hxy
        refine ⟨v * t - ϖ ^ (d - 1) * σ t, ?_⟩
        have : x = y + ϖ ^ n * t := by rw [← ht]; ring
        simp only [twistOp, hσc, this, map_add, hσϖ]
        ring)
      (fun n x hx => by
        rw [mem_maximalIdeal_pow_iff hπB] at hx
        obtain ⟨w, hw⟩ := hx
        obtain ⟨v', hv'⟩ := hv.exists_right_inv
        refine ⟨x - ϖ ^ n * (v' * w), ?_, ?_⟩
        · rw [mem_maximalIdeal_pow_iff hπB]
          exact ⟨-(v' * w), by ring⟩
        · rw [mem_maximalIdeal_pow_iff hπB]
          refine ⟨ϖ ^ (d - 2) * σ (v' * w), ?_⟩
          simp only [twistOp, hσc, map_sub, hσϖ] at hw ⊢
          linear_combination hw - ϖ ^ n * w * hv' + ϖ ^ n * σ (v' * w) * hpow)
      (m := 0) (x₀ := 0) (by simp)
    exact ⟨x, sub_eq_zero.1 hx⟩

omit [Finite (ResidueField A)] in

theorem map_residue_map_eq_X_pow {π : A} (hmem : algebraMap A B π ∈ maximalIdeal B)
    {f : PowerSeries A} (hf : IsLubinTateSeries π f) :
    PowerSeries.map (residue B) (PowerSeries.map (algebraMap A B) f) =
      PowerSeries.X ^ Nat.card (ResidueField A) := by
  ext n
  obtain ⟨c, hc⟩ := hf.dvd_coeff_sub n
  rw [map_sub] at hc
  have h1 : PowerSeries.coeff n f =
      PowerSeries.coeff n (PowerSeries.X ^ Nat.card (ResidueField A) : PowerSeries A) + π * c := by
    rw [← hc]
    ring
  have h0 : residue B (algebraMap A B π) = 0 := (residue_eq_zero_iff _).2 hmem
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, h1, map_add, map_add, map_mul, map_mul, h0,
    zero_mul, add_zero, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
  split_ifs <;> simp

variable (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))
include hunr hσ

theorem dvd_coeff_twistedDefect {π : A} (hπB : Irreducible (algebraMap A B π)) {u : A}
    {f g : PowerSeries A} (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries (u * π) g)
    {ι : Type*} [Finite ι] (φ : MvPowerSeries ι B) (e : ι →₀ ℕ) :
    algebraMap A B π ∣ coeff e (twistedDefect (σ : B →+* B) (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) f) φ) := by
  classical
  have := isLocalHom_of_map_maximalIdeal hunr
  let := Fintype.ofFinite (ResidueField A)
  obtain ⟨p, hcp, n, hp, hcard⟩ := FiniteField.card' (ResidueField A)
  have := hcp
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (ResidueField B) p :=
    CharP.of_ringHom_of_ne_zero (ResidueField.map (algebraMap A B)) p hp.ne_zero
  have hq : Nat.card (ResidueField A) = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hq0 : p ^ (n : ℕ) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hmemf : algebraMap A B π ∈ maximalIdeal B :=
    (mem_maximalIdeal _).2 hπB.not_isUnit
  have hmemg : algebraMap A B (u * π) ∈ maximalIdeal B := by
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ hmemf
  have hf0 : PowerSeries.constantCoeff (PowerSeries.map (algebraMap A B) f) = 0 := by
    rw [powerSeries_constantCoeff_map, hf.constantCoeff_eq_zero, map_zero]
  have hcomp : (residue B).comp (σ : B →+* B) =
      (iterateFrobenius (ResidueField B) p n).comp (residue B) := by
    ext x
    simp only [RingHom.comp_apply, iterateFrobenius_def]
    rw [← hq]
    exact hσ x
  rw [← residue_eq_zero_iff_dvd hπB, ← coeff_map]
  set ψ := MvPowerSeries.map (residue B) (dropConst φ)
  have hs : PowerSeries.HasSubst (dropConst φ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_dropConst φ)
  have hs' : PowerSeries.HasSubst ψ := PowerSeries.HasSubst.of_constantCoeff_zero (by
    rw [constantCoeff_map, constantCoeff_dropConst, map_zero])
  have hE := hasSubst_substEach (σ := ι) hf0
  have hmapE : (fun i => MvPowerSeries.map (residue B)
      (substEach (PowerSeries.map (algebraMap A B) f) i : MvPowerSeries ι B)) =
      fun i => X i ^ (p ^ (n : ℕ)) := by
    funext i
    rw [map_substEach, substEach_apply, map_residue_map_eq_X_pow hmemf hf,
      PowerSeries.subst_pow (PowerSeries.HasSubst.X i),
      PowerSeries.subst_X (PowerSeries.HasSubst.X i), hq]
  have hfrob : MvPowerSeries.map (residue B) (MvPowerSeries.map (σ : B →+* B) (dropConst φ)) =
      MvPowerSeries.map (iterateFrobenius (ResidueField B) p n) ψ := by
    ext d
    simp only [coeff_map, ψ]
    exact RingHom.congr_fun hcomp _
  have h3 : subst (fun i => (X i : MvPowerSeries ι (ResidueField B)) ^ (p ^ (n : ℕ)))
      (MvPowerSeries.map (iterateFrobenius (ResidueField B) p n) ψ) =
      MvPowerSeries.map (iterateFrobenius (ResidueField B) p n)
        (subst (fun i => (X i : MvPowerSeries ι (ResidueField B)) ^ (p ^ (n : ℕ))) ψ) := by
    rw [map_subst (HasSubst.X_pow hq0)]
    simp only [map_pow, map_X]
  have h4 := map_iterateFrobenius_expand p hp.ne_zero ψ n
  simp only [expand, coe_substAlgHom] at h4
  rw [twistedDefect, map_sub, map_subst hE, PowerSeries.map_subst hs,
    map_residue_map_eq_X_pow hmemg hg, PowerSeries.subst_pow hs', PowerSeries.subst_X hs', hmapE,
    hfrob, h3, h4, hq, sub_self, map_zero]

end Hypotheses

section Main

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (ResidueField A)]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [IsAlgClosed (ResidueField B)] [IsAdicComplete (maximalIdeal B) B]
  (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
  (σ : B →ₐ[A] B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))
  {π : A} (hπ : Irreducible π) (u : Aˣ) {f g : PowerSeries A}
  (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries (u * π) g)

include hunr hσ hπ hf hg

omit [IsAlgClosed (ResidueField B)] in

theorem isTwistedLift_unique {ι : Type*} [Finite ι] {ℓ φ ψ : MvPowerSeries ι B}
    (hφ : IsTwistedLift (σ : B →+* B) (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) f) ℓ φ)
    (hψ : IsTwistedLift (σ : B →+* B) (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) f) ℓ ψ) : φ = ψ := by
  have hπB := irreducible_algebraMap hunr hπ
  refine hφ.unique (σ : B →+* B) (u := algebraMap A B u) (π := algebraMap A B π)
    (by rw [powerSeries_constantCoeff_map, hf.constantCoeff_eq_zero, map_zero])
    (by rw [PowerSeries.coeff_map, hf.coeff_one])
    (by rw [powerSeries_constantCoeff_map, hg.constantCoeff_eq_zero, map_zero])
    (by rw [PowerSeries.coeff_map, hg.coeff_one, map_mul])
    (fun x hx => (mul_eq_zero.1 hx).resolve_left hπB.ne_zero)
    (fun d hd => bijective_twistOp σ hπB (u.isUnit.map (algebraMap A B)) hd)
    (fun φ e => dvd_coeff_twistedDefect σ hunr hσ hπB hf hg φ e) hψ

omit [IsAlgClosed (ResidueField B)] in

theorem exists_isTwistedLift {ε : B} (hε : σ ε = algebraMap A B u * ε) :
    ∃ θ : PowerSeries B, IsTwistedLift (σ : B →+* B) (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) f) (PowerSeries.C ε * PowerSeries.X) θ := by
  have hπB := irreducible_algebraMap hunr hπ
  have hσc : ∀ x, (σ : B →+* B) x = σ x := fun _ => rfl
  have hℓ0 : constantCoeff (PowerSeries.C ε * PowerSeries.X : MvPowerSeries Unit B) = 0 := by
    change PowerSeries.constantCoeff (PowerSeries.C ε * PowerSeries.X) = 0
    simp
  obtain ⟨θ, ⟨h2, he⟩, -⟩ := existsUnique_twisted (σ : B →+* B) (ι := Unit)
    (u := algebraMap A B u) (π := algebraMap A B π)
    (by rw [powerSeries_constantCoeff_map, hf.constantCoeff_eq_zero, map_zero])
    (by rw [PowerSeries.coeff_map, hf.coeff_one])
    (by rw [powerSeries_constantCoeff_map, hg.constantCoeff_eq_zero, map_zero])
    (by rw [PowerSeries.coeff_map, hg.coeff_one, map_mul])
    (fun x hx => (mul_eq_zero.1 hx).resolve_left hπB.ne_zero)
    (fun d hd => bijective_twistOp σ hπB (u.isUnit.map (algebraMap A B)) hd)
    (fun φ e => dvd_coeff_twistedDefect σ hunr hσ hπB hf hg φ e) hℓ0 (fun e he => by
      have hd' : e = Finsupp.single () (e ()) := by ext; simp
      rw [hd', Finsupp.degree_single] at he
      rw [hd', he]
      change algebraMap A B u * algebraMap A B π * PowerSeries.coeff 1
          (PowerSeries.C ε * PowerSeries.X) =
        algebraMap A B π * σ (PowerSeries.coeff 1 (PowerSeries.C ε * PowerSeries.X))
      rw [coeff_one_C_mul_X, hε]
      ring)
  have h2' : (2 : ℕ∞) ≤ order ((PowerSeries.C ε * PowerSeries.X : MvPowerSeries Unit B) - θ) := by
    rw [← neg_sub, order_neg]
    exact h2
  exact ⟨θ, constantCoeff_eq_zero_of_two_le_order_sub h2' hℓ0, h2, he⟩

theorem exists_iso_lubinTateFormalGroup :
    ∃ θ : Iso ((lubinTateFormalGroup hπ hf).map (algebraMap A B))
        ((lubinTateFormalGroup ((irreducible_units_mul u).2 hπ) hg).map (algebraMap A B)),
      IsUnit (PowerSeries.coeff 1 θ.hom.toPowerSeries) ∧
      σ (PowerSeries.coeff 1 θ.hom.toPowerSeries) =
        algebraMap A B u * PowerSeries.coeff 1 θ.hom.toPowerSeries ∧
      PowerSeries.map (σ : B →+* B) θ.hom.toPowerSeries =
        PowerSeries.subst (PowerSeries.map (algebraMap A B) (lubinTateHom hπ hf hf u).toPowerSeries)
          θ.hom.toPowerSeries ∧
      (∀ a : A, θ.hom.comp ((lubinTateHom hπ hf hf a).map (algebraMap A B)) =
        ((lubinTateHom ((irreducible_units_mul u).2 hπ) hg hg a).map (algebraMap A B)).comp
          θ.hom) ∧
      PowerSeries.subst θ.hom.toPowerSeries (PowerSeries.map (algebraMap A B) g) =
        PowerSeries.subst (PowerSeries.map (algebraMap A B) f)
          (PowerSeries.map (σ : B →+* B) θ.hom.toPowerSeries) := by
  have hπ' : Irreducible (u * π) := (irreducible_units_mul u).2 hπ
  have hπB := irreducible_algebraMap hunr hπ
  have hσc : ∀ x, (σ : B →+* B) x = σ x := fun _ => rfl
  have hf0B : PowerSeries.constantCoeff (PowerSeries.map (algebraMap A B) f) = 0 := by
    rw [powerSeries_constantCoeff_map, hf.constantCoeff_eq_zero, map_zero]
  have hg0B : PowerSeries.constantCoeff (PowerSeries.map (algebraMap A B) g) = 0 := by
    rw [powerSeries_constantCoeff_map, hg.constantCoeff_eq_zero, map_zero]

  obtain ⟨η, hη⟩ := exists_units_eq_mul σ hσ hπB (Units.map (algebraMap A B : A →* B) u)
  set ε : B := (η : B)
  have hε : σ ε = algebraMap A B u * ε := by simpa using hη

  obtain ⟨θ, hθ⟩ := exists_isTwistedLift hunr σ hσ hπ u hf hg hε
  have hθ0 : PowerSeries.constantCoeff θ = 0 := hθ.1
  have hθ1 : PowerSeries.coeff 1 θ = ε := by
    have := eq_coeff_of_two_le_order_sub hθ.2.1 (e := Finsupp.single () 1) (by simp)
    change PowerSeries.coeff 1 θ = PowerSeries.coeff 1 (PowerSeries.C ε * PowerSeries.X) at this
    rw [this, coeff_one_C_mul_X]

  have hL : MvPowerSeries.map (algebraMap A B) (sum₂ (![1, 1] : Fin 2 → A)) =
      X 0 + X 1 := by
    rw [linearForm_fin_two]
    simp
  have hFf : IsLubinTateLift (PowerSeries.map (algebraMap A B) f)
      (PowerSeries.map (algebraMap A B) f) (X 0 + X 1)
      (MvPowerSeries.map (algebraMap A B) (lubinTateFormalGroup hπ hf).toPowerSeries) := by
    rw [← hL]
    exact (isLubinTateLift_lubinTateLift hπ hf hf _).map (algebraMap A B) hf.constantCoeff_eq_zero
  have hFg : IsLubinTateLift (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) g) (X 0 + X 1)
      (MvPowerSeries.map (algebraMap A B) (lubinTateFormalGroup hπ' hg).toPowerSeries) := by
    rw [← hL]
    exact (isLubinTateLift_lubinTateLift hπ' hg hg _).map (algebraMap A B) hg.constantCoeff_eq_zero
  have hHom : ∀ {h h' : PowerSeries A} (hh : IsLubinTateSeries π h) (hh' : IsLubinTateSeries π h')
      (hπ₀ : Irreducible π) (a : A), IsLubinTateLift (PowerSeries.map (algebraMap A B) h)
        (PowerSeries.map (algebraMap A B) h') (PowerSeries.C (algebraMap A B a) * PowerSeries.X)
        (PowerSeries.map (algebraMap A B) (lubinTateHom hπ₀ hh hh' a).toPowerSeries) := by
    intro h h' hh hh' hπ₀ a
    rw [← map_C_mul_X]
    exact (isLubinTateLift_lubinTateHom hπ₀ hh hh' a).map (algebraMap A B) hh'.constantCoeff_eq_zero
  have hHom' : ∀ a : A, IsLubinTateLift (PowerSeries.map (algebraMap A B) g)
        (PowerSeries.map (algebraMap A B) g) (PowerSeries.C (algebraMap A B a) * PowerSeries.X)
        (PowerSeries.map (algebraMap A B) (lubinTateHom hπ' hg hg a).toPowerSeries) := by
    intro a
    rw [← map_C_mul_X]
    exact (isLubinTateLift_lubinTateHom hπ' hg hg a).map (algebraMap A B) hg.constantCoeff_eq_zero
  have uniq := fun {ι : Type} [Finite ι] {ℓ φ ψ : MvPowerSeries ι B} hφ hψ =>
    isTwistedLift_unique hunr σ hσ hπ u hf hg (ℓ := ℓ) (φ := φ) (ψ := ψ) hφ hψ

  have hX : ∀ j : Fin 2, IsTwistedLift (σ : B →+* B) (PowerSeries.map (algebraMap A B) g)
      (PowerSeries.map (algebraMap A B) f) (C ε * X j)
      (PowerSeries.subst (X j : MvPowerSeries (Fin 2) B) θ) := by
    intro j
    have := hθ.comp_lift (σ : B →+* B) hf0B hf0B (v := fun _ : Unit => (X j : MvPowerSeries (Fin 2) B))
      (u := fun _ => X j) (fun _ => isLubinTateLift_X hf0B j) (fun _ => map_X _ _)
    rwa [← PowerSeries.subst_def, ← PowerSeries.subst_def,
      powerSeries_subst_C_mul_X (PowerSeries.HasSubst.X j)] at this
  have hD := hθ.comp_lift (σ : B →+* B) hf0B hf0B
    (v := fun _ : Unit => (X 0 + X 1 : MvPowerSeries (Fin 2) B))
    (u := fun _ => MvPowerSeries.map (algebraMap A B) (lubinTateFormalGroup hπ hf).toPowerSeries)
    (fun _ => hFf) (fun _ => map_sigma_map_algebraMap σ _)
  rw [← PowerSeries.subst_def, ← PowerSeries.subst_def,
    powerSeries_subst_C_mul_X (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))] at hD
  have hE := IsLubinTateLift.comp_twisted (σ : B →+* B) hf0B hg0B hFg
    (map_sigma_map_algebraMap σ _)
    (w := ![C ε * X 0, C ε * X 1])
    (v := ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) B) θ,
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) B) θ])
    (fun j => by fin_cases j <;> simpa using hX _)
  have hs2 : HasSubst (![C ε * X 0, C ε * X 1] : Fin 2 → MvPowerSeries (Fin 2) B) :=
    hasSubst_pair (by simp) (by simp)
  rw [subst_add hs2, subst_X hs2, subst_X hs2] at hE
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    at hE
  rw [← mul_add] at hE
  have hDE := uniq hD hE
  let θh : Hom ((lubinTateFormalGroup hπ hf).map (algebraMap A B))
      ((lubinTateFormalGroup hπ' hg).map (algebraMap A B)) :=
    { toPowerSeries := θ
      constantCoeff_eq_zero := hθ0
      map_add := by
        rw [FormalGroup.map_toPowerSeries, FormalGroup.map_toPowerSeries, hDE] }
  let θi := Iso.ofIsUnit θh (by
    change IsUnit (PowerSeries.coeff 1 θ)
    rw [hθ1]
    exact η.isUnit)
  refine ⟨θi, ?_, ?_, ?_, ?_, ?_⟩
  · change IsUnit (PowerSeries.coeff 1 θ)
    rw [hθ1]
    exact η.isUnit
  · change σ (PowerSeries.coeff 1 θ) = _ * PowerSeries.coeff 1 θ
    rw [hθ1, hε]
  ·
    change PowerSeries.map (σ : B →+* B) θ = PowerSeries.subst _ θ
    have h1 := hθ.map (σ : B →+* B) hf0B (powerSeries_map_sigma_map_algebraMap σ f)
      (powerSeries_map_sigma_map_algebraMap σ g)
    have h2 := hθ.comp_lift (σ : B →+* B) hf0B hf0B
      (v := fun _ : Unit => PowerSeries.C (algebraMap A B u) * PowerSeries.X)
      (u := fun _ => PowerSeries.map (algebraMap A B) (lubinTateHom hπ hf hf u).toPowerSeries)
      (fun _ => hHom hf hf hπ u) (fun _ => map_sigma_map_algebraMap σ _)
    rw [← PowerSeries.subst_def, ← PowerSeries.subst_def,
      powerSeries_subst_C_mul_X (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_C_mul_X _))] at h2
    rw [map_C_mul_X, hσc, hε] at h1
    rw [C_unit_eq, ← mul_assoc, ← map_mul, mul_comm ε] at h2
    exact uniq h1 h2
  ·
    intro a
    apply Hom.ext
    rw [Hom.toPowerSeries_comp, Hom.toPowerSeries_comp, Hom.map_toPowerSeries,
      Hom.map_toPowerSeries]
    change PowerSeries.subst _ θ = PowerSeries.subst θ _
    have h1 := hθ.comp_lift (σ : B →+* B) hf0B hf0B
      (v := fun _ : Unit => PowerSeries.C (algebraMap A B a) * PowerSeries.X)
      (u := fun _ => PowerSeries.map (algebraMap A B) (lubinTateHom hπ hf hf a).toPowerSeries)
      (fun _ => hHom hf hf hπ a) (fun _ => map_sigma_map_algebraMap σ _)
    have h2 := IsLubinTateLift.comp_twisted (σ : B →+* B) hf0B hg0B (hHom' a)
      (map_sigma_map_algebraMap σ _)
      (w := fun _ : Unit => PowerSeries.C ε * PowerSeries.X) (v := fun _ => θ) (fun _ => hθ)
    rw [← PowerSeries.subst_def, ← PowerSeries.subst_def,
      powerSeries_subst_C_mul_X (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_C_mul_X _))] at h1
    rw [← PowerSeries.subst_def, ← PowerSeries.subst_def,
      powerSeries_subst_C_mul_X (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_C_mul_X _))] at h2
    rw [C_unit_eq] at h1 h2
    have e : PowerSeries.C ε * (PowerSeries.C (algebraMap A B a) * PowerSeries.X) =
        PowerSeries.C (algebraMap A B a) * (PowerSeries.C ε * PowerSeries.X) := by ring
    rw [e] at h1
    exact uniq h1 h2
  ·
    change PowerSeries.subst θ _ = PowerSeries.subst _ (PowerSeries.map (σ : B →+* B) θ)
    rw [hθ.2.2, subst_substEach_unit]
    rfl

end Main

end GroundTheory.LocalField.FormalGroup
