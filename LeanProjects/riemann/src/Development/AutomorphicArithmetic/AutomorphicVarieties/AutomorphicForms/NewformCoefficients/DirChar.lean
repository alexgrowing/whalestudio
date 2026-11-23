import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.IntOfIntegers

open NumberField IsDedekindDomain Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep

namespace UpperTheory.V.Af.Nf

private theorem dc_inv {M : ℕ} (hM : 1 ≤ M) : algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * M = 1 := by
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hM', map_one]

private theorem dc_uniq {M : ℕ} (hM : 1 ≤ M) {x : Af ℚ} {d e : ℤ} (hd : ∃ y ∈ Ohat ℚ, x - d = M * y)
    (he : ∃ y ∈ Ohat ℚ, x - e = M * y) : (d : ZMod M) = e := by
  obtain ⟨y, hy, hd⟩ := hd
  obtain ⟨z, hz, he⟩ := he
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h1 : algebraMap ℚ (Af ℚ) ((M : ℚ)⁻¹ * ((e : ℚ) - d)) = y - z := by
    rw [map_mul, map_sub, map_intCast, map_intCast]
    linear_combination algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * (hd - he) + (y - z) * dc_inv hM
  obtain ⟨n, hn⟩ := ratAd.2.2 _ (h1 ▸ sub_mem hy hz)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨n, ?_⟩
  rw [inv_mul_eq_iff_eq_mul₀ hM'] at hn
  exact_mod_cast hn

private theorem dc_red {M : ℕ} (hM : 1 ≤ M) : ∃ ρ : ↥(Ohat ℚ) →* ZMod M,
    ∀ (x : ↥(Ohat ℚ)) (d : ℤ), (∃ y ∈ Ohat ℚ, (x : Af ℚ) - d = M * y) → ρ x = d := by
  choose f hf using fun x : ↥(Ohat ℚ) => ratAd.2.1 M hM x x.2
  refine ⟨⟨⟨fun x => f x, ?_⟩, fun a b => ?_⟩, fun x d h => dc_uniq hM (hf x) h⟩
  · have := dc_uniq hM (e := 1) (hf 1) ⟨0, zero_mem _, by simp⟩
    simpa using this
  · obtain ⟨y, hy, h1⟩ := hf a
    obtain ⟨z, hz, h2⟩ := hf b
    have := dc_uniq hM (e := f a * f b) (hf (a * b)) ⟨a * z + f b * y,
      add_mem (mul_mem a.2 hz) (mul_mem (intCast_mem _ _) hy), by
        rw [Subring.coe_mul, Int.cast_mul]
        linear_combination (a : Af ℚ) * h2 + (f b : Af ℚ) * h1⟩
    simpa using this

private noncomputable abbrev pF : Ideles ℚ →* (Af ℚ)ˣ := Units.map (pFin ℚ).toMonoidHom

private noncomputable abbrev pR : Ideles ℚ →* ℝˣ := Units.map (ev.comp (TR.pInf ℚ)).toMonoidHom

private noncomputable abbrev dg : ℚˣ →* Ideles ℚ := Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom

private theorem pR_dg (r : ℚˣ) : (pR (dg r) : ℝ) = ((r : ℚ) : ℝ) :=
  eq_ratCast ((ev.comp (TR.pInf ℚ)).comp (algebraMap ℚ (Ad ℚ))) (r : ℚ)

private theorem pF_dg (r : ℚˣ) : pF (dg r) = Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r := Units.ext rfl

private theorem pF_inf (t : (TR.Rinf ℚ)ˣ) : pF (TR.infId ℚ t) = 1 := by
  refine Units.ext ?_
  change (1 : Af ℚ) - 0 + 0 = 1
  simp

private theorem pR_inf (t : (TR.Rinf ℚ)ˣ) : (pR (TR.infId ℚ t) : ℝ) = t.val Rat.infinitePlace := by
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  change ev (TR.pInf ℚ (1 - TR.sInf ℚ 1 + TR.sInf ℚ t.val)) = ev t.val
  simp [h]

private theorem pF_fin (u : (Af ℚ)ˣ) : pF (finId ℚ u) = u := by
  refine Units.ext ?_
  change (1 : Af ℚ) - 1 + u = u
  simp

private theorem pR_fin (u : (Af ℚ)ˣ) : (pR (finId ℚ u) : ℝ) = 1 := by
  have h : ∀ x, TR.pInf ℚ (sFin ℚ x) = 0 := fun x => map_zero (TR.infEq ℚ).symm
  change ev (TR.pInf ℚ (1 - sFin ℚ 1 + sFin ℚ u.val)) = 1
  simp [h]

private theorem zu_mul {u v : (Af ℚ)ˣ} (hu : IsZU u) (hv : IsZU v) : IsZU (u * v) :=
  ⟨mul_mem hu.1 hv.1, by rw [mul_inv]; exact mul_mem hu.2 hv.2⟩

private theorem zu_one : IsZU 1 := ⟨one_mem _, one_mem _⟩

private noncomputable def PU : Subgroup (Ideles ℚ) where
  carrier := {a | 0 < (pR a : ℝ) ∧ IsZU (pF a)}
  one_mem' := ⟨by rw [map_one]; exact one_pos, by rw [map_one]; exact zu_one⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul]; exact mul_pos ha.1 hb.1, by rw [map_mul]; exact zu_mul ha.2 hb.2⟩
  inv_mem' := fun {a} ha => ⟨by rw [map_inv, Units.val_inv_eq_inv_val]; exact inv_pos.2 ha.1,
    by rw [map_inv]; exact ⟨ha.2.2, ha.2.1⟩⟩

private theorem dc_ker (r : ℚˣ) (h : dg r ∈ PU) : r = 1 := by
  obtain ⟨h0, h1, h2⟩ := h
  rw [pR_dg, Rat.cast_pos] at h0
  obtain ⟨n, hn⟩ := ratAd.2.2 r h1
  obtain ⟨m, hm⟩ := ratAd.2.2 (r⁻¹ : ℚˣ) h2
  have e : n * m = 1 := by
    have := r.mul_inv
    rw [hn, hm] at this
    exact_mod_cast this
  rw [hn] at h0
  have := Int.eq_one_of_mul_eq_one_right (by exact_mod_cast h0.le) e
  exact Units.ext (by rw [hn, this]; rfl)

private theorem dc_surj : Function.Surjective (PU.subtype.coprod dg) := by
  intro a
  obtain ⟨r, u, hr, hu, e⟩ := ratAd.1 (pF a)
  have key : ∀ s : ℚˣ, s * s = 1 → IsZU (pF (dg s)) → 0 < ((s : ℚ) : ℝ) * pR a →
      ∃ p, PU.subtype.coprod dg p = a := fun s hs hz hp => by
    refine ⟨(⟨a * dg (s * r⁻¹), ?_, ?_⟩, s * r), ?_⟩
    · rw [map_mul, Units.val_mul, pR_dg, Units.val_mul, Rat.cast_mul, ← mul_assoc, mul_comm _ (((s : ℚ) : ℝ))]
      refine mul_pos hp ?_
      rw [Units.val_inv_eq_inv_val, Rat.cast_pos]
      exact inv_pos.2 hr
    · have : pF (a * dg (s * r⁻¹)) = u * pF (dg s) := by
        rw [map_mul, e, ← pF_dg, map_mul, map_mul, map_inv, map_inv, mul_comm _ u, mul_comm (pF (dg s)),
          mul_assoc, mul_inv_cancel_left]
      rw [this]
      exact zu_mul hu hz
    · change a * dg (s * r⁻¹) * dg (s * r) = a
      rw [mul_assoc, ← map_mul, mul_mul_mul_comm, hs, inv_mul_cancel, mul_one, map_one, mul_one]
  rcases lt_or_gt_of_ne (pR a).ne_zero with h | h
  · refine key (-1) (by simp) ?_ (by simpa using h)
    have : algebraMap ℚ (Af ℚ) (-1) ∈ Ohat ℚ := by rw [map_neg, map_one]; exact neg_mem (one_mem _)
    exact ⟨this, this⟩
  · exact key 1 (by simp) (by rw [map_one, map_one]; exact zu_one) (by simpa using h)

private theorem dc_nhds {M : ℕ} : ∀ᶠ a : Ideles ℚ in 𝓝 1, a ∈ PU ∧
    algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * ((pF a : Af ℚ) - (1 : ℤ)) ∈ Ohat ℚ := by
  have c1 : Continuous pF := Continuous.units_map _ continuous_snd
  have c2 : Continuous fun a => (pR a : ℝ) :=
    ((InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)).continuous.comp
      ((continuous_apply Rat.infinitePlace).comp continuous_fst)).comp Units.continuous_val
  have c3 : Continuous fun a => (pF a : Af ℚ) := Units.continuous_val.comp c1
  have c4 : Continuous fun a => (((pF a)⁻¹ : (Af ℚ)ˣ) : Af ℚ) := Units.continuous_coe_inv.comp c1
  have c5 : Continuous fun a => algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * ((pF a : Af ℚ) - (1 : ℤ)) :=
    continuous_const.mul (c3.sub continuous_const)
  have h2 : ∀ᶠ a : Ideles ℚ in 𝓝 1, 0 < (pR a : ℝ) := (isOpen_lt continuous_const c2).mem_nhds PU.one_mem.1
  have h3 := (isOpen_Ohat.preimage c3).mem_nhds (x := 1) PU.one_mem.2.1
  have h4 := (isOpen_Ohat.preimage c4).mem_nhds (x := 1) PU.one_mem.2.2
  have h5 := (isOpen_Ohat.preimage c5).mem_nhds (x := 1) (by
    rw [Set.mem_preimage, map_one, Units.val_one, Int.cast_one, sub_self, mul_zero]; exact zero_mem (Ohat ℚ))
  filter_upwards [h2, h3, h4, h5] with a a2 a3 a4 a5
  exact ⟨⟨a2, a3, a4⟩, a5⟩

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.dirChar :
    UpperTheory.V.Af.Nf.DirChar := by
  intro M hM χ
  obtain ⟨ρ, hρ⟩ := dc_red hM
  let j : ↥PU →* ↥(Ohat ℚ) :=
    { toFun := fun p => ⟨pF p, p.2.2.1⟩
      map_one' := Subtype.ext (congrArg Units.val (map_one pF))
      map_mul' := fun a b => Subtype.ext (congrArg Units.val (map_mul pF a.1 b.1)) }
  let ψ : ↥PU →* ℂˣ := (χ.toMonoidHom.comp (ρ.comp j)).toHomUnits
  let φ : ↥PU × ℚˣ →* ℂˣ := ψ⁻¹.comp (MonoidHom.fst _ _)
  have hker : (PU.subtype.coprod dg).ker ≤ φ.ker := fun p hp => by
    have h1 : (p.1 : Ideles ℚ) * dg p.2 = 1 := hp
    have h2 := dc_ker p.2 (by rw [eq_inv_of_mul_eq_one_right h1]; exact PU.inv_mem p.1.2)
    rw [h2, map_one, mul_one] at h1
    change ψ⁻¹ p.1 = 1
    rw [show p.1 = 1 from Subtype.ext h1, map_one]
  let ω : Ideles ℚ →* ℂˣ := MonoidHom.liftOfSurjective _ dc_surj ⟨φ, hker⟩
  have hω : ∀ p, ω (PU.subtype.coprod dg p) = φ p := fun p => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ p
  have hv : ∀ a (ha : a ∈ PU) (d : ℤ), (∃ y ∈ Ohat ℚ, (pF a : Af ℚ) - d = M * y) → (ω a : ℂ) * χ (d : ZMod M) = 1 := by
    intro a ha d hd
    have h1 : ω (a * dg 1) = (ψ ⟨a, ha⟩)⁻¹ := hω (⟨a, ha⟩, 1)
    rw [map_one, mul_one] at h1
    rw [h1, ← hρ (j ⟨a, ha⟩) d hd]
    exact (ψ ⟨a, ha⟩).inv_mul
  have hone : ∀ a (ha : a ∈ PU), (∃ y ∈ Ohat ℚ, (pF a : Af ℚ) - (1 : ℤ) = M * y) → ω a = 1 := fun a ha h => by
    have := hv a ha 1 h
    rw [Int.cast_one, map_one, mul_one] at this
    exact Units.ext this
  refine ⟨⟨ω, continuous_of_continuousAt_one ω ?_, fun k => ?_⟩, fun t ht => ?_, fun u hu d hd => ?_⟩
  · refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
    filter_upwards [dc_nhds (M := M)] with a ha
    exact (hone a ha.1 ⟨_, ha.2, by rw [← mul_assoc, mul_comm (M : Af ℚ), dc_inv hM, one_mul]⟩).symm
  · have h1 : ω (1 * dg k) = ψ⁻¹ 1 := hω (1, k)
    rw [map_one, one_mul] at h1
    exact h1
  · exact hone _ ⟨by rw [pR_inf]; exact ht _, by rw [pF_inf]; exact zu_one⟩
      ⟨0, zero_mem _, by rw [pF_inf]; simp⟩
  · exact hv _ ⟨by rw [pR_fin]; exact one_pos, by rw [pF_fin]; exact hu⟩ d (by rw [pF_fin]; exact hd)
