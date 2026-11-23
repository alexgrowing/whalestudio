import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Descent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.WCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsNE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatLam

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.CG

section Alg

variable {K : Type} [Field K] {Δ τ : K}

private theorem ofE_mul (x y : Etau K τ) : ofE Δ (x * y) = ofE Δ x * ofE Δ y := by ext <;> simp [ofE]
private theorem ofE_add (x y : Etau K τ) : ofE Δ (x + y) = ofE Δ x + ofE Δ y := by ext <;> simp [ofE]
private theorem ofE_smul (k : K) (x : Etau K τ) : ofE Δ (k • x) = k • ofE Δ x := by ext <;> simp [ofE]
private theorem ofE_one : ofE Δ (1 : Etau K τ) = 1 := by
  ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
private theorem ofE_omega : ofE Δ (ω : Etau K τ) = ω := by
  ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
private theorem ofE_star (x : Etau K τ) : star (ofE Δ x) = ofE Δ (star x) := by ext <;> simp [ofE]
private theorem sigL_ofE (x : Etau K τ) : sigL (ofE Δ x) = ofE Δ x := by ext <;> simp [ofE, sigL]
private theorem sigL_mul (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL] <;> ring
private theorem sigL_smul (k : Lsq K Δ) (y : EL Δ τ) : sigL (k • y) = star k • sigL y := by
  ext <;> simp [sigL] <;> ring
private theorem sigL_sigL (x : EL Δ τ) : sigL (sigL x) = x := by ext <;> simp [sigL]
private theorem star_smulL (k : Lsq K Δ) (y : EL Δ τ) : star (k • y) = k • star y := by
  ext <;> simp <;> ring
private theorem trace_ofE (x : Etau K τ) :
    QuadraticAlgebra.trace (ofE Δ x) = algebraMap K (Lsq K Δ) (QuadraticAlgebra.trace x) := by
  simp [ofE, trace_def, map_ofNat]
private theorem ofE_mul_star (x : Etau K τ) : ofE Δ x * star (ofE Δ x) = QuadraticAlgebra.norm x • (1 : EL Δ τ) := by
  rw [ofE_star, ← ofE_mul, ← algebraMap_norm_eq_mul_star, Algebra.algebraMap_eq_smul_one, ofE_smul, ofE_one]
private theorem ofE_inv (y : (Etau K τ)ˣ) : ofE Δ ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) * ofE Δ (y : Etau K τ) = 1 := by
  rw [← ofE_mul, Units.inv_mul, ofE_one]

private theorem herm_add (c : K) (m : EL Δ τ) (x y z : Sp Δ τ) : herm c m (x + y) z = herm c m x z + herm c m y z := by
  simp only [herm, Prod.fst_add, Prod.snd_add, mul_add, add_mul, map_add]; ring
private theorem herm_smul (c : K) (m : EL Δ τ) (k : Lsq K Δ) (x y : Sp Δ τ) : herm c m (k • x) y = k * herm c m x y := by
  simp only [herm, Prod.smul_fst, Prod.smul_snd, mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]; ring
private theorem herm_smul' (c : K) (m : EL Δ τ) (k : Lsq K Δ) (x y : Sp Δ τ) :
    herm c m x (k • y) = star k * herm c m x y := by
  simp only [herm, Prod.smul_fst, Prod.smul_snd, sigL_smul, star_smulL, mul_smul_comm, map_smul, smul_eq_mul, star_mul']
  ring

private theorem h90E (h2 : (2 : K) ≠ 0) (β : (Etau K τ)ˣ) (hβ : QuadraticAlgebra.norm (β : Etau K τ) = 1) :
    ∃ z : (Etau K τ)ˣ, z * star z⁻¹ = β ∨ z * star z⁻¹ = -β := by
  have key : ∀ β : (Etau K τ)ˣ, QuadraticAlgebra.norm (β : Etau K τ) = 1 →
      QuadraticAlgebra.norm (1 + β : Etau K τ) ≠ 0 → ∃ z : (Etau K τ)ˣ, z * star z⁻¹ = β := by
    intro β hβ hn
    have hu : IsUnit (1 + β : Etau K τ) := isUnit_iff_norm_isUnit.2 (Ne.isUnit hn)
    refine ⟨hu.unit, ?_⟩
    rw [star_inv, mul_inv_eq_iff_eq_mul]
    ext1
    have := algebraMap_norm_eq_mul_star (β : Etau K τ)
    rw [hβ, map_one] at this
    simp only [IsUnit.unit_spec, Units.val_mul, Units.coe_star, star_add, star_one]
    linear_combination this
  by_cases hn : QuadraticAlgebra.norm (1 + β : Etau K τ) = 0
  · obtain ⟨z, hz⟩ := key (-β) (by simpa using hβ) (by
      intro h
      apply mul_ne_zero h2 h2
      simp only [norm_def, re_add, im_add, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, Units.val_neg, re_neg,
        im_neg] at hn h hβ
      linear_combination hn + h - 2 * hβ)
    exact ⟨z, Or.inr hz⟩
  · obtain ⟨z, hz⟩ := key β hβ hn
    exact ⟨z, Or.inl hz⟩

end Alg

section Int

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {Δ τ : K}

private theorem int_of (a : O) : IsInt O (algebraMap K (Lsq K Δ) (algebraMap O K a)) := by
  rw [← IsScalarTower.algebraMap_apply]; exact isIntegral_algebraMap

private theorem int_star {y : Lsq K Δ} (hy : IsInt O y) : IsInt O (star y) := by
  let φ : Lsq K Δ →ₐ[O] Lsq K Δ :=
    { starRingEnd (Lsq K Δ) with
      commutes' := fun r => by
        change star (algebraMap O (Lsq K Δ) r) = _
        rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
        ext <;> simp }
  exact hy.map φ

variable (O) in

private def IB (x : EL Δ τ) : Prop := IsInt O x.re ∧ IsInt O x.im

private theorem IB.mul (hτ : τ ∈ (algebraMap O K).range) {x y : EL Δ τ} (hx : IB O x) (hy : IB O y) : IB O (x * y) := by
  obtain ⟨a, rfl⟩ := hτ
  exact ⟨(hx.1.mul hy.1).add ((isIntegral_one.neg.mul hx.2).mul hy.2),
    ((hx.1.mul hy.2).add (hx.2.mul hy.1)).add (((int_of a).mul hx.2).mul hy.2)⟩

private theorem IB.smul {k : Lsq K Δ} (hk : IsInt O k) {y : EL Δ τ} (hy : IB O y) : IB O (k • y) :=
  ⟨hk.mul hy.1, hk.mul hy.2⟩

private theorem IB.smulO (a : O) {y : EL Δ τ} (hy : IB O y) : IB O (algebraMap O K a • y) := by
  rw [← algebraMap_smul (Lsq K Δ)]; exact hy.smul (int_of a)

private theorem IB.neg {y : EL Δ τ} (hy : IB O y) : IB O (-y) := ⟨hy.1.neg, hy.2.neg⟩

private theorem IB.sig {y : EL Δ τ} (hy : IB O y) : IB O (sigL y) := ⟨int_star hy.1, int_star hy.2⟩

private theorem IB.star (hτ : τ ∈ (algebraMap O K).range) {y : EL Δ τ} (hy : IB O y) : IB O (star y) := by
  obtain ⟨a, rfl⟩ := hτ
  exact ⟨hy.1.add ((int_of a).mul hy.2), hy.2.neg⟩

private theorem IB.tr (hτ : τ ∈ (algebraMap O K).range) {y : EL Δ τ} (hy : IB O y) :
    IsInt O (QuadraticAlgebra.trace y) := by
  obtain ⟨a, rfl⟩ := hτ
  rw [trace_def, two_mul]
  exact (hy.1.add hy.1).add ((int_of a).mul hy.2)

private theorem IB.ofE {y : Etau K τ} (h1 : y.re ∈ (algebraMap O K).range) (h2 : y.im ∈ (algebraMap O K).range) :
    IB O (ofE Δ y) := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  exact ⟨by simpa [Loc.ofE, ← ha] using int_of a, by simpa [Loc.ofE, ← hb] using int_of b⟩

private theorem int_unit (u : Oˣ) {x : Lsq K Δ} (h : IsInt O (algebraMap K (Lsq K Δ) (algebraMap O K u) * x)) :
    IsInt O x := by
  have := (int_of ((u⁻¹ : Oˣ) : O)).mul h
  rwa [← mul_assoc, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one, one_mul] at this

private theorem IB.unit (u : Oˣ) {x : EL Δ τ} (h : IB O (algebraMap O K u • x)) : IB O x := by
  have := h.smulO ((u⁻¹ : Oˣ) : O)
  rwa [smul_smul, ← map_mul, Units.inv_mul, map_one, one_smul] at this

private theorem IB.of_tr (hτ : τ ∈ (algebraMap O K).range) (u : Oˣ) (hu : algebraMap O K u = τ ^ 2 - 4) {y : EL Δ τ}
    (h1 : IsInt O (QuadraticAlgebra.trace y)) (h2 : IsInt O (QuadraticAlgebra.trace (ω * y))) : IB O y := by
  obtain ⟨a, ha⟩ := hτ
  have hi : IsInt O (algebraMap K (Lsq K Δ) τ) := ha ▸ int_of a
  refine ⟨int_unit u ?_, int_unit u ?_⟩
  · convert (((hi.mul hi).sub (isIntegral_one.add isIntegral_one)).mul h1).sub (hi.mul h2) using 1
    rw [hu]
    simp only [trace_def, re_mul, im_mul, omega_re, omega_im, map_sub, map_pow, map_ofNat]
    ring
  · convert (h2.add h2).sub (hi.mul h1) using 1
    rw [hu]
    simp only [trace_def, re_mul, im_mul, omega_re, omega_im, map_sub, map_pow, map_ofNat]
    ring

variable (O Δ) in

private def lat (r : K) (y : (Etau K τ)ˣ) : Set (Sp Δ τ) :=
  {x | IsInt O (algebraMap K (Lsq K Δ) r * x.1) ∧ IB O (ofE Δ ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x.2)}

private theorem tor_lat (r : K) (y z : (Etau K τ)ˣ) : tor Δ z '' lat O Δ r y = lat O Δ r (z * star z⁻¹ * y) := by
  generalize hq : z * star z⁻¹ = q
  have hq' : quo z = q := by rw [← hq]; rfl
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨hx.1, ?_⟩
    convert hx.2 using 1
    simp only [tor, hq', mul_inv, Units.val_mul, ofE_mul]
    linear_combination (ofE Δ ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x.2) * ofE_inv (Δ := Δ) q
  · intro hx
    refine ⟨(x.1, ofE Δ ((q⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x.2), ⟨hx.1, ?_⟩, ?_⟩
    · convert hx.2 using 1
      simp only [mul_inv, Units.val_mul, ofE_mul]
      ring
    · refine Prod.ext rfl ?_
      simp only [tor, hq']
      linear_combination x.2 * ofE_inv (Δ := Δ) q

private theorem lat_unit (hτ : τ ∈ (algebraMap O K).range) (r : K) (y w : (Etau K τ)ˣ) (h : IB O (ofE Δ (w : Etau K τ)))
    (h' : IB O (ofE Δ ((w⁻¹ : (Etau K τ)ˣ) : Etau K τ))) : lat O Δ r (w * y) = lat O Δ r y := by
  ext x
  refine and_congr_right fun _ => ⟨fun hx => ?_, fun hx => ?_⟩
  · convert h.mul hτ hx using 1
    simp only [mul_inv, Units.val_mul, ofE_mul]
    linear_combination (-ofE Δ ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x.2) * ofE_inv (Δ := Δ) w
  · convert h'.mul hτ hx using 1
    simp only [mul_inv, Units.val_mul, ofE_mul]
    ring

end Int

section Lat

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {Δ τ : K}

private theorem herm_lat {c r t : K} {e v : Oˣ} (hc : c = algebraMap O K e * r ^ 2) {y : (Etau K τ)ˣ}
    (hv : algebraMap O K v = t * QuadraticAlgebra.norm (y : Etau K τ)) (x w : Sp Δ τ) :
    herm c (t • (1 : EL Δ τ)) x w =
      algebraMap K (Lsq K Δ) (algebraMap O K e) * (algebraMap K (Lsq K Δ) r * x.1 * star (algebraMap K (Lsq K Δ) r * w.1)) +
      algebraMap K (Lsq K Δ) (algebraMap O K v) * QuadraticAlgebra.trace (ofE Δ ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x.2 *
        star (sigL (ofE Δ ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w.2))) := by
  have e1 : star (algebraMap K (Lsq K Δ) r) = algebraMap K (Lsq K Δ) r := by ext <;> simp
  have h1 := ofE_inv (Δ := Δ) y
  have h2 := congrArg star h1
  rw [star_mul', star_one] at h2
  unfold herm
  congr 1
  · rw [hc, star_mul', e1, map_mul, map_pow]; ring
  · rw [← smul_eq_mul (algebraMap K (Lsq K Δ) _), ← map_smul, algebraMap_smul, hv, mul_smul,
      ← one_mul (ofE Δ ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x.2 * _), ← smul_mul_assoc (QuadraticAlgebra.norm (y : Etau K τ)),
      ← ofE_mul_star, sigL_mul, sigL_ofE, star_mul', mul_assoc, smul_mul_assoc, one_mul]
    congr 2
    linear_combination (-(x.2 * star (sigL w.2)) * (star (ofE Δ ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ)) *
      star (ofE Δ (y : Etau K τ)))) * h1 - (x.2 * star (sigL w.2)) * h2

private theorem lat_dual (hτ : τ ∈ (algebraMap O K).range) (u : Oˣ) (hu : algebraMap O K u = τ ^ 2 - 4)
    {c r t : K} {e v : Oˣ} (hr : r ≠ 0) (hc : c = algebraMap O K e * r ^ 2) {y : (Etau K τ)ˣ}
    (hv : algebraMap O K v = t * QuadraticAlgebra.norm (y : Etau K τ)) (w : Sp Δ τ) :
    w ∈ lat O Δ r y ↔ ∀ x ∈ lat O Δ r y, IsInt O (herm c (t • (1 : EL Δ τ)) x w) := by
  constructor
  · intro hw x hx
    rw [herm_lat hc hv]
    exact ((int_of _).mul (hx.1.mul (int_star hw.1))).add
      ((int_of _).mul ((hx.2.mul hτ (hw.2.sig.star hτ)).tr hτ))
  · intro h
    have z0 : IB O (0 : EL Δ τ) := ⟨isIntegral_zero, isIntegral_zero⟩
    have e1 : algebraMap K (Lsq K Δ) r * algebraMap K (Lsq K Δ) r⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hr, map_one]
    have k : ∀ b : EL Δ τ, IB O b → IsInt O (QuadraticAlgebra.trace
        (b * star (sigL (ofE Δ ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w.2)))) := fun b hb => by
      have := h (0, ofE Δ (y : Etau K τ) * b)
        ⟨by simpa using isIntegral_zero, by simpa only [← mul_assoc, ofE_inv, one_mul] using hb⟩
      rw [herm_lat hc hv] at this
      simp only [mul_zero, zero_mul, zero_add, ← mul_assoc, ofE_inv, one_mul] at this
      exact int_unit v this
    constructor
    · have := h (algebraMap K (Lsq K Δ) r⁻¹, 0) ⟨by simpa only [e1] using isIntegral_one, by simpa using z0⟩
      rw [herm_lat hc hv] at this
      simp only [mul_zero, zero_mul, map_zero, add_zero, e1, one_mul] at this
      simpa only [star_star] using int_star (int_unit e this)
    · have := IB.of_tr hτ u hu (by simpa only [one_mul] using k 1 ⟨isIntegral_one, isIntegral_zero⟩)
        (k ω ⟨isIntegral_zero, isIntegral_one⟩)
      simpa only [star_star, sigL_sigL] using (this.star hτ).sig

private theorem lat_stab (hτ : τ ∈ (algebraMap O K).range) (r : K) (y : (Etau K τ)ˣ) {d d' : EL Δ τ} (hd : IB O d)
    (hd' : IB O d') (hdd : d' * d = 1) : semi d '' lat O Δ r y = lat O Δ r y := by
  have e1 : star (algebraMap K (Lsq K Δ) r) = algebraMap K (Lsq K Δ) r := by ext <;> simp
  have k : ∀ d : EL Δ τ, IB O d → ∀ x ∈ lat O Δ r y, semi d x ∈ lat O Δ r y := fun d hd x hx => by
    refine ⟨by simpa only [star_mul', e1, semi] using int_star hx.1, ?_⟩
    convert hd.mul hτ hx.2.sig using 1
    simp only [semi, sigL_mul, sigL_ofE]
    ring
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact k d hd x hx
  · intro hx
    refine ⟨_, k _ hd'.sig x hx, Prod.ext (star_star _) ?_⟩
    simp only [semi, sigL_mul, sigL_sigL]
    linear_combination x.2 * hdd

private theorem lat_fg [IsDomain O] [IsDiscreteValuationRing O] (hl : IsLoc O Δ) {r : K} (hr : r ≠ 0) (y : (Etau K τ)ˣ) :
    ∃ s : Finset (Sp Δ τ), lat O Δ r y = Submodule.span O (s : Set (Sp Δ τ)) := by
  obtain ⟨ε, s₀, hs₀, hΔ⟩ := hl.even
  have hε : Δ * s₀⁻¹ ^ 2 = algebraMap O K ε := by rw [hΔ]; field_simp
  have hD := descent O K Δ hl s₀⁻¹ ε hε
  let R : Submodule O (Lsq K Δ) := Submodule.span O {1, ⟨0, s₀⁻¹⟩}
  have hR : ∀ x, x ∈ R ↔ IsInt O x := fun x => by
    rw [(hD x).1, Submodule.mem_span_pair]
    constructor
    · rintro ⟨a, b, rfl⟩
      exact ⟨⟨a, by simp [Algebra.algebraMap_eq_smul_one, QuadraticAlgebra.re_one]⟩, b,
        by simp [Algebra.algebraMap_eq_smul_one, QuadraticAlgebra.im_one]⟩
    · rintro ⟨⟨a, ha⟩, b, hb⟩
      exact ⟨a, b, by
        ext <;> simp [Algebra.algebraMap_eq_smul_one, ← ha, hb, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]⟩
  have hfg : R.FG := Submodule.fg_span (Set.toFinite _)
  let f : (Lsq K Δ × Lsq K Δ × Lsq K Δ) →ₗ[Lsq K Δ] Sp Δ τ :=
    { toFun := fun p => (algebraMap K (Lsq K Δ) r⁻¹ * p.1, ofE Δ (y : Etau K τ) * (p.2.1 • 1 + p.2.2 • ω))
      map_add' := fun p q => Prod.ext (by simp [mul_add]) (by simp only [Prod.fst_add, Prod.snd_add, add_smul]; ring)
      map_smul' := fun k p => Prod.ext (by simp only [Prod.smul_fst, smul_eq_mul, RingHom.id_apply]; ring)
        (by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply, mul_smul, ← smul_add, mul_smul_comm]) }
  obtain ⟨s, hs⟩ := (hfg.prod (hfg.prod hfg)).map (f.restrictScalars O)
  refine ⟨s, ?_⟩
  rw [hs]
  have e1 : algebraMap K (Lsq K Δ) r * algebraMap K (Lsq K Δ) r⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hr, map_one]
  ext x
  constructor
  · intro hx
    refine ⟨(_, _, _), ⟨(hR _).2 hx.1, (hR _).2 hx.2.1, (hR _).2 hx.2.2⟩, Prod.ext ?_ ?_⟩
    · change algebraMap K (Lsq K Δ) r⁻¹ * (algebraMap K (Lsq K Δ) r * x.1) = x.1
      linear_combination x.1 * e1
    · have : ∀ b : EL Δ τ, b.re • (1 : EL Δ τ) + b.im • ω = b := fun b => by
        ext1 <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
      change ofE Δ (y : Etau K τ) * ((ofE Δ ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x.2).re • 1 +
        (ofE Δ ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) * x.2).im • ω) = x.2
      rw [this]
      linear_combination x.2 * ofE_inv (Δ := Δ) y
  · rintro ⟨⟨a, b, b'⟩, ⟨ha, hb, hb'⟩, rfl⟩
    constructor
    · change IsInt O (algebraMap K (Lsq K Δ) r * (algebraMap K (Lsq K Δ) r⁻¹ * a))
      rw [← mul_assoc, e1, one_mul]
      exact (hR _).1 ha
    · change IB O (_ * (ofE Δ (y : Etau K τ) * (b • 1 + b' • ω)))
      rw [← mul_assoc, ofE_inv, one_mul]
      exact ⟨by simpa [QuadraticAlgebra.re_one] using (hR _).1 hb, by simpa [QuadraticAlgebra.im_one] using (hR _).1 hb'⟩

end Lat

section Fix

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {Δ τ : K} {c : K} {d d' m : EL Δ τ} {S : Set (Sp Δ τ)}

private theorem fx_add (hS : IsFix O c d m S) {x y : Sp Δ τ} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S := by
  obtain ⟨s, rfl⟩ := hS.fg
  exact Submodule.add_mem _ hx hy

private theorem fx_smul (hS : IsFix O c d m S) {k : Lsq K Δ} (hk : IsInt O k) {y : Sp Δ τ} (hy : y ∈ S) : k • y ∈ S :=
  (hS.dual _).2 fun x hx => by
    rw [herm_smul']
    exact (int_star hk).mul ((hS.dual _).1 hy x hx)

private theorem fx_semi (hS : IsFix O c d m S) {y : Sp Δ τ} (hy : y ∈ S) : semi d y ∈ S :=
  hS.stab ▸ ⟨y, hy, rfl⟩

private theorem fx_N (hS : IsFix O c d m S) (hd : d * sigL d = ω) {y : Sp Δ τ} (hy : y ∈ S) : (y.1, ω * y.2) ∈ S := by
  convert fx_semi hS (fx_semi hS hy) using 1
  refine Prod.ext (star_star _).symm ?_
  simp only [semi, sigL_mul, sigL_sigL, ← hd, mul_assoc]

private theorem fx_split (hS : IsFix O c d m S) (hd : d * sigL d = ω) (hτ : τ ∈ (algebraMap O K).range) (u : Oˣ)
    (hu : algebraMap O K u = 2 - τ) {y : Sp Δ τ} (hy : y ∈ S) : (y.1, 0) ∈ S ∧ (0, y.2) ∈ S := by
  obtain ⟨a, ha⟩ := hτ
  have hi : IsInt O (algebraMap K (Lsq K Δ) τ) := ha ▸ int_of a
  have h1 : (y.1, 0) ∈ S := by
    convert fx_smul hS (int_of ((u⁻¹ : Oˣ) : O))
      (fx_add hS (fx_add hS (fx_N hS hd (fx_N hS hd hy)) (fx_smul hS hi.neg (fx_N hS hd hy))) hy) using 1
    have e : algebraMap K (Lsq K Δ) (algebraMap O K ((u⁻¹ : Oˣ) : O)) * (2 - algebraMap K (Lsq K Δ) τ) = 1 := by
      rw [← map_ofNat (algebraMap K (Lsq K Δ)) 2, ← map_sub, ← hu, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    refine Prod.ext ?_ ?_
    · simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul]
      linear_combination (-y.1) * e
    · have : ω * (ω * y.2) + -algebraMap K (Lsq K Δ) τ • (ω * y.2) + y.2 = 0 := by
        ext1 <;> simp [Algebra.smul_def] <;> ring
      simp only [Prod.smul_snd, Prod.snd_add, this, smul_zero]
  refine ⟨h1, ?_⟩
  convert fx_add hS hy (fx_smul hS isIntegral_one.neg h1) using 1
  ext1 <;> simp

private theorem fx_B (hS : IsFix O c d m S) (hd : d * sigL d = ω) {b x : EL Δ τ} (hb : IB O b)
    (hx : ((0, x) : Sp Δ τ) ∈ S) : ((0, b * x) : Sp Δ τ) ∈ S := by
  convert fx_add hS (fx_smul hS hb.1 hx) (fx_smul hS hb.2 (fx_N hS hd hx)) using 1
  refine Prod.ext (by simp) ?_
  ext1 <;> simp <;> ring

private theorem fx_sig (hS : IsFix O c d m S) (hd : d * sigL d = ω) (hd' : IB O d') (hdd : d' * d = 1) {x : EL Δ τ}
    (hx : ((0, x) : Sp Δ τ) ∈ S) : ((0, sigL x) : Sp Δ τ) ∈ S := by
  have h := fx_semi hS hx
  simp only [semi, star_zero] at h
  simpa only [← mul_assoc, hdd, one_mul] using fx_B hS hd hd' h

private theorem fx_dec [IsDomain O] [IsDiscreteValuationRing O] (hl : IsLoc O Δ) (hS : IsFix O c d m S)
    (hd : d * sigL d = ω) (hd' : IB O d') (hdd : d' * d = 1) {x : EL Δ τ} (hx : ((0, x) : Sp Δ τ) ∈ S) :
    ∃ (δ : Lsq K Δ) (x₁ x₂ : Etau K τ), IsInt O δ ∧ ((0, ofE Δ x₁) : Sp Δ τ) ∈ S ∧ ((0, ofE Δ x₂) : Sp Δ τ) ∈ S ∧
      x = ofE Δ x₁ + δ • ofE Δ x₂ := by
  obtain ⟨ε, s₀, hs₀, hΔ⟩ := hl.even
  have hε : Δ * s₀⁻¹ ^ 2 = algebraMap O K ε := by rw [hΔ]; field_simp
  generalize s₀⁻¹ = s at hε
  have hδ : IsInt O (⟨0, s⟩ : Lsq K Δ) := (descent O K Δ hl s ε hε _).1.2 ⟨zero_mem _, 1, by simp⟩
  obtain ⟨u, hu⟩ := hl.two
  have hu' : algebraMap O K (u⁻¹ : Oˣ) * 2 = 1 := by
    rw [← map_ofNat (algebraMap O K) 2, ← hu, ← map_mul, Units.inv_mul, map_one]
  have hε' : algebraMap O K (ε⁻¹ : Oˣ) * (Δ * s ^ 2) = 1 := by
    rw [hε, ← map_mul, Units.inv_mul, map_one]
  have i1 := int_of (Δ := Δ) (K := K) ((u⁻¹ : Oˣ) : O)
  have i2 := int_of (Δ := Δ) (K := K) ((ε⁻¹ : Oˣ) : O)
  generalize algebraMap O K (u⁻¹ : Oˣ) = h at hu' i1
  generalize algebraMap O K (ε⁻¹ : Oˣ) = e at hε' i2
  have hσ := fx_sig hS hd hd' hdd hx
  refine ⟨⟨0, s⟩, ⟨x.re.re, x.im.re⟩, ⟨e * Δ * s * x.re.im, e * Δ * s * x.im.im⟩, hδ, ?_, ?_, ?_⟩
  · convert fx_smul hS i1 (fx_add hS hx hσ) using 1
    refine Prod.ext (by simp) ?_
    ext <;> simp [ofE, sigL]
    · linear_combination (-x.re.re) * hu'
    · linear_combination (-x.im.re) * hu'
  · convert fx_smul hS ((hδ.mul i2).mul i1) (fx_add hS hx (fx_smul hS isIntegral_one.neg hσ)) using 1
    refine Prod.ext (by simp) ?_
    ext <;> simp [ofE, sigL]
    · linear_combination (-e * Δ * s * x.re.im) * hu'
    · linear_combination (-e * Δ * s * x.im.im) * hu'
  · ext <;> simp [ofE]
    · linear_combination (-x.re.im) * hε'
    · linear_combination (-x.im.im) * hε'

private theorem herm_E (c t k : K) (a y : Etau K τ) :
    herm c (t • (1 : EL Δ τ)) (0, ofE Δ a) (0, k • ofE Δ y) =
      algebraMap K (Lsq K Δ) (k * (t * QuadraticAlgebra.trace (a * star y))) := by
  rw [herm, ← ofE_smul, sigL_ofE, ofE_star, ← ofE_one, ← ofE_smul, ← ofE_mul, ← ofE_mul, trace_ofE]
  simp only [mul_zero, zero_mul, zero_add]
  congr 1
  simp [trace_def, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  ring

private theorem fx_gen [IsDomain O] [IsDiscreteValuationRing O] (hl : IsLoc O Δ) {t : K} (hS : IsFix O c d (t • 1) S)
    (hd : d * sigL d = ω) (hd' : IB O d') (hdd : d' * d = 1) (hτ : τ ∈ (algebraMap O K).range) (u : Oˣ)
    (hu : algebraMap O K u = 2 - τ) :
    ∃ (y : (Etau K τ)ˣ) (v : Oˣ), algebraMap O K v = t * QuadraticAlgebra.norm (y : Etau K τ) ∧
      ((0, ofE Δ (y : Etau K τ)) : Sp Δ τ) ∈ S := by
  haveI := hl.frac
  by_contra hne
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ0 : algebraMap O K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hπ.ne_zero
  have k1 : ∀ y : Etau K τ, ((0, ofE Δ y) : Sp Δ τ) ∈ S →
      ∃ a : O, t * QuadraticAlgebra.norm y = algebraMap O K π * algebraMap O K a := fun y hy => by
    have h := (hS.dual _).1 hy _ hy
    have e := herm_E (Δ := Δ) c t 1 y y
    rw [one_smul, ← algebraMap_norm_eq_mul_star, trace_algebraMap] at e
    obtain ⟨w, hw⟩ := hl.two
    have h' : IsInt O (algebraMap K (Lsq K Δ) (t * QuadraticAlgebra.norm y)) := by
      refine int_unit w ?_
      rw [← map_mul, hw, map_ofNat]
      convert e ▸ h using 2
      ring
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      ((isIntegral_algebraMap_iff (algebraMap K (Lsq K Δ)).injective).mp h')
    by_cases hau : IsUnit a
    · have hn : QuadraticAlgebra.norm y ≠ 0 := fun h0 => (hau.map (algebraMap O K)).ne_zero (by rw [ha, h0, mul_zero])
      have hyu : IsUnit y := isUnit_iff_norm_isUnit.2 (Ne.isUnit hn)
      exact absurd ⟨hyu.unit, hau.unit, ha, hy⟩ hne
    · have : a ∈ Ideal.span {π} := hπ.maximalIdeal_eq ▸ hau
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 this
      exact ⟨b, by rw [← ha, map_mul]⟩
  have k2 : ∀ x y : Etau K τ, ((0, ofE Δ x) : Sp Δ τ) ∈ S → ((0, ofE Δ y) : Sp Δ τ) ∈ S →
      IsInt O (herm c (t • (1 : EL Δ τ)) (0, ofE Δ x) (0, (algebraMap O K π)⁻¹ • ofE Δ y)) := fun x y hx hy => by
    obtain ⟨a, ha⟩ := k1 x hx
    obtain ⟨b, hb⟩ := k1 y hy
    obtain ⟨e, he⟩ := k1 (x + y) (by simpa [ofE_add] using fx_add hS hx hy)
    rw [herm_E]
    convert int_of (e - a - b) using 2
    rw [inv_mul_eq_iff_eq_mul₀ hπ0, map_sub, map_sub]
    simp only [norm_def, trace_def, re_add, im_add, re_mul, im_mul, re_star, im_star] at ha hb he ⊢
    linear_combination he - ha - hb
  have k3 : ∀ y : Etau K τ, ((0, ofE Δ y) : Sp Δ τ) ∈ S → ((0, (algebraMap O K π)⁻¹ • ofE Δ y) : Sp Δ τ) ∈ S :=
    fun y hy => (hS.dual _).2 fun x hx => by
      obtain ⟨δ, x₁, x₂, hδ, h1, h2, e⟩ := fx_dec hl hS hd hd' hdd (fx_split hS hd hτ u hu hx).2
      have := (k2 x₁ y h1 hy).add (hδ.mul (k2 x₂ y h2 hy))
      rw [← herm_smul, ← herm_add] at this
      convert this using 1
      simp [herm, e]
  have k4 : ∀ x : EL Δ τ, ((0, x) : Sp Δ τ) ∈ S → ((0, (algebraMap O K π)⁻¹ • x) : Sp Δ τ) ∈ S := fun x hx => by
    obtain ⟨δ, x₁, x₂, hδ, h1, h2, e⟩ := fx_dec hl hS hd hd' hdd hx
    convert fx_add hS (k3 _ h1) (fx_smul hS hδ (k3 _ h2)) using 1
    refine Prod.ext (by simp) ?_
    simp only [e, smul_add, Prod.snd_add, Prod.smul_snd, smul_comm δ]
  obtain ⟨s, hs⟩ := hS.fg
  let N : Submodule O (EL Δ τ) := (Submodule.span O (s : Set (Sp Δ τ))).map (LinearMap.snd O _ _)
  have hN : ∀ x, x ∈ N ↔ ((0, x) : Sp Δ τ) ∈ S := fun x => by
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (fx_split hS hd hτ u hu (hs ▸ hy)).2
    · intro hx
      exact ⟨_, hs ▸ hx, rfl⟩
  have hbot : N = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O) N
      (Submodule.FG.map _ ⟨s, rfl⟩) (fun x hx => ?_) (IsLocalRing.maximalIdeal_le_jacobson _)
    have := Submodule.smul_mem_smul (I := IsLocalRing.maximalIdeal O) (r := π) hπ.not_isUnit
      ((hN _).2 (k4 x ((hN x).1 hx)))
    rwa [← algebraMap_smul K π, smul_smul, mul_inv_cancel₀ hπ0, one_smul] at this
  have h1 : (1 : EL Δ τ) ∈ N := (hN _).2 ((hS.dual _).2 fun x hx => by
    have : x.2 ∈ N := (hN _).2 (fx_split hS hd hτ u hu hx).2
    rw [hbot, Submodule.mem_bot] at this
    simpa [herm, this] using isIntegral_zero)
  rw [hbot, Submodule.mem_bot] at h1
  exact one_ne_zero h1

end Fix

section Main

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K] {Δ τ : K}

private theorem lat_fix (hl : IsLoc O Δ) (hτ : τ ∈ (algebraMap O K).range) (u : Oˣ) (hu : algebraMap O K u = τ ^ 2 - 4)
    {c r t : K} {e v : Oˣ} (hr : r ≠ 0) (hc : c = algebraMap O K e * r ^ 2) {y : (Etau K τ)ˣ}
    (hv : algebraMap O K v = t * QuadraticAlgebra.norm (y : Etau K τ)) {d d' : EL Δ τ} (hd : IB O d)
    (hd' : IB O d') (hdd : d' * d = 1) : IsFix O c d (t • 1) (lat O Δ r y) :=
  ⟨lat_fg hl hr y, lat_dual hτ u hu hr hc hv, lat_stab hτ r y hd hd' hdd⟩

private theorem fix_lat (hl : IsLoc O Δ) (hτ : τ ∈ (algebraMap O K).range) (u : Oˣ) (hu : algebraMap O K u = τ ^ 2 - 4)
    (u' : Oˣ) (hu' : algebraMap O K u' = 2 - τ) {c r t : K} {e : Oˣ} (hr : r ≠ 0) (hc : c = algebraMap O K e * r ^ 2)
    {d d' : EL Δ τ} (hd : d * sigL d = ω) (hd' : IB O d') (hdd : d' * d = 1) {S : Set (Sp Δ τ)}
    (hS : IsFix O c d (t • 1) S) :
    ∃ (y : (Etau K τ)ˣ) (v : Oˣ), algebraMap O K v = t * QuadraticAlgebra.norm (y : Etau K τ) ∧ S = lat O Δ r y := by
  obtain ⟨y, v, hv, hy⟩ := fx_gen hl hS hd hd' hdd hτ u' hu'
  refine ⟨y, v, hv, ?_⟩
  have hsub : S ⊆ lat O Δ r y := fun x hx => by
    obtain ⟨h1, h2⟩ := fx_split hS hd hτ u' hu' hx
    constructor
    · have e1 : star (algebraMap K (Lsq K Δ) r) = algebraMap K (Lsq K Δ) r := by ext <;> simp
      have := (hS.dual _).1 (fx_semi hS h1) _ h1
      rw [herm_lat hc hv] at this
      simp only [semi, mul_zero, zero_mul, map_zero, add_zero, star_mul', star_star, e1] at this
      exact IsIntegral.of_pow two_pos (by rw [pow_two]; exact int_unit e this)
    · have k : ∀ w : EL Δ τ, ((0, w) : Sp Δ τ) ∈ S → IsInt O (QuadraticAlgebra.trace
          (ofE Δ ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w)) := fun w hw => by
        have := (hS.dual _).1 hy _ hw
        rw [herm_lat hc hv, ofE_inv, ← ofE_one, sigL_ofE, ofE_one] at this
        simp only [mul_zero, zero_mul, zero_add, star_one, mul_one] at this
        exact int_unit v this
      exact IB.of_tr hτ u hu (k _ h2) (by simpa only [mul_left_comm ω] using k _ (fx_N hS hd h2))
  refine hsub.antisymm fun w hw => (hS.dual _).2 fun x hx => ?_
  exact (lat_dual hτ u hu hr hc hv w).1 hw x (hsub hx)

private theorem normE (hl : IsLoc O Δ) (hτ : τ ∈ (algebraMap O K).range) (u : Oˣ) (hu : algebraMap O K u = τ ^ 2 - 4)
    (v : Oˣ) : ∃ w : (Etau K τ)ˣ, QuadraticAlgebra.norm (w : Etau K τ) = algebraMap O K v ∧
      IB O (ofE Δ (w : Etau K τ)) ∧ IB O (ofE Δ ((w⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
  have hl' : IsLoc O (τ ^ 2 - 4) := { hl with even := ⟨u, 1, one_ne_zero, by simp [hu]⟩ }
  obtain ⟨ν, hν, hn⟩ := normEx O K _ hl' v
  obtain ⟨h1, b, hb⟩ := (descent O K _ hl' 1 u (by simp [hu]) ν).1.1 hν
  have h2 : ν.im ∈ (algebraMap O K).range := ⟨b, by simp [hb]⟩
  have hn' : QuadraticAlgebra.norm (⟨ν.re - τ * ν.im, ν.im + ν.im⟩ : Etau K τ) = algebraMap O K v := by
    rw [← hn, norm_def, norm_def]; ring
  have hw : IsUnit (⟨ν.re - τ * ν.im, ν.im + ν.im⟩ : Etau K τ) :=
    isUnit_iff_norm_isUnit.2 (hn' ▸ v.isUnit.map (algebraMap O K))
  have hI : IB O (ofE Δ (hw.unit : Etau K τ)) := IB.ofE (sub_mem h1 (mul_mem hτ h2)) (add_mem h2 h2)
  have hn'' : QuadraticAlgebra.norm (hw.unit : Etau K τ) = algebraMap O K v := hn'
  refine ⟨hw.unit, hn', hI, IB.unit v ?_⟩
  convert hI.star hτ using 1
  rw [← hn'', ← one_mul (ofE Δ _), ← smul_mul_assoc, ← ofE_mul_star]
  linear_combination star (ofE Δ (hw.unit : Etau K τ)) * ofE_inv (Δ := Δ) hw.unit

private theorem IB_of_int (hl : IsLoc O Δ) (hτ : τ ∈ (algebraMap O K).range) (u : Oˣ)
    (hu : algebraMap O K u = τ ^ 2 - 4) {x : Etau K τ} (hx : IsIntegral O x) : IB O (ofE Δ x) := by
  haveI := hl.frac
  let φ : Etau K τ →ₐ[O] Etau K τ :=
    { starRingEnd (Etau K τ) with
      commutes' := fun r => by
        change star (algebraMap O (Etau K τ) r) = _
        rw [IsScalarTower.algebraMap_apply O K (Etau K τ)]
        ext <;> simp }
  have k : ∀ x : Etau K τ, IsIntegral O x → IsInt O (QuadraticAlgebra.trace (ofE Δ x)) := fun x hx => by
    have h : IsIntegral O (x + star x) := hx.add (hx.map φ)
    rw [← algebraMap_trace_eq_add_star] at h
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      ((isIntegral_algebraMap_iff (algebraMap K (Etau K τ)).injective).mp h)
    rw [trace_ofE, ← ha]
    exact int_of a
  have hω : IsIntegral O (ω : Etau K τ) := by
    obtain ⟨a, ha⟩ := hτ
    refine ⟨Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + 1, by monicity!, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, Polynomial.eval₂_one]
    rw [IsScalarTower.algebraMap_apply O K (Etau K τ), ha, pow_two]
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  exact IB.of_tr hτ u hu (k x hx) (by simpa only [ofE_mul, ofE_omega] using k _ (hω.mul hx))

private theorem main (hl : IsLoc O Δ) (hτ : τ ∈ (algebraMap O K).range) (u : Oˣ) (hu : algebraMap O K u = τ ^ 2 - 4)
    (u' : Oˣ) (hu' : algebraMap O K u' = 2 - τ) {c r : K} (t : Kˣ) {e : Oˣ} (hr : r ≠ 0)
    (hc : c = algebraMap O K e * r ^ 2) {d d' : EL Δ τ} (hd : d * sigL d = ω) (hI : IB O d) (hd' : IB O d')
    (hdd : d' * d = 1) : lcount O c d ((t : K) • 1) = if hs (τ ^ 2 - 4) (t : K) = 1 then 1 else 0 := by
  classical
  have hD : τ ^ 2 - 4 ≠ 0 := hu ▸ (u.isUnit.map (algebraMap O K)).ne_zero
  have h2 : (2 : K) ≠ 0 := by
    have := (hl.two.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  have hinv : ∀ y : (Etau K τ)ˣ, QuadraticAlgebra.norm ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) *
      QuadraticAlgebra.norm (y : Etau K τ) = 1 := fun y => by rw [← map_mul, Units.inv_mul, map_one]
  split_ifs with ht
  · obtain ⟨z₀, hz₀⟩ := (hsNE O K Δ τ hl hD t).2 ht
    have hz : QuadraticAlgebra.norm (z₀ : Etau K τ) = t := congrArg Units.val hz₀
    letI := torAct (K := K) Δ τ
    have hsm : ∀ (z y : (Etau K τ)ˣ), z • lat O Δ r y = lat O Δ r (z * star z⁻¹ * y) := fun z y => tor_lat r y z
    have h := wCard (Etau K τ)ˣ (Set (Sp Δ τ)) (Cint O τ) {S | IsFix O c d ((t : K) • 1) S} {lat O Δ r z₀⁻¹}
      ?_ ?_ (Set.finite_singleton _) ?_ ?_ ?_
    · rw [Set.ncard_singleton, Nat.cast_one] at h
      rw [← h]
      unfold lcount
      congr 1
    · intro z S hS
      obtain ⟨y, v, hv, rfl⟩ := fix_lat hl hτ u hu u' hu' hr hc hd hd' hdd hS
      rw [hsm]
      refine lat_fix (v := v) hl hτ u hu hr hc ?_ hI hd' hdd
      rw [hv, Units.val_mul, Units.val_mul, map_mul, map_mul, Units.coe_star, QuadraticAlgebra.norm_star,
        mul_comm (QuadraticAlgebra.norm (z : Etau K τ)), hinv, one_mul]
    · rintro _ rfl
      refine lat_fix (v := 1) hl hτ u hu hr hc ?_ hI hd' hdd
      rw [← hz, mul_comm, hinv, Units.val_one, map_one]
    · rintro z hz _ rfl
      rw [hsm]
      refine lat_unit hτ r _ _ (IB_of_int hl hτ u hu hz.1) (IB_of_int hl hτ u hu ?_)
      rw [mul_inv]
      convert hz.2 using 1
      simp [quo]
    · intro S hS
      obtain ⟨y, v, hv, rfl⟩ := fix_lat hl hτ u hu u' hu' hr hc hd hd' hdd hS
      obtain ⟨w, hw, hw1, hw2⟩ := normE hl hτ u hu v
      obtain ⟨z, hz'⟩ := h90E h2 (w * z₀⁻¹ * y⁻¹) (by
        simp only [Units.val_mul, map_mul]
        rw [hw, hv, ← hz]
        linear_combination (QuadraticAlgebra.norm ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ) *
          QuadraticAlgebra.norm (y : Etau K τ)) * hinv z₀ + hinv y)
      refine ⟨z, ?_⟩
      rw [hsm, Set.mem_singleton_iff]
      rcases hz' with h | h
      · rw [h, inv_mul_cancel_right]
        exact lat_unit hτ r _ w hw1 hw2
      · rw [h, neg_mul, inv_mul_cancel_right, ← neg_mul]
        have hneg : ∀ x : Etau K τ, ofE Δ (-x) = -ofE Δ x := fun x => by ext <;> simp [ofE]
        exact lat_unit hτ r _ (-w) (by simpa [hneg] using hw1.neg) (by simpa [hneg] using hw2.neg)
    · rintro z _ rfl h
      exact ⟨1, one_mem _, by rw [one_smul]; exact h.symm⟩
  · have hno : ∀ S, ¬ IsFix O c d ((t : K) • 1) S := fun S hS => by
      obtain ⟨y, v, hv, -⟩ := fix_lat hl hτ u hu u' hu' hr hc hd hd' hdd hS
      obtain ⟨w, hw, -⟩ := normE hl hτ u hu v
      refine ht ((hsNE O K Δ τ hl hD t).1 ⟨w * y⁻¹, Units.ext ?_⟩)
      change QuadraticAlgebra.norm ((w : Etau K τ) * ((y⁻¹ : (Etau K τ)ˣ) : Etau K τ)) = t
      rw [map_mul, hw, hv]
      linear_combination (t : K) * hinv y
    simp [lcount, wcount, hno]

end Main

end UpperTheory.V.Z.Sym.Loc.CG

open UpperTheory.V.Z.Sym.Loc.CG in
theorem UpperTheory.V.Z.Sym.Loc.caseG :
    UpperTheory.V.Z.Sym.Loc.CaseG := by
  rintro O K _ _ _ _ _ Δ τ hl ⟨u, hu⟩ c ⟨e, r, hr, hc⟩ lam hlam hn z hz t
  haveI := hl.frac
  have hD : τ ^ 2 - 4 ≠ 0 := hu ▸ (u.isUnit.map (algebraMap O K)).ne_zero
  obtain ⟨a, ha⟩ : ∃ a : O, algebraMap O K a = τ := by
    refine IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.of_pow two_pos ?_)
    have : τ ^ 2 = algebraMap O K (u + 4) := by rw [map_add, hu, map_ofNat]; ring
    exact this ▸ isIntegral_algebraMap
  have hp : IsUnit ((2 - a) * (2 + a)) := by
    have : (2 - a) * (2 + a) = -(u : O) := IsFractionRing.injective O K (by
      simp only [map_mul, map_sub, map_add, map_neg, map_ofNat, ha, hu]; ring)
    exact this ▸ u.isUnit.neg
  obtain ⟨u₁, hu₁⟩ := isUnit_of_mul_isUnit_left hp
  obtain ⟨u₂, hu₂⟩ := isUnit_of_mul_isUnit_right hp
  have h₁ : algebraMap O K u₁ = 2 - τ := by rw [hu₁, map_sub, map_ofNat, ha]
  have h₂ : algebraMap O K u₂ = 2 + τ := by rw [hu₂, map_add, map_ofNat, ha]
  have hc0 : c ≠ 0 := hc ▸ mul_ne_zero (e.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero _ hr)
  have hd := (datLam K Δ τ c hD hc0 lam hn z hz).d_norm
  rw [ofE_omega] at hd
  have hzI : IB O (ofE Δ (z : Etau K τ)) := IB.ofE (by rw [hz]; simp [QuadraticAlgebra.re_one])
    (by rw [hz]; simp [QuadraticAlgebra.im_one])
  have hzn : QuadraticAlgebra.norm (z : Etau K τ) = algebraMap O K u₂ := by
    rw [hz, h₂, norm_def]; simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]; ring
  have hzz := congrArg star (ofE_inv (Δ := Δ) z)
  rw [star_mul', star_one] at hzz
  refine main (d' := algebraMap O K ((u₂⁻¹ : Oˣ) : O) • star lam • star (ofE Δ (z : Etau K τ))) hl ⟨a, ha⟩ u hu u₁ h₁ t hr hc hd
    ?_ (((hzI.star ⟨a, ha⟩).smul (int_star hlam)).smulO _) ?_
  · refine IB.smul hlam (IB.unit u₂ ?_)
    convert hzI using 1
    rw [← hzn, ← one_mul (ofE Δ (star _)), ← smul_mul_assoc, ← ofE_mul_star, ← ofE_star]
    linear_combination ofE Δ (z : Etau K τ) * hzz
  · rw [dLam, ← ofE_star, smul_mul_assoc, smul_mul_smul_comm, mul_comm (star (ofE Δ _)), hzz, mul_comm,
      ← algebraMap_norm_eq_mul_star, hn, ← h₂, algebraMap_smul (Lsq K Δ), smul_smul, ← map_mul, Units.inv_mul, map_one, one_smul]
