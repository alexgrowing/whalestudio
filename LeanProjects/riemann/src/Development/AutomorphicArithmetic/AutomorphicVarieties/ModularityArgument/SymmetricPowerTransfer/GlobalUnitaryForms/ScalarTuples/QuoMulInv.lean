import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ModelMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.SplitUnitElements.HermAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.OfEMulStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatLam
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsNE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NonsqMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.WCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Descent

open QuadraticAlgebra NumberField IsDedekindDomain UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob.GP

section Alg

variable {K : Type} [Field K] {Δ τ : K}

private theorem ofE_mul (x y : Etau K τ) : ofE Δ (x * y) = ofE Δ x * ofE Δ y := by ext <;> simp [ofE]

private theorem ofE_one : ofE Δ (1 : Etau K τ) = 1 := by
  ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem quo_mul_inv (z : (Etau K τ)ˣ) : quo z * quo z⁻¹ = 1 := by
  have e : ∀ a b : (Etau K τ)ˣ, quo (a * b) = quo a * quo b := fun a b => by
    simp only [quo, _root_.mul_inv_rev, Units.val_mul, star_mul]; ring
  rw [← e, mul_inv_cancel]
  simp [quo]

private theorem tor_inv (z : (Etau K τ)ˣ) (x : Sp Δ τ) : tor Δ z (tor Δ z⁻¹ x) = x := by
  refine Prod.ext rfl ?_
  simp only [tor]
  rw [← mul_assoc, ← ofE_mul, quo_mul_inv, ofE_one, one_mul]

end Alg

section Lat

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {Δ τ : K}

private theorem int_of (a : O) : IsInt O (algebraMap K (Lsq K Δ) (algebraMap O K a)) := by
  rw [← IsScalarTower.algebraMap_apply]; exact isIntegral_algebraMap

private theorem int_unit (u : Oˣ) {x : Lsq K Δ} (h : IsInt O (algebraMap K (Lsq K Δ) (algebraMap O K u) * x)) :
    IsInt O x := by
  have := (int_of ((u⁻¹ : Oˣ) : O)).mul h
  rwa [← mul_assoc, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one, one_mul] at this

variable (O) in

private def IB (x : EL Δ τ) : Prop := IsInt O x.re ∧ IsInt O x.im

private theorem IB.mul (hτ : τ ∈ (algebraMap O K).range) {x y : EL Δ τ} (hx : IB O x) (hy : IB O y) : IB O (x * y) := by
  obtain ⟨a, rfl⟩ := hτ
  exact ⟨(hx.1.mul hy.1).add ((isIntegral_one.neg.mul hx.2).mul hy.2),
    ((hx.1.mul hy.2).add (hx.2.mul hy.1)).add (((int_of a).mul hx.2).mul hy.2)⟩

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

variable (O Δ τ) in

private def lat : Set (Sp Δ τ) := {x | IsInt O x.1 ∧ IB O x.2}

variable [IsDomain O] [IsDiscreteValuationRing O]

private theorem IB.sig (hl : IsLoc O Δ) {y : EL Δ τ} (hy : IB O y) : IB O (sigL y) :=
  ⟨OE.int_star hl hy.1, OE.int_star hl hy.2⟩

private theorem lat_fg (hl : IsLoc O Δ) : ∃ s : Finset (Sp Δ τ), lat O Δ τ = Submodule.span O (s : Set (Sp Δ τ)) := by
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
    { toFun := fun p => (p.1, p.2.1 • 1 + p.2.2 • ω)
      map_add' := fun p q => Prod.ext rfl (by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel)
      map_smul' := fun k p => Prod.ext rfl
        (by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply, mul_smul, ← smul_add]) }
  obtain ⟨s, hs⟩ := (hfg.prod (hfg.prod hfg)).map (f.restrictScalars O)
  refine ⟨s, ?_⟩
  rw [hs]
  ext x
  constructor
  · intro hx
    refine ⟨(x.1, x.2.re, x.2.im), ⟨(hR _).2 hx.1, (hR _).2 hx.2.1, (hR _).2 hx.2.2⟩, Prod.ext rfl ?_⟩
    change x.2.re • (1 : EL Δ τ) + x.2.im • ω = x.2
    ext1 <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · rintro ⟨⟨a, b, b'⟩, ⟨ha, hb, hb'⟩, rfl⟩
    refine ⟨(hR _).1 ha, ?_⟩
    exact ⟨by simpa [f, QuadraticAlgebra.re_one] using (hR _).1 hb, by simpa [f, QuadraticAlgebra.im_one] using (hR _).1 hb'⟩

private theorem lat_fix (hl : IsLoc O Δ) (hτ : τ ∈ (algebraMap O K).range) (u : Oˣ) (hu : algebraMap O K u = τ ^ 2 - 4)
    (e : Oˣ) {d d' m m' : EL Δ τ} (hd : IB O d) (hd' : IB O d') (hdd : d' * d = 1) (hm : IB O m) (hm' : IB O m')
    (hmm : m * m' = 1) : IsFix O (algebraMap O K e) d m (lat O Δ τ) := by
  refine ⟨lat_fg hl, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩, ?_⟩
  · exact ((int_of _ |>.mul hx.1).mul (OE.int_star hl hy.1)).add
      (((hm.mul hτ hx.2).mul hτ ((hy.2.sig hl).star hτ)).tr hτ)
  · have z0 : IB O (0 : EL Δ τ) := ⟨isIntegral_zero, isIntegral_zero⟩
    have k : ∀ b : EL Δ τ, IB O b → IsInt O (QuadraticAlgebra.trace (b * star (sigL y.2))) := fun b hb => by
      have := h (0, m' * b) ⟨isIntegral_zero, hm'.mul hτ hb⟩
      simpa only [herm, mul_zero, zero_mul, zero_add, ← mul_assoc, hmm, one_mul] using this
    constructor
    · have := h (1, 0) ⟨isIntegral_one, z0⟩
      simp only [herm, mul_one, mul_zero, zero_mul, map_zero, add_zero] at this
      simpa only [star_star] using OE.int_star hl (int_unit e this)
    · have := IB.of_tr hτ u hu (by simpa only [one_mul] using k 1 ⟨isIntegral_one, isIntegral_zero⟩)
        (k ω ⟨isIntegral_zero, isIntegral_one⟩)
      have e2 : sigL (star (star (sigL y.2))) = y.2 := by ext <;> simp [sigL]
      have := (this.star hτ).sig hl
      rwa [e2] at this
  · have k : ∀ d : EL Δ τ, IB O d → ∀ x ∈ lat O Δ τ, semi d x ∈ lat O Δ τ := fun d hd x hx =>
      ⟨OE.int_star hl hx.1, hd.mul hτ (hx.2.sig hl)⟩
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact k d hd x hx
    · intro hx
      refine ⟨_, k _ (hd'.sig hl) x hx, Prod.ext (star_star _) ?_⟩
      have e2 : sigL (sigL d' * sigL x.2) = d' * x.2 := by ext <;> simp [sigL] <;> ring
      change d * sigL (sigL d' * sigL x.2) = x.2
      rw [e2]
      linear_combination x.2 * hdd

private theorem lcount_std (hl : IsLoc O Δ) (hu : ∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) (e : Oˣ) {d d' m m' : EL Δ τ}
    (h : IsDat (algebraMap O K e) d m) (hd : IB O d) (hd' : IB O d') (hdd : d' * d = 1) (hm : IB O m) (hm' : IB O m')
    (hmm : m * m' = 1) : lcount O (algebraMap O K e) d m = 1 := by
  classical
  obtain ⟨hτ, -, -, hint⟩ := One.intE O K Δ τ hl hu
  obtain ⟨u, hu'⟩ := hu
  have hfix := lat_fix hl hτ u hu' e hd hd' hdd hm hm' hmm
  letI := torAct (K := K) Δ τ
  have hC : ∀ z ∈ Cint O τ, tor Δ z '' lat O Δ τ = lat O Δ τ := fun z hz => by
    have hq : ∀ z : (Etau K τ)ˣ, IsIntegral O (quo z) → IB O (ofE Δ (quo z)) := fun z h =>
      IB.ofE ((hint _).1 h).1 ((hint _).1 h).2
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy.1, (hq z hz.1).mul hτ hy.2⟩
    · intro hx
      exact ⟨tor Δ z⁻¹ x, ⟨hx.1, (hq z⁻¹ hz.2).mul hτ hx.2⟩, tor_inv z x⟩
  have w := wCard (Etau K τ)ˣ (Set (Sp Δ τ)) (Cint O τ) {S | IsFix O (algebraMap O K e) d m S} {lat O Δ τ}
    ?_ ?_ (Set.finite_singleton _) ?_ ?_ ?_
  · rw [Set.ncard_singleton, Nat.cast_one] at w
    rw [← w]
    unfold lcount
    congr 1
  · intro z S hS
    exact (isFix_tor _ d m z S).2 hS
  · rintro _ rfl
    exact hfix
  · rintro z hz _ rfl
    exact hC z hz
  · intro S hS
    obtain ⟨z, hz⟩ := One.uniq O K Δ τ hl ⟨u, hu'⟩ _ d m h S _ hS hfix
    refine ⟨z, ?_⟩
    change tor Δ z '' S = lat O Δ τ
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hz y).1 hy
    · intro hx
      exact ⟨tor Δ z⁻¹ x, (hz _).2 (by rwa [tor_inv]), tor_inv z x⟩
  · rintro z _ rfl hz
    exact ⟨1, one_mem _, by rw [one_smul]; exact Eq.symm hz⟩

private theorem gen_loc (hl : IsLoc O Δ) (hu : ∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) (e : Oˣ) {d d' m m' : EL Δ τ}
    (h : IsDat (algebraMap O K e) d m) (hd : IB O d) (hd' : IB O d') (hdd : d' * d = 1) (hm : IB O m) (hm' : IB O m')
    (hmm : m * m' = 1) (t : Kˣ) : lcount O (algebraMap O K e) d ((t : K) • m) = one (t ∈ NE τ) := by
  classical
  obtain ⟨-, -, ⟨u₂, h₂⟩, -⟩ := One.intE O K Δ τ hl hu
  have hD : τ ^ 2 - 4 ≠ 0 := h.reg
  obtain ⟨lam, hlam, hn⟩ := normEx O K Δ hl u₂
  rw [h₂] at hn
  obtain ⟨z, hz⟩ := exists_unit_one_add_generator hD
  have h0 := datLam K Δ τ _ hD h.c_ne lam hn z hz
  obtain ⟨m₀, hm₀, hmove⟩ := dat_move hl h h0.d_norm
  obtain ⟨s, rfl⟩ := datForm O K Δ τ hl _ lam hn z hz m₀ hm₀
  have hcase := caseG O K Δ τ hl hu (algebraMap O K e) ⟨e, 1, one_ne_zero, by simp⟩ lam hlam hn z hz
  have key : ∀ t : Kˣ, lcount O (algebraMap O K e) d ((t : K) • m) =
      if hs (τ ^ 2 - 4) ((t * s : Kˣ) : K) = 1 then 1 else 0 := fun t => by
    rw [hmove, smul_smul, ← Units.val_mul]
    exact hcase (t * s)
  have h1 : hs (τ ^ 2 - 4) (s : K) = 1 := by
    have := key 1
    rw [Units.val_one, one_smul, lcount_std hl hu e h hd hd' hdd hm hm' hmm, one_mul] at this
    by_contra hne
    simp [hne] at this
  rw [key t, Units.val_mul, hsMul O K Δ hl _ _ _ hD t.ne_zero s.ne_zero, h1, mul_one]
  by_cases ht : t ∈ NE τ
  · rw [if_pos ((hsNE O K Δ τ hl hD t).1 ht)]
    simp [one, ht]
  · rw [if_neg (fun h => ht ((hsNE O K Δ τ hl hD t).2 h))]
    simp [one, ht]

end Lat

section Elmap

variable {K K' : Type} [Field K] [Field K']

private theorem lmap_alg (f : K →+* K') (Δ x : K) :
    lmap f Δ (algebraMap K (Lsq K Δ) x) = algebraMap K' (Lsq K' (f Δ)) (f x) := by
  ext <;> simp [lmap]

private theorem elmap_mul (f : K →+* K') {Δ τ : K} (x y : EL Δ τ) : elmap f (x * y) = elmap f x * elmap f y := by
  ext1
  · simp only [elmap, re_mul, map_add, map_mul, map_neg, map_one, lmap_alg]
  · simp only [elmap, im_mul, map_add, map_mul, lmap_alg]

private theorem elmap_one (f : K →+* K') {Δ τ : K} : elmap f (1 : EL Δ τ) = 1 := by
  ext1 <;> simp [elmap, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

end Elmap

section Int

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ : K}

private theorem int_L {a b : K} (ha : a ∈ (algebraMap O K).range) (hb : b ∈ (algebraMap O K).range)
    (hΔ : Δ ∈ (algebraMap O K).range) : IsInt O (⟨a, b⟩ : Lsq K Δ) := by
  obtain ⟨a₀, rfl⟩ := ha
  obtain ⟨b₀, rfl⟩ := hb
  obtain ⟨D₀, hD⟩ := hΔ
  have hw : IsInt O (⟨0, 1⟩ : Lsq K Δ) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    have : (⟨0, 1⟩ : Lsq K Δ) ^ 2 = algebraMap O (Lsq K Δ) D₀ := by
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ), hD]
      ext <;> simp [sq]
    rw [this]
    exact isIntegral_algebraMap
  have e : (⟨algebraMap O K a₀, algebraMap O K b₀⟩ : Lsq K Δ) =
      algebraMap K (Lsq K Δ) (algebraMap O K a₀) + algebraMap K (Lsq K Δ) (algebraMap O K b₀) * ⟨0, 1⟩ := by
    ext <;> simp
  rw [e]
  exact (int_of a₀).add ((int_of b₀).mul hw)

end Int

section Global

variable {F : Type} [Field F] [NumberField F]

private theorem mem_int (v : Pl F) (y : F) (hy : v.valuation F y ≤ 1) :
    cv v y ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v (y : v.adicCompletion F) ≤ 1
  rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

private theorem ae_int (x : F) :
    ∀ᶠ v : Pl F in Filter.cofinite, cv v x ∈ (algebraMap (Ov v) (Kv v)).range := by
  refine (HeightOneSpectrum.Support.finite (𝓞 F) x).subset fun v hv => ?_
  by_contra hn
  simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hn
  exact hv ⟨⟨_, mem_int v x hn⟩, rfl⟩

private theorem ae_unit {x : F} (hx : x ≠ 0) :
    ∀ᶠ v : Pl F in Filter.cofinite, ∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v x := by
  filter_upwards [ae_int x, ae_int x⁻¹] with v ⟨a, ha⟩ ⟨b, hb⟩
  have : a * b = 1 := by
    apply Subtype.ext
    change algebraMap (Ov v) (Kv v) (a * b) = 1
    rw [map_mul, ha, hb, ← map_mul, mul_inv_cancel₀ hx, map_one]
  exact ⟨⟨a, b, this, by rw [mul_comm, this]⟩, ha⟩

private theorem ae_ib {Δ τ : F} (x : EL Δ τ) :
    ∀ᶠ v : Pl F in Filter.cofinite, IB (Ov v) (elmap (cv v) x) := by
  filter_upwards [ae_int Δ, ae_int x.re.re, ae_int x.re.im, ae_int x.im.re, ae_int x.im.im] with v h0 h1 h2 h3 h4
  exact ⟨int_L h1 h2 h0, int_L h3 h4 h0⟩

end Global

end UpperTheory.V.Z.Sym.Glob.GP

open UpperTheory.V.Z.Sym.Glob.GP in
theorem UpperTheory.V.Z.Sym.Glob.genPl :
    UpperTheory.V.Z.Sym.Glob.GenPl := by
  intro F _ _ Δ D hD τ c d m h
  have oo : ofE Δ (ω : Etau F τ) * ofE Δ (star ω : Etau F τ) = 1 := by
    ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hdu : IsUnit d := IsUnit.of_mul_eq_one (sigL d * ofE Δ (star ω : Etau F τ)) (by rw [← mul_assoc, h.d_norm, oo])
  obtain ⟨du, rfl⟩ := hdu
  obtain ⟨mu, rfl⟩ := h.m_unit
  filter_upwards [ae_ib (du : EL Δ τ), ae_ib ((du⁻¹ : (EL Δ τ)ˣ) : EL Δ τ), ae_ib (mu : EL Δ τ), ae_ib ((mu⁻¹ : (EL Δ τ)ˣ) : EL Δ τ),
    ae_unit h.reg, ae_unit h.c_ne, D.Sg.eventually_cofinite_notMem] with v a1 a2 a3 a4 a5 ⟨e, he⟩ a7 t
  have hd := (modelMap F (Kv v) (cv v) Δ τ c du mu h).1
  rw [← he] at hd ⊢
  exact gen_loc (hD.off v a7) (by simpa [map_ofNat] using a5) e hd a1 a2 (by rw [← elmap_mul, Units.inv_mul, elmap_one]) a3 a4
    (by rw [← elmap_mul, Units.mul_inv, elmap_one]) t
