import Mathlib
import GroundTheory.PAdicHodge.BCrisEigenFixed
import GroundTheory.PAdicHodge.BCrisEigenChar
import GroundTheory.PAdicHodge.BCrisEigenMaps
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

open GroundTheory.LocalField EigenWitt EigenChar

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

include hζ in

theorem exists_eq_zpow_mul_unit {y : 𝔹dR} (hy : y ≠ 0) :
    ∃ (i : ℤ) (u : 𝔹ˣ), y = algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ i * algebraMap 𝔹 𝔹dR (u : 𝔹) := by
  have ht : Irreducible (fontaineT ε hε) :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer _ |>.2 (maximalIdeal_eq_span_fontaineT hε hζ)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝔹) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hy
    exact hy rfl
  obtain ⟨m, u₁, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 ht
  obtain ⟨n, u₂, hb'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 ht
  refine ⟨(m : ℤ) - n, u₁ * u₂⁻¹, ?_⟩
  have hT : algebraMap 𝔹 𝔹dR (fontaineT ε hε) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2 ht.ne_zero
  have hu₂ : algebraMap 𝔹 𝔹dR (u₂ : 𝔹) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2 u₂.ne_zero
  have hinv : algebraMap 𝔹 𝔹dR ((u₂⁻¹ : 𝔹ˣ) : 𝔹) = (algebraMap 𝔹 𝔹dR (u₂ : 𝔹))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  rw [ha, hb', Units.val_mul]
  simp only [map_mul, map_pow]
  rw [hinv, zpow_sub₀ hT, zpow_natCast, zpow_natCast]
  field_simp

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem exists_gal_smul_unit (σ : Gal(PadicAlgCl p/L)) {i : ℤ} {u : 𝔹} {q : ℚ_[p]}
    (h : σ • (algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ i * algebraMap 𝔹 𝔹dR u) =
      algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 q) *
        (algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ i * algebraMap 𝔹 𝔹dR u))
    (hT : algebraMap 𝔹 𝔹dR (fontaineT ε hε) ≠ 0) :
    ∃ q' : ℚ_[p], σ • u = algebraMap ℚ_[p] 𝔹 q' * u := by
  set χ : ℚ_[p] := ((cycloChar L σ : ℤ_[p]) : ℚ_[p])
  have hχ : χ ≠ 0 := by
    intro h0
    have := (cycloChar L σ).isUnit.map (PadicInt.Coe.ringHom (p := p))
    exact this.ne_zero h0
  refine ⟨q * χ⁻¹ ^ i, IsFractionRing.injective 𝔹 𝔹dR ?_⟩
  set A := algebraMap 𝔹 𝔹dR
  have hσT : σ • A (fontaineT ε hε) = A (algebraMap ℚ_[p] 𝔹 χ) * A (fontaineT ε hε) := by
    rw [gal_smul_algebraMap_bDeRham, gal_smul_fontaineT, map_mul]
  have hAχ : A (algebraMap ℚ_[p] 𝔹 χ) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2
      ((map_ne_zero_iff _ (algebraMap ℚ_[p] 𝔹).injective).2 hχ)
  rw [gal_smul_bDeRham_def, map_mul, map_zpow₀, ← gal_smul_bDeRham_def, ← gal_smul_bDeRham_def,
    hσT, gal_smul_algebraMap_bDeRham] at h
  set Aq : ℚ_[p] →+* 𝔹dR := A.comp (algebraMap ℚ_[p] 𝔹) with hAq
  have eAq : ∀ r : ℚ_[p], A (algebraMap ℚ_[p] 𝔹 r) = Aq r := fun r => rfl
  rw [map_mul, eAq, map_mul, map_zpow₀, map_inv₀]
  rw [eAq, eAq] at h
  rw [eAq] at hAχ
  have hTi : A (fontaineT ε hε) ^ i ≠ 0 := zpow_ne_zero _ hT
  have hχi : Aq χ ^ i ≠ 0 := zpow_ne_zero _ hAχ
  rw [mul_zpow] at h
  have h2 : A (fontaineT ε hε) ^ i * (Aq χ ^ i * A (σ • u)) =
      A (fontaineT ε hε) ^ i * (Aq q * A u) := by
    linear_combination h
  have h3 := mul_left_cancel₀ hTi h2
  rw [inv_zpow', zpow_neg]
  field_simp
  linear_combination h3

variable (p) in

def SenTateCharacters : Prop :=
  ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (η : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ), Continuous η →
    ∀ x : ℂ_[p], x ≠ 0 → (∀ σ, σ • x = algebraMap ℚ_[p] ℂ_[p] (η σ) * x) →
      (η '' {σ | ∀ u ∈ unramifiedClosure p, σ u = u}).Finite

theorem exists_twist_of_finite_image {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] K] {x : ℂ_[p]} (hx0 : x ≠ 0) (ψ : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ)
    (hψc : Continuous ψ) (hψx : ∀ σ, σ • x = algebraMap ℚ_[p] ℂ_[p] (ψ σ) * x)
    (hfin : (ψ '' {σ | ∀ u ∈ unramifiedClosure p, σ u = u}).Finite) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), ∃ hKL : K ≤ L, FiniteDimensional ℚ_[p] L ∧
      ∃ (f : ℕ) (c : (AInf ℂ_[p] p)ˣ), 0 < f ∧
        ∀ σ : Gal(PadicAlgCl p/L), ∃ z : ℤ_[p],
          (z : ℚ_[p]) = ((ψ (galRes hKL σ) : ℚ_[p]ˣ) : ℚ_[p]) ^ f ∧
          σ • (c : AInf ℂ_[p] p) = IsPerfectoidField.padicIntToWitt p z * (c : AInf ℂ_[p] p) := by
  obtain ⟨E, hE, hEψ⟩ := exists_fixingSubgroup_of_finite_image ψ hψc _ hfin
  have : IsScalarTower ℚ_[p] K E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hE' : FiniteDimensional ℚ_[p] E := Module.Finite.trans K E
  obtain ⟨L, hL⟩ : ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), L = E.restrictScalars ℚ_[p] :=
    ⟨_, rfl⟩
  have hLE : ∀ y, y ∈ L ↔ y ∈ E := fun y => by rw [hL]; exact IntermediateField.mem_restrictScalars _
  have hKL : K ≤ L := fun k hk => (hLE _).2 (E.algebraMap_mem ⟨k, hk⟩)
  have : FiniteDimensional ℚ_[p] L := by subst hL; exact hE'
  have hres : ∀ σ : Gal(PadicAlgCl p/L), galRes hKL σ ∈ E.fixingSubgroup := fun σ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun e he => σ.commutes ⟨e, (hLE e).2 he⟩
  obtain ⟨ψL, -, hψLx⟩ := exists_eigenChar (K := L) hx0 (fun σ => ⟨_, hψx (galRes hKL σ)⟩)
  have hψL : ∀ σ, ψL σ = ψ (galRes hKL σ) := fun σ =>
    Units.ext (eq_of_mul_eq hx0 ((hψLx σ).symm.trans (hψx (galRes hKL σ))))
  obtain ⟨f, hf, c, hc⟩ := exists_twist_of_unramified hx0 ψL hψLx (fun σ hσ => by
    have h3 := mem_inertia_of_degree hσ
    rw [hψL]
    refine hEψ _ (hres σ) fun u hu => ?_
    rw [galRes_apply]
    exact h3 u hu)
  refine ⟨L, hKL, this, f, c, hf, fun σ => ?_⟩
  obtain ⟨z, hz, hzc⟩ := hc σ
  exact ⟨z, by rw [hz, hψL], hzc⟩

include hζ in
set_option maxHeartbeats 1600000 in

theorem exists_unramified_twist (hST : SenTateCharacters p)
    {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K] {y : 𝔹dR}
    (hy0 : y ≠ 0) (hyσ : ∀ σ : Gal(PadicAlgCl p/K), ∃ q : ℚ_[p],
      σ • y = algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 q) * y) :
    ∃ (i : ℤ) (u : 𝔹ˣ), y = algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ i * algebraMap 𝔹 𝔹dR (u : 𝔹) ∧
      ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), K ≤ L ∧ FiniteDimensional ℚ_[p] L ∧
      ∃ (f : ℕ) (c : (AInf ℂ_[p] p)ˣ) (ψ : Gal(PadicAlgCl p/L) → ℚ_[p]ˣ), 0 < f ∧
        (∀ σ : Gal(PadicAlgCl p/L), σ • (u : 𝔹) = algebraMap ℚ_[p] 𝔹 (ψ σ) * u) ∧
        ∀ σ : Gal(PadicAlgCl p/L), ∃ z : ℤ_[p], (z : ℚ_[p]) = ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f ∧
          σ • (c : AInf ℂ_[p] p) = IsPerfectoidField.padicIntToWitt p z * (c : AInf ℂ_[p] p) := by
  classical
  obtain ⟨i, u, hyu⟩ := exists_eq_zpow_mul_unit hε hζ hy0
  have hT : algebraMap 𝔹 𝔹dR (fontaineT ε hε) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2 (fontaineT_ne_zero hε hζ)
  have huσ : ∀ σ : Gal(PadicAlgCl p/K), ∃ q : ℚ_[p], σ • (u : 𝔹) = algebraMap ℚ_[p] 𝔹 q * u :=
    fun σ => by
      obtain ⟨q, hq⟩ := hyσ σ
      exact exists_gal_smul_unit hε σ (by rw [← hyu]; exact hq) hT
  have hx0 : thetaAlgHom p (u : 𝔹) ≠ 0 := (u.isUnit.map (thetaAlgHom p)).ne_zero
  have hθ : ∀ {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : Gal(PadicAlgCl p/L)) (q : ℚ_[p]),
      σ • (u : 𝔹) = algebraMap ℚ_[p] 𝔹 q * u →
        σ • thetaAlgHom p (u : 𝔹) = algebraMap ℚ_[p] ℂ_[p] q * thetaAlgHom p (u : 𝔹) := by
    intro L σ q h
    rw [thetaAlgHom_apply, ← thetaBDeRhamPlusField_gal_smul, h, ← thetaAlgHom_apply, map_mul,
      AlgHom.commutes]
    rfl
  obtain ⟨ψ, hψc, hψx⟩ := exists_eigenChar hx0 fun σ => (huσ σ).imp fun q h => hθ σ q h
  obtain ⟨L, hKL, hL, f, c, hf, hc⟩ := exists_twist_of_finite_image hx0 ψ hψc hψx
    (hST K ψ hψc _ hx0 hψx)
  refine ⟨i, u, hyu, L, hKL, hL, f, c, fun σ => ψ (galRes hKL σ), hf, fun σ => ?_, hc⟩
  obtain ⟨q, hq⟩ := huσ (galRes hKL σ)
  have hq' : σ • (u : 𝔹) = algebraMap ℚ_[p] 𝔹 q * u := hq
  have h2 : q = ψ (galRes hKL σ) := eq_of_mul_eq hx0 ((hθ σ q hq').symm.trans (hψx (galRes hKL σ)))
  rw [hq', h2]

theorem isUnit_of_fixed_twist {R F G : Type*} [CommRing R] [IsDomain R] [Field F] [Group G]
    [MulSemiringAction G F] (g : R →+* F) (hg : Function.Injective g) (act : G → R → R)
    (hequiv : ∀ σ y, g (act σ y) = σ • g y)
    (hunit : ∀ B : R, B ≠ 0 → (∀ σ, act σ B = B) → IsUnit B)
    {b : R} (hb0 : b ≠ 0) {f : ℕ} (hf : 0 < f) (c T : Rˣ) (n : ℤ)
    (hfix : ∀ σ : G, σ • (g b ^ f * (g ↑c)⁻¹ * g ↑T ^ n) = g b ^ f * (g ↑c)⁻¹ * g ↑T ^ n) :
    IsUnit b := by
  set B := b ^ f * ↑c⁻¹ * ↑(T ^ n) with hB
  have hgT : g ↑(T ^ n) = g ↑T ^ n := by
    have h := congrArg Units.val (map_zpow (Units.map (g : R →* F)) T n)
    rw [Units.val_zpow_eq_zpow_val] at h
    exact h
  have hgB : g B = g b ^ f * (g ↑c)⁻¹ * g ↑T ^ n := by
    rw [hB, map_mul, map_mul, map_pow, map_units_inv, hgT]
  have hB0 : B ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ hb0) (Units.ne_zero _)) (Units.ne_zero _)
  have hBu : IsUnit B := hunit B hB0 fun σ => hg (by rw [hequiv, hgB, hfix])
  have hbf : b ^ f = B * ↑c * ↑(T ^ (-n)) := by
    rw [hB]
    have e1 : (↑c⁻¹ : R) * ↑c = 1 := Units.inv_mul c
    have e2 : (↑(T ^ n) : R) * ↑(T ^ (-n)) = 1 := by
      rw [← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
    calc b ^ f = b ^ f * ((↑c⁻¹ * ↑c) * (↑(T ^ n) * ↑(T ^ (-n)))) := by rw [e1, e2, one_mul, mul_one]
      _ = _ := by ring
  have hbfu : IsUnit (b ^ f) := by
    rw [hbf]
    exact (hBu.mul c.isUnit).mul (Units.isUnit _)
  exact (isUnit_pow_iff hf.ne').1 hbfu

include hζ in
set_option maxHeartbeats 3200000 in

theorem isUnit_of_twist {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]
    {b : BCris hε} (hb0 : b ≠ 0) {i : ℤ} {u : 𝔹ˣ}
    (hyu : iotaB hε hζ b = algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ i * algebraMap 𝔹 𝔹dR (u : 𝔹))
    {f : ℕ} (hf : 0 < f) {c : (AInf ℂ_[p] p)ˣ} {ψ : Gal(PadicAlgCl p/L) → ℚ_[p]ˣ}
    (huL : ∀ σ : Gal(PadicAlgCl p/L), σ • (u : 𝔹) = algebraMap ℚ_[p] 𝔹 (ψ σ) * u)
    (hc : ∀ σ : Gal(PadicAlgCl p/L), ∃ z : ℤ_[p], (z : ℚ_[p]) = ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f ∧
      σ • (c : AInf ℂ_[p] p) = IsPerfectoidField.padicIntToWitt p z * (c : AInf ℂ_[p] p)) :
    IsUnit b := by
  have := isDomain_bCris hε hζ
  have hT : algebraMap 𝔹 𝔹dR (fontaineT ε hε) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2 (fontaineT_ne_zero hε hζ)
  obtain ⟨C, hCdef⟩ : ∃ C : 𝔹dR,
      C = algebraMap 𝔹 𝔹dR (wittToBDeRhamPlus (normInteger ℂ_[p]) p (c : AInf ℂ_[p] p)) := ⟨_, rfl⟩
  have hC0 : C ≠ 0 := by
    rw [hCdef]
    exact (map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2
      ((c.isUnit.map (wittToBDeRhamPlus (normInteger ℂ_[p]) p)).ne_zero)
  have hCσ : ∀ σ : Gal(PadicAlgCl p/L),
      σ • C = algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 (ψ σ)) ^ f * C := fun σ => by
    obtain ⟨z, hz, hzc⟩ := hc σ
    rw [hCdef, gal_smul_algebraMap_bDeRham, gal_smul_wittToBDeRhamPlus, hzc, map_mul, map_mul,
      ← IsPerfectoidField.algebraMap_padic_coe, hz, map_pow, map_pow]
  obtain ⟨cB, hcBdef⟩ : ∃ cB : BCris hε, cB = aInfToBCris hε (c : AInf ℂ_[p] p) := ⟨_, rfl⟩
  have hcB : IsUnit cB := by rw [hcBdef]; exact c.isUnit.map _
  have hιc : iotaB hε hζ ↑hcB.unit = C := by rw [IsUnit.unit_spec, hcBdef, hCdef, iotaB_aInfToBCris]
  have hιT : iotaB hε hζ ↑(isUnit_periodTCris hε).unit = algebraMap 𝔹 𝔹dR (fontaineT ε hε) := by
    rw [IsUnit.unit_spec, iotaB_periodTCris_eq]
  refine isUnit_of_fixed_twist (G := Gal(PadicAlgCl p/L)) (iotaB hε hζ) (iotaB_injective hε hζ)
    (fun σ y => galB hε σ y) (fun σ y => iotaB_galB (K := L) hε hζ σ y)
    (fun B hB0 hB => isUnit_of_galB_fixed hε hζ (L := L) hB0 hB) hb0 hf hcB.unit
    (isUnit_periodTCris hε).unit (-(i * f)) fun σ => ?_
  rw [hιc, hιT, hyu]
  have hψ0 : algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 (ψ σ)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2
      ((map_ne_zero_iff _ (algebraMap ℚ_[p] 𝔹).injective).2 (Units.ne_zero _))
  have hsimp : (algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ i * algebraMap 𝔹 𝔹dR (u : 𝔹)) ^ f * C⁻¹ *
      algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ (-(i * f)) = algebraMap 𝔹 𝔹dR (u : 𝔹) ^ f * C⁻¹ := by
    rw [mul_pow, ← zpow_natCast (_ ^ i), ← zpow_mul, zpow_neg]
    have hTz : algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ (i * (f : ℤ)) ≠ 0 := zpow_ne_zero _ hT
    field_simp
  rw [hsimp, gal_smul_bDeRham_def, map_mul, map_pow, map_inv₀, ← gal_smul_bDeRham_def,
    ← gal_smul_bDeRham_def, gal_smul_algebraMap_bDeRham, huL σ, hCσ σ, map_mul, mul_pow]
  field_simp

include hζ in
set_option maxHeartbeats 3200000 in

theorem isUnit_of_forall_galB_eq_mul (hST : SenTateCharacters p)
    {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K] {b : BCris hε}
    (hb0 : b ≠ 0)
    (hb : ∀ σ : Gal(PadicAlgCl p/K), ∃ q : ℚ_[p], galB hε σ b = algebraMap ℚ_[p] (BCris hε) q * b) :
    IsUnit b := by
  have hy0 : iotaB hε hζ b ≠ 0 := (map_ne_zero_iff _ (iotaB_injective hε hζ)).2 hb0
  obtain ⟨i, u, hyu, L, -, hL, f, c, ψ, hf, huL, hc⟩ := exists_unramified_twist hε hζ hST hy0
    (fun σ => by
      obtain ⟨q, hq⟩ := hb σ
      refine ⟨q, ?_⟩
      rw [← iotaB_galB (K := K) hε hζ σ b, hq, map_mul, iotaB_algebraMap_padic_bdRPlus])
  exact isUnit_of_twist hε hζ (L := L) hb0 hyu hf huL hc

include hζ in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem isRegular_bCris (hST : SenTateCharacters p) {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] K] :
    letI := isDomain_bCris hε hζ
    letI := galBAction (K := K) hε
    haveI := smulCommClass_galBAction (K := K) hε
    IsRegular Gal(PadicAlgCl p/K) ℚ_[p] (BCris hε) :=
  letI := isDomain_bCris hε hζ
  letI := galBAction (K := K) hε
  haveI := smulCommClass_galBAction (K := K) hε
  { image_fixedPoints := image_fixedPoints_fractionRing (K := K) hε hζ
    isUnit_of_mem_span := fun b hb0 hb => isUnit_of_forall_galB_eq_mul hε hζ hST hb0 fun σ => by
      obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.1 (hb σ)
      exact ⟨q, (hq.symm.trans (Algebra.smul_def q b) :)⟩ }

end ACris

end GroundTheory.PAdicHodge
