import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NabValNMap
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralCombinationOfMemHaO
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.VVAlgebraMapNonnegDvr

set_option autoImplicit false

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.ThetaLeast

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.QuadDeriv GlobalTheory.GaugeBaseChange in

theorem nabValN_algebraMap (S S' : Type) [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S'] [Algebra S S']
    (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB S d O) (h : PS S 2 d)
    (hc : MvPowerSeries.constantCoeff h = 0) (w0 : O) (m n : ℕ) (f : PS S n d) (κ : Type) [Fintype κ]
    (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S) :
    nabValN B S' (MvPowerSeries.map (algebraMap S S') h) w0 m (MvPowerSeries.map (algebraMap S S') f) cp
      (fun l j => algebraMap S S' (u l j)) (MvPolynomial.map (algebraMap S S') P) =
      algebraMap S S' (nabValN B S h w0 m f cp u P) := by
  set ψ := algebraMap S S' with hψ
  have eF : (fun i => MvPowerSeries.map ψ (B.FK S i)) = B.FK S' := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.G.F i)) =
      MvPowerSeries.map (algebraMap S S') (B.G.F i)
    ext e
    simp [coeff_map, hψ]
  have eA : mapP ψ (B.actK S w0) = B.actK S' w0 := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.A.act w0 i)) =
      MvPowerSeries.map (algebraMap S S') (B.A.act w0 i)
    ext e
    simp [coeff_map, hψ]
  have gC : GP (comp1 (B.actK S w0) (pt S (n := 1) d 0)) := gp_comp1 _ _ (gp_actK B w0) (gp_pt 0)
  have cL : constantCoeff (B.hL S h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map ψ (B.hL S h w0) = B.hL S' (MvPowerSeries.map ψ h) w0 := by
    unfold FB.hL
    rw [map_ev_two _ _ _ (gp_pt _) gC, baseChange_comp1 _ _ _ (gp_pt _), eA, baseChange_pt]
  have g1 : ∀ (b : Fin n) (j : Fin 1), GP ((![pt S d b] : Fin 1 → Pt S n d) j) := by
    intro b j
    fin_cases j
    exact gp_pt b
  have cb : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt S d b] (B.hL S h w0)) = 0 :=
    fun b => gt_const_ev _ (g1 b) _ cL
  have eb : ∀ b : Fin n, MvPowerSeries.map ψ (ev (n := n) ![pt S d b] (B.hL S h w0)) =
      ev (n := n) ![pt S' d b] (B.hL S' (MvPowerSeries.map ψ h) w0) := by
    intro b
    rw [map_ev ψ _ (g1 b), eL]
    congr 1
    funext j
    fin_cases j
    exact baseChange_pt ψ b
  unfold nabValN
  rw [← MvPowerSeries.constantCoeff_map, ← GlobalTheory.dpolyN_map, eF, map_mul,
    map_expS _ _ (by
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, map_sum, Finset.sum_eq_zero fun b _ => cb b, mul_zero]),
    MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, map_C, map_natCast ψ, map_sum,
    Finset.sum_congr rfl fun b _ => eb b]

theorem smul_mem_HHa {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k] {cc : Ty → Ty} {isX : Ty → Prop}
    {a : Ty → ℕ → ℕ} (s : k) {P : MvPolynomial (Letter Ty r n) k} (hP : P ∈ HHa r n k cc isX a) :
    s • P ∈ HHa r n k cc isX a :=
  ⟨Submodule.smul_mem _ s hP.1, fun σ i i' hi t => by rw [map_smul, hP.2.1 σ i i' hi t],
    fun m hm => hP.2.2 m (MvPolynomial.support_smul hm)⟩

theorem exists_lift_integers (K : Type) [Field K] [NumberField K] (V L : Type) [CommRing V] [IsDomain V]
    [IsIntegrallyClosed V] [Field L] [Algebra V L] [IsFractionRing V L] (io : K →+* L) :
    ∃ φ : 𝓞 K →+* V, ∀ x : 𝓞 K, algebraMap V L (φ x) = io (x : K) := by
  have h : ∀ x : 𝓞 K, ∃ z : V, algebraMap V L z = io (x : K) := fun x =>
    IsIntegrallyClosed.algebraMap_eq_of_integral
      (IsIntegral.tower_top (R := ℤ) (map_isIntegral_int io x.isIntegral_coe))
  choose g hg using h
  have inj := IsFractionRing.injective V L
  refine ⟨⟨⟨⟨g, inj ?_⟩, fun x y => inj ?_⟩, inj ?_, fun x y => inj ?_⟩, hg⟩ <;> simp [hg]

theorem exists_combination_integers (K : Type) [Field K] [NumberField K] (T : CDVR) (io : K →+* T.Fr)
    (Ty : Type) (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
    (P : MvPolynomial (Letter Ty r n) T.Fr) (hP : P ∈ HaO r n T.Fr (algebraMap T.V T.Fr).range cc isX a) :
    ∃ (s : ℕ) (c : Fin s → T.V) (Q : Fin s → MvPolynomial (Letter Ty r n) K),
      (∀ j, Q j ∈ HaO r n K (integralClosure ℤ K).toSubring cc isX a) ∧
      P = ∑ j, algebraMap T.V T.Fr (c j) • MvPolynomial.map io (Q j) := by
  classical
  obtain ⟨φ, hφ⟩ := exists_lift_integers K T.V T.Fr io
  let p : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal T.V).comap φ
  haveI hp : p.IsPrime := Ideal.comap_isPrime _ _
  have hS : p.primeCompl ≤ nonZeroDivisors (𝓞 K) := p.primeCompl_le_nonZeroDivisors
  let V := Localization.subalgebra.ofField K p.primeCompl hS
  haveI : IsLocalRing V := IsLocalization.AtPrime.isLocalRing V p
  haveI : IsDedekindDomain V := IsLocalization.isDedekindDomain (𝓞 K) hS V
  haveI : IsPrincipalIdealRing V :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain V).out 2 0).1 ‹IsDedekindDomain V›
  have hu : ∀ s : p.primeCompl, IsUnit (φ s) := fun s => by
    by_contra hn
    exact s.2 ((IsLocalRing.mem_maximalIdeal _).2 hn)
  have hV : ∀ x : V, io (algebraMap V K x) ∈ (algebraMap T.V T.Fr).range := by
    rintro ⟨x, a, s, hs, rfl⟩
    obtain ⟨u, hu'⟩ := hu ⟨s, hs⟩
    refine ⟨φ a * (u⁻¹ : T.Vˣ), ?_⟩
    change _ = io (algebraMap _ K a * (algebraMap _ K s)⁻¹)
    rw [map_mul, map_mul, map_inv₀, map_units_inv, hu', hφ, hφ]
  obtain ⟨s, c, Q, hc, hQ, hsum⟩ := GlobalTheory.exists_integral_combination_of_mem_HaO Ty r n V K T.Fr io _ hV cc isX a P hP
  have hden : ∀ j, ∃ b : p.primeCompl, ∀ m, (((b : 𝓞 K) : K) • Q j).coeff m ∈ (integralClosure ℤ K).toSubring := by
    intro j
    choose g hg using (hQ j).2
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples p.primeCompl (Q j).support g
    refine ⟨b, fun m => ?_⟩
    by_cases hm : m ∈ (Q j).support
    · obtain ⟨z, hz⟩ := hb m hm
      have : (((b : 𝓞 K) : K) • Q j).coeff m = (z : K) := by
        rw [MvPolynomial.coeff_smul, ← hg m]
        have := congrArg (algebraMap V K) hz
        rw [← IsScalarTower.algebraMap_apply, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply] at this
        exact this.symm
      rw [this]
      exact z.isIntegral_coe
    · rw [MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.1 hm, smul_zero]
      exact Subring.zero_mem _
  choose b hb using hden
  choose c' hc' using hc
  choose u hu' using hu
  refine ⟨s, fun j => c' j * ((u (b j))⁻¹ : T.Vˣ), fun j => ((b j : 𝓞 K) : K) • Q j,
    fun j => ⟨smul_mem_HHa _ (hQ j).1, hb j⟩, ?_⟩
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : io ((b j : 𝓞 K) : K) ≠ 0 := by
    rw [← hφ, ← hu']
    exact ((u (b j)).isUnit.map _).ne_zero
  beta_reduce
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map io), MvPolynomial.map_C, ← mul_assoc,
    ← map_mul, map_mul (algebraMap T.V T.Fr), map_units_inv, hu', hφ, hc', mul_assoc, inv_mul_cancel₀ h0, mul_one]

theorem totalDegree_le_DF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    (T : CDVR) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {P : MvPolynomial (LtN Dw n) T.Fr} (hP : P ∈ FFV (Dw := Dw) T a n) :
    P.totalDegree ≤ DF Dw a := by
  have key : ∀ m ∈ P.support, (m.sum fun _ e => e) = DF Dw a := by
    intro m hm
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, DF]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP.1.2.2 m hm τ i
  exact Finset.sup_le fun m' hm' => (key m' hm').le

theorem val_algebraMap_nonneg (T : CDVR) {F : Type} [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ))
    (hv : ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ)) (x : T.V) :
    0 ≤ v (algebraMap T.Fr F (algebraMap T.V T.Fr x)) := by
  by_cases hx : algebraMap T.V T.Fr x = 0
  · rw [hx, map_zero, AddValuation.map_zero]; exact le_top
  · rw [hv _ hx]
    exact_mod_cast GlobalTheory.vV_algebraMap_nonneg_dvr T x

theorem nval_le_of_val (T : CDVR) {F : Type} [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ))
    (hv : ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ))
    {x z : T.Fr} (hx : x ≠ 0) {ε : F} (hε : 0 ≤ v ε) {ρ : ℚ} (hρ : v (ε * algebraMap T.Fr F z) = (ρ : WithTop ℚ))
    {δ : ℝ} (hle : (ρ : ℝ) ≤ ((vV T.V x : ℤ) : ℚ) + δ) (e : ℕ) :
    nval T.V e z ≤ nval T.V e x + ((δ / e : ℝ) : EReal) := by
  have hz : z ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero, AddValuation.map_zero] at hρ
    exact WithTop.top_ne_coe hρ
  rw [AddValuation.map_mul, hv z hz] at hρ
  have h1 : (((vV T.V z : ℤ) : ℚ) : WithTop ℚ) ≤ (ρ : WithTop ℚ) := hρ ▸ le_add_of_nonneg_left hε
  have h2 : ((vV T.V z : ℤ) : ℚ) ≤ ρ := WithTop.coe_le_coe.1 h1
  have h3 : ((vV T.V z : ℤ) : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast h2
  rw [nval_of_ne hz, nval_of_ne hx, ← EReal.coe_add, EReal.coe_le_coe_iff, ← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg e)
  rw [Rat.cast_intCast] at hle
  linarith

theorem le_iInf_add_coe {ι : Sort*} {X : EReal} {g : ι → EReal} {δ : ℝ} (h : ∀ i, X ≤ g i + (δ : EReal)) :
    X ≤ (⨅ i, g i) + (δ : EReal) := by
  rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))]
  exact le_iInf fun i =>
    (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))).2 (h i)

end GlobalTheory.ThetaLeast
