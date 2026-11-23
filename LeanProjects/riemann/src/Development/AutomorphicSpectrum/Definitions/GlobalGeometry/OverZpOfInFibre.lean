import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.ModelTest

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem isCp_two : IsCp 2 (4 : ℚ) := by
  unfold GlobalTheory.CompanionTheory.Ar.HT.IsCp
  simp

theorem isCp_exists (p : ℕ) (hp : p ≠ 0) : ∃ κ : ℂ, IsCp p κ := by
  by_cases h2 : p = 2
  · refine ⟨4, ?_⟩
    unfold GlobalTheory.CompanionTheory.Ar.HT.IsCp
    simp [h2]
  · refine ⟨Complex.exp (2 * Real.pi * Complex.I / p) - 1, ?_⟩
    unfold GlobalTheory.CompanionTheory.Ar.HT.IsCp
    rw [if_neg h2]
    exact ⟨_, Complex.isPrimitiveRoot_exp p hp, rfl⟩

theorem isCp_ne_zero {Ω : Type} [Field Ω] [CharZero Ω] {p : ℕ} (hp : p.Prime) {κ : Ω} (h : IsCp p κ) : κ ≠ 0 := by
  unfold GlobalTheory.CompanionTheory.Ar.HT.IsCp at h
  split_ifs at h with h2
  · rw [h]
    norm_num
  · obtain ⟨ζ, hζ, rfl⟩ := h
    exact sub_ne_zero.mpr (hζ.ne_one hp.one_lt)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem bar_eq (H : Host E) (a : 𝓞 E) : RingOfIntegers.mapRingEquiv (cmConj E) a = H.bar a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq a]
  rfl

theorem overZp_of_inFibre {p : ℕ} (hp : p.Prime) (q : Cpt 𝔐.ξ) (hq : InFibre 𝔐.ξ p q) : OverZp 𝔐 p q := by
  intro r hr hrq
  by_contra hne
  have hloc : IsLocalRing (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) :=
    IsLocalRing.of_surjective' (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict
      (GlobalTheory.CompanionTheory.Ar.genMap 𝔐.ξ q).rangeRestrict_surjective
  have key : ∀ m : ℕ, GlobalTheory.CompanionTheory.Ar.InFibre 𝔐.ξ m q → ¬ IsUnit ((m : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)) := by
    intro m hm hu
    apply hm
    obtain ⟨u, hu'⟩ := hu
    have h1 : (m : Ω) * (((u⁻¹ : (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q)ˣ) : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q) : Ω) = 1 := by
      have h2 := congrArg (fun x : GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q => (x : Ω)) u.mul_inv
      simpa [hu'] using h2
    have h0 : (m : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    refine ⟨h0, natCast_mem _ m, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact SetLike.coe_mem _
  have hcop : Nat.Coprime r p := (Nat.coprime_primes hr hp).2 hne
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (GlobalTheory.CompanionTheory.Ar.regAt 𝔐.ξ q))
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
  · exact key r hrq (by simpa using isUnit_of_mul_isUnit_right h)
  · exact key p hq (by simpa using isUnit_of_mul_isUnit_right h)

theorem omP_le (p : ℕ) (q : Cpt 𝔐.ξ) : omP 𝔐 p q ≤ 𝔐.M.omLat q := by
  unfold GlobalTheory.CompanionTheory.Ar.HT.omP GlobalTheory.CompanionTheory.Ar.LieModel.htOm
  refine Submodule.span_le.mpr ?_
  rintro w ⟨x, -, hx⟩
  exact hx.1

theorem dR_le (p : ℕ) (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ) :
    𝔐.dR s q ≤ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q := by
  intro e he
  apply Submodule.subset_span
  refine ⟨he.2, fun w hw => ?_⟩
  exact omP_le 𝔐 p q hw e he.1

theorem sandwich_iff (p : ℕ) (κ : Ω) : Sandwich 𝔐 p κ ↔ ∀ q, InFibre 𝔐.ξ p q → κ ∈ regAt 𝔐.ξ q ∧
    (∀ w ∈ 𝔐.M.omLat q, κ • w ∈ omP 𝔐 p q) ∧
    ∀ s, ∀ e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q, κ • e ∈ 𝔐.dR s q := by
  unfold GlobalTheory.CompanionTheory.Ar.HT.Sandwich
  constructor
  · intro h q hq
    obtain ⟨h1, -, h3, h4⟩ := h q hq
    exact ⟨h1, h3, fun s => (h4 s).2⟩
  · intro h q hq
    obtain ⟨h1, h3, h4⟩ := h q hq
    exact ⟨h1, omP_le 𝔐 p q, h3, fun s => ⟨dR_le 𝔐 p s q, h4 s⟩⟩

variable {𝔐} {p : ℕ} {o : Type} [CommRing o] [Algebra o Ω]
  {Dc Dc' : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)}

theorem side (h : IsHTFamily 𝔐 p o Dc) (s) (σ : 𝓞 E →+* Ω) (w : Module.Dual Ω 𝔐.Li)
    (hw : ∀ a, (Dc s).ρΩ a w = σ a • w) (t : CMType H ⊕ CMType H) (e : 𝔐.Li) (he : e ∈ 𝔐.Vgen t)
    (hne : w e ≠ 0) (a : 𝓞 E) : 𝔐.emb t (H.bar a) = σ a := by
  have h1 := congrArg (fun f : Module.Dual Ω 𝔐.Li => f e) ((h.act s a w).symm.trans (hw a))
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h1
  have he' : e ∈ GlobalTheory.CompanionTheory.Ar.eigSp 𝔐.ρ (𝔐.emb t) := he
  have h2 : 𝔐.ρ (H.bar a) e = 𝔐.emb t (H.bar a) • e := by
    have h3 := (Submodule.mem_iInf _).1 he' (H.bar a)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h3
    simpa using h3
  rw [h2, map_smul, smul_eq_mul] at h1
  exact mul_right_cancel₀ hne h1

theorem om_unique (h : IsHTFamily 𝔐 p o Dc) (h' : IsHTFamily 𝔐 p o Dc') (s) :
    (Dc s).om = (Dc' s).om ∧ (Dc s).ρΩ = (Dc' s).ρΩ := by
  refine ⟨?_, ?_⟩
  · ext w
    rw [h.om_iff s w, h'.om_iff s w]
  · exact RingHom.ext fun a => LinearMap.ext fun w => by rw [h.act s a w, h'.act s a w]

theorem pow_smul_mem (hp : p.Prime) (h : IsHTFamily 𝔐 p o Dc) (s) (q : Cpt 𝔐.ξ) (hs : InChart 𝔐.ξ (mseg y) s.1 q)
    (hq : InFibre 𝔐.ξ p q) (w) (hw : w ∈ (Dc s).om) : (p ^ 𝔐.R p) • w ∈ omP 𝔐 p q := by
  rw [h.om'_loc s q hs hq]
  apply Submodule.subset_span
  show (p ^ 𝔐.R p) • w ∈ (Dc s).om'
  unfold GlobalTheory.CompanionTheory.Ar.HT.HTChart.om'
  apply Submodule.mem_sup_right
  refine ⟨w, hw, ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

end GlobalTheory.CompanionTheory.Ar.HT.ModelTest
