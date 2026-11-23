import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LatticeFrames.LatticeHomothetyOfEqUnimodular
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Descent

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.CP

open QuadraticAlgebra

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ τ : K}

variable (Δ) in

def mkL (σ : K) : (K × Etau K τ) × (K × Etau K τ) →ₗ[K] Sp Δ τ where
  toFun p := (⟨p.1.1, σ * p.2.1⟩, ⟨⟨p.1.2.re, σ * p.2.2.re⟩, ⟨p.1.2.im, σ * p.2.2.im⟩⟩)
  map_add' a b := by ext <;> simp <;> ring
  map_smul' a b := by ext <;> simp <;> ring

theorem mkL_apply (σ : K) (v w : K × Etau K τ) :
    mkL Δ σ (v, w) = (⟨v.1, σ * w.1⟩, ⟨⟨v.2.re, σ * w.2.re⟩, ⟨v.2.im, σ * w.2.im⟩⟩) := rfl

theorem mkL_surj {σ : K} (hσ : σ ≠ 0) (x : Sp Δ τ) : ∃ v w, x = mkL Δ σ (v, w) := by
  refine ⟨(x.1.re, ⟨x.2.re.re, x.2.im.re⟩), (σ⁻¹ * x.1.im, ⟨σ⁻¹ * x.2.re.im, σ⁻¹ * x.2.im.im⟩), ?_⟩
  ext <;> simp [mkL_apply, hσ]

theorem mkL_inj {σ : K} (hσ : σ ≠ 0) {v w v' w' : K × Etau K τ} (h : mkL Δ σ (v, w) = mkL Δ σ (v', w')) : v = v' ∧ w = w' := by
  simp only [mkL_apply, Prod.mk.injEq, QuadraticAlgebra.mk.injEq, mul_right_inj' hσ] at h
  obtain ⟨⟨a, b⟩, ⟨c, d⟩, e, f⟩ := h
  exact ⟨Prod.ext a (QuadraticAlgebra.ext c e), Prod.ext b (QuadraticAlgebra.ext d f)⟩

def Mu (u : Etau K τ) (v : K × Etau K τ) : K × Etau K τ := (v.1, u * v.2)

theorem herm_mkL (c t σ : K) (v w v' w' : K × Etau K τ) : herm c (t • (1 : EL Δ τ)) (mkL Δ σ (v, w)) (mkL Δ σ (v', w')) =
    ⟨Bf τ c t v v' - Δ * σ ^ 2 * Bf τ c t w w', σ * (Bf τ c t w v' - Bf τ c t v w')⟩ := by
  ext <;> simp [herm, mkL_apply, Bf_apply, sigL, trace] <;> ring

theorem semi_mkL (σ : K) (u : Etau K τ) (v w : K × Etau K τ) : semi (ofE Δ u) (mkL Δ σ (v, w)) = mkL Δ σ (Mu u v, -Mu u w) := by
  ext <;> simp [semi, mkL_apply, Mu, sigL, ofE] <;> ring

theorem mul_mkL (σ : K) (u : Etau K τ) (v w : K × Etau K τ) :
    (((mkL Δ σ (v, w)).1, ofE Δ u * (mkL Δ σ (v, w)).2) : Sp Δ τ) = mkL Δ σ (Mu u v, Mu u w) := by
  ext <;> simp [mkL_apply, Mu, ofE] <;> ring

variable (Δ) in

def up (σ : K) (S : Set (K × Etau K τ)) : Set (Sp Δ τ) := {x | ∃ v ∈ S, ∃ w ∈ S, x = mkL Δ σ (v, w)}

theorem mem_up {σ : K} (hσ : σ ≠ 0) {S : Set (K × Etau K τ)} {v w : K × Etau K τ} : mkL Δ σ (v, w) ∈ up Δ σ S ↔ v ∈ S ∧ w ∈ S := by
  constructor
  · rintro ⟨v', hv', w', hw', h⟩
    obtain ⟨rfl, rfl⟩ := mkL_inj hσ h
    exact ⟨hv', hw'⟩
  · rintro ⟨hv, hw⟩
    exact ⟨v, hv, w, hw, rfl⟩

theorem up_inj {σ : K} (hσ : σ ≠ 0) {S S' : Set (K × Etau K τ)} (h : up Δ σ S = up Δ σ S') : S = S' := by
  ext p
  have key := congrArg (fun T => mkL Δ σ (p, p) ∈ T) h
  simpa [mem_up hσ] using key

theorem tor_up (σ : K) (z : (Etau K τ)ˣ) (S : Set (K × Etau K τ)) : tor Δ z '' up Δ σ S = up Δ σ (Mu (quo z) '' S) := by
  ext x
  constructor
  · rintro ⟨_, ⟨v, hv, w, hw, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, _, ⟨w, hw, rfl⟩, mul_mkL σ _ v w⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, w, hw, rfl⟩, mul_mkL σ _ v w⟩

theorem poly_mem {W : Type} [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W] (M : Submodule O W) (N : W → W)
    (hN : ∀ x ∈ M, N x ∈ M) {r : O} (h1 : IsUnit r) (h2 : IsUnit (2 + r)) {x : W} (hx : x ∈ M) :
    (algebraMap O K r)⁻¹ • (x + N x) - (algebraMap O K r * (2 + algebraMap O K r))⁻¹ • (N (N x) - (algebraMap O K r ^ 2 - 2) • N x + x) ∈ M := by
  obtain ⟨u, rfl⟩ := h1
  obtain ⟨u2, hu2⟩ := h2
  have e1 : (algebraMap O K ↑u)⁻¹ = algebraMap O K ↑u⁻¹ := (map_units_inv (algebraMap O K) u).symm
  have e2 : (algebraMap O K ↑u * (2 + algebraMap O K ↑u))⁻¹ = algebraMap O K ↑(u * u2)⁻¹ := by
    rw [map_units_inv, Units.val_mul, map_mul, hu2, map_add, map_ofNat]
  have e3 : algebraMap O K ↑u ^ 2 - 2 = algebraMap O K (↑u ^ 2 - 2) := by
    rw [map_sub, map_pow, map_ofNat]
  rw [e1, e2, e3, algebraMap_smul, algebraMap_smul, algebraMap_smul]
  exact M.sub_mem (M.smul_mem _ (M.add_mem hx (hN x hx)))
    (M.smul_mem _ (M.add_mem (M.sub_mem (hN _ (hN x hx)) (M.smul_mem _ (hN x hx))) hx))

theorem poly_Mu {r : K} (h1 : r ≠ 0) (h2 : 2 + r ≠ 0) (hr : r ^ 2 = 2 + τ) {a : Etau K τ} (ha : a = ω ∨ a = star ω) (x : K × Etau K τ) :
    Mu (r⁻¹ • (1 + a)) x = r⁻¹ • (x + Mu a x) - (r * (2 + r))⁻¹ • (Mu a (Mu a x) - (r ^ 2 - 2) • Mu a x + x) := by
  have hτ : τ = r ^ 2 - 2 := by linear_combination -hr
  subst hτ
  rcases ha with rfl | rfl <;> ext <;> simp [Mu] <;> field_simp <;> ring

theorem u_norm {r : K} (h1 : r ≠ 0) (hr : r ^ 2 = 2 + τ) : (r⁻¹ • (1 + ω) : Etau K τ) * (r⁻¹ • (1 + star ω)) = 1 := by
  ext <;> simp <;> field_simp <;> first | ring1 | linear_combination -hr | linear_combination -2 * hr

theorem Mu_Mu (a b : Etau K τ) (v : K × Etau K τ) : Mu a (Mu b v) = Mu (a * b) v := by simp [Mu, mul_assoc]

theorem Mu_one (v : K × Etau K τ) : Mu 1 v = v := by simp [Mu]

theorem omega_star : (ω : Etau K τ) * star ω = 1 := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

variable [IsDomain O] [IsDiscreteValuationRing O] {c t σ : K} {ε : Oˣ} {r : O}

private theorem exists_finset_up_span_eq_span (σ : K) (s : Finset (K × Etau K τ)) :
    ∃ t : Finset (Sp Δ τ), up Δ σ (Submodule.span O (s : Set (K × Etau K τ)) : Set (K × Etau K τ)) =
      ↑(Submodule.span O (t : Set (Sp Δ τ))) := by
  set M := Submodule.span O (s : Set (K × Etau K τ))
  have hM : M.FG := ⟨s, rfl⟩
  obtain ⟨t, ht⟩ := (hM.prod hM).map ((mkL Δ σ).restrictScalars O)
  refine ⟨t, ?_⟩
  rw [ht]
  ext x
  simp only [up, Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_map, Submodule.mem_prod,
    LinearMap.coe_restrictScalars]
  constructor
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact ⟨(v, w), ⟨hv, hw⟩, rfl⟩
  · rintro ⟨⟨v, w⟩, ⟨hv, hw⟩, rfl⟩
    exact ⟨v, hv, w, hw, rfl⟩

private theorem mu_image_eq_of_mu_omega_image_eq {M : Submodule O (K × Etau K τ)} {q : O} (h1 : IsUnit q) (h2 : IsUnit (2 + q))
    (hq : algebraMap O K q ^ 2 = 2 + τ) (hN : Mu ω '' (M : Set (K × Etau K τ)) = M) :
    Mu ((algebraMap O K q)⁻¹ • (1 + ω)) '' (M : Set (K × Etau K τ)) = M := by
  have hq1 : algebraMap O K q ≠ 0 := (h1.map (algebraMap O K)).ne_zero
  have hq2 : 2 + algebraMap O K q ≠ 0 := by
    have := (h2.map (algebraMap O K)).ne_zero
    rwa [map_add, map_ofNat] at this
  have hω : ∀ x ∈ M, Mu ω x ∈ M := by
    intro x hx
    have : Mu ω x ∈ Mu ω '' (M : Set (K × Etau K τ)) := ⟨x, hx, rfl⟩
    rwa [hN] at this
  have hω' : ∀ x ∈ M, Mu (star ω) x ∈ M := by
    intro x hx
    have : x ∈ (M : Set (K × Etau K τ)) := hx
    rw [← hN] at this
    obtain ⟨y, hy, rfl⟩ := this
    rw [Mu_Mu, mul_comm, omega_star, Mu_one]
    exact hy
  have key : ∀ a : Etau K τ, (a = ω ∨ a = star ω) → (∀ x ∈ M, Mu a x ∈ M) →
      ∀ x ∈ M, Mu ((algebraMap O K q)⁻¹ • (1 + a)) x ∈ M := by
    intro a ha hM x hx
    rw [poly_Mu hq1 hq2 hq ha x]
    exact poly_mem M (Mu a) hM h1 h2 hx
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact key ω (Or.inl rfl) hω y hy
  · intro hx
    refine ⟨Mu ((algebraMap O K q)⁻¹ • (1 + star ω)) x, key (star ω) (Or.inr rfl) hω' x hx, ?_⟩
    rw [Mu_Mu, u_norm hq1 hq, Mu_one]

theorem fix_up (L : IsLoc O Δ) (hσ : Δ * σ ^ 2 = algebraMap O K ε) (h1 : IsUnit r) (h2 : IsUnit (2 + r)) (hr : algebraMap O K r ^ 2 = 2 + τ)
    {S : Set (K × Etau K τ)} (hS : Uni O c t S) (hN : Mu ω '' S = S) :
    IsFix O c (ofE Δ ((algebraMap O K r)⁻¹ • (1 + ω))) (t • (1 : EL Δ τ)) (up Δ σ S) := by
  obtain ⟨s, hs⟩ := hS.fg
  subst hs
  set M := Submodule.span O (s : Set (K × Etau K τ))
  have hε : algebraMap O K ε ≠ 0 := (ε.isUnit.map (algebraMap O K)).ne_zero
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    exact hε (by rw [← hσ]; ring)
  have hst := mu_image_eq_of_mu_omega_image_eq h1 h2 hr hN
  refine ⟨exists_finset_up_span_eq_span σ s, ?_, ?_⟩
  · intro y
    obtain ⟨v, w, rfl⟩ := mkL_surj hσ0 y
    rw [mem_up hσ0]
    constructor
    · rintro ⟨hv, hw⟩ x ⟨v', hv', w', hw', rfl⟩
      rw [herm_mkL, (descent O K Δ L σ ε hσ _).1]
      refine ⟨?_, ?_⟩
      · obtain ⟨a, ha⟩ := (hS.dual v).1 hv v' hv'
        obtain ⟨b, hb⟩ := (hS.dual w).1 hw w' hw'
        exact ⟨a - ε * b, by rw [map_sub, map_mul, ha, hb, hσ]⟩
      · obtain ⟨a, ha⟩ := (hS.dual v).1 hv w' hw'
        obtain ⟨b, hb⟩ := (hS.dual w).1 hw v' hv'
        exact ⟨a - b, by rw [map_sub, ha, hb]⟩
    · intro h
      have h0 : (0 : K × Etau K τ) ∈ (M : Set (K × Etau K τ)) := M.zero_mem
      refine ⟨(hS.dual v).2 fun v' hv' => ?_, (hS.dual w).2 fun w' hw' => ?_⟩
      · have key := h _ ⟨v', hv', 0, h0, rfl⟩
        rw [herm_mkL, (descent O K Δ L σ ε hσ _).1] at key
        simpa using key.1
      · have key := h _ ⟨0, h0, w', hw', rfl⟩
        rw [herm_mkL, (descent O K Δ L σ ε hσ _).1] at key
        obtain ⟨a, ha⟩ := key.1
        simp only [map_zero, LinearMap.zero_apply, zero_sub] at ha
        rw [hσ] at ha
        refine ⟨-(↑ε⁻¹ * a), ?_⟩
        rw [map_neg, map_mul, map_units_inv, ha]
        field_simp
  · ext z
    constructor
    · rintro ⟨x, ⟨v, hv, w, hw, rfl⟩, rfl⟩
      rw [semi_mkL]
      refine ⟨_, ?_, _, ?_, rfl⟩
      · rw [← hst]
        exact ⟨v, hv, rfl⟩
      · have : Mu ((algebraMap O K r)⁻¹ • (1 + ω)) w ∈ (M : Set (K × Etau K τ)) := by
          rw [← hst]
          exact ⟨w, hw, rfl⟩
        exact M.neg_mem this
    · rintro ⟨v, hv, w, hw, rfl⟩
      obtain ⟨v', hv', rfl⟩ : v ∈ Mu ((algebraMap O K r)⁻¹ • (1 + ω)) '' (M : Set (K × Etau K τ)) := by
        rw [hst]
        exact hv
      obtain ⟨w', hw', rfl⟩ : w ∈ Mu ((algebraMap O K r)⁻¹ • (1 + ω)) '' (M : Set (K × Etau K τ)) := by
        rw [hst]
        exact hw
      refine ⟨mkL Δ σ (v', -w'), ⟨v', hv', -w', M.neg_mem hw', rfl⟩, ?_⟩
      rw [semi_mkL]
      congr 2
      ext <;> simp [Mu]

private theorem mkL_mu_half_one_add_omega_eq {R : K} (h1 : R ≠ 0) (h2 : 2 + R ≠ 0) (hr : R ^ 2 = 2 + τ) (v w : K × Etau K τ) :
    mkL Δ σ (Mu (R⁻¹ • (1 + ω)) v, Mu (R⁻¹ • (1 + ω)) w) =
      R⁻¹ • (mkL Δ σ (v, w) + mkL Δ σ (Mu ω v, Mu ω w)) -
        (R * (2 + R))⁻¹ • (mkL Δ σ (Mu ω (Mu ω v), Mu ω (Mu ω w)) - (R ^ 2 - 2) • mkL Δ σ (Mu ω v, Mu ω w) +
          mkL Δ σ (v, w)) := by
  rw [poly_Mu h1 h2 hr (Or.inl rfl) v, poly_Mu h1 h2 hr (Or.inl rfl) w]
  ext <;> simp [mkL_apply] <;> ring

private theorem sq_inv_smul_one_add_omega_eq_omega {R : K} (h1 : R ≠ 0) (hr : R ^ 2 = 2 + τ) :
    (R⁻¹ • (1 + ω) : Etau K τ) * (R⁻¹ • (1 + ω)) = ω := by
  ext <;> simp <;> field_simp <;>
    first | ring1 | linear_combination hr | linear_combination -hr | linear_combination 2 * hr | linear_combination -2 * hr

private theorem isInt_herm_mkL_iff_bf_integral (L : IsLoc O Δ) (hσ : Δ * σ ^ 2 = algebraMap O K ε) (hσ0 : σ ≠ 0)
    (v w v' w' : K × Etau K τ) :
    IsInt O (herm c (t • (1 : EL Δ τ)) (mkL Δ σ (v', w')) (mkL Δ σ (v, w))) ↔
      (Bf τ c t v' v - algebraMap O K ε * Bf τ c t w' w ∈ (algebraMap O K).range ∧
        Bf τ c t w' v - Bf τ c t v' w ∈ (algebraMap O K).range) := by
  rw [herm_mkL, (descent O K Δ L σ ε hσ _).1, hσ]
  exact and_congr Iff.rfl
    ⟨fun ⟨b, hb⟩ => ⟨b, ((mul_right_inj' hσ0).1 hb).symm⟩, fun ⟨b, hb⟩ => ⟨b, by rw [← hb]⟩⟩

theorem fix_down (L : IsLoc O Δ) (hσ : Δ * σ ^ 2 = algebraMap O K ε) (h1 : IsUnit r) (h2 : IsUnit (2 + r)) (hr : algebraMap O K r ^ 2 = 2 + τ)
    {T : Set (Sp Δ τ)} (hT : IsFix O c (ofE Δ ((algebraMap O K r)⁻¹ • (1 + ω))) (t • (1 : EL Δ τ)) T) :
    ∃ S, Uni O c t S ∧ Mu ω '' S = S ∧ T = up Δ σ S := by
  obtain ⟨t0, ht0⟩ := hT.fg
  subst ht0
  obtain ⟨U, hU⟩ : ∃ U : Etau K τ, U = (algebraMap O K r)⁻¹ • (1 + ω) := ⟨_, rfl⟩
  rw [← hU] at hT
  set M := Submodule.span O (t0 : Set (Sp Δ τ)) with hMdef
  have hε : algebraMap O K ε ≠ 0 := (ε.isUnit.map (algebraMap O K)).ne_zero
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    exact hε (by rw [← hσ]; ring)
  have hR1 : algebraMap O K r ≠ 0 := (h1.map (algebraMap O K)).ne_zero
  have hR2 : 2 + algebraMap O K r ≠ 0 := by
    have := (h2.map (algebraMap O K)).ne_zero
    rwa [map_add, map_ofNat] at this
  have hUU : U * U = ω := by
    rw [hU]
    exact sq_inv_smul_one_add_omega_eq_omega hR1 hr
  have hneg : ∀ (a : Etau K τ) (x : K × Etau K τ), Mu a (-x) = -Mu a x := by
    intro a x
    ext <;> simp [Mu]
  have hMu0 : ∀ a : Etau K τ, Mu a 0 = 0 := by
    intro a
    ext <;> simp [Mu]
  have hstab := hT.stab
  have hφ : ∀ x ∈ M, semi (ofE Δ U) x ∈ M := by
    intro x hx
    have : semi (ofE Δ U) x ∈ semi (ofE Δ U) '' (M : Set (Sp Δ τ)) := ⟨x, hx, rfl⟩
    rwa [hstab] at this
  have hφ' : ∀ y ∈ M, ∃ x ∈ M, semi (ofE Δ U) x = y := by
    intro y hy
    have : y ∈ (M : Set (Sp Δ τ)) := hy
    rw [← hstab] at this
    obtain ⟨x, hx, e⟩ := this
    exact ⟨x, hx, e⟩
  have hss : ∀ a b, semi (ofE Δ U) (semi (ofE Δ U) (mkL Δ σ (a, b))) = mkL Δ σ (Mu ω a, Mu ω b) := by
    intro a b
    rw [semi_mkL, semi_mkL, hneg, neg_neg, Mu_Mu, Mu_Mu, hUU]
  have hA : ∀ v w, mkL Δ σ (v, w) ∈ M → mkL Δ σ (Mu U v, Mu U w) ∈ M := by
    intro v w h
    have key := poly_mem (K := K) M (fun x => semi (ofE Δ U) (semi (ofE Δ U) x))
      (fun x hx => hφ _ (hφ x hx)) h1 h2 h
    simp only [hss] at key
    rw [hU, mkL_mu_half_one_add_omega_eq hR1 hR2 hr]
    exact key
  obtain ⟨h2u, hh⟩ := L.two
  have hK : algebraMap O K ↑h2u⁻¹ * 2 = 1 := by
    have : algebraMap O K (↑h2u⁻¹ * ↑h2u) = 1 := by simp
    rwa [map_mul, hh, map_ofNat] at this
  have hsplit : ∀ v w, mkL Δ σ (v, w) ∈ M → mkL Δ σ (v, 0) ∈ M ∧ mkL Δ σ (0, w) ∈ M := by
    intro v w h
    obtain ⟨x, hx, hxe⟩ := hφ' _ h
    obtain ⟨a, b, rfl⟩ := mkL_surj hσ0 x
    rw [semi_mkL] at hxe
    obtain ⟨rfl, rfl⟩ := mkL_inj hσ0 hxe
    have hAx := hA a b hx
    have hφx := hφ _ hx
    rw [semi_mkL] at hφx
    constructor
    · have e : ((Mu U a, 0) : (K × Etau K τ) × (K × Etau K τ)) =
          algebraMap O K ↑h2u⁻¹ • ((Mu U a, Mu U b) + (Mu U a, -Mu U b)) := by
        rw [Prod.mk_add_mk, add_neg_cancel, ← two_smul K (Mu U a), Prod.smul_mk, smul_smul, hK, one_smul,
          smul_zero]
      rw [e, map_smul, map_add, algebraMap_smul]
      exact M.smul_mem _ (M.add_mem hAx hφx)
    · have e : ((0, -Mu U b) : (K × Etau K τ) × (K × Etau K τ)) =
          algebraMap O K ↑h2u⁻¹ • ((Mu U a, -Mu U b) - (Mu U a, Mu U b)) := by
        rw [Prod.mk_sub_mk, sub_self, ← neg_add', ← two_smul K (Mu U b), Prod.smul_mk, smul_zero, smul_neg,
          smul_smul, hK, one_smul]
      rw [e, map_smul, map_sub, algebraMap_smul]
      exact M.smul_mem _ (M.sub_mem hφx hAx)
  have hswap1 : ∀ w, mkL Δ σ (0, w) ∈ M → mkL Δ σ (w, 0) ∈ M := by
    intro w hw
    show mkL Δ σ (w, 0) ∈ (M : Set (Sp Δ τ))
    refine (hT.dual _).2 fun x hx => ?_
    obtain ⟨v', w', rfl⟩ := mkL_surj hσ0 x
    obtain ⟨hv'0, h0w'⟩ := hsplit v' w' hx
    have k1 := (hT.dual (mkL Δ σ (0, w))).1 hw (mkL Δ σ (v', 0)) hv'0
    have k2 := (hT.dual (mkL Δ σ (0, w))).1 hw (mkL Δ σ (0, w')) h0w'
    rw [isInt_herm_mkL_iff_bf_integral L hσ hσ0] at k1 k2 ⊢
    simp only [map_zero, LinearMap.zero_apply, mul_zero, sub_zero, zero_sub] at k1 k2 ⊢
    refine ⟨by simpa using (algebraMap O K).range.neg_mem k1.2, ?_⟩
    obtain ⟨a, ha⟩ := k2.1
    refine ⟨-(↑ε⁻¹ * a), ?_⟩
    rw [map_neg, map_mul, map_units_inv, ha]
    field_simp
  have hswap2 : ∀ v, mkL Δ σ (v, 0) ∈ M → mkL Δ σ (0, v) ∈ M := by
    intro v hv
    show mkL Δ σ (0, v) ∈ (M : Set (Sp Δ τ))
    refine (hT.dual _).2 fun x hx => ?_
    obtain ⟨v', w', rfl⟩ := mkL_surj hσ0 x
    obtain ⟨hv'0, h0w'⟩ := hsplit v' w' hx
    have k1 := (hT.dual (mkL Δ σ (v, 0))).1 hv (mkL Δ σ (v', 0)) hv'0
    have k2 := (hT.dual (mkL Δ σ (v, 0))).1 hv (mkL Δ σ (w', 0)) (hswap1 w' h0w')
    rw [isInt_herm_mkL_iff_bf_integral L hσ hσ0] at k1 k2 ⊢
    simp only [map_zero, LinearMap.zero_apply, mul_zero, sub_zero, zero_sub] at k1 k2 ⊢
    exact ⟨(algebraMap O K).range.neg_mem ((algebraMap O K).range.mul_mem ⟨↑ε, rfl⟩ k2.1),
      (algebraMap O K).range.neg_mem k1.1⟩
  refine ⟨{v | mkL Δ σ (v, 0) ∈ M}, ⟨?_, ?_⟩, ?_, ?_⟩
  · have inj : Function.Injective (mkL (τ := τ) Δ σ) := fun p q h => Prod.ext_iff.2 (mkL_inj hσ0 h)
    have surj : Function.Surjective (mkL (τ := τ) Δ σ) := fun x => by
      obtain ⟨v, w, h⟩ := mkL_surj hσ0 x
      exact ⟨(v, w), h.symm⟩
    let e := LinearEquiv.ofBijective (mkL (τ := τ) Δ σ) ⟨inj, surj⟩
    have he : ∀ a b, e.symm (mkL Δ σ (a, b)) = (a, b) := fun a b => e.symm_apply_apply (a, b)
    let p := ((LinearMap.fst K (K × Etau K τ) (K × Etau K τ)).comp e.symm.toLinearMap).restrictScalars O
    have hp : ∀ a b, p (mkL Δ σ (a, b)) = a := by
      intro a b
      simp [p, he]
    obtain ⟨s, hs⟩ := Submodule.FG.map p (⟨t0, rfl⟩ : M.FG)
    refine ⟨s, ?_⟩
    rw [hs]
    ext v
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_map]
    constructor
    · intro hv
      exact ⟨_, hv, hp v 0⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, b, rfl⟩ := mkL_surj hσ0 x
      rw [hp]
      exact (hsplit a b hx).1
  · intro y
    constructor
    · intro hy x hx
      have k := (hT.dual (mkL Δ σ (y, 0))).1 hy (mkL Δ σ (x, 0)) hx
      rw [isInt_herm_mkL_iff_bf_integral L hσ hσ0] at k
      simp only [map_zero, LinearMap.zero_apply, mul_zero, sub_zero] at k
      exact k.1
    · intro h
      show mkL Δ σ (y, 0) ∈ (M : Set (Sp Δ τ))
      refine (hT.dual _).2 fun x hx => ?_
      obtain ⟨v', w', rfl⟩ := mkL_surj hσ0 x
      obtain ⟨hv'0, h0w'⟩ := hsplit v' w' hx
      rw [isInt_herm_mkL_iff_bf_integral L hσ hσ0]
      simp only [map_zero, LinearMap.zero_apply, mul_zero, sub_zero]
      exact ⟨h v' hv'0, h w' (hswap1 w' h0w')⟩
  · ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      have key := hφ _ (hφ (mkL Δ σ (a, 0)) ha)
      rw [hss, hMu0] at key
      exact key
    · intro hv
      obtain ⟨x1, hx1, e1⟩ := hφ' (mkL Δ σ (v, 0)) hv
      obtain ⟨x0, hx0, e0⟩ := hφ' _ hx1
      obtain ⟨a, b, rfl⟩ := mkL_surj hσ0 x0
      rw [← e0, hss] at e1
      exact ⟨a, (hsplit a b hx0).1, (mkL_inj hσ0 e1).1⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨v, w, rfl⟩ := mkL_surj hσ0 x
      obtain ⟨h1', h2'⟩ := hsplit v w hx
      exact ⟨v, h1', w, hswap1 w h2', rfl⟩
    · rintro ⟨v, hv, w, hw, rfl⟩
      have hv' : mkL Δ σ (v, 0) ∈ M := hv
      have hw' : mkL Δ σ (w, 0) ∈ M := hw
      have key := M.add_mem hv' (hswap2 w hw')
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add] at key
      exact key

end UpperTheory.V.Z.Sym.Loc.CP
