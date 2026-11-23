import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LatticeFrames.ExistsPsi

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.CP

open QuadraticAlgebra

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}

theorem lat_basis (L : IsLoc O Δ) (hD : τ ^ 2 - 4 ≠ 0) {Λ : Set (Etau K τ)} (h : IsLat O τ Λ) :
    ∃ y₁ y₂ : Etau K τ, (y₂ * star y₁).im ≠ 0 ∧ ∀ b, b ∈ Λ ↔ ∃ p q : O, b = algebraMap O K p • y₁ + algebraMap O K q • y₂ := by
  obtain ⟨y, x, hx, -, -, rfl⟩ := latCls O K Δ τ L hD Λ h
  have hs : ∀ (p : O) (z : Etau K τ), p • z = algebraMap O K p • z := fun p z => (algebraMap_smul K p z).symm
  have hn : QuadraticAlgebra.norm (y : Etau K τ) ≠ 0 :=
    (QuadraticAlgebra.isUnit_iff_norm_isUnit.mp y.isUnit).ne_zero
  refine ⟨y, y * x, ?_, ?_⟩
  · have e : (y : Etau K τ) * x * star (y : Etau K τ) = x * algebraMap K _ (QuadraticAlgebra.norm (y : Etau K τ)) := by
      rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star]
      ring
    rw [e, QuadraticAlgebra.im_mul]
    simp
    exact ⟨hx, hn⟩
  · intro b
    simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_span_pair]
    constructor
    · rintro ⟨z, ⟨p, q, rfl⟩, rfl⟩
      refine ⟨p, q, ?_⟩
      rw [hs, hs, mul_add, mul_smul_comm, mul_smul_comm, mul_one]
    · rintro ⟨p, q, rfl⟩
      refine ⟨p • 1 + q • x, ⟨p, q, rfl⟩, ?_⟩
      rw [hs, hs, mul_add, mul_smul_comm, mul_smul_comm, mul_one]

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem mem_S0_of_sum_eq {s : K} {β y₁ y₂ : Etau K τ} {Λ : Set (Etau K τ)} (h : ∀ b, b ∈ Λ ↔ ∃ p q : O, b = algebraMap O K p • y₁ + algebraMap O K q • y₂)
    {v : K × Etau K τ} : v ∈ S0 s β Λ ↔ psi s β v y₁ ∈ Λ ∧ psi s β v y₂ ∈ Λ := by
  simp only [S0, Set.mem_setOf_eq]
  constructor
  · intro hv
    exact ⟨hv _ ((h _).2 ⟨1, 0, by simp⟩), hv _ ((h _).2 ⟨0, 1, by simp⟩)⟩
  · rintro ⟨h1, h2⟩ y hy
    obtain ⟨p, q, rfl⟩ := (h _).1 hy
    obtain ⟨p1, q1, e1⟩ := (h _).1 h1
    obtain ⟨p2, q2, e2⟩ := (h _).1 h2
    refine (h _).2 ⟨p * p1 + q * p2, p * q1 + q * q2, ?_⟩
    rw [map_add, map_smul, map_smul, e1, e2]
    simp only [map_add, map_mul, smul_add, smul_smul, add_smul]
    abel

variable {c t s : K} {ε : Oˣ} {β : Etau K τ}

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem Bf_int (L2 : IsUnit (2 : O)) (hc : c = (τ ^ 2 - 4) * algebraMap O K ε * s ^ 2) (hβ : QuadraticAlgebra.norm β * algebraMap O K ε * s ^ 2 = 2 * t)
    {y₁ y₂ : Etau K τ} (hg : (y₂ * star y₁).im ≠ 0) {Λ : Set (Etau K τ)}
    (h : ∀ b, b ∈ Λ ↔ ∃ p q : O, b = algebraMap O K p • y₁ + algebraMap O K q • y₂) {v w : K × Etau K τ} (hv : v ∈ S0 s β Λ) (hw : w ∈ S0 s β Λ) :
    Bf τ c t v w ∈ (algebraMap O K).range := by
  have hadd : ∀ a b, a ∈ Λ → b ∈ Λ → a + b ∈ Λ := by
    intro a b ha hb
    obtain ⟨p, q, rfl⟩ := (h _).1 ha
    obtain ⟨p', q', rfl⟩ := (h _).1 hb
    refine (h _).2 ⟨p + p', q + q', ?_⟩
    simp only [map_add, add_smul]
    abel
  have hsm : ∀ (r : O) a, a ∈ Λ → algebraMap O K r • a ∈ Λ := by
    intro r a ha
    obtain ⟨p, q, rfl⟩ := (h _).1 ha
    refine (h _).2 ⟨r * p, r * q, ?_⟩
    simp only [map_mul, smul_add, smul_smul]
  have h1 : y₁ ∈ Λ := (h _).2 ⟨1, 0, by simp⟩
  have key : (2 * Bf τ c t v w) • y₁ ∈ Λ := by
    rw [← psi_anti hc hβ v w y₁]
    exact hsm ε _ (hadd _ _ (hv _ (hw _ h1)) (hw _ (hv _ h1)))
  obtain ⟨p, q, e⟩ := (h _).1 key
  have e' : (2 * Bf τ c t v w) • y₁ + (0 : K) • y₂ = algebraMap O K p • y₁ + algebraMap O K q • y₂ := by
    rw [zero_smul, add_zero]
    exact e
  obtain ⟨e1, -⟩ := coord_uniq hg e'
  refine ⟨((L2.unit⁻¹ : Oˣ) : O) * p, ?_⟩
  have h2 : algebraMap O K ((L2.unit⁻¹ : Oˣ) : O) * 2 = 1 := by
    rw [← map_ofNat (algebraMap O K) 2, ← map_mul, IsUnit.val_inv_mul, map_one]
  rw [map_mul, ← e1, ← mul_assoc, h2, one_mul]

theorem isUnimodular_cliffordLatticeStabilizer (L : IsLoc O Δ) (hD : τ ^ 2 - 4 ≠ 0) (hs : s ≠ 0) (hu : IsUnit β) (hc : c = (τ ^ 2 - 4) * algebraMap O K ε * s ^ 2)
    (hβ : QuadraticAlgebra.norm β * algebraMap O K ε * s ^ 2 = 2 * t) {Λ : Set (Etau K τ)} (hΛ : IsLat O τ Λ) : Uni O c t (S0 s β Λ) := by
  obtain ⟨y₁, y₂, hg, hΛ'⟩ := lat_basis L hD hΛ
  have h2K : (2 : K) ≠ 0 := by
    have := (L.two.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  have hεK : algebraMap O K ε ≠ 0 := ((ε.isUnit).map (algebraMap O K)).ne_zero
  obtain ⟨e, f, k, he1, he2, hf1, hf2, hk1, hk2⟩ := exists_efh hD h2K hs hu hg
  have ev1 : ∀ a b d : K, psi s β (a • e + b • f + d • k) y₁ = (-d) • y₁ + b • y₂ := by
    intro a b d
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, he1, hf1, hk1]
    module
  have ev2 : ∀ a b d : K, psi s β (a • e + b • f + d • k) y₂ = a • y₁ + d • y₂ := by
    intro a b d
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, he2, hf2, hk2]
    module
  have dec : ∀ v : K × Etau K τ, ∃ a b d : K, v = a • e + b • f + d • k := by
    intro v
    obtain ⟨α, b, h1⟩ : ∃ α b : K, psi s β v y₁ = α • y₁ + b • y₂ := ⟨_, _, coord hg _⟩
    obtain ⟨a, δ, h2⟩ : ∃ a δ : K, psi s β v y₂ = a • y₁ + δ • y₂ := ⟨_, _, coord hg _⟩
    have A1 := psi_anti hc hβ v k y₁
    have A2 := psi_anti hc hβ v k y₂
    simp only [hk1, hk2, map_neg, h1, h2, map_add, map_smul] at A1 A2
    have E1 : (algebraMap O K ε * (-2 * α)) • y₁ + (0 : K) • y₂ = (2 * Bf τ c t v k) • y₁ + (0 : K) • y₂ := by
      rw [← A1]
      module
    have E2 : (0 : K) • y₁ + (algebraMap O K ε * (2 * δ)) • y₂ = (0 : K) • y₁ + (2 * Bf τ c t v k) • y₂ := by
      rw [← A2]
      module
    obtain ⟨r1, -⟩ := coord_uniq hg E1
    obtain ⟨-, r2⟩ := coord_uniq hg E2
    have hδ : δ = -α := by
      have := mul_left_cancel₀ hεK (r2.trans r1.symm)
      exact mul_left_cancel₀ h2K (by linear_combination this)
    refine ⟨a, b, -α, ?_⟩
    rw [← sub_eq_zero]
    refine psi_inj hD hs hu (fun y => ?_)
    rw [coord hg y]
    simp only [map_sub, LinearMap.sub_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      h1, h2, he1, he2, hf1, hf2, hk1, hk2, hδ]
    module
  have pair : ∀ x z : K, (∃ p q : O, x • y₁ + z • y₂ = algebraMap O K p • y₁ + algebraMap O K q • y₂) ↔
      x ∈ (algebraMap O K).range ∧ z ∈ (algebraMap O K).range := by
    intro x z
    constructor
    · rintro ⟨p, q, hpq⟩
      obtain ⟨r1, r2⟩ := coord_uniq hg hpq
      exact ⟨RingHom.mem_range.mpr ⟨p, r1.symm⟩, RingHom.mem_range.mpr ⟨q, r2.symm⟩⟩
    · rintro ⟨hx, hz⟩
      obtain ⟨p, rfl⟩ := RingHom.mem_range.mp hx
      obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hz
      exact ⟨p, q, rfl⟩
  have memc : ∀ a b d : K, a • e + b • f + d • k ∈ S0 s β Λ ↔
      a ∈ (algebraMap O K).range ∧ b ∈ (algebraMap O K).range ∧ d ∈ (algebraMap O K).range := by
    intro a b d
    rw [mem_S0_of_sum_eq hΛ', ev1, ev2, hΛ', hΛ', pair, pair, neg_mem_iff]
    tauto
  have ind : ∀ a b d a' b' d' : K, a • e + b • f + d • k = a' • e + b' • f + d' • k → a = a' ∧ b = b' ∧ d = d' := by
    intro a b d a' b' d' hv
    have q1 := congrArg (fun v => psi s β v y₁) hv
    have q2 := congrArg (fun v => psi s β v y₂) hv
    simp only [ev1, ev2] at q1 q2
    obtain ⟨u1, u2⟩ := coord_uniq hg q1
    obtain ⟨u3, -⟩ := coord_uniq hg q2
    exact ⟨u3, u2, neg_inj.mp u1⟩
  have gram : ∀ a b d : K, 2 * Bf τ c t e (a • e + b • f + d • k) = algebraMap O K ε * b ∧
      2 * Bf τ c t f (a • e + b • f + d • k) = algebraMap O K ε * a ∧
      Bf τ c t k (a • e + b • f + d • k) = algebraMap O K ε * d := by
    intro a b d
    have Ae := psi_anti hc hβ e (a • e + b • f + d • k) y₂
    have Af := psi_anti hc hβ f (a • e + b • f + d • k) y₁
    have Ak := psi_anti hc hβ k (a • e + b • f + d • k) y₁
    rw [ev2, he2, ev1, map_add, map_smul, map_smul, he1, he2] at Ae
    rw [ev1, hf1, ev2, map_add, map_smul, map_smul, hf1, hf2] at Af
    rw [ev1, hk1, map_neg, ev1, map_add, map_smul, map_smul, hk1, hk2] at Ak
    have Ee : (0 : K) • y₁ + (algebraMap O K ε * b) • y₂ = (0 : K) • y₁ + (2 * Bf τ c t e (a • e + b • f + d • k)) • y₂ := by
      rw [← Ae]
      module
    have Ef : (algebraMap O K ε * a) • y₁ + (0 : K) • y₂ = (2 * Bf τ c t f (a • e + b • f + d • k)) • y₁ + (0 : K) • y₂ := by
      rw [← Af]
      module
    have Ek : (2 * (algebraMap O K ε * d)) • y₁ + (0 : K) • y₂ = (2 * Bf τ c t k (a • e + b • f + d • k)) • y₁ + (0 : K) • y₂ := by
      rw [← Ak]
      module
    exact ⟨(coord_uniq hg Ee).2.symm, (coord_uniq hg Ef).1.symm, (mul_left_cancel₀ h2K (coord_uniq hg Ek).1).symm⟩
  refine ⟨?_, ?_⟩
  · classical
    refine ⟨{e, f, k}, ?_⟩
    ext v
    obtain ⟨a, b, d, rfl⟩ := dec v
    rw [memc]
    simp only [Finset.coe_insert, Finset.coe_singleton, SetLike.mem_coe, Submodule.mem_span_insert,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨hp, hq, hr⟩
      obtain ⟨p, rfl⟩ := RingHom.mem_range.mp hp
      obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hq
      obtain ⟨r, rfl⟩ := RingHom.mem_range.mp hr
      refine ⟨p, q • f + r • k, ⟨q, r • k, ⟨r, rfl⟩, rfl⟩, ?_⟩
      all_goals rw [algebraMap_smul, algebraMap_smul, algebraMap_smul, add_assoc]
    · rintro ⟨p, _, ⟨q, _, ⟨r, rfl⟩, rfl⟩, hv⟩
      rw [← algebraMap_smul K p e, ← algebraMap_smul K q f, ← algebraMap_smul K r k, ← add_assoc] at hv
      obtain ⟨u1, u2, u3⟩ := ind _ _ _ _ _ _ hv
      exact ⟨RingHom.mem_range.mpr ⟨p, u1.symm⟩, RingHom.mem_range.mpr ⟨q, u2.symm⟩, RingHom.mem_range.mpr ⟨r, u3.symm⟩⟩
  · intro y
    constructor
    · intro hy x hx
      exact Bf_int L.two hc hβ hg hΛ' hx hy
    · intro H
      obtain ⟨a, b, d, rfl⟩ := dec y
      have meme : e ∈ S0 s β Λ := by
        have := (memc 1 0 0).2 ⟨one_mem _, zero_mem _, zero_mem _⟩
        simpa using this
      have memf : f ∈ S0 s β Λ := by
        have := (memc 0 1 0).2 ⟨zero_mem _, one_mem _, zero_mem _⟩
        simpa using this
      have memk : k ∈ S0 s β Λ := by
        have := (memc 0 0 1).2 ⟨zero_mem _, zero_mem _, one_mem _⟩
        simpa using this
      obtain ⟨g1, g2, g3⟩ := gram a b d
      have hinv : algebraMap O K ↑ε⁻¹ * algebraMap O K ↑ε = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rw [memc]
      refine ⟨?_, ?_, ?_⟩
      · have ha : a = algebraMap O K (↑ε⁻¹ * 2) * Bf τ c t f (a • e + b • f + d • k) := by
          rw [map_mul, map_ofNat]
          linear_combination (-(algebraMap O K ↑ε⁻¹)) * g2 - a * hinv
        rw [ha]
        exact mul_mem (RingHom.mem_range_self _ _) (H f memf)
      · have hb : b = algebraMap O K (↑ε⁻¹ * 2) * Bf τ c t e (a • e + b • f + d • k) := by
          rw [map_mul, map_ofNat]
          linear_combination (-(algebraMap O K ↑ε⁻¹)) * g1 - b * hinv
        rw [hb]
        exact mul_mem (RingHom.mem_range_self _ _) (H e meme)
      · have hd : d = algebraMap O K ↑ε⁻¹ * Bf τ c t k (a • e + b • f + d • k) := by
          linear_combination (-(algebraMap O K ↑ε⁻¹)) * g3 - d * hinv
        rw [hd]
        exact mul_mem (RingHom.mem_range_self _ _) (H k memk)

end UpperTheory.V.Z.Sym.Loc.CP
