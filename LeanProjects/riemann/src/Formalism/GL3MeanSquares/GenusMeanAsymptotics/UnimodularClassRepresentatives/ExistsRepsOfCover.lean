import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho

open Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace OrbSum

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

theorem exists_reps_of_cover (A : Set X) (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) (C : Set X)
    (hC : C.Finite) (hCA : ∀ c ∈ C, c ∈ A) (hcov : ∀ x ∈ A, ∃ c ∈ C, ∃ g : G, g • c = x) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ x ∈ A, ∃! t, t ∈ T ∧ ∃ g : G, g • t = x := by
  classical
  let rep : X → X := fun x => (Quotient.mk (MulAction.orbitRel G X) x).out
  have hrep : ∀ x, ∃ g : G, g • x = rep x := fun x => by
    have h1 : Quotient.mk (MulAction.orbitRel G X) (rep x) = Quotient.mk _ x := Quotient.out_eq _
    have h2 : rep x ∈ MulAction.orbit G x := Quotient.exact h1
    exact MulAction.mem_orbit_iff.1 h2
  have hrepA : ∀ x ∈ A, rep x ∈ A := fun x hx => by
    obtain ⟨g, hg⟩ := hrep x
    rw [← hg]
    exact hA g x hx
  have hrep_eq : ∀ x y : X, ∀ g : G, g • y = x → rep y = rep x := fun x y g hg => by
    show (Quotient.mk (MulAction.orbitRel G X) y).out = (Quotient.mk (MulAction.orbitRel G X) x).out
    congr 1
    apply Quotient.sound
    show y ∈ MulAction.orbit G x
    rw [MulAction.mem_orbit_iff]
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  refine ⟨hC.toFinset.image rep, ?_, ?_⟩
  · intro t ht
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 ht
    exact hrepA c (hCA c (hC.mem_toFinset.1 hc))
  · intro x hx
    obtain ⟨c, hc, g, hg⟩ := hcov x hx
    obtain ⟨g', hg'⟩ := hrep c
    refine ⟨rep c, ⟨Finset.mem_image.2 ⟨c, hC.mem_toFinset.2 hc, rfl⟩, ⟨g * g'⁻¹, ?_⟩⟩, ?_⟩
    · rw [← hg', mul_smul, inv_smul_smul, hg]
    · rintro t ⟨ht, h, hh⟩
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨g'', hg''⟩ := hrep c'
      have e1 : rep c' = rep x := (hrep_eq (rep c') c' g'' hg'').trans (hrep_eq x (rep c') h hh)
      have e2 : rep c = rep x := hrep_eq x c g hg
      rw [e1, e2]

theorem card_stab_smul (g : G) (x : X) :
    Nat.card (MulAction.stabilizer G (g • x)) = Nat.card (MulAction.stabilizer G x) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_stab_sub (π : X → Y) (hπ : ∀ (g : G) x, π (g • x) = g • π x) (x : X) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer G (π x)) x) =
      Nat.card (MulAction.stabilizer G x) := Nat.card_congr
  { toFun := fun h => ⟨h.1.1, h.2⟩
    invFun := fun g => ⟨⟨g.1, by
      show g.1 • π x = π x
      rw [← hπ]
      exact congrArg π g.2⟩, g.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem sum_orbits_on (π : X → Y) (hπ : ∀ (g : G) x, π (g • x) = g • π x) (A : Set X) (B : Set Y)
    (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) (hAB : ∀ x ∈ A, π x ∈ B)
    (sX : Finset X) (sY : Finset Y) (hsX : ∀ t ∈ sX, t ∈ A) (hsY : ∀ u ∈ sY, u ∈ B)
    (hX : ∀ x ∈ A, ∃! t : X, t ∈ sX ∧ ∃ g : G, g • t = x)
    (hY : ∀ y ∈ B, ∃! t : Y, t ∈ sY ∧ ∃ g : G, g • t = y)
    (hfinY : ∀ y ∈ B, (MulAction.stabilizer G y : Set G).Finite) :
    ∑ t ∈ sX, ((Nat.card (MulAction.stabilizer G t) : ℕ) : ℝ)⁻¹ =
      ∑ u ∈ sY, (Nat.card {x // x ∈ A ∧ π x = u} : ℝ) /
        (Nat.card (MulAction.stabilizer G u) : ℝ) := by
  classical
  have key : ∀ t : X, ∃ (u : Y) (g : G), t ∈ A → (u ∈ sY ∧ g • u = π t) := by
    intro t
    by_cases ht : t ∈ A
    · obtain ⟨u, ⟨hu, g, hg⟩, -⟩ := hY (π t) (hAB t ht)
      exact ⟨u, g, fun _ => ⟨hu, hg⟩⟩
    · exact ⟨π t, 1, fun h => absurd h ht⟩
  choose U γ hU using key
  have hπ' : ∀ t ∈ A, π ((γ t)⁻¹ • t) = U t := by
    intro t ht
    rw [hπ, ← (hU t ht).2, inv_smul_smul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := sX) (t := sY) (g := U)
    (fun t ht => (hU t (hsX t ht)).1)]
  refine Finset.sum_congr rfl fun u hu => ?_
  set T : Finset X := (sX.filter (fun t => U t = u)).image (fun t => (γ t)⁻¹ • t) with hTdef
  have hinj : Set.InjOn (fun t => (γ t)⁻¹ • t) (sX.filter (fun t => U t = u) : Set X) := by
    intro t₁ h₁ t₂ h₂ e
    have h₁' := (Finset.mem_filter.mp h₁).1
    have h₂' := (Finset.mem_filter.mp h₂).1
    exact (hX _ (hA (γ t₁)⁻¹ t₁ (hsX t₁ h₁'))).unique ⟨h₁', _, rfl⟩ ⟨h₂', _, e.symm⟩
  have hstab : ∀ g : MulAction.stabilizer G u, ∀ x ∈ {x : X | x ∈ A ∧ π x = u},
      g • x ∈ {x : X | x ∈ A ∧ π x = u} := by
    rintro ⟨g, hg⟩ x ⟨hx1, hx2⟩
    refine ⟨hA g x hx1, ?_⟩
    change π (g • x) = u
    rw [hπ, hx2]
    exact MulAction.mem_stabilizer_iff.mp hg
  have hTA : ∀ t ∈ T, t ∈ {x : X | x ∈ A ∧ π x = u} := by
    intro t ht
    obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨h₁, rfl⟩ := Finset.mem_filter.mp h₀
    exact ⟨hA _ _ (hsX t₀ h₁), hπ' t₀ (hsX t₀ h₁)⟩
  have hT : ∀ x ∈ {x : X | x ∈ A ∧ π x = u},
      ∃! t, t ∈ T ∧ ∃ g : MulAction.stabilizer G u, g • t = x := by
    rintro x ⟨hx1, hx2⟩
    obtain ⟨t, ⟨ht, g, hg⟩, huniq⟩ := hX x hx1
    have htA := hsX t ht
    have e1 : (g * γ t) • U t = u := by
      rw [mul_smul, (hU t htA).2, ← hπ, hg, hx2]
    have hUt : U t = u :=
      (hY u (hsY u hu)).unique ⟨(hU t htA).1, _, e1⟩ ⟨hu, 1, one_smul _ _⟩
    refine ⟨(γ t)⁻¹ • t, ⟨Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hUt⟩, rfl⟩,
      ⟨g * γ t, MulAction.mem_stabilizer_iff.mpr (by rw [← hUt] at e1 ⊢; exact e1)⟩, ?_⟩, ?_⟩
    · change (g * γ t) • (γ t)⁻¹ • t = x
      rw [mul_smul, smul_inv_smul, hg]
    · rintro t' ⟨ht', ⟨g', hg'm⟩, hg'⟩
      obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.mp ht'
      have h₀' := (Finset.mem_filter.mp h₀).1
      have : t₀ = t := huniq t₀ ⟨h₀', g' * (γ t₀)⁻¹, by rw [mul_smul]; exact hg'⟩
      rw [this]
  have hfinG : Finite (MulAction.stabilizer G u) := (hfinY u (hsY u hu)).to_subtype
  have hfinA : Finite ↥{x : X | x ∈ A ∧ π x = u} := by
    apply Set.Finite.to_subtype
    refine ((T : Set X).toFinite.biUnion
      (fun t _ => Set.finite_range (fun g : MulAction.stabilizer G u => g • t))).subset ?_
    intro x hx
    obtain ⟨t, ⟨ht, g, hg⟩, -⟩ := hT x hx
    exact Set.mem_biUnion (Finset.mem_coe.mpr ht) ⟨g, hg⟩
  have main := sum_inv_card_stab (G := MulAction.stabilizer G u) {x : X | x ∈ A ∧ π x = u}
    hstab T hTA hT
  have e0 : (Nat.card {x // x ∈ A ∧ π x = u} : ℝ) =
      (Nat.card ↥{x : X | x ∈ A ∧ π x = u} : ℝ) := rfl
  rw [e0, main, hTdef, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨ht1, rfl⟩ := Finset.mem_filter.mp ht
  have := card_stab_sub π hπ ((γ t)⁻¹ • t)
  rw [hπ' t (hsX t ht1)] at this
  rw [this, card_stab_smul]

end OrbSum

end Formalism.HermitianLattices.Ext.L3
