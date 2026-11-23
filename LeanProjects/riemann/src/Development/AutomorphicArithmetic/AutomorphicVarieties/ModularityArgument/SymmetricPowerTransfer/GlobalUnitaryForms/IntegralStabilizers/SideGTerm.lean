import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.GqIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.CentFin
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Glob.sideGTerm :
    ∀ (Γ G V H : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [Group H] (B : Base Γ G V), B.Fin →
    ∀ (s : B.Tw) (f : G → ℂ), s.IsTest f → B.ω = 1 → B.Γ₀ = ⊥ → ∀ (δ n : Γ) (i : H →* Γ), n ∉ i.range →
    (∀ x, x⁻¹ * δ * s.θΓ x = δ ↔ x ∈ i.range ∨ n * x ∈ i.range) → ∀ (U : Subgroup G) (H₀ : Subgroup H), B.U = U → i.ker = H₀ →
    2 * s.term f δ = LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ) * gqOn (B.ι.comp i) H₀ U (fun y => f (y.out⁻¹ * B.ι δ * s.θ y.out)) := by
  classical
  intro Γ G V H _ _ _ _ _ B hB s f hf hω hΓ δ n i hn hc U H₀ hU hH
  subst hU hH
  set C := s.Cent δ with hC
  have memC : ∀ x, x ∈ C ↔ x⁻¹ * δ * s.θΓ x = δ := by
    intro x
    constructor
    · rintro ⟨z, hz, h⟩
      rw [hΓ, Subgroup.mem_bot] at hz
      simpa [hz] using h
    · intro h
      exact ⟨1, one_mem _, by simpa using h⟩
  have hRC : ∀ x, x ∈ C ↔ x ∈ i.range ∨ n * x ∈ i.range := fun x => (memC x).trans (hc x)
  have hiC : ∀ h, i h ∈ C := fun h => (hRC _).2 (Or.inl ⟨h, rfl⟩)
  let φ : H →* C := i.codRestrict C hiC
  have hnC : n ∈ C := by
    have : n⁻¹ ∈ C := (hRC _).2 (Or.inr (by simp [one_mem]))
    simpa using C.inv_mem this
  have hφ : ∀ c : C, c ∈ φ.range ↔ (c : Γ) ∈ i.range := by
    intro c
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, rfl⟩
    · rintro ⟨h, e⟩
      exact ⟨h, Subtype.ext e⟩
  have hidx : (φ.range ⊔ (⊥ : Subgroup C)).index = 2 := by
    rw [sup_bot_eq, Subgroup.index_eq_two_iff']
    refine ⟨⟨n, hnC⟩, fun b => ?_⟩
    rw [hφ, hφ]
    by_cases hb : (b : Γ) ∈ i.range
    · refine Or.inr ⟨hb, fun h => hn ?_⟩
      have := i.range.mul_mem h (i.range.inv_mem hb)
      simpa using this
    · refine Or.inl ⟨?_, hb⟩
      exact ((hRC _).1 b.2).resolve_left hb
  have hfl : ∀ (u : B.U) y, f (u * y) = f y := by
    intro u y
    rw [hf.left, hω]
    simp
  have hfr : ∀ (u : B.U) y, f (y * s.θ u) = f y := by
    intro u y
    rw [hf.right, hω]
    simp
  have kmk : ∀ g : G, s.ker f δ (g : G ⧸ B.U) = f (g⁻¹ * B.ι δ * s.θ g) := by
    intro g
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U g
    have e : (g * (u : G))⁻¹ * B.ι δ * s.θ (g * (u : G)) = ((u⁻¹ : B.U) : G) * (g⁻¹ * B.ι δ * s.θ g * s.θ u) := by
      simp [mul_assoc]
    show f (_) = _
    rw [hu, e, hfl, hfr]
  have hk : ∀ (h : C) (y : G ⧸ B.U), s.ker f δ ((B.ι.comp C.subtype) h • y) = s.ker f δ y := by
    intro h y
    induction y using QuotientGroup.induction_on with
    | H g =>
      have e : (B.ι (h : Γ) * g)⁻¹ * B.ι δ * s.θ (B.ι (h : Γ) * g) =
          g⁻¹ * B.ι ((h : Γ)⁻¹ * δ * s.θΓ (h : Γ)) * s.θ g := by
        simp [s.comm, mul_assoc]
      show s.ker f δ ((B.ι (h : Γ) * g : G) : G ⧸ B.U) = _
      rw [kmk, kmk, e, (memC _).1 h.2]
  have hS : ∃ S : Finset (G ⧸ B.U), ∀ y, s.ker f δ y ≠ 0 → ∃ h, ∃ x ∈ S, y = (B.ι.comp C.subtype) h • x := by
    obtain ⟨S, hS⟩ := Tf.centFin Γ G V B hB s f hf δ
    refine ⟨Finset.image (QuotientGroup.mk : G → G ⧸ B.U) S, fun y hy => ?_⟩
    obtain ⟨t, x, hx, u, hu, e⟩ := hS y.out hy
    refine ⟨t, (x : G ⧸ B.U), Finset.mem_image_of_mem _ hx, ?_⟩
    calc y = ((y.out : G) : G ⧸ B.U) := (QuotientGroup.out_eq' y).symm
      _ = (((B.ι.comp C.subtype) t * x : G) : G ⧸ B.U) := by
        rw [e]
        exact QuotientGroup.mk_mul_of_mem _ hu
      _ = _ := rfl
  have hw : ∀ y : G ⧸ B.U, s.ker f δ y ≠ 0 →
      (⊥ : Subgroup C).relIndex ((MulAction.stabilizer G y).comap (B.ι.comp C.subtype)) ≠ 0 := by
    intro y _
    induction y using QuotientGroup.induction_on with
    | H g =>
      have h1 := hB.stab g
      rw [hΓ, Subgroup.relIndex_bot_left] at h1
      haveI := (Nat.card_ne_zero.1 h1).2
      rw [Subgroup.relIndex_bot_left, Nat.card_ne_zero]
      refine ⟨⟨1, one_mem _⟩, ?_⟩
      let m : ((MulAction.stabilizer G (g : G ⧸ B.U)).comap (B.ι.comp C.subtype)) →
          ((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι) := fun c => ⟨(c.1 : Γ), by
        have h2 : (((B.ι (c.1 : Γ) * g : G)) : G ⧸ B.U) = (g : G ⧸ B.U) := c.2
        have h3 := QuotientGroup.eq.1 h2.symm
        exact ⟨_, h3, by simp [mul_assoc]⟩⟩
      refine Finite.of_injective m fun a b e => ?_
      exact Subtype.ext (Subtype.ext (congrArg (fun c => (c.1 : Γ)) e))
  have hz : ∀ z ∈ (⊥ : Subgroup C), ∀ y : G ⧸ B.U, (B.ι.comp C.subtype) z • y = y := by
    intro z hz y
    rw [Subgroup.mem_bot.1 hz]
    simp
  have key := Tf.gqIndex H C G φ (B.ι.comp C.subtype) ⊥ B.U (s.ker f δ) inferInstance hz
    (by rw [hidx]; norm_num) hk hS hw
  have e1 : (B.ι.comp C.subtype).comp φ = B.ι.comp i := by
    ext h
    rfl
  have e2 : (⊥ : Subgroup C).comap φ = i.ker := by
    ext h
    simp [φ, MonoidHom.mem_ker, Subtype.ext_iff]
  rw [e1, e2, hidx] at key
  have e3 : gqOn (B.ι.comp i) i.ker B.U (fun y => f (y.out⁻¹ * B.ι δ * s.θ y.out)) =
      gqOn (B.ι.comp i) i.ker B.U (s.ker f δ) := rfl
  rw [e3, key, Base.Tw.term, hΓ, Subgroup.bot_subgroupOf]
  push_cast
  ring
