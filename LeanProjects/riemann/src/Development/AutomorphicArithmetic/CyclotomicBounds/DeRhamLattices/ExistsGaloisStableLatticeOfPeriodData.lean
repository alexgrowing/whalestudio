import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.AdmissibleLatticesCommensurable
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsLatticeEqAddSmulOfStableFgSubmodule
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsLinearEquivQuotientOfLatticeSum
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

private theorem admissible_lattice_inclusion {G O LL V : Type} [Group G] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [Field LL] [Algebra O LL] [IsFractionRing O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] (ρ : Representation LL G V)
    (Λ : Lattice (O := O) ρ)
    {A : Type} [AddCommGroup A] [Module O A] [Module.Finite O A] (j : A →ₗ[O] V) (actA : G → A → A)
    {E : Type} [AddCommGroup E] [Module O E] (act : G → E → E) (S : Submodule O E)
    (q : A →ₗ[O] (E ⧸ S)) (c : O)
    (hj : Function.Injective j) (hact : ∀ g a, j (actA g a) = ρ g (j a)) (hq : Function.Surjective q)
    (hqa : ∀ g a x, q a = Submodule.Quotient.mk x → q (actA g a) = Submodule.Quotient.mk (act g x))
    (hc : c ≠ 0) (hcy : ∀ y : E ⧸ S, c • y = 0) :
    ∃ (L₁ L₂ : Lattice (O := O) ρ),
      L₂.T ≤ L₁.T ∧ ∃ e : (E ⧸ S) ≃ₗ[O] (↥L₁.T ⧸ L₂.T.comap L₁.T.subtype),
        ∀ (g : G) (x : E) (y : ↥L₁.T), e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
          e (Submodule.Quotient.mk (act g x)) = Submodule.Quotient.mk ⟨ρ g y, L₁.stable g y y.2⟩ := by
  have h0 : ∀ g, actA g 0 = 0 := fun g => hj (by rw [hact, map_zero, map_zero])
  have hker : ∀ g a, q a = 0 → q (actA g a) = 0 := by
    intro g a ha
    have h1 := hqa g a 0 (by rw [ha]; rfl)
    have h2 := hqa g 0 0 (by rw [map_zero]; rfl)
    rw [h1, ← h2, h0, map_zero]
  obtain ⟨μ, hμ, hcom⟩ := UpperTheory.KN.admissible_lattices_commensurable (LL := LL) Λ.T (LinearMap.range j) Λ.fg c hc
  have fg1 : (LinearMap.range j).FG := by
    rw [← Submodule.map_top]
    exact Submodule.FG.map j Module.Finite.fg_top
  have fg2 : ((LinearMap.ker q).map j).FG :=
    Submodule.FG.map j (IsNoetherian.noetherian _)
  obtain ⟨L₁, hL₁⟩ := UpperTheory.KN.exists_lattice_eq_add_smul_of_stable_fg_submodule ρ Λ (LinearMap.range j) fg1
    (by rintro g _ ⟨a, rfl⟩; exact ⟨actA g a, hact g a⟩) μ hμ
  obtain ⟨L₂, hL₂⟩ := UpperTheory.KN.exists_lattice_eq_add_smul_of_stable_fg_submodule ρ Λ ((LinearMap.ker q).map j) fg2
    (by rintro g _ ⟨a, ha, rfl⟩; exact ⟨actA g a, hker g a ha, hact g a⟩) μ hμ
  let B : Submodule O V := Λ.T.map (μ • (LinearMap.id : V →ₗ[O] V))
  have hB : ∀ b, b ∈ B ↔ ∃ u ∈ Λ.T, μ • u = b := fun b => Iff.rfl
  obtain ⟨e, he⟩ := UpperTheory.KN.exists_linearEquiv_quotient_of_lattice_sum j q B L₁.T L₂.T hj hq
    (by
      intro a ha
      obtain ⟨u, hu, hua⟩ := (hB _).1 ha
      obtain ⟨_, ⟨a', rfl⟩, h⟩ := hcom u hu ⟨a, hua.symm⟩
      have : a = c • a' := hj (by rw [map_smul, ← h, hua])
      rw [this, map_smul, hcy])
    (by
      intro v
      rw [hL₁]
      constructor
      · rintro ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩
        exact ⟨a, _, (hB _).2 ⟨u, hu, rfl⟩, rfl⟩
      · rintro ⟨a, b, hb, rfl⟩
        obtain ⟨u, hu, rfl⟩ := (hB _).1 hb
        exact ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩)
    (by
      intro v
      rw [hL₂]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, u, hu, rfl⟩
        exact ⟨a, ha, _, (hB _).2 ⟨u, hu, rfl⟩, rfl⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        obtain ⟨u, hu, rfl⟩ := (hB _).1 hb
        exact ⟨_, ⟨a, ha, rfl⟩, u, hu, rfl⟩)
  refine ⟨L₁, L₂, ?_, e, ?_⟩
  · intro v hv
    obtain ⟨_, ⟨a, _, rfl⟩, u, hu, rfl⟩ := (hL₂ v).1 hv
    exact (hL₁ _).2 ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩
  · intro g x y hxy
    obtain ⟨a, ha⟩ := hq (Submodule.Quotient.mk x)
    rw [← ha] at hxy
    obtain ⟨a', ha', b, hb, hy⟩ := (he a y).1 hxy
    obtain ⟨u, hu, rfl⟩ := (hB _).1 hb
    rw [← hqa g a' x (ha'.trans ha)]
    refine (he _ _).2 ⟨actA g a', rfl, μ • ρ g u, (hB _).2 ⟨_, Λ.stable g u hu, rfl⟩, ?_⟩
    show ρ g y = _
    rw [hy, map_add, hact, LinearMap.map_smul_of_tower]

theorem _root_.UpperTheory.KN.exists_galois_stable_lattice_of_period_data :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
      [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
      {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
      [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
      [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
      {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
      {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [IsFractionRing O LL] {nn : ℕ}
      (emb : ZMod nn → (K₀ →ₐ[Qp] LL)) (lam : O) (jT : ZMod nn → ℤ → ℤ) (cT : G → Polynomial LL)
      {m : ℕ} (F : Fin m → tableLineDegreeTwo.FullRep PD emb lam jT cT) (Λ : Lattice (O := O) (tableLineDegreeTwo.piRep F))
      {A : Type} [AddCommGroup A] [Module O A] [Module.Finite O A] (j : A →ₗ[O] (∀ k, (F k).V)) (actA : G → A → A)
      {E : Type} [AddCommGroup E] [Module O E] (act : G → E → E) (S : Submodule O E) (q : A →ₗ[O] (E ⧸ S)) (c : O),
      Function.Injective j → (∀ g a, j (actA g a) = tableLineDegreeTwo.piRep F g (j a)) → Function.Surjective q →
      (∀ g a x, q a = Submodule.Quotient.mk x → q (actA g a) = Submodule.Quotient.mk (act g x)) →
      c ≠ 0 → (∀ y : E ⧸ S, c • y = 0) → tableLineDegreeTwo.AdmQ PD emb lam jT cT act S := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ _ O _ _ _ _ _ nn emb lam jT cT
    m F Λ A _ _ _ j actA E _ _ act S q c hj hact hq hqa hc hcy
  exact ⟨m, F, admissible_lattice_inclusion (tableLineDegreeTwo.piRep F) Λ j actA act S q c hj hact hq hqa hc hcy⟩
