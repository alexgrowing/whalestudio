import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad

private theorem embedding_fibre_constant_card {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] (j : L →+* K) :
    ∃ d : ℕ, 0 < d ∧ d * Module.finrank ℚ L = Module.finrank ℚ K ∧
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ψ : L →+* Ω), Nat.card {θ : K →+* Ω // θ.comp j = ψ} = d := by
  letI : Algebra L K := j.toAlgebra
  haveI : IsScalarTower ℚ L K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Module.Finite L K := Module.Finite.of_restrictScalars_finite ℚ L K
  refine ⟨Module.finrank L K, Module.finrank_pos, by rw [mul_comm, Module.finrank_mul_finrank], ?_⟩
  intro Ω _ _ ψ
  letI : Algebra L Ω := ψ.toAlgebra
  have e : {θ : K →+* Ω // θ.comp j = ψ} ≃ (K →ₐ[L] Ω) :=
    ⟨fun θ => ⟨θ.1, fun a => RingHom.congr_fun θ.2 a⟩, fun θ => ⟨θ.toRingHom, θ.comp_algebraMap⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, AlgHom.card]

private theorem residueField_embedding_points_equiv {F Ω : Type} [Field F] [Field Ω] {X : Scheme.{0}} (s : X ⟶ Sp F) (x : X)
    (ι : CommRingCat.of F ⟶ X.residueField x) (hι : Spec.map ι = X.fromSpecResidueField x ≫ s) (σ : F →+* Ω) :
    ∃ E : {ψ : X.residueField x →+* Ω // ψ.comp ι.hom = σ} ≃
        {z : {z : Sp Ω ⟶ X // z ≫ s = spMap σ} // below z.1 = x},
      ∀ ψ, (E ψ).1.1 = Spec.map (CommRingCat.ofHom ψ.1) ≫ X.fromSpecResidueField x := by
  have hP (ψ : {ψ : X.residueField x →+* Ω // ψ.comp ι.hom = σ}) :
      (Spec.map (CommRingCat.ofHom ψ.1) ≫ X.fromSpecResidueField x) ≫ s = spMap σ := by
    have h : ι ≫ CommRingCat.ofHom ψ.1 = CommRingCat.ofHom σ := CommRingCat.hom_ext ψ.2
    rw [Category.assoc, ← hι, ← Spec.map_comp]
    exact congrArg Spec.map h
  let P : {ψ : X.residueField x →+* Ω // ψ.comp ι.hom = σ} →
      {z : {z : Sp Ω ⟶ X // z ≫ s = spMap σ} // below z.1 = x} :=
    fun ψ => ⟨⟨Spec.map (CommRingCat.ofHom ψ.1) ≫ X.fromSpecResidueField x, hP ψ⟩,
      (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply x _)⟩
  refine ⟨Equiv.ofBijective P ⟨fun a b h => ?_, ?_⟩, fun _ => rfl⟩
  · have h1 : Spec.map (CommRingCat.ofHom a.1) ≫ X.fromSpecResidueField x =
        Spec.map (CommRingCat.ofHom b.1) ≫ X.fromSpecResidueField x := congrArg (fun t => t.1.1) h
    exact Subtype.ext (congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h1)))
  · rintro ⟨⟨y, hy⟩, hyx⟩
    obtain ⟨ψ, h⟩ : ∃ ψ : X.residueField x ⟶ CommRingCat.of Ω, Spec.map ψ ≫ X.fromSpecResidueField x = y := by
      subst hyx
      exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X y⟩
    have h2 : Spec.map (ι ≫ ψ) = Spec.map (CommRingCat.ofHom σ) := by
      rw [Spec.map_comp, hι, ← Category.assoc, h]
      exact hy
    exact ⟨⟨ψ.hom, congrArg CommRingCat.Hom.hom (Spec.map_injective h2)⟩, Subtype.ext (Subtype.ext h)⟩

private theorem finsum_fibre_degree {F L K Ω : Type} [Field F] [Field L] [NumberField L] [Field K] [NumberField K]
    [Field Ω] [CharZero Ω] (ι : F →+* L) (j : L →+* K) (σ : F →+* Ω) (d : ℕ)
    (hd : ∀ ψ : L →+* Ω, Nat.card {θ : K →+* Ω // θ.comp j = ψ} = d)
    (h : {ψ : L →+* Ω // ψ.comp ι = σ} → ℝ) (G : (K →+* Ω) → ℝ)
    (hG : ∀ (θ : K →+* Ω) (ψ : {ψ : L →+* Ω // ψ.comp ι = σ}), θ.comp j = ψ.1 → h ψ = G θ) :
    (d : ℝ) * ∑ᶠ ψ, h ψ = ∑ᶠ (θ : K →+* Ω) (_ : θ.comp (j.comp ι) = σ), G θ := by
  classical
  rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  let r : {θ : K →+* Ω // θ.comp (j.comp ι) = σ} → {ψ : L →+* Ω // ψ.comp ι = σ} :=
    fun θ => ⟨θ.1.comp j, θ.2⟩
  rw [← Finset.sum_fiberwise Finset.univ r]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => h ψ) fun θ hθ =>
    (hG θ.1 ψ (congrArg Subtype.val (Finset.mem_filter.1 hθ).2)).symm, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← hd ψ.1, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr ⟨fun θ => ⟨⟨θ.1, by rw [← RingHom.comp_assoc, θ.2, ψ.2]⟩, Subtype.ext θ.2⟩,
    fun θ => ⟨θ.1.1, congrArg Subtype.val θ.2⟩, fun _ => rfl, fun _ => rfl⟩

theorem UpperTheory.algebraic_points_degree_sum :
    ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] (Y : Var F) (φ : F →+* K) (q : Sp K ⟶ Y.X), q ≫ Y.str = spMap φ → ∃ d : ℕ, 0 < d ∧ d * Module.finrank ℚ F * Nat.card {y : AlgPt Y // below y.1 = below q} = Module.finrank ℚ K ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (σ : F →+* Ω) (f : {z : Sp Ω ⟶ Y.X // z ≫ Y.str = spMap σ} → ℝ) (G : (K →+* Ω) → ℝ), (∀ (θ : K →+* Ω) (z : {z : Sp Ω ⟶ Y.X // z ≫ Y.str = spMap σ}), θ.comp φ = σ → z.1 = spMap θ ≫ q → f z = G θ) → (d : ℝ) * ∑ᶠ (z : {z : Sp Ω ⟶ Y.X // z ≫ Y.str = spMap σ}) (_ : below z.1 = below q), f z = ∑ᶠ (θ : K →+* Ω) (_ : θ.comp φ = σ), G θ := by
  intro F K _ _ _ _ Y φ q hq
  obtain ⟨ι, hι⟩ := Spec.map_surjective (Y.X.fromSpecResidueField (below q) ≫ Y.str)
  obtain ⟨j, hj⟩ : ∃ j : Y.X.residueField (below q) ⟶ CommRingCat.of K,
      Spec.map j ≫ Y.X.fromSpecResidueField (below q) = q :=
    ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y.X q⟩
  have hφ : j.hom.comp ι.hom = φ := by
    have h2 : Spec.map (ι ≫ j) = Spec.map (CommRingCat.ofHom φ) := by
      rw [Spec.map_comp, hι, ← Category.assoc, hj]
      exact hq
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  haveI : CharZero (Y.X.residueField (below q)) := j.hom.charZero
  haveI : NumberField (Y.X.residueField (below q)) :=
    { to_finiteDimensional := FiniteDimensional.of_injective j.hom.toRatAlgHom.toLinearMap j.hom.injective }
  obtain ⟨d, hd0, hd1, hd⟩ := embedding_fibre_constant_card j.hom
  obtain ⟨n, -, hn1, hn⟩ := embedding_fibre_constant_card (L := F) ι.hom
  refine ⟨d, hd0, ?_, ?_⟩
  · obtain ⟨E, -⟩ := residueField_embedding_points_equiv Y.str (below q) ι hι (algebraMap F (AlgebraicClosure F))
    have h1 : Nat.card {y : AlgPt Y // below y.1 = below q} = n :=
      (Nat.card_congr E).symm.trans (hn _ _)
    rw [h1, ← hd1, ← hn1]
    ring
  · intro Ω _ _ σ f G hfG
    haveI : CharZero Ω := charZero_of_injective_ringHom σ.injective
    obtain ⟨E, hE⟩ := residueField_embedding_points_equiv Y.str (below q) ι hι σ
    have h1 := finsum_fibre_degree (F := F) ι.hom j.hom σ d (hd Ω) (fun ψ => f (E ψ).1) G fun θ ψ hθ => by
      refine hfG θ _ ?_ ?_
      · rw [← hφ, ← RingHom.comp_assoc, hθ, ψ.2]
      · have h3 : CommRingCat.ofHom ψ.1 = j ≫ CommRingCat.ofHom θ := CommRingCat.hom_ext hθ.symm
        rw [hE, h3, Spec.map_comp, Category.assoc, hj]
    rw [hφ] at h1
    rw [← h1, ← finsum_subtype_eq_finsum_cond, ← finsum_comp_equiv E]
