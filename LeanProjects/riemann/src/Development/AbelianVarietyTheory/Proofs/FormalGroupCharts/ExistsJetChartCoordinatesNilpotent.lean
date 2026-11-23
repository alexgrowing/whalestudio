import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointAddSqZeroEqProdMulTangentStatement

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetOnto

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem comp_eq_of_factor {A B C : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [CommRing C] [Algebra R C] {X : Over (Spec (CommRingCat.of R))} (p : A →ₐ[R] B) (q : B →ₐ[R] C)
    {y y' : sp (R₀ := R) A ⟶ X} (h : spMap p ≫ y = spMap p ≫ y') :
    spMap (q.comp p) ≫ y = spMap (q.comp p) ≫ y' := by
  rw [← spMap_comp, Category.assoc, Category.assoc, h]

theorem aug_comp_jetLift {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) {d m : ℕ}
    (h : (RingHom.ker aug) ^ (m + 1) = ⊥) (b : Fin d → A) (hb : ∀ j, b j ∈ RingHom.ker aug) :
    aug.comp (jetLift R _ h b hb) = jetAug R (Fin d) m :=
  jet_ext fun j => by
    rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]; exact hb j

theorem spMap_jetAug {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G)
    (h0 : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) (m : ℕ) :
    spMap (jetAug R (Fin d) m) ≫ x m = 1 := by
  have e : jetAug R (Fin d) m = (jetAug R (Fin d) 0).comp (jetZeroR R (Fin d) m) :=
    (jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact (jetAug_zR (R := R) 0 j).symm)
  rw [e, ← spMap_comp, Category.assoc, h0 m, comp_one']

end GlobalTheory.JetOnto

namespace GlobalTheory

open JetOnto

theorem exists_jet_coordinates : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) → (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) → (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) → ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ → ∀ y : sp (R₀ := R) A ⟶ G, spMap aug ≫ y = 1 → ∃ ψ : JetR R (Fin d) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin d) m ∧ y = spMap ψ ≫ x m := by
  intro R _ G _ _ hG d v hv x ht h0 h1 A _ _ aug m hN y hy
  have key : ∀ k : ℕ, ∃ (b : Fin d → A) (hb : ∀ j, b j ∈ RingHom.ker aug),
      spMap (Ideal.Quotient.mkₐ R ((RingHom.ker aug) ^ (k + 1))) ≫ y =
        spMap (Ideal.Quotient.mkₐ R ((RingHom.ker aug) ^ (k + 1))) ≫
          spMap (jetLift R _ hN b hb) ≫ x m := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun _ => 0, fun _ => zero_mem _, ?_⟩
      have e : Ideal.Quotient.mkₐ R ((RingHom.ker aug) ^ (0 + 1)) =
          (Algebra.ofId R _).comp aug := by
        ext a
        change Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ (algebraMap R A (aug a))
        rw [Ideal.Quotient.eq, zero_add, pow_one, RingHom.mem_ker, map_sub, AlgHom.commutes,
          Algebra.algebraMap_self, RingHom.id_apply, sub_self]
      rw [e]
      refine comp_eq_of_factor _ _ ?_
      rw [hy, ← Category.assoc, spMap_comp, aug_comp_jetLift, spMap_jetAug x h0]
    | succ k ih =>
      obtain ⟨b, hb, ih⟩ := ih
      set N := RingHom.ker aug with hNdef
      let B := A ⧸ N ^ (k + 1 + 1)
      let π : A →ₐ[R] B := Ideal.Quotient.mkₐ R (N ^ (k + 1 + 1))
      have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
      let augB : B →ₐ[R] R := Ideal.Quotient.liftₐ _ aug
        (fun a ha => (Ideal.pow_le_self (by omega) ha : a ∈ N))
      have haug : augB.comp π = aug := by ext a; rfl
      have hker : RingHom.ker augB = N.map π := by
        apply le_antisymm
        · intro z hz
          obtain ⟨a, rfl⟩ := hπ z
          exact Ideal.mem_map_of_mem _ hz
        · exact Ideal.map_le_iff_le_comap.2 fun a ha => ha
      let J : Ideal B := (N ^ (k + 1)).map π
      have hJN : J * RingHom.ker augB = ⊥ := by
        rw [hker, ← Ideal.map_mul, ← pow_succ]
        exact Ideal.map_quotient_self _
      have hJle : J ≤ RingHom.ker augB := by
        rw [hker]
        exact Ideal.map_mono (Ideal.pow_le_self (by omega))
      have hJ : J ^ 2 = ⊥ := by
        rw [← le_bot_iff, pow_two, ← hJN]
        exact Ideal.mul_mono_right hJle
      let q : (A ⧸ N ^ (k + 1)) →ₐ[R] B ⧸ J := Ideal.Quotient.liftₐ _
        ((Ideal.Quotient.mkₐ R J).comp π)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha))
      have hq : q.comp (Ideal.Quotient.mkₐ R (N ^ (k + 1))) = (Ideal.Quotient.mkₐ R J).comp π := by
        ext a; rfl
      have h2 := comp_eq_of_factor _ q ih
      rw [hq, ← spMap_comp, Category.assoc, Category.assoc] at h2
      haveI := hG
      obtain ⟨c, hc, -⟩ := SqZero.existsUnique_eq_lieExp_mul hv hJ h2.symm
      choose δ hδ hδc using fun j => (Ideal.mem_map_iff_of_surjective π hπ).1 (c j).2
      have hb' : ∀ j, b j + δ j ∈ N := fun j =>
        add_mem (hb j) (Ideal.pow_le_self (by omega) (hδ j))
      refine ⟨fun j => b j + δ j, hb', ?_⟩
      have h3 := GlobalTheory.T.jetPoint_add_sqZero_eq_prod_mul_tangent R G hG d v hv x ht h0 h1 B augB J hJN hJle m
        (π.comp (jetLift R _ hN b hb)) (π.comp (jetLift R _ hN (fun j => b j + δ j) hb'))
        (by rw [← AlgHom.comp_assoc, haug, aug_comp_jetLift])
        (by rw [← AlgHom.comp_assoc, haug, aug_comp_jetLift])
        (fun j => SqZero.epsTo R (c j : B) (SqZero.mul_eq_zero_of_sq hJ (c j).2 (c j).2))
        (fun j => by erw [SqZero.epsTo_eps]; exact (c j).2)
        (fun j => by
          erw [SqZero.epsTo_eps]
          rw [AlgHom.comp_apply, AlgHom.comp_apply, jetLift_zR, jetLift_zR,
            map_add, hδc])
      change spMap π ≫ y = spMap π ≫ _
      rw [hc, ← Category.assoc, spMap_comp, ← Category.assoc, spMap_comp, h3]
      rfl
  obtain ⟨b, hb, h⟩ := key m
  refine ⟨jetLift R _ hN b hb, aug_comp_jetLift aug hN b hb, ?_⟩
  let q : (A ⧸ (RingHom.ker aug) ^ (m + 1)) →ₐ[R] A := Ideal.Quotient.liftₐ _ (AlgHom.id R A)
    (fun a ha => by rw [hN] at ha; exact ha)
  have hq : q.comp (Ideal.Quotient.mkₐ R ((RingHom.ker aug) ^ (m + 1))) = AlgHom.id R A := by
    ext a; rfl
  have h2 := comp_eq_of_factor _ q h
  rwa [hq, spMap_id, Category.id_comp, Category.id_comp] at h2

end GlobalTheory
