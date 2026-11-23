import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointAddSqZeroEqProdMulTangent

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilChart

open SqZero

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B]

def augAlg (R : Type) [CommRing R] {B : Type} [CommRing B] [Algebra R B] (I : Ideal B) : Subalgebra R (R × B) :=
  AlgHom.equalizer ((Ideal.Quotient.mkₐ R I).comp (AlgHom.snd R R B))
    ((Ideal.Quotient.mkₐ R I).comp ((Algebra.ofId R B).comp (AlgHom.fst R R B)))

theorem mem_augAlg {I : Ideal B} {b : R × B} : b ∈ augAlg R I ↔ b.2 - algebraMap R B b.1 ∈ I :=
  Ideal.Quotient.eq

theorem mk_comp_eq {κ : Type} {m : ℕ} {I : Ideal B} (ψ : JetR R κ m →ₐ[R] B) (h : ∀ j, ψ (zR m j) ∈ I) :
    (Ideal.Quotient.mkₐ R I).comp ψ = (Algebra.ofId R _).comp (jetAug R κ m) :=
  jet_ext fun j => by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, jetAug_zR, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h j)

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) {d : ℕ}
  {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v) {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G}
  (hx₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
  (hx₂ : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
  (hx₃ : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)

include hG hv hx₁ hx₂ hx₃

theorem move {I J : Ideal B} (hJ : J * I = ⊥) (hle : J ≤ I) {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B)
    (hψ : ∀ j, ψ (zR m j) ∈ I) (c : Fin d → B) (hcJ : ∀ j, c j ∈ J) (hc : ∀ j, c j * c j = 0)
    (h : ∀ j, ψ' (zR m j) = ψ (zR m j) + c j) : spMap ψ' ≫ x m = lieExp v c hc * (spMap ψ ≫ x m) := by
  have hψ' : ∀ j, ψ' (zR m j) ∈ I := fun j => by rw [h]; exact add_mem (hψ j) (hle (hcJ j))
  let aug : augAlg R I →ₐ[R] R := (AlgHom.fst R R B).comp (augAlg R I).val
  let p : augAlg R I →ₐ[R] B := (AlgHom.snd R R B).comp (augAlg R I).val
  let up : ∀ φ : JetR R (Fin d) m →ₐ[R] B, (∀ j, φ (zR m j) ∈ I) → (JetR R (Fin d) m →ₐ[R] augAlg R I) :=
    fun φ hφ => ((jetAug R (Fin d) m).prod φ).codRestrict _ fun a => by
      have := AlgHom.congr_fun (mk_comp_eq φ hφ) a
      exact this
  let J' : Ideal (augAlg R I) := J.comap p ⊓ RingHom.ker aug
  have hker : ∀ a : augAlg R I, a ∈ RingHom.ker aug → p a ∈ I := fun a ha => by
    have h1 : a.1.1 = 0 := ha
    have h2 := mem_augAlg.1 a.2
    rw [h1, map_zero, sub_zero] at h2
    exact h2
  have hJ' : J' * RingHom.ker aug = ⊥ := by
    rw [← le_bot_iff, Ideal.mul_le]
    intro a ha b hb
    have h1 : a.1.1 = 0 := ha.2
    have h2 : p a * p b ∈ J * I := Ideal.mul_mem_mul ha.1 (hker b hb)
    rw [hJ] at h2
    exact Subtype.ext (Prod.ext (show a.1.1 * b.1.1 = 0 by rw [h1, zero_mul]) h2)
  let c' : Fin d → augAlg R I := fun j => ⟨(0, c j), mem_augAlg.2 (by simpa using hle (hcJ j))⟩
  have hc' : ∀ j, c' j * c' j = 0 := fun j => Subtype.ext (Prod.ext (mul_zero _) (hc j))
  have he : ∀ j, epsTo R (c' j) (hc' j) (TrivSqZeroExt.inr 1) = c' j := fun j => epsTo_eps _ _
  have key := jet_add_sqZero_eq_prod_mul R G hG d v hv x hx₁ hx₂ hx₃ _ aug J' hJ' inf_le_right m
    (up ψ hψ) (up ψ' hψ') rfl rfl (fun j => epsTo R (c' j) (hc' j))
    (fun j => by rw [he]; exact ⟨hcJ j, rfl⟩)
    (fun j => by
      rw [he]
      exact Subtype.ext (Prod.ext (add_zero _).symm (h j)))
  have fin := congrArg (spMap p ≫ ·) key
  change spMap p ≫ spMap _ ≫ x m = spMap p ≫ (lieExp v c' hc' * (spMap _ ≫ x m)) at fin
  rw [MonObj.comp_mul, comp_lieExp, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp] at fin
  exact fin

theorem eq_of_sub_mem {I J : Ideal B} (hJ : J * I = ⊥) (hle : J ≤ I) {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B)
    (hψ : ∀ j, ψ (zR m j) ∈ I) (hδ : ∀ j, ψ' (zR m j) - ψ (zR m j) ∈ J)
    (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  have hJ2 : J ^ 2 = ⊥ := by
    rw [← le_bot_iff, pow_two, ← hJ]
    exact Ideal.mul_mono_right hle
  let c : Fin d → J := fun j => ⟨_, hδ j⟩
  have hc : ∀ j, (c j : B) * (c j : B) = 0 := fun j => mul_eq_zero_of_sq hJ2 (c j).2 (c j).2
  have key := move hG hv hx₁ hx₂ hx₃ hJ hle ψ ψ' hψ (fun j => c j) (fun j => (c j).2) hc
    (fun j => (add_sub_cancel _ _).symm)
  rw [← h] at key
  have h1 : lieExp v (fun j => (c j : B)) hc = 1 := mul_eq_right.1 key.symm
  have h0 : c = 0 := by
    apply (expHom_bijective hv hJ2).1
    rw [map_zero]
    exact congrArg Additive.ofMul (Subtype.ext h1)
  refine jet_ext fun j => ?_
  have : ψ' (zR m j) - ψ (zR m j) = 0 := congrArg Subtype.val (congrFun h0 j)
  exact (sub_eq_zero.1 this).symm

theorem eq_of_nil {N : Ideal B} (hN : IsNilpotent N) {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B)
    (hψ : ∀ j, ψ (zR m j) ∈ N) (hψ' : ∀ j, ψ' (zR m j) ∈ N)
    (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  have main : ∀ k j, ψ' (zR m j) - ψ (zR m j) ∈ N ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro j
      rw [zero_add, pow_one]
      exact sub_mem (hψ' j) (hψ j)
    | succ k ih =>
      let q : B →ₐ[R] B ⧸ N ^ (k + 1 + 1) := Ideal.Quotient.mkₐ R _
      have e := eq_of_sub_mem hG hv hx₁ hx₂ hx₃ (I := N.map q) (J := (N ^ (k + 1)).map q)
        (by rw [← Ideal.map_mul, ← pow_succ]; exact Ideal.map_quotient_self _)
        (Ideal.map_mono (Ideal.pow_le_self (by omega)))
        (q.comp ψ) (q.comp ψ') (fun j => Ideal.mem_map_of_mem _ (hψ j))
        (fun j => by
          rw [AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub]
          exact Ideal.mem_map_of_mem _ (ih j))
        (by rw [← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, h])
      intro j
      exact Ideal.Quotient.eq.1 (AlgHom.congr_fun e (zR m j)).symm
  obtain ⟨n, hn⟩ := hN
  refine jet_ext fun j => ?_
  have := main n j
  rw [pow_succ, hn, zero_mul, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact (sub_eq_zero.1 this).symm

theorem coord_unique {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B) (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  have nil : ∀ φ : JetR R (Fin d) m →ₐ[R] B, IsNilpotent ((RingHom.ker (jetAug R (Fin d) m)).map φ) := fun φ =>
    ⟨m + 1, by rw [← Ideal.map_pow, ker_jetAug_pow, Ideal.map_bot, Ideal.zero_eq_bot]⟩
  refine eq_of_nil hG hv hx₁ hx₂ hx₃ (N := (RingHom.ker (jetAug R (Fin d) m)).map ψ +
    (RingHom.ker (jetAug R (Fin d) m)).map ψ') ((Commute.all _ _).isNilpotent_add (nil ψ) (nil ψ')) ψ ψ'
    (fun j => Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (zR_mem_ker m j)))
    (fun j => Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (zR_mem_ker m j))) h

theorem coord_exists {m : ℕ} {N : Ideal B} (hN : N ^ (m + 1) = ⊥) (y : sp (R₀ := R) B ⟶ G)
    (hy : spMap (Ideal.Quotient.mkₐ R N) ≫ y = 1) : ∃ ψ : JetR R (Fin d) m →ₐ[R] B, spMap ψ ≫ x m = y := by
  have haug : spMap (jetAug R (Fin d) m) ≫ x m = 1 := by
    have e : jetAug R (Fin d) m = (jetAug R (Fin d) 0).comp (jetZeroR R (Fin d) m) :=
      (jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact (jetAug_zR (R := R) 0 j).symm)
    rw [e, ← spMap_comp, Category.assoc, hx₂ m, comp_one']
  have fac : ∀ {A₁ A₂ : Type} [CommRing A₁] [Algebra R A₁] [CommRing A₂] [Algebra R A₂] (p : B →ₐ[R] A₁)
      (q : A₁ →ₐ[R] A₂) {y y' : sp (R₀ := R) B ⟶ G}, spMap p ≫ y = spMap p ≫ y' →
      spMap (q.comp p) ≫ y = spMap (q.comp p) ≫ y' := fun p q y y' h => by
    rw [← spMap_comp, Category.assoc, Category.assoc, h]
  have key : ∀ k : ℕ, ∃ (b : Fin d → B) (hb : ∀ j, b j ∈ N),
      spMap (Ideal.Quotient.mkₐ R (N ^ (k + 1))) ≫ y =
        spMap (Ideal.Quotient.mkₐ R (N ^ (k + 1))) ≫ spMap (jetLift R _ hN b hb) ≫ x m := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun _ => 0, fun _ => zero_mem _, ?_⟩
      have e : Ideal.Quotient.mkₐ R (N ^ (0 + 1)) =
          (Ideal.Quotient.factorₐ R (show N ≤ N ^ (0 + 1) by rw [zero_add, pow_one])).comp
            (Ideal.Quotient.mkₐ R N) := by
        ext a; rfl
      rw [e]
      refine fac _ _ ?_
      rw [hy, ← Category.assoc, spMap_comp, mk_comp_eq _ (fun j => by rw [jetLift_zR]; exact zero_mem _),
        ← spMap_comp, Category.assoc, haug, comp_one']
    | succ k ih =>
      obtain ⟨b, hb, ih⟩ := ih
      let B' := B ⧸ N ^ (k + 1 + 1)
      let π : B →ₐ[R] B' := Ideal.Quotient.mkₐ R (N ^ (k + 1 + 1))
      have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
      let J : Ideal B' := (N ^ (k + 1)).map π
      have hJN : J * N.map π = ⊥ := by
        rw [← Ideal.map_mul, ← pow_succ]
        exact Ideal.map_quotient_self _
      have hJle : J ≤ N.map π := Ideal.map_mono (Ideal.pow_le_self (by omega))
      have hJ : J ^ 2 = ⊥ := by
        rw [← le_bot_iff, pow_two, ← hJN]
        exact Ideal.mul_mono_right hJle
      let q : (B ⧸ N ^ (k + 1)) →ₐ[R] B' ⧸ J := Ideal.Quotient.liftₐ _
        ((Ideal.Quotient.mkₐ R J).comp π)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha))
      have hq : q.comp (Ideal.Quotient.mkₐ R (N ^ (k + 1))) = (Ideal.Quotient.mkₐ R J).comp π := by
        ext a; rfl
      have h2 := fac _ q ih
      rw [hq, ← spMap_comp, Category.assoc, Category.assoc] at h2
      haveI := hG
      obtain ⟨c, hc, -⟩ := SqZero.existsUnique_eq_lieExp_mul hv hJ h2.symm
      choose δ hδ hδc using fun j => (Ideal.mem_map_iff_of_surjective π hπ).1 (c j).2
      have hb' : ∀ j, b j + δ j ∈ N := fun j =>
        add_mem (hb j) (Ideal.pow_le_self (by omega) (hδ j))
      refine ⟨fun j => b j + δ j, hb', ?_⟩
      have h3 := move hG hv hx₁ hx₂ hx₃ hJN hJle
        (π.comp (jetLift R _ hN b hb)) (π.comp (jetLift R _ hN (fun j => b j + δ j) hb'))
        (fun j => by rw [AlgHom.comp_apply, jetLift_zR]; exact Ideal.mem_map_of_mem _ (hb j))
        (fun j => (c j : B')) (fun j => (c j).2) (fun j => SqZero.mul_eq_zero_of_sq hJ (c j).2 (c j).2)
        (fun j => by
          rw [AlgHom.comp_apply, AlgHom.comp_apply, jetLift_zR, jetLift_zR, map_add, hδc])
      change spMap π ≫ y = spMap π ≫ _
      rw [hc, ← Category.assoc, spMap_comp, ← Category.assoc, spMap_comp, h3]
  obtain ⟨b, hb, h⟩ := key m
  refine ⟨jetLift R _ hN b hb, ?_⟩
  let q : (B ⧸ N ^ (m + 1)) →ₐ[R] B := Ideal.Quotient.liftₐ _ (AlgHom.id R B)
    (fun a ha => by rw [hN] at ha; exact ha)
  have hq : q.comp (Ideal.Quotient.mkₐ R (N ^ (m + 1))) = AlgHom.id R B := by
    ext a; rfl
  have h2 := fac _ q h
  rw [hq, spMap_id, Category.id_comp, Category.id_comp] at h2
  exact h2.symm

theorem existsUnique_coord {m : ℕ} {N : Ideal B} (hN : N ^ (m + 1) = ⊥) (y : sp (R₀ := R) B ⟶ G)
    (hy : spMap (Ideal.Quotient.mkₐ R N) ≫ y = 1) : ∃! ψ : JetR R (Fin d) m →ₐ[R] B, spMap ψ ≫ x m = y := by
  obtain ⟨ψ, h⟩ := coord_exists hG hv hx₁ hx₂ hx₃ hN y hy
  exact ⟨ψ, h, fun ψ' h' => coord_unique hG hv hx₁ hx₂ hx₃ _ _ (h'.trans h.symm)⟩

end GlobalTheory.NilChart
