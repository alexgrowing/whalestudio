import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAdjoinRootAlgebrasGeneratedByPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianMultiplicationModelNonsplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjUnitaryOfSameHermitianMultiplicationModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianModelsConjUnitaryDifferByNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModelOfSelfDualLatticeCountNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfHermitianMultiplicationModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralCongruenceLevelEqCountStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKernelSignEqEtaGramDetStatement

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem model_mul_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w), IsModel w e B u x γ → ∀ c : B.Aˣ, IsModel w e B u (x * ((c : B.A) * B.σ (c : B.A))) γ := by
  intro E _ _ _ w K e B u x n γ hM c
  obtain ⟨ψ, h1, h2, h3⟩ := hM
  let φ : B.A ≃+ (Fin n → w.adicCompletion E) :=
    { toFun := fun y => ψ ((c : B.A) * y)
      invFun := fun v => ((c⁻¹ : B.Aˣ) : B.A) * ψ.symm v
      left_inv := fun y => by simp [← mul_assoc]
      right_inv := fun v => by simp [← mul_assoc]
      map_add' := fun y z => by simp [mul_add] }
  refine ⟨φ, fun a y => ?_, fun y => ?_, fun y z => ?_⟩
  · show ψ ((c : B.A) * (a • y)) = e a • ψ ((c : B.A) * y)
    rw [mul_smul_comm, h1]
  · show ψ ((c : B.A) * (u * y)) = γ.val *ᵥ ψ ((c : B.A) * y)
    rw [show (c : B.A) * (u * y) = u * ((c : B.A) * y) by ring, h2]
  · show stdH w (ψ ((c : B.A) * y)) (ψ ((c : B.A) * z)) = _
    rw [h3]
    unfold GlobalTheory.UnitLemma.InvAlg.herm
    congr 2
    rw [map_mul]
    ring

theorem kapOrb_eq_kapSum_of_fits {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} (hw : ¬ IsSplitAt w)
    {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hBr : Bridge w K e) {k : ℕ} {t : K.O} (ht : K.Small t)
    (htk : GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k) {n : ℕ} {Q₁ Q₂ : (w.adicCompletion E)[X]}
    {B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K} {u₁ : B₁.A} {u₂ : B₂.A} (hsep : (Q₁ * Q₂).Separable) (hmon : (Q₁ * Q₂).Monic)
    (hdeg : (Q₁ * Q₂).natDegree = n) (hF₁ : Fits w e B₁ Q₁ u₁) (hF₂ : Fits w e B₂ Q₂ u₂)
    (hg : 1 + algebraMap K.O (B₁.prod B₂).A t * (B₁.prod B₂).g = (u₁, u₂)) :
    kapOrb n w Q₁ Q₂ (({γ : UL n w | γ.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) =
      ((GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ : ℚ) : ℂ) := by
  have hF := GlobalTheory.T.prod_adjoinRootAlgebras_generated_by_pair E w K e Q₁ Q₂ B₁ B₂ u₁ u₂ hsep hF₁ hF₂
  unfold kapOrb clSum GlobalTheory.UnitLemma.InvAlg.kapSum
  rw [cast_finsum]
  set S' : Set (TwCl (MonoidHom.id (UL n w))) := {c | c.rep.1.val.charpoly = Q₁ * Q₂} with hS'
  have hex : ∀ c : TwCl (MonoidHom.id (UL n w)), c ∈ S' → ∃ x : (B₁.prod B₂).A, (B₁.prod B₂).σ x = x ∧ IsUnit x ∧
      IsModel w e (B₁.prod B₂) (u₁, u₂) x c.rep.1 := fun c hc =>
    GlobalTheory.T.exists_hermitianMultiplicationModel_nonsplit E w hw K e hBr n (Q₁ * Q₂) (B₁.prod B₂) (u₁, u₂) hsep hF c.rep.1 c.rep.2 hc
  let Φ : TwCl (MonoidHom.id (UL n w)) → (B₁.prod B₂).Cl := fun c =>
    if h : ∃ x : (B₁.prod B₂).A, (B₁.prod B₂).σ x = x ∧ IsUnit x ∧ IsModel w e (B₁.prod B₂) (u₁, u₂) x c.rep.1 then
      Quot.mk _ ⟨h.choose_spec.2.1.unit, by simpa using h.choose_spec.1⟩ else Quot.mk _ ⟨1, by simp⟩
  have hrep : ∀ c ∈ S', IsModel w e (B₁.prod B₂) (u₁, u₂) (GlobalTheory.UnitLemma.InvAlg.Cl.rep (Φ c)) c.rep.1 := by
    intro c hc
    have h := hex c hc
    have hΦ : Φ c = Quot.mk _ ⟨h.choose_spec.2.1.unit, by simpa using h.choose_spec.1⟩ := dif_pos h
    have hq := Quot.eqvGen_exact ((Quot.out_eq (Φ c)).trans hΦ)
    obtain ⟨v, hv⟩ := (clRel_equiv (B₁.prod B₂)).symm ((clRel_equiv (B₁.prod B₂)).eqvGen_iff.1 hq)
    have hr : GlobalTheory.UnitLemma.InvAlg.Cl.rep (Φ c) = h.choose * ((v : (B₁.prod B₂).A) * (B₁.prod B₂).σ (v : (B₁.prod B₂).A)) := by
      unfold GlobalTheory.UnitLemma.InvAlg.Cl.rep
      rw [hv]
      simp
    rw [hr]
    exact model_mul_norm E w K e (B₁.prod B₂) _ _ n _ h.choose_spec.2.2 v
  let G : (B₁.prod B₂).Cl → ℂ := fun κ =>
    ((K.eta (B₁.gramDet (GlobalTheory.UnitLemma.InvAlg.Cl.rep κ).1) * (B₁.prod B₂).N κ.rep : ℚ) : ℂ)
  have hterm : ∀ c ∈ S', kapSign n w Q₁ c.rep.1 * twOrb (MonoidHom.id (UL n w)) (KL n w) c.rep
      (({γ : UL n w | γ.1 ∈ congSet w n k} : Set (UL n w)).indicator 1) = G (Φ c) := by
    intro c hc
    have hm := hrep c hc
    have h7 := GlobalTheory.T.twisted_orbitalIntegral_congruence_level_eq_count E w hw K e hBr k t ht htk n (Q₁ * Q₂) (B₁.prod B₂) _ _ hsep hF hg.symm c.rep.1 c.rep.2 hm
    simp only [Subtype.coe_eta] at h7
    rw [GlobalTheory.T.inertPlace_kernelSign_eq_eta_gramDet E w hw K e hBr n Q₁ Q₂ B₁ B₂ u₁ u₂ hsep hF₁ hF₂ _ _ hm, h7]
    simp [G]
  have hinj : Set.InjOn Φ S' := by
    intro c₁ hc₁ c₂ hc₂ h12
    have m₁ := hrep c₁ hc₁
    have m₂ := hrep c₂ hc₂
    rw [h12] at m₁
    obtain ⟨y, hy, hyc⟩ := GlobalTheory.T.conj_unitary_of_same_hermitianMultiplicationModel E w hw K e (B₁.prod B₂) _ _ n _ _ m₁ m₂
    rw [← Quot.out_eq c₁, ← Quot.out_eq c₂]
    exact Quot.sound ⟨⟨y, hy⟩, Subtype.ext (by simpa [TwCl.rep] using hyc)⟩
  have hsupp : Function.support G ⊆ Φ '' S' := by
    intro κ hκ
    have hN : (B₁.prod B₂).N κ.rep ≠ 0 := by
      intro h0; apply hκ; simp [G, h0]
    have hfix : (B₁.prod B₂).σ (GlobalTheory.UnitLemma.InvAlg.Cl.rep κ) = GlobalTheory.UnitLemma.InvAlg.Cl.rep κ := (Quot.out κ).2
    have hunit : IsUnit (GlobalTheory.UnitLemma.InvAlg.Cl.rep κ) := (Quot.out κ).1.isUnit
    obtain ⟨γ, hγ, hmγ⟩ := GlobalTheory.T.exists_unitary_model_of_selfDualLatticeCount_ne_zero E w hw K e hBr n (Q₁ * Q₂) (B₁.prod B₂) _ _ hF hdeg hfix hunit hN
    have hcp : γ.val.charpoly = Q₁ * Q₂ := GlobalTheory.T.charpoly_eq_of_hermitianMultiplicationModel E w K e n (Q₁ * Q₂) (B₁.prod B₂) _ _ γ hmon hF hmγ
    let c : TwCl (MonoidHom.id (UL n w)) := Quot.mk _ ⟨γ, hγ⟩
    obtain ⟨g, hg'⟩ := (conjRel_equiv (UL n w)).symm
      ((conjRel_equiv (UL n w)).eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq c)))
    have hcrep : c.rep.1 = g.1⁻¹ * γ * g.1 := by
      have := congrArg Subtype.val hg'
      simpa [TwCl.rep] using this
    have hc : c ∈ S' := by
      show c.rep.1.val.charpoly = Q₁ * Q₂
      rw [hcrep, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj', hcp]
    refine ⟨c, hc, ?_⟩
    have m := hrep c hc
    rw [hcrep] at m
    obtain ⟨v, hv⟩ := GlobalTheory.T.hermitianModels_conj_unitary_differ_by_norm E w hw K e n (Q₁ * Q₂) (B₁.prod B₂) _ _ _ hsep hF γ g.1 g.2 hmγ m
    exact (Quot.out_eq (Φ c)).symm.trans ((Quot.sound ((clRel_equiv _).symm ⟨v, hv⟩)).trans (Quot.out_eq κ))
  calc _ = ∑ᶠ c, S'.indicator (fun c => G (Φ c)) c := finsum_congr fun c => by
          by_cases hc : c ∈ S'
          · rw [Set.indicator_of_mem hc, ← hterm c hc]
            exact if_pos hc
          · rw [Set.indicator_of_notMem hc]
            exact if_neg hc
    _ = ∑ᶠ c ∈ S', G (Φ c) := (finsum_mem_def _ _).symm
    _ = ∑ᶠ κ ∈ Φ '' S', G κ := (finsum_mem_image hinj).symm
    _ = ∑ᶠ κ, G κ := by
      exact (finsum_mem_inter_support_eq G (Φ '' S') Set.univ (by rw [Set.univ_inter, Set.inter_eq_right.2 hsupp])).trans
        (finsum_mem_univ G)

theorem kapOrb_congruence_eq_kapSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (n a b : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), a + b = n → Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → Algebra.adjoin K.E {(1 + algebraMap K.O B₁.A t * B₁.g)} = ⊤ → aeval (1 + algebraMap K.O B₁.A t * B₁.g) (Q₁.map e.symm.toRingHom) = 0 → Module.finrank K.E B₁.A = Q₁.natDegree → (1 + algebraMap K.O B₁.A t * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A t * B₁.g) = 1 → Algebra.adjoin K.E {(1 + algebraMap K.O B₂.A t * B₂.g)} = ⊤ → aeval (1 + algebraMap K.O B₂.A t * B₂.g) (Q₂.map e.symm.toRingHom) = 0 → Module.finrank K.E B₂.A = Q₂.natDegree → (1 + algebraMap K.O B₂.A t * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A t * B₂.g) = 1 → kapOrb n w Q₁ Q₂ ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w n ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}} : Set (UL n w))).indicator 1) = ((GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ : ℚ) : ℂ) := by
  intro E _ _ _ hU w hw K e he1 he2 he3 he4 k t ht htk n a b Q₁ Q₂ B₁ B₂ hab hm₁ hm₂ hd₁ hd₂ hsep hc₁ hc₂
    hadj₁ hae₁ hfr₁ hu₁ hadj₂ hae₂ hfr₂ hu₂
  exact kapOrb_eq_kapSum_of_fits hw ⟨he1, he2, he3, he4⟩ ht htk hsep (hm₁.mul hm₂)
    (by rw [hm₁.natDegree_mul hm₂, hd₁, hd₂, hab]) ⟨hadj₁, hae₁, hfr₁, hu₁⟩ ⟨hadj₂, hae₂, hfr₂, hu₂⟩ (Prod.ext rfl rfl)

end GlobalTheory.KapLat
