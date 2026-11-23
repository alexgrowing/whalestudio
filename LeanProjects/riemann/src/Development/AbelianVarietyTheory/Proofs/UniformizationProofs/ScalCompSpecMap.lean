import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtIffStalks

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ExpandsLinear

def scalOn {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) :
    R →+* Γ(Y, W) :=
  (Y.presheaf.map (homOfLE le_top).op).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem scalOn_apply {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    (W : Y.Opens) (r : R) : resTop W (scal p r) = scalOn p W r := rfl

theorem scal_comp_specMap {R C : Type} [CommRing R] [CommRing C] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of C)) (φ : R →+* C) (r : R) :
    scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r = scal p (φ r) := by
  unfold scal
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  congr 1
  have := congrArg (fun g => g.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact this.symm

theorem app_resTop_scal {R : Type} [CommRing R] {Y Y' : Scheme.{0}} (h : Y' ⟶ Y)
    (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) (r : R) :
    (h.app W).hom (resTop W (scal p r)) = resTop _ (scal (h ≫ p) r) := by
  simp only [resTop]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.naturality, CommRingCat.hom_comp,
    RingHom.comp_apply]
  rfl

def secComb {Y : Scheme.{0}} {L : LB Y} {n : ℕ} (a : Fin n → Γ(Y, ⊤)) (s : Fin n → LB.Sec L) : LB.Sec L where
  f := fun j => ∑ i, resTop _ (a i) * (s i).f j
  compat := fun j j' => by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (a i) (s i)).compat j j'

theorem secScal_comb {R C : Type} [CommRing R] [CommRing C] (φ : R →+* C) {X Y Y' : Scheme.{0}} (L : LB X)
    {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ)
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (h : Y' ⟶ Y) (π : Y' ⟶ Spec (CommRingCat.of C))
    (π' : Y' ⟶ Spec (CommRingCat.of R)) (p : Y ⟶ Spec (CommRingCat.of R))
    (hπ : π' = π ≫ Spec.map (CommRingCat.ofHom φ)) (hp : h ≫ p = π') {n : ℕ}
    (s : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (t : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂))
    (r a : Fin n → R) (d : R) (c : Fin n → C) (hc : ∀ i, φ (a i) * φ (r i) = φ d * c i)
    (H : ∀ i, GeneratorPullback.SecScal L φ₁ ε₁ (s i) φ₂ ε₂ (t i) h (scal π' (r i)))
    (s₀ : LB.Sec (LB.LinComb L φ₁ ε₁)) (hs : ∀ j, s₀.f j = ∑ i, resTop _ (scal π (c i)) * (s i).f j) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₀ φ₂ ε₂ (secComb (fun i => scal p (a i)) t) h (scal π' d) := by
  intro j₁ j₂ hco
  erw [hs]
  dsimp only [secComb]
  erw [map_sum, map_sum, map_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have Hi := H i j₁ j₂ hco
  erw [map_mul, map_mul, map_mul, Hi, app_resTop_scal, SecOps.resTop_res, SecOps.resTop_res]
  rw [hp, hπ, scal_comp_specMap, scal_comp_specMap, scal_comp_specMap, ← _root_.mul_assoc, ← _root_.mul_assoc]
  simp only [scalOn_apply]
  rw [← map_mul, hc, map_mul]

theorem fam_sum_f {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {N : Type} (S : Finset N) (s : N → Fam D F k) (α : D.X) (j) :
    ((∑ i ∈ S, s i).s α).f j = ∑ i ∈ S, ((s i).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

end ExpandsLinear

open ExpandsLinear in

theorem expands_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) (n : ℕ) (b : Fin n → U.SecK k) (F : Fin n → Fam D.toPre (FractionRing R) k) (c : Fin n → FractionRing R) (s : U.SecK k), (∀ i, U.Expands k (b i) (F i)) → (∀ j, (s).f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j) → U.Expands k s (∑ i, c i • F i) := by
  intro R _ _ I _ D A G _ _ _ U k n b F c s hE hs
  choose r hr σ f hσ hf hE using hE
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun i => c i / algebraMap R (FractionRing R) (r i))
  choose a ha using hd
  have hc : ∀ i, algebraMap R (FractionRing R) (a i) * algebraMap R (FractionRing R) (r i) =
      algebraMap R (FractionRing R) d * c i := fun i => by
    have h0 : algebraMap R (FractionRing R) (r i) ≠ 0 :=
      fun h => hr i ((IsFractionRing.injective R (FractionRing R)) (h.trans (map_zero _).symm))
    rw [ha i, Algebra.smul_def, _root_.mul_assoc, div_mul_cancel₀ _ h0]
  refine ⟨d, nonZeroDivisors.ne_zero d.2, secComb (fun i => scal G.hom (a i)) σ,
    fun α => secComb (fun i => scal D.toPre.P.A.hom (a i)) (fun i => f i α), ?_, fun α => ?_, fun e => ?_⟩
  · exact secScal_comb (algebraMap R (FractionRing R)) _ _ _ _ _ _ (pullback.snd G.hom (jK R)) _ G.hom rfl
      pullback.condition b σ r a d c hc hσ s hs
  · refine secScal_comb (algebraMap R (FractionRing R)) _ _ _ _ _ _
      (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left _ D.toPre.P.A.hom ?_
      (Over.w (DegPre.prB D.toPre (FractionRing R))) (fun i => (F i).s α) (fun i => f i α) r a d c hc
      (fun i => hf i α) _ fun j => ?_
    · rw [← Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)]
      congr 1
      change Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ _ = _
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    · rw [fam_sum_f]
      rfl
  · exact expandsAt_linear R I D A G U k e n a σ f _ _ (fun i => hE i e) (fun _ => rfl) (fun _ _ => rfl)

end GlobalTheory
