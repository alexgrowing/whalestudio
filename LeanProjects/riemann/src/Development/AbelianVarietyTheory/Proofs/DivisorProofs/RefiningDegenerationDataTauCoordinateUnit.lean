import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateEqUnitMulTauCoordinate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.RefTauCoord

open GlobalTheory.PeriodBalance GlobalTheory.PsiTauCoordRel

theorem gm_stalk {X Y Z : Scheme.{0}} (κ : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (κ z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (κ ≫ r) z U a = Units.map (κ.stalkMap z).hom.toMonoidHom (gm r (κ z) U a) := by
  apply Units.ext
  refine (gm_val (κ ≫ r) z U h a).trans (Eq.trans ?_ (congrArg (κ.stalkMap z).hom (gm_val r (κ z) U h a)).symm)
  exact (Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ U) z h _).symm

theorem val_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y' ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (κ : Z ⟶ Y) (r : Y ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    val t (κ ≫ r) z J = Units.map (κ.stalkMap z).hom.toMonoidHom (val t r (κ z) fun ψ => J (κ ≫ ψ)) := by
  rw [val_of t (κ ≫ r) z J (fun k => J (κ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_stalk κ r z _ (Set.mem_iInter.2 fun k => hJ (κ ≫ r ≫ φ k)) _

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem exists_good_over (ξ : Spec (CommRingCat.of (FractionRing R))) {X S : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (s : X ⟶ S) [IsSeparated s] (f : Spec (CommRingCat.of R) ⟶ S) :
    ∃ J, Good L ξ J ∧ ∀ p : Spec (CommRingCat.of R) ⟶ X, p ≫ s = f →
      p (closedPoint R) ∈ L.U (J (jK R ≫ p)) := by
  haveI : IsDominant (jK R) := DVR.isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ X => exists_chart hL (p (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL ξ (K := {p : Spec (CommRingCat.of R) ⟶ X // p ≫ s = f})
    (fun p => jK R ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated s (a.2.trans b.2.symm) (jK R) h))
    (fun p => by
      have := DVR.eq_top_of_closedPoint_mem (p.1 ⁻¹ᵁ L.U (pick p.1)) (hpk p.1)
      have h2 : jK R ξ ∈ p.1 ⁻¹ᵁ L.U (pick p.1) := by rw [this]; trivial
      exact h2)
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

theorem gm_unitOn {A : Type} [CommRing A] (σ : A →+* FractionRing R) (ξ : Spec (CommRingCat.of (FractionRing R)))
    (k : Aˣ) : (gm (spMap σ) ξ ⊤ (unitOn k)).val = kst ξ (σ k) := by
  rw [gm_val _ ξ ⊤ trivial]
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) k.val)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  exact (congrArg ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom hnat).symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (hρ : Function.Injective ρ),
    Refines Q ρ D e → ∀ (a b : D.X) (k : (FractionRing R)ˣ), Q.TauCoord (e a) (e b) k →
      ∀ x : (FractionRing R')ˣ, IsTauCoord D a b x → ∃ u : R'ˣ, (x : FractionRing R') =
        algebraMap R' (FractionRing R') u * IsFractionRing.lift (A := R) (K := FractionRing R)
          (g := (algebraMap R' (FractionRing R')).comp ρ) ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (k : FractionRing R) := by
  intro R _ _ R' _ _ _ Q ρ D e hρ href a b k hk x hx
  letI := D.P.isAb.comm
  obtain ⟨β, β₂, w, h₁, h₂, -, -, h₅⟩ := href
  have hσ : ∀ r, IsFractionRing.lift (A := R) (K := FractionRing R) (g := (algebraMap R' (FractionRing R')).comp ρ)
      ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (algebraMap R (FractionRing R) r) =
      algebraMap R' (FractionRing R') (ρ r) := fun r => IsFractionRing.lift_algebraMap _ r
  generalize IsFractionRing.lift (A := R) (K := FractionRing R) (g := (algebraMap R' (FractionRing R')).comp ρ)
      ((IsFractionRing.injective R' (FractionRing R')).comp hρ) = σ at hσ ⊢
  have hκ : spMap σ ≫ jK R = jK R' ≫ spMap ρ := by
    have : σ.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp ρ := RingHom.ext hσ
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, this]
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  haveI : IsProper Q.B.hom := Q.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R'))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J', hJ', hc'⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  obtain ⟨J, hJ, hc⟩ := exists_good_over ξ Q.M.isLB Q.B.hom (spMap ρ)
  have E := h₅ (spMap σ) hκ a b ξ J J' hJ hJ'
  obtain ⟨u₁, e₁⟩ := GlobalTheory.TauShift.coord_val D ξ hJ' hc' hx
  obtain ⟨u₂, e₂⟩ : ∃ u : R'ˣ, (lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left ξ J J').val =
      cst ξ u := by
    have hp : (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left = jK R' ≫ (lift (D.c a) (D.c b)).left := by
      simp [← CartesianMonoidalCategory.comp_lift]
    rw [hp]
    refine unit_gm' ξ (lift (D.c a) (D.c b)).left _ ?_ _
    refine And.intro (mem_pull.2 (Set.mem_iInter.2 fun I => ?_)) (Set.mem_iInter.2 fun I => ?_)
    · have := hc ((lift (D.c a) (D.c b)).left ≫ β₂ ≫ (psum Q.B (x2 Q.B) I.down).left) (by
        rw [Category.assoc, Category.assoc, Over.w, ← Over.w (fst Q.B Q.B), reassoc_of% h₂.1, h₁.1.w,
          Over.w_assoc, Over.w_assoc]
        exact Category.id_comp _)
      exact this
    · have := hc' ((lift (D.c a) (D.c b)).left ≫ (psum D.P.A (x2 D.P.A) I.down).left) (by
        rw [Category.assoc, Over.w, Over.w]; rfl)
      exact this
  obtain ⟨u, -, hu⟩ := hk
  obtain ⟨u₃, e₃⟩ : ∃ v : R'ˣ, (val u (jK R' ≫ spMap ρ) ξ J).val = cst ξ v := by
    refine unit_gm' ξ _ _ (Set.mem_iInter.2 fun i => ?_) _
    obtain ⟨q, hq⟩ : ∃ q : 𝟙_ (Over (Sp R)) ⟶ Q.B, lamPts (Q.c (e a)) (Q.c (e b)) i = q.left := by
      fin_cases i <;> exact ⟨_, rfl⟩
    have := hc (spMap ρ ≫ lamPts (Q.c (e a)) (Q.c (e b)) i) (by
      rw [hq, Category.assoc, Over.w q]; exact Category.comp_id _)
    exact this
  have hT := congrArg (Units.map ((spMap σ).stalkMap ξ).hom.toMonoidHom)
    (hu (spMap σ ξ) (fun ψ => J (spMap σ ≫ ψ)) fun ψ => hJ (spMap σ ≫ ψ))
  have v₁ := val_stalk (Q.tau (e a) (e b)) (spMap σ) (𝟙 (TK R).left) ξ hJ
  have v₂ := val_stalk u (spMap σ) (toUnit (TK R)).left ξ hJ
  have v₃ := gm_stalk (spMap σ) (𝟙 (TK R).left) ξ ⊤ trivial (unitOn k)
  have hh : spMap σ ≫ (toUnit (TK R)).left = jK R' ≫ spMap ρ := by
    rw [show (toUnit (TK R)).left = jK R by simpa using Over.w (toUnit (TK R))]; exact hκ
  have hT' := v₁.trans (hT.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) v₃.symm v₂.symm)))
  rw [hh] at hT'
  rw [show spMap σ ≫ 𝟙 (TK R).left = spMap σ from Category.comp_id _] at hT'
  have F : (val (Q.tau (e a) (e b)) (spMap σ) ξ J).val = kst ξ (σ k) * cst ξ u₃ :=
    (congrArg Units.val hT').trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) (gm_unitOn σ ξ k) e₃))
  have G : kst ξ x.val = cst ξ u₁ * (cst ξ u₂ * (kst ξ (σ k) * cst ξ u₃)) :=
    (congrArg Units.val e₁).trans ((Units.val_mul _ _).trans (congrArg (cst ξ u₁ * ·)
      ((congrArg Units.val E).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) e₂ F)))))
  refine ⟨u₁ * u₂ * u₃, kst_injective ξ ?_⟩
  rw [G, map_mul, kst_algebraMap, Units.val_mul, Units.val_mul, map_mul, map_mul]
  ring

end GlobalTheory.RefTauCoord
