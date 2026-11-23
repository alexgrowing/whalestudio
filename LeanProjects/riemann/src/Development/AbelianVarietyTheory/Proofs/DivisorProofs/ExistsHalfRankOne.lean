import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.EqZeroIffSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.QuotientTiedToDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InhabitedAndRefines

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R]

theorem evenDefect_one_iff (D : DegPre R) : EvenDefect D (fun _ => 1) ↔ D.PsiEven := by
  have e : unitOn (1 : (FractionRing R)ˣ) = 1 := map_one _
  constructor
  · intro h χ
    refine corr_of_val D.P.isLB fun y J hJ => ?_
    have := h χ y J hJ
    rw [e, map_one, _root_.one_mul] at this
    rw [val_mul hJ, val_pull hJ, Category.id_comp]
    exact this
  · intro h χ z J hJ
    have := val_corr hJ (h χ) (𝟙 _)
    rw [val_mul hJ, val_pull hJ, Category.id_comp] at this
    rw [e, map_one, _root_.one_mul]
    exact this

theorem evenDefect_rescale (D : DegPre R) (h g : D.X → (FractionRing R)ˣ) (H : EvenDefect D h) :
    EvenDefect (rescale D g) (fun χ : D.X => h χ * g (-χ) * (g χ)⁻¹) := by
  intro χ z J hJ
  have := H χ z J hJ
  have a : ∀ χ : D.X, val ((rescale D g).psi χ) (𝟙 (TK R).left) z J =
      gm (𝟙 (TK R).left) z ⊤ (unitOn (g χ)) * val (D.psi χ) (𝟙 (TK R).left) z J := fun χ =>
    GlobalTheory.UU.val_scaleGen (Y := (TK R).left) (L := D.P.L) (unitOn (g χ)) (D.psi χ) (𝟙 _) hJ
  let u : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ :=
    (gm (𝟙 (TK R).left) z ⊤).comp (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom.toMonoidHom)
  have key : ∀ (χ : D.X) (p m s : ((TK R).left.presheaf.stalk z)ˣ), m * s = u (h χ) * p →
      u (g (-χ)) * m * s = u (h χ * g (-χ) * (g χ)⁻¹) * (u (g χ) * p) := fun χ p m s e => by
    rw [_root_.mul_assoc, e, map_mul, map_mul, map_inv]
    generalize u (h χ) = A, u (g (-χ)) = B, u (g χ) = C
    rw [_root_.mul_assoc (A * B), inv_mul_cancel_left, mul_left_comm, _root_.mul_assoc]
  exact (congrArg (fun q => q * val D.sym (D.xK χ) z J) (a (-(show D.X from χ)))).trans
    ((key χ _ _ _ this).trans (congrArg (fun q => u (h χ * g (-(show D.X from χ)) * (g χ)⁻¹) * q) (a χ).symm))

theorem lamVal_id {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB) {T : Over S}
    (x y : T ⟶ B) (z : T.left) (J J') (hJ : Good M z J) (hJ' : Good M z J') :
    lamVal (isoPullId (idIso (abelian₂ B M)) (F := 𝟙 _) rfl) (lift x y).left z J J' =
      trF (lamPts x y) negε (𝟙 _) z (fun k => J' (𝟙 _ ≫ lamPts x y k)) (fun k => J (𝟙 _ ≫ lamPts x y k)) := by
  have m := hJ.mem (fun I : ULift (Finset (Fin 2)) => (psum B (x2 B) I.down).left) (lift x y).left
  have m' := hJ'.mem (fun I : ULift (Finset (Fin 2)) => (psum B (x2 B) I.down).left) (lift x y).left
  have e := gw_isoPullId (idIso (abelian₂ B M)) (F := 𝟙 _) rfl (lift x y).left z _ _ m m'
  have e₂ := gm_linComb M (fun I : ULift (Finset (Fin 2)) => (psum B (x2 B) I.down).left) (fun I => (-1) ^ (2 - I.down.card)) (lift x y).left z _ _ m m'
  refine Eq.trans ?_ (e.trans (e₂.trans ?_))
  · rfl
  · have p : ∀ I : Finset (Fin 2), (lift x y).left ≫ (psum B (x2 B) I).left = (psum B ![x, y] I).left := fun I =>
      congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 B) I).trans (by
        congr 1; funext i; fin_cases i <;> simp [x2, preHom]))
    have inv : ∀ ψ : T.left ⟶ B.left, gm ψ z _ (M.g (J' ψ) (J ψ)) = (gm ψ z _ (M.g (J ψ) (J' ψ)))⁻¹ := fun ψ => by
      have c := gm_cocycle hM ψ z (hJ ψ) (hJ' ψ) (hJ ψ)
      have d := gm_cocycle hM ψ z (hJ ψ) (hJ ψ) (hJ ψ)
      rw [mul_eq_left.1 d] at c
      exact eq_inv_of_mul_eq_one_right c
    let H : (T.left ⟶ B.left) → (T.left.presheaf.stalk z)ˣ := fun ψ => gm ψ z _ (M.g (J ψ) (J' ψ))
    change ∏ I : ULift (Finset (Fin 2)), H ((lift x y).left ≫ (psum B (x2 B) I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      ∏ k, gm (𝟙 _ ≫ lamPts x y k) z _ (M.g (J' (𝟙 _ ≫ lamPts x y k)) (J (𝟙 _ ≫ lamPts x y k))) ^ negε k
    refine Eq.trans ?_ (Finset.prod_congr rfl fun k _ => congrArg (· ^ negε k) (inv (𝟙 _ ≫ lamPts x y k)).symm)
    change _ = ∏ k, (H (𝟙 _ ≫ lamPts x y k))⁻¹ ^ negε k
    simp only [p, Category.id_comp]
    rw [← Equiv.ulift.symm.prod_comp, show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide,
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
      Fin.prod_univ_four]
    have q0 : psum B ![x, y] ∅ = 1 := rfl
    have q1 : psum B ![x, y] {0} = x := _root_.mul_one x
    have q2 : psum B ![x, y] {1} = y := _root_.mul_one y
    have q3 : psum B ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
    simp [q0, q1, q2, q3, lamPts, negε]
    generalize H (x * y).left = A, H x.left = A₁, H y.left = A₂, H (1 : T ⟶ B).left = A₀
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem half_ofDeg (D : DegPre R) (h : D.TauBimult) : Half (ofDeg D h) (RingHom.id R) D (AddEquiv.refl _) fun _ _ => 1 := by
  have s : spMap (RingHom.id R) = 𝟙 (Sp R) := by simp [spMap]
  refine ⟨𝟙 _, 𝟙 _, isoPullId (idIso (abelian₂ D.P.A D.P.L)) rfl, ?_, ⟨by simp; rfl, by simp; rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [s]; exact GlobalTheory.UU.TorusQuotientChecks.isGrpPullback_id _
  · exact (isGen_iff _).2 (isoPullId_pgen (idIso_isGen (LB.isLB_linComb D.P.isLB _ _)) rfl)
  · intro T z J J' hJ hJ'
    refine (lamVal_id D.P.isLB 1 1 z J J' hJ hJ').trans ?_
    let H : (T.left ⟶ D.P.A.left) → (T.left.presheaf.stalk z)ˣ := fun ψ => gm ψ z _ (D.P.L.g (J' ψ) (J ψ))
    change ∏ k, H (𝟙 _ ≫ lamPts 1 1 k) ^ negε k = 1
    simp [Fin.prod_univ_four, lamPts, negε]
  · intro a
    rw [s]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  · intro κ hκ a b z J J' hJ hJ'
    obtain rfl : κ = 𝟙 _ := by
      rw [s] at hκ
      haveI : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
      exact (cancel_mono (jK R)).1 (hκ.trans (by simp))
    rw [show unitOn (1 : (FractionRing R)ˣ) = 1 from map_one _, map_one, _root_.mul_one]
    refine ((Wit.exists_tau D a b).choose_spec.2 _ _ z J' hJ').symm.trans ?_
    refine (gen_trans (Wit.exists_tau D a b).choose_spec.1 (𝟙 _) z (hJ'.mem _ _) (Good.mem (L := D.P.L) hJ _ _)).trans ?_
    exact congrArg₂ (· * ·) (lamVal_id D.P.isLB _ _ z J J' hJ hJ').symm rfl

theorem exists_half_rank_one (k : Type) [Field k] : ∃ (Q : Data (PowerSeries k)) (D : DegPre (PowerSeries k)) (e : D.X ≃+ Q.X),
    Module.finrank ℤ Q.X = 1 ∧ Half Q (RingHom.id _) D e (fun _ _ => 1) ∧ EvenDefect D fun _ => 1 := by
  obtain ⟨D, -, h, -⟩ := exists_cusp_data k (n := 1) one_ne_zero
  exact ⟨ofDeg D.toPre D.tau_bimult, D.toPre, AddEquiv.refl _, h, half_ofDeg _ _, (evenDefect_one_iff _).2 D.psi_even⟩

theorem half_models :
    (∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), EvenDefect D (fun _ => 1) ↔ D.PsiEven) ∧
    (∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (h g : D.X → (FractionRing R)ˣ), EvenDefect D h →
      EvenDefect (rescale D g) (fun χ : D.X => h χ * g (-χ) * (g χ)⁻¹)) ∧
    (∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (h : D.TauBimult),
      Half (ofDeg D h) (RingHom.id R) D (AddEquiv.refl _) fun _ _ => 1) ∧
    ∀ (k : Type) [Field k], ∃ (Q : Data (PowerSeries k)) (D : DegPre (PowerSeries k)) (e : D.X ≃+ Q.X),
      Module.finrank ℤ Q.X = 1 ∧ Half Q (RingHom.id _) D e (fun _ _ => 1) ∧ EvenDefect D fun _ => 1 :=
  ⟨fun _ _ _ D => evenDefect_one_iff D, fun _ _ _ D h g H => evenDefect_rescale D h g H,
    fun _ _ _ D h => half_ofDeg D h, fun k _ => exists_half_rank_one k⟩

end GlobalTheory.PolDeg
