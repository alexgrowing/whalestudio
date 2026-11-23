import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowTorus

section Box

variable {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

private theorem units_map_stalkMap_gm_eq_gm_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (s : Y ⟶ X) (z : Z) (U : X.Opens)
    (a : Γ(X, U)ˣ) :
    Units.map ((r.stalkMap z).hom : Y.presheaf.stalk (r z) →* Z.presheaf.stalk z) (gm s (r z) U a) =
      gm (r ≫ s) z U a := by
  unfold gm
  by_cases h : s (r z) ∈ U
  · have h' : (r ≫ s) z ∈ U := h
    rw [dif_pos h, dif_pos h']
    apply Units.ext
    simp only [Units.coe_map, MonoidHom.coe_coe]
    unfold pullU
    simp only [Units.coe_map, MonoidHom.coe_coe, MonoidHom.comp_apply]
    have key := congrArg (fun φ => φ.hom ((s.app U).hom a.val)) (Scheme.Hom.germ_stalkMap r (s ⁻¹ᵁ U) z h)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at key
    exact key
  · have h' : ¬ (r ≫ s) z ∈ U := h
    rw [dif_neg h, dif_neg h']
    simp

private theorem units_map_stalkMap_bw_eq_bw_comp {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
    (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (r : Z ⟶ Y) (ψ : Y ⟶ X') (z : Z) (jN : Fin j → M.ι) (k : M'.ι) :
    Units.map ((r.stalkMap z).hom : Y.presheaf.stalk (r z) →* Z.presheaf.stalk z) (bw w ψ (r z) jN k) =
      bw w (r ≫ ψ) z jN k := by
  unfold bw
  exact units_map_stalkMap_gm_eq_gm_comp r ψ z _ _

private theorem units_map_stalkMap_val_eq_val_comp {X Y Y₁ Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y₁ ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (s : Y ⟶ Y₁) (z : Z) (J : (Z ⟶ X) → L.ι) :
    Units.map ((r.stalkMap z).hom : Y.presheaf.stalk (r z) →* Z.presheaf.stalk z)
        (val t s (r z) (fun ψ => J (r ≫ ψ))) = val t (r ≫ s) z J := by
  rw [val_of t (r ≫ s) z J (fun k => J (r ≫ s ≫ φ k)) (fun k => by rw [Category.assoc]),
    val_of t s (r z) _ (fun k => J (r ≫ s ≫ φ k)) (fun k => rfl)]
  exact units_map_stalkMap_gm_eq_gm_comp r s z _ _

theorem box_gen_val_along (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {Y₀ : Scheme.{0}}
    {φ' : K → (Y ⟶ X')} {φ : Fin j → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε))
    (H : LB.Gen.Maps (LB.linCombIso w φ' ε) t'
      (GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))))
    (r : Z ⟶ Y) (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (r ≫ φ' a) y (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r y J' =
      ∏ i, val (t i) (r ≫ ρ i) y J := by
  have E := box_gen_val w hψ t' t H (r y) (J := fun ψ => J (r ≫ ψ)) (J' := fun ψ => J' (r ≫ ψ))
    (fun ψ => hJ (r ≫ ψ)) (fun ψ => hJ' (r ≫ ψ))
  have E2 := congrArg (Units.map ((r.stalkMap y).hom : Y.presheaf.stalk (r y) →* Z.presheaf.stalk y)) E
  rw [map_mul, map_prod, map_prod] at E2
  simp only [map_zpow, units_map_stalkMap_bw_eq_bw_comp, units_map_stalkMap_val_eq_val_comp, Category.comp_id] at E2
  simp only [Category.assoc]
  exact E2

end Box

section Coord

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem val_on_torus {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (χ : D.X) {z : Z.left}
    {J : (Z.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (τ : Z ⟶ splitTorus _ D.X) :
    val (g.t χ) (τ ≫ g.i).left z J = gm τ.left z ⊤ (charUnit _ D.X χ) := by
  have h1 := GlobalTheory.TorusCoord.val_torus g χ hJ τ 1
  rw [_root_.mul_one] at h1
  rw [h1, GlobalTheory.TorusCoord.val_unit g χ hJ, _root_.mul_one]

theorem prod_on_torus (χ : D.X) {V : Type} [CommGroup V]
    (f : ((splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X).left ⟶ D.P.A.left) → V) :
    ∏ k, f (g.i.left ≫ D.Oφ g.pG χ k) ^ Oinvε k = 1 := by
  have k0 : g.i ≫ g.q = (1 : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ thickObj R I e G) ≫ g.q := by
    have := g.q_hom
    rw [g.isKernel.w, MonObj.one_comp]
    rfl
  have k1 : (Over.map (thick R I e)).map g.i ≫ g.pG = 1 := by
    have h := GlobalTheory.TorusCoord.im_congr g k0
    rw [GlobalTheory.TorusCoord.im_one] at h
    exact h
  have e0 : g.i.left ≫ (padd D.P.A g.pG (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ)).left =
      g.i.left ≫ (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ).left := by
    change ((Over.map (thick R I e)).map g.i ≫ _).left = ((Over.map (thick R I e)).map g.i ≫ _).left
    have hp : padd D.P.A g.pG (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ) =
        g.pG * (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ D.c χ) := rfl
    rw [hp, MonObj.comp_mul, k1, _root_.one_mul]
  have e2 : g.i.left ≫ g.pG.left = g.i.left ≫ (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ η).left := by
    change ((Over.map (thick R I e)).map g.i ≫ _).left = ((Over.map (thick R I e)).map g.i ≫ _).left
    rw [k1, ← Category.assoc, toUnit_unique ((Over.map (thick R I e)).map g.i ≫ toUnit _) (toUnit _)]
    rfl
  simp only [Fin.prod_univ_four, Oinvε, DegPre.Oφ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  erw [e0, e2]
  group

end Coord

theorem gm_char_zero {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X)
    (z : Z.left) : gm τ.left z ⊤ (charUnit S X 0) = 1 := by
  have h := GlobalTheory.splitTorusPointsEquiv_val S X (splitTorus S X) (𝟙 _) 0
  rw [ofAdd_zero, map_one, Units.val_one] at h
  have h2 : charUnit S X 0 = 1 := by
    ext
    rw [Units.val_one, h]
    simp
  rw [h2, map_one]

theorem torus_ext {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ τ' : Z ⟶ splitTorus S X)
    (h : ∀ χ z, gm τ.left z ⊤ (charUnit S X χ) = gm τ'.left z ⊤ (charUnit S X χ)) : τ = τ' := by
  apply (splitTorusPointsEquiv S X Z).injective
  refine MonoidHom.ext fun χ => Units.ext ?_
  obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.splitTorusPointsEquiv_val]
  exact GlobalTheory.TorusCoord.appTop_eq_of_gm _ _ _ (h x)

section Pow

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}

theorem exists_factor (P : UnifPowOf3 pD pA pG U' U) (e : ℕ) (i : Fin j) :
    ∃ h : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
      h ≫ (U.gt e).i = (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i) := by
  have hk := (U.gt e).isKernel
  have hη : (η : 𝟙_ _ ⟶ thickObj R I e D'.toPre.P.A) ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = η := by
    have hm := pD.pw.hom i
    change (_ ≫ _) ≫ _ = _ ≫ _
    rw [Category.assoc, ← Functor.map_comp, hm.one_hom]
  have hc : ((U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i)) ≫ (U.gt e).q =
      toUnit _ ≫ η := by
    rw [Category.assoc, ← P.q_pr e i, ← Category.assoc, (U'.gt e).isKernel.w, Category.assoc, hη]
  exact ⟨hk.lift _ _ hc, hk.lift_fst _ _ hc⟩

set_option maxHeartbeats 800000 in

theorem char_prod (P : UnifPowOf3 pD pA pG U' U) (e : ℕ)
    (h : Fin j → (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X))
    (hh : ∀ i, h i ≫ (U.gt e).i = (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i))
    (x : D'.toPre.X) (z : (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X).left) :
    gm (𝟙 _) z ⊤ (charUnit _ D'.toPre.X x) = ∏ i, gm (h i).left z ⊤ (charUnit _ D.toPre.X (pD.xe x i)) := by
  obtain ⟨J, hJ, -⟩ := exists_good D.toPre.P.L D.toPre.P.isLB z (K := PEmpty) (fun k => k.elim)
    (fun k => k.elim) (fun a => a.elim) (fun k => k.elim)
  obtain ⟨J', hJ', -⟩ := exists_good D'.toPre.P.L D'.toPre.P.isLB z (K := PEmpty) (fun k => k.elim)
    (fun k => k.elim) (fun a => a.elim) (fun k => k.elim)
  obtain ⟨hψ, H⟩ := P.t_pr e x
  have B := box_gen_val_along pD.w hψ ((U'.gt e).t x) (fun i => (U.gt e).t (pD.xe x i)) H
    (U'.gt e).i.left z hJ hJ'
  have hP := prod_on_torus (U'.gt e) x (fun ψ => bw pD.w ψ z (fun i => J (ψ ≫ (pD.pw.pr i).left)) (J' ψ))
  rw [hP, _root_.one_mul] at B
  have L1 := val_on_torus (U'.gt e) x hJ' (𝟙 _)
  rw [Category.id_comp] at L1
  rw [L1] at B
  refine B.trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [← val_on_torus (U.gt e) (pD.xe x i) hJ (h i), hh i]
  rfl

end Pow

theorem torus_isPow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (P : UnifPowOf3 pD pA pG U' U) (e : ℕ), ∃ pT : IsPowGrp (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X) (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X) j, (∀ i, (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i) = pT.pr i ≫ (U.gt e).i) ∧ ∀ (i : Fin j) (χ : D.toPre.X), res (fun x _ => show (pT.pr i).left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial) (pullU (pT.pr i).left ⊤ (charUnit _ D.toPre.X χ)) = charUnit _ D'.toPre.X (pD.xe.symm (Pi.single i χ)) := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U P e
  obtain ⟨p, hp⟩ := GlobalTheory.exists_isPowGrp_splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X
    D'.toPre.X j pD.xe
  choose h hh using fun i => exists_factor P e i
  refine ⟨p, fun i => ?_, hp⟩
  have key : h i = p.pr i := by
    apply torus_ext
    intro χ z
    have c := char_prod P e h hh (pD.xe.symm (Pi.single i χ)) z
    rw [Finset.prod_eq_single i] at c
    · rw [AddEquiv.apply_symm_apply, Pi.single_eq_same] at c
      rw [← c]
      have hz := (gm_rp₁ (p.pr i).left z ⊤ ⊤ _ trivial (charUnit _ D.toPre.X χ)).symm.trans
        (congrArg (gm (𝟙 _) z ⊤) (hp i χ))
      exact hz.symm
    · intro b _ hb
      rw [AddEquiv.apply_symm_apply, Pi.single_eq_of_ne hb, gm_char_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [← hh i, key]

end GlobalTheory.PowTorus
