import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ChangeChart
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RatioTrans
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TripleProductPointCompProjection

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig GlobalTheory.WCub

theorem tri_map {S S' : Scheme.{0}} {G G' : Over S} (f : S' ⟶ S) {E E' T : Over S'} (p : (Over.map f).obj E ⟶ G)
    (p' : (Over.map f).obj E' ⟶ G') (x : Fin 3 → (T ⟶ E')) (ρ : E' ⟶ E) (π : G' ⟶ G)
    (h : p'.left ≫ π.left = ρ.left ≫ p.left) :
    (∀ a, ((Over.map f).map (x a) ≫ p') ≫ π = (Over.map f).map (x a ≫ ρ) ≫ p) ∧
      tri f p' x ≫ (π ⊗ₘ π ⊗ₘ π).left = tri f p (fun a => x a ≫ ρ) := by
  have e : ∀ a, ((Over.map f).map (x a) ≫ p') ≫ π = (Over.map f).map (x a ≫ ρ) ≫ p := fun a =>
    Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg ((x a).left ≫ ·) h).trans
      (Category.assoc _ _ _).symm))
  refine ⟨e, ?_⟩
  show (lift _ (lift _ _) ≫ (π ⊗ₘ π ⊗ₘ π)).left = _
  rw [lift_map, lift_map, e, e, e]

theorem psum_comp {S : Scheme.{0}} {E E' T : Over S} [GrpObj E] [IsCommMonObj E] [GrpObj E'] [IsCommMonObj E']
    (x : Fin 3 → (T ⟶ E')) (ρ : E' ⟶ E) [IsMonHom ρ] (k : Finset (Fin 3)) :
    (psum E' x k).left ≫ ρ.left = (psum E (fun a => x a ≫ ρ) k).left :=
  congrArg (fun z => z.left) (psum_hom (MonoidHom.mk' (fun z : T ⟶ E' => z ≫ ρ) fun a b => MonObj.mul_comp a b ρ) x k)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem w_cub_val (U : UnifPre I D A G) (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (x : Fin 3 → (T ⟶ thickObj R I e G)) (y : T.left) {J N} (hJ : Good D.toPre.P.L y J) (hN : Good U.LG.L y N) :
    val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (tri (thick R I e) (U.gt e).pG x) y J =
      (∏ k : thK, Geo.Tor.gw (U.w e) (psum (thickObj R I e G) x k.down).left y
        (J (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k))
        (fun _ => N (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k)) ^ thε k) *
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t (tri (thick R I e) (fstG I e G) x) y N := by
  have := (U.gt e).q_hom
  have f₃ := tri_thφ (thick R I e) (fstG I e G) x (𝟙 _) (Category.id_comp _).symm
  have f₄ := tri_thφ (thick R I e) (U.gt e).pG x (U.gt e).q rfl
  exact (clause_iff (tri (thick R I e) (U.gt e).pG x) (tri (thick R I e) (fstG I e G) x)
    (fun k : thK => (psum (thickObj R I e G) x k.down).left) _ _ _ (D.toPre.cub.t.s _) (U.cubG.t.s _)
    (fun k => (U.w e).s (fun _ => J (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k),
      fun _ => N (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k))) thε).1
    (U.w_cub e T x _ _ (fun a b e => congrArg N e) (fun a b e => congrArg J e)) y
    (hJ.mem _ _) (hN.mem _ _) (fun k => ⟨mem_pull.2 (pt_of_eq (f₄ k) y ▸
      hJ (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k)),
      mem_pull.2 (pt_of_eq (f₃ k) y ▸ hN (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k))⟩)

theorem cub_box_val (hG : GlobalFnsSt) (pD : IsPowDeg D'.toPre D.toPre j) (e : ℕ)
    {E E' T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (p : (Over.map (thick R I e)).obj E ⟶ D.toPre.P.A)
    (p' : (Over.map (thick R I e)).obj E' ⟶ D'.toPre.P.A) (x : Fin 3 → (T ⟶ E')) (ρ : Fin j → (E' ⟶ E))
    (h : ∀ i, p'.left ≫ (pD.pw.pr i).left = (ρ i).left ≫ p.left) (y : T.left) (J J')
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') :
    (∏ k : thK, om (pr := fun i => (pD.pw.pr i).left) pD.w y J J'
        (tri (thick R I e) p' x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ^ thε k) *
      val (L := D'.toPre.P.L) (φ := thφ D'.toPre.P.A (x3 D'.toPre.P.A)) (ε := thε) D'.toPre.cub.t
        (tri (thick R I e) p' x) y J' =
      ∏ i, val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (tri (thick R I e) p (fun a => x a ≫ ρ i)) y J := by
  have c := GlobalTheory.CubBox.cubV_box hG R j D.toPre D'.toPre pD ((Over.map (thick R I e)).obj T) y J J' hJ hJ'
    ((Over.map (thick R I e)).map (x 0) ≫ p') ((Over.map (thick R I e)).map (x 1) ≫ p')
    ((Over.map (thick R I e)).map (x 2) ≫ p')
  have q := prod_cub ((Over.map (thick R I e)).map (x 0) ≫ p') ((Over.map (thick R I e)).map (x 1) ≫ p')
    ((Over.map (thick R I e)).map (x 2) ≫ p') (om (pr := fun i => (pD.pw.pr i).left) pD.w y J J')
  refine (congrArg₂ (· * ·) q rfl).trans ((mul_comm _ _).trans (c.trans (Finset.prod_congr rfl fun i _ => ?_)))
  have t := (tri_map (thick R I e) p p' x (ρ i) (pD.pw.pr i) (h i)).1
  rw [t, t, t]
  rfl

theorem cub_box (hG : GlobalFnsSt) (pD : IsPowDeg D'.toPre D.toPre j) (pG : IsPowGrp G' G j) (U : UnifPre I D A G)
    (e : ℕ) (g' : GtCoord I D'.toPre e G')
    (hq : ∀ i, g'.pG.left ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ (U.gt e).pG.left)
    (w' : LB.Iso ((boxLB U.LG.L pG.pr).pull (fstG I e G').left) (D'.toPre.P.L.pull g'.pG.left))
    (Q : BoxSquare (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) pD.w (U.w e) w' (rhoE I pG e))
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : Fin 3 → (T ⟶ thickObj R I e G'))
    (jL : thK → Fin j → U.LG.L.ι) (jM : thK → D'.toPre.P.L.ι)
    (cM : LB.Coh D'.toPre.P.L (fun k => tri (thick R I e) g'.pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) jM)
    (y : T.left) (hB : tri (thick R I e) g'.pG x y ∈ LB.wchart D'.toPre.P.L (thφ D'.toPre.P.A (x3 D'.toPre.P.A)) jM)
    (hL : tri (thick R I e) (fstG I e G') x y ∈ LB.wchart (boxLB U.LG.L pG.pr) (thφ G' (x3 G')) jL) :
    gm (tri (thick R I e) g'.pG x) y (LB.wchart D'.toPre.P.L (thφ D'.toPre.P.A (x3 D'.toPre.P.A)) jM)
        (D'.toPre.cub.t.s jM) =
      (∏ k : thK, Geo.Tor.gw w' (psum (thickObj R I e G') x k.down).left y (jM k) (fun _ => jL k) ^ thε k) *
      gm (tri (thick R I e) (fstG I e G') x) y (LB.wchart (boxLB U.LG.L pG.pr) (thφ G' (x3 G')) jL)
        ((boxCub pG U.LG.L U.cubG.t).s jL) := by
  have := g'.q_hom
  have := (U.gt e).q_hom
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  let ρ : Fin j → (thickObj R I e G' ⟶ thickObj R I e G) := fun i => (Over.pullback (thick R I e)).map (pG.pr i)
  have ps : ∀ i (k : thK), (psum (thickObj R I e G') x k.down).left ≫ rhoE I pG e i =
      (psum (thickObj R I e G) (fun a => x a ≫ ρ i) k.down).left := fun i k => by
    have := pG.hom i
    exact psum_comp x (ρ i) k.down
  have f₂ := tri_thφ (thick R I e) g'.pG x g'.q rfl
  have f₃ := fun i => tri_thφ (thick R I e) (fstG I e G) (fun a => x a ≫ ρ i) (𝟙 _) (Category.id_comp _).symm
  have f₄ := fun i => tri_thφ (thick R I e) (U.gt e).pG (fun a => x a ≫ ρ i) (U.gt e).q rfl
  have hψ : ∀ i a, thφ G' (x3 G') a ≫ (pG.pr i).left = (pG.pr i ⊗ₘ pG.pr i ⊗ₘ pG.pr i).left ≫ thφ G (x3 G) a :=
    fun i a => letI := pG.hom i; (CubeMap.ofHom (pG.pr i)).psum_comm a.down
  have t := fun i => (tri_map (thick R I e) (fstG I e G) (fstG I e G') x (ρ i) (pG.pr i) (hρ i).symm).2
  have key := rel_box (T := (thickObj R I e G).left) (T' := (thickObj R I e G').left) D.toPre.P.isLB D'.toPre.P.isLB
    U.LG.isLB (U.w_gen e) Q hρ hq (K := thK) (ε := thε) y (fun k => (psum (thickObj R I e G') x k.down).left)
    (φ := thφ G (x3 G)) (ψ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ψ' := thφ D'.toPre.P.A (x3 D'.toPre.P.A))
    U.cubG.isGen D.toPre.cub.t D'.toPre.cub.t (tri (thick R I e) g'.pG x)
    (fun i => tri (thick R I e) (U.gt e).pG (fun a => x a ≫ ρ i))
    (fun i => tri (thick R I e) (fstG I e G) (fun a => x a ≫ ρ i))
    (fun i k => (congrArg (· ≫ fGl I G e) (ps i k)).trans (f₃ i k).symm) (fun k => (f₂ k).symm)
    (fun i k => (congrArg (· ≫ pGl U e) (ps i k)).trans (f₄ i k).symm)
    (cub_box_val hG pD e (U.gt e).pG g'.pG x ρ hq y)
    (fun i J N hJ hN => (w_cub_val U e T (fun a => x a ≫ ρ i) y hJ hN).trans (congrArg₂ (· * ·)
      (Finset.prod_congr rfl fun k _ => by rw [ps i k]) rfl))
    jL jM cM (Set.mem_iInter.1 hB) (fun k i => by
      have a : ((tri (thick R I e) (fstG I e G') x ≫ thφ G' (x3 G') k) ≫ (pG.pr i).left) y ∈ U.LG.L.U (jL k i) :=
        Set.mem_iInter.1 (Set.mem_iInter.1 hL k) i
      rw [Category.assoc, hψ, ← Category.assoc, t] at a
      exact a)
  refine key.trans (congrArg₂ (· * ·) rfl (Eq.trans (Finset.prod_congr rfl fun i _ => ?_)
    (gm_box_pull U.LG.L (fun i => (pG.pr i).left) _ hψ (fun _ => U.cubG.t) _ y jL hL).symm))
  rw [t]

end GlobalTheory.PowUnif
