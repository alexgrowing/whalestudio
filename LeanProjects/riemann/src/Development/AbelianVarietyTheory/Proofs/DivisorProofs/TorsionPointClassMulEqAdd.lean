import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricGenericPointStalkOfFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantGeometricGenericPointSpecDomainStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

open CartesianMonoidalCategory MonObj
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem valAt_comp_stalk {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {V : Scheme.{0}} (ℓ : V ⟶ X') {M : Type}
    (w : M → (V ⟶ G.left)) {W : Scheme.{0}} (f : W ⟶ (torsion G n).left) (q : W) (c : M)
    (h : ValAt G n ℓ w (f q) c) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (y : Sp Ω ⟶ Spec (W.presheaf.stalk q)) (z : Sp Ω ⟶ V)
    (hz : y ≫ W.fromSpecStalk q ≫ f ≫ (torsion G n).hom = z ≫ ℓ) :
    y ≫ W.fromSpecStalk q ≫ f ≫ (torsion.ι G n).left = z ≫ w c := by
  have e := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := q)
  have h1 := h Ω (y ≫ Spec.map (f.stalkMap q)) z (by rw [Category.assoc, reassoc_of% e]; exact hz)
  rwa [Category.assoc, reassoc_of% e] at h1

theorem comp_torsion_ι_mulN {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {Y : Over X'} (a : Y ⟶ torsion G n) :
    (a ≫ torsion.ι G n) ≫ mulN G n = 1 := by
  have e : torsion.ι G n ≫ mulN G n = toUnit (torsion G n) ≫ (η : 𝟙_ (Over X') ⟶ G) :=
    (pullback.condition (f := mulN G n) (g := (η : 𝟙_ (Over X') ⟶ G))).trans
      (congrArg (· ≫ (η : 𝟙_ (Over X') ⟶ G)) (toUnit_unique _ _))
  rw [Category.assoc, e, ← Category.assoc, Hom.one_def]
  congr 1
  exact toUnit_unique _ _

theorem valAt_mul : ∀ {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c')
    (hadd : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (a b : M) (A B C : Over.mk (x ≫ ℓ) ⟶ G),
      A.left = x ≫ w a → B.left = x ≫ w b → C.left = x ≫ w (a + b) → C = A * B)
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P Q : Over.mk t ⟶ G)
    (PT QT RT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (hRT : RT ≫ (torsion.ι G n).left = (P * Q).left) (x : Sp K)
    (cP cQ cR : M) (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) cQ)
    (hcR : GlobalTheory.TorsSpec.ValAt G n ℓ w (RT x) cR), cR = cP + cQ := by
  intro X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ hun hadd K _ _ t P Q PT QT RT hPT hQT hRT x cP cQ cR hcP hcQ hcR
  haveI : Etale (torsion G n).hom := GlobalTheory.GrpTangent.etale_torsion G hn
  have hιT : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w (torsion.ι G n)
  have hPt : PT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hPT]; exact Over.w P
  have hQt : QT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hQT]; exact Over.w Q
  let h : pullback (torsion G n).hom (torsion G n).hom ⟶ X' :=
    pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom
  haveI : Etale h := inferInstance
  let pq : Sp K ⟶ pullback (torsion G n).hom (torsion G n).hom := pullback.lift PT QT (hPt.trans hQt.symm)
  haveI : IsDomain ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk (pq x)) :=
    isDomain_stalk_of_etale h (pq x)
  obtain ⟨Ω, _, _, y, hy, -⟩ := GlobalTheory.T.exists_dominant_geometricGenericPoint_spec_domain ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk (pq x))
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_lift_geometricGenericPoint_stalk_of_flat h (pq x) ℓ Ω y hy
  let WO : Over X' := Over.mk h
  let A' : WO ⟶ torsion G n := Over.homMk (pullback.fst (torsion G n).hom (torsion G n).hom) rfl
  let B' : WO ⟶ torsion G n :=
    Over.homMk (pullback.snd (torsion G n).hom (torsion G n).hom) pullback.condition.symm
  let A : WO ⟶ G := A' ≫ torsion.ι G n
  let B : WO ⟶ G := B' ≫ torsion.ι G n
  have hs : (A * B) ≫ mulN G n = 1 := by
    letI : CommGroup (WO ⟶ G) := Hom.commGroup
    rw [GlobalTheory.GrpTangent.comp_mulN, mul_pow, ← GlobalTheory.GrpTangent.comp_mulN, ← GlobalTheory.GrpTangent.comp_mulN,
      comp_torsion_ι_mulN, comp_torsion_ι_mulN, _root_.one_mul]
  obtain ⟨sT, hsT⟩ := exists_lift_torsion n (A * B) hs
  let g : Over.mk t ⟶ WO := Over.homMk pq (by
    show pq ≫ pullback.fst _ _ ≫ _ = t
    rw [pullback.lift_fst_assoc, hPt])
  have hgA : g ≫ A = P := by
    ext1
    simp only [A, A', g, pq, Over.comp_left, Over.homMk_left, pullback.lift_fst_assoc, hPT]
  have hgB : g ≫ B = Q := by
    ext1
    simp only [B, B', g, pq, Over.comp_left, Over.homMk_left, pullback.lift_snd_assoc, hQT]
  have hRT' : pq ≫ sT.left = RT := by
    haveI := mono_torsion_ι G n
    rw [← cancel_mono (torsion.ι G n).left, Category.assoc, ← Over.comp_left, hsT, hRT, ← hgA, ← hgB,
      ← MonObj.comp_mul]
    rfl
  have e1 : (pullback.fst (torsion G n).hom (torsion G n).hom) (pq x) = PT x := by
    show (pq ≫ pullback.fst _ _) x = _
    rw [pullback.lift_fst]
  have e2 : (pullback.snd (torsion G n).hom (torsion G n).hom) (pq x) = QT x := by
    show (pq ≫ pullback.snd _ _) x = _
    rw [pullback.lift_snd]
  have e3 : sT.left (pq x) = RT x := by
    show (pq ≫ sT.left) x = _
    rw [hRT']
  rw [← e1] at hcP
  rw [← e2] at hcQ
  rw [← e3] at hcR
  have hP' := valAt_comp_stalk G n ℓ w _ (pq x) cP hcP Ω y z hz
  have hQ' := valAt_comp_stalk G n ℓ w _ (pq x) cQ hcQ Ω y z (by rw [← pullback.condition]; exact hz)
  have hR' := valAt_comp_stalk G n ℓ w sT.left (pq x) cR hcR Ω y z (by rw [Over.w sT]; exact hz)
  let k : Over.mk (z ≫ ℓ) ⟶ WO :=
    Over.homMk (y ≫ (pullback (torsion G n).hom (torsion G n).hom).fromSpecStalk (pq x))
      (by simpa [WO] using hz)
  have hC := hadd Ω z cP cQ (k ≫ A) (k ≫ B) (Over.homMk (z ≫ w (cP + cQ)) (by simp [hw]))
    (by simpa [k, A, A'] using hP') (by simpa [k, B, B'] using hQ') rfl
  rw [← MonObj.comp_mul, ← hsT] at hC
  have hC' := congrArg (fun u => u.left) hC
  simp only [Over.homMk_left, Over.comp_left, k] at hC'
  refine hun Ω z cR (cP + cQ) ?_
  rw [← hR']
  simp only [Category.assoc] at hC'
  exact hC'.symm

end GlobalTheory.TorsSpec
