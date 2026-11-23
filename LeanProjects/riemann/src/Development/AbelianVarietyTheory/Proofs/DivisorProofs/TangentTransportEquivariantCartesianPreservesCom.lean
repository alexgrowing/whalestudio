import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrvEqSelf
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvTrans

theorem epsMul_comp_algebraMap {R : Type} [CommRing R] (c : R) :
    spMap (epsMul c) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) := by
  simp only [spMap, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun a => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X Y : Scheme.{0}} {t : SAB H Y} {p : X ⟶ Y} {G' : Over X} [GrpObj G'] {ψ : G'.left ⟶ t.G.left}

theorem trv_epsMul (hψ : IsPullback ψ G'.hom t.G.hom p) (g : G'.left ⟶ G'.left) {R : Type} [CommRing R]
    (q : Sp R ⟶ X) (c : R) {v : Sp (DualNumber R) ⟶ t.G.left}
    (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g q (spMap (epsMul c) ≫ v) = spMap (epsMul c) ≫ trv hψ g q v := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ g q w hw hw', trv_eq hψ g q (spMap (epsMul c) ≫ w) (by rw [Category.assoc, hw])
    (by rw [Category.assoc, hw', ← Category.assoc, epsMul_comp_algebraMap])]
  simp only [Category.assoc]

end GlobalTheory.EqvTrans

open MonObj GlobalTheory.EqvTrans in

theorem GlobalTheory.EqvTrans.trv_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X Y : Scheme.{0}} (t : SAB H Y) (p : X ⟶ Y) (G' : Over X) [GrpObj G'] (ψ : G'.left ⟶ t.G.left) (b : X ⟶ X) (g : G'.left ⟶ G'.left) (hG : IsGrpPullback G' t.G p ψ), IsGrpPullback G' G' b g → ∀ {R : Type} [CommRing R] (q : Sp R ⟶ X) {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) (a : Fin n → R) (w : Sp (DualNumber R) ⟶ t.G.left), (∀ i, IsTanAtG t (q ≫ p) (v i)) → IsTanAtG t (q ≫ p) w → IsCombAtG t (q ≫ p) v a w → IsCombAtG t ((q ≫ b) ≫ p) (fun i => GlobalTheory.EqvTrans.trv hG.1 g q (v i)) a (GlobalTheory.EqvTrans.trv hG.1 g q w) := by
  intro E _ _ _ H X Y t p G' _ ψ b g hG hg R _ q n v a w hv _ hc
  obtain ⟨u, hu, hw⟩ := hc

  let T : Over X := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ q)
  let e1 : Over.mk (T.hom ≫ p) ⟶ tEpsG (q ≫ p) := Over.homMk (𝟙 _) (by simp [T])
  let T' : Over X := Over.mk (T.hom ≫ b)
  let e2 : Over.mk (T'.hom ≫ p) ⟶ tEpsG ((q ≫ b) ≫ p) := Over.homMk (𝟙 _) (by simp [T, T'])
  have hov : ∀ x : tEpsG (q ≫ p) ⟶ t.G,
      x.left ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p := fun x => by
    simpa using Over.w x

  let L : (tEpsG (q ≫ p) ⟶ t.G) → (T ⟶ G') := fun x =>
    Over.homMk (hG.1.lift x.left T.hom (by rw [hov x]; simp [T])) (hG.1.lift_snd _ _ _)
  have hL : ∀ x, (L x).left ≫ ψ = x.left := fun x => hG.1.lift_fst _ _ _
  have hLw : ∀ x, (L x).left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q := fun x => Over.w (L x)
  have hgw : g ≫ G'.hom = G'.hom ≫ b := hg.1.w

  let Φ : (tEpsG (q ≫ p) ⟶ t.G) → (tEpsG ((q ≫ b) ≫ p) ⟶ t.G) := fun x =>
    Over.homMk (trv hG.1 g q x.left) (by
      have := trv_over hG.1 g hgw q (hov x)
      simpa using this)
  have hΦ : ∀ x, (Φ x).left = (L x).left ≫ g ≫ ψ := fun x => trv_eq hG.1 g q (L x).left (hL x) (hLw x)

  let M : (tEpsG (q ≫ p) ⟶ t.G) → (T' ⟶ G') := fun x =>
    Over.homMk ((L x).left ≫ g) (by
      show ((L x).left ≫ g) ≫ G'.hom = T.hom ≫ b
      rw [Category.assoc, hgw, ← Category.assoc, Over.w])
  have hmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y => by
    have h1 : ((e1 ≫ x) * (e1 ≫ y)).left = (L x * L y).left ≫ ψ :=
      hG.2 T (L x) (L y) (e1 ≫ x) (e1 ≫ y) (by simp [e1, hL]) (by simp [e1, hL])
    rw [← MonObj.comp_mul] at h1
    have h1' : (L x * L y).left ≫ ψ = (x * y).left := by rw [← h1]; simp [e1]
    have h2 : (M x * M y).left = (L x * L y).left ≫ g :=
      hg.2 T (L x) (L y) (M x) (M y) rfl rfl
    have h3 : ((e2 ≫ Φ x) * (e2 ≫ Φ y)).left = (M x * M y).left ≫ ψ :=
      hG.2 T' (M x) (M y) (e2 ≫ Φ x) (e2 ≫ Φ y) (by simp [e2, hΦ, M]) (by simp [e2, hΦ, M])
    rw [← MonObj.comp_mul, h2] at h3
    apply Over.OverMorphism.ext
    have h4 : (Φ (x * y)).left = (L x * L y).left ≫ g ≫ ψ :=
      trv_eq hG.1 g q (L x * L y).left h1' (Over.w (L x * L y))
    rw [h4, ← Category.assoc, ← h3]
    simp [e2]
  let Φm : (tEpsG (q ≫ p) ⟶ t.G) →* (tEpsG ((q ≫ b) ≫ p) ⟶ t.G) := MonoidHom.mk' Φ hmul
  refine ⟨fun i => Φ (u i), fun i => ?_, ?_⟩
  · show trv hG.1 g q (u i).left = _
    rw [hu i, trv_epsMul hG.1 g q (a i) (hv i).1]
  · have : (List.ofFn fun i => Φ (u i)) = (List.ofFn u).map Φm := by
      rw [List.map_ofFn]; rfl
    rw [this, ← map_list_prod]
    show trv hG.1 g q _ = _
    rw [hw]
