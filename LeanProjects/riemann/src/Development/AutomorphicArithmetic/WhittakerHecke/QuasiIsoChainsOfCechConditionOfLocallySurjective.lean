import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoChainsCechOfIsLocallySurjective

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

private abbrev vtx {X : Spc} {Q : PSh} (p : X ⟶ disc.obj Q) : X.obj (op ⦋0⦌) ⟶ Q :=
  p.app (op ⦋0⦌)

private lemma vtx_cond {X : Spc} {Q : PSh} (p : X ⟶ disc.obj Q) (n : SimplexCategoryᵒᵖ)
    (i : Fin (n.unop.len + 1)) :
    X.map (SimplexCategory.const ⦋0⦌ n.unop i).op ≫ vtx p = p.app n := by
  have h := p.naturality (SimplexCategory.const ⦋0⦌ n.unop i).op
  simpa using h

private noncomputable def nerveMap {X : Spc} {Q : PSh} (p : X ⟶ disc.obj Q) :
    X ⟶ (Arrow.mk (vtx p)).cechNerve where
  app n := WidePullback.lift (p.app n) (fun i => X.map (SimplexCategory.const ⦋0⦌ n.unop i).op)
    (fun i => vtx_cond p n i)
  naturality n n' g := by
    apply WidePullback.hom_ext
    · intro i
      erw [Category.assoc, Category.assoc, WidePullback.lift_π]
      simp only [Arrow.cechNerve]
      erw [WidePullback.lift_π, WidePullback.lift_π]
      rw [← X.map_comp]
      congr 1
    · erw [Category.assoc, Category.assoc, WidePullback.lift_base]
      simp only [Arrow.cechNerve]
      erw [WidePullback.lift_base, WidePullback.lift_base]
      simpa using p.naturality g

private theorem isIso_nerveMap_of_existsUnique_vertices {X : Spc} {Q : PSh} (p : X ⟶ disc.obj Q)
    (h : ∀ (n : ℕ) (U : Scheme.{0}) (t : Fin (n + 1) → Sx X 0 U),
      (∀ i j, (p.app (op ⦋0⦌)).app (op U) (t i) = (p.app (op ⦋0⦌)).app (op U) (t j)) →
      ∃! z : Sx X n U, ∀ i, Sx.along z (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) = t i) :
    IsIso (_root_.nerveMap p) := by
  have hπ : ∀ (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}) (x : (X.obj n).obj (op U)) (i : Fin (n.unop.len + 1)),
      (WidePullback.π (fun _ : Fin (n.unop.len + 1) => vtx p) i).app (op U) (((_root_.nerveMap p).app n).app (op U) x)
        = (X.map (SimplexCategory.const ⦋0⦌ n.unop i).op).app (op U) x := by
    intro n U x i
    have e : (_root_.nerveMap p).app n ≫ WidePullback.π (fun _ : Fin (n.unop.len + 1) => vtx p) i = X.map (SimplexCategory.const ⦋0⦌ n.unop i).op := by
      simp only [_root_.nerveMap]
      erw [WidePullback.lift_π]
    have e2 := NatTrans.congr_app e (op U)
    rw [NatTrans.comp_app] at e2
    simpa using ConcreteCategory.congr_hom e2 x
  have hb : ∀ (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}) (x : (X.obj n).obj (op U)),
      (WidePullback.base (fun _ : Fin (n.unop.len + 1) => vtx p)).app (op U) (((_root_.nerveMap p).app n).app (op U) x)
        = (p.app n).app (op U) x := by
    intro n U x
    have e : (_root_.nerveMap p).app n ≫ WidePullback.base (fun _ : Fin (n.unop.len + 1) => vtx p) = p.app n := by
      simp only [_root_.nerveMap]
      erw [WidePullback.lift_base]
    have e2 := NatTrans.congr_app e (op U)
    rw [NatTrans.comp_app] at e2
    simpa using ConcreteCategory.congr_hom e2 x
  have hv : ∀ (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}) (x : (X.obj n).obj (op U)) (i : Fin (n.unop.len + 1)),
      (p.app (op ⦋0⦌)).app (op U) ((X.map (SimplexCategory.const ⦋0⦌ n.unop i).op).app (op U) x)
        = (p.app n).app (op U) x := by
    intro n U x i
    have e2 := NatTrans.congr_app (vtx_cond p n i) (op U)
    rw [NatTrans.comp_app] at e2
    have e3 := ConcreteCategory.congr_hom e2 x
    simp only [ConcreteCategory.comp_apply] at e3
    exact e3
  have hbπ : ∀ (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}) (w : ((Arrow.mk (vtx p)).cechNerve.obj n).obj (op U)) (i : Fin (n.unop.len + 1)),
      (p.app (op ⦋0⦌)).app (op U) ((WidePullback.π (fun _ : Fin (n.unop.len + 1) => vtx p) i).app (op U) w)
        = (WidePullback.base (fun _ : Fin (n.unop.len + 1) => vtx p)).app (op U) w := by
    intro n U w i
    have e2 := NatTrans.congr_app (WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => vtx p) i) (op U)
    rw [NatTrans.comp_app] at e2
    simpa using ConcreteCategory.congr_hom e2 w
  have key : ∀ n, IsIso ((_root_.nerveMap p).app n) := by
    intro n
    have hU : ∀ U : Schemeᵒᵖ, IsIso (((_root_.nerveMap p).app n).app U) := by
      intro U
      obtain ⟨U⟩ := U
      rw [isIso_iff_bijective]
      constructor
      · intro x y hxy
        let t : Fin (n.unop.len + 1) → Sx X 0 U := fun i => (X.map (SimplexCategory.const ⦋0⦌ n.unop i).op).app (op U) x
        have ht : ∀ i j, (p.app (op ⦋0⦌)).app (op U) (t i) = (p.app (op ⦋0⦌)).app (op U) (t j) := by
          intro i j
          exact (hv n U x i).trans (hv n U x j).symm
        obtain ⟨z, -, huniq⟩ := h n.unop.len U t ht
        have hx : ∀ i, Sx.along (E := X) (N := n.unop.len) x (SimplexCategory.const ⦋0⦌ ⦋n.unop.len⦌ i) = t i := fun i => rfl
        have hy : ∀ i, Sx.along (E := X) (N := n.unop.len) y (SimplexCategory.const ⦋0⦌ ⦋n.unop.len⦌ i) = t i := by
          intro i
          have a := hπ n U x i
          have b := hπ n U y i
          rw [hxy] at a
          exact b.symm.trans a
        exact (huniq x hx).trans (huniq y hy).symm
      · intro w
        let t : Fin (n.unop.len + 1) → Sx X 0 U := fun i => (WidePullback.π (fun _ : Fin (n.unop.len + 1) => vtx p) i).app (op U) w
        have ht : ∀ i j, (p.app (op ⦋0⦌)).app (op U) (t i) = (p.app (op ⦋0⦌)).app (op U) (t j) := by
          intro i j
          exact (hbπ n U w i).trans (hbπ n U w j).symm
        obtain ⟨z, hz, -⟩ := h n.unop.len U t ht
        refine ⟨z, ?_⟩
        apply yonedaEquiv.symm.injective
        apply WidePullback.hom_ext
        · intro i
          apply yonedaEquiv.injective
          simp only [yonedaEquiv_comp]
          erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          exact (hπ n U z i).trans (hz i)
        · apply yonedaEquiv.injective
          simp only [yonedaEquiv_comp]
          erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          exact (hb n U z).trans ((hv n U z 0).symm.trans ((congrArg (fun a => (p.app (op ⦋0⦌)).app (op U) a) (hz 0)).trans (hbπ n U w 0)))
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

theorem UpperTheory.quasiIso_chains_of_cech_condition_of_locallySurjective :
    ∀ (R : Type) [CommRing R] (X : Spc) (Q : PSh) (p : X ⟶ disc.obj Q),
        (∀ (n : ℕ) (U : Scheme.{0}) (t : Fin (n + 1) → Sx X 0 U),
          (∀ i j, (p.app (op ⦋0⦌)).app (op U) (t i) = (p.app (op ⦋0⦌)).app (op U) (t j)) →
          ∃! z : Sx X n U, ∀ i, Sx.along z (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) = t i) →
        Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (p.app (op ⦋0⦌)) →
        QuasiIso ((chains R).map p) := by
  intro R _ X Q p h hs
  have e : _root_.nerveMap p ≫ (Arrow.mk (vtx p)).augmentedCechNerve.hom = p := by
    ext n : 2
    simp [_root_.nerveMap, Arrow.augmentedCechNerve]
  haveI := isIso_nerveMap_of_existsUnique_vertices p h
  haveI := quasiIso_chains_cech_of_isLocallySurjective R (X _⦋0⦌) Q (vtx p) hs
  rw [← e, Functor.map_comp]
  infer_instance
