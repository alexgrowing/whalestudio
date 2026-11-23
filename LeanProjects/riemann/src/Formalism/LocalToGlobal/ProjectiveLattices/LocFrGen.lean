import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

set_option maxHeartbeats 400000 in

theorem locFrGen_of {L : Type} [CommRing L] (x : Sp L ⟶ Xo.X) {t' : SAB H (Sp L)} (m1 : SABMap t' Xo.univ.t x)
    (σ' : LB.Sec t'.PP.L) (hgen : ∀ s' : LB.Sec t'.PP.L, ∃! a : L, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i) :
    ∃ s : LB.Sec (PPx x), ∀ s'' : LB.Sec (PPx x), ∃! a : L, ∀ i, s''.f i = scal x a i * s.f i := by
  obtain ⟨w, hwG, -, -⟩ := m1.lin
  have hw : PGen w := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w).mp hwG
  have hL := Xo.univ.t.PP.isLB
  have hL' := t'.PP.isLB
  obtain ⟨s0, hs0⟩ := thf_secUp hw hL hL' σ'
  have P' := m1.cart.1
  obtain ⟨h, hF, hS⟩ : ∃ h : Gx x ⟶ t'.G.left, h ≫ m1.cm.F = (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left ∧ h ≫ t'.G.hom = (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left :=
    ⟨P'.lift _ _ ((Over.w (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G)).trans
      (Over.w (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G)).symm),
      P'.lift_fst _ _ _, P'.lift_snd _ _ _⟩
  obtain ⟨k, hk1, hk2⟩ : ∃ k : t'.G.left ⟶ Gx x, k ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom ∧ k ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m1.cm.F :=
    ⟨(CartesianMonoidalCategory.lift
        (Over.homMk t'.G.hom P'.w.symm : Over.mk (m1.cm.F ≫ Xo.univ.t.G.hom) ⟶ Over.mk x)
        (Over.homMk m1.cm.F rfl : Over.mk (m1.cm.F ≫ Xo.univ.t.G.hom) ⟶ Xo.univ.t.G)).left,
      congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst _ _),
      congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd _ _)⟩
  have gext : ∀ u v : Gx x ⟶ Gx x, u ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = v ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left → u ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = v ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left → u = v := by
    intro u v e1 e2
    have e3 : (Over.homMk u rfl : Over.mk (u ≫ (Over.mk x ⊗ Xo.univ.t.G).hom) ⟶ Over.mk x ⊗ Xo.univ.t.G) =
        Over.homMk (U := Over.mk (u ≫ (Over.mk x ⊗ Xo.univ.t.G).hom)) (V := Over.mk x ⊗ Xo.univ.t.G) v (by
          show v ≫ _ = u ≫ _
          rw [← Over.w (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G), ← Category.assoc,
            ← Category.assoc, e1]) := by
      apply CartesianMonoidalCategory.hom_ext
      · first | exact Over.OverMorphism.ext e1 | exact Over.Hom.ext e1 | (ext; exact e1)
      · first | exact Over.OverMorphism.ext e2 | exact Over.Hom.ext e2 | (ext; exact e2)
    exact congrArg Over.Hom.left e3
  have hhk : h ≫ k = 𝟙 _ := gext _ _ (by rw [Category.assoc, hk1, hS, Category.id_comp])
    (by rw [Category.assoc, hk2, hF, Category.id_comp])
  have hkh : k ≫ h = 𝟙 _ := P'.hom_ext (by rw [Category.assoc, hF, hk2, Category.id_comp])
    (by rw [Category.assoc, hS, hk1, Category.id_comp])
  have hle : ∀ j, m1.cm.F ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ k ⁻¹ᵁ (PPx x).U (fun _ => j) := fun j z hz =>
    Set.mem_iInter.mpr fun _ => Set.mem_iInter.mp
      (chart_le_pullback_open Xo.univ.t.PP.L k hk2 (fun _ => j) (Set.mem_iInter.mpr fun _ => hz)) PUnit.unit
  have hpre : ∀ (z : t'.G.left) j, z ∈ (Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j) →
      z ∈ m1.cm.F ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z j hz => Set.mem_iInter.mp hz PUnit.unit
  refine ⟨thfPull1 Xo.univ.t.PP.L h hF s0, fun s'' => ?_⟩
  obtain ⟨σ'', hσ''⟩ := sec_down hw hL hL'
    (fun j => (k.appLE ((PPx x).U (fun _ => j)) (m1.cm.F ⁻¹ᵁ Xo.univ.t.PP.L.U j) (hle j)).hom
      (s''.f (fun _ => j))) (by
      intro y j j' hj hj'
      try beta_reduce
      have h1 : k y ∈ (PPx x).U (fun _ => j) := hle j hj
      have h2 : k y ∈ (PPx x).U (fun _ => j') := hle j' hj'
      have hg : gm (𝟙 _ ≫ k) y ((PPx x).U (fun _ => j) ⊓ (PPx x).U (fun _ => j'))
          ((PPx x).g (fun _ => j) (fun _ => j')) =
          gm m1.cm.F y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j') :=
        (gm_linComb Xo.univ.t.PP.L (fun _ : Fin 1 => (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left) (fun _ => 1) (𝟙 _ ≫ k) y
          (fun _ => j) (fun _ => j') h1 h2).trans (by rw [Fin.prod_univ_one, zpow_one, Category.id_comp, hk2])
      rw [gs_appLE k _ _ (hle j) (𝟙 _) y hj, gs_appLE k _ _ (hle j') (𝟙 _) y hj',
        gs_compat s'' (𝟙 _ ≫ k) y h1 h2, hg])
  obtain ⟨a, ha, hau⟩ := hgen σ''
  refine ⟨a, fun J => ?_, fun b hb => hau b fun i => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, J = fun _ => j := ⟨J 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
    apply fn_ext
    intro y hy
    have hyh : h y ∈ (Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j) :=
      chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j) hy
    obtain ⟨i, hi⟩ : ∃ i, h y ∈ t'.PP.L.U i := TopologicalSpace.Opens.mem_iSup.mp (by
      rw [hL'.cover]
      first | trivial | exact Set.mem_univ _ | simp)
    have e1 := gs_appLE k _ _ (hle j) h y (hpre _ _ hyh) (s''.f (fun _ => j))
    rw [hhk] at e1
    have e2 := hσ'' _ h y j i (hpre _ _ hyh) hi
    have e3 := hs0 _ h y (fun _ => j) i hyh hi
    have e4 : gs (𝟙 _) y ((PPx x).U (fun _ => j)) ((thfPull1 Xo.univ.t.PP.L h hF s0).f (fun _ => j)) =
        gs (𝟙 _ ≫ h) y _ (s0.f (fun _ => j)) := gs_appLE h _ _ _ (𝟙 _) y hy _
    rw [Category.id_comp] at e4
    have e5 : gs (𝟙 _) y ((PPx x).U (fun _ => j)) (scal x a (fun _ => j)) = cst (𝟙 _ ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left) y a :=
      gs_constFn (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U (fun _ => j)) (𝟙 _) y hy a
    rw [gs_mul (𝟙 _) y _ hy, e4, e3, e5, ← e1, e2, ha i, gs_mul h y _ hi, gs_constFn t'.G.hom _ h y hi a,
      hS, Category.id_comp]
    ring
  · apply fn_ext
    intro y' hy'
    obtain ⟨j, hj⟩ : ∃ j, m1.cm.F y' ∈ Xo.univ.t.PP.L.U j := TopologicalSpace.Opens.mem_iSup.mp (by
      rw [hL.cover]
      first | trivial | exact Set.mem_univ _ | simp)
    have hkm : k y' ∈ (PPx x).U (fun _ => j) := hle j hj
    have hmem : y' ∈ (Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j) := Set.mem_iInter.mpr fun _ => hj
    have f1 := hσ'' _ (𝟙 _) y' j i hj hy'
    have f2 := gs_appLE k _ _ (hle j) (𝟙 _) y' hj (s''.f (fun _ => j))
    have f3 : gs (𝟙 _ ≫ k) y' ((PPx x).U (fun _ => j)) (scal x b (fun _ => j)) = cst ((𝟙 _ ≫ k) ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left) y' b :=
      gs_constFn (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U (fun _ => j)) (𝟙 _ ≫ k) y' hkm b
    have f4 : gs (𝟙 _ ≫ k) y' ((PPx x).U (fun _ => j)) ((thfPull1 Xo.univ.t.PP.L h hF s0).f (fun _ => j)) =
        gs ((𝟙 _ ≫ k) ≫ h) y' _ (s0.f (fun _ => j)) := gs_appLE h _ _ _ (𝟙 _ ≫ k) y' hkm _
    rw [Category.assoc, hkh, Category.comp_id] at f4
    have f5 := hs0 _ (𝟙 _) y' (fun _ => j) i hmem hy'
    have f2b : gs (𝟙 _ ≫ k) y' ((PPx x).U (fun _ => j)) (s''.f (fun _ => j)) =
        cst ((𝟙 _ ≫ k) ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left) y' b *
          gs (𝟙 _) y' ((Xo.univ.t.PP.L.pull m1.cm.F).U (fun _ => j)) (s0.f (fun _ => j)) := by
      rw [hb (fun _ => j), gs_mul (𝟙 _ ≫ k) y' _ hkm, f3, f4]
    rw [f5] at f2b
    have f6 := (f1.symm.trans f2).trans f2b
    rw [Category.id_comp, hk1, mul_left_comm] at f6
    rw [gs_mul (𝟙 _) y' _ hy', gs_constFn t'.G.hom _ (𝟙 _) y' hy' b, Category.id_comp]
    exact (Units.mul_right_inj _).mp f6

end Formalism.L2.Pj
