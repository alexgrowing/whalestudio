import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection

noncomputable section

namespace GlobalTheory.RigIso

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem gm_eq_of_eq_along_section {Y Z T : Scheme.{0}} {N : LB Y} (hN : ∀ y : Y, ∃ i, y ∈ N.U i)
    (q : Z ⟶ Y) (p : Z ⟶ T) (e : T ⟶ Z) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {t₁ t₂ : LB.Gen N} (h₁ : t₁.IsGen) (h₂ : t₂.IsGen)
    (h : ∀ (s : T) (i : N.ι), (e ≫ q) s ∈ N.U i → gm (e ≫ q) s (N.U i) (t₁.s i) = gm (e ≫ q) s (N.U i) (t₂.s i))
    {W : Scheme.{0}} (r : W ⟶ Z) (z : W) (i : N.ι) (hi : (r ≫ q) z ∈ N.U i) :
    gm (r ≫ q) z (N.U i) (t₁.s i) = gm (r ≫ q) z (N.U i) (t₂.s i) := by
  have tr : ∀ {t : LB.Gen N}, t.IsGen → ∀ (i j : N.ι) (x : Y), x ∈ N.U i ⊓ N.U j →
      gm (𝟙 Y) x (N.U i) (t.s i) = gm (𝟙 Y) x (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Y) x (N.U j) (t.s j) := by
    intro t ht i j x hx
    have := congrArg (gm (𝟙 Y) x (N.U i ⊓ N.U j)) (ht i j)
    rwa [map_mul, gm_res _ x _ hx, gm_res _ x _ hx] at this
  obtain ⟨u, hu⟩ := glue_unit ⊤ N.U (fun _ => le_top) (fun y _ => Opens.mem_iSup.2 (hN y))
    (fun i => t₁.s i * (t₂.s i)⁻¹) (fun i j x hx => by
      rw [map_mul, map_mul, map_inv, map_inv, tr h₁ i j x hx, tr h₂ i j x hx, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul])
  obtain ⟨a, ha⟩ := hp (q.appTop.hom u.val)
  have key : ∀ (W : Scheme.{0}) (r : W ⟶ Z) (z : W) (i : N.ι), (r ≫ q) z ∈ N.U i →
      (gm (r ≫ q) z (N.U i) (t₁.s i) * (gm (r ≫ q) z (N.U i) (t₂.s i))⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro W r z i hi
    rw [← map_inv, ← map_mul, ← hu i, gm_res (r ≫ q) z _ hi]
    exact (gs_unit (r ≫ q) z ⊤ trivial _).symm.trans ((gs_pull r q z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  have a1 : a = 1 := fn_ext fun y _ => by
    obtain ⟨i, hi⟩ := hN ((e ≫ q) y)
    have := key _ e y i hi
    rw [h y i hi, mul_inv_cancel, he] at this
    rw [← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
  have := key _ r z i hi
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

theorem valR_eq_of_gs {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) (h : ∀ z, gs x z U a = gs x z U b) : valR x U a = valR x U b := by
  rw [valR, valR, dif_pos hU, dif_pos hU]
  congr 1
  have : (x.app U).hom a = (x.app U).hom b := fn_ext fun z hz => by
    rw [gs_pull (𝟙 _) x z U hz, gs_pull (𝟙 _) x z U hz, Category.id_comp]
    exact h z
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, this]

theorem isAbelianScheme_fibre {S T : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (y : T ⟶ S)
    (hp : IsProper (pullback.snd G.hom y)) : IsAbelianScheme ((Over.pullback y).obj G) := by
  haveI := hG.comm
  haveI := hG.smooth
  haveI := hG.geomConnected
  exact ⟨inferInstance, (inferInstance : Smooth (pullback.snd G.hom y)), hp,
    (inferInstance : GeometricallyConnected (pullback.snd G.hom y))⟩

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f), (∃ w, IsRigIso m.cm t'.PP t.PP w) ∧ ∀ (w w' : LB.Iso t'.PP.L (t.PP.L.pull m.φ)), IsRigIso m.cm t'.PP t.PP w → IsRigIso m.cm t'.PP t.PP w' → ∀ (F : Type) [Field F] (y : Sp F ⟶ S') (x : Over.mk y ⟶ t'.G), IsProper (pullback.snd t'.G.hom y) → ∀ j j', ⊤ ≤ x.left ⁻¹ᵁ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') → valR x.left _ (w.s (fun _ => j, j')).val = valR x.left _ (w'.s (fun _ => j, j')).val := by
  intro hL _ E _ _ _ H _ S S' t t' f m
  refine ⟨m.lin.imp fun w hw => ⟨hw.1, hw.2.1⟩, ?_⟩
  intro w w' hw hw' F _ y x hp j j' hU
  have hs : Function.Surjective (pullback.snd t'.G.hom y).appTop.hom :=
    (hL.globalFns _ _ (isAbelianScheme_fibre t'.G t'.semi y hp)).2
  have he : eSec t'.G ≫ t'.G.hom = 𝟙 S' := Over.w η[t'.G]
  have hx : x.left ≫ t'.G.hom = 𝟙 _ ≫ y := (Over.w x).trans (Category.id_comp y).symm
  have he' : (y ≫ eSec t'.G) ≫ t'.G.hom = 𝟙 _ ≫ y := by
    rw [Category.id_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) he).trans (Category.comp_id y))
  refine valR_eq_of_gs _ _ hU _ _ fun z => ?_
  have hz : x.left z ∈ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') :=
    hU (show z ∈ (⊤ : (Sp F).Opens) from trivial)
  rw [gs_unit _ _ _ hz, gs_unit _ _ _ hz]
  congr 1
  have hcov : ∀ a : t'.G.left, ∃ i, a ∈ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U i := fun a => by
    obtain ⟨i, hi⟩ := exists_chart t'.PP.isLB a
    obtain ⟨k, hk⟩ := exists_chart t.PP.isLB (m.φ a)
    exact ⟨(fun _ => k, i), mem_pull.2 hk, hi⟩
  have key := gm_eq_of_eq_along_section hcov (pullback.fst t'.G.hom y) (pullback.snd t'.G.hom y)
    (pullback.lift (y ≫ eSec t'.G) (𝟙 _) he') (pullback.lift_snd _ _ _) hs hw.1 hw'.1 (by
      rw [pullback.lift_fst]
      rintro s ⟨k, i⟩ ⟨hk, hi⟩
      have k₁ := gm_maps_pt hw.2 y s k i hk hi
      have k₂ := gm_maps_pt hw'.2 y s k i hk hi
      exact mul_right_cancel (k₁.symm.trans k₂))
    (pullback.lift x.left (𝟙 _) hx) z (fun _ => j, j')
  rw [pullback.lift_fst] at key
  exact key hz

end GlobalTheory.RigIso
