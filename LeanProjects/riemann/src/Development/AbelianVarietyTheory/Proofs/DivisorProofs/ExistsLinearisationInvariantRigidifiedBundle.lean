import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalizedBoth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

noncomputable section

namespace GlobalTheory.MumLin

variable {X Y Z : Scheme.{0}} {L : LB X}

theorem exists_gen_diff (hL : L.IsLB) (σ : X ⟶ X) (h : LBIso L (L.pull σ)) :
    ∃ w : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, σ] ![1, -1]), w.IsGen := by
  have h1 := (GlobalTheory.TripleCompare.lbIso_iff_pull_id L (L.pull σ)).1 h
  obtain ⟨t, ht⟩ := (GlobalTheory.TripleCompare.lbIso_iff_gen _ _ _ _).1 h1
  obtain ⟨w, hw, -⟩ := DVR.gen_transport (φ' := ![𝟙 X, σ]) (ε' := ![1, -1]) hL (by
    rw [DVR.sameSum_iff_fsum, DVR.fsum_sumElim]
    simp [DVR.fsum, Fin.sum_univ_two]) t ht
  exact ⟨w, hw⟩

theorem corr_of_pull_section (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen)
    (hs : DVR.fsum φ ε = DVR.fsum φ' ε') (p : Y ⟶ Z) (z : Z ⟶ Y) (hzp : z ≫ p = 𝟙 Z)
    (hp : Function.Surjective p.appTop.hom)
    (H : LB.Gen.Corr L _ ε _ ε' (LB.pullGen L φ ε t z) (LB.pullGen L φ' ε' t' z)) :
    LB.Gen.Corr L φ ε φ' ε' t t' := by
  have hq : (LB.mulGen L _ _ _ _ t (LB.invGen L φ' ε' t')).IsGen :=
    DVR.mulGen_isGen_of_isGen t ht _ (DVR.invGen_isGen_of_isGen t' ht')
  have h0 : DVR.fsum (fun k => 𝟙 Y ≫ Sum.elim φ φ' k) (Sum.elim ε fun k => -ε' k) = 0 := by
    rw [DVR.fsum_comp, DVR.fsum_sumElim, DVR.fsum_neg, hs, add_neg_cancel, Finsupp.mapDomain_zero]
  obtain ⟨c, hc⟩ := DVR.exists_value hL _ _ _ hq (𝟙 Y) h0
  have key : ∀ (W : Scheme.{0}) (r : W ⟶ Y) (w : W) (J : (W ⟶ X) → L.ι), Good L w J →
      val (LB.mulGen L _ _ _ _ t (LB.invGen L φ' ε' t')) r w J = gm r w ⊤ c := by
    intro W r w J hJ
    have e1 := val_pull hJ (LB.mulGen L _ _ _ _ t (LB.invGen L φ' ε' t')) (𝟙 Y) r
    rw [Category.comp_id] at e1
    rw [← e1, val_of _ r w J (fun k => J (r ≫ 𝟙 Y ≫ Sum.elim φ φ' k)) (fun _ => rfl),
      ← hc _ (fun k₁ k₂ e => by simp only [e])]
    exact gm_res r w le_top (hJ.mem _ r) c
  have hz1 : ∀ w : Z, gm z w ⊤ c = 1 := by
    intro w
    obtain ⟨J, hJ, -⟩ := exists_good (Z := Z) L hL w (K := PEmpty) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have e1 := val_pull hJ t z (𝟙 Z)
    have e2 := val_pull hJ t' z (𝟙 Z)
    rw [Category.id_comp] at e1 e2
    rw [← key Z z w J hJ, val_mul hJ, val_inv, ← e1, ← e2, val_corr hJ H, mul_inv_cancel]
  obtain ⟨d, hd⟩ := hp c.val
  have d1 : d = 1 := fn_ext fun w _ => by
    have e' : gm (𝟙 Z ≫ z) w ⊤ c = 1 := by rw [Category.id_comp]; exact hz1 w
    have e'' := (gs_pull (𝟙 Z ≫ z) p w ⊤ trivial d).symm.trans ((congrArg (gs (𝟙 Z ≫ z) w ⊤) hd).trans
      ((gs_unit _ w ⊤ trivial c).trans (congrArg Units.val e')))
    rw [Category.assoc, hzp, Category.comp_id] at e''
    rw [e'', gs_eq _ w ⊤ trivial, map_one, map_one, Units.val_one]
  have c1 : c = 1 := Units.ext (by rw [← hd, d1, map_one]; rfl)
  refine corr_of_val hL fun y J hJ => ?_
  have e := key Y (𝟙 Y) y J hJ
  rw [c1, map_one, val_mul hJ, val_inv, mul_inv_eq_one] at e
  exact e

theorem exists_linearisation : ∀ (T X : Scheme.{0}) (π : X ⟶ T) (e : T ⟶ X), e ≫ π = 𝟙 T → Function.Surjective π.appTop.hom → ∀ (L : LB X), L.IsLB → (∃ r : LB.Gen (L.pull e), r.IsGen) → ∀ (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (θ : Ga → (T ⟶ T)), (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a c, θ (a * c) = θ a ≫ θ c) → (∀ a, e ≫ ρ a = θ a ≫ e) → (∀ a, LBIso L (L.pull (ρ a))) → ∃ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) ∧ ∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a))) := by
  intro T X π e he hπ L hL ⟨r, hr⟩ Ga _ ρ θ hρ hθ heρ hiso
  have hex : ∀ a, ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), u.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u e)
        (LB.mulGen L _ _ _ _ r (LB.invGen L _ _ (LB.pullGen L _ _ r (θ a)))) := by
    intro a
    obtain ⟨w, hw⟩ := exists_gen_diff hL (ρ a) (hiso a)
    refine DVR.exists_normalized_to hL _ _ w hw π e he _ _ _
      (DVR.mulGen_isGen_of_isGen r hr _ (DVR.invGen_isGen_of_isGen _ (DVR.pullGen_isGen_of_isGen _ _ r hr _))) ?_
    rw [DVR.fsum_sumElim]
    simp [DVR.fsum, Fin.sum_univ_two, heρ a]
  choose u hu hue using hex
  refine ⟨u, hu, fun a c => ?_⟩
  refine corr_of_pull_section hL (hu _) (DVR.mulGen_isGen_of_isGen _ (hu a) _ (DVR.pullGen_isGen_of_isGen _ _ _ (hu c) _))
    ?_ π e he hπ ?_
  · rw [DVR.fsum_sumElim]
    simp only [DVR.fsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Category.comp_id, hρ]
    rw [add_assoc, ← add_assoc (Finsupp.single (ρ a) (-1 : ℤ)), ← Finsupp.single_add, neg_add_cancel, Finsupp.single_zero,
      zero_add]
  · refine corr_of_val hL fun y J hJ => ?_
    have v1 := val_corr hJ (hue (a * c)) (𝟙 T)
    have v2 := val_corr hJ (hue a) (𝟙 T)
    have v3 := val_corr hJ (hue c) (θ a)
    simp only [val_mul hJ, val_inv, val_pull hJ, Category.id_comp, Category.assoc, hθ] at v1 v2 v3 ⊢
    rw [heρ a, v1, v2, v3, _root_.mul_assoc, inv_mul_cancel_left]

end GlobalTheory.MumLin
