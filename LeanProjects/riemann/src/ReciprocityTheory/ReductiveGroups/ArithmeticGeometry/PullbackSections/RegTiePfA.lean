import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTie
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Calc

variable {X Y Z : Scheme.{0}}

theorem sval_zCast {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ : ℤ} (h : k₁ = k₂)
    (F : LB.Sec (LPow A L k₁ T)) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    sval (zCast A h F) r z J = sval F r z J := by
  subst h
  rfl

def pull1 (L : LB X) (h : Y ⟶ X) (s : LB.Sec L) : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => 1)) :=
  thfPull1 L (F := 𝟙 X) h (Category.comp_id h) (thfPull L (𝟙 X) s)

theorem gs_pull1 (L : LB X) (h : Y ⟶ X) (s : LB.Sec L) (r : Z ⟶ Y) (z : Z) (j : Fin 1 → L.ι)
    (hz : r z ∈ LB.wchart L (fun _ : Fin 1 => h) j) :
    gs r z _ ((pull1 L h s).f j) = gs (r ≫ h) z (L.U (j 0)) (s.f (j 0)) := by
  simp only [pull1, thfPull1, thfPull]
  refine Eq.trans (gs_appLE h _ _ _ r z ?_ _) ?_
  · exact hz
  refine Eq.trans (gs_appLE (𝟙 X) _ _ _ (r ≫ h) z ?_ _) ?_
  · exact chart_le_pullback_open L h (Category.comp_id h) j hz
  rw [Category.comp_id]

def secOne (L : LB X) (s : LB.Sec L) : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)) :=
  pull1 L (𝟙 X) s

theorem plain_le (L : LB X) (i : L.ι) : L.U i ≤ (𝟙 X) ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := by
  intro y hy
  exact Set.mem_iInter.mpr fun _ => hy

def plainOf (L : LB X) (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1))) : LB.Sec L where
  f i := (Scheme.Hom.appLE (𝟙 X) _ _ (plain_le L i)).hom (σ.f (fun _ => i))
  compat i j := fn_ext fun y hy => by
    have m₁ : (𝟙 X ≫ 𝟙 X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := plain_le L i hy.1
    have m₂ : (𝟙 X ≫ 𝟙 X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j) := plain_le L j hy.2
    have g : gm (𝟙 X ≫ 𝟙 X) y _ ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).g (fun _ => i) (fun _ => j)) =
        gm (𝟙 X) y (L.U i ⊓ L.U j) (L.g i j) :=
      (gm_linComb L _ _ (𝟙 X ≫ 𝟙 X) y _ _ m₁ m₂).trans (by simp only [Fin.prod_univ_one, zpow_one, Category.comp_id])
    refine (gs_res _ y _ hy _).trans ((gs_appLE (𝟙 X) _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat σ (𝟙 X ≫ 𝟙 X) y m₁ m₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val g.symm))
        ((gs_res _ y _ hy _).trans (gs_appLE (𝟙 X) _ _ _ (𝟙 _) y hy.2 _)))))))

theorem gs_plainOf (L : LB X) (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1))) (y : X) (i : L.ι)
    (hy : y ∈ L.U i) :
    gs (𝟙 X) y (L.U i) ((plainOf L σ).f i) =
      gs (𝟙 X) y (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i)) (σ.f (fun _ => i)) := by
  simp only [plainOf]
  refine Eq.trans (gs_appLE (𝟙 X) _ _ _ (𝟙 X) y ?_ _) ?_
  · exact hy
  rw [Category.comp_id]

theorem gs_resTop (r : Z ⟶ X) (z : Z) {U : X.Opens} (hz : r z ∈ U) (a : Γ(X, ⊤)) :
    gs r z U (resG X (le_top : U ≤ ⊤) a) = gs r z ⊤ a := by
  exact gs_res r z le_top hz a

theorem secOne_gen {S : Type} [CommRing S] (G : Over (Sp S)) (L : LB G.left) (θ : LB.Sec L)
    (hθ : ∀ σ : LB.Sec L, ∃! a : S, ∀ i, σ.f i = resG G.left le_top ((G.hom).appTop.hom (toΓ S a)) * θ.f i) :
    ∀ σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))),
      ∃! a : S, ∀ i, σ.f i = resG G.left le_top ((G.hom).appTop.hom (toΓ S a)) * (secOne L θ).f i := by
  show ∀ σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)),
    ∃! a : S, ∀ i, σ.f i = resG G.left le_top ((G.hom).appTop.hom (toΓ S a)) * (secOne L θ).f i
  have e3 : ∀ (i : L.ι) (y : G.left)
      (hy : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)).U (fun _ => i)),
      gs (𝟙 G.left) y _ ((secOne L θ).f (fun _ => i)) = gs (𝟙 G.left) y (L.U i) (θ.f i) := by
    intro i y hy
    refine (gs_pull1 L (𝟙 _) θ (𝟙 _) y (fun _ => i) hy).trans ?_
    rw [Category.comp_id]
  intro σ
  obtain ⟨a, ha, huniq⟩ := hθ (plainOf L σ)
  refine ⟨a, ?_, fun b hb => huniq b ?_⟩
  · rintro (j : Fin 1 → L.ι)
    obtain ⟨i, rfl⟩ : ∃ i : L.ι, j = fun _ => i := ⟨j 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
    refine fn_ext fun y hy => ?_
    have hyi : y ∈ L.U i := LB.wchart_le L _ (fun _ : Fin 1 => i) 0 hy
    rw [gs_mul _ y _ hy, gs_resTop _ y hy, e3 i y hy]
    refine (gs_plainOf L σ y i hyi).symm.trans ?_
    rw [ha i, gs_mul _ y _ hyi, gs_resTop _ y hyi]
  · intro i
    refine fn_ext fun y hyi => ?_
    have hy : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)).U (fun _ => i) := plain_le L i hyi
    rw [gs_mul _ y _ hyi, gs_resTop _ y hyi]
    refine (gs_plainOf L σ y i hyi).trans ?_
    show gs (𝟙 G.left) y ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)).U (fun _ => i))
      (σ.f (fun _ => i)) = _
    rw [hb (fun _ => i), gs_mul _ y _ hy, gs_resTop _ y hy, e3 i y hy]

theorem gs_isoMaps {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoMaps w s s') (r : Z ⟶ X)
    (z : Z) (i : M.ι) (k : L.ι) (hi : r z ∈ M.U i) (hk : r z ∈ L.U k) :
    gs r z (M.U i) (s'.f i) = (gv w r z i k).val * gs r z (L.U k) (s.f k) := by
  unfold Formalism.L2.Pj.IsoMaps at h
  have hV : r z ∈ M.U i ⊓ L.U k := ⟨hi, hk⟩
  have h' := congrArg (gs r z (M.U i ⊓ L.U k)) (h i k)
  rw [gs_res r z _ hV, gs_mul _ z _ hV, gs_res r z _ hV] at h'
  rw [h']
  congr 1
  exact gs_unit _ z _ hV _

end Calc

theorem thetaTie : ThetaTieSt := by
  intro E _ _ _ H Dw l Xo c Tc io y I
  let _ := io.toAlgebra
  let A := Xo.univ.t.G
  let θK : LB.Sec (LPow I.t'.G I.t'.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp Tc.Fr)))) :=
    pull1 I.t'.PP.L (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left I.σ
  have gθK : ∀ (Z : Scheme.{0}) (zp : Z ⟶ (𝟙_ (Over (Sp Tc.Fr)) ⊗ I.t'.G).left) (z : Z)
      (J' : (Z ⟶ I.t'.G.left) → I.t'.PP.L.ι), Good I.t'.PP.L z J' →
      sval θK zp z J' = gs (zp ≫ (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left) z
        (I.t'.PP.L.U (J' (zp ≫ (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left)))
        (I.σ.f (J' (zp ≫ (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left))) :=
    fun Z zp z J' hJ' => gs_pull1 I.t'.PP.L _ I.σ zp z _ (hJ'.mem _ zp)
  refine ⟨secOne I.G.PP.L I.θ, secOne_gen I.G.G I.G.PP.L I.θ I.θgen, θK, ?_, ?_⟩
  · intro Z r zp zp' h1 h2 h3 z J J' hJ hJ'
    let a0 : Over.mk (I.t'.G.hom ≫ y.x) ⟶ Over.mk y.x := Over.homMk I.t'.G.hom rfl
    let b0 : Over.mk (I.t'.G.hom ≫ y.x) ⟶ A := Over.homMk I.m1.φ I.m1.cart.1.w
    let g0 : I.t'.G.left ⟶ Gx y.x := (lift a0 b0).left
    have g0f : g0 ≫ (fst (Over.mk y.x) A).left = I.t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
    have g0s : g0 ≫ (snd (Over.mk y.x) A).left = I.m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
    have hzp : zp = r ≫ g0 := by
      apply pullback.hom_ext
      · show zp ≫ (fst (Over.mk y.x) A).left = (r ≫ g0) ≫ (fst (Over.mk y.x) A).left
        rw [Category.assoc, g0f, h2]
      · show zp ≫ (snd (Over.mk y.x) A).left = (r ≫ g0) ≫ (snd (Over.mk y.x) A).left
        rw [Category.assoc, g0s, h1]
    subst hzp
    have hj : ∀ j : PUnit → Xo.univ.t.PP.L.ι,
        (Xo.univ.t.PP.L.pull I.m1.φ).U j ≤ g0 ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit) := fun j y' hy' =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q y' ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) g0s).mpr (mem_pull.1 hy')
    have mJ : r z ∈ (Xo.univ.t.PP.L.pull I.m1.φ).U (fun _ => J (r ≫ I.m1.φ)) := mem_pull.2 (hJ (r ≫ I.m1.φ))
    have mK : r z ∈ I.t'.PP.L.U (J' (r ≫ 𝟙 _)) := by simpa using hJ' (r ≫ 𝟙 _)
    have e1 : sval (zCast A Nat.cast_one.symm y.s) (r ≫ g0) z J =
        gs (r ≫ g0) z _ (y.s.f (fun _ => J (r ≫ I.m1.φ))) := by
      rw [sval_zCast]
      exact sval_of (L := Xo.univ.t.PP.L) (φ := fun _ : Fin 1 => (snd (Over.mk y.x) A).left) (ε := fun _ => 1) y.s
        (r ≫ g0) z J (fun _ => J (r ≫ I.m1.φ)) (fun _ => by rw [Category.assoc, g0s])
    have e2 : gs (r ≫ g0) z _ (y.s.f (fun _ => J (r ≫ I.m1.φ))) =
        gs r z _ (I.s1.f (fun _ => J (r ≫ I.m1.φ))) := by
      rw [I.gen1 g0 g0s g0f _ (hj _)]
      erw [gs_appLE g0 _ _ (hj _) r z mJ]
    erw [e1, e2, gs_isoMaps I.maps1 r z _ _ mJ mK, gθK Z zp' z J' hJ', h3, pow_one, Category.comp_id]
  · intro Z r zp h3 z J J' hJ hJ'
    have mJ : r z ∈ (I.G.PP.L.pull I.m2.φ).U (fun _ => J (r ≫ I.m2.φ)) := mem_pull.2 (hJ (r ≫ I.m2.φ))
    have mK : r z ∈ I.t'.PP.L.U (J' (r ≫ 𝟙 _)) := by simpa using hJ' (r ≫ 𝟙 _)
    have hpl : (I.G.PP.L.pull I.m2.φ).U (fun _ => J (r ≫ I.m2.φ)) ≤ I.m2.φ ⁻¹ᵁ I.G.PP.L.U (J (r ≫ I.m2.φ)) :=
      fun _ hy' => mem_pull.1 hy'
    have e1 : sval (secOne I.G.PP.L I.θ) (r ≫ I.m2.φ) z J =
        gs (r ≫ I.m2.φ) z (I.G.PP.L.U (J (r ≫ I.m2.φ))) (I.θ.f (J (r ≫ I.m2.φ))) := by
      erw [sval_of _ _ z J (fun _ => J (r ≫ I.m2.φ)) (fun _ => by rw [Category.comp_id])]
      rw [secOne]
      erw [gs_pull1 _ _ _ _ z _ (plain_le _ _ (hJ (r ≫ I.m2.φ)))]
      rw [Category.comp_id]
    have e2 : gs (r ≫ I.m2.φ) z (I.G.PP.L.U (J (r ≫ I.m2.φ))) (I.θ.f (J (r ≫ I.m2.φ))) =
        gs r z _ (I.θ2.f (fun _ => J (r ≫ I.m2.φ))) := by
      rw [I.pull _ hpl]
      erw [gs_appLE I.m2.φ _ _ hpl r z mJ]
    erw [e1, e2, gs_isoMaps I.maps2 r z _ _ mJ mK, gθK Z zp z J' hJ', h3, pow_one, Category.comp_id]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
