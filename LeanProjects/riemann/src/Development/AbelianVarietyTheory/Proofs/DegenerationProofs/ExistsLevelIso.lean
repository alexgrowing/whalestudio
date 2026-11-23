import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThickIsoOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralSectionsCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfPullbackId

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericIso

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RigidSections GlobalTheory.FamFieldPull

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I D A G) (U' : UnifPre I D' A' G')
  (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G)

def LevelIso : Prop :=
  ∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧
    (U'.gt e).pG.left ≫ prA hD = (j e).hom.left ≫ (U.gt e).pG.left ∧
    ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ prA hD =
        (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧
      PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x)
        ((U.gt e).t (hD.xe x)) (j e).hom.left

def AgreeAll (k : ℕ) (σ : H0 U.LG.L k) (σ' : H0 U'.LG.L k) : Prop :=
  ∀ e : ℕ, Agree U U' hD e k (j e).hom.left σ σ'

def Enough : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    (∀ σ₀ : H0 U.LG.L k, ∃ (c : R) (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), c ≠ 0 ∧
      (∀ i, σ.f i = resTop _ (scal G.hom c) * σ₀.f i) ∧ AgreeAll U U' hD j k σ σ') ∧
    ∀ σ₀ : H0 U'.LG.L k, ∃ (c : R) (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), c ≠ 0 ∧
      (∀ i, σ'.f i = resTop _ (scal G'.hom c) * σ₀.f i) ∧ AgreeAll U U' hD j k σ σ'

def GenericRel (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G)
    (w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R)))
      (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))) : Prop :=
  w.IsGen ∧ ∀ k : ℕ, 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), AgreeAll U U' hD j k σ σ' →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL →
      (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' →
      gs (r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL))
          (σ.f (fun _ => jL)) =
        (Geo.Tor.gw w r z jL (fun _ => jL') ^ k).val *
          gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL'))
            (σ'.f (fun _ => jL'))

open ThickIso TorusCoordPull in
theorem exists_levelIso (hG : GlobalFnsSt) : ∃ j, LevelIso U U' hD j := by
  choose j hm hj using fun e : ℕ => exists_iso hD (U.gt e) (U'.gt e) hG
  refine ⟨j, fun e => ?_⟩
  have h₀ := hj e _ (𝟙 _)
  have hp : (U'.gt e).pG.left ≫ abMap hD = (j e).hom.left ≫ (U.gt e).pG.left := by
    simpa only [Category.id_comp] using h₀.1
  have hO := Oφ_pull hD (U.gt e).pG (U'.gt e).pG (j e).hom.left hp
  refine ⟨hm e, (hj (e + 1) _ (thickMap R I e G')).unique_right ?_, hp, fun x => ⟨hO x,
    pmaps_of_good ((isGen_iff hD.w).1 hD.w_gen) D.toPre.P.isLB D'.toPre.P.isLB (hO x) ((U'.gt e).t_gen x)
      ((U.gt e).t_gen _) fun y J J' hJ hJ' => h₀.2 x y J J' hJ hJ'⟩⟩
  simpa only [Category.id_comp] using h₀.succ (U.gt_q e) (U.gt_t e) (U'.gt_q e) (U'.gt_t e)

variable {U U' hD j}

theorem LevelIso.agreeAll (hj : LevelIso U U' hD j) {k : ℕ} {σ : H0 U.LG.L k} {σ' : H0 U'.LG.L k}
    {f : ∀ α, D.toPre.SecB k α} {f' : ∀ α, D'.toPre.SecB k α} (hE : ∀ e, U.ExpandsAt e k σ f)
    (hE' : ∀ e, U'.ExpandsAt e k σ' f')
    (hf : ∀ x, IsSecPull hD.w (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) (prA hD) (f' x)
      (f (hD.xe x))) : AgreeAll U U' hD j k σ σ' := fun e =>
  agree_of_expandsAt _ _ hD e k _ (hj e).2.2.1 (fun x => ((hj e).2.2.2 x).1) (fun x => ((hj e).2.2.2 x).2)
    (hE e) (hE' e) hf

theorem LevelIso.enough (hj : LevelIso U U' hD j) (hG : GlobalFnsSt) (hU : ∀ k, 1 ≤ k → U.ExpBij k)
    (hU' : ∀ k, 1 ≤ k → U'.ExpBij k) : Enough U U' hD j := by
  intro k hk
  constructor
  · intro σ₀
    obtain ⟨s, hs⟩ := exists_restrict U k σ₀
    obtain ⟨F, ⟨r, hr, σ, f, h₁, h₂, h₃⟩, -⟩ := (hU k hk).1 s
    obtain ⟨F', hF⟩ := exists_pull hD _ hG k F
    obtain ⟨s', ⟨r', hr', σ', f', h₁', h₂', h₃'⟩, -⟩ := (hU' k hk).2 F'
    exact ⟨r' * r, _, _, mul_ne_zero hr' hr, scale_of_restrict _ hs h₁ r', hj.agreeAll
      (fun e => expandsAt_scale _ (h₃ e) _) (fun e => expandsAt_scale _ (h₃' e) _) (integral_rel hD _ hF h₂ h₂')⟩
  · intro σ₀
    obtain ⟨s', hs⟩ := exists_restrict U' k σ₀
    obtain ⟨F', ⟨r', hr', σ', f', h₁', h₂', h₃'⟩, -⟩ := (hU' k hk).1 s'
    obtain ⟨F, hF⟩ := exists_push hD _ hG k F'
    obtain ⟨s, ⟨r, hr, σ, f, h₁, h₂, h₃⟩, -⟩ := (hU k hk).2 F
    exact ⟨r * r', _, _, mul_ne_zero hr hr', scale_of_restrict _ hs h₁' r, hj.agreeAll
      (fun e => expandsAt_scale _ (h₃ e) _) (fun e => expandsAt_scale _ (h₃' e) _) (integral_rel hD _ hF h₂ h₂')⟩

open LinearUnifIso in

theorem LevelIso.act_comm (hj : LevelIso U U' hD j) (hG : GlobalFnsSt) {O : Type} [CommRing O] [StarRing O]
    [Module O D.toPre.X] [Module O D'.toPre.X] {o : D.OAct O} {o' : D'.OAct O} {oA : A.OAct O} {oA' : A'.OAct O}
    {oG : RingAct G O} {oG' : RingAct G' O} (lin : U.OLinear O o oA oG) (lin' : U'.OLinear O o' oA' oG')
    (hx : ∀ (x : O) y, hD.xe (x • y) = x • hD.xe y)
    (hB : ∀ x, o'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (o.onB.act x))
    (a : O) (e : ℕ) : (Over.pullback (thick R I e)).map (oG'.act a) ≫ (j e).hom =
      (j e).hom ≫ (Over.pullback (thick R I e)).map (oG.act a) := by
  have hs : specOf (RingHom.id R) = 𝟙 _ := specOf_id R
  have := hD.e_hom
  obtain ⟨ψ, hψ, eψ⟩ := exists_hom_of_pullback_id hs hD.e
  have P : ∀ {S : Scheme.{0}} (t : S ⟶ Spec (CommRingCat.of R)) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback t).map c).left ≫ pullback.fst Y.hom t =
        pullback.fst X.hom t ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have hψa : o'.onB.act a ≫ ψ = ψ ≫ o.onB.act a := Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, eψ, Category.assoc, ← P, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, hB])
  obtain ⟨hm, -, hp, ht⟩ := hj e
  have hq : (j e).hom ≫ (U.gt e).q = (U'.gt e).q ≫ (Over.pullback (thick R I e)).map ψ := by
    refine Over.OverMorphism.ext ?_
    rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e)), Over.comp_left, Over.comp_left,
      Category.assoc, Category.assoc, P, eψ]
    exact hp.symm.trans (Category.assoc _ _ _)
  obtain ⟨s, hsi, hsx⟩ := exists_torus_map (U.gt e) (U'.gt e) _ _ hq hD.w hD.xe (fun x => (ht x).1)
    (fun x => (ht x).2)
  obtain ⟨t, tc, ti⟩ := lin.i_lin e a
  obtain ⟨t', tc', ti'⟩ := lin'.i_lin e a
  have := oG.hom a
  have := oG'.hom a
  have hts : t' ≫ s = s ≫ t := by
    refine PowTorus.torus_ext _ _ fun χ z => ?_
    obtain ⟨x, rfl⟩ := hD.xe.surjective χ
    rw [Over.comp_left, Over.comp_left, gm_torusEnd tc, ← hx, hsx, gm_comp_of_id _ _ _ (hsx x),
      ← gm_torusEnd tc', Category.id_comp]
  refine hom_ext_torus (U.gt e) (U'.gt e) hG _ _ ?_ ?_
  · rw [Category.assoc, Category.assoc, lin.q_lin, hq, reassoc_of% hq, reassoc_of% (lin'.q_lin e a),
      ← Functor.map_comp, ← Functor.map_comp, hψa]
  · rw [reassoc_of% ti', ← hsi, ← reassoc_of% hsi, ti, reassoc_of% hts]

end GlobalTheory.GenericIso
