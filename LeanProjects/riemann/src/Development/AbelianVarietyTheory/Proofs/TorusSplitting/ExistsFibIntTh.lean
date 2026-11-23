import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace FibEx

theorem exists_along {X Y B : Scheme.{0}} {L : LB X} {M : LB B} {g : Y ⟶ X} {u : X ⟶ Y} (hu : u ≫ g = 𝟙 X)
    {p : Y ⟶ B} (w : LB.Iso (L.pull g) (M.pull p)) (hw : PGen w) {ψ : X ⟶ B} (hψ : u ≫ p = ψ) :
    ∃ v : LB.Iso L (M.pull ψ), PGen v ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j : M.ι) (k : L.ι),
      ψ (f z) ∈ M.U j → f z ∈ L.U k → Geo.Tor.gw v f z j k = Geo.Tor.gw w (f ≫ u) z j (fun _ => k) := by
  subst hψ
  have mk : ∀ (x : X) (k : L.ι), x ∈ L.U k → u x ∈ (L.pull g).U (fun _ => k) := fun x k hx =>
    mem_pull.2 ((congrArg (fun q => q x ∈ L.U k) hu).mpr hx)
  have le : ∀ (J : PUnit → M.ι) (k : L.ι), (M.pull (u ≫ p)).U J ⊓ L.U k ≤
      u ⁻¹ᵁ ((M.pull p).U J ⊓ (L.pull g).U (fun _ => k)) := fun J k x hx =>
    ⟨mem_pull.2 (mem_pull₂.1 hx.1), mk x k hx.2⟩
  let v : LB.Iso L (M.pull (u ≫ p)) := ⟨fun q => res (le q.1 q.2) (pullU u _ (w.s (q.1, fun _ => q.2)))⟩
  have hv : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j : M.ι) (k : L.ι),
      (u ≫ p) (f z) ∈ M.U j → f z ∈ L.U k → Geo.Tor.gw v f z j k = Geo.Tor.gw w (f ≫ u) z j (fun _ => k) :=
    fun Z f z j k hj hk => by
      have hm : f z ∈ (M.pull (u ≫ p)).U (fun _ => j) ⊓ L.U k := ⟨mem_pull.2 hj, hk⟩
      exact (gm_res f z (le _ _) hm _).trans (gm_pull f u z _ (le _ _ hm) _)
  refine ⟨v, fun Z f z j j' k k' hj hj' hk hk' => ?_, hv⟩
  rw [hv Z f z j k hj hk, hv Z f z j' k' hj' hk',
    hw Z (f ≫ u) z j j' (fun _ => k) (fun _ => k') hj hj' (mk _ k hk) (mk _ k' hk'),
    gm_pull_g L g (f ≫ u) z _ _ (mk _ k hk) (mk _ k' hk'), Category.assoc, Category.assoc, hu, Category.comp_id]

theorem val_of_pmaps {X X' S S' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {e : S ⟶ X} {e' : S' ⟶ X'} {h : S' ⟶ S} (he : e' ≫ F = h ≫ e) {a : LB.Gen (L'.pull e')} {t : LB.Gen (L.pull e)}
    (H : PMaps w (K := PUnit) (fun _ => e') (fun _ => e) (fun _ => 1) a t h) (z : S') {J' J}
    (hJ' : Good L' z J') (hJ : Good L z J) :
    Geo.Tor.gw w e' z (J (h ≫ e)) (J' e') * val (L := L') (φ := fun _ : PUnit => e') (ε := fun _ => 1) a (𝟙 _) z J' =
      val (L := L) (φ := fun _ : PUnit => e) (ε := fun _ => 1) t h z J := by
  have k := H _ (𝟙 _) z (fun _ => J (h ≫ e)) (fun _ => J' e')
    (fun _ => (congrArg (fun q => q z ∈ L.U (J (h ≫ e))) he).mpr (hJ (h ≫ e))) (fun _ => hJ' e')
  rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at k
  rw [val_of a (𝟙 _) z J' (fun _ => J' e') (fun _ => by rw [Category.id_comp])]
  exact k.symm

theorem gs_isoMaps {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {σ : LB.Sec L'} {s : LB.Sec (L.pull F)} (h : IsoMaps w σ s) (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι)
    (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs r z _ (s.f (fun _ => j)) = (Geo.Tor.gw w r z j k).val * gs r z _ (σ.f k) := by
  have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have a := congrArg (gs r z _) (h (fun _ => j) k)
  exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))

theorem exists_sec_one {X : Scheme.{0}} {L : LB X} (θ : LB.Sec L) :
    ∃ σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J → sval σ r z J = gs r z _ (θ.f (J (r ≫ 𝟙 _))) := by
  refine ⟨thfPull1 L (𝟙 X) (Category.id_comp _) (thfPull L (𝟙 X) θ), fun Z r z J hJ => ?_⟩
  have h₁ := hJ.mem (fun _ : Fin 1 => 𝟙 X) r
  have h₂ : (r ≫ 𝟙 X) z ∈ (L.pull (𝟙 X)).U (fun _ => J (r ≫ 𝟙 _)) := chart_le_pullback_open L (𝟙 X) (Category.id_comp _) _ h₁
  refine (gs_appLE (𝟙 X) _ _ _ r z h₁ _).trans ((gs_appLE (𝟙 X) _ _ _ (r ≫ 𝟙 X) z h₂ _).trans ?_)
  simp only [Category.comp_id]

theorem core {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (PP : RigLB G) (hPP : U.LG = PP)
    {T : Over (Spec (CommRingCat.of (FractionRing R)))} [GrpObj T] [IsCommMonObj T] (L' : RigLB T)
    {φ : T.left ⟶ G.left} (cart : IsGrpPullback T G (jK R) φ) (w : LB.Iso L'.L (PP.L.pull φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec T) (fun _ => eSec G) (fun _ => 1) L'.rig PP.rig (jK R))
    (θ : LB.Sec PP.L) (σ : LB.Sec L'.L)
    (hθ : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) j k, φ (r z) ∈ PP.L.U j → r z ∈ L'.L.U k →
      gs (r ≫ φ) z _ (θ.f j) = (Geo.Tor.gw w r z j k).val * gs r z _ (σ.f k)) :
    ∃ (κ : A.A ≅ T) (_ : IsMonHom κ.hom) (_ : κ.hom.left ≫ φ = U.gen.inv.left ≫ pullback.fst G.hom (jK R))
      (w' : LB.Iso A.L (L'.L.pull κ.hom.left)) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w₀ : GlobalTheory.UT.W0 U), PGen w' ∧
      PMaps w' (K := PUnit) (fun _ => eSec A.A) (fun _ => eSec T) (fun _ => 1) ρ L'.rig (𝟙 _) ∧
      GlobalTheory.UT.NormW U w₀ ρ ∧
      ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (th : GlobalTheory.UT.SecA A F 1),
        (∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (JA) (i : L'.L.ι), Good A.L z JA →
          κ.hom.left ((r ≫ (snd (TFK (R := R) F) A.A).left) z) ∈ L'.L.U i →
          gs ((r ≫ (snd (TFK (R := R) F) A.A).left) ≫ κ.hom.left) z _ (σ.f i) =
            (Geo.Tor.gw w' (r ≫ (snd (TFK (R := R) F) A.A).left) z i
              (JA (r ≫ (snd (TFK (R := R) F) A.A).left))).val * GlobalTheory.UT.sA th r z JA) → IntTh U w₀ th := by
  subst hPP
  have := U.gen_hom
  have hi : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have hA : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  obtain ⟨κ, hκ, eκ⟩ := grpPullback_iso hA cart
  obtain ⟨w₀, g₀⟩ := U.ext
  have ug : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have gu : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left]
  obtain ⟨v, gv', hv⟩ := exists_along ug w₀ ((isGen_iff w₀).1 g₀) eκ.symm
  obtain ⟨w', Tr⟩ := exists_cancel U.LG.isLB w v hw gv' L'.isLB A.isLB
  have g' := Tr.pgen_cancel U.LG.isLB hw gv'
  have e₁ : eSec A.A ≫ κ.hom.left = 𝟙 _ ≫ eSec T := (cubeMapOf (isGrpPullback_of_iso κ)).e_comm
  have e₂ : eSec A.A ≫ U.gen.inv.left = 𝟙 _ ≫ eSec ((Over.pullback (jK R)).obj G) :=
    (cubeMapOf (isGrpPullback_of_iso U.gen.symm)).e_comm
  have e₃ : eSec A.A ≫ κ.hom.left ≫ φ = (𝟙 _ ≫ jK R) ≫ eSec G := by
    rw [eκ, Category.id_comp]; exact (cubeMapOf hA).e_comm
  obtain ⟨ρ, gρ, hρ⟩ := H1.exists_gen_move L'.isLB A.isLB w' g' (K := PUnit) (fun _ => eSec T) (fun _ => eSec A.A)
    (fun _ => 1) (𝟙 _) (fun _ => e₁) L'.rig L'.rigGen
  refine ⟨κ, hκ, eκ, w', ρ, w₀, g', hρ, ⟨g₀, gρ, fun z JA JG hA' hG => ?_⟩, fun F _ _ th H => ?_⟩
  · have k := val_of_pmaps e₃ (Tr.pmaps_comp L'.isLB (fun _ => e₁) hr hρ) z hA' hG
    rw [hv _ _ z _ _ ((congrArg (fun q => q z ∈ U.LG.L.U (JG _)) e₃).mpr (hG _)) (hA' _), e₂,
      Category.id_comp, Category.id_comp] at k
    exact k
  · obtain ⟨σ₁, h₁⟩ := exists_sec_one θ
    refine ⟨g₀, σ₁, fun Z r z JA JG hA' hG => ?_⟩
    rw [h₁ _ _ z JG hG]
    have q₁ : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left :=
      congrArg (fun q => q.left) (lift_snd (fst _ _) (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G) ≫ U.gen.hom))
    have H' := fun i => H Z (r ≫ (U.genF F).left) z JA i hA'
    have q₂ : ((r ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left) ≫ U.gen.inv.left =
        r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
      rw [Category.assoc r, q₁, Category.assoc, Category.assoc, gu, Category.comp_id]
    have q₃ : r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ pullback.fst G.hom (jK R) =
        (((r ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left) ≫ κ.hom.left) ≫ φ := by
      rw [Category.assoc _ κ.hom.left, eκ, ← Category.assoc _ U.gen.inv.left, q₂, Category.assoc]
    rw [q₃, ← q₂]
    generalize (r ≫ (U.genF F).left) ≫ (snd (TFK (R := R) F) A.A).left = a at H' ⊢
    obtain ⟨i, hi'⟩ := exists_chart L'.isLB (κ.hom.left (a z))
    have hj : φ (κ.hom.left (a z)) ∈ U.LG.L.U (JG (((a ≫ κ.hom.left) ≫ φ) ≫ 𝟙 _)) := hG (((a ≫ κ.hom.left) ≫ φ) ≫ 𝟙 _)
    rw [hθ Z (a ≫ κ.hom.left) z _ i hj hi', H' i hi', ← hv Z a z _ _ hj (hA' a), Tr Z a z _ i _ hj hi' (hA' a),
      Units.val_mul, _root_.mul_assoc]

theorem rigIso_pt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {X Y : Scheme.{0}}
    {t₁ : SAB H Y} {t : SAB H X} {f : Y ⟶ X} {m : SABMap t₁ t f} {w : LB.Iso t₁.PP.L (t.PP.L.pull m.φ)}
    (h : RigIso m w) : PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec t₁.G) (fun _ => eSec t.G) (fun _ => 1) t₁.PP.rig t.PP.rig f := by
  refine ⟨(isGen_iff w).1 h.1, ?_⟩
  have := (maps_iff w _ (fun _ => eSec t.G) _ t₁.PP.rig t.PP.rig m.cm.e _
    (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L) (fun _ => rfl)).1 h.2
  rwa [m.base] at this

end FibEx

open FibEx in

theorem exists_fib_intTh : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [Algebra c.F (FractionRing V)] (y : FrPt Xo c (FractionRing V)) (G : SAB H (Sp V)) (_ : IntSec Xo V y.x y.s G) (P : PELUnif (maximalIdeal V) G), ∃ (Φ : Fib Xo y.x P.A) (w₀ : GlobalTheory.UT.W0 P.U.toUnifPre), GlobalTheory.UT.NormW P.U.toUnifPre w₀ Φ.ρ ∧ (∀ a : 𝓞 E, ((letI := H.starRing; P.oA.act a : P.A.A ⟶ P.A.A)).left ≫ Φ.φ = Φ.φ ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra c.F F] (ψ : FractionRing V →ₐ[c.F] F) (z : FrPt Xo c F) (th : GlobalTheory.UT.SecA P.A F 1), ψ.toRingHom = algebraMap (FractionRing V) F → FrMap ψ y z → Φ.SecTie z.x z.s th → IntTh P.U.toUnifPre w₀ th := by
  intro E _ _ _ H Dw l Xo c V _ _ _ _ y G I P
  obtain ⟨g₁, r₁⟩ := rigIso_pt I.rig1
  obtain ⟨g₂, r₂⟩ := rigIso_pt I.rig2
  have hL := Xo.univ.t.PP.isLB
  have hL' := I.t'.PP.isLB
  obtain ⟨κ, hκ, eκ, w', ρ, w₀, g', hρ, hN, hI⟩ := core P.U.toUnifPre G.PP P.bundle I.t'.PP I.m2.cart I.w2 g₂ r₂ I.θ I.σ
    (fun Z r z j k hj hk => by
      have le : (G.PP.L.pull I.m2.φ).U (fun _ => j) ≤ I.m2.φ ⁻¹ᵁ G.PP.L.U j := fun q hq => mem_pull.1 hq
      refine Eq.trans ?_ (gs_isoMaps I.maps2 Z r z j k hj hk)
      rw [I.pull (fun _ => j) le]
      exact (gs_appLE I.m2.φ _ _ le r z (mem_pull.2 hj) _).symm)
  obtain ⟨ω, Tr⟩ := exists_comp hL' I.w1 w' g₁ g' hL P.A.isLB
  have cart : IsGrpPullback P.A.A Xo.univ.t.G y.x (κ.hom.left ≫ I.m1.φ) :=
    ((isGrpPullback_of_iso κ).comp I.m1.cart).congr (Category.id_comp _) rfl
  have e₁ : eSec P.A.A ≫ κ.hom.left = 𝟙 _ ≫ eSec I.t'.G := (cubeMapOf (isGrpPullback_of_iso κ)).e_comm
  have hω := Tr.pmaps_comp hL' (fun _ => e₁) r₁ hρ
  rw [Category.id_comp] at hω
  refine ⟨⟨κ.hom.left ≫ I.m1.φ, cart, ω, (isGen_iff ω).2 (Tr.pgen_comp hL' g₁ g'), ρ, hN.2.1,
    fun z JA J hA hJ => val_of_pmaps (cubeMapOf cart).e_comm hω z hA hJ⟩, w₀, hN, fun a => ?_,
    fun F _ _ _ ψ z th hψ hm hT => hI F th fun Z r p JA i hA hi => ?_⟩
  · let _ := H.starRing
    have x₁ : P.oA.act a ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK V)).map (G.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      exact (P.lin.ext a).symm
    have x₂ : ((Over.pullback (jK V)).map (G.act.act a)).left ≫ pullback.fst G.G.hom (jK V) =
        pullback.fst G.G.hom (jK V) ≫ (G.act.act a).left := pullback.lift_fst _ _ _
    have x₃ : (P.oA.act a).left ≫ κ.hom.left = κ.hom.left ≫ (I.t'.act.act a).left := by
      apply I.m2.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, I.m2.act, ← Category.assoc κ.hom.left, eκ, ← Category.assoc,
          ← Over.comp_left, x₁, Over.comp_left, Category.assoc, x₂, Category.assoc]
      · simp only [Category.assoc, Over.w]
    show (P.oA.act a).left ≫ κ.hom.left ≫ I.m1.φ = (κ.hom.left ≫ I.m1.φ) ≫ _
    rw [← Category.assoc, x₃, Category.assoc, I.m1.act, Category.assoc]
  · obtain ⟨hx, -, pm, pm₁, pm₂, hpm⟩ := hm
    let a0 : Over.mk (I.t'.G.hom ≫ y.x) ⟶ Over.mk y.x := Over.homMk I.t'.G.hom rfl
    let b0 : Over.mk (I.t'.G.hom ≫ y.x) ⟶ Xo.univ.t.G := Over.homMk I.m1.φ I.m1.cart.1.w
    let g : I.t'.G.left ⟶ Gx y.x := (lift a0 b0).left
    have gf : g ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = I.t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
    have gs' : g ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = I.m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
    clear_value g
    let p₁ : (TFK (R := V) F ⊗ P.A.A).left ⟶ Sp F := (fst (TFK (R := V) F) P.A.A).left
    let a : Z ⟶ P.A.A.left := r ≫ (snd (TFK (R := V) F) P.A.A).left
    have hj : spMap ψ.toRingHom = jFK (R := V) F := by rw [hψ]
    have a2 : (r ≫ p₁) ≫ spMap ψ.toRingHom = a ≫ P.A.A.hom := by
      rw [hj, Category.assoc, Category.assoc]
      exact congrArg (r ≫ ·) ((Over.w (fst (TFK (R := V) F) P.A.A)).trans (Over.w (snd (TFK (R := V) F) P.A.A)).symm)
    have w : (r ≫ p₁) ≫ z.x = (a ≫ κ.hom.left ≫ I.m1.φ) ≫ Xo.univ.t.G.hom := by
      rw [hx, ← Category.assoc, a2, Category.assoc a, Category.assoc a, cart.1.w]
    let r' : Z ⟶ Gx z.x := pullback.lift (r ≫ p₁) (a ≫ κ.hom.left ≫ I.m1.φ) w
    have h1 : r' ≫ (fst (Over.mk z.x) Xo.univ.t.G).left = r ≫ p₁ := pullback.lift_fst _ _ _
    have h2 : r' ≫ (snd (Over.mk z.x) Xo.univ.t.G).left = a ≫ κ.hom.left ≫ I.m1.φ := pullback.lift_snd _ _ _
    clear_value r'
    have e : r' ≫ pm = (a ≫ κ.hom.left) ≫ g := by
      apply pullback.hom_ext
      · show (r' ≫ pm) ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (_ ≫ g) ≫ (fst (Over.mk y.x) Xo.univ.t.G).left
        rw [Category.assoc, pm₂, ← Category.assoc, h1, Category.assoc _ g, gf, Category.assoc a, Over.w]
        exact a2
      · show (r' ≫ pm) ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (_ ≫ g) ≫ (snd (Over.mk y.x) Xo.univ.t.G).left
        rw [Category.assoc, pm₁, Category.assoc _ g, gs']
        exact h2.trans (Category.assoc _ _ _).symm
    obtain ⟨J, hJ, -⟩ := exists_good Xo.univ.t.PP.L hL p (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim)
      (fun a => a.elim)
    have k := hT.2 Z r r' (h2.trans (Category.assoc _ _ _)) h1 p JA J hA hJ
    have mz := hJ.mem (fun _ : Fin 1 => (snd (Over.mk z.x) Xo.univ.t.G).left) r'
    have mj : I.m1.φ (κ.hom.left (a p)) ∈ Xo.univ.t.PP.L.U (J (r' ≫ (snd (Over.mk z.x) Xo.univ.t.G).left)) := by
      rw [h2]; exact hJ (a ≫ κ.hom.left ≫ I.m1.φ)
    unfold sval at k
    beta_reduce at k
    generalize J (r' ≫ (snd (Over.mk z.x) Xo.univ.t.G).left) = j at k mz mj
    have le₁ : (PPx z.x).U (fun _ => j) ≤ pm ⁻¹ᵁ (PPx y.x).U (fun _ => j) := fun q hq =>
      Set.mem_iInter.2 fun _ => (congrArg (fun u => u q ∈ Xo.univ.t.PP.L.U j) pm₁).mpr (Set.mem_iInter.1 hq 0)
    have le₂ : (Xo.univ.t.PP.L.pull I.m1.φ).U (fun _ => j) ≤ g ⁻¹ᵁ (PPx y.x).U (fun _ => j) := fun q hq =>
      Set.mem_iInter.2 fun _ => (congrArg (fun u => u q ∈ Xo.univ.t.PP.L.U j) gs').mpr (mem_pull.1 hq)
    have k₁ : gs r' p ((PPx z.x).U (fun _ => j)) (z.s.f (fun _ => j)) =
        gs (r' ≫ pm) p ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) :=
      (congrArg (gs r' p _) (hpm (fun _ => j) le₁).symm).trans (gs_appLE pm _ _ le₁ r' p mz _)
    have k₂ : gs (a ≫ κ.hom.left) p _ (I.s1.f (fun _ => j)) =
        gs ((a ≫ κ.hom.left) ≫ g) p ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) :=
      (congrArg (gs (a ≫ κ.hom.left) p _) (I.gen1 g gs' gf (fun _ => j) le₂)).trans
        (gs_appLE g _ _ le₂ (a ≫ κ.hom.left) p (mem_pull.2 mj) _)
    have k₃ := gs_isoMaps I.maps1 Z (a ≫ κ.hom.left) p j i mj hi
    have k₄ := Tr Z a p j i (JA a) mj hi (hA a)
    rw [e, ← k₂, k₃] at k₁
    have k₅ := k₁.symm.trans (k.trans (congrArg (fun u => u.val * GlobalTheory.UT.sA th r p JA) k₄))
    rw [Units.val_mul, _root_.mul_assoc] at k₅
    exact (Units.mul_right_inj _).1 k₅

end GlobalTheory.EtaVal
