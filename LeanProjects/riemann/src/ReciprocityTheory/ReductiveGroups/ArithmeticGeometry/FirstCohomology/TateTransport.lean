import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

def TateTransportStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    (I : Ideal R) (t : SAB H (Sp R)) (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (Dw : Datum H),
    letI := H.starRing
    ∀ I₀ : TateIso Dw F (TF (R := R) F ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun n g g' c => WeilIs t.G t.PP.L n g g' (unitOn c)),
      ∃ I₁ : TateIso Dw F (TFK (R := R) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a)
          (fun n g g' c => WeilIs P.A.A P.A.L n g g' (unitOn c)),
        ∀ n, I₁.ζ n = I₀.ζ n

theorem weil_move (hW : WeilSt) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {φ : P.A.A.left ⟶ t.G.left} (hp : IsGrpPullback P.A.A t.G (jK R) φ)
    (w : LB.Iso P.A.L (t.PP.L.pull φ)) (hw : w.IsGen)
    (n : ℕ) (x y : TFK (R := R) F ⟶ P.A.A) (hx : x ^ n = 1) (hy : y ^ n = 1) (c : Γ(Sp F, ⊤)ˣ)
    (hG : WeilIs t.G t.PP.L n (pushPt hp.1.w x) (pushPt hp.1.w y) c) : WeilIs P.A.A P.A.L n x y c := by
  obtain ⟨c', hc', -⟩ := (hW (Sp (FractionRing R)) P.A n (TFK (R := R) F)).1 x y hx hy
  intro p
  obtain ⟨V, hpV, ⟨θx₀, θy₀, hpx₀, hpy₀⟩, hall₀⟩ := hG p
  obtain ⟨V', hpV', -, hall'⟩ := hc' p
  have hsub : Subsingleton (Spec (CommRingCat.of F)) := inferInstance
  have hVV : V = V' := by
    ext q
    rw [@Subsingleton.elim _ hsub q p]
    exact ⟨fun _ => hpV', fun _ => hpV⟩
  subst hVV
  have hτ : 𝟙 _ ≫ (overRes (T := TF (R := R) F) V).hom = (overRes (T := TFK (R := R) F) V).hom ≫ jK R := by
    rw [Category.id_comp]; exact (Category.assoc _ _ _).symm
  have mvx : 𝟙 _ ≫ θx₀.pt.left = (overResι (T := TFK (R := R) F) V ≫ x).left ≫ φ := by
    rw [hpx₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc]; rfl
  have mvy : 𝟙 _ ≫ θy₀.pt.left = (overResι (T := TFK (R := R) F) V ≫ y).left ≫ φ := by
    rw [hpy₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc]; rfl
  obtain ⟨θx, hθx, mx⟩ := exists_theta_move (T := overRes (T := TFK (R := R) F) V) (T₀ := overRes (T := TF (R := R) F) V)
    hp (𝟙 _) hτ t.PP.isLB P.A.isLB w hw n _ θx₀ mvx
  obtain ⟨θy, hθy, my⟩ := exists_theta_move (T := overRes (T := TFK (R := R) F) V) (T₀ := overRes (T := TF (R := R) F) V)
    hp (𝟙 _) hτ t.PP.isLB P.A.isLB w hw n _ θy₀ mvy
  have hm := commIsOf_move (T := overRes (T := TFK (R := R) F) V) (T₀ := overRes (T := TF (R := R) F) V) hp (𝟙 _) hτ t.PP.isLB P.A.isLB w n θx₀ θy₀ θx θy (by rw [hθx]; exact mvx)
    (by rw [hθy]; exact mvy) mx my (unitRes (T := TF (R := R) F) V c) (unitRes (T := TFK (R := R) F) V c) (fun Z r z => by rw [Category.comp_id]; rfl)
    (hall₀ θx₀ θy₀ hpx₀ hpy₀)
  have hcc := commIsOf_unique P.A.isLB θx θy _ _ hm (hall' θx θy hθx hθy)
  refine ⟨V, hpV, ⟨θx, θy, hθx, hθy⟩, fun θx' θy' h₁ h₂ => ?_⟩
  rw [hcc]
  exact hall' θx' θy' h₁ h₂

theorem tateTransport_holds (hW : WeilSt) : TateTransportStatement := by
  intro E _ _ _ H R _ _ I t P F _ _ Dw
  letI := H.starRing
  intro I₀
  have := P.U.gen_hom
  have gpG : IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) := by
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := by
    have h := P.U.ext
    rw [P.bundle] at h
    exact h
  have hL : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) := by
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) :=
      LBIso.chartPull (chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull P.A.L _ hgi)
      (chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  obtain ⟨w, hw⟩ := hL
  let Φ := pushHom gpG (TFK (R := R) F)
  have hinj : Function.Injective Φ := fun x y hxy =>
    Over.OverMorphism.ext (gpG.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y]))
  have hsurj : Function.Surjective Φ := fun x₀ =>
    ⟨Over.homMk (gpG.1.lift x₀.left (jFK (R := R) F) (Over.w x₀)) (gpG.1.lift_snd _ _ _),
      Over.OverMorphism.ext (gpG.1.lift_fst _ _ _)⟩
  let Φe : (TFK (R := R) F ⟶ P.A.A) ≃* (TF (R := R) F ⟶ t.G) := MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hΦ : ∀ x, Φe x = pushPt gpG.1.w x := fun x => rfl
  have actA : ∀ a, (P.oA.act a).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
      P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ (t.act.act a).left := by
    intro a
    have e : P.oA.act a ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext a)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have hact : ∀ x a, Φe (x ≫ P.oA.act a) = Φe x ≫ t.act.act a := fun x a => by
    apply Over.OverMorphism.ext
    show (x ≫ P.oA.act a).left ≫ _ = (pushPt gpG.1.w x).left ≫ (t.act.act a).left
    rw [Over.comp_left, Category.assoc, actA]; rfl
  have hpow : ∀ n, 0 < n → ∀ a, (Φe.symm (I₀.ev n a)) ^ n = 1 := fun n hn a => by
    rw [← map_pow, (I₀.onto n hn _).2 ⟨a, rfl⟩, map_one]
  refine ⟨
    { ζ := I₀.ζ
      ζ_prim := I₀.ζ_prim
      ζ_pow := I₀.ζ_pow
      ev := fun n a => Φe.symm (I₀.ev n a)
      add := fun n a b => by simp only [I₀.add, map_mul]
      lin := fun n c a => by
        show Φe.symm (I₀.ev n (c • a)) = Φe.symm (I₀.ev n a) ≫ P.oA.act c
        apply Φe.injective
        rw [MulEquiv.apply_symm_apply, hact, MulEquiv.apply_symm_apply]
        exact I₀.lin n c a
      ker := fun n hn a => (map_eq_one_iff _ Φe.symm.injective).trans (I₀.ker n hn a)
      onto := fun n hn x => by
        rw [← map_eq_one_iff Φe Φe.injective, map_pow, I₀.onto n hn]
        exact exists_congr fun a => Φe.symm_apply_eq.symm
      tower := fun n m hn hm a => by rw [← map_pow, I₀.tower n m hn hm a]
      isom := fun n hn a b => by
        have h := I₀.isom n hn a b
        rw [← Φe.apply_symm_apply (I₀.ev n a), ← Φe.apply_symm_apply (I₀.ev n b), hΦ, hΦ] at h
        exact weil_move hW P F gpG w hw n _ _ (hpow n hn a) (hpow n hn b) _ h }, fun n => rfl⟩

end ReciprocityTheory.ChartRestriction.G.H1
