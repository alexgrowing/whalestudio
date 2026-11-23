import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg

noncomputable section

namespace GlobalTheory.ArcPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PsiEvenPull (proj)
open scoped CategoryTheory.Obj

section General

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]

def om (w : LB.Iso L' (L.pull Φ)) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (x : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ := Geo.Tor.gw w x z (J (x ≫ Φ)) (J' x)

theorem pmaps_om {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
    (hψ : ∀ k, φ' k ≫ Φ = h ≫ φ k) {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)}
    (H : PMaps w φ' φ ε a t h) (r : Z ⟶ Y') (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val t (r ≫ h) z J = (∏ k, om w z J J' (r ≫ φ' k) ^ ε k) * val a r z J' :=
  DegPull.pmaps_val hψ H r z hJ hJ'

theorem exists_down_om {w : LB.Iso L' (L.pull Φ)} (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hψ : ∀ k, φ' k ≫ Φ = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J J', Good L z J →
      Good L' z J' → val t (r ≫ h) z J = (∏ k, om w z J J' (r ≫ φ' k) ^ ε k) * val a r z J' := by
  obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps ((isGen_iff w).1 hw) hL hL' h hψ t ht
  exact ⟨a, ha, fun Z r z J J' hJ hJ' => pmaps_om hψ H r z hJ hJ'⟩

end General

section Rosati

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A] [IsCommMonObj A']
  {f : S' ⟶ S} {Φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}

omit [IsCommMonObj A] [IsCommMonObj A'] in
theorem mul_push (gp : IsGrpPullback A' A f Φ) {T' : Over S'} {T : Over S} (h : T'.left ⟶ T.left) {x' y' : T' ⟶ A'}
    {x y : T ⟶ A} (hx : x'.left ≫ Φ = h ≫ x.left) (hy : y'.left ≫ Φ = h ≫ y.left) :
    (x' * y').left ≫ Φ = h ≫ (x * y).left := by
  have hh : h ≫ T.hom = T'.hom ≫ f := by
    rw [← Over.w x, ← Category.assoc, ← hx, Category.assoc, gp.1.w, ← Category.assoc, Over.w]
  let ρ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk h hh
  have e := gp.2 T' x' y' (ρ ≫ x) (ρ ≫ y) hx.symm hy.symm
  rw [← MonObj.comp_mul] at e
  exact e.symm

theorem ros_val (hG : GlobalFnsSt) (gp : IsGrpPullback A' A f Φ) (hA' : IsAbelianScheme A') (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull Φ)} (hw : w.IsGen) {a b : A ⟶ A} {a' b' : A' ⟶ A'} [IsMonHom a'] [IsMonHom b']
    (ha : a'.left ≫ Φ = Φ ≫ a.left) (hb : b'.left ≫ Φ = Φ ≫ b.left)
    {u : LB.Gen (LB.LinComb L (rosatiφ A a b) rosatiε)} {u' : LB.Gen (LB.LinComb L' (rosatiφ A' a' b') rosatiε)}
    (hu : TorusExt.IsRos L a b u) (hu' : TorusExt.IsRos L' a' b' u') {T' : Over S'} (x' y' : T' ⟶ A')
    (m : T'.left ⟶ (A ⊗ A).left) (hx : x'.left ≫ Φ = m ≫ (fst A A).left) (hy : y'.left ≫ Φ = m ≫ (snd A A).left)
    {z : T'.left} {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val u m z J = om w z J J' ((x' ≫ a') * y').left * (om w z J J' (x' ≫ a').left)⁻¹ * (om w z J J' y'.left)⁻¹ *
      (om w z J J' (x' * (y' ≫ b')).left)⁻¹ * om w z J J' x'.left * om w z J J' (y' ≫ b').left *
      val₂ u' z J' x' y' := by
  let Φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left := (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A'))).left
  have f₁ : (fst A' A').left ≫ Φ = Φ₂ ≫ (fst A A).left :=
    (congrArg (fun q => q.left) (lift_fst (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).symm
  have f₂ : (snd A' A').left ≫ Φ = Φ₂ ≫ (snd A A).left :=
    (congrArg (fun q => q.left) (lift_snd (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).symm
  have f₃ : (fst A' A' ≫ a').left ≫ Φ = Φ₂ ≫ (fst A A ≫ a).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, f₁, Category.assoc]
  have f₄ : (snd A' A' ≫ b').left ≫ Φ = Φ₂ ≫ (snd A A ≫ b).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hb, ← Category.assoc, f₂, Category.assoc]
  have hψ : ∀ i, rosatiφ A' a' b' i ≫ Φ = Φ₂ ≫ rosatiφ A a b i := fun i => by
    fin_cases i
    exacts [mul_push gp Φ₂ f₃ f₂, f₃, f₂, mul_push gp Φ₂ f₁ f₄, f₁, f₄]
  have cmp : ∀ {T' : Over S'} (x' y' : T' ⟶ A') (m : T'.left ⟶ (A ⊗ A).left), x'.left ≫ Φ = m ≫ (fst A A).left →
      y'.left ≫ Φ = m ≫ (snd A A).left → (lift x' y').left ≫ Φ₂ = m := fun x' y' m hx hy => by
    apply pullback.hom_ext
    · refine Eq.trans ?_ hx
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) f₁.symm).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_fst]
    · refine Eq.trans ?_ hy
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) f₂.symm).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
  obtain ⟨t, ht, vt⟩ := exists_down_om hw hL hL' Φ₂ hψ u hu.1
  have rt : TorusExt.IsRos L' a' b' t := ⟨ht, corr_of_val hL' fun y I' hI' => by
    obtain ⟨I, hI⟩ := DegPull.exists_good' hL y
    have o : lift (1 : 𝟙_ (Over S') ⟶ A') (1 : 𝟙_ (Over S') ⟶ A') = lift η[A'] η[A'] := by simp [Hom.one_def]
    have he : eSec A' ≫ Φ = f ≫ eSec A := (cubeMapOf gp).e_comm
    have o₁ : (1 : 𝟙_ (Over S') ⟶ A').left = eSec A' := Category.id_comp _
    have e := vt _ (lift (1 : 𝟙_ (Over S') ⟶ A') (1 : 𝟙_ (Over S') ⟶ A')).left y I I' hI hI'
    rw [prod_ros, cmp 1 1 (f ≫ zero2 A) (by
        rw [o₁, he, Category.assoc, ← Over.comp_left, lift_fst]; rfl) (by
        rw [o₁, he, Category.assoc, ← Over.comp_left, lift_snd]; rfl),
      MonObj.one_comp, MonObj.one_comp, _root_.mul_one, o] at e
    have e₁ := (val_pull hI _ _ _).symm.trans ((val_corr hI hu.2 f).trans (val_one _))
    rw [e₁] at e
    rw [val_pull hI', val_one, Category.id_comp]
    simpa using e.symm⟩
  have e := vt _ (lift x' y').left z J J' hJ hJ'
  rw [prod_ros, cmp x' y' m hx hy] at e
  exact e.trans (congrArg _ (TorusExt.IsRos.unique hG hA' hL' rt hu' hJ' x' y'))

end Rosati

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) (r' : Z ⟶ (TK R').left)
  (hr : r' ≫ jK R' ≫ spMap φ = r ≫ jK R) {z : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} {J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι}
  (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
include hr hJ hJ'

theorem psi_val (x : D'.X) :
    val (D.psi (hD.xe x)) r z J = (om hD.w z J J' (r' ≫ D'.xK x))⁻¹ * val (D'.psi x) r' z J' := by
  have hW : r ≫ jK R = (r' ≫ hD.g) ≫ hD.W.ι := by
    rw [Category.assoc, hD.g_comm]; exact hr.symm
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : Z ⟶ (jK R ⁻¹ᵁ hD.W).toScheme, lam ≫ (jK R ⁻¹ᵁ hD.W).ι = r ∧
      lam ≫ (jK R ∣_ hD.W) = r' ≫ hD.g :=
    ⟨(isPullback_morphismRestrict (jK R) hD.W).lift _ _ hW.symm,
      (isPullback_morphismRestrict (jK R) hD.W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) hD.W).lift_fst _ _ _⟩
  have e := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (hD.psiW.psi_eq (hD.xe x)) lam).trans (val_pull hJ _ _ _))
  rw [l₁, l₂] at e
  exact e.symm.trans (PsiEvenPull.psi_pull hD x r' z hJ hJ')

theorem rig_val : val D.rigK r z J = om hD.w z J J' (r' ≫ (1 : TK R' ⟶ D'.P.A).left) * val D'.rigK r' z J' := by
  have pm := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
    (rigPull_le (proj hD) (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
  have e := pmaps_om (fun _ => hD.he) pm (r' ≫ jK R') z hJ hJ'
  rw [Fintype.prod_unique, zpow_one, Category.assoc, Category.assoc] at e
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
  exact (congrArg (fun q => val D.rig q z J) hr.symm).trans e

theorem tau_val (a b : D'.X) : val (D.tau (hD.xe a) (hD.xe b)) r z J =
    (om hD.w z J J' (r' ≫ D'.xK (a + b)))⁻¹ * om hD.w z J J' (r' ≫ D'.xK a) * om hD.w z J J' (r' ≫ D'.xK b) *
      (om hD.w z J J' (r' ≫ (1 : TK R' ⟶ D'.P.A).left))⁻¹ * val (D'.tau a b) r' z J' := by
  rw [TauPull.val_tau r hJ, TauPull.val_tau r' hJ', ← map_add, psi_val hD r r' hr hJ hJ', psi_val hD r r' hr hJ hJ',
    psi_val hD r r' hr hJ hJ', rig_val hD r r' hr hJ hJ']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Pull

section Inj

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}

def fracMap (hφ : Function.Injective φ) : FractionRing R →+* FractionRing R' :=
  IsFractionRing.lift (g := (algebraMap R' (FractionRing R')).comp φ) ((IsFractionRing.injective R' _).comp hφ)

theorem fracMap_algebraMap (hφ : Function.Injective φ) (x : R) :
    fracMap hφ (algebraMap R _ x) = algebraMap R' _ (φ x) := IsFractionRing.lift_algebraMap _ x

def genMap (hφ : Function.Injective φ) : (TK R').left ⟶ (TK R).left := spMap (fracMap hφ)

theorem fracMap_sq (hφ : Function.Injective φ) :
    𝟙 (TK R').left ≫ jK R' ≫ spMap φ = genMap hφ ≫ jK R :=
  (Category.id_comp _).trans ((spMap_comp _ (fracMap hφ)).symm.trans
    ((congrArg spMap (RingHom.ext (fracMap_algebraMap hφ))).trans (spMap_comp φ _))).symm

variable {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D')

theorem cPoint_proj {T : Over (Sp R)} {T' : Over (Sp R')} (h : T'.left ⟶ T.left) (hh : T'.hom ≫ spMap φ = h ≫ T.hom)
    (x : D'.X) : (cP D' T' x).left ≫ proj hD = h ≫ (cP D T (hD.xe x)).left := by
  show (T'.hom ≫ (D'.c x).left) ≫ proj hD = h ≫ T.hom ≫ (D.c (hD.xe x)).left
  rw [Category.assoc, hD.c_pr, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ _) hh

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X]

theorem exists_oAct (hG : GlobalFnsSt) (hφ : Function.Injective φ) (oa : D.OAct O)
    (hx : ∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) :
    ∃ oa' : D'.OAct O, ∀ a, (oa'.onB.act a).left ≫ proj hD = proj hD ≫ (oa.onB.act a).left := by
  have gp := pull_grp hD
  obtain ⟨o, ho⟩ := polOActPull _ _ _ D.P D'.P _ gp (LBIso.symm ⟨hD.w, hD.w_gen⟩) O oa.onB
  have cl : ∀ (a : O) y, D'.c (a • y) = D'.c y ≫ o.act a := fun a y => by
    refine Over.OverMorphism.ext (gp.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [hD.c_pr, hx, oa.c_lin, Over.comp_left, Over.comp_left, Category.assoc, ho, ← Category.assoc (D'.c y).left,
      hD.c_pr, Category.assoc]
  refine ⟨⟨o, cl, fun a u' hu' h₀ y y' => corr_of_val D'.P.isLB fun z J' hJ' => ?_⟩, ho⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB z
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have := o.hom a
  have := o.hom (star a)
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ (oa.onB.rosati a)
  have sq := fracMap_sq hφ
  have hh : (TK R').hom ≫ spMap φ = genMap hφ ≫ (TK R).hom := (Category.id_comp _).symm.trans sq
  have e := val_corr hJ (oa.tau_bal a u hu u₀ (hD.xe y) (hD.xe y')) (genMap hφ)
  have v := ros_val hG gp D'.P.isAb D.P.isLB D'.P.isLB hD.w_gen (ho a) (ho (star a)) ⟨hu, u₀⟩ ⟨hu', h₀⟩
    (cP D' (TK R') y) (cP D' (TK R') y') (genMap hφ ≫ D.pt2 (hD.xe y) (hD.xe y'))
    ((cPoint_proj hD _ hh y).trans (by
      rw [Category.assoc, DegPre.pt2, ← Over.comp_left, lift_fst]; rfl))
    ((cPoint_proj hD _ hh y').trans (by
      rw [Category.assoc, DegPre.pt2, ← Over.comp_left, lift_snd]; rfl)) hJ hJ'
  have cs : ∀ (a : O) y, cP D' (TK R') y ≫ o.act a = cP D' (TK R') (a • y) := fun a y => by
    rw [cP, cP, cl, Category.assoc]
  rw [cs, cs, ← cPoint_add, ← cPoint_add] at v
  rw [val_mul hJ, val_pull hJ, v] at e
  beta_reduce at e
  rw [← hx, ← hx, tau_val hD _ _ sq hJ hJ', tau_val hD _ _ sq hJ hJ'] at e
  simp only [Category.id_comp] at e
  rw [val_mul hJ', val_pull hJ', Category.id_comp]
  have e' := congrArg Additive.ofMul e
  apply Additive.ofMul.injective
  have c₀ : ∀ x, (cP D' (TK R') x).left = D'.xK x := fun _ => rfl
  have c₁ : val₂ u' z J' (cP D' (TK R') y) (cP D' (TK R') y') = val u' (D'.pt2 y y') z J' := rfl
  simp only [ofMul_mul, ofMul_inv, c₀, c₁] at e' ⊢
  linear_combination (norm := abel) e'

theorem traceFormTwistIso_of_pullback (hφ : Function.Injective φ) {oa : D.OAct O} {oa' : D'.OAct O}
    (hx : ∀ (a : O) y, hD.xe (a • y) = a • hD.xe y)
    (ho : ∀ a, (oa'.onB.act a).left ≫ proj hD = proj hD ≫ (oa.onB.act a).left) {w0 : O} (h : TraceFormTwistIso D oa w0) :
    TraceFormTwistIso D' oa' w0 := by
  have gp := pull_grp hD
  obtain ⟨u, hu, u₀, hy⟩ := h
  have := oa'.onB.hom w0
  have i₁ : (𝟙 D'.P.A : D'.P.A ⟶ _).left ≫ proj hD = proj hD ≫ (𝟙 D.P.A : D.P.A ⟶ _).left :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  have i₂ : (toUnit D'.P.A ≫ η[D'.P.A]).left ≫ proj hD = proj hD ≫ (toUnit D.P.A ≫ η[D.P.A]).left := by
    show (D'.P.A.hom ≫ eSec D'.P.A) ≫ proj hD = proj hD ≫ D.P.A.hom ≫ eSec D.P.A
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hD.he).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) gp.1.w.symm).trans (Category.assoc _ _ _))))
  obtain ⟨t, ht, vt⟩ := exists_down_om hD.w_gen D.P.isLB D'.P.isLB
    (φ' := ![(padd D'.P.A (𝟙 _) (oa'.onB.act w0)).left, 𝟙 D'.P.A.left, (oa'.onB.act w0).left,
      (toUnit D'.P.A ≫ η[D'.P.A]).left]) (proj hD) (fun k => by
      fin_cases k
      exacts [mul_push gp _ i₁ (ho w0), i₁, ho w0, i₂]) u hu
  have pr : ∀ {T : Over (Sp R')} (x : T ⟶ D'.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D'.P.A.left) → U),
      ∏ k : Fin 4, h (x.left ≫ ![(padd D'.P.A (𝟙 _) (oa'.onB.act w0)).left, 𝟙 D'.P.A.left, (oa'.onB.act w0).left,
      (toUnit D'.P.A ≫ η[D'.P.A]).left] k) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) k =
      h (x * (x ≫ oa'.onB.act w0)).left * (h x.left ^ 2)⁻¹ * (h (x ≫ oa'.onB.act w0).left)⁻¹ *
        h (1 : T ⟶ D'.P.A).left ^ 2 := by
    intro T x U _ h
    have a₀ : x ≫ padd D'.P.A (𝟙 _) (oa'.onB.act w0) = x * (x ≫ oa'.onB.act w0) :=
      (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id])
    have a₁ : x ≫ toUnit D'.P.A ≫ η[D'.P.A] = 1 := MonObj.comp_one (M := D'.P.A) x
    rw [Fin.prod_univ_four]
    show h (x ≫ padd D'.P.A (𝟙 _) (oa'.onB.act w0)).left ^ (1 : ℤ) * h (x.left ≫ 𝟙 _) ^ (-2 : ℤ) *
      h (x ≫ oa'.onB.act w0).left ^ (-1 : ℤ) * h (x ≫ toUnit D'.P.A ≫ η[D'.P.A]).left ^ (2 : ℤ) = _
    rw [a₀, a₁, Category.comp_id]
    simp only [zpow_neg, zpow_ofNat, pow_one]
  refine ⟨t, ht, corr_of_val D'.P.isLB fun y J' hJ' => ?_, fun x => corr_of_val D'.P.isLB fun z J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have o₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A).left = eSec D'.P.A := Category.id_comp _
    have e := vt _ (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A).left y J J' hJ hJ'
    rw [pr, MonObj.one_comp, _root_.mul_one, o₁, hD.he] at e
    have e₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ u₀ (specOf φ)).trans (val_one _))
    rw [e₁] at e
    rw [val_pull hJ', val_one, Category.id_comp]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB z
    have sq := fracMap_sq hφ
    have hh : (TK R').hom ≫ spMap φ = genMap hφ ≫ (TK R).hom := (Category.id_comp _).symm.trans sq
    have e := val_corr hJ (hy (hD.xe x)) (genMap hφ)
    have v := vt _ (cP D' (TK R') x).left z J J' hJ hJ'
    rw [pr, cPoint_proj hD _ hh, ← TorusExt.cPoint_smul oa', ← cPoint_add] at v
    have c₀ : ∀ x, (cP D' (TK R') x).left = D'.xK x := fun _ => rfl
    have c₁ : ∀ x, (cP D (TK R) x).left = D.xK x := fun _ => rfl
    simp only [c₀, c₁] at v
    rw [val_mul hJ, val_mul hJ, val_pull hJ, v, ← hx, tau_val hD _ _ sq hJ hJ', psi_val hD _ _ sq hJ hJ',
      rig_val hD _ _ sq hJ hJ'] at e
    simp only [Category.id_comp] at e
    rw [val_mul hJ', val_mul hJ', val_pull hJ', Category.id_comp]
    have e' := congrArg Additive.ofMul e
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ⊢
    linear_combination (norm := abel) e'

theorem psiUnitOn_univ_iff (D : DegPre R) (χ : D.X) : PsiUnitOn D χ Set.univ ↔
    ∃ t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (Y := Sp R) (fun _ => (D.c χ).left) (fun _ => -1)), t.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (jK R)) (D.psi χ) := by
  have hss : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have dn := TauPull.jK_mem (R := R) z
  have inj := TauPull.gm_injective_of_dense (jK R) z dn
  constructor
  · intro H
    have glue : ∀ j : PUnit → D.P.L.ι, ∃ s : Γ(Sp R, LB.wchart D.P.L (Y := Sp R) (fun _ : PUnit => (D.c χ).left) j)ˣ,
        jK R z ∈ LB.wchart D.P.L (Y := Sp R) (fun _ : PUnit => (D.c χ).left) j →
        gm (jK R) z _ s = gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j) := by
      intro j
      let U := LB.wchart D.P.L (Y := Sp R) (fun _ : PUnit => (D.c χ).left) j
      have loc : ∀ V : {V : (Sp R).Opens // IsAffineOpen V ∧ V ≤ U}, ∃ s : Γ(Sp R, V.1)ˣ, jK R z ∈ V.1 →
          gm (jK R) z _ s = gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j) := by
        rintro ⟨V, hV, hU⟩
        have h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j :=
          fun y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hU hy) k
        obtain ⟨r, hr, e⟩ := H j V hV (Set.subset_univ _) (fun y hy => Set.mem_iInter.1 (hU hy) PUnit.unit) h
        refine ⟨hr.unit, fun hz => ?_⟩
        have e' : pullU (jK R) V hr.unit = res h ((D.psi χ).s j) := Units.ext e
        have p := gm_pull (𝟙 _) (jK R) z V hz hr.unit
        rw [Category.id_comp, e'] at p
        exact p.symm.trans (gm_res (𝟙 _) z h hz _)
      choose s hs using loc
      obtain ⟨a, ha⟩ := glue_unit U (fun V : {V : (Sp R).Opens // IsAffineOpen V ∧ V ≤ U} => V.1) (fun V => V.2.2)
        (fun y hy => by
          obtain ⟨_, ⟨V, hV, rfl⟩, hy', hle⟩ := (Sp R).isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
          exact Opens.mem_iSup.2 ⟨⟨V, hV, hle⟩, hy'⟩) s (fun V V' y hy => by
          have hz : jK R z ∈ V.1 ⊓ V'.1 := dn _ ⟨y, hy⟩
          have : res (inf_le_left : V.1 ⊓ V'.1 ≤ _) (s V) = res inf_le_right (s V') := inj _ hz
            ((gm_res _ z _ hz _).trans ((hs V hz.1).trans ((gm_res _ z _ hz _).trans (hs V' hz.2)).symm))
          exact (gm_res _ y inf_le_left hy _).symm.trans ((congrArg (gm _ y _) this).trans (gm_res _ y _ hy _)))
      refine ⟨a, fun hz => ?_⟩
      obtain ⟨_, ⟨V, hV, rfl⟩, hy', hle⟩ := (Sp R).isBasis_affineOpens.exists_subset_of_mem_open hz U.isOpen
      exact (gm_res _ z hle hy' a).symm.trans ((congrArg (gm _ z _) (ha ⟨V, hV, hle⟩)).trans (hs ⟨V, hV, hle⟩ hy'))
    choose s hs using glue
    refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => congrArg (gm _ y _) ?_, corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · have hz : jK R z ∈ LB.wchart D.P.L (Y := Sp R) (fun _ : PUnit => (D.c χ).left) j ⊓
          LB.wchart D.P.L (Y := Sp R) (fun _ : PUnit => (D.c χ).left) j' := dn _ ⟨y, hy⟩
      refine inj _ hz (((gm_res _ z _ hz _).trans (hs j hz.1)).trans (Eq.symm ?_))
      refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linComb D.P.L _ _ (jK R) z j j' hz.1 hz.2)
        ((gm_res _ z _ hz _).trans (hs j' hz.2)))).trans (Eq.symm ?_)
      refine (gen_trans (D.psi_gen χ) (𝟙 _) z (j' := j') (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz.1 k)
        (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz.2 k)).trans (congrArg₂ (· * ·) ?_ rfl)
      simp only [trF, Category.id_comp]
      rfl
    · obtain rfl : y = z := Subsingleton.elim _ _
      rw [val_pull hJ, Category.id_comp, val_of (D.psi χ) _ y J (fun _ => J (D.xK χ)) (fun _ => by rw [Category.id_comp])]
      exact hs _ (hJ.mem _ _)
  · rintro ⟨t, -, H⟩ j V _ _ hle h
    have le : V ≤ LB.wchart D.P.L (Y := Sp R) (fun _ : PUnit => (D.c χ).left) j :=
      fun y hy => Set.mem_iInter.2 fun k => hle hy
    refine ⟨(res le (t.s j)).val, Units.isUnit _, ?_⟩
    have : pullU (jK R) V (res le (t.s j)) = res h ((D.psi χ).s j) := unit_ext fun y hy => by
      refine (gm_pull (𝟙 _) (jK R) y V hy _).trans ((gm_res _ y le hy _).trans (Eq.trans ?_ (gm_res _ y h hy _).symm))
      exact (gm_pullGen D.P.L _ _ t (jK R) (𝟙 _) y j (h hy)).symm.trans
        (gm_corr D.P.L H (𝟙 _) y (j PUnit.unit) (h hy) (h hy))
    exact congrArg Units.val this

theorem nonempty_psiOn_top (D : DegPre R) (h : ∀ χ, PsiUnitOn D χ Set.univ) : Nonempty (PsiOn D ⊤) := by
  choose t ht H using fun χ => (psiUnitOn_univ_iff D χ).1 (h χ)
  refine ⟨⟨fun χ => LB.pullGen D.P.L _ _ (t χ) (⊤ : (Sp R).Opens).ι, fun χ => pullGen_isGen _ _ _ _ (ht χ) _,
    fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  refine (val_pull hJ _ _ _).trans ((val_pull hJ (t χ) _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  rw [← val_corr hJ (H χ), val_pull hJ, Category.assoc, Category.assoc, morphismRestrict_ι]

include hD in

theorem psiUnitOn_pull (hφ : Function.Injective φ) (x : D'.X) (h : PsiUnitOn D (hD.xe x) Set.univ) :
    PsiUnitOn D' x Set.univ := by
  obtain ⟨t, ht, H⟩ := (psiUnitOn_univ_iff D _).1 h
  obtain ⟨a, ha, va⟩ := exists_down_om hD.w_gen D.P.isLB D'.P.isLB (Y' := Sp R') (K := PUnit)
    (φ' := fun _ => (D'.c x).left) (spMap φ) (fun _ => hD.c_pr x) t ht
  refine (psiUnitOn_univ_iff D' x).2 ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
  have sq := fracMap_sq hφ
  have e := ((psi_val hD _ _ sq hJ hJ' x).symm.trans ((val_corr hJ H _).symm.trans ((val_pull hJ _ _ _).trans
    (congrArg (fun q => val t q y J) (sq.symm.trans (Category.assoc _ _ _).symm))))).trans
    (va _ (𝟙 _ ≫ jK R') y J J' hJ hJ')
  rw [Fintype.prod_unique, zpow_neg_one, Category.assoc] at e
  exact (val_pull hJ' _ _ _).trans (mul_left_cancel e).symm

end Inj

end GlobalTheory.ArcPull
