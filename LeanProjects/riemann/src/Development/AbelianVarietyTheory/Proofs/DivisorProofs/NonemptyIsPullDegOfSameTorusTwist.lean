import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValPsiZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Uniq

section General

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {J : Type} [Fintype J]

theorem exists_cancel_linComb (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB) (pr : J → (X' ⟶ X)) (ε : J → ℤ)
    (F : X'' ⟶ X') (pr'' : J → (X'' ⟶ X)) (hpr : ∀ i, pr'' i = F ≫ pr i)
    (w : LB.Iso L' (LB.LinComb L pr ε)) (hw : w.IsGen) (w'' : LB.Iso L'' (LB.LinComb L pr'' ε)) (hw'' : w''.IsGen) :
    ∃ w' : LB.Iso L'' (L'.pull F), PGen w' ∧ ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : J → L.ι) (i : L'.ι) (k : L''.ι),
      f y ∈ LB.wchart L pr'' j → F (f y) ∈ L'.U i → f y ∈ L''.U k →
      gv w'' f y j k = gv w (f ≫ F) y j i * gw w' f y i k := by
  obtain rfl : pr'' = fun i => F ≫ pr i := funext hpr
  have hN := DVR.linComb_isLB L hL pr ε
  have up : ∀ (x : X'') (j : J → L.ι), F x ∈ LB.wchart L pr j → x ∈ LB.wchart L (fun i => F ≫ pr i) j :=
    fun x j h => Set.mem_iInter.2 fun i => Set.mem_iInter.1 h i
  have down : ∀ (x : X'') (j : J → L.ι), x ∈ LB.wchart L (fun i => F ≫ pr i) j → F x ∈ LB.wchart L pr j :=
    fun x j h => Set.mem_iInter.2 fun i => Set.mem_iInter.1 h i
  let v : LB.Iso L'' ((LB.LinComb L pr ε).pull (F ≫ 𝟙 X')) :=
    ⟨fun p => res (fun y hy => ⟨up y _ (mem_pull₂.1 hy.1), hy.2⟩ :
      ((LB.LinComb L pr ε).pull (F ≫ 𝟙 X')).U p.1 ⊓ L''.U p.2 ≤
        LB.wchart L (fun i => F ≫ pr i) (p.1 PUnit.unit) ⊓ L''.U p.2) (w''.s (p.1 PUnit.unit, p.2))⟩
  have hv : ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : J → L.ι) (k : L''.ι), F (f y) ∈ LB.wchart L pr j →
      f y ∈ L''.U k → gw v f y j k = gv w'' f y j k := fun Y f y j k hj hk =>
    gm_res f y _ (show f y ∈ ((LB.LinComb L pr ε).pull (F ≫ 𝟙 X')).U (fun _ => j) ⊓ L''.U k from
      ⟨mem_pull₂.2 hj, hk⟩) _
  have gv' : PGen v := by
    intro Y f y j j' k k' hj hj' hk hk'
    have hj₀ : F (f y) ∈ LB.wchart L pr j := hj
    have hj₀' : F (f y) ∈ LB.wchart L pr j' := hj'
    rw [hv Y f y j k hj₀ hk, hv Y f y j' k' hj₀' hk']
    refine (gm_isGen hw'' f y j j' k k' (up _ _ hj₀) (up _ _ hj₀') hk hk').trans ?_
    refine congrArg (fun a => a * _ * _) ?_
    refine (gm_linComb L _ ε f y j j' (up _ _ hj₀) (up _ _ hj₀')).trans
      (Eq.trans ?_ (gm_linComb L pr ε (f ≫ F ≫ 𝟙 X') y j j' hj₀ hj₀').symm)
    simp only [Category.comp_id, Category.assoc]
  obtain ⟨w', T⟩ := exists_cancel hN (isoPullId w rfl) v (isoPullId_pgen hw rfl) gv' hL' hL''
  refine ⟨w', T.pgen_cancel hN (isoPullId_pgen hw rfl) gv', fun Y f y j i k hj hi hk => ?_⟩
  have e := T Y f y j i k (down _ _ hj) hi hk
  rwa [hv Y f y j k (down _ _ hj) hk, gw_isoPullId w rfl (f ≫ F) y j i (down _ _ hj) hi] at e

theorem gm_mapsAtExp {Y : Scheme.{0}} {pr : J → (X' ⟶ X)} {ε : J → ℤ} {w : LB.Iso L' (LB.LinComb L pr ε)} {p : Y ⟶ X'}
    {n : ℤ} {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n))}
    {b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun i => n * ε i))} (h : MapsAtExp L L' pr ε w p n a b)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (j : J → L.ι) (i : L'.ι) (hj : p (r z) ∈ LB.wchart L pr j)
    (hi : p (r z) ∈ L'.U i) :
    gm r z (LB.wchart L (fun i => p ≫ pr i) j) (b.s j) =
      gv w (r ≫ p) z j i ^ n * gm r z (LB.wchart L' (fun _ : PUnit => p) (fun _ => i)) (a.s (fun _ => i)) := by
  have hm : r z ∈ p ⁻¹ᵁ (LB.div (LB.LinComb L pr ε) L').U (j, i) := ⟨hj, hi⟩
  have e := congrArg (gm r z _) (h j i)
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  exact (map_zpow _ _ _).trans (congrArg (· ^ n) (gm_pull r p z _ hm _))

theorem pmaps_of_mapsAtExp (hL : L.IsLB) {pr : J → (X' ⟶ X)} {ε : J → ℤ} {F : X'' ⟶ X'} {pr'' : J → (X'' ⟶ X)}
    (hpr : ∀ i, pr'' i = F ≫ pr i) {w : LB.Iso L' (LB.LinComb L pr ε)} {w'' : LB.Iso L'' (LB.LinComb L pr'' ε)}
    {w' : LB.Iso L'' (L'.pull F)}
    (T : ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : J → L.ι) (i : L'.ι) (k : L''.ι),
      f y ∈ LB.wchart L pr'' j → F (f y) ∈ L'.U i → f y ∈ L''.U k →
      gv w'' f y j k = gv w (f ≫ F) y j i * gw w' f y i k)
    {Y : Scheme.{0}} {p : Y ⟶ X'} {p'' : Y ⟶ X''} (hp : p'' ≫ F = p) {n : ℤ}
    {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n))}
    {a'' : LB.Gen (LB.LinComb L'' (K := PUnit) (fun _ => p'') (fun _ => n))}
    {b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun i => n * ε i))}
    {b'' : LB.Gen (LB.LinComb L (K := J) (fun i => p'' ≫ pr'' i) (fun i => n * ε i))}
    (h : MapsAtExp L L' pr ε w p n a b) (h'' : MapsAtExp L L'' pr'' ε w'' p'' n a'' b'')
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι), Good L z I → val b r z I = val b'' r z I) :
    PMaps w' (K := PUnit) (fun _ => p'') (fun _ => p) (fun _ => n) a'' a (𝟙 Y) := by
  obtain rfl : pr'' = fun i => F ≫ pr i := funext hpr
  subst hp
  intro Z r z P Q hP hQ
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have e := H Z r z I hI
  rw [val_of b r z I (fun i => I (r ≫ p'' ≫ F ≫ pr i)) (fun i => by rw [Category.assoc]),
    val_of b'' r z I (fun i => I (r ≫ p'' ≫ F ≫ pr i)) (fun i => rfl)] at e
  have m : ∀ i, pr i (F (p'' (r z))) ∈ L.U (I (r ≫ p'' ≫ F ≫ pr i)) := fun i => hI (r ≫ p'' ≫ F ≫ pr i)
  rw [gm_mapsAtExp h r z _ (P PUnit.unit) (Set.mem_iInter.2 m) (hP PUnit.unit),
    gm_mapsAtExp h'' r z _ (Q PUnit.unit) (Set.mem_iInter.2 m) (hQ PUnit.unit),
    T Z (r ≫ p'') z _ (P PUnit.unit) (Q PUnit.unit) (Set.mem_iInter.2 m) (hP PUnit.unit) (hQ PUnit.unit),
    mul_zpow, Category.assoc, _root_.mul_assoc] at e
  rw [Category.comp_id, Fintype.prod_unique]
  exact mul_left_cancel e

theorem pmaps_of_dense {Y Z₀ : Scheme.{0}} [IsReduced Y] (h : Z₀ ⟶ Y) (z₀ : Z₀)
    (hd : ∀ V : Y.Opens, (V : Set Y).Nonempty → h z₀ ∈ V) {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} {φ' : Y ⟶ X'}
    {φ : Y ⟶ X} (hφ : φ' ≫ F = φ) {a : LB.Gen (L'.pull φ')} {t : LB.Gen (L.pull φ)}
    (H : ∀ (p : L.ι) (q : L'.ι), φ (h z₀) ∈ L.U p → φ' (h z₀) ∈ L'.U q →
      gm h z₀ (LB.wchart L (fun _ : PUnit => φ) (fun _ => p)) (t.s (fun _ => p)) =
        gw w (h ≫ φ') z₀ p q * gm h z₀ (LB.wchart L' (fun _ : PUnit => φ') (fun _ => q)) (a.s (fun _ => q))) :
    PMaps w (K := PUnit) (fun _ => φ') (fun _ => φ) (fun _ => 1) a t (𝟙 Y) := by
  subst hφ
  intro Z r z P Q hP hQ
  let V : Y.Opens := LB.wchart L (fun _ : PUnit => φ' ≫ F) P ⊓ LB.wchart L' (fun _ : PUnit => φ') Q
  have l : V ≤ φ' ⁻¹ᵁ ((L.pull F).U (fun _ => P PUnit.unit) ⊓ L'.U (Q PUnit.unit)) := fun y hy =>
    ⟨mem_pull.2 (Set.mem_iInter.1 hy.1 PUnit.unit), Set.mem_iInter.1 hy.2 PUnit.unit⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ V →
      gm r z V (res (inf_le_left : V ≤ _) (t.s P)) = gm r z (LB.wchart L (fun _ : PUnit => φ' ≫ F) P) (t.s P) ∧
      gm r z V (res l (pullU φ' _ (w.s (fun _ => P PUnit.unit, Q PUnit.unit))) * res (inf_le_right : V ≤ _) (a.s Q)) =
        gw w (r ≫ φ') z (P PUnit.unit) (Q PUnit.unit) * gm r z (LB.wchart L' (fun _ : PUnit => φ') Q) (a.s Q) :=
    fun Z r z hz => ⟨gm_res r z _ hz _, (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z l hz _).trans (gm_pull r φ' z _ (l hz) _)) (gm_res r z _ hz _))⟩
  have hz : r z ∈ V := ⟨Set.mem_iInter.2 hP, Set.mem_iInter.2 hQ⟩
  have hz₀ : h z₀ ∈ V := hd V ⟨_, hz⟩
  have e := TauPull.gm_injective_of_dense h z₀ hd V hz₀ ((key _ h z₀ hz₀).1.trans
    ((H (P PUnit.unit) (Q PUnit.unit) (Set.mem_iInter.1 hz₀.1 PUnit.unit) (Set.mem_iInter.1 hz₀.2 PUnit.unit)).trans
      (key _ h z₀ hz₀).2.symm))
  rw [Category.comp_id, Fintype.prod_unique, zpow_one]
  exact (key _ r z hz).1.symm.trans ((congrArg (gm r z V) e).trans (key _ r z hz).2)

end General

variable {R : Type} [CommRing R] [IsDomain R]

theorem xK_zero (D : DegPre R) : D.xK 0 = jK R ≫ eSec D.P.A := by
  have c0 : (D.c 0).left = eSec D.P.A := by
    have := PsiZero.cPoint_zero' D (𝟙_ _)
    rw [DVR.cP, toUnit_unit, Category.id_comp, Hom.one_def, toUnit_unit, Category.id_comp] at this
    rw [this]; rfl
  rw [← c0]; rfl

theorem gm_psi_zero {D : DegPre R} (hB : D.TauBimult) (χ : D.X) (hχ : χ = 0) (y : (TK R).left) (j : D.P.L.ι)
    (hj : eSec D.P.A (jK R y) ∈ D.P.L.U j) :
    gm (𝟙 _) y (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => j)) ((D.psi χ).s (fun _ => j)) =
      (gm (jK R) y (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => j)) (D.rig.s (fun _ => j)))⁻¹ := by
  subst hχ
  have hx := xK_zero D
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB y (K := PUnit) (fun _ => D.xK 0) (fun _ => j) (fun _ _ _ => rfl)
    (fun k => by rw [hx]; exact hj)
  have e := PsiZero.val_psi_zero hB hJ
  rwa [val_of (D.psi 0) _ y J (fun _ => j) (fun k => (congrArg J (Category.id_comp (D.xK 0))).trans (eJ k)),
    val_of D.rig _ y J (fun _ => j) (fun k => (congrArg J hx.symm).trans (eJ k))] at e

theorem twφ_comp (D₀ D₂ D : DegPre R) (Φ : D₂.P.A ⟶ D₀.P.A) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (i : Fin 3) : twφ D₂ D (Φ ≫ β) b i = Φ.left ≫ twφ D₀ D β b i := by
  have hu : Φ ≫ toUnit D₀.P.A = toUnit D₂.P.A := toUnit_unique _ _
  fin_cases i
  · show (padd D.P.A (Φ ≫ β) (toUnit D₂.P.A ≫ b)).left = (Φ ≫ padd D.P.A β (toUnit D₀.P.A ≫ b)).left
    rw [padd, padd, ← Category.assoc Φ, comp_lift, ← Category.assoc Φ, hu]
  · show (toUnit D₂.P.A ≫ b).left = (Φ ≫ toUnit D₀.P.A ≫ b).left
    rw [← hu, Category.assoc]
  · show (toUnit D₂.P.A ≫ η[D.P.A]).left = (Φ ≫ toUnit D₀.P.A ≫ η[D.P.A]).left
    rw [← hu, Category.assoc]

theorem nonempty_isPullDeg_of_isTwist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D₂ D : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g → Nonempty (IsPullDeg (RingHom.id R) D₀.toPre D₂.toPre) := by
  intro R _ _ _ hR D₀ D₂ D g ⟨β₀, x₀, m₀, c₀, w₀, g₀, ψ₀⟩ ⟨β₂, x₂, m₂, c₂, w₂, g₂, ψ₂⟩
  let Φ : D₂.toPre.P.A ≅ D₀.toPre.P.A := β₂ ≪≫ β₀.symm
  have mΦ : IsMonHom Φ.hom := inferInstanceAs (IsMonHom (β₂.hom ≫ β₀.inv))
  have hβ : β₂.hom = Φ.hom ≫ β₀.hom := by simp [Φ]
  have gp : IsGrpPullback D₂.toPre.P.A D₀.toPre.P.A (specOf (RingHom.id R)) Φ.hom.left :=
    (isGrpPullback_of_iso Φ).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D₀.toPre.P.A (specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) = Φ.hom.left := hF
  have hpr : ∀ i, twφ D₂.toPre D.toPre β₂.hom g.b i =
      (e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R))) ≫ twφ D₀.toPre D.toPre β₀.hom g.b i :=
    fun i => by rw [hF', hβ]; exact twφ_comp _ _ _ _ _ _ i
  obtain ⟨w, gw', T⟩ := exists_cancel_linComb D.toPre.P.isLB D₀.toPre.P.isLB D₂.toPre.P.isLB _ twε _ _ hpr w₀ g₀ w₂ g₂
  let xe : D₂.toPre.X ≃+ D₀.toPre.X := x₂.trans x₀.symm
  have hxe : ∀ χ, x₀ (xe χ) = x₂ χ := fun χ => x₀.apply_symm_apply _
  have hc : ∀ χ, D₂.toPre.c χ ≫ Φ.hom = D₀.toPre.c (xe χ) := fun χ => by
    rw [← cancel_mono β₀.hom, Category.assoc, ← hβ, c₂, c₀, hxe]
  have hc' : ∀ χ, (D₂.toPre.c χ).left ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) =
      (D₀.toPre.c (xe χ)).left := fun χ => by rw [hF', ← Over.comp_left, hc]
  have hx : ∀ χ, D₂.toPre.xK χ ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) =
      D₀.toPre.xK (xe χ) := fun χ => by
    show (jK R ≫ (D₂.toPre.c χ).left) ≫ _ = jK R ≫ (D₀.toPre.c (xe χ)).left
    rw [Category.assoc, hc']
  have hE : eSec D₂.toPre.P.A ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) =
      eSec D₀.toPre.P.A := by
    rw [hF', eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  have hψ : ∀ χ, PMaps w (K := PUnit) (fun _ => D₂.toPre.xK χ) (fun _ => D₀.toPre.xK (xe χ)) (fun _ => -1)
      (D₂.toPre.psi χ) (D₀.toPre.psi (xe χ)) (𝟙 _) := fun χ => by
    obtain ⟨t₀, a₀, b₀⟩ := ψ₀ (xe χ)
    obtain ⟨t₂, a₂, b₂⟩ := ψ₂ χ
    refine pmaps_of_mapsAtExp D.toPre.P.isLB hpr T (hx χ) a₀ a₂ fun Z r z I hI => ?_
    rw [val_corr hI b₀ r, val_corr hI b₂ r]
    have : ∀ a b : D.toPre.X, a = b →
        val (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi a) (LB.pullGen D.toPre.P.L _ _ (g.s a) (toUnit (TK R)).left)) r z I =
        val (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi b) (LB.pullGen D.toPre.P.L _ _ (g.s b) (toUnit (TK R)).left)) r z I := by
      rintro a b rfl; rfl
    exact this _ _ (hxe χ)
  obtain ⟨z₀⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have red : IsReduced (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  have hr : PMaps w (K := PUnit) (fun _ => eSec D₂.toPre.P.A) (fun _ => eSec D₀.toPre.P.A) (fun _ => 1)
      D₂.toPre.rig D₀.toPre.rig (𝟙 _) := by
    refine pmaps_of_dense (Z₀ := (TK R).left) (jK R) z₀ (TauPull.jK_mem z₀) hE fun p q hp hq => ?_
    have e := hψ 0 _ (𝟙 _) z₀ (fun _ => p) (fun _ => q)
      (fun _ => by
        show (D₂.toPre.xK 0 ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R))) z₀ ∈ _
        rw [hx, map_zero, xK_zero]; exact hp)
      (fun _ => by rw [xK_zero]; exact hq)
    rw [Category.id_comp, Fintype.prod_unique, gm_psi_zero D₀.tau_bimult _ (map_zero xe) z₀ p hp,
      gm_psi_zero D₂.tau_bimult _ rfl z₀ q hq, Category.id_comp, xK_zero, zpow_neg, zpow_one, ← mul_inv, inv_inj] at e
    exact e
  obtain ⟨W, hW, ⟨ψW⟩⟩ := psiOnExists R _ hR.1 D₀
  obtain ⟨hD, -⟩ := UnifUniq.exists_isPullDeg_id D₀.toPre D₂.toPre W hW ψW e me w ((isGen_iff _).2 gw') hE hr xe hc' hψ
  exact ⟨hD⟩

end GlobalTheory.MumCmp.Uniq
