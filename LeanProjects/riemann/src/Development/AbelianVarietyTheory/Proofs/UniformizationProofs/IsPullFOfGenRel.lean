import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback

noncomputable section

namespace GlobalTheory.ArcSpecialise

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArcPull (om pmaps_om exists_down_om mul_push)
open GlobalTheory.ArcTransport (unitStk genRel_val cub_push GtRel)
open scoped CategoryTheory.Obj

section General

variable {X X' X'' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {Φ : X' ⟶ X} {Ψ : X'' ⟶ X'}
  {K : Type} [Fintype K]

theorem pmaps_of_val {w : LB.Iso L' (L.pull Φ)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')}
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ Φ = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} (ha : a.IsGen) {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (H : ∀ (y : Y') J J', Good L y J → Good L' y J' →
      val t h y J = (∏ k, om w y J J' (φ' k) ^ ε k) * val a (𝟙 _) y J') :
    PMaps w φ' φ ε a t h := by
  obtain ⟨a₁, ha₁, H₁⟩ := DegPull.exists_pmaps hw hL hL' h hψ t ht
  have e : ∀ j, a₁.s j = a.s j := fun j => unit_ext fun y hy => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' hL y
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' hL' y
    have v₀ := pmaps_om hψ H₁ (𝟙 _) y hJ hJ'
    simp only [Category.id_comp] at v₀
    have v : val a₁ (𝟙 _) y J' = val a (𝟙 _) y J' := mul_left_cancel (v₀.symm.trans (H y J J' hJ hJ'))
    exact (gen_trans ha₁ (𝟙 _) y hy (hJ'.mem _ _)).trans ((congrArg _ v).trans
      (gen_trans ha (𝟙 _) y hy (hJ'.mem _ _)).symm)
  intro Z r z p q hp hq
  exact (H₁ Z r z p q hp hq).trans (congrArg₂ (· * ·) rfl (congrArg (gm r z (LB.wchart L' φ' q)) (e q)))

theorem val_scale {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ (hJ.mem φ r) _) rfl)

theorem gm_unitOn_spMap {S F : Type} [CommRing S] [Field F] (r : S →+* F) (v : Sˣ) (y : Sp F) :
    gm (spMap r) y ⊤ (unitOn v) = unitStk y (Units.map r.toMonoidHom v) := by
  apply Units.ext
  rw [gm_val _ y ⊤ trivial]
  have nat := congrArg (fun q => q.hom v.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom r))
  exact congrArg ((Sp F).presheaf.germ ⊤ y trivial).hom nat.symm

variable {F : Type} [Field F]

theorem pmaps_of_genRel {w : LB.Iso L' (L.pull Φ)} {wD : LB.Iso L'' (L'.pull Ψ)} {w' : LB.Iso L'' (L.pull (Ψ ≫ Φ))}
    (T : Tri w wD w') (hw : PGen w) (hwD : PGen wD) (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB)
    {φ : K → (Y ⟶ X')} {pt₀ : K → (Sp F ⟶ X)} {pt : K → (Sp F ⟶ X'')} {ε : K → ℤ}
    {s : LB.Gen (LB.LinComb L' φ ε)} {t₀ : LB.Gen (LB.LinComb L pt₀ ε)} {t : LB.Gen (LB.LinComb L'' pt ε)}
    (hs : s.IsGen) (ht₀ : t₀.IsGen) (ht : t.IsGen) (π : Sp F ⟶ Y) (hπ : ∀ k, pt k ≫ Ψ = π ≫ φ k) (x : Fˣ)
    (H : ∀ (y : Sp F) J J', Good L y J → Good L' y J' →
      unitStk y x * vS t₀ y J = (∏ k, om w y J J' (π ≫ φ k) ^ ε k) * val s π y J')
    (H' : GenRel w' t t₀ (x : F)) : PMaps wD pt φ ε t s π := by
  refine pmaps_of_val hwD hL' hL'' hπ ht hs fun y J' J'' hJ' hJ'' => ?_
  obtain ⟨J, hJ⟩ := DegPull.exists_good' hL y
  have a := ((genRel_val (T.pgen_comp hL' hw hwD) hL hL'' ht ht₀ x).1 H').2 y J J'' hJ hJ''
  have b : ∀ k, Geo.Tor.gw w' (pt k) y (J (pt k ≫ Ψ ≫ Φ)) (J'' (pt k)) =
      om w y J J' (π ≫ φ k) * om wD y J' J'' (pt k) := fun k => by
    rw [← hπ k, om, om, Category.assoc]
    exact T _ (pt k) y _ _ _ (hJ (pt k ≫ Ψ ≫ Φ)) (hJ' (pt k ≫ Ψ)) (hJ'' (pt k))
  simp only [b, mul_zpow, Finset.prod_mul_distrib] at a
  rw [H y J J' hJ hJ', _root_.mul_assoc] at a
  exact (mul_left_cancel a).symm

end General

section Psi

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {D : DegPre R} {D' : DegPre R'}

theorem psiOn_generic {W : (Spec (CommRingCat.of R)).Opens} (ψ : PsiOn D W) (χ : D.X) {Z : Scheme.{0}}
    (r : Z ⟶ W.toScheme) (s : Z ⟶ (TK R).left) (h : r ≫ W.ι = s ≫ jK R) {z : Z} {J} (hJ : Good D.P.L z J) :
    val (ψ.psi χ) r z J = val (D.psi χ) s z J := by
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : Z ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = s ∧ lam ≫ (jK R ∣_ W) = r :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ h,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  have e := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψ.psi_eq χ) lam).trans (val_pull hJ _ _ _))
  rw [l₁, l₂] at e
  exact e

theorem psiOn_agree {W W' : (Spec (CommRingCat.of R)).Opens} (ψ : PsiOn D W) (ψ' : PsiOn D W') (χ : D.X)
    {Z : Scheme.{0}} (r : Z ⟶ W.toScheme) (r' : Z ⟶ W'.toScheme) (h : r ≫ W.ι = r' ≫ W'.ι) {z : Z} {J}
    (hJ : Good D.P.L z J) : val (ψ.psi χ) r z J = val (ψ'.psi χ) r' z J := by
  let m := (Spec (CommRingCat.of R)).homOfLE (inf_le_left : W ⊓ W' ≤ W)
  let m' := (Spec (CommRingCat.of R)).homOfLE (inf_le_right : W ⊓ W' ≤ W')
  have f₁ : m ≫ W.ι = (W ⊓ W').ι := Scheme.homOfLE_ι _ _
  have f₂ : m' ≫ W'.ι = (W ⊓ W').ι := Scheme.homOfLE_ι _ _
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Z ⟶ (W ⊓ W').toScheme, ρ ≫ (W ⊓ W').ι = r ≫ W.ι :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact ⟨(r y).2, (congrArg (fun q => q y ∈ W') h).mpr (r' y).2⟩), IsOpenImmersion.lift_fac _ _ _⟩
  have r₁ : ρ ≫ m = r := by rw [← cancel_mono W.ι, Category.assoc, f₁, hρ]
  have r₂ : ρ ≫ m' = r' := by rw [← cancel_mono W'.ι, Category.assoc, f₂, hρ, h]
  have key := PsiEvenPull.val_eq_of_app_injective D.P.isLB (u := LB.pullGen D.P.L _ _ (ψ.psi χ) m)
    (u' := LB.pullGen D.P.L _ _ (ψ'.psi χ) m') (fun V _ k => Finset.prod_congr rfl fun i _ => by
      show k (m' ≫ W'.ι ≫ (D.c χ).left) ^ _ = k (m ≫ W.ι ≫ (D.c χ).left) ^ _
      rw [← Category.assoc, ← Category.assoc, f₁, f₂])
    (jK R ∣_ (W ⊓ W')) (PsiEvenPull.app_injective_generic _) (pullGen_isGen _ _ _ _ (ψ.psi_gen χ) _)
    (pullGen_isGen _ _ _ _ (ψ'.psi_gen χ) _) (fun y I hI => by
      refine (val_pull hI _ _ _).trans (Eq.trans ?_ (val_pull hI _ _ _).symm)
      exact (psiOn_generic ψ χ _ (jK R ⁻¹ᵁ (W ⊓ W')).ι (by rw [Category.assoc, f₁, morphismRestrict_ι]) hI).trans
        (psiOn_generic ψ' χ _ (jK R ⁻¹ᵁ (W ⊓ W')).ι (by rw [Category.assoc, f₂, morphismRestrict_ι]) hI).symm)
    Z ρ z J hJ
  have k' := (val_pull hJ _ _ _).symm.trans (key.trans (val_pull hJ _ _ _))
  rw [r₁, r₂] at k'
  exact k'

theorem pmaps_psiOn {g : R →+* R'} (hD : IsPullDeg g D D') {Wo : (Spec (CommRingCat.of R)).Opens} (ψ : PsiOn D Wo)
    {Y : Scheme.{0}} (s : Y ⟶ (TK R').left) (zo : Y ⟶ (TW Wo).left) (hz : zo ≫ Wo.ι = s ≫ jK R' ≫ specOf g)
    (x : D'.X) :
    (s ≫ D'.xK x) ≫ PsiEvenPull.proj hD = 𝟙 _ ≫ zo ≫ (toUnit (TW Wo) ≫ D.c (hD.xe x)).left ∧
    PMaps hD.w (K := PUnit) (fun _ => s ≫ D'.xK x) (fun _ => zo ≫ (toUnit (TW Wo) ≫ D.c (hD.xe x)).left)
      (fun _ => -1) (LB.pullGen _ _ _ (D'.psi x) s) (LB.pullGen _ _ _ (ψ.psi (hD.xe x)) zo) (𝟙 _) := by
  have hp : (s ≫ D'.xK x) ≫ PsiEvenPull.proj hD = 𝟙 _ ≫ zo ≫ (toUnit (TW Wo) ≫ D.c (hD.xe x)).left := by
    have hx : D'.xK x ≫ PsiEvenPull.proj hD = jK R' ≫ specOf g ≫ (D.c (hD.xe x)).left := by
      rw [← hD.c_pr x, ← Category.assoc]; rfl
    show _ = 𝟙 _ ≫ zo ≫ Wo.ι ≫ (D.c (hD.xe x)).left
    rw [Category.id_comp, ← Category.assoc zo, hz, Category.assoc, hx]
    simp only [Category.assoc]
  refine ⟨hp, pmaps_of_val ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (fun _ => hp)
    (pullGen_isGen _ _ _ _ (D'.psi_gen _) _) (pullGen_isGen _ _ _ _ (ψ.psi_gen _) _) fun y J J' hJ hJ' => ?_⟩
  rw [val_pull hJ, val_pull hJ', Category.id_comp, Category.id_comp, Fintype.prod_unique, zpow_neg_one]
  refine (psiOn_agree ψ hD.psiW _ zo (s ≫ hD.g) (by rw [hz, Category.assoc, hD.g_comm]) hJ).trans ?_
  exact PsiEvenPull.psi_pull hD x s y hJ hJ'

end Psi

section Gt

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {Φ : D'.P.A.left ⟶ D.P.A.left}

theorem prod_gtT {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (DegPre.gtφT D T b χ i) ^ DegPre.gtε i =
      (h (cP D _ χ * b).left)⁻¹ * h (cP D _ χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  show h (cP D _ χ * b).left ^ (-1 : ℤ) * h (cP D _ χ).left ^ (1 : ℤ) * h b.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem gtφT_hom {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) (i : Fin 4) :
    DegPre.gtφT D T b χ i ≫ D.P.A.hom = T.hom := by
  fin_cases i <;> exact Over.w _

theorem gtφT_push (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ) {χ : D.X} {χ' : D'.X}
    (hc : (D'.c χ').left ≫ Φ = spMap f ≫ (D.c χ).left) {T : Over (Sp R)} {T' : Over (Sp R')} (h : T'.left ⟶ T.left)
    {b' : T' ⟶ D'.P.A} {b : T ⟶ D.P.A} (hb : b'.left ≫ Φ = h ≫ b.left) (i : Fin 4) :
    DegPre.gtφT D' T' b' χ' i ≫ Φ = h ≫ DegPre.gtφT D T b χ i := by
  have hh : T'.hom ≫ spMap f = h ≫ T.hom := by
    rw [← Over.w b, ← Category.assoc, ← hb, Category.assoc, gp.1.w, ← Category.assoc, Over.w]
  have c₁ : (cP D' T' χ').left ≫ Φ = h ≫ (cP D T χ).left := by
    show (T'.hom ≫ (D'.c χ').left) ≫ Φ = h ≫ T.hom ≫ (D.c χ).left
    rw [Category.assoc, hc, ← Category.assoc, hh, Category.assoc]
  have c₀ : (1 : T' ⟶ D'.P.A).left ≫ Φ = h ≫ (1 : T ⟶ D.P.A).left := by
    show (T'.hom ≫ eSec D'.P.A) ≫ Φ = h ≫ T.hom ≫ eSec D.P.A
    have he : eSec D'.P.A ≫ Φ = spMap f ≫ eSec D.P.A := (cubeMapOf gp).e_comm
    rw [Category.assoc, he, ← Category.assoc, hh, Category.assoc]
  fin_cases i
  exacts [mul_push gp h c₁ hb, c₁, hb, c₀]

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_gtPt (hG : GlobalFnsSt) (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ)
    {w : LB.Iso D'.P.L (D.P.L.pull Φ)} (hw : w.IsGen) {e : D.X ≃+ D'.X}
    (hc : ∀ y, (D'.c (e y)).left ≫ Φ = spMap f ≫ (D.c y).left) (g₀ : GtPtF D F) (T : Over (Sp R'))
    (h : T.left ⟶ Sp F) (hh : T.hom ≫ spMap f = h ≫ (TF (R := R) F).hom) (u : D.X → Γ(T.left, ⊤)ˣ)
    (hu : ∀ a b, u (a + b) = u a * u b) :
    ∃ g : GtPt D' T, g.b.left ≫ Φ = h ≫ g₀.b.left ∧ ∀ χ χ', e χ = χ' →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
        gm r z ⊤ (u χ) * val (g₀.s χ) (r ≫ h) z J =
          (∏ i, om w z J J' (r ≫ DegPre.gtφT D' T g.b χ' i) ^ DegPre.gtε i) * val (g.s χ') r z J' := by
  let b : T ⟶ D'.P.A := Over.homMk (gp.1.lift (h ≫ g₀.b.left) T.hom (by rw [Category.assoc, Over.w, hh]))
    (gp.1.lift_snd _ _ _)
  have hb : b.left ≫ Φ = h ≫ g₀.b.left := gp.1.lift_fst _ _ _
  have u0 : u 0 = 1 := mul_eq_left.1 ((hu 0 0).symm.trans (congrArg u (add_zero 0)))
  have ex : ∀ χ', ∃ s : LB.Gen (LB.LinComb D'.P.L (DegPre.gtφT D' T b χ') DegPre.gtε), s.IsGen ∧ ∀ χ, e χ = χ' →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
        gm r z ⊤ (u χ) * val (g₀.s χ) (r ≫ h) z J =
          (∏ i, om w z J J' (r ≫ DegPre.gtφT D' T b χ' i) ^ DegPre.gtε i) * val s r z J' := by
    intro χ'
    obtain ⟨χ, rfl⟩ := e.surjective χ'
    obtain ⟨a, ha, va⟩ := exists_down_om hw D.P.isLB D'.P.isLB (Y := (TF (R := R) F).left) h
      (gtφT_push gp (hc χ) (T := TF (R := R) F) h hb) (g₀.s χ) (g₀.isGen χ)
    refine ⟨scaleGen (u χ) a, scaleGen_isGen _ _ ha, fun χ₁ h₁ Z r z J J' hJ hJ' => ?_⟩
    obtain rfl := e.injective h₁
    rw [val_scale _ _ _ hJ', mul_left_comm]
    exact congrArg₂ (· * ·) rfl (va Z r z J J' hJ hJ')
  choose s hs vs using ex
  have vs' : ∀ χ (y : T.left) J J', Good D.P.L y J → Good D'.P.L y J' →
      gm (𝟙 _) y ⊤ (u χ) * val (g₀.s χ) h y J = (om w y J J' (cP D' _ (e χ) * b).left)⁻¹ *
        om w y J J' (cP D' _ (e χ)).left * om w y J J' b.left * (om w y J J' (1 : T ⟶ D'.P.A).left)⁻¹ *
        val (s (e χ)) (𝟙 _) y J' := fun χ y J J' hJ hJ' => by
    have v := vs _ χ rfl _ (𝟙 _) y J J' hJ hJ'
    simp only [Category.id_comp] at v
    exact v.trans (congrArg₂ (· * ·) (prod_gtT b (e χ) (om w y J J')) rfl)
  refine ⟨⟨b, s, hs, corr_of_val D'.P.isLB fun y J' hJ' => ?_, fun χ χ' => corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩,
    hb, fun χ χ' h => vs χ' χ h⟩
  · obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have z : val (g₀.s 0) h y J = 1 := (val_corr hJ g₀.s_zero _).trans (val_one _)
    have v := vs' 0 y J J' hJ hJ'
    rw [z, u0, map_one, _root_.mul_one, map_zero e, cPoint_zero, _root_.one_mul] at v
    rw [val_one]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul v
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    obtain ⟨χ, rfl⟩ := e.surjective χ
    obtain ⟨χ', rfl⟩ := e.surjective χ'
    let σ : Over.mk (T.hom ≫ spMap f) ⟶ TF (R := R) F := Over.homMk h hh.symm
    have e₀ := gt_mul σ hJ g₀ χ χ'
    have c := cub_push hG gp ((isGen_iff w).1 hw) (T' := T) hJ hJ' (cP D' _ (e χ)) (cP D' _ (e χ')) b
    have pc : ∀ x, (cP D' T (e x)).left ≫ Φ = (cP D (Over.mk (T.hom ≫ spMap f)) x).left := fun x => by
      show (T.hom ≫ (D'.c (e x)).left) ≫ Φ = (T.hom ≫ spMap f) ≫ (D.c x).left
      rw [Category.assoc, hc, Category.assoc]
    have q : (lift (cP D' T (e χ)) (lift (cP D' T (e χ')) b)).left ≫ (cubeMapOf gp).F3 =
        (lift (cP D (Over.mk (T.hom ≫ spMap f)) χ) (lift (cP D _ χ') (σ ≫ g₀.b))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i
      · simp only [x3]; simpa using (show _ ≫ (cubeMapOf gp).F = _ from pc χ)
      · simp only [x3]; simpa using (show _ ≫ (cubeMapOf gp).F = _ from pc χ')
      · simp only [x3]; simpa using (show _ ≫ (cubeMapOf gp).F = σ.left ≫ _ from hb)
    rw [q] at c
    have c' := c.trans (congrArg₂ (· * ·) (prod_cub (cP D' _ (e χ)) (cP D' _ (e χ')) b (om w y J J')) rfl)
    have e₁ : val (g₀.s (χ + χ')) h y J * _ = val (g₀.s χ) h y J * val (g₀.s χ') h y J :=
      (congrArg₂ (· * ·) rfl c'.symm).trans e₀
    have k := val_cub D'.cub (𝟙 T) hJ' (cP D' _ (e χ)) (cP D' _ (e χ')) b
    rw [Category.id_comp, Category.id_comp, Category.id_comp] at k
    refine (val_mul hJ' _ _ _).trans (((congrArg₂ (· * ·) rfl k).trans ?_).trans (val_mul hJ' _ _ _).symm)
    have v₁ := vs' χ y J J' hJ hJ'
    have v₂ := vs' χ' y J J' hJ hJ'
    have v₃ := vs' (χ + χ') y J J' hJ hJ'
    rw [map_add e, cPoint_add, hu, map_mul] at v₃
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul e₁
    have b₁ := congrArg Additive.ofMul v₁
    have b₂ := congrArg Additive.ofMul v₂
    have b₃ := congrArg Additive.ofMul v₃
    simp only [ofMul_mul, ofMul_inv] at a₁ b₁ b₂ b₃ ⊢
    linear_combination (norm := abel) a₁ + b₁ + b₂ - b₃

theorem isPullF_of_genRel (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ) {w : LB.Iso D'.P.L (D.P.L.pull Φ)}
    (hw : w.IsGen) {e : D.X ≃+ D'.X} {g₀ : GtPtF D F} {T : Over (Sp R')} {h : T.left ⟶ Sp F}
    {u : D.X → Γ(T.left, ⊤)ˣ} {g : GtPt D' T} (hb : g.b.left ≫ Φ = h ≫ g₀.b.left)
    (hv : ∀ χ χ', e χ = χ' →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
        gm r z ⊤ (u χ) * val (g₀.s χ) (r ≫ h) z J =
          (∏ i, om w z J J' (r ≫ DegPre.gtφT D' T g.b χ' i) ^ DegPre.gtε i) * val (g.s χ') r z J')
    {F₁ : Type} [Field F₁] [Algebra (FractionRing R) F₁] [Algebra (FractionRing R') F₁] (r : Sp F₁ ⟶ T.left)
    (hr : r ≫ T.hom = (TF (R := R') F₁).hom)
    {g₁ : GtPtF D F₁} (hb₁ : g₁.b.left = (r ≫ h) ≫ g₀.b.left)
    (hs₁ : ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g₁.s χ) (LB.pullGen D.P.L _ _ (g₀.s χ) (r ≫ h)))
    {v : D.X → F₁ˣ} (huv : ∀ χ (y : Sp F₁), gm r y ⊤ (u χ) = unitStk y (v χ))
    {g' : GtPtF D' F₁} (H : GtRel w e v g₁ g') : GtPt.IsPullF F₁ r g g' := by
  let ρ : TF (R := R') F₁ ⟶ T := Over.homMk r hr
  have hb' : g'.b.left = r ≫ g.b.left := by
    refine gp.1.hom_ext ?_ ?_
    · exact ((H 0).1 2).trans (hb₁.trans ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hb.symm).trans
        (Category.assoc _ _ _).symm)))
    · exact (Over.w g'.b).trans (Over.w (ρ ≫ g.b)).symm
  refine ⟨hb', fun χ' => corr_of_val D'.P.isLB fun (y : Sp F₁) J' hJ' => ?_⟩
  obtain ⟨χ, rfl⟩ := e.surjective χ'
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
  have hb'' : g'.b = ρ ≫ g.b := Over.OverMorphism.ext hb'
  have pt : ∀ i, DegPre.gtφ D' F₁ g'.b (e χ) i = r ≫ DegPre.gtφT D' T g.b (e χ) i := fun i => by
    rw [hb'']
    fin_cases i
    · exact congrArg (fun q => q.left) ((congrArg (· * (ρ ≫ g.b)) (comp_cP D' ρ _).symm).trans
        (MonObj.comp_mul ρ (cP D' T (e χ)) g.b).symm)
    · exact congrArg (fun q => q.left) (comp_cP D' ρ _).symm
    · rfl
    · exact congrArg (fun q : TF (R := R') F₁ ⟶ D'.P.A => q.left) (MonObj.comp_one (M := D'.P.A) ρ).symm
  have a := ((genRel_val ((isGen_iff w).1 hw) D.P.isLB D'.P.isLB (g'.isGen _) (g₁.isGen _) (v χ)).1 (H χ)).2
    y J J' hJ hJ'
  have c := hv χ _ rfl _ r y J J' hJ hJ'
  have d : vS (g₁.s χ) y J = val (g₀.s χ) (r ≫ h) y J :=
    (val_corr hJ (hs₁ χ) _).trans ((val_pull hJ _ _ _).trans
      (congrArg (fun q => val (g₀.s χ) q y J) (Category.id_comp _)))
  have a' : (∏ i, om w y J J' (r ≫ DegPre.gtφT D' T g.b (e χ) i) ^ DegPre.gtε i) * vS (g'.s (e χ)) y J' =
      gm r y ⊤ (u χ) * val (g₀.s χ) (r ≫ h) y J :=
    (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => congrArg (fun q => om w y J J' q ^ DegPre.gtε i)
      (pt i).symm) rfl).trans (a.trans (congrArg₂ (· * ·) (huv χ y).symm d))
  exact (mul_left_cancel (a'.trans c)).trans ((congrArg (fun q => val (g.s (e χ)) q y J') (Category.id_comp r).symm).trans
    (val_pull hJ' _ _ _).symm)

end Gt

section ThetaShiftProofs

open NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem exists_lift_open {S F : Type} [CommRing S] [IsLocalRing S] [Field F] (π : S →+* F) [IsLocalHom π] (κ : F →+* S)
    (hπ : spMap π ≫ spMap κ = 𝟙 _) (ξ : Sp S ⟶ Y.X) (yF : Sp F ⟶ Xo.XF c) (h₁ : yF ≫ Y.j = spMap π ≫ ξ)
    (h₂ : ξ ≫ Y.s = spMap κ ≫ spMap π ≫ ξ ≫ Y.s) : ∃ yS : Sp S ⟶ Xo.XF c, yS ≫ Y.j = ξ ∧ spMap π ≫ yS = yF := by
  have h₁' : yF ≫ Y.jQ ≫ pullback.fst _ _ = spMap π ≫ ξ := h₁
  let ℓ : Sp S ⟶ pullback Y.s (spMap β) := pullback.lift ξ (spMap κ ≫ yF ≫ Y.jQ ≫ pullback.snd _ _) (by
    rw [h₂]
    simp only [Category.assoc, ← pullback.condition]
    rw [reassoc_of% h₁'])
  have ℓ₁ : ℓ ≫ pullback.fst _ _ = ξ := pullback.lift_fst _ _ _
  have ℓ₂ : ℓ ≫ pullback.snd _ _ = spMap κ ≫ yF ≫ Y.jQ ≫ pullback.snd _ _ := pullback.lift_snd _ _ _
  have hℓ : spMap π ≫ ℓ = yF ≫ Y.jQ := by
    apply pullback.hom_ext
    · rw [Category.assoc, ℓ₁, Category.assoc, h₁']
    · rw [Category.assoc, ℓ₂, ← Category.assoc, hπ, Category.id_comp, Category.assoc]
  have := Y.jQ_open
  have hr : Set.range ℓ ⊆ Set.range Y.jQ := by
    rintro _ ⟨x, rfl⟩
    have h0 : ℓ (IsLocalRing.closedPoint S) ∈ Set.range Y.jQ := by
      rw [← IsLocalRing.comap_closedPoint π]
      exact ⟨yF (IsLocalRing.closedPoint F), (congrArg (fun q => q (IsLocalRing.closedPoint F)) hℓ).symm⟩
    exact ((IsLocalRing.specializes_closedPoint x).map ℓ.continuous).mem_open Y.jQ.isOpenEmbedding.isOpen_range h0
  refine ⟨IsOpenImmersion.lift Y.jQ ℓ hr, ?_, ?_⟩
  · show _ ≫ Y.jQ ≫ pullback.fst _ _ = ξ
    rw [← Category.assoc, IsOpenImmersion.lift_fac, ℓ₁]
  · rw [← cancel_mono Y.jQ, Category.assoc, IsOpenImmersion.lift_fac, hℓ]

variable {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R]
  [IsDomain R] {I : Ideal R} {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X}

theorem dvd_be (a : ArcIn D l β O' b) {n : ℕ} (hn : n ∣ l.M') (y z : a.D₀.X) : (n : ℤ) ∣ a.be y z :=
  ((Int.natCast_dvd_natCast.2 hn).mul_left 2).trans (a.be_dvd y z)

theorem be_half (a : ArcIn D l β O' b) (x y : a.D₀.X) :
    a.be (x + y) (x + y) / 2 = a.be x y + a.be x x / 2 + a.be y y / 2 := by
  have h₁ : (2 : ℤ) ∣ a.be x x := (Dvd.intro _ rfl).trans (a.be_dvd x x)
  have h₂ : (2 : ℤ) ∣ a.be y y := (Dvd.intro _ rfl).trans (a.be_dvd y y)
  have h₃ := a.be_symm y x
  simp only [map_add, LinearMap.add_apply]
  omega

theorem exists_partner (hG : GlobalFnsSt) (W : ArcWit Y a I f u χ) {F : Type} [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] (v : Fˣ)
    (hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x)))
    (hv : (v : F) = algebraMap (FractionRing R) F (algebraMap R _ u)) {n : ℕ} (hn : n ∣ l.M') (q₀ : QkPt a.D₀ F n) :
    ∃ q : QkPt W.P.D.toPre F n, q.y = W.e q₀.y ∧
      GtRel W.w W.e.toAddEquiv (fun z => v ^ (a.be q₀.y z / n)) q₀.g q.g := by
  obtain ⟨gp, hw, hr, -, hc, hψ⟩ := W.spec
  have hT := ArcTransport.base_comm hF
  have hw' := (isGen_iff W.w).1 hw
  have ex : ∀ (i : ℕ) (g₀ : GtPtF a.D₀ F), ∃ g : GtPtF W.P.D.toPre F,
      GtRel W.w W.e.toAddEquiv (fun z => v ^ ((i : ℤ) * (a.be q₀.y z / n))) g₀ g :=
    fun i g₀ => ArcTransport.exists_gtRel gp hT (e := W.e.toAddEquiv) hc hw' hG _ (fun x y => by
      rw [map_add, Int.add_ediv_of_dvd_left (dvd_be a hn _ _), mul_add, zpow_add]) g₀
  choose dn hdn using ex
  obtain ⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩ := q₀.eq
  refine ⟨⟨W.e q₀.y, dn 1 q₀.g, dn n h, ⟨fun i => dn i (gs i), ?_, fun i => ?_, congrArg (dn n) gl⟩, ?_⟩, rfl, ?_⟩
  · exact GtRel.isZero gp hT (e := W.e.toAddEquiv) hc hw' (fun χ => by simp) (hdn _ _) g₀
  · refine GtRel.isAdd gp hT (e := W.e.toAddEquiv) hc hw' hG (fun χ => ?_) (hdn _ _) (hdn _ _) (hdn _ _) (gst i)
    rw [← zpow_add, ← add_mul]
    simp
  · have := hdn n h
    simp only [Int.mul_ediv_cancel' (dvd_be a hn _ _)] at this
    refine GtRel.isIota gp hT (e := W.e.toAddEquiv) hc hw' hr (v := fun y => v ^ (a.be y y / 2)) (fun χ => ?_)
      (fun χ => ?_) this hι
    · rw [Units.val_zpow_eq_zpow_val]
      exact (hψ F v hF hv).1 χ
    · rw [be_half, zpow_add, zpow_add]
  · have := hdn 1 q₀.g
    simp only [Nat.cast_one, _root_.one_mul] at this
    exact this

end ThetaShiftProofs

end GlobalTheory.ArcSpecialise
