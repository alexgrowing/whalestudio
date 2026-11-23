import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DegPull

section Transport

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem exists_down_val {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ} {ψ : K → (Y ⟶ X)} (hψ : ∀ k, φ' k ≫ F = ψ k)
    (t : LB.Gen (LB.LinComb L ψ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L ψ p →
        r z ∈ LB.wchart L' φ' q → gm r z (LB.wchart L ψ p) (t.s p) =
          pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  obtain rfl : (fun k => φ' k ≫ F) = ψ := funext hψ
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm r z _ s = (pw w φ' ε r z p q)⁻¹ * gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p,
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm r z _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε r z p q)⁻¹ * gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun Z r z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q _ _ z hz))) (gm_res _ z _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)
      (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv _ (𝟙 Y) y p hy.1, hv _ (𝟙 Y) y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self hL' _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun Z r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ z inf_le_right hz s).symm.trans ((congrArg (gm _ z _) (hs p)).trans (hv Z r z p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z p q hp hq => ?_⟩
  · choose p hp using fun k => exists_chart hL (F (φ' k y))
    have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
    refine (hs j _ (𝟙 Y) y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y p m hj')).symm)
    rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv,
      _root_.mul_assoc]
  · exact (mul_inv_cancel_left _ _).symm.trans (congrArg _ (hs q Z r z p hp hq).symm)

theorem exists_pmaps {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ PMaps w φ' φ ε a t h := by
  obtain ⟨a, ha, hv⟩ := exists_down_val hw hL hL' hψ (LB.pullGen L φ ε t h) (DVR.pullGen_isGen _ _ _ _ ht h)
  refine ⟨a, ha, fun Z r z p q hp hq => ?_⟩
  have m : r z ∈ LB.wchart L (fun k => h ≫ φ k) p := Set.mem_iInter.2 fun k => by
    show (h ≫ φ k) (r z) ∈ L.U (p k)
    rw [← hψ k]; exact hp k
  exact (gm_pullGen L φ ε t h r z p m).symm.trans (hv Z r z p q m (Set.mem_iInter.2 hq))

theorem pmaps_val {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
    (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)}
    (H : PMaps w φ' φ ε a t h) (r : Z ⟶ Y') (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val t (r ≫ h) z J = (∏ k, gw w (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ F)) (J' (r ≫ φ' k)) ^ ε k) * val a r z J' :=
  (val_of t (r ≫ h) z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by
    rw [Category.assoc, Category.assoc, hψ])).trans
    (H Z r z _ _ (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k)))

theorem exists_good' (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  exact ⟨I, hI⟩

end Transport

section Cube

theorem isCub_of_rel {A B U : Type} [CommGroup A] [CommGroup B] [CommGroup U] {θ : B → B → B → U} (hθ : IsCub θ)
    (β : A →* B) (Ω : A → U) (θ' : A → A → A → U)
    (h : ∀ a b c, θ (β a) (β b) (β c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a *
      Ω b * Ω c * (Ω 1)⁻¹ * θ' a b c) : IsCub θ' := by
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  refine ⟨fun x y => ?_, fun x y z => ?_, fun x y z => ?_, fun x x' x'' y => ?_⟩
  · have e := h 1 x y
    rw [map_one, hθ.face, _root_.one_mul, _root_.one_mul] at e
    apply Additive.ofMul.injective
    have e' := E e
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := h x y z
    rw [hθ.s01, h y x z, mul_comm y x] at e
    apply Additive.ofMul.injective
    have e' := E e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := h x y z
    rw [hθ.s12, h x z y, mul_comm z y, mul_right_comm x z y] at e
    apply Additive.ofMul.injective
    have e' := E e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := hθ.coc (β x) (β x') (β x'') (β y)
    rw [← map_mul, ← map_mul, h, h, h, h, ← _root_.mul_assoc x x' x''] at e
    apply Additive.ofMul.injective
    have e' := E e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem nonempty_cubical (L : RigLB G) (t : LB.Gen (LB.LinComb L.L (thφ G (x3 G)) thε)) (ht : t.IsGen)
    (h : ∀ (T : Over S) (z : T.left) (J), Good L.L z J →
      IsCub (fun x x' y : T ⟶ G => val t (lift x (lift x' y)).left z J)) : Nonempty (CubicalStr G L) := by
  have v : ∀ (T : Over S) (z : T.left) (J), Good L.L z J → ∀ a : T ⟶ G3 G,
      val (LB.pullGen L.L (thφ G (x3 G)) thε t a.left) (𝟙 T.left) z J = val t a.left z J := fun T z J hJ a =>
    (val_pull hJ _ _ _).trans (by rw [Category.id_comp])
  have i3 : 𝟙 (G3 G).left = (lift (x3 G 0) (lift (x3 G 1) (x3 G 2))).left := by
    rw [← Over.id_left]; congr 1
    ext <;> simp [x3]
  refine ⟨⟨t, ht, fun i => corr_of_val L.isLB fun y J hJ => ?_, corr_of_val L.isLB fun y J hJ => ?_,
    corr_of_val L.isLB fun y J hJ => ?_, corr_of_val L.isLB fun y J hJ => ?_⟩⟩
  · refine (v (G2 G) y J hJ _).trans (Eq.trans ?_ (val_one _).symm)
    fin_cases i
    · exact (h (G2 G) y J hJ).face _ _
    · exact (h (G2 G) y J hJ).face₂ _ _
    · exact (h (G2 G) y J hJ).face₃ _ _
  · refine Eq.trans ?_ (v (G3 G) y J hJ _).symm
    exact (congrArg (fun r => val t r y J) i3).trans ((h (G3 G) y J hJ).s01 _ _ _)
  · refine Eq.trans ?_ (v (G3 G) y J hJ _).symm
    exact (congrArg (fun r => val t r y J) i3).trans ((h (G3 G) y J hJ).s12 _ _ _)
  · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v (G4 G) y J hJ _) (v (G4 G) y J hJ _))).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v (G4 G) y J hJ _) (v (G4 G) y J hJ _))).symm)
    exact (h (G4 G) y J hJ).coc _ _ _ _

variable {S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}

theorem nonempty_cubical_pull (gp : IsGrpPullback G' G f F) {L : RigLB G} (c : CubicalStr G L) (L' : RigLB G')
    {w : LB.Iso L'.L (L.L.pull F)} (hw : PGen w) : Nonempty (CubicalStr G' L') := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨t, ht, H⟩ := exists_pmaps hw L.isLB L'.isLB (ε := thε) (cubeMapOf gp).F3 hψ c.t c.isGen
  refine nonempty_cubical L' t ht fun T z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' L.isLB z
  refine isCub_of_rel (isCub_cubV c (T := Over.mk (T.hom ≫ f)) hJ) (pushHom gp T)
    (fun x => gw w x.left z (J (x.left ≫ F)) (J' x.left)) _ fun a b c' => ?_
  have e := pmaps_val hψ H (lift a (lift b c')).left z hJ hJ'
  have q : (lift a (lift b c')).left ≫ (cubeMapOf gp).F3 =
      (lift (pushHom gp T a) (lift (pushHom gp T b) (pushHom gp T c'))).left := hom_ext_triple _ fun i => by
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3] <;> rfl
  rw [q] at e
  exact e.trans (congrArg₂ (· * ·) (prod_cub a b c' (fun q => gw w q z (J (q ≫ F)) (J' q))) rfl)

theorem exists_sym_pull (gp : IsGrpPullback G' G f F) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} (hw : PGen w)
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : s.IsGen)
    (hr : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ s (eSec G)) (LB.oneGen L)) :
    ∃ s' : LB.Gen (LB.LinComb L' (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1]), s'.IsGen ∧
      LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ s' (eSec G')) (LB.oneGen L') := by
  have hι : (ι[G']).left ≫ F = F ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom gp G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine Eq.trans e ?_
    show (𝟙 _ ≫ F) ≫ _ = _
    rw [Category.id_comp]
  have hψ : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ F = F ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨s', hs', H⟩ := exists_pmaps hw hL hL' F hψ s hs
  refine ⟨s', hs', corr_of_val hL' fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e := pmaps_val hψ H (eSec G') y hJ hJ'
  have e₀ : eSec G' ≫ (ι[G']).left = eSec G' := by
    rw [eSec, ← Over.comp_left]; simp
  have he : eSec G' ≫ F = f ≫ eSec G := (cubeMapOf gp).e_comm
  rw [Fin.prod_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₀, Category.comp_id, zpow_one, zpow_neg,
    mul_inv_cancel, _root_.one_mul] at e
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
  rw [Category.id_comp, ← e, he]
  exact (val_pull hJ s (eSec G) f).symm.trans ((val_corr hJ hr f).trans (val_one _))

end Cube

theorem exists_isPullDeg (hP : PolBaseChangeSt) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (φ : R →+* R') (D : DegPre R) (W : (Spec (CommRingCat.of R)).Opens) (hW : Nonempty (PsiOn D W))
    (hη : (specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W) :
    ∃ (D' : DegPre R') (hD : IsPullDeg φ D D'), hD.W = W ∧ D'.P.g = D.P.g := by
  obtain ⟨ψW⟩ := hW
  obtain ⟨P', F, hF, hdim, hmul, t, ht⟩ := hP _ _ (specOf φ) D.P
  have gp : IsGrpPullback P'.A D.P.A (specOf φ) F := ⟨hF, fun T x y x₀ y₀ hx hy => by
    have ex : x₀ = toBase hF.w x := Over.OverMorphism.ext hx
    have ey : y₀ = toBase hF.w y := Over.OverMorphism.ext hy
    rw [ex, ey, ← hmul]; rfl⟩
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf φ))
  subst he
  obtain ⟨w, hw⟩ := LBIso.symm ⟨t, ht⟩
  have hw' := (isGen_iff w).1 hw
  have hE : eSec P'.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨rig, hrig, Hrig⟩ := exists_pmaps hw' D.P.isLB P'.isLB (K := PUnit) (φ' := fun _ => eSec P'.A)
    (φ := fun _ => eSec D.P.A) (ε := fun _ => 1) (specOf φ) (fun _ => hE) D.rig D.rig_gen
  obtain ⟨cub⟩ := nonempty_cubical_pull gp D.cub ⟨P'.L, rig, P'.isLB, hrig⟩ hw'
  obtain ⟨sym, hsym, hsr⟩ := exists_sym_pull gp D.P.isLB P'.isLB hw' D.sym D.sym_gen D.sym_rig
  obtain ⟨c, hc⟩ : ∃ c : D.X → (𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ P'.A), ∀ x,
      (c x).left ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ (D.c x).left :=
    ⟨fun x => Over.homMk (hF.lift (specOf φ ≫ (D.c x).left) (𝟙 _) (by
      rw [Category.assoc, Over.w, Category.id_comp]; exact Category.comp_id _)) (hF.lift_snd _ _ _),
      fun x => hF.lift_fst _ _ _⟩
  have cadd : ∀ a b, c (a + b) = padd P'.A (c a) (c b) := fun a b => by
    refine Over.OverMorphism.ext (hF.hom_ext ?_ (by rw [Over.w, Over.w]))
    have u : (toUnit (Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R')))).hom ≫ specOf φ))).left = specOf φ :=
      Category.id_comp _
    have m := gp.2 _ (c a) (c b) (toUnit _ ≫ D.c a) (toUnit _ ≫ D.c b)
      (by rw [hc, Over.comp_left, u]) (by rw [hc, Over.comp_left, u])
    rw [← MonObj.comp_mul, Over.comp_left, u] at m
    rw [hc, D.c_add]
    exact m
  obtain ⟨g, hg⟩ : ∃ g : (TK R').left ⟶ (TW W).left, g ≫ W.ι = jK R' ≫ specOf φ :=
    ⟨IsOpenImmersion.lift W.ι (jK R' ≫ specOf φ) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hy : jK R' y = genericPoint (Spec (CommRingCat.of R')) := by
        rw [genericPoint_eq_bot_of_affine]
        apply PrimeSpectrum.ext
        show Ideal.comap (algebraMap R' (FractionRing R')) (PrimeSpectrum.asIdeal y) = ⊥
        rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal y) (PrimeSpectrum.isPrime y)]
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R' (FractionRing R'))
      show specOf φ (jK R' y) ∈ W
      rw [hy]; exact hη), IsOpenImmersion.lift_fac _ _ _⟩
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c x).left =
      ptK (c x) ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) := fun x => by
    show g ≫ W.ι ≫ (D.c x).left = (jK R' ≫ (c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => ptK (c x) ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi x) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen x) g)
  choose psi hpsi vpsi using fun x => exists_down_val hw' D.P.isLB P'.isLB (K := PUnit)
    (φ' := fun _ => ptK (c x)) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  let D' : DegPre R' :=
    { P := P', rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D.X,
      c := c, c_add := cadd, psi := psi, psi_gen := hpsi }
  refine ⟨D',
    ⟨e, e_hom, w, hw, hE, ?_, AddEquiv.refl _, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, hdim⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ rig D.rig (specOf φ) _
      (rigPull_le (G' := P'.A) (G := D.P.A) _ (specOf φ) hE D.P.L) (fun _ => rfl)).2 Hrig
  · refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

end GlobalTheory.DegPull
