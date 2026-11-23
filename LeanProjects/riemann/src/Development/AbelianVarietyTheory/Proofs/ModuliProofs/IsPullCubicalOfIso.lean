import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

open TopologicalSpace

theorem exists_unit_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (a b : LB.Gen (LB.LinComb L φ ε)) (ha : a.IsGen) (hb : b.IsGen) :
    ∃ u : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (q : K → L.ι), r z ∈ LB.wchart L φ q →
      gm r z (LB.wchart L φ q) (a.s q) = gm r z ⊤ u * gm r z (LB.wchart L φ q) (b.s q) := by
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (q : K → L.ι),
      gm r z (LB.wchart L φ q) (a.s q * (b.s q)⁻¹) =
        gm r z (LB.wchart L φ q) (a.s q) * (gm r z (LB.wchart L φ q) (b.s q))⁻¹ := fun Z r z q =>
    (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
  obtain ⟨u, hu⟩ := glue_unit ⊤ (LB.wchart L φ) (fun _ => le_top) (fun y _ => by
      choose q hq using fun k => exists_chart hL (φ k y)
      exact Opens.mem_iSup.2 ⟨q, Set.mem_iInter.2 hq⟩) (fun q => a.s q * (b.s q)⁻¹) (fun q q' y hy => by
      refine (v _ _ y q).trans (Eq.trans ?_ (v _ _ y q').symm)
      rw [gen_trans ha (𝟙 Y) y hy.1 hy.2, gen_trans hb (𝟙 Y) y hy.1 hy.2, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul])
  refine ⟨u, fun Z r z q hq => ?_⟩
  rw [← gm_res r z (le_top : LB.wchart L φ q ≤ ⊤) hq u, hu q]
  exact ((congrArg (· * _) (v Z r z q)).trans (inv_mul_cancel_right _ _)).symm

theorem isPullCubical_of_iso (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G']
    [GrpObj G] [IsCommMonObj G] (hA : IsAbelianScheme G') (α : G' ⟶ G) [IsMonHom α] {L' : RigLB G'} {L : RigLB G}
    (c' : CubicalStr G' L') (c : CubicalStr G L) (h : LBIso L'.L (L.L.pull α.left)) :
    (CubeMap.ofHom α).IsPullCubical c' c := by
  obtain ⟨w, hw⟩ := h
  have hw' := (isGen_iff w).1 hw
  obtain ⟨a, ha, hm⟩ := DegPull.exists_pmaps (K := PUnit) hw' L.isLB L'.isLB (φ' := fun _ => eSec G')
    (φ := fun _ => eSec G) (ε := fun _ => 1) (𝟙 _) (fun _ => (CubeMap.ofHom α).e_comm) L.rig L.rigGen
  obtain ⟨u, hu⟩ := exists_unit_ratio L'.isLB a L'.rig ha L'.rigGen
  let w₁ : LB.Iso L'.L (L.L.pull α.left) :=
    ⟨fun p => w.s p * res (U := G'.hom ⁻¹ᵁ ⊤) (fun _ _ => trivial) (pullU G'.hom ⊤ u)⟩
  have g₁ : ∀ (Y : Scheme.{0}) (f : Y ⟶ G'.left) (y : Y) j k, α.left (f y) ∈ L.L.U j → f y ∈ L'.L.U k →
      gw w₁ f y j k = gw w f y j k * gm (f ≫ G'.hom) y ⊤ u := fun Y f y j k hj hk =>
    (map_mul _ _ _).trans (congrArg _ ((gm_res f y _ (show f y ∈ (L.L.pull α.left).U (fun _ => j) ⊓ L'.L.U k from
      ⟨mem_pull.2 hj, hk⟩) _).trans (gm_pull f G'.hom y ⊤ trivial u)))
  have hw₁ : PGen w₁ := fun Y f y j j' k k' hj hj' hk hk' => by
    rw [g₁ Y f y j k hj hk, g₁ Y f y j' k' hj' hk', hw' Y f y j j' k k' hj hj' hk hk', _root_.mul_assoc]
  refine (isPullCubical_iff _ c c').2 ⟨w₁, hw₁, fun Z r z p q hp hq => ?_, ?_⟩
  · refine (hm Z r z p q hp hq).trans ?_
    have e : (r ≫ eSec G') ≫ G'.hom = r := by
      rw [Category.assoc, show eSec G' ≫ G'.hom = 𝟙 _ from Over.w η[G'], Category.comp_id]
    have e₂ := g₁ Z (r ≫ eSec G') z _ _ (hp default) (hq default)
    rw [e] at e₂
    rw [hu Z r z q (Set.mem_iInter.2 hq), Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one]
    exact (_root_.mul_assoc _ _ _).symm.trans (congrArg (· * _) e₂.symm)
  · let e : 𝟙_ (Over S) ⟶ G3 G' := lift 1 (lift 1 1)
    have s₁ := (hG _ _ hA).2
    have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ α.left = (CubeMap.ofHom α).F3 ≫ thφ G (x3 G) I :=
      fun I => (CubeMap.ofHom α).psum_comm I.down
    refine EvenPull.pmaps_of_section (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε) hw₁ L.isLB L'.isLB
      (CubeMap.ofHom α).F3 hψ c'.t c'.isGen
      c.t c.isGen (G3 G').hom e.left (Over.w e) (AbLaw.Cube.surj_tensor hG hA (AbLaw.Cube.surj_tensor hG hA s₁))
      (fun y J J' hJ hJ' => ?_)
    have a₁ : e.left ≫ (CubeMap.ofHom α).F3 = (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left := by
      show (e ≫ (α ⊗ₘ α ⊗ₘ α)).left = _
      simp only [e, lift_map, MonObj.one_comp]
    have b₁ := (isCub_cubV c (T := 𝟙_ (Over S)) hJ).face 1 1
    have b₂ := (isCub_cubV c' (T := 𝟙_ (Over S)) hJ').face 1 1
    have b₃ := prod_cub (1 : 𝟙_ (Over S) ⟶ G') 1 1 (fun ψ => gw w₁ ψ y (J (ψ ≫ α.left)) (J' ψ))
    refine Eq.trans ((congrArg (fun q => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t q y J) a₁).trans b₁)
      (Eq.symm ?_)
    refine (congrArg₂ (· * ·) b₃ b₂).trans ?_
    simp

theorem mono_of_kTriv {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] (α : G' ⟶ G) [IsMonHom α]
    {L' : LB G'.left} {L : LB G.left} (hL' : L'.IsLB) (hL : L.IsLB) (h : LBIso L' (L.pull α.left))
    (hK : Out.KTriv G' L') : Mono α.left := by
  obtain ⟨w, hw⟩ := h
  have key : ∀ (R : Type) [CommRing R] (t : Sp R ⟶ S) (x : Over.mk t ⟶ G'), x ≫ α = 1 → x = 1 := by
    intro R _ t x hx
    refine hK R t x fun p => ⟨⊤, trivial, ?_⟩
    let φ' : Fin 2 → ((Over.mk t ⊗ G').left ⟶ G'.left) :=
      ![(lift (fst (Over.mk t) G' ≫ x) (snd (Over.mk t) G') ≫ μ[G']).left, (snd (Over.mk t) G').left]
    have e : φ' 0 ≫ α.left = φ' 1 ≫ α.left := by
      show (((fst (Over.mk t) G' ≫ x) * snd (Over.mk t) G') ≫ α).left = (snd (Over.mk t) G' ≫ α).left
      rw [MonObj.mul_comp, Category.assoc, hx, MonObj.comp_one, _root_.one_mul]
    obtain ⟨t₁, h₁, -⟩ := exists_gen hL (φ' := fun k => φ' k ≫ α.left) (ε' := ![1, -1]) (fun U _ k => by
      rw [Fin.prod_univ_two]; simp [e]) (LB.oneGen L (Y := (Over.mk t ⊗ G').left)) AbLaw.Cube.oneGen_isGen
    obtain ⟨t₂, h₂⟩ := exists_down ((isGen_iff w).1 hw) hL hL' t₁ h₁
    exact gen_chartPull (chartPullPull _ _ _ rfl) t₂ h₂
  refine ⟨fun {Z} f g hfg => ?_⟩
  refine Scheme.Cover.hom_ext Z.affineCover _ _ fun i => ?_
  have hs : g ≫ G'.hom = f ≫ G'.hom := by rw [← Over.w α, reassoc_of% hfg]
  let j : Spec (CommRingCat.of (Z.affineOpenCover.X i)) ⟶ Z := Z.affineCover.f i
  let x : Over.mk (j ≫ f ≫ G'.hom) ⟶ G' := Over.homMk (j ≫ f) (Category.assoc _ _ _)
  let y : Over.mk (j ≫ f ≫ G'.hom) ⟶ G' := Over.homMk (j ≫ g) (by rw [Category.assoc, hs]; rfl)
  have e : x ≫ α = y ≫ α := Over.OverMorphism.ext (by
    show (j ≫ f) ≫ _ = (j ≫ g) ≫ _
    rw [Category.assoc, hfg, Category.assoc])
  have := key _ _ (x * y⁻¹) (by rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel])
  exact congrArg (fun q => q.left) (mul_inv_eq_one.1 this)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem iso_of_lam {S : Scheme.{0}} (t' t : SAB H S) (α : t'.G ⟶ t.G) [IsMonHom α]
    (hact : ∀ a, t'.act.act a ≫ α = α ≫ t.act.act a)
    (h : LBIso (abelian₂ t'.G (lbPow t'.PP.L 1)) (abelian₂ t'.G (t.PP.L.pull α.left))) :
    LBIso t'.PP.L (t.PP.L.pull α.left) := by
  let U : t'.G ⟶ G2 t'.G := lift (𝟙 _) (t'.act.act H.w0)
  have ps : ∀ I : Finset (Fin 2), U ≫ psum t'.G (x2 t'.G) I = psum t'.G ![𝟙 _, t'.act.act H.w0] I := fun I =>
    (psum_hom (preHom U) (x2 t'.G) I).trans (congrArg (fun q => psum t'.G q I) (funext fun i => by
      fin_cases i <;> simp [preHom, U, x2]))
  have pa : ∀ I : Finset (Fin 2), psum t'.G ![𝟙 _, t'.act.act H.w0] I ≫ α = α ≫ psum t.G ![𝟙 _, t.act.act H.w0] I :=
    fun I => (psum_hom (MonoidHom.mk' (fun z : t'.G ⟶ t'.G => z ≫ α) fun a b => MonObj.mul_comp a b α) _ I).trans
      ((congrArg (fun q => psum t.G q I) (funext fun i => by
        fin_cases i <;> simp [preHom, hact])).trans (psum_hom (preHom α) ![𝟙 _, t.act.act H.w0] I).symm)
  have h₁ : LBIso (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (lbPow t'.PP.L 1))
      (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (t.PP.L.pull α.left)) :=
    LBIso.chartPull (chartPullSame _ _ _ _ U.left fun I => congrArg (fun q => q.left) (ps I.down).symm)
      (chartPullSame _ _ _ _ U.left fun I => congrArg (fun q => q.left) (ps I.down).symm) h
  have h₂ : LBIso (t'.PP.L.pull (𝟙 _)) (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (t'.PP.L.pull (𝟙 _))) :=
    LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullLinComb _ _ _ _ _ (𝟙 _) fun I => by simp) t'.prim
  have h₃ : LBIso (t.PP.L.pull α.left) (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (t.PP.L.pull α.left)) :=
    LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullLinComb _ _ _ _ _ α.left fun I =>
      congrArg (fun q => q.left) (pa I.down)) t.prim
  have i₁ := pull_isLB t'.PP.isLB (𝟙 _)
  have i₂ := pull_isLB t.PP.isLB α.left
  have h₄ := LBIso.trans i₁ (DVR.linComb_isLB _ i₂ _ _) i₂
    (LBIso.trans i₁ (DVR.linComb_isLB _ i₁ _ _) (DVR.linComb_isLB _ i₂ _ _) h₂ h₁) h₃.symm
  exact LBIso.chartPull (chartPullUnpull _ _ rfl) (chartPullId _) h₄

theorem pow_eq_one_of_weilIs (hK : Out.KerPowSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S)
    {T : Over S} [Unique T.left] {n : ℕ} (hn : 0 < n) {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs P.A P.L n x y c) : x ^ n = 1 ∧ y ^ n = 1 := by
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, -⟩ := h default
  have key : ∀ θ : Out.ThetaGrp P.A P.L n (Out.overRes V), θ.pt ^ n = 1 := fun θ =>
    (hK S P n hn _ θ.pt).1 fun p => ⟨⊤, trivial, gen_chartPull (chartPullPull _ _ _ rfl) θ.φ θ.isGen⟩
  have hs : Surjective V.ι := ⟨fun z => ⟨⟨default, hV⟩, Subsingleton.elim _ _⟩⟩
  have he : Epi V.ι := Flat.epi_of_flat_of_surjective _
  have key₂ : ∀ z : T ⟶ P.A, (Out.overResι V ≫ z) ^ n = 1 → z ^ n = 1 := fun z hz => by
    rw [← MonObj.comp_pow, ← MonObj.comp_one (Out.overResι V)] at hz
    exact Over.OverMorphism.ext ((cancel_epi V.ι).1 (congrArg (fun q => q.left) hz))
  exact ⟨key₂ x (hx ▸ key θx), key₂ y (hy ▸ key θy)⟩

end GlobalTheory.HeckePoint
