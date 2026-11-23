import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.AlgebraLevelSetting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenCubicUnitEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianAndTqOfIsGt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAdd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LiftConnectedOfTrivialUnique

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UU
open GlobalTheory.IndefiniteRowSideFullHecke.AlgebraLevelSetting (SymTriv Level Step FormalTorus Lv pr torus_w)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UniformizationSetting

section Weights
variable {S A Y₁ Y₂ : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
  {L : LB A}

theorem exists_genWt_of_base (hL : L.IsLB) {F₁ : G.left ⟶ Y₁} {F₂ : G.left ⟶ Y₂}
    (h₁ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ F₁ = g.left ≫ F₁)
    (h₂ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ F₂ = g.left ≫ F₂)
    {K₁ K₂ K₀ : Type} [Fintype K₁] [Fintype K₂] [Fintype K₀] {φ₁ : K₁ → (Y₁ ⟶ A)} {ε₁ : K₁ → ℤ}
    {φ₂ : K₂ → (Y₂ ⟶ A)} {ε₂ : K₂ → ℤ} {φ₀ : K₀ → (S ⟶ A)} {ε₀ : K₀ → ℤ}
    (hw : ∃ w : LB.Gen (LB.LinComb L φ₀ ε₀), w.IsGen)
    (hs : ∀ (U : Type) [CommGroup U] (f : (G.left ⟶ A) → U),
      (∏ k, f (F₁ ≫ φ₁ k) ^ ε₁ k) * ∏ k, f (G.hom ≫ φ₀ k) ^ ε₀ k = ∏ k, f (F₂ ≫ φ₂ k) ^ ε₂ k) {χ : X}
    (h : ∃ u : LB.Gen ((LB.LinComb L φ₁ ε₁).pull F₁), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val χ) :
    ∃ u : LB.Gen ((LB.LinComb L φ₂ ε₂).pull F₂), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val χ := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨u, hu, hχ⟩ := h
  obtain ⟨v, hv, e⟩ := exists_gen hL (φ' := fun k => F₂ ≫ φ₂ k) (ε' := ε₂)
    (fun U _ f => (Fintype.prod_sum_type _).trans (hs U f))
    (LB.mulGen L _ _ _ _ (flatGen u) (LB.pullGen L _ _ w G.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (flatGen_isGen hu) (DVR.pullGen_isGen _ _ _ _ hw _))
  refine ⟨unflatGen v, unflatGen_isGen hv, isWt_unflatGen h₂ hL hv fun Z t g z J hJ => ?_⟩
  rw [e _ _ z J hJ, e _ _ z J hJ, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, Over.w, Over.w,
    val_flatGen h₁ hχ t g hJ, _root_.mul_assoc]

end Weights

section Packages
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] {X : Type} [AddCommGroup X]

theorem cp_unique [ConnectedSpace S'] [Module.Free ℤ X] [Module.Finite ℤ X] (Q : TQ G' X) {P' : CP G'} {P : CP G}
    {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f} {w₁ w₂ : LB.Iso P'.L.L (P.L.L.pull F)}
    (h₁ : IsCPMap P' P f F hw w₁) (h₂ : IsCPMap P' P f F hw w₂) : w₁ = w₂ :=
  have := TrivDescentCompare.connected Q
  TrivDescentCompare.cpMap_unique (fun u hu => even_cubic_unit_eq_one globalFns_holds S' X G' Q u hu) h₁ h₂

theorem cp_unique_ab [ConnectedSpace S'] (hA : IsAbelianScheme G') {P' : CP G'} {P : CP G}
    {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f} {w₁ w₂ : LB.Iso P'.L.L (P.L.L.pull F)}
    (h₁ : IsCPMap P' P f F hw w₁) (h₂ : IsCPMap P' P f F hw w₂) : w₁ = w₂ :=
  cp_unique (TQ.abelian G' hA Unit) h₁ h₂

variable {P : CP G} {P' : CP G'} {P'' : CP G''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {f'' : S'' ⟶ S}
  {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left} {F'' : G''.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}

theorem comp_of_eq {hw' : F' ≫ G'.hom = G''.hom ≫ f'} (hw'' : F'' ≫ G.hom = G''.hom ≫ f'') (ef : f' ≫ f = f'')
    (eF : F' ≫ F = F'') {w : LB.Iso P'.L.L (P.L.L.pull F)} {w' : LB.Iso P''.L.L (P'.L.L.pull F')}
    (h : IsCPMap P' P f F hw w) (h' : IsCPMap P'' P' f' F' hw' w') :
    ∃ w'', IsCPMap P'' P f'' F'' hw'' w'' ∧ ∀ (Y : Scheme.{0}) (r : Y ⟶ G''.left) (y : Y) (j : P.L.L.ι) (i : P'.L.L.ι)
      (k : P''.L.L.ι), F'' (r y) ∈ P.L.L.U j → F' (r y) ∈ P'.L.L.U i → r y ∈ P''.L.L.U k →
      gw w'' r y j k = gw w (r ≫ F') y j i * gw w' r y i k := by
  subst ef eF
  obtain ⟨w'', T, H⟩ := h.exists_comp h' hw''
  exact ⟨w'', H, T⟩

theorem cancel_of_eq {hw'' : F'' ≫ G.hom = G''.hom ≫ f''} (hF : IsGrpPullback G'' G' f' F') (ef : f' ≫ f = f'')
    (eF : F' ≫ F = F'') {w : LB.Iso P'.L.L (P.L.L.pull F)} {w'' : LB.Iso P''.L.L (P.L.L.pull F'')}
    (h : IsCPMap P' P f F hw w) (h'' : IsCPMap P'' P f'' F'' hw'' w'') :
    ∃ w', IsCPMap P'' P' f' F' hF.1.w w' ∧ ∀ (Y : Scheme.{0}) (r : Y ⟶ G''.left) (y : Y) (j : P.L.L.ι) (i : P'.L.L.ι)
      (k : P''.L.L.ι), F'' (r y) ∈ P.L.L.U j → F' (r y) ∈ P'.L.L.U i → r y ∈ P''.L.L.U k →
      gw w'' r y j k = gw w (r ≫ F') y j i * gw w' r y i k := by
  subst ef eF
  exact (isCPMap_comp_cancel S S' S'' f f' G G' G'' P P' P'' F hw w F' hF.1.w hw'' h).2
    (TowerEx.toBase_mul hF _) w'' h''

theorem cubV_congr {L : RigLB G} (c : CubicalStr G L) {Z : Scheme.{0}} {a b : Z ⟶ S} (z : Z) (J)
    {x y u : Over.mk a ⟶ G} {x' y' u' : Over.mk b ⟶ G} (hx : x.left = x'.left) (hy : y.left = y'.left)
    (hu : u.left = u'.left) :
    @id (Z.presheaf.stalk z)ˣ (cubV c (T := Over.mk a) z J x y u) = cubV c (T := Over.mk b) z J x' y' u' := by
  obtain rfl : a = b := (Over.w x).symm.trans ((congrArg (· ≫ G.hom) hx).trans (Over.w x'))
  rw [Over.OverMorphism.ext hx, Over.OverMorphism.ext hy, Over.OverMorphism.ext hu]
  rfl

theorem isSemiAbelian_of_tq [Module.Free ℤ X] [Module.Finite ℤ X] (Q : TQ G X) : IsSemiAbelian G := by
  have := Q.q_affine
  have := Q.isAb.proper
  refine ⟨inferInstance, (TrivDescentCompare.smooth_conn Q).1, ?_, ?_, (TrivDescentCompare.smooth_conn Q).2,
    fun Ω _ _ p => ?_⟩
  · rw [← Over.w Q.q]; infer_instance
  · rw [← Over.w Q.q]; infer_instance
  · obtain ⟨Q', -⟩ := exists_tq_baseChange _ _ p X G _ _ (isGrpPullback_pullback G p) Q
    have := Q'.q_affine
    exact ⟨{ X := X, B := Q'.B, isAbelian := Q'.isAb, q := Q'.q, q_hom := Q'.q_hom, q_flat := Q'.q_flat,
             q_surjective := Q'.q_surj, q_quasiCompact := inferInstance, i := Q'.i, i_hom := Q'.i_hom,
             isKernel := Q'.isKernel }⟩

end Packages

theorem isSemiAbelian_of_level {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
    [IsCommMonObj G] (hs : Smooth G.hom) (hsep : IsSeparated G.hom) (hq : QuasiCompact G.hom)
    (gen : (Over.pullback (jK V)).obj G ≅ A.A) (hgen : IsMonHom gen.hom) {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (Q : TQ (thickObj V (IsLocalRing.maximalIdeal V) 0 G) X) :
    IsSemiAbelian G := by
  have : IsCommMonObj ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))).obj G) :=
    Functor.isCommMonObj_obj
  obtain ⟨Q'⟩ := nonempty_tq_pullback_comp (g := Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (show IsLocalRing.maximalIdeal V ^ (0 + 1) ≤ IsLocalRing.maximalIdeal V by simp))))
    (thick V (IsLocalRing.maximalIdeal V) 0) (by rw [← Spec.map_comp]; rfl) G Q
  exact ZJ.isSemiAbelian_of_fibres_dvr V G hs hsep hq (isSemiAbelian_of_tq Q')
    (isSemiAbelian_of_isAbelianScheme _
      (PolPull.isAbelianScheme_of_isGrpPullback A.isAb (isGrpPullback_of_iso gen)))

section Triv
variable {S S' : Scheme.{0}} {G : Over S} {G' H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  [GrpObj H] {P : CP G} {P' : CP G'} {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
  {w : LB.Iso P'.L.L (P.L.L.pull F)} {i : H ⟶ G'}

theorem triv_comp (h : IsCPMap P' P f F hw w) (i : H ⟶ G') (k : Fin 2) :
    ![i.left, (1 : H ⟶ G').left] k ≫ F = 𝟙 _ ≫ ![i.left ≫ F, H.hom ≫ f ≫ eSec G] k := by
  rw [Category.id_comp]
  fin_cases k
  · rfl
  · exact (one_left_comp h.mul H).trans (Category.assoc _ _ _)

theorem triv_vals (h : IsCPMap P' P f F hw w) (hj : (i.left ≫ F) ≫ G.hom = H.hom ≫ f)
    {s : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![i.left ≫ F, H.hom ≫ f ≫ eSec G] ![1, -1])}
    {a : LB.Gen (LB.LinComb P'.L.L (K := Fin 2) ![i.left, (1 : H ⟶ G').left] ![1, -1])}
    (Hs : PMaps w _ _ _ a s (𝟙 _)) {T : Over S'} {z : T.left} {J J'} (hJ : Good P.L.L z J) (hJ' : Good P'.L.L z J') :
    ∃ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
      (∀ x : T ⟶ H, val s x.left z J = W (x ≫ i) * (W 1)⁻¹ * val a x.left z J') ∧
      (∀ x : T ⟶ H, val P.sym (x.left ≫ i.left ≫ F) z J * W (x ≫ i) = W (x ≫ i)⁻¹ * val P'.sym (x ≫ i).left z J') ∧
      ∀ x y u : T ⟶ H, @id (T.left.presheaf.stalk z)ˣ
          (cubV P.c (T := Over.mk (T.hom ≫ f)) z J (toBase hj x) (toBase hj y) (toBase hj u)) *
          W ((x ≫ i) * (y ≫ i)) * W ((x ≫ i) * (u ≫ i)) * W ((y ≫ i) * (u ≫ i)) * W 1 =
        W ((x ≫ i) * (y ≫ i) * (u ≫ i)) * W (x ≫ i) * W (y ≫ i) * W (u ≫ i) *
          cubV P'.c z J' (x ≫ i) (y ≫ i) (u ≫ i) := by
  obtain ⟨-, a₂, a₃⟩ := h.vals T z J' J hJ' hJ _ fun _ => rfl
  have e : ∀ x : T ⟶ H, toBase hj x = toBase hw (x ≫ i) := fun x =>
    Over.OverMorphism.ext (Category.assoc _ _ _).symm
  refine ⟨fun x => gw w x.left z (J (x.left ≫ F)) (J' x.left), fun x => ?_, fun x => ?_, fun x y u => ?_⟩
  · have := CubTransport.val_pmaps (triv_comp h i) Hs x.left hJ hJ'
    rw [Category.comp_id] at this
    exact this.trans (congrArg₂ (· * ·)
      (CubTrivTorus.prod_cubTriv i x (fun q => gw w q z (J (q ≫ F)) (J' q))) rfl)
  · rw [← Category.assoc]; exact a₂ (x ≫ i)
  · rw [e, e, e]; exact a₃ _ _ _

theorem nonempty_symTriv_iff [IsMonHom i] (h : IsCPMap P' P f F hw w) (hj : (i.left ≫ F) ≫ G.hom = H.hom ≫ f) :
    Nonempty (SymTriv P (i.left ≫ F) hj) ↔ ∃ σ : CubTriv P'.c i, σ.Even := by
  have hp := (isGen_iff w).1 h.gen
  constructor
  · rintro ⟨s⟩
    obtain ⟨a, ha, Ha⟩ := CubTransport.exists_pmaps hp P.L.isLB P'.L.isLB _ (triv_comp h i) s.s s.gen
    refine ⟨⟨a, ha, fun T x y u z J' hJ' => ?_⟩, fun T x z J' hJ' => ?_⟩
    all_goals
      obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
      obtain ⟨W, v, a₂, a₃⟩ := triv_vals h hj Ha hJ hJ'
    · have b := s.cub T x y u z J hJ
      simp only [v, MonObj.mul_comp] at b
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul (a₃ x y u)
      have b' := congrArg Additive.ofMul b
      simp only [ofMul_mul, ofMul_inv] at a' b' ⊢
      linear_combination (norm := abel) a' + b'
    · have b := s.even T x z J hJ
      rw [v, v, GrpObj.inv_comp] at b
      show val a _ z J' = _ * val a _ z J'
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul (a₂ x)
      have b' := congrArg Additive.ofMul b
      simp only [ofMul_mul, ofMul_inv] at a' b' ⊢
      linear_combination (norm := abel) a' + b'
  · rintro ⟨σ, hσ⟩
    have up : ∀ φ : Fin 2 → (H.left ⟶ G.left), (∀ k, ![i.left, (1 : H ⟶ G').left] k ≫ F = 𝟙 _ ≫ φ k) →
        ∃ t : LB.Gen (LB.LinComb P.L.L φ ![1, -1]), t.IsGen ∧ PMaps w _ φ _ σ.s t (𝟙 _) := fun φ hc => by
      obtain rfl : φ = fun k => ![i.left, (1 : H ⟶ G').left] k ≫ F :=
        funext fun k => ((hc k).trans (Category.id_comp _)).symm
      obtain ⟨t, ht, e⟩ := exists_up hp P.L.isLB P'.L.isLB σ.s σ.gen
      refine ⟨t, ht, fun Z r z p q hp hq => ?_⟩
      rw [Category.comp_id]
      exact e Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)
    obtain ⟨s, hs, Hs⟩ := up _ (triv_comp h i)
    refine ⟨⟨s, hs, fun T x y u z J hJ => ?_, fun T x z J hJ => ?_⟩⟩
    all_goals
      obtain ⟨J', hJ'⟩ := exists_good_pt P'.L.isLB z
      obtain ⟨W, v, a₂, a₃⟩ := triv_vals h hj Hs hJ hJ'
    · have b := σ.cub T x y u z J' hJ'
      simp only [v, MonObj.mul_comp]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul (a₃ x y u)
      have b' := congrArg Additive.ofMul b
      simp only [ofMul_mul, ofMul_inv] at a' b' ⊢
      linear_combination (norm := abel) b' - a'
    · have b := hσ T x z J' hJ'
      rw [v, v, GrpObj.inv_comp]
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul (a₂ x)
      have b' := congrArg Additive.ofMul b
      simp only [ofMul_mul, ofMul_inv] at a' b' ⊢
      linear_combination (norm := abel) b' - a'

variable {S'' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem symTriv_compat [ConnectedSpace S''] [Module.Free ℤ X] {g : S'' ⟶ S'} {f'' : S'' ⟶ S}
    {j : (splitTorus S' X).left ⟶ G.left} {hj : j ≫ G.hom = (splitTorus S' X).hom ≫ f}
    {j'' : (splitTorus S'' X).left ⟶ G.left} {hj'' : j'' ≫ G.hom = (splitTorus S'' X).hom ≫ f''}
    (σ : SymTriv P j hj) (σ'' : SymTriv P j'' hj'') (ef : g ≫ f = f'') (ej : SplitTorus.bcMap g X ≫ j = j'')
    (Z : Scheme.{0}) (r : Z ⟶ (splitTorus S'' X).left) (z : Z) (J) (hJ : Good P.L.L z J) :
    val σ.s (r ≫ SplitTorus.bcMap g X) z J = val σ''.s r z J := by
  subst ef ej
  have hE := SplitTorus.isGrpPullback_bcMap g X
  obtain ⟨a, ha⟩ := TorusCoord.exists_ratio P.L.isLB (fun U _ k => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← Category.assoc, hE.1.w, Category.assoc, Category.assoc])
    (LB.pullGen P.L.L _ _ σ.s (SplitTorus.bcMap g X)) (DVR.pullGen_isGen _ _ _ _ σ.gen _) σ''.s σ''.gen
  have ha' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (splitTorus S'' X).left) (z : Z) (J), Good P.L.L z J →
      val σ.s (r ≫ SplitTorus.bcMap g X) z J = gm r z ⊤ a * val σ''.s r z J := fun Z r z J hJ =>
    (val_pull hJ _ _ _).symm.trans (ha Z r z J hJ)
  let β := toBaseHom (TowerEx.toBase_mul hE hE.1.w)
  have h₃ : ∀ (Z : Over S'') (x y u : Z ⟶ splitTorus S'' X) (z : Z.left),
      gm (x * y * u).left z ⊤ a * gm x.left z ⊤ a * gm y.left z ⊤ a * gm u.left z ⊤ a =
        gm (x * y).left z ⊤ a * gm (x * u).left z ⊤ a * gm (y * u).left z ⊤ a := fun Z x y u z => by
    obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    obtain ⟨V, hV⟩ : ∃ V : (Z ⟶ splitTorus S'' X) → (Z.left.presheaf.stalk z)ˣ,
      ∀ t, V t = val σ.s (β Z t).left z J := ⟨_, fun _ => rfl⟩
    have b := σ.cub _ (β Z x) (β Z y) (β Z u) z J hJ
    simp only [← map_mul] at b
    have c := σ''.cub Z x y u z J hJ
    obtain ⟨C, hC⟩ : ∃ C, C = @id (Z.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (Z.hom ≫ g ≫ f)) z J
      (toBase hj'' x) (toBase hj'' y) (toBase hj'' u)) := ⟨_, rfl⟩
    have b' : V (x * y * u) * V x * V y * V u = C * V (x * y) * V (x * u) * V (y * u) := by
      rw [hC, cubV_congr P.c z J (x' := toBase hj (β Z x)) (y' := toBase hj (β Z y)) (u' := toBase hj (β Z u))
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm]
      simp only [hV]; exact b
    have v : ∀ t, V t = gm t.left z ⊤ a * val σ''.s t.left z J := fun t => (hV t).trans (ha' _ t.left z J hJ)
    rw [← hC] at c
    simp only [v] at b'
    apply Additive.ofMul.injective
    have c' := congrArg Additive.ofMul c
    have b'' := congrArg Additive.ofMul b'
    simp only [ofMul_mul] at c' b'' ⊢
    linear_combination (norm := abel) b'' - c'
  have a1 : a = 1 := CubTrivTorus.eq_one_of_even a h₃ (fun Z z => by
      have := h₃ Z 1 1 1 z
      simp only [_root_.mul_one] at this
      exact mul_eq_left.1 this) fun Z x z => by
    obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    have b := σ.even _ (β Z x) z J hJ
    rw [← map_inv] at b
    have b' : val σ.s ((x⁻¹).left ≫ SplitTorus.bcMap g X) z J =
      val P.sym ((x.left ≫ SplitTorus.bcMap g X) ≫ j) z J * val σ.s (x.left ≫ SplitTorus.bcMap g X) z J := b
    rw [ha' _ _ z J hJ, ha' _ _ z J hJ, σ''.even Z x z J hJ, Category.assoc x.left,
      mul_left_comm _ (gm x.left z ⊤ a)] at b'
    exact mul_right_cancel b'
  rw [ha' Z r z J hJ, a1, map_one, _root_.one_mul]

theorem exists_even_of_desc {Q : TQ G X} (D : Q.Desc P) : ∃ σ : CubTriv P.c Q.i, σ.Even := by
  have := Q.i_hom
  obtain ⟨s, hs, v⟩ := exists_gen D.M.L.isLB (φ := (PEmpty.elim : PEmpty → ((splitTorus S X).left ⟶ Q.B.left)))
    (ε := PEmpty.elim) (K' := Fin 2) (φ' := ![(1 : splitTorus S X ⟶ Q.B).left, (1 : splitTorus S X ⟶ Q.B).left])
    (ε' := ![1, -1]) (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen D.M.L.L)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have v' : ∀ (Z : Scheme.{0}) r (z : Z) J, Good D.M.L.L z J → val s r z J = 1 := fun Z r z J hJ =>
    (v Z r z J hJ).trans (val_one _)
  have e : Q.i ≫ Q.q = 1 := Q.isKernel.w
  refine TowerEx.exists_even_pull D.map (e ▸ TorusCompat.of_comp Q.i Q.q : TorusCompat _ _ Q.i 1)
    ⟨s, hs, fun T x y u z J hJ => ?_⟩ fun T x z J hJ => ?_
  · simp only [v' _ _ z J hJ, MonObj.comp_one, (isCub_cubV D.M.c hJ).face, _root_.mul_one]
  · show val s _ z J = _ * val s _ z J
    rw [v' _ _ z J hJ, v' _ _ z J hJ, MonObj.comp_one, D.M.val_sym_one hJ, _root_.mul_one]

end Triv

theorem exists_even_lift {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [Nontrivial A']
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) (φ : A →+* A') (hφ : Function.Surjective φ)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (G' : Over (Spec (CommRingCat.of A'))) [GrpObj G']
    [IsCommMonObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom φ)) F)
    {P : CP G} {P' : CP G'} {hw} {w} (hP : IsCPMap P' P (Spec.map (CommRingCat.ofHom φ)) F hw w)
    {i : splitTorus _ X ⟶ G} {i' : splitTorus _ X ⟶ G'} [IsMonHom i] [IsMonHom i']
    (hi : TorusCompat (Spec.map (CommRingCat.ofHom φ)) F i' i) (h : ∃ σ : CubTriv P'.c i', σ.Even) :
    ∃ σ : CubTriv P.c i, σ.Even := by
  have hJ : RingHom.ker φ ≠ ⊤ := RingHom.ker_ne_top φ
  have hN : IsNilpotent (RingHom.ker φ) := by
    obtain ⟨n, hn⟩ := hA
    exact ⟨n, le_bot_iff.1 ((Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hJ) n).trans hn.le)⟩
  let e := (RingHom.quotientKerEquivOfSurjective hφ).symm
  let g : Spec (CommRingCat.of (A ⧸ RingHom.ker φ)) ⟶ Spec (CommRingCat.of A') := Spec.map e.toCommRingCatIso.hom
  have hg : g ≫ Spec.map (CommRingCat.ofHom φ) = red (RingHom.ker φ) := by
    rw [← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
    exact (RingHom.quotientKerEquivOfSurjective hφ).symm_apply_eq.2 rfl
  have hG := isGrpPullback_pullback G' g
  have hF₀ := (hG.comp hF).congr hg rfl
  obtain ⟨i₀, h₀, -⟩ := existsUnique_torusCompat (G' := (Over.pullback g).obj G') hG.1 i'
  have := h₀.isMonHom hG
  obtain ⟨_, _, _, _, _, _, _, hP₀⟩ := exists_isCPMap P' (TowerEx.toBase_mul hG hG.1.w) _ (pull_isLB P'.L.isLB _) _
    (pullIso_isGen P'.L.isLB _)
  obtain ⟨_, -, h₁⟩ := hP.exists_comp hP₀ (hG.comp hF).1.w
  obtain ⟨_, h₂⟩ := TowerEx.exists_congr h₁ hg rfl hF₀.1.w
  obtain ⟨σ, hσ⟩ := h
  exact T.exists_even_cubicalTrivialisation_lift_nilpotent A _ hN hJ X G _ _ _ hF₀ P _ _ h₂ i i₀ inferInstance this (hg ▸ h₀.trans hi)
    (TowerEx.nonempty_biTriv A hA G P i inferInstance) (TowerEx.exists_even_pull hP₀ h₀ σ hσ)

theorem exists_tq_lift {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [Nontrivial A']
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) (φ : A →+* A') (hφ : Function.Surjective φ)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (G' : Over (Spec (CommRingCat.of A'))) [GrpObj G']
    [IsCommMonObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom φ)) F)
    (Q' : TQ G' X) : ∃ Q : TQ G X, TorusCompat (Spec.map (CommRingCat.ofHom φ)) F Q'.i Q.i := by
  obtain ⟨Q, hQ, -⟩ := TowerEx.exists_lift hA φ hφ G G' hF (P := CP.triv G) (P' := CP.triv G')
    (IsCPMap.triv (hw := hF.1.w) (TowerEx.toBase_mul hF _)) Q' ⟨CubTriv.triv _, CubTriv.triv_even _⟩
  exact ⟨Q, hQ⟩

section Levels
variable {S S₁ S₂ : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : CP G} {X : Type} [AddCommGroup X]
  [Module.Free ℤ X] [Module.Finite ℤ X] {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S}
  {G₁ : Over S₁} [GrpObj G₁] [IsCommMonObj G₁] {F₁ : G₁.left ⟶ G.left} {h₁ : F₁ ≫ G.hom = G₁.hom ≫ f₁}
  {G₂ : Over S₂} [GrpObj G₂] [IsCommMonObj G₂] {F₂ : G₂.left ⟶ G.left} {h₂ : F₂ ≫ G.hom = G₂.hom ≫ f₂}
  [ConnectedSpace S₁] {L₁ : Level P X f₁ G₁ F₁ h₁} {L₂ : Level P X f₂ G₂ F₂ h₂} {t : S₁ ⟶ S₂} {m : G₁.left ⟶ G₂.left}

theorem level_ext (L : Level P X f₁ G₁ F₁ h₁) {v} (hv : IsCPMap L.Pe P f₁ F₁ h₁ v) : ⟨L.Q, L.Pe, v, hv, L.D⟩ = L := by
  obtain rfl := cp_unique L.Q hv L.v_map
  rfl

omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem step_ext {s s' : Step L₁ L₂ t m} (h : s.β = s'.β) : s = s' := by
  obtain ⟨_, β, _, _, u, hu, _⟩ := s
  obtain ⟨_, β', _, _, u', hu', _⟩ := s'
  obtain rfl : β = β' := h
  obtain rfl := cp_unique_ab L₁.Q.isAb hu hu'
  rfl

def mkStep (hm : IsGrpPullback G₁ G₂ t m) (ef : t ≫ f₂ = f₁) (eF : m ≫ F₂ = F₁)
    (tor : TorusCompat t m L₁.Q.i L₂.Q.i) (β : L₁.Q.B.left ⟶ L₂.Q.B.left) (hβ : IsCPPullback L₁.D.M L₂.D.M t β)
    (hq : L₁.Q.q.left ≫ β = m ≫ L₂.Q.q.left) : Step L₁ L₂ t m where
  torus := tor
  β := β
  β_pull := hβ.1
  q_β := hq
  u := hβ.2.choose
  u_map := hβ.2.choose_spec
  compat Z x z l k₁ k₂ j₁ j₂ hl hk₁ hk₂ hj₁ hj₂ := by
    have w : (L₁.Q.q.left ≫ β) ≫ L₂.Q.B.hom = G₁.hom ≫ t := by
      rw [Category.assoc, hβ.1.1.w, ← Category.assoc, Over.w]
    obtain ⟨a, ha, va⟩ := cancel_of_eq hm ef eF L₂.v_map L₁.v_map
    obtain ⟨b, hb, vb⟩ := comp_of_eq w (Category.comp_id t) hq.symm L₂.D.map ha
    obtain ⟨c, hc, vc⟩ := comp_of_eq w (Category.id_comp t) rfl hβ.2.choose_spec L₁.D.map
    obtain rfl := cp_unique L₁.Q hb hc
    rw [← vc Z x z j₂ j₁ k₁ hj₂ hj₁ hk₁, vb Z x z j₂ k₂ k₁ hj₂ hk₂ hk₁, va Z x z l k₂ k₁ hl hk₂ hk₁]
    ac_rfl

variable {B : Over S} [GrpObj B] [IsCommMonObj B] {M : CP B}

omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem red_ext {r r' : L₁.Red M} (h : r.toB = r'.toB) : r = r' := by
  obtain ⟨b, _, a, ha⟩ := r
  obtain ⟨b', _, a', ha'⟩ := r'
  obtain rfl : b = b' := h
  obtain rfl := cp_unique_ab L₁.Q.isAb ha ha'
  rfl

omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem compat_iff (ef : t ≫ f₂ = f₁) (s : Step L₁ L₂ t m) (r₁ : L₁.Red M) (r₂ : L₂.Red M) :
    s.Compat r₁ r₂ ↔ s.β ≫ r₂.toB = r₁.toB := by
  refine ⟨And.left, fun e => ⟨e, ?_⟩⟩
  obtain ⟨c, hc, vc⟩ := comp_of_eq r₁.toB_pull.1.w ef e r₂.a_map s.u_map
  obtain rfl := cp_unique_ab L₁.Q.isAb hc r₁.a_map
  exact vc

omit [Module.Free ℤ X] [Module.Finite ℤ X] in

theorem isCPPullback_iff (β : L₁.Q.B.left ⟶ B.left) : IsCPPullback L₁.D.M M f₁ β ↔ ∃! r : L₁.Red M, r.toB = β :=
  ⟨fun ⟨h, v, hv⟩ => ⟨⟨β, h, v, hv⟩, rfl, fun _ e => red_ext e⟩,
    fun ⟨r, e, _⟩ => e ▸ ⟨r.toB_pull, r.a, r.a_map⟩⟩

end Levels

theorem represents_iff {A : Type} [CommRing A] [IsLocalRing A] {S : Scheme.{0}} {G : Over S} [GrpObj G]
    [IsCommMonObj G] {P : CP G} {X : Type} [AddCommGroup X] {f : Spec (CommRingCat.of A) ⟶ S}
    {G₁ : Over (Spec (CommRingCat.of A))} [GrpObj G₁] [IsCommMonObj G₁] {F : G₁.left ⟶ G.left}
    {h : F ≫ G.hom = G₁.hom ≫ f} {L : Level P X f G₁ F h} {B : Over S} [GrpObj B] [IsCommMonObj B] {M : CP B}
    (r : L.Red M) (c : 𝟙_ (Over S) ⟶ B) (χ : X) :
    r.Represents c χ ↔ ∃ u : LB.Gen ((LB.LinComb M.L.L (K := Fin 2) ![((toUnit B ≫ c) * 𝟙 B).left, 𝟙 B.left]
      ![-1, 1]).pull (L.Q.q.left ≫ r.toB)), u.IsGen ∧ ∀ j, IsWt L.Q.i _ (u.s j).val χ := by
  have := L.Q.q_hom
  have q₁ : ∀ (Z : Over _) (t : Z ⟶ splitTorus _ X) (g : Z ⟶ G₁),
      ((t ≫ L.Q.i) * g).left ≫ L.Q.q.left = g.left ≫ L.Q.q.left := fun Z t g =>
    congrArg (fun k => k.left) (show ((t ≫ L.Q.i) * g) ≫ L.Q.q = g ≫ L.Q.q by
      rw [MonObj.mul_comp, Category.assoc, L.Q.isKernel.w, ← Category.assoc, toUnit_unique (t ≫ toUnit _) (toUnit _),
        ← Hom.one_def, _root_.one_mul])
  have q₂ : ∀ (Z : Over _) (t : Z ⟶ splitTorus _ X) (g : Z ⟶ G₁),
      ((t ≫ L.Q.i) * g).left ≫ L.Q.q.left ≫ r.toB = g.left ≫ L.Q.q.left ≫ r.toB := fun Z t g => by
    rw [← Category.assoc, q₁, Category.assoc]
  let c₀ : S ⟶ B.left := c.left
  have e₁ : (L.Q.q.left ≫ r.toB) ≫ ((toUnit B ≫ c) * 𝟙 B).left = L.Q.q.left ≫ r.lamφ c 0 := by
    have : r.pt ≫ ((toUnit B ≫ c) * 𝟙 B) = (toUnit _ ≫ c) * r.pt := by
      rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]
    exact (Category.assoc _ _ _).trans (congrArg (fun k => L.Q.q.left ≫ k.left) this)
  have e₂ : G₁.hom ≫ f ≫ c₀ = L.Q.q.left ≫ r.lamφ c 1 := by
    show _ = L.Q.q.left ≫ (toUnit (Over.mk (L.Q.B.hom ≫ f))).left ≫ c.left
    rw [Rosenlicht.toUnit_left, ← Over.w L.Q.q]
    exact (Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _).symm)
  have e₃ : (L.Q.q.left ≫ r.toB) ≫ 𝟙 _ = L.Q.q.left ≫ r.lamφ c 2 := Category.comp_id _
  have e₄ : G₁.hom ≫ f ≫ eSec B = L.Q.q.left ≫ r.lamφ c 3 := by
    show _ = L.Q.q.left ≫ (1 : Over.mk (L.Q.B.hom ≫ f) ⟶ B).left
    rw [one_left, ← Over.w L.Q.q]
    exact (Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _).symm)
  constructor
  · refine exists_genWt_of_base M.L.isLB q₁ q₂ (DVR.exists_gen_of_local M.L.L M.L.isLB (K := Fin 2)
      ![f ≫ c₀, f ≫ eSec B] ![-1, 1]) fun U _ k => ?_
    rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two, ← e₁, ← e₂, ← e₃, ← e₄]
    apply Additive.ofMul.injective
    simp
    abel
  · refine exists_genWt_of_base M.L.isLB q₂ q₁ (DVR.exists_gen_of_local M.L.L M.L.isLB (K := Fin 2)
      ![f ≫ c₀, f ≫ eSec B] ![1, -1]) fun U _ k => ?_
    rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two, ← e₁, ← e₂, ← e₃, ← e₄]
    apply Additive.ofMul.injective
    simp
    abel

end GlobalTheory.UniformizationSetting
end
