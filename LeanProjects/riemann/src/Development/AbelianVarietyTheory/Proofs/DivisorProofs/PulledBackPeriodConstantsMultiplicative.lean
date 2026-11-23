import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.LamRigid GlobalTheory.LamBiext

noncomputable section

namespace GlobalTheory.TChart.PeriodAdd

theorem exists_ratio {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  refine ⟨a, fun Z r z J hJ => ?_⟩
  rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
    ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))

theorem exists_pull {X X' Y : Scheme.{0}} {L : LB X} (F : X' ⟶ X) {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    {a : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)} (ha : a.IsGen) :
    ∃ a' : LB.Gen (LB.LinComb (L.pull F) φ' ε), a'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (j : K → PUnit → L.ι), r z ∈ LB.wchart (L.pull F) φ' j →
      gm r z (LB.wchart (L.pull F) φ' j) (a'.s j) =
        gm r z (LB.wchart L (fun k => φ' k ≫ F) (fun k => j k PUnit.unit)) (a.s fun k => j k PUnit.unit) := by
  have le : ∀ j : K → PUnit → L.ι, LB.wchart (L.pull F) φ' j ≤
      LB.wchart L (fun k => φ' k ≫ F) (fun k => j k PUnit.unit) := fun j y hy =>
    Set.mem_iInter.2 fun k => (mem_pull (F := F) (x := φ' k y)).1 (Set.mem_iInter.1 hy k)
  refine ⟨⟨fun j => res (le j) (a.s fun k => j k PUnit.unit)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z j hj => gm_res r z (le j) hj _⟩
  refine (gm_res _ y (le j) hj _).trans ((gen_trans ha (𝟙 Y) y (le j hj) (le j' hj')).trans
    (congrArg₂ (· * ·) ?_ (gm_res _ y (le j') hj' _).symm))
  refine Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (Eq.symm ?_)
  refine (gm_pull_g L F (𝟙 Y ≫ φ' k) y (j k) (j' k) (Set.mem_iInter.1 hj k) (Set.mem_iInter.1 hj' k)).trans ?_
  rw [Category.assoc]

theorem rigid_two {X X₁ X' Y S₀ : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {F : X' ⟶ X} {F₁ : X' ⟶ X₁}
    (w : LB.Iso (L.pull F) (L₁.pull F₁)) (hw : w.IsGen) (hL : L.IsLB) (hL₁ : L₁.IsLB) {K : Type} [Fintype K]
    (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    {a : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)} (ha : a.IsGen)
    {t : LB.Gen (LB.LinComb L₁ (fun k => φ' k ≫ F₁) ε)} (ht : t.IsGen)
    (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom) :
    ∃ c : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X₁) → L₁.ι) (J' : (Z ⟶ X) → L.ι), Good L₁ z J →
      Good L z J' → (val t r z J * ((∏ k, gw w (r ≫ φ' k) z (J (r ≫ φ' k ≫ F₁)) (fun _ => J' (r ≫ φ' k ≫ F)) ^ ε k) *
        val a r z J')⁻¹).val = gs (r ≫ p) z ⊤ c := by
  obtain ⟨a', ha', hv'⟩ := exists_pull F φ' ε ha
  have hP : (L.pull F).IsLB := DVR.linComb_isLB _ hL _ _
  obtain ⟨t₁, ht₁, hv⟩ := exists_up ((isGen_iff w).1 hw) hL₁ hP a' ha'
  obtain ⟨c, hc⟩ := exists_ratio hL₁ p hp ht ht₁
  refine ⟨c, fun Z r z J J' hJ hJ' => Eq.trans ?_ (hc Z r z J hJ)⟩
  have m : r z ∈ LB.wchart (L.pull F) φ' (fun k _ => J' (r ≫ φ' k ≫ F)) :=
    Set.mem_iInter.2 fun k => mem_pull.2 (hJ' (r ≫ φ' k ≫ F))
  have e := (hv Z r z _ _ (hJ.mem _ r) m).trans (congrArg (_ * ·) (hv' Z r z _ m))
  exact congrArg (fun q => (val t r z J * q⁻¹).val) e.symm

theorem exists_law {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B']
    [IsCommMonObj B'] (M : RigLB B) (c : CubicalStr B M) {f : S' ⟶ S} {β : B'.left ⟶ B.left}
    {β₂ : (G2 B').left ⟶ (G2 B).left} (hβ : IsGrpPullback B' B f β) (hsq : IsSquare β β₂) :
    ∃ t : LB.Gen (LB.LinComb (abelian₂ B M.L) (fun k => law1φ B' (x3 B' 0) (x3 B' 1) (x3 B' 2) k ≫ β₂) lawε), t.IsGen ∧
      ∀ {T₀ : Over S'} (a a' b : T₀ ⟶ B') (z₀ : T₀.left) (J₀ : (T₀.left ⟶ B.left) → M.L.ι), Good M.L z₀ J₀ →
        val (L := abelian₂ B M.L) t (lift a (lift a' b)).left z₀ (ind B J₀) =
          cubV (T := Over.mk (T₀.hom ≫ f)) c z₀ J₀ (toBase hβ.1.w a) (toBase hβ.1.w a') (toBase hβ.1.w b) := by
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have pt_mul : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'), toBase hw₀ (a * b) = toBase hw₀ a * toBase hw₀ b :=
    fun a b => Over.OverMorphism.ext (hβ.2 _ a b _ _ rfl rfl).symm
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  have Hlam : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B') {U : Type} [CommGroup U] (h : (T₀.left ⟶ B.left) → U),
      ∏ i, h (((lift a b).left ≫ β₂) ≫ lamφ B i) ^ lamε i =
        h (toBase hw₀ a * toBase hw₀ b).left * (h (toBase hw₀ a).left)⁻¹ * (h (toBase hw₀ b).left)⁻¹ *
          h (1 : Over.mk (T₀.hom ≫ f) ⟶ B).left := fun a b U _ h => by
    rw [β₂_lift]; exact prod_lam (toBase hw₀ a) (toBase hw₀ b) h
  let φ3 := law1φ B' (x3 B' 0) (x3 B' 1) (x3 B' 2)
  let β₃ : (G3 B').left ⟶ (G3 B).left :=
    (lift (toBase hw₀ (x3 B' 0)) (lift (toBase hw₀ (x3 B' 1)) (toBase hw₀ (x3 B' 2)))).left
  have fe3 : FormEq (fun I => β₃ ≫ thφ B (x3 B) I) thε (flatφ (lamφ B) (fun k => φ3 k ≫ β₂)) (flatε lamε lawε) :=
    fun U _ h => by
      have a := prod_cub (toBase hw₀ (x3 B' 0)) (toBase hw₀ (x3 B' 1)) (toBase hw₀ (x3 B' 2)) h
      have b := prod_law₁ (x3 B' 0) (x3 B' 1) (x3 B' 2) (fun χ => ∏ i, h ((χ ≫ β₂) ≫ lamφ B i) ^ lamε i)
      rw [id₃] at b
      simp only [Over.id_left, Category.id_comp, Hlam, pt_mul] at b
      rw [a, prod_flat, b]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
  obtain ⟨g₃, hg₃, hv₃⟩ := exists_gen M.isLB fe3 (LB.pullGen M.L (thφ B (x3 B)) thε c.t β₃)
    (DVR.pullGen_isGen _ _ _ _ c.isGen β₃)
  refine ⟨_, nest_isGen (L := M.L) (φ := lamφ B) (δ := lamε) hg₃, ?_⟩
  intro T₀ a a' b z₀ J₀ hJ₀
  show val (L := LB.LinComb M.L (lamφ B) lamε) (nest M.L (lamφ B) lamε (fun k => φ3 k ≫ β₂) lawε g₃) _ z₀ (ind B J₀) = _
  rw [val_nest hg₃ _ (good_ind hJ₀) hJ₀]
  simp only [adj_ind M.isLB hJ₀, one_zpow, Finset.prod_const_one, _root_.one_mul]
  rw [hv₃ _ _ z₀ J₀ hJ₀]
  refine (val_pull hJ₀ _ _ _).trans ?_
  refine congrArg (fun q => val (L := M.L) (φ := thφ B (x3 B)) (ε := thε) c.t q z₀ J₀) ?_
  refine hom_ext_triple B fun i => ?_
  have e1 : β₃ ≫ (x3 B i).left = (x3 B' i).left ≫ β := by
    show (lift _ (lift _ _) ≫ x3 B i).left = _
    rw [cartesian_lift_three_comp_projection]; fin_cases i <;> rfl
  rw [Category.assoc, e1, ← Category.assoc, ← Over.comp_left, cartesian_lift_three_comp_projection, ← Over.comp_left, cartesian_lift_three_comp_projection]
  fin_cases i <;> rfl

theorem isoVal_law {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B]
    [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B'] (M : RigLB B) (c : CubicalStr B M) (M₁ : RigLB B₁)
    (c₁ : CubicalStr B₁ M₁) {f : S' ⟶ S} {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (hβ : IsGrpPullback B' B f β) (hsq : IsSquare β β₂) {f₁ : S' ⟶ S₁} {β' : B'.left ⟶ B₁.left}
    {β₂' : (G2 B').left ⟶ (G2 B₁).left} (hβ' : IsGrpPullback B' B₁ f₁ β') (hsq' : IsSquare β' β₂')
    (hB : IsAbelianScheme B') (w : LB.Iso ((abelian₂ B M.L).pull β₂) ((abelian₂ B₁ M₁.L).pull β₂')) (hw : w.IsGen)
    {T : Over S'} (x x' y : T ⟶ B') (z : T.left) (J : (T.left ⟶ B₁.left) → M₁.L.ι) (J' : (T.left ⟶ B.left) → M.L.ι)
    (hJ : Good M₁.L z J) (hJ' : Good M.L z J') :
    @id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f₁)) c₁ z J (toBase hβ'.1.w x) (toBase hβ'.1.w x')
        (toBase hβ'.1.w y)) * isoVal w (lift x y).left z J J' * isoVal w (lift x' y).left z J J' =
      isoVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' * isoVal w (lift (x * x') y).left z J J' *
        @id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f)) c z J' (toBase hβ.1.w x) (toBase hβ.1.w x')
          (toBase hβ.1.w y)) := by
  haveI := hB.comm
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨a, ha, va⟩ := exists_law M c hβ hsq
  obtain ⟨t, ht, vt⟩ := exists_law M₁ c₁ hβ' hsq'
  have sj3 : Function.Surjective ((snd B' (B' ⊗ B')).left ≫ (snd B' B').left ≫ B'.hom).appTop.hom :=
    surj_comp (surj_snd hG hB _) (surj_comp (surj_snd hG hB _) (hG _ _ hB).2)
  obtain ⟨u, hu⟩ := rigid_two w hw (DVR.linComb_isLB _ M.isLB _ _) (DVR.linComb_isLB _ M₁.isLB _ _) _ lawε ha ht _ sj3
  have key : ∀ x x' y : T ⟶ B',
      (@id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f₁)) c₁ z J (toBase hβ'.1.w x) (toBase hβ'.1.w x')
        (toBase hβ'.1.w y)) * (isoVal w (lift (x * x') y).left z J J' * (isoVal w (lift x y).left z J J')⁻¹ *
        (isoVal w (lift x' y).left z J J')⁻¹ *
        @id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f)) c z J' (toBase hβ.1.w x) (toBase hβ.1.w x')
          (toBase hβ.1.w y)))⁻¹).val = gs T.hom z ⊤ u := by
    intro x x' y
    have e := hu T.left (lift x (lift x' y)).left z (ind B₁ J) (ind B J') (good_ind hJ) (good_ind hJ')
    have e₀ : (lift x (lift x' y)).left ≫ (snd B' (B' ⊗ B')).left ≫ (snd B' B').left ≫ B'.hom = T.hom := by
      rw [Over.w, Over.w]; exact Over.w (lift x (lift x' y))
    rw [e₀, va x x' y z J' hJ', vt x x' y z J hJ] at e
    refine Eq.trans ?_ e
    refine congrArg Units.val (congrArg₂ (· * ·) rfl (congrArg (·⁻¹) (congrArg₂ (· * ·) ?_ rfl)))
    refine (prod_law₁ x x' y (fun χ => isoVal w χ z J J')).symm.trans (Finset.prod_congr rfl fun k _ => ?_)
    refine congrArg (· ^ lawε k) ?_
    refine congrArg₂ (fun (j : ULift.{0} (Finset (Fin 2)) → M₁.L.ι) (j' : ULift.{0} (Finset (Fin 2)) → M.L.ι) =>
      gw w ((lift x (lift x' y)).left ≫ law1φ B' (x3 B' 0) (x3 B' 1) (x3 B' 2) k) z j (fun _ => j'))
      (funext fun I => congrArg J ?_) (funext fun I => congrArg J' ?_) <;> simp only [Category.assoc]
  have o : toBase hβ.1.w (1 : T ⟶ B') = 1 := map_one (pushHom hβ T)
  have o' : toBase hβ'.1.w (1 : T ⟶ B') = 1 := map_one (pushHom hβ' T)
  have k₁ := key 1 1 1
  rw [o, o', (isCub_cubV c (T := Over.mk (T.hom ≫ f)) hJ').face, (isCub_cubV c₁ (T := Over.mk (T.hom ≫ f₁)) hJ).face,
    _root_.mul_one (1 : T ⟶ B')] at k₁
  have k₂ := Units.ext ((key x x' y).trans k₁.symm)
  simp only [id] at k₂ ⊢
  apply Additive.ofMul.injective
  have k₃ := congrArg Additive.ofMul k₂
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at k₃ ⊢
  linear_combination (norm := abel) k₃

theorem val_τ₀_add {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (Z : Over (Sp W))
    {z : Z.left} {J : (Z.left ⟶ T.B.left) → T.M.L.ι} (hJ : Good T.M.L z J) (a a' b : Fin T.r → ℤ) :
    val (T.τ₀ (a + a') b) (toUnit Z).left z J *
        cubV T.cub z J (toUnit Z ≫ T.c₀ a) (toUnit Z ≫ T.c₀ a') (toUnit Z ≫ T.c₀ b) =
      val (T.τ₀ a b) (toUnit Z).left z J * val (T.τ₀ a' b) (toUnit Z).left z J := by
  have C := corr_of_val T.M.isLB (t := LB.mulGen T.M.L _ _ _ _ (T.τ₀ (a + a') b)
      (LB.pullGen T.M.L (thφ T.B (x3 T.B)) thε T.cub.t (lift (T.c₀ a) (lift (T.c₀ a') (T.c₀ b))).left))
    (t' := LB.mulGen T.M.L _ _ _ _ (T.τ₀ a b) (T.τ₀ a' b)) fun y J hJ => by
      refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
      refine Eq.trans (congrArg₂ (· * ·) rfl ?_) (T.τ₀_add a a' b y J hJ)
      refine (val_pull hJ _ _ _).trans ?_
      rw [Category.id_comp]; rfl
  have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ C (toUnit Z).left).trans (val_mul hJ _ _ _))
  exact Eq.trans (congrArg₂ (· * ·) rfl (val_cub T.cub (toUnit Z) hJ _ _ _).symm) this

theorem period_add : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → IsNormIso w₁ → ∀ a a' b, q (a + a') b = q a b * q a' b := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' _ _ _ _ hf _ _ _ hβ' hβ'' sq' sq'' x hx w₁ q hw hP hN a a' b
  have hB : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback L.T.isAb hβ''
  obtain ⟨κK, hκ, -⟩ := GlobalTheory.HalfBC.exists_kappa f₁ (RingHom.id V₁) (RingHom.id _) (fun _ => rfl) hf
  let z : (TK V₁).left := IsLocalRing.closedPoint (FractionRing V₁)
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt L.T.M.isLB z
  obtain ⟨J', hJ'⟩ := GlobalTheory.UU.exists_good_pt D.toPre.P.isLB z
  let p : (Fin L.T.r → ℤ) → (TK V₁ ⟶ B') := fun a => toUnit (TK V₁) ≫ x a
  let T' : Over (Sp V) := Over.mk ((TK V₁).hom ≫ spMap f₁)
  let T'' : Over (Sp L.W) := Over.mk ((TK V₁).hom ≫ spMap κ₁)
  have pD : ∀ a, Out.toBase hβ'.1.w (p a) = DVR.cP D.toPre T' ((e.trans e₀) a) := fun a => Over.OverMorphism.ext (by
    show ((TK V₁).hom ≫ (x a).left) ≫ β' = ((TK V₁).hom ≫ spMap f₁) ≫ (D.toPre.c (e₀ (e a))).left
    rw [Category.assoc, (hx a).1, Category.assoc])
  have pT : ∀ a, Out.toBase hβ''.1.w (p a) = toUnit T'' ≫ L.T.c₀ ((n : ℤ) • a) := fun a => Over.OverMorphism.ext (by
    show ((TK V₁).hom ≫ (x a).left) ≫ β'' = ((TK V₁).hom ≫ spMap κ₁) ≫ (L.T.c₀ ((n : ℤ) • a)).left
    rw [Category.assoc, (hx a).2, Category.assoc])
  have pa : p (a + a') = p a * p a' := by
    refine Over.OverMorphism.ext (hβ''.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    refine Eq.trans ?_ (hβ''.2 _ (p a) (p a') (Out.toBase hβ''.1.w (p a)) (Out.toBase hβ''.1.w (p a')) rfl rfl)
    rw [pT, pT, ← MonObj.comp_mul, ← L.T.c₀_add, ← smul_add, ← pT]
    rfl
  have law := isoVal_law ⟨D.toPre.P.L, D.toPre.rig, D.toPre.P.isLB, D.toPre.rig_gen⟩ D.toPre.cub L.T.M L.T.cub hβ' sq'
    hβ'' sq'' hB w₁ hw (p a) (p a') (p b) z J J' hJ hJ'
  rw [pD, pD, pD, pT, pT, pT, ← pa] at law
  have h₀ := hN z J J' hJ hJ'
  have hD := GlobalTheory.TauTwist.val_tau_add (T := T') (Over.homMk κK hκ) (z := z) (J := J') hJ' D.tau_bimult
    ((e.trans e₀) a) ((e.trans e₀) a') ((e.trans e₀) b)
  have hT := val_τ₀_add L.T T'' (z := z) (J := J) hJ ((n : ℤ) • a) ((n : ℤ) • a') ((n : ℤ) • b)
  rw [← smul_add] at hT
  rw [← map_add] at hD
  have r₁ := hP κK hκ (a + a') b z J J' hJ hJ'
  have r₂ := hP κK hκ a b z J J' hJ hJ'
  have r₃ := hP κK hκ a' b z J J' hJ hJ'
  refine GlobalTheory.TauTwist.unitAt_injective (F := FractionRing V₁) z ?_
  rw [map_mul]
  have alg : ∀ {U : Type} [CommGroup U] {t₁ t₂ t₃ q₁ q₂ q₃ i₀ i₁ i₂ i₃ s₁ s₂ s₃ c c' : U}, t₁ = q₁ * (i₁ * s₁) →
      t₂ = q₂ * (i₂ * s₂) → t₃ = q₃ * (i₃ * s₃) → t₁ * c = t₂ * t₃ → s₁ * c' = s₂ * s₃ → i₀ = 1 →
      c' * i₂ * i₃ = i₀ * i₁ * c → q₁ = q₂ * q₃ := by
    intro U _ t₁ t₂ t₃ q₁ q₂ q₃ i₀ i₁ i₂ i₃ s₁ s₂ s₃ c c' h₁ h₂ h₃ h₄ h₅ h₆ h₇
    subst h₁ h₂ h₃ h₆
    apply Additive.ofMul.injective
    have k₄ := congrArg Additive.ofMul h₄
    have k₅ := congrArg Additive.ofMul h₅
    have k₇ := congrArg Additive.ofMul h₇
    simp only [ofMul_mul, ofMul_one] at k₄ k₅ k₇ ⊢
    linear_combination (norm := abel) k₄ - k₅ + k₇
  exact alg (U := ((TK V₁).left.presheaf.stalk z)ˣ) r₁ r₂ r₃ hD hT h₀ law

end GlobalTheory.TChart.PeriodAdd
