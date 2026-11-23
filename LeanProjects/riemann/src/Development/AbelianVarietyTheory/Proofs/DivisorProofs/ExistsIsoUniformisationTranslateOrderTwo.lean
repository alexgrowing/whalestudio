import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisedAbelianSchemesIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfIsClosedImmersionOfThickeningsOfIsProper
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedTranslatedBundleIsoPsiZeroStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp.Transl

section Group

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (a : 𝟙_ (Over S) ⟶ G)

abbrev tr : G ⟶ G := (toUnit G ≫ a) * 𝟙 G

omit [IsCommMonObj G] in
theorem comp_tr {T : Over S} (y : T ⟶ G) : y.left ≫ (tr a).left = ((toUnit T ≫ a) * y).left := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem prod_cub_tr {T : Over S} (x x' y : T ⟶ G) {V : Type} [CommGroup V] (h : (T.left ⟶ G.left) → V) :
    (∏ k : thK.{0}, h (((lift x (lift x' y)).left ≫ thφ G (x3 G) k) ≫ (tr a).left) ^ thε k) *
      ∏ k : thK.{0}, h ((lift x (lift x' (toUnit T ≫ a))).left ≫ thφ G (x3 G) k) ^ thε k =
      ∏ k : thK.{0}, h ((lift x (lift x' ((toUnit T ≫ a) * y))).left ≫ thφ G (x3 G) k) ^ thε k := by
  rw [prod_cub x x' y (fun s => h (s ≫ (tr a).left)), prod_cub, prod_cub]
  simp only [comp_tr]
  generalize toUnit T ≫ a = b
  rw [_root_.mul_one, show b * (x * x' * y) = x * x' * (b * y) from mul_left_comm _ _ _,
    show b * (x * x') = x * x' * b from _root_.mul_comm _ _, show b * (x * y) = x * (b * y) from mul_left_comm _ _ _,
    show b * (x' * y) = x' * (b * y) from mul_left_comm _ _ _, _root_.mul_comm b x, _root_.mul_comm b x']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

variable {L L' : RigLB G} {w : LB.Iso L'.L (L.L.pull (tr a).left)}

theorem cube_tr (hw : PGen w) (c : CubicalStr G L) (c' : CubicalStr G L')
    (hs : Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom)
    {T : Over S} (x x' y : T ⟶ G) {z : T.left} {N : (T.left ⟶ G.left) → L.L.ι} {N' : (T.left ⟶ G.left) → L'.L.ι}
    (hN : Good L.L z N) (hN' : Good L'.L z N') :
    cubV c z N x x' ((toUnit T ≫ a) * y) =
      (∏ k : thK.{0}, gw w ((lift x (lift x' y)).left ≫ thφ G (x3 G) k) z
        (N (((lift x (lift x' y)).left ≫ thφ G (x3 G) k) ≫ (tr a).left))
        (N' ((lift x (lift x' y)).left ≫ thφ G (x3 G) k)) ^ thε k) *
      cubV c' z N' x x' y * cubV c z N x x' (toUnit T ≫ a) := by
  obtain ⟨t, ht, hv⟩ := exists_up hw L.isLB L'.isLB (φ' := thφ G (x3 G)) (ε := thε) c'.t c'.isGen
  have tv : ∀ {T : Over S} (x x' y : T ⟶ G) {z : T.left} {N : (T.left ⟶ G.left) → L.L.ι}
      {N' : (T.left ⟶ G.left) → L'.L.ι}, Good L.L z N → Good L'.L z N' → val t (lift x (lift x' y)).left z N =
      (∏ k : thK.{0}, gw w ((lift x (lift x' y)).left ≫ thφ G (x3 G) k) z
        (N (((lift x (lift x' y)).left ≫ thφ G (x3 G) k) ≫ (tr a).left))
        (N' ((lift x (lift x' y)).left ≫ thφ G (x3 G) k)) ^ thε k) * cubV c' z N' x x' y := by
    intro T x x' y z N N' hN hN'
    refine (hv _ _ z _ _ (Good.mem hN _ _) (Good.mem hN' _ _)).trans (congrArg₂ (· * ·) ?_ rfl)
    exact Finset.prod_congr rfl fun k _ => by rw [Category.assoc]
  have vv : ∀ {T : Over S} (x x' y : T ⟶ G) {z : T.left} {N : (T.left ⟶ G.left) → L.L.ι}, Good L.L z N →
      val (LB.pullGen L.L (thφ G (x3 G)) thε c.t
        (lift (x3 G 0) (lift (x3 G 1) ((toUnit _ ≫ a) * x3 G 2))).left) (lift x (lift x' y)).left z N =
        cubV c z N x x' ((toUnit T ≫ a) * y) ∧
      val (LB.mulGen L.L _ _ _ _ t (LB.pullGen L.L (thφ G (x3 G)) thε c.t
        (lift (x3 G 0) (lift (x3 G 1) (toUnit _ ≫ a))).left)) (lift x (lift x' y)).left z N =
        val t (lift x (lift x' y)).left z N * cubV c z N x x' (toUnit T ≫ a) := by
    intro T x x' y z N hN
    have a₀ : lift x (lift x' y) ≫ x3 G 0 = x := by simp [x3]
    have a₁ : lift x (lift x' y) ≫ x3 G 1 = x' := by simp [x3]
    have a₂ : lift x (lift x' y) ≫ x3 G 2 = y := by simp [x3]
    have a₃ : lift x (lift x' y) ≫ toUnit _ ≫ a = toUnit T ≫ a := by rw [← Category.assoc, comp_toUnit]
    constructor
    · rw [val_cub c _ hN, MonObj.comp_mul, a₀, a₁, a₂, a₃]
    · refine (val_mul hN _ _ _).trans (congrArg (_ * ·) ?_)
      rw [val_cub c _ hN, a₀, a₁, a₃]
  let e : 𝟙_ (Over S) ⟶ G3 G := lift 1 (lift 1 1)
  have he : e.left ≫ (snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := gen_unique' L.isLB (fun V _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans (congrArg₂ (· * ·) ?_ rfl)
        (prod_cub_tr a (x3 G 0) (x3 G 1) (x3 G 2) h))
      have : lift (x3 G 0) (lift (x3 G 1) (x3 G 2)) = 𝟙 _ := by ext <;> simp [x3]
      rw [this]
      exact Finset.prod_congr rfl fun k _ => congrArg (fun q => h (q ≫ _) ^ _) (Category.id_comp _).symm) _ e.left he hs
    (DVR.pullGen_isGen _ _ _ _ c.isGen (lift (x3 G 0) (lift (x3 G 1) ((toUnit _ ≫ a) * x3 G 2))).left)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ c.isGen
      (lift (x3 G 0) (lift (x3 G 1) (toUnit _ ≫ a))).left)) (fun s J hJ => by
      choose J' hJ' using fun ψ : (𝟙_ (Over S)).left ⟶ G.left => exists_chart L'.isLB (ψ s)
      have v := vv (1 : 𝟙_ (Over S) ⟶ G) 1 1 hJ
      refine v.1.trans (Eq.trans ?_ v.2.symm)
      rw [tv (1 : 𝟙_ (Over S) ⟶ G) 1 1 hJ hJ', (isCub_cubV c' (T := 𝟙_ (Over S)) hJ').face, _root_.mul_one, _root_.mul_one,
        prod_cub 1 1 1 (fun q => gw w q s (J (q ≫ (tr a).left)) (J' q))]
      simp) _ (lift x (lift x' y)).left z N hN
  exact (vv x x' y hN).1.symm.trans (key.trans ((vv x x' y hN).2.trans (congrArg (· * _) (tv x x' y hN hN'))))

theorem sym_tr (hw : PGen w) (ha : a ^ 2 = 1)
    (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : s.IsGen)
    (s' : LB.Gen (LB.LinComb L'.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs' : s'.IsGen)
    (rig : LB.Gen.Corr L'.L _ _ _ _ (LB.pullGen L'.L _ _ s' (eSec G)) (LB.oneGen L'.L))
    (hf : Function.Surjective G.hom.appTop.hom)
    {Z : Scheme.{0}} (r : Z ⟶ G.left) {z : Z} {N : (Z ⟶ G.left) → L.L.ι} {N' : (Z ⟶ G.left) → L'.L.ι}
    (hN : Good L.L z N) (hN' : Good L'.L z N') :
    val s (r ≫ (tr a).left) z N =
      gw w (r ≫ (ι[G]).left) z (N ((r ≫ (ι[G]).left) ≫ (tr a).left)) (N' (r ≫ (ι[G]).left)) *
      (gw w r z (N (r ≫ (tr a).left)) (N' r))⁻¹ * val s' r z N' * val s (r ≫ (toUnit G ≫ a).left) z N := by
  obtain ⟨t, ht, hv⟩ := exists_up hw L.isLB L'.isLB s' hs'
  have tv : ∀ {Z : Scheme.{0}} (r : Z ⟶ G.left) {z : Z} {N : (Z ⟶ G.left) → L.L.ι} {N' : (Z ⟶ G.left) → L'.L.ι},
      Good L.L z N → Good L'.L z N' → val t r z N =
      gw w (r ≫ (ι[G]).left) z (N ((r ≫ (ι[G]).left) ≫ (tr a).left)) (N' (r ≫ (ι[G]).left)) *
      (gw w r z (N (r ≫ (tr a).left)) (N' r))⁻¹ * val s' r z N' := by
    intro Z r z N N' hN hN'
    refine (hv _ _ z _ _ (Good.mem hN _ _) (Good.mem hN' _ _)).trans (congrArg₂ (· * ·) ?_ rfl)
    rw [pw, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.assoc, Category.comp_id, Category.id_comp,
      zpow_one, zpow_neg]
  have ai : (toUnit G ≫ a)⁻¹ = toUnit G ≫ a := by
    rw [inv_eq_iff_mul_eq_one, ← MonObj.comp_mul, ← pow_two, ha, MonObj.comp_one]
  have i₁ : (toUnit G ≫ a).left ≫ (ι[G]).left = (toUnit G ≫ a).left := by
    rw [← Over.comp_left, ← Hom.inv_def, ai]
  have i₂ : (tr a).left ≫ (ι[G]).left = (ι[G]).left ≫ (tr a).left := by
    rw [comp_tr, ← Over.comp_left, ← Hom.inv_def, mul_inv, ai, Hom.inv_def, Category.id_comp]
  have key := gen_unique' L.isLB (fun V _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
        Category.comp_id, Category.id_comp, i₁, i₂, zpow_one, zpow_neg, mul_inv_cancel, _root_.mul_one])
    G.hom (eSec G) (Over.w η[G]) hf (DVR.pullGen_isGen _ _ _ _ hs (tr a).left)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ hs (toUnit G ≫ a).left)) (fun y J hJ => by
      choose J' hJ' using fun ψ : S ⟶ G.left => exists_chart L'.isLB (ψ y)
      have oi : eSec G ≫ (ι[G]).left = eSec G := by
        have : η[G] ≫ ι[G] = η[G] := by simp
        exact congrArg (fun q => q.left) this
      have b := val_corr hJ' rig (𝟙 _)
      rw [val_pull hJ', val_one, Category.id_comp] at b
      have ot : eSec G ≫ (tr a).left = eSec G ≫ (toUnit G ≫ a).left := by
        refine (comp_tr a η[G]).trans (congrArg (fun q => q.left) (?_ : _ = η[G] ≫ toUnit G ≫ a))
        rw [← Category.assoc, comp_toUnit]
        exact (congrArg (_ * ·) (by simp [Hom.one_def] : η[G] = 1)).trans (_root_.mul_one _)
      rw [val_mul hJ, val_pull hJ, val_pull hJ, tv _ hJ hJ', oi, b, ot]
      simp) _ r z N hN
  rw [val_mul hN, val_pull hN, val_pull hN, tv r hN hN'] at key
  exact key

end Group

section Compare

variable {B B' G G' E : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {L' : LB G'}

theorem exists_repack {K : LB E} (ψ : E ⟶ E) (f : E ⟶ G) {g : E ⟶ G} (h : ψ ≫ f = g) (v : LB.Iso K (L.pull g))
    (hv : PGen v) : ∃ v' : LB.Iso K ((L.pull f).pull ψ), PGen v' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ E) (z : Z) (j : L.ι)
      (k : K.ι), g (r z) ∈ L.U j → r z ∈ K.U k → gw v' r z (fun _ => j) k = gw v r z j k := by
  subst h
  have le : ∀ (J : PUnit → PUnit → L.ι) (k : K.ι), ((L.pull f).pull ψ).U J ⊓ K.U k ≤
      (L.pull (ψ ≫ f)).U (fun _ => J PUnit.unit PUnit.unit) ⊓ K.U k := fun J k x hx =>
    ⟨mem_pull₂.2 (mem_pull.1 (mem_pull.1 hx.1)), hx.2⟩
  let v' : LB.Iso K ((L.pull f).pull ψ) :=
    ⟨fun p => res (le p.1 p.2) (v.s (fun _ => p.1 PUnit.unit PUnit.unit, p.2))⟩
  have e : ∀ (Z : Scheme.{0}) (r : Z ⟶ E) (z : Z) (j : L.ι) (k : K.ι), (ψ ≫ f) (r z) ∈ L.U j → r z ∈ K.U k →
      gw v' r z (fun _ => j) k = gw v r z j k := fun Z r z j k hj hk =>
    gm_res r z (le (fun _ _ => j) k) ⟨mem_pull.2 (mem_pull.2 hj), hk⟩ _
  refine ⟨v', fun Z r z j j' k k' hj hj' hk hk' => ?_, e⟩
  have m := mem_pull.1 hj
  have m' := mem_pull.1 hj'
  have g₁ := GlobalTheory.Algebraise.gm_pull_g f (r ≫ ψ) z m m'
  rw [Category.assoc] at g₁
  refine (e Z r z _ k m hk).trans ((hv Z r z _ _ k k' m m' hk hk').trans ?_)
  exact (congrArg₂ (· * ·) (congrArg (· * _) g₁) (e Z r z _ k' m' hk')).symm

theorem exists_comparison (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB) {p : E ⟶ B} {p' : E ⟶ B'}
    {f : E ⟶ G} {f' : E ⟶ G'} {F : G' ⟶ G} (ψ : E ⟶ E) (h : ψ ≫ f = f' ≫ F)
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f') (M'.pull p')}
    {wL : LB.Iso L' (L.pull F)} (hw : w.IsGen) (hw' : w'.IsGen) (hwL : PGen wL) :
    ∃ u : LB.Iso (M'.pull p') (M.pull (ψ ≫ p)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ E) (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
        p (ψ (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → F (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
        gw u r z jM (fun _ => jM') * gw w' r z jM' (fun _ => jL') =
          gw w (r ≫ ψ) z jM (fun _ => jL) * gw wL (r ≫ f') z jL jL' := by
  obtain ⟨y₁, g₁, v₁⟩ := GlobalTheory.Algebraise.exists_swap _ _ w' hw' (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _)
  rw [isGen_iff] at g₁ hw
  obtain ⟨y₂, t₂⟩ := exists_comp hL' wL y₁ hwL g₁ hL (LB.isLB_pull hM' _)
  obtain ⟨y₃, g₃, v₃⟩ := exists_repack ψ f h y₂ (t₂.pgen_comp hL' hwL g₁)
  obtain ⟨u, t₄⟩ := exists_comp (LB.isLB_pull hL _) w y₃ hw g₃ hM (LB.isLB_pull hM' _)
  refine ⟨u, (isGen_iff u).2 (t₄.pgen_comp (LB.isLB_pull hL _) hw g₃), fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  have a₅ : f (ψ (r z)) ∈ L.U jL := (congrArg (fun q : E ⟶ G => q (r z) ∈ L.U jL) h).mpr a₃
  rw [t₄ Z r z jM (fun _ => jL) (fun _ => jM') a₁ (mem_pull.2 a₅) (mem_pull.2 a₂), v₃ Z r z jL _ a₃ (mem_pull.2 a₂),
    t₂ Z r z jL jL' _ a₃ a₄ (mem_pull.2 a₂), v₁ Z r z jM' jL' a₂ a₄, Category.comp_id, _root_.mul_assoc,
    inv_mul_cancel_right]

end Compare

section Level

open TorusInvariance WCub

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] {e : ℕ}

abbrev up {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (y : T ⟶ thickObj R I e G) :
    (Over.map (thick R I e)).obj T ⟶ G :=
  (Over.map (thick R I e)).map y ≫ fstG I e G

omit [IsDomain R] [IsCommMonObj G] in
theorem up_mul {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x y : T ⟶ thickObj R I e G) :
    up (x * y) = up x * up y :=
  map_mul (pushHom (isGrpPullback_pullback G (thick R I e)) T) x y

variable {a : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G} {ae : 𝟙_ _ ⟶ thickObj R I e G}
  (hae : ae.left ≫ (fstG I e G).left = thick R I e ≫ a.left)
include hae

omit [IsDomain R] [IsCommMonObj G] [GrpObj G] in
theorem up_ae (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) : up (toUnit T ≫ ae) = toUnit _ ≫ a := by
  apply Over.OverMorphism.ext
  show (T.hom ≫ ae.left) ≫ (fstG I e G).left = (T.hom ≫ thick R I e) ≫ a.left
  rw [Category.assoc, Category.assoc]
  exact congrArg (T.hom ≫ ·) hae

omit [IsDomain R] in
theorem tr_fst : (tr ae).left ≫ (fstG I e G).left = (fstG I e G).left ≫ (tr a).left := by
  have h := up_mul (toUnit _ ≫ ae) (𝟙 (thickObj R I e G))
  rw [up_ae hae] at h
  have k : up (𝟙 (thickObj R I e G)) = fstG I e G := Over.OverMorphism.ext (Category.id_comp _)
  rw [k] at h
  exact (congrArg (fun q => q.left) h).trans (comp_tr a (fstG I e G)).symm

variable {D D' : DegData R I} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {U : UnifPre I D A G}
  {U' : UnifPre I D' A' G}
  (u : LB.Iso (D'.toPre.P.L.pull (U'.gt e).pG.left) (D.toPre.P.L.pull ((tr ae).left ≫ (U.gt e).pG.left)))

def uV {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
    (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι) (r : Z ⟶ (thickObj R I e G).left) : (Z.presheaf.stalk z)ˣ :=
  gw u r z (J (r ≫ (tr ae).left ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left))

variable {wL : LB.Iso U'.LG.L (U.LG.L.pull (tr a).left)} (hw : PGen wL)
  (sq : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
    (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left ((tr ae).left (r z)) ∈ D.toPre.P.L.U jM →
    (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (tr a).left ((fstG I e G).left (r z)) ∈ U.LG.L.U jL →
    (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
    gw u r z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') =
      gw (U.w e) (r ≫ (tr ae).left) z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL')
include sq

theorem uV_mul {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι} {N : (Z ⟶ G.left) → U.LG.L.ι} {N' : (Z ⟶ G.left) → U'.LG.L.ι}
    (hJ : Good D.toPre.P.L z J) (hJ' : Good D'.toPre.P.L z J') (hN : Good U.LG.L z N) (hN' : Good U'.LG.L z N')
    (r : Z ⟶ (thickObj R I e G).left) :
    uV u z J J' r * wVal U' e z J' N' r = wVal U e z J N (r ≫ (tr ae).left) *
      gw wL (r ≫ (fstG I e G).left) z (N ((r ≫ (fstG I e G).left) ≫ (tr a).left)) (N' (r ≫ (fstG I e G).left)) := by
  have k : (r ≫ (tr ae).left) ≫ (fstG I e G).left = (r ≫ (fstG I e G).left) ≫ (tr a).left :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (tr_fst hae)).trans (Category.assoc _ _ _).symm)
  unfold wVal uV
  rw [k, Category.assoc r (tr ae).left]
  exact sq _ r z _ _ _ _ (hJ (r ≫ (tr ae).left ≫ (U.gt e).pG.left)) (hJ' _)
    (hN ((r ≫ (fstG I e G).left) ≫ (tr a).left)) (hN' _)

include hw

theorem cube_uV (hs : Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom)
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x x' y : T ⟶ thickObj R I e G)
    {z : T.left} {J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L z J) (hJ' : Good D'.toPre.P.L z J') :
    val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (tri (thick R I e) (U.gt e).pG ![x, x', (toUnit T ≫ ae) * y]) z J =
      (∏ k : thK.{0}, uV u z J J' (psum (thickObj R I e G) ![x, x', y] k.down).left ^ thε k) *
        val (L := D'.toPre.P.L) (φ := thφ D'.toPre.P.A (x3 D'.toPre.P.A)) (ε := thε) D'.toPre.cub.t
          (tri (thick R I e) (U'.gt e).pG ![x, x', y]) z J' *
        val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
          (tri (thick R I e) (U.gt e).pG ![x, x', toUnit T ≫ ae]) z J := by
  choose N hN using fun χ : T.left ⟶ G.left => exists_chart U.LG.isLB (χ z)
  choose N' hN' using fun χ : T.left ⟶ G.left => exists_chart U'.LG.isLB (χ z)
  have f₃ := tri_thφ (thick R I e) (fstG I e G) ![x, x', y] (𝟙 _) (Category.id_comp _).symm
  have e₁ := cube_val U ![x, x', (toUnit T ≫ ae) * y] hJ hN
  have e₂ := cube_val U ![x, x', toUnit T ≫ ae] hJ hN
  have e₃ := cube_val U' ![x, x', y] hJ' hN'
  have e₄ := cube_tr a hw U.cubG U'.cubG hs (T := (Over.map (thick R I e)).obj T) (up x) (up x') (up y) hN hN'
  rw [← up_ae hae, ← up_mul] at e₄
  have e₅ := prod_cub_tr ae x x' y (wVal U e z J N)
  rw [prod_cub x x' y (fun s => wVal U e z J N (s ≫ (tr ae).left)),
    ← prod_psum x x' y (fun s => wVal U e z J N (s ≫ (tr ae).left)), prod_cub, ← prod_psum, prod_cub,
    ← prod_psum] at e₅
  have e₆ : (∏ k : thK.{0}, uV u z J J' (psum (thickObj R I e G) ![x, x', y] k.down).left ^ thε k) *
      (∏ k : thK.{0}, wVal U' e z J' N' (psum (thickObj R I e G) ![x, x', y] k.down).left ^ thε k) =
      (∏ k : thK.{0}, wVal U e z J N ((psum (thickObj R I e G) ![x, x', y] k.down).left ≫ (tr ae).left) ^ thε k) *
      ∏ k : thK.{0}, gw wL (tri (thick R I e) (fstG I e G) ![x, x', y] ≫ thφ G (x3 G) k) z
        (N ((tri (thick R I e) (fstG I e G) ![x, x', y] ≫ thφ G (x3 G) k) ≫ (tr a).left))
        (N' (tri (thick R I e) (fstG I e G) ![x, x', y] ≫ thφ G (x3 G) k)) ^ thε k := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow, ← mul_zpow, f₃ k]
    exact congrArg (· ^ thε k) (uV_mul hae u sq hJ hJ' hN hN' _)
  have alg : ∀ {V : Type} [CommGroup V] {m₁ m₂ m₃ w₁ w₂ w₃ w₄ l₁ l₂ l₃ d c : V}, m₁ = w₁ * l₁ → m₂ = w₂ * l₂ →
      m₃ = w₃ * l₃ → l₁ = d * l₃ * l₂ → w₄ * w₂ = w₁ → c * w₃ = w₄ * d → m₁ = c * m₃ * m₂ := by
    intro V _ m₁ m₂ m₃ w₁ w₂ w₃ w₄ l₁ l₂ l₃ d c h₁ h₂ h₃ h₄ h₅ h₆
    rw [h₁, h₂, h₃, h₄, ← h₅, ← _root_.mul_assoc c, h₆]
    ac_rfl
  exact alg e₁ e₂ e₃ e₄ e₅ e₆

theorem even_uV (ha : a ^ 2 = 1) (hf : Function.Surjective G.hom.appTop.hom)
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (y : T ⟶ thickObj R I e G) {z : T.left}
    {J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} {J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    {N : (T.left ⟶ G.left) → U.LG.L.ι}
    (hJ : Good D.toPre.P.L z J) (hJ' : Good D'.toPre.P.L z J') (hN : Good U.LG.L z N) :
    val D.toPre.sym (y.left ≫ (tr ae).left ≫ (U.gt e).pG.left) z J * uV u z J J' y.left =
      uV u z J J' (y.left ≫ (ι[thickObj R I e G]).left) * (val D'.toPre.sym (y.left ≫ (U'.gt e).pG.left) z J' *
        val U.symG (T.hom ≫ thick R I e ≫ a.left) z N) := by
  choose N' hN' using fun χ : T.left ⟶ G.left => exists_chart U'.LG.isLB (χ z)
  have iF : (ι[thickObj R I e G]).left ≫ (fstG I e G).left = (fstG I e G).left ≫ (ι[G]).left :=
    EvenPull.inv_fst _ G
  have ae2 : (toUnit T ≫ ae) * (toUnit T ≫ ae) = 1 := by
    have h := up_mul (toUnit T ≫ ae) (toUnit T ≫ ae)
    rw [up_ae hae, ← MonObj.comp_mul _ a a, ← pow_two a, ha, MonObj.comp_one] at h
    have o := up_mul (1 : T ⟶ thickObj R I e G) 1
    rw [_root_.mul_one] at o
    have k := congrArg (fun q => q.left) (h.trans (left_eq_mul.1 o).symm)
    exact Over.OverMorphism.ext (pullback.hom_ext k ((Over.w _).trans (Over.w (1 : T ⟶ thickObj R I e G)).symm))
  have i₂ : (y.left ≫ (tr ae).left) ≫ (ι[thickObj R I e G]).left =
      (y.left ≫ (ι[thickObj R I e G]).left) ≫ (tr ae).left := by
    rw [comp_tr, ← Over.comp_left, ← Over.comp_left, comp_tr, ← Hom.inv_def, ← Hom.inv_def, mul_inv,
      inv_eq_of_mul_eq_one_right ae2]
  have e₁ := even_val U (y.left ≫ (tr ae).left) hJ hN
  have e₂ := even_val U' y.left hJ' hN'
  have e₃ := sym_tr a hw ha U.symG U.symG_gen U'.symG U'.symG_gen U'.symG_rig hf (y.left ≫ (fstG I e G).left) hN hN'
  have e₅ := uV_mul hae u sq hJ hJ' hN hN' y.left
  have e₆ := uV_mul hae u sq hJ hJ' hN hN' (y.left ≫ (ι[thickObj R I e G]).left)
  have k₁ : (y.left ≫ (tr ae).left) ≫ (fstG I e G).left = (y.left ≫ (fstG I e G).left) ≫ (tr a).left :=
    (Category.assoc _ _ _).trans ((congrArg (y.left ≫ ·) (tr_fst hae)).trans (Category.assoc _ _ _).symm)
  have k₂ : (y.left ≫ (ι[thickObj R I e G]).left) ≫ (fstG I e G).left =
      (y.left ≫ (fstG I e G).left) ≫ (ι[G]).left :=
    (Category.assoc _ _ _).trans ((congrArg (y.left ≫ ·) iF).trans (Category.assoc _ _ _).symm)
  have k₃ : (y.left ≫ (fstG I e G).left) ≫ (toUnit G ≫ a).left = T.hom ≫ thick R I e ≫ a.left := by
    have : up y ≫ toUnit G ≫ a = toUnit _ ≫ a := by rw [← Category.assoc, comp_toUnit]
    exact (congrArg (fun q => q.left) this).trans (Category.assoc T.hom _ _)
  rw [i₂, k₁, Category.assoc y.left (tr ae).left] at e₁
  rw [k₂] at e₆
  rw [k₃] at e₃
  have alg : ∀ {V : Type} [CommGroup V] {m w w' s m₂ v v' s₂ d d' κ c c' : V}, m * w = w' * s → m₂ * v = v' * s₂ →
      s = d' * d⁻¹ * s₂ * κ → c * v = w * d → c' * v' = w' * d' → m * c = c' * (m₂ * κ) := by
    intro V _ m w w' s m₂ v v' s₂ d d' κ c c' h₁ h₂ h₃ h₅ h₆
    have a₁ := congrArg Additive.ofMul h₁
    have a₂ := congrArg Additive.ofMul h₂
    have a₄ := congrArg Additive.ofMul h₃
    have a₅ := congrArg Additive.ofMul h₅
    have a₆ := congrArg Additive.ofMul h₆
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₄ a₅ a₆ ⊢
    linear_combination (norm := abel) a₁ - a₂ + a₄ + a₅ - a₆
  exact alg e₁ e₂ e₃ e₅ e₆

omit u sq in
set_option maxHeartbeats 400000 in

theorem exists_level [IsLocalRing R] (hG : IsSemiAbelian G) (ha : a ^ 2 = 1)
    (hf : Function.Surjective G.hom.appTop.hom)
    (hs : Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom)
    (β : D'.toPre.P.A ⟶ D.toPre.P.A) (hβ : (U'.gt e).pG.left ≫ β.left = (U.gt e).pG.left)
    (be : (thickObj R I e D'.toPre.P.A).left ⟶ D.toPre.P.A.left)
    (hb : (tr ae).left ≫ (U.gt e).pG.left = (U'.gt e).q.left ≫ be) :
    ∃ v : LB.Iso (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left) (D.toPre.P.L.pull be), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
      (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left ((tr ae).left (r z)) ∈ D.toPre.P.L.U jM →
      (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (tr a).left ((fstG I e G).left (r z)) ∈ U.LG.L.U jL →
      (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
      gw v (r ≫ (U'.gt e).q.left) z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') =
        gw (U.w e) (r ≫ (tr ae).left) z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL' := by
  obtain ⟨u, hu, sq⟩ := exists_comparison D.toPre.P.isLB D'.toPre.P.isLB U.LG.isLB U'.LG.isLB (tr ae).left
    (tr_fst hae) (U.w_gen e) (U'.w_gen e) hw
  have := (U'.gt e).q_hom
  have := (U'.gt e).i_hom
  have hq' : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D'.toPre.X),
      (τ ≫ (U'.gt e).i) ≫ (U'.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U'.gt e).q := fun τ => by
    rw [Category.assoc, (U'.gt e).isKernel.w, MonObj.one_comp, ← Category.assoc, comp_toUnit, Hom.one_def]
  have hm : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D'.toPre.X)
      (y : Z ⟶ thickObj R I e G), ((τ ≫ (U'.gt e).i) * y) ≫ (U'.gt e).q = y ≫ (U'.gt e).q := fun τ y => by
    rw [MonObj.mul_comp, hq', ← MonObj.mul_comp, _root_.one_mul]
  have hF : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {x y : Z ⟶ thickObj R I e G},
      x ≫ (U'.gt e).q = y ≫ (U'.gt e).q →
      x.left ≫ (tr ae).left ≫ (U.gt e).pG.left = y.left ≫ (tr ae).left ≫ (U.gt e).pG.left := fun {Z x y} h => by
    have : x.left ≫ (U'.gt e).q.left = y.left ≫ (U'.gt e).q.left := congrArg (fun q => q.left) h
    rw [hb, reassoc_of% this]
  have him : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {x y : Z ⟶ thickObj R I e G},
      x ≫ (U'.gt e).q = y ≫ (U'.gt e).q → TorusCoord.im (U.gt e) x = TorusCoord.im (U.gt e) y := fun {Z x y} h => by
    apply Over.OverMorphism.ext
    have := pG_congr (U'.gt e) h
    show x.left ≫ (U.gt e).pG.left = y.left ≫ (U.gt e).pG.left
    rw [← hβ]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ β.left) this).trans (Category.assoc _ _ _))
  have htri : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (t t' : Z ⟶ splitTorus _ D'.toPre.X)
      (y : Z ⟶ thickObj R I e G), tri (thick R I e) (U.gt e).pG ![t ≫ (U'.gt e).i, t' ≫ (U'.gt e).i, y] =
      tri (thick R I e) (U.gt e).pG ![1, 1, y] := fun t t' y => by
    show (lift (TorusCoord.im (U.gt e) (t ≫ (U'.gt e).i)) (lift (TorusCoord.im (U.gt e) (t' ≫ (U'.gt e).i))
      (TorusCoord.im (U.gt e) y))).left =
      (lift (TorusCoord.im (U.gt e) 1) (lift (TorusCoord.im (U.gt e) 1) (TorusCoord.im (U.gt e) y))).left
    rw [him (hq' t), him (hq' t')]
  have inv : ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D'.toPre.X)
      (y : Z ⟶ thickObj R I e G) (z : Z.left) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι),
      ((tr ae).left ≫ (U.gt e).pG.left) (y.left z) ∈ D.toPre.P.L.U jM →
      (U'.gt e).pG.left (y.left z) ∈ D'.toPre.P.L.U jM' →
      gw u ((τ ≫ (U'.gt e).i) * y).left z jM (fun _ => jM') = gw u y.left z jM (fun _ => jM') := by
    intro Z₀ τ₀ y₀ z₀ jM jM' m m'
    have := hG.geomConnected
    have := U.smooth
    have := connectedSpace_spec_quotient (I ^ (e + 1)) (Z₀.hom z₀)
    have : GeometricallyConnected (thickObj R I e G).hom :=
      inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (thick R I e)))
    have : ConnectedSpace (thickObj R I e G).left :=
      GroupConn.connectedSpace_of_section (thickObj R I e G).hom (η : 𝟙_ _ ⟶ thickObj R I e G).left (Over.w _)
    obtain ⟨ρ, key⟩ := exists_ratio_translate (U'.gt e).i D.toPre.P.isLB D'.toPre.P.isLB u hu
      (fun _ t y => hF (hm t y)) (fun _ t y => pG_congr _ (hm t y))
    have triv := ratio_eq_one (U'.gt e).i ρ (fun Z z => by
      choose J hJ using fun χ : Z.left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ z)
      choose J' hJ' using fun χ : Z.left ⟶ D'.toPre.P.A.left => exists_chart D'.toPre.P.isLB (χ z)
      choose N hN using fun χ : Z.left ⟶ G.left => exists_chart U.LG.isLB (χ z)
      refine ⟨uV u z J J', fun t y => ?_, fun t t' y => ?_, fun t => ?_⟩
      · rw [uV, uV, hF (hm t y), pG_congr _ (hm t y)]
        exact key Z t y z _ _ (hJ (y.left ≫ (tr ae).left ≫ (U.gt e).pG.left)) (hJ' _)
      · have a := cube_uV hae u hw sq hs (t ≫ (U'.gt e).i) (t' ≫ (U'.gt e).i) y hJ hJ'
        have b := cube_uV hae u hw sq hs 1 1 y hJ hJ'
        rw [htri, htri, tri_congr (U'.gt e) y (hq' t) (hq' t')] at a
        exact mul_right_cancel (mul_right_cancel (a.symm.trans b))
      · have a := even_uV hae u hw sq ha hf (t ≫ (U'.gt e).i) hJ hJ' hN
        have b := even_uV hae u hw sq ha hf (1 : Z ⟶ thickObj R I e G) hJ hJ' hN
        rw [hF (hq' t), pG_congr (U'.gt e) (hq' t)] at a
        exact cancel_even a b)
    rw [key Z₀ τ₀ y₀ z₀ jM jM' m m', triv, map_one, _root_.one_mul]
  haveI := (U'.gt e).q_flat
  haveI := (U'.gt e).q_surj
  haveI := (U'.gt e).q_affine
  obtain ⟨v, hv, hv'⟩ := LevelComparison.exists_iso_descend (U'.gt e).q.left (fstG I e D'.toPre.P.A).left be
    (p := (tr ae).left ≫ (U.gt e).pG.left) (p' := (U'.gt e).pG.left) hb rfl u hu (fun Z g₁ g₂ z j j' h a b => by
      let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (g₂ ≫ (thickObj R I e G).hom)
      let k₂ : Z' ⟶ thickObj R I e G := Over.homMk g₂ rfl
      let k₁ : Z' ⟶ thickObj R I e G := Over.homMk g₁ (by
        change g₁ ≫ (thickObj R I e G).hom = g₂ ≫ (thickObj R I e G).hom
        rw [← Over.w (U'.gt e).q, reassoc_of% h])
      have e₁ : k₁ ≫ (U'.gt e).q = k₂ ≫ (U'.gt e).q := Over.OverMorphism.ext h
      have w : (k₁ * k₂⁻¹) ≫ (U'.gt e).q = toUnit Z' ≫ η[thickObj R I e D'.toPre.P.A] := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, e₁, mul_inv_cancel]
        rfl
      have ht : ((U'.gt e).isKernel.lift _ _ w ≫ (U'.gt e).i) * k₂ = k₁ := by
        rw [(U'.gt e).isKernel.lift_fst, inv_mul_cancel_right]
      have := inv Z' ((U'.gt e).isKernel.lift _ _ w) k₂ z j j' a b
      rw [ht] at this
      exact this)
  refine ⟨v, hv, fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  rw [← sq Z r z jM jM' jL jL' a₁ a₂ a₃ a₄]
  exact congrArg (· * _) (hv' Z r z jM jM' a₁ a₂)

end Level

section Limit

open UnifCompare

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]

theorem gw_trans' {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : UnifPre I D A G)
    (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
    (hM : (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM) (hL : (fstG I e G).left (r z) ∈ U.LG.L.U jL) :
    gw (U.w (e + 1)) (r ≫ thickMap R I e G) z jM (fun _ => jL) = gw (U.w e) r z jM (fun _ => jL) := by
  have hM' : (U.gt (e + 1)).pG.left (thickMap R I e G (r z)) ∈ D.toPre.P.L.U jM :=
    (congrArg (fun g => g (r z) ∈ D.toPre.P.L.U jM) (U.gt_q e)).mpr hM
  have hL' : (fstG I (e + 1) G).left (thickMap R I e G (r z)) ∈ U.LG.L.U jL :=
    (congrArg (fun g => g (r z) ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL
  have hm : r z ∈ thickMap R I e G ⁻¹ᵁ ((D.toPre.P.L.pull (U.gt (e + 1)).pG.left).U (fun _ => jM) ⊓
        (U.LG.L.pull (fstG I (e + 1) G).left).U (fun _ => jL)) ⊓
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓
        (U.LG.L.pull (fstG I e G).left).U (fun _ => jL)) :=
    ⟨⟨mem_pull.2 hM', mem_pull.2 hL'⟩, mem_pull.2 hM, mem_pull.2 hL⟩
  have H := congrArg (gm r z _)
    (U.w_compat e (fun _ => jM, fun _ => jL) _ inf_le_left inf_le_right)
  have h₁ := gm_pull r (thickMap R I e G) z _ hm.1 ((U.w (e + 1)).s (fun _ => jM, fun _ => jL))
  exact h₁.symm.trans ((gm_res r z inf_le_left hm _).symm.trans (H.trans (gm_res r z inf_le_right hm _)))

omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in

theorem thickMap_comm {G' : Over (Spec (CommRingCat.of R))} (e : ℕ) (f₀ : thickObj R I e G' ⟶ thickObj R I e G)
    (f₁ : thickObj R I (e + 1) G' ⟶ thickObj R I (e + 1) G) (f : G'.left ⟶ G.left)
    (h₀ : f₀.left ≫ (fstG I e G).left = (fstG I e G').left ≫ f)
    (h₁ : f₁.left ≫ (fstG I (e + 1) G).left = (fstG I (e + 1) G').left ≫ f) :
    thickMap R I e G' ≫ f₁.left = f₀.left ≫ thickMap R I e G := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((congrArg (thickMap R I e G' ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ f) (trans_comp_proj e G')).trans (h₀.symm.trans
        ((congrArg (f₀.left ≫ ·) (trans_comp_proj e G).symm).trans (Category.assoc _ _ _).symm)))))
  · have a₁ : f₁.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f₁
    have a₀ : f₀.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f₀
    have k : ∀ B : Over (Spec (CommRingCat.of R)), thickMap R I e B ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ thickTrans R I e := fun B => pullback.lift_snd _ _ _
    exact (Category.assoc _ _ _).trans ((congrArg (thickMap R I e G' ≫ ·) a₁).trans ((k G').trans
      ((congrArg (· ≫ thickTrans R I e) a₀.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (f₀.left ≫ ·) (k _).symm).trans (Category.assoc _ _ _).symm)))))

theorem surjective_appTop {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    (U : UnifPre I D A G) : Function.Surjective G.hom.appTop.hom ∧
      Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom := by
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    RigidIsoCube.surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  exact ⟨s₁, surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G A.isAb hg _)
    (surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G A.isAb hg _) s₁)⟩

set_option maxHeartbeats 400000 in

theorem exists_iso_translate [IsLocalRing R] (hR : AdmBase R I) (hG : IsSemiAbelian G) {D D' : DegData R I}
    {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (a : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) (ha : a ^ 2 = 1) (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.toPre.P.A)
    (hab : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left),
      ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left →
      ae ≫ (U.gt e).pG.left = thick R I e ≫ b.left)
    (wL : LB.Iso U'.LG.L (U.LG.L.pull (tr a).left)) (hw : wL.IsGen) (β : D'.toPre.P.A ≅ D.toPre.P.A)
    (hβ : ∀ e, (U'.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) :
    ∃ w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull (padd D.toPre.P.A β.hom (toUnit D'.toPre.P.A ≫ b)).left),
      w.IsGen := by
  rw [isGen_iff] at hw
  obtain ⟨hf, hs⟩ := surjective_appTop U
  obtain ⟨ae, hae⟩ : ∃ ae : ∀ e, 𝟙_ _ ⟶ thickObj R I e G,
      ∀ e, (ae e).left ≫ (fstG I e G).left = thick R I e ≫ a.left :=
    ⟨fun e => Over.homMk (pullback.lift (thick R I e ≫ a.left) (𝟙 _) (by
      rw [Category.assoc, Over.w a]; exact (Category.comp_id _).trans (Category.id_comp _).symm))
      (pullback.lift_snd _ _ _), fun e => pullback.lift_fst _ _ _⟩
  let Φ : D'.toPre.P.A ≅ D.toPre.P.A :=
    { hom := β.hom * (toUnit _ ≫ b)
      inv := (𝟙 _ * (toUnit _ ≫ b)⁻¹) ≫ β.inv
      hom_inv_id := by
        rw [← Category.assoc, MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, ← Category.assoc, comp_toUnit,
          mul_inv_cancel_right, β.hom_inv_id]
      inv_hom_id := by
        rw [MonObj.comp_mul, Category.assoc, β.inv_hom_id, Category.comp_id, ← Category.assoc, comp_toUnit,
          inv_mul_cancel_right] }
  let βe : ∀ e, thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A := fun e =>
    (Over.pullback (thick R I e)).mapIso Φ
  have hβe : ∀ e, (βe e).hom.left ≫ (fstG I e D.toPre.P.A).left = (fstG I e D'.toPre.P.A).left ≫ Φ.hom.left :=
    fun e => pullback.lift_fst _ _ _
  have hb : ∀ e, (tr (ae e)).left ≫ (U.gt e).pG.left =
      (U'.gt e).q.left ≫ (βe e).hom.left ≫ (fstG I e D.toPre.P.A).left := fun e => by
    have h₁ := TorusCoord.im_mul (U.gt e) (toUnit _ ≫ ae e) (𝟙 (thickObj R I e G))
    have h₂ : TorusCoord.im (U.gt e) (toUnit (thickObj R I e G) ≫ ae e) = toUnit _ ≫ b := by
      apply Over.OverMorphism.ext
      show ((thickObj R I e G).hom ≫ (ae e).left) ≫ (U.gt e).pG.left = ((thickObj R I e G).hom ≫ thick R I e) ≫ b.left
      rw [Category.assoc, Category.assoc]
      exact congrArg ((thickObj R I e G).hom ≫ ·) (hab e _ (Over.w (ae e)) (hae e))
    have h₃ : TorusCoord.im (U.gt e) (𝟙 (thickObj R I e G)) = (U'.gt e).pG ≫ β.hom :=
      Over.OverMorphism.ext ((Category.id_comp _).trans (hβ e).symm)
    have h₄ : (U'.gt e).pG ≫ Φ.hom = ((U'.gt e).pG ≫ β.hom) * (toUnit _ ≫ b) := by
      show (U'.gt e).pG ≫ (β.hom * (toUnit _ ≫ b)) = _
      rw [MonObj.comp_mul, ← Category.assoc _ (toUnit _), comp_toUnit]
    rw [h₂, h₃, _root_.mul_comm (toUnit _ ≫ b), ← h₄] at h₁
    rw [hβe]
    exact (congrArg (fun q => q.left) h₁).trans (Category.assoc (U'.gt e).q.left _ _)
  choose v hvg hv using fun e => exists_level (hae e) hw hG ha hf hs β.hom (hβ e) _ (hb e)
  have hc : ∀ e, thickMap R I e D'.toPre.P.A ≫ (βe (e + 1)).hom.left =
      (βe e).hom.left ≫ thickMap R I e D.toPre.P.A := fun e => thickMap_comm e _ _ _ (hβe e) (hβe (e + 1))
  have ht : ∀ e, thickMap R I e G ≫ (tr (ae (e + 1))).left = (tr (ae e)).left ≫ thickMap R I e G := fun e =>
    thickMap_comm e _ _ _ (tr_fst (hae e)) (tr_fst (hae (e + 1)))
  obtain ⟨hN, -, -, hC⟩ := hR
  obtain ⟨Ψ, w, hwg, H⟩ := exists_iso_of_compatible_thickenings GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    GlobalTheory.abelianSchemeLaws_all.1.ample R I D.toPre.P D'.toPre.P βe v hvg hc (by
    intro e Z r z j j' hj hj'
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    have hm : ∀ y : (thickObj R I e D'.toPre.P.A).left,
        y ∈ (D.toPre.P.L.pull ((βe e).hom.left ≫ (fstG I e D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left).U (fun _ => j') →
        thickMap R I e D'.toPre.P.A y ∈
          (D.toPre.P.L.pull ((βe (e + 1)).hom.left ≫ (fstG I (e + 1) D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I (e + 1) D'.toPre.P.A).left).U (fun _ => j') := by
      intro y hy
      have k : thickMap R I e D'.toPre.P.A ≫ (βe (e + 1)).hom.left ≫ (fstG I (e + 1) D.toPre.P.A).left =
          (βe e).hom.left ≫ (fstG I e D.toPre.P.A).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I (e + 1) D.toPre.P.A).left) (hc e)).trans
          ((Category.assoc _ _ _).trans (congrArg ((βe e).hom.left ≫ ·) (trans_comp_proj e _))))
      exact ⟨mem_pull.2 ((congrArg (fun g => g y ∈ D.toPre.P.L.U j) k).mpr (mem_pull.1 hy.1)),
        mem_pull.2 ((congrArg (fun g => g y ∈ D'.toPre.P.L.U j') (trans_comp_proj e _)).mpr
          (mem_pull.1 hy.2))⟩
    have hz : r z ∈ (D.toPre.P.L.pull ((βe e).hom.left ≫ (fstG I e D.toPre.P.A).left)).U (fun _ => j) ⊓
          (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left).U (fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    refine (gm_pull r _ z _ (hm _ hz) _).symm.trans
      (gm_eq_of_flat_surjective (U'.gt e).q.left _ _ (fun x _ hx => ?_) r z (hm _ hz) hz)
    refine (gm_pull _ _ x _ (hm _ hx) _).trans ?_
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((tr a).left ((fstG I e G).left x))
    obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG I e G).left x)
    have hM : (U.gt e).pG.left ((tr (ae e)).left x) ∈ D.toPre.P.L.U j :=
      (congrArg (fun g => g x ∈ D.toPre.P.L.U j) (hb e)).mpr (mem_pull.1 hx.1)
    have hM' : (U'.gt e).pG.left x ∈ D'.toPre.P.L.U j' := mem_pull.1 hx.2
    have k₁ : (thickMap R I e G ≫ (tr (ae (e + 1))).left) ≫ (U.gt (e + 1)).pG.left =
        (tr (ae e)).left ≫ (U.gt e).pG.left :=
      (congrArg (· ≫ (U.gt (e + 1)).pG.left) (ht e)).trans ((Category.assoc _ _ _).trans
        (congrArg ((tr (ae e)).left ≫ ·) (U.gt_q e)))
    have h₀ := hv e _ (𝟙 _) x j j' jL jL' hM hM' hL hL'
    have h₁ := hv (e + 1) _ (thickMap R I e G) x j j' jL jL'
      ((congrArg (fun g => g x ∈ D.toPre.P.L.U j) k₁).mpr hM)
      ((congrArg (fun g => g x ∈ D'.toPre.P.L.U j') (U'.gt_q e)).mpr hM')
      ((congrArg (fun g => (tr a).left (g x) ∈ U.LG.L.U jL) (trans_comp_proj e G)).mpr hL)
      ((congrArg (fun g => g x ∈ U'.LG.L.U jL') (trans_comp_proj e G)).mpr hL')
    rw [gw_trans U' e x j' jL' hM' hL', ht, gw_trans' U e (tr (ae e)).left x j jL hM
      ((congrArg (fun g => g x ∈ U.LG.L.U jL) (tr_fst (hae e))).mpr hL), trans_comp_q, trans_comp_proj] at h₁
    rw [Category.id_comp, Category.id_comp, Category.id_comp] at h₀
    exact mul_right_cancel (h₁.trans h₀.symm))
  have := D'.toPre.P.isAb.proper
  have := D.toPre.P.isAb.proper
  have e : Ψ.hom = padd D.toPre.P.A β.hom (toUnit D'.toPre.P.A ≫ b) :=
    hom_eq_of_thickenings_of_isProper R I (IsAdicComplete.le_jacobson_bot I) _ _ Ψ.hom Φ.hom
      fun e => (H e).1.trans (hβe e)
  rw [← e]
  exact ⟨w, hwg⟩

end Limit

end GlobalTheory.MumCmp.Transl

theorem GlobalTheory.MumCmp.exists_iso_twist_of_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∃ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen ∧ ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left)) := by
  intro R _ _ _ hR D A G _ _ hG U g _ a ha hab A₂ D₂ U₂ ⟨wL, hw⟩ β hβ hq
  obtain ⟨w, hw⟩ := GlobalTheory.MumCmp.Transl.exists_iso_translate hR.1 hG U.toUnifPre U₂.toUnifPre a ha g.b
    (fun e ae h₁ h₂ => (hab e ae h₁ h₂).1) wL hw β hq
  exact GlobalTheory.T.exists_rigidified_translatedBundle_iso_psi_zero R _ D D₂ g β.hom hβ w hw
