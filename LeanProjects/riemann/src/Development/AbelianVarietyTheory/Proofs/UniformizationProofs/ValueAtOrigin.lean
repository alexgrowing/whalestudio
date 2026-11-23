import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.EvalZero
open GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

theorem gm_comp_map {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U)
    (a : Γ(X, U)ˣ) : (gm (r ≫ g) z U a).val = (r.stalkMap z).hom (gm g (r z) U a).val := by
  rw [← gs_unit (r ≫ g) z U h, ← gs_unit g (r z) U h, ← gs_pull r g z U h, gs_stalkMap r z _ h]
  exact congrArg _ ((gs_pull (𝟙 _) g (r z) U h _).trans (by rw [Category.id_comp]))

theorem val_comp_map {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y') (g : Y' ⟶ Y) (q : Z ⟶ Y) (hq : r ≫ g = q) (z : Z) {J}
    (hJ : Good L z J) : (val t q z J).val = (r.stalkMap z).hom (val t g (r z) (fun ψ => J (r ≫ ψ))).val := by
  subst hq
  have hJ' : Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => hJ (r ≫ ψ)
  rw [val_of t (r ≫ g) z J (fun k => J (r ≫ g ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_comp_map r g z _ (hJ'.mem φ g) _

theorem alg_norm {M : Type} [CommGroup M] {a g₀ p₀ r₀ p r g x y q : M} (h₀ : q = a * p) (h₁ : a = g₀ * (p₀ * r₀)⁻¹)
    (h₂ : p = y * x⁻¹ * p₀) (h₃ : r = x * r₀) (h₄ : g = y * g₀) : q * r = g := by
  rw [h₀, h₁, h₂, h₃, h₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem alg_value {M K : Type} [CommRing M] [Fintype K] {k : ℕ} {p r g : Mˣ} {s s' b : M} {u v : K → M}
    (h₁ : s' = (p ^ k).val * s) (h₂ : s' = ∑ i, u i) (h₃ : s = b * (r ^ k).val) (h₄ : p.val * r.val = g.val)
    (h₅ : ∀ i, u i = v i * (g ^ k).val) : b = ∑ i, v i := by
  refine (g ^ k).mul_left_inj.1 ?_
  rw [Finset.sum_mul, ← Finset.sum_congr rfl fun i _ => h₅ i, ← h₂, h₁, h₃]
  simp only [Units.val_pow_eq_pow_val, ← h₄]
  ring

theorem sumI_map {R : Type} [CommRing R] (I : Ideal R) {E Ix : Type} [AddCommGroup E] [Module R E] (φ : R →ₗ[R] E)
    (a : Ix → R) (x : R) (h : ∀ n : ℕ, ∃ S : Finset Ix, ∀ T : Finset Ix, S ⊆ T → x - ∑ i ∈ T, a i ∈ I ^ (n + 1)) :
    SumI I (fun i => φ (a i)) (φ x) := by
  refine ⟨Submodule.map φ ⊤, (Module.Finite.fg_top).map φ, ⟨x, trivial, rfl⟩, fun i => ⟨a i, trivial, rfl⟩, fun n => ?_⟩
  obtain ⟨S, hS⟩ := h n
  refine ⟨S, fun T hT => ?_⟩
  rw [← map_sum, ← map_sub, ← Submodule.map_smul'']
  refine Submodule.mem_map_of_mem ?_
  simpa using Submodule.smul_mem_smul (Ideal.pow_le_pow_right (Nat.le_succ n) (hS T hT)) (Submodule.mem_top (x := (1 : R)))

theorem sumF_map {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {Ix : Type} (a : Ix → R) (x : R)
    (h : ∀ n : ℕ, ∃ S : Finset Ix, ∀ T : Finset Ix, S ⊆ T → x - ∑ i ∈ T, a i ∈ I ^ (n + 1)) :
    SumF I F (fun i => algebraMap (FractionRing R) F (algebraMap R _ (a i)))
      (algebraMap (FractionRing R) F (algebraMap R _ x)) := by
  let _ : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  have e : ∀ r : R, LinearMap.toSpanSingleton R F 1 r = algebraMap (FractionRing R) F (algebraMap R _ r) :=
    fun r => (Algebra.algebraMap_eq_smul_one (algebraMap R (FractionRing R) r)).symm
  have := sumI_map I (LinearMap.toSpanSingleton R F 1) a x h
  simp only [e] at this
  exact this

theorem sumF_comb {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hI : AdmBase R I) (F : Type) [Field F]
    [Algebra (FractionRing R) F] {Ix K : Type} (S : Finset K) (c : K → F) (x : K → Ix → F) (s : K → F)
    (h : ∀ i, SumF I F (x i) (s i)) : SumF I F (fun α => ∑ i ∈ S, c i * x i α) (∑ i ∈ S, c i * s i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using sumF_map I F (fun _ : Ix => 0) 0 (fun n => ⟨∅, fun T _ => by simp⟩)
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (GlobalTheory.AdicSum.sumF_calculus R I hI F Ix _ _ _ _).2.1 (h a) ih _

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem eK_gen : eSec ((Over.pullback (jK R)).obj G) ≫ U.gen.hom.left = eSec A.A := by
  have := U.gen_hom
  exact congrArg (·.left) (IsMonHom.one_hom U.gen.hom)

omit [IsDomain R] [IsCommMonObj G] in
theorem eK_fst : eSec ((Over.pullback (jK R)).obj G) ≫ pullback.fst G.hom (jK R) = jK R ≫ eSec G := by
  simp [eSec]
  rw [pullback.lift_fst, ← Category.assoc, ← pullback.condition, Category.comp_id]

theorem exists_normW (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) : ∃ w₀, NormW U w₀ ρ := by
  obtain ⟨w, hw⟩ := U.ext
  let z₀ : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  obtain ⟨JA₀, hA₀⟩ := exists_good' A.isLB z₀
  obtain ⟨JG₀, hG₀⟩ := exists_good' U.LG.isLB z₀
  let eK : Spec (CommRingCat.of (FractionRing R)) ⟶ ((Over.pullback (jK R)).obj G).left :=
    eSec ((Over.pullback (jK R)).obj G)
  have h₁ : eK ≫ U.gen.hom.left = eSec A.A := eK_gen U
  have h₂ : eK ≫ pullback.fst G.hom (jK R) = jK R ≫ eSec G := eK_fst
  have h₃ : eK ≫ ((Over.pullback (jK R)).obj G).hom = 𝟙 _ := Over.w η[(Over.pullback (jK R)).obj G]
  have hsurj : ∀ u : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z₀)ˣ,
      ∃ a : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)ˣ, gm (𝟙 _) z₀ ⊤ a = u := by
    intro u
    obtain ⟨V, hV, s, hs⟩ := (Spec (CommRingCat.of (FractionRing R))).presheaf.exists_germ_eq u.val
    obtain rfl : V = ⊤ := eq_top_iff.2 fun y _ =>
      (Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z₀ y) ▸ hV
    have hu : IsUnit s := (Spec (CommRingCat.of (FractionRing R))).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain rfl : z₀ = y := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z₀ y
      exact (congrArg IsUnit hs).mpr u.isUnit
    exact ⟨hu.unit, Units.ext ((gm_val _ z₀ ⊤ trivial _).trans hs)⟩
  obtain ⟨a, ha⟩ := hsurj (val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (jK R) z₀ JG₀ *
    (pw w eK z₀ (JA₀ (eSec A.A)) (JG₀ (jK R ≫ eSec G)) *
      val (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) (Z := Spec (CommRingCat.of (FractionRing R)))
        ρ (𝟙 _) z₀ JA₀)⁻¹)
  refine ⟨scaleGen (pullU ((Over.pullback (jK R)).obj G).hom ⊤ a) w, scaleGen_isGen _ _ hw, hρ, fun z JA JG hA hG => ?_⟩
  obtain rfl : z₀ = z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z₀ z
  have mA : ∀ J, Good A.L z₀ J → U.gen.hom.left (eK z₀) ∈ A.L.U (J (eSec A.A)) := fun J hJ =>
    (congrArg (fun q => q z₀ ∈ A.L.U (J (eSec A.A))) h₁).mpr (hJ _)
  have mG : ∀ J, Good U.LG.L z₀ J → pullback.fst G.hom (jK R) (eK z₀) ∈ U.LG.L.U (J (jK R ≫ eSec G)) := fun J hJ =>
    (congrArg (fun q => q z₀ ∈ U.LG.L.U (J (jK R ≫ eSec G))) h₂).mpr (hJ _)
  have b₀ : gw (scaleGen (pullU ((Over.pullback (jK R)).obj G).hom ⊤ a) w) eK z₀ (JG (jK R ≫ eSec G))
      (fun _ => JA (eSec A.A)) = gm (𝟙 _) z₀ ⊤ a * pw w eK z₀ (JA (eSec A.A)) (JG (jK R ≫ eSec G)) := by
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ rfl)
    refine (gm_res eK z₀ _ (by exact ⟨mem_pull.2 (mG _ hG), mem_pull.2 (mA _ hA)⟩) _).trans ?_
    exact (gm_pull eK _ z₀ ⊤ trivial a).trans (by rw [h₃])
  have b₁ := pw_trans hw eK z₀ (mA _ hA) (mA _ hA₀) (mG _ hG) (mG _ hG₀)
  have b₂ := val_tr (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1)
    (Z := Spec (CommRingCat.of (FractionRing R))) hρ (𝟙 _) hA hA₀
  have b₃ := val_tr (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rigGen (jK R) hG hG₀
  rw [h₁, h₂] at b₁
  rw [Fintype.prod_unique, zpow_one] at b₂ b₃
  rw [Category.id_comp] at b₂
  exact alg_norm b₀ ha b₁ b₂ b₃

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem normW_ext {w₀ : W0 U} {ρ : LB.Gen (A.L.pull (eSec A.A))} (h : NormW U w₀ ρ) (z : Sp F) {JA JG}
    (hA : Good A.L z JA) (hG : Good U.LG.L z JG) :
    (pw w₀ (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) z (JA (jFK (R := R) F ≫ eSec A.A))
        (JG ((jFK (R := R) F ≫ jK R) ≫ eSec G))).val *
      (val (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) ρ (jFK (R := R) F) z JA).val =
      (val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (jFK (R := R) F ≫ jK R) z JG).val := by
  have hA' : Good A.L (jFK (R := R) F z) (fun ψ => JA (jFK (R := R) F ≫ ψ)) := fun ψ => hA (jFK (R := R) F ≫ ψ)
  have hG' : Good U.LG.L (jFK (R := R) F z) (fun ψ => JG (jFK (R := R) F ≫ ψ)) := fun ψ => hG (jFK (R := R) F ≫ ψ)
  have e := congrArg (fun u => ((jFK (R := R) F).stalkMap z).hom u.val) (h.2.2 _ _ _ hA' hG')
  have mA := (congrArg (fun q => q (jFK (R := R) F z) ∈ A.L.U (JA (jFK (R := R) F ≫ eSec A.A))) (eK_gen U)).mpr (hA' _)
  have mG := (congrArg (fun q => q (jFK (R := R) F z) ∈ U.LG.L.U (JG (jFK (R := R) F ≫ jK R ≫ eSec G)))
    (eK_fst (G := G))).mpr (hG' _)
  rw [Category.assoc]
  refine Eq.trans ?_ (e.trans (val_comp_map _ _ _ _ rfl z hG).symm)
  refine Eq.trans (congrArg₂ (· * ·) ?_ ?_) (map_mul _ _ _).symm
  · exact gm_comp_map _ _ z _ (by exact ⟨mem_pull.2 mG, mem_pull.2 mA⟩) _
  · exact val_comp_map _ _ _ _ (Category.comp_id _) z hA

theorem val_rigT {S : Scheme.{0}} (B : Over S) [GrpObj B] (L : LB B.left) (ρ : LB.Gen (L.pull (eSec B)))
    (T : Over S) (k : ℕ) (z : T.left) {J} (hJ : Good L z J) :
    val (rigT B L ρ T (k : ℤ)) (𝟙 _) z J =
      val (L := L) (φ := fun _ : PUnit => eSec B) (ε := fun _ => 1) (Z := T.left) ρ T.hom z J ^ k := by
  rw [val_of (rigT B L ρ T (k : ℤ)) (𝟙 _) z J (fun _ => J (T.hom ≫ eSec B)) (fun _ => congrArg J (Category.id_comp _))]
  have hm : (𝟙 T.left : T.left ⟶ T.left) z ∈
      LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec B) (fun _ => J (T.hom ≫ eSec B)) :=
    Set.mem_iInter.2 fun _ => hJ (T.hom ≫ eSec B)
  have e := (gm_res (𝟙 T.left) z (rigT_le B L (fun _ => J (T.hom ≫ eSec B))) hm _).trans
    (gm_pull (𝟙 T.left) T.hom z _ (rigT_le B L _ hm) (ρ.s (fun _ => J (T.hom ≫ eSec B))))
  rw [Category.id_comp] at e
  exact (map_zpow _ _ _).trans ((zpow_natCast _ _).trans (congrArg (· ^ k) e))

omit [IsDomain R] in

theorem cst_base (z : (TF (R := R) F).left) (a : R) :
    Geo.Tor.cst (jFK (R := R) F ≫ jK R) z a = cstH z (algebraMap (FractionRing R) F (algebraMap R _ a)) :=
  ((GlobalTheory.ExpansionValueZero.cst_comp _ _ z a).trans (H1.gs_spec _ z _)).trans (cst_eq z _)

theorem coef_comb {D : DegPre R} {k n : ℕ} (s : Fam D F k) (c : Fin n → F) (f : Fin n → ∀ α : D.X, D.SecB k α) (α : D.X)
    (hs : GeneratorPullback.SecLin D.P.L (DegPre.famφ D F α) (DegPre.famε k) (s.s α)
        (D.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D F).left
        (fun i => scal (fst (TF (R := R) F) D.P.A).left (c i)))
    (a : Fin n → R) (ha : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good D.P.L z J →
      sval (f i α) (r ≫ eSec D.P.A) z J = Geo.Tor.cst r z (a i) * (val (L := D.P.L) D.rig r z J ^ k).val)
    (g : GtPtF D F) (w : Frm D F k g.b) (hg : g.IsZero) (hw : FrmOne w) :
    coef s g w α = ∑ i, c i * algebraMap (FractionRing R) F (algebraMap R _ (a i)) := by
  obtain ⟨hb, hv⟩ := (isZero_iff g).1 hg
  refine coef_eq fun z J hJ => ?_
  have e₁ : lift (𝟙 (TF (R := R) F)) g.b = lift (𝟙 (TF (R := R) F)) 1 := by rw [hb]
  have e₂ : (lift (𝟙 (TF (R := R) F)) (1 : _ ⟶ D.P.A)).left ≫ (DegPre.prB D F).left =
      (jFK (R := R) F ≫ jK R) ≫ eSec D.P.A := GC.zF_prB D F
  have e₃ : (lift (𝟙 (TF (R := R) F)) (1 : _ ⟶ D.P.A)).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  rw [hw.2 z J hJ, hv α z J hJ, e₁, secLin_val hs _ z hJ, e₂, Units.val_one, _root_.mul_one, _root_.mul_one, cst_eq,
    map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have b : gs (lift (𝟙 (TF (R := R) F)) (1 : _ ⟶ D.P.A)).left z ⊤ (scal (fst (TF (R := R) F) D.P.A).left (c i)) =
      cstH z (c i) := ((gs_pull _ _ z ⊤ trivial _).trans (by rw [e₃]; rfl)).trans (cst_eq z _)
  rw [b, map_mul, _root_.mul_assoc, ← cst_base]
  exact congrArg _ (ha i _ _ z J hJ).symm

theorem value_comb {w₀ : W0 U} {ρ : LB.Gen (A.L.pull (eSec A.A))} (h : NormW U w₀ ρ) {k n : ℕ} (t : SecA A F k)
    (σ' : U.SecGF F k)
    (hR : GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k
      (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) σ')
    (c : Fin n → F) (σ : Fin n → H0 U.LG.L k)
    (hσ : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (k : ℤ)) σ'
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c i)))
    (x : Fin n → R) (hx : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good U.LG.L z J →
      sval (σ i) (r ≫ eSec G) z J = Geo.Tor.cst r z (x i) * (val (L := U.LG.L) U.LG.rig r z J ^ k).val)
    (b : F) (hb : ∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J =
      @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z b) *
        (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val) :
    b = ∑ i, c i * algebraMap (FractionRing R) F (algebraMap R _ (x i)) := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨JA, hA⟩ := exists_good' (Z := (TFK (R := R) F).left) A.isLB z
  obtain ⟨JG, hG⟩ := exists_good' (Z := (TFK (R := R) F).left) U.LG.isLB z
  have := U.gen_hom
  let r : TFK (R := R) F ⟶ UnifPre.GF (G := G) F := lift (𝟙 _) 1
  have e₁ : r.left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G) := by
    rw [← Over.comp_left, lift_snd]; rfl
  have e₂ : r.left ≫ (U.genF F).left = (ptSecT A.A 1).left := by
    rw [← Over.comp_left]
    congr 1
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simp [r, ptSecT]
    · simp [r, ptSecT, MonObj.one_comp]
  have e₃ : r.left ≫ UnifPre.gFK (G := G) F = (jFK (R := R) F ≫ jK R) ≫ eSec G := by
    rw [← Category.assoc, e₁, Category.assoc, Category.assoc]
    exact congrArg _ eK_fst
  have e₄ : r.left ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have e₅ : (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) ≫ U.gen.hom.left = jFK (R := R) F ≫ eSec A.A :=
    (Category.assoc _ _ _).trans (congrArg _ (eK_gen U))
  have e₆ : (jFK (R := R) F ≫ eSec ((Over.pullback (jK R)).obj G)) ≫ pullback.fst G.hom (jK R) =
      (jFK (R := R) F ≫ jK R) ≫ eSec G :=
    (Category.assoc _ _ _).trans ((congrArg _ eK_fst).trans (Category.assoc _ _ _).symm)
  have a₁ := isoRel_val hR r.left z hA hG
  have a₂ := secLin_val hσ r.left z hG
  have a₃ := hb z JA hA
  have a₄ := normW_ext U F h z hA hG
  rw [Category.comp_id, e₁, e₂] at a₁
  rw [e₃] at a₂
  rw [val_rigT _ _ _ _ _ _ hA] at a₃
  have a₅ : ∀ i, gs r.left z ⊤ (scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c i)) *
      sval (Z := (TFK (R := R) F).left) (σ i) ((jFK (R := R) F ≫ jK R) ≫ eSec G) z JG =
      @id ((TFK (R := R) F).left.presheaf.stalk z)
        (cstH (R := R) z (c i * algebraMap (FractionRing R) F (algebraMap R _ (x i)))) *
        (val (L := U.LG.L) (Z := (TFK (R := R) F).left) U.LG.rig (jFK (R := R) F ≫ jK R) z JG ^ k).val := fun i => by
    rw [map_mul, ← cst_base]
    exact (congrArg₂ (· * ·) (((gs_pull _ _ z ⊤ trivial _).trans (by rw [e₄]; rfl)).trans (cst_eq (R := R) z _))
      (hx i _ _ z JG hG)).trans (_root_.mul_assoc _ _ _).symm
  apply cstH_inj (R := R) z
  rw [map_sum, ← cst_eq]
  erw [e₅, e₆] at a₁
  exact alg_value a₁ a₂ a₃ a₄ a₅

theorem value_at_origin : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => (∃ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen) ∧ (∀ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen → ∃ w₀, NormW U.toUnifPre w₀ ρ) ∧ ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (k : ℕ) (t : SecA A F k) s, U.ExpandsF F k w₀ t s → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b), g.IsZero → FrmOne w → ∀ c : F, (∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val) → SumF I F (coef s g w) c := by
  intro _ R _ _ _ I hI D A G _ _ _ U F _ _ _
  refine ⟨exists_gen_pt (Y := Spec (CommRingCat.of (FractionRing R))) A.isLB
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
      (fun y => Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _) _ _,
    exists_normW U.toUnifPre, ?_⟩
  rintro w₀ ρ h k t s ⟨σ', hR, n, c, σ, f, hE, hσ, hs⟩ g w hg hw b hb
  choose a ha using fun i α => exists_value D.toPre k α (f i α)
  choose x hx using fun i => exists_coeff (A := R) U.LG.isLB (σ i) (eSec G) (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig k)
    (powGen_isGen _ _ _ _ U.LG.rigGen k) (fun W _ f => by simp)
  have hx' : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good U.LG.L z J →
      sval (σ i) (r ≫ eSec G) z J = Geo.Tor.cst r z (x i) * (val (L := U.LG.L) U.LG.rig r z J ^ k).val :=
    fun i Z r z J hJ => (hx i Z r z J hJ).trans (by rw [val_pow])
  rw [value_comb U.toUnifPre F h t σ' hR c σ hσ x hx' b hb,
    funext fun α => coef_comb F s c f α (hs α) (fun i => a i α) (fun i => ha i α) g w hg hw]
  exact sumF_comb hI F _ c _ _ fun i => sumF_map I F (a i) (x i) fun e =>
    value_sub_sum_mem U.toUnifPre e k (σ i) (f i) (hE i e) (x i) (hx' i) (a i) (ha i)

end GlobalTheory.UT.EvalZero
end
