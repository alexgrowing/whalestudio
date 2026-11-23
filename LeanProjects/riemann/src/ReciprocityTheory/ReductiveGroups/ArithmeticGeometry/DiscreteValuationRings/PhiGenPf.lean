import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

def cP (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ

theorem cPoint_add (T : Over (Spec (CommRingCat.of R))) (a b : D.X) : cP D T (a + b) = cP D T a * cP D T b := by
  simp only [cP, D.c_add, padd]
  rw [← Category.assoc, comp_lift]
  rfl

theorem cPoint_nsmul (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (a : D.X) : cP D T (k • a) = cP D T a ^ k := by
  induction k with
  | zero =>
    have h0 : cP D T 0 = cP D T 0 * cP D T 0 := by rw [← cPoint_add, add_zero]
    simpa using h0
  | succ k ih => rw [succ_nsmul, cPoint_add, ih, pow_succ]

theorem comp_cP {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (a : D.X) : ρ ≫ cP D T a = cP D T' a := by
  simp only [cP, ← Category.assoc]
  congr 1
  exact toUnit_unique _ _

abbrev th {T : Over (Spec (CommRingCat.of R))} (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) := cubV D.cub z J

theorem surj_appTop (hG : GlobalFnsSt) : Function.Surjective (fst (TF (R := R) F) D.P.A).left.appTop.hom := by
  have hA : IsAbelianScheme (DegPre.BFo D F) :=
    { comm := inferInstance
      smooth := by have := D.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := D.P.isAb.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D.P.isAb.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have hb := (hG _ _ hA).2
  have e : (fst (TF (R := R) F) D.P.A).left =
      (pullbackSymmetry (DegPre.jFR (R := R) F) D.P.A.hom).hom ≫ pullback.snd D.P.A.hom (DegPre.jFR (R := R) F) :=
    (pullbackSymmetry_hom_comp_snd _ _).symm
  rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  have : IsIso (pullbackSymmetry (DegPre.jFR (R := R) F) D.P.A.hom).hom.appTop :=
    inferInstanceAs (IsIso ((pullbackSymmetry (DegPre.jFR (R := R) F) D.P.A.hom).hom.app ⊤))
  exact (ConcreteCategory.bijective_of_isIso
    (pullbackSymmetry (DegPre.jFR (R := R) F) D.P.A.hom).hom.appTop).2.comp hb

theorem tr_fst (m : TF (R := R) F ⟶ D.P.A) : DegPre.trPt D F m ≫ fst _ _ = fst _ _ := by
  simp [DegPre.trPt]

theorem tr_pr (m : TF (R := R) F ⟶ D.P.A) :
    DegPre.trPt D F m ≫ DegPre.prB D F = DegPre.prB D F * (fst _ _ ≫ m) := by
  simp only [DegPre.trPt, DegPre.prB, lift_snd, padd]
  rfl

theorem trF_eq (mu : D.X) : DegPre.trF D F mu = DegPre.trPt D F (cP D _ mu) := by
  simp [DegPre.trF, DegPre.trPt, cP]

theorem prod_fam {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F) (α : D.X) (k : ℕ) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ DegPre.famφ D F α i) ^ DegPre.famε k i =
      h (ρ ≫ DegPre.prB D F).left ^ ((k : ℤ) - 1) * h (cP D T α * (ρ ≫ DegPre.prB D F)).left * (h (cP D T α).left)⁻¹ *
        h (1 : T ⟶ D.P.A).left := by
  have e₁ : ρ.left ≫ DegPre.famφ D F α 1 = (cP D T α * (ρ ≫ DegPre.prB D F)).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (DegPre.prB D F) (cP D _ α)).trans (by rw [comp_cP, mul_comm]))
  have e₂ : ρ.left ≫ DegPre.famφ D F α 2 = (cP D T α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₃ : ρ.left ≫ DegPre.famφ D F α 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

theorem prod_neg {K U : Type} [Fintype K] [CommGroup U] (f : K → U) (e : K → ℤ) {c : U} (h : ∏ i, f i ^ e i = c) :
    ∏ i, f i ^ (-e i) = c⁻¹ := by
  simp only [zpow_neg, Finset.prod_inv_distrib, h]

theorem prod_sum₂ {K K' U : Type} [Fintype K] [Fintype K'] [CommGroup U] (f : K ⊕ K' → U) {c c' : U}
    (h : ∏ i, f (.inl i) = c) (h' : ∏ i, f (.inr i) = c') : ∏ i, f i = c * c' := by
  rw [Fintype.prod_sum_type, h, h']

def uVal (k : ℕ) (α : D.X) (m : TF (R := R) F ⟶ D.P.A) {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F)
    (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) : (T.left.presheaf.stalk z)ˣ :=
  cubN (th D z J) k (cP D T α) (ρ ≫ fst _ _ ≫ m) (ρ ≫ DegPre.prB D F) *
    (th D z J (cP D T α) (ρ ≫ DegPre.prB D F) (ρ ≫ fst _ _ ≫ m))⁻¹

theorem gen_u (hG : GlobalFnsSt) (k : ℕ) (α α' : D.X) (m : TF (R := R) F ⟶ D.P.A)
    (hα : cP D _ α' = cP D _ α * m ^ k) {K : Type} [Fintype K] {φ : K → ((TF (R := R) F).left ⟶ D.P.A.left)} {ε : K → ℤ}
    (v : LB.Gen (LB.LinComb D.P.L φ ε)) (hv : v.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : ((TF (R := R) F).left ⟶ D.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
      (h (cP D _ α * m).left)⁻¹ * h (cP D _ α).left * h m.left * (h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹ *
        (h m.left ^ k)⁻¹ * h (1 : TF (R := R) F ⟶ D.P.A).left ^ k) :
    (∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (DegPre.famφ D F α')
        (fun i => (DegPre.trPt D F m).left ≫ DegPre.famφ D F α i)) (DegPre.deltaε k)), u.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) v) ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (DegPre.famφ D F α')
        (fun i => (DegPre.trPt D F m).left ≫ DegPre.famφ D F α i)) (DegPre.deltaε k)), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) v →
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
        val u ρ.left z J = uVal D F k α m ρ z J * val v (ρ ≫ fst _ _).left z J := by
  let a : DegPre.BF D F ⟶ D.P.A := cP D _ α
  let mm : DegPre.BF D F ⟶ D.P.A := fst _ _ ≫ m
  let x : DegPre.BF D F ⟶ D.P.A := DegPre.prB D F
  have hα' : cP D (DegPre.BF D F) α' = a * mm ^ k := by
    rw [← comp_cP D (fst (TF (R := R) F) D.P.A), hα]
    exact (map_mul (preHom (fst (TF (R := R) F) D.P.A)) _ _).trans
      (congrArg₂ (· * ·) (comp_cP D _ α) (map_pow (preHom (fst (TF (R := R) F) D.P.A)) _ _))
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub a mm x k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.P.isLB (φ' := Sum.elim (DegPre.famφ D F α')
      (fun i => (DegPre.trPt D F m).left ≫ DegPre.famφ D F α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a x mm h
      have p₂ := hF U (fun q => h ((fst (TF (R := R) F) D.P.A).left ≫ q))
      have p₃ := prod_fam D F (𝟙 _) α' k h
      have p₄ := prod_fam D F (DegPre.trPt D F m) α k h
      have q₁ : (fst (TF (R := R) F) D.P.A).left ≫ (cP D _ α * m).left = (a * mm).left :=
        congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) ((MonObj.comp_mul (fst (TF (R := R) F) D.P.A) (cP D _ α) m).trans
          (congrArg (· * mm) (comp_cP D (fst (TF (R := R) F) D.P.A) α)))
      have q₂ : (fst (TF (R := R) F) D.P.A).left ≫ (cP D _ α).left = a.left :=
        congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (comp_cP D (fst (TF (R := R) F) D.P.A) α)
      have q₃ : (fst (TF (R := R) F) D.P.A).left ≫ (1 : TF (R := R) F ⟶ D.P.A).left = (1 : DegPre.BF D F ⟶ D.P.A).left :=
        congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (fst (TF (R := R) F) D.P.A))
      have q₄ : (fst (TF (R := R) F) D.P.A).left ≫ m.left = mm.left := rfl
      rw [q₁, q₂, q₃, q₄] at p₂
      simp only [Over.id_left, Category.id_comp] at p₃
      rw [hα'] at p₃
      rw [tr_pr] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := K) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)
      rw [← _root_.mul_assoc (cP D _ α), mul_comm mm x]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift x mm)).left)))
      (LB.pullGen D.P.L _ _ v (fst (TF (R := R) F) D.P.A).left))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _)))
      (pullGen_isGen _ _ _ _ hv _))
  have val₀ : ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
      val u₀ ρ.left z J = uVal D F k α m ρ z J * val v (ρ ≫ fst _ _).left z J := fun T ρ z J hJ => by
    refine (vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      ((congrArg₂ (· * ·) (vN T ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.cub ρ hJ _ _ _)))).trans ?_))
      (val_pull hJ _ _ _)))
    rw [uVal, ← comp_cP D ρ α]
  have z₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
  have at₀ : ∀ y J, Good D.P.L y J → val u₀ (DegPre.zF D F).left y J = val v (𝟙 _) y J := fun y J hJ => by
    have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    rw [val₀ _ _ y J hJ, uVal, z₂, z₁, C.N_one, C.face₂, inv_one, _root_.one_mul, _root_.one_mul]; rfl
  refine ⟨⟨u₀, hu₀, corr_of_val D.P.isLB fun y J hJ => ?_⟩, fun u hu hc T ρ z J hJ => ?_⟩
  · rw [val_pull hJ, Category.id_comp]; exact at₀ y J hJ
  · refine (gen_unique D.P.isLB (fst (TF (R := R) F) D.P.A).left (DegPre.zF D F).left (congrArg (fun q => q.left) z₁)
      (surj_appTop D F hG) hu hu₀ (fun y J hJ => ?_) _ ρ.left z J hJ).trans (val₀ T ρ z J hJ)
    have := val_corr hJ hc (𝟙 _)
    rw [val_pull hJ, Category.id_comp] at this
    exact this.trans (at₀ y J hJ).symm

theorem powGen_isGen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℕ) : (GeneratorPullback.powGen L φ ε t n).IsGen := fun i j => by
  refine ((map_pow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans (mul_pow _ _ _))).trans
    (congrArg₂ (· * ·) ?_ (map_pow _ _ _).symm)
  exact (Finset.prod_pow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ =>
    (zpow_natCast _ n).symm.trans ((zpow_mul _ _ _).symm.trans (congrArg _ (mul_comm _ _))))

theorem tau_isGen (a b : D.X) : (D.tau a b).IsGen := by
  unfold DegPre.tau DegPre.rigK
  exact mulGen_isGen _ _ _ _ _ _ _
    (mulGen_isGen _ _ _ _ _ _ _
      (mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _) (invGen_isGen _ _ _ _ (D.psi_gen _)))
      (invGen_isGen _ _ _ _ (D.psi_gen _)))
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _))

section Values

variable {D F} {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
  {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ

theorem tau_symm (a b : D.X) : val (D.tau a b) (σ.left ≫ jFK (R := R) F) z J = val (D.tau b a) (σ.left ≫ jFK (R := R) F) z J := by
  have e : ∀ a b : D.X, val (D.tau a b) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi (a + b)) (σ.left ≫ jFK (R := R) F) z J * (val (D.psi a) (σ.left ≫ jFK (R := R) F) z J)⁻¹ *
        (val (D.psi b) (σ.left ≫ jFK (R := R) F) z J)⁻¹ * (val D.rigK (σ.left ≫ jFK (R := R) F) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  rw [e, e, add_comm b a, mul_right_comm (val (D.psi (a + b)) _ z J)]

theorem tau_mul (hB : D.TauBimult) (a a' b : D.X) :
    val (D.tau (a + a') b) (σ.left ≫ jFK (R := R) F) z J * th D z J (cP D T a) (cP D T a') (cP D T b) =
      val (D.tau a b) (σ.left ≫ jFK (R := R) F) z J * val (D.tau a' b) (σ.left ≫ jFK (R := R) F) z J := by
  let κ : T ⟶ TK R := Over.homMk (σ.left ≫ jFK (R := R) F) ((Category.assoc _ _ _).trans (Over.w σ))
  have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) κ.left).trans (val_mul hJ _ _ _))
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
  refine Eq.trans ?_ (val_cub D.cub κ hJ (cP D _ a) (cP D _ a') (cP D _ b)).symm
  rw [comp_cP, comp_cP, comp_cP]

theorem gt_mul (g : GtPtF D F) (a a' : D.X) :
    val (g.s (a + a')) σ.left z J * th D z J (cP D T a) (cP D T a') (σ ≫ g.b) =
      val (g.s a) σ.left z J * val (g.s a') σ.left z J := by
  have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.mult a a') σ.left).trans (val_mul hJ _ _ _))
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
  refine Eq.trans ?_ (val_cub D.cub σ hJ (cP D _ a) (cP D _ a') g.b).symm
  rw [comp_cP, comp_cP]

theorem gt_nsmul (g : GtPtF D F) (a mu : D.X) (k : ℕ) :
    val (g.s (a + k • mu)) σ.left z J * cubN (th D z J) k (cP D T a) (cP D T mu) (σ ≫ g.b) =
      val (g.s a) σ.left z J * val (g.s mu) σ.left z J ^ k := by
  induction k with
  | zero => rw [zero_nsmul, add_zero, pow_zero]; rfl
  | succ k ih =>
    have e := gt_mul σ hJ g (a + k • mu) mu
    rw [cPoint_add, cPoint_nsmul] at e
    rw [succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, e, pow_succ,
      ← _root_.mul_assoc, ← ih, cubN, mul_right_comm]

theorem chain_val {k : ℕ} (p : QkPt D F k) (mu : D.X) :
    val (D.tau p.y mu) (σ.left ≫ jFK (R := R) F) z J * cubN (th D z J) k 1 (σ ≫ p.g.b) (cP D T mu) =
      val (p.g.s mu) σ.left z J ^ k := by
  obtain ⟨h, ⟨gs, h₀, hs, hl⟩, hι⟩ := p.eq
  have C : IsCub (cubV D.cub z J) := isCub_cubV D.cub hJ
  have key : ∀ i (hi : i < k + 1), (gs ⟨i, hi⟩).b = p.g.b ^ i ∧
      val ((gs ⟨i, hi⟩).s mu) σ.left z J * cubN (th D z J) i 1 (σ ≫ p.g.b) (cP D T mu) = val (p.g.s mu) σ.left z J ^ i := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨h₀.1, (_root_.mul_one _).trans ((val_corr hJ (h₀.2 mu) σ.left).trans
        ((val_one _).trans (pow_zero _).symm))⟩
    | succ i ih =>
      intro hi
      obtain ⟨b₁, v₁⟩ := ih (by omega)
      obtain ⟨b₂, v₂⟩ := hs ⟨i, by omega⟩
      refine ⟨b₂.trans ((congrArg (· * p.g.b) b₁).trans (pow_succ _ _).symm), ?_⟩
      have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub σ hJ _ _ _))).symm.trans
        ((val_corr hJ (v₂ mu) σ.left).trans (val_mul hJ _ _ _))
      have e₁ : σ ≫ (gs (Fin.castSucc ⟨i, by omega⟩)).b = 1 * (σ ≫ p.g.b) ^ i := by
        rw [_root_.one_mul]; exact (congrArg (σ ≫ ·) b₁).trans (map_pow (preHom σ) _ _)
      have e₂ : σ ≫ DegPre.cF D F mu = cP D T mu := comp_cP D σ mu
      rw [e₁, e₂, C.s01, C.s12] at e
      rw [cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, pow_succ, ← v₁, cubN]
      exact (congrArg₂ (· * ·) e rfl).trans (mul_right_comm _ _ _)
  have hk := (key k (Nat.lt_succ_self k)).2
  have hl' : gs ⟨k, Nat.lt_succ_self k⟩ = h := hl
  rw [hl'] at hk
  rw [← hk]
  exact congrArg₂ (· * ·) ((val_corr hJ (hι.2 mu) σ.left).trans (val_pull hJ _ _ _)).symm rfl

end Values

variable {D F}

theorem cPoint_y {k : ℕ} (p : QkPt D F k) : cP D _ p.y = p.g.b ^ k := by
  obtain ⟨h, ⟨gs, h0, hadd, hlast⟩, hio⟩ := p.eq
  have key : ∀ i : Fin (k + 1), (gs i).b = p.g.b ^ (i : ℕ) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [h0.1, Fin.val_zero, pow_zero]
      rfl
    | succ i ih =>
      rw [(hadd i).1, Fin.val_succ, pow_succ, ← Fin.coe_castSucc, ← ih]
      rfl
  show DegPre.cF D F p.y = _
  rw [← hio.1, ← hlast, key (Fin.last k), Fin.val_last]

theorem gen_phi (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen) (α : D.X) :
    (∃ u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k)), u.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w)) ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k)), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) →
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
        val u ρ.left z J = uVal D F k α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J :=
  gen_u D F hG k α (α + p.y) p.g.b (by rw [cPoint_add, cPoint_y]) _ (mulGen_isGen _ _ _ _ _ _ _ (p.g.isGen α) hw) (fun U _ h => by
    refine (Fintype.prod_sum_type _).trans ?_
    rw [Fin.prod_univ_four, Fin.prod_univ_two]
    show h (cP D _ α * p.g.b).left ^ (-1 : ℤ) * h (cP D _ α).left ^ (1 : ℤ) * h p.g.b.left ^ (1 : ℤ) *
      h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) *
      (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h p.g.b.left ^ (-(k : ℤ))) = _
    simp only [zpow_neg, zpow_one, zpow_natCast]
    ac_rfl)

theorem gen_fe (hG : GlobalFnsSt) (k : ℕ) (mu α : D.X) :
    (∃ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k)), u.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F k mu α)) ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k)), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F k mu α) →
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
        val u ρ.left z J = uVal D F k α (cP D _ mu) ρ z J * val (DegPre.famMult D F k mu α) (ρ ≫ fst _ _).left z J := by
  have H := gen_u D F hG k α (α + k • mu) (cP D _ mu) (by rw [cPoint_add, cPoint_nsmul]) (DegPre.famMult D F k mu α)
    (pullGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (powGen_isGen _ _ _ _ (D.psi_gen mu) k) (tau_isGen D mu α))
      (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) k)) _) (fun U _ h => by
    have a₁ : ∀ χ, jFK (R := R) F ≫ D.xK χ = (cP D (TF (R := R) F) χ).left := fun χ => (Category.assoc _ _ _).symm
    have a₂ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
      (Category.assoc _ _ _).symm
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
    rw [add_comm mu α, cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module)
  rw [← trF_eq] at H
  exact H

theorem val_famMult {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (k : ℕ) (mu α : D.X) :
    val (DegPre.famMult D F k mu α) σ.left z J = val (D.tau mu α) (σ.left ≫ jFK (R := R) F) z J *
      (val (GeneratorPullback.powGen D.P.L _ _ (D.psi mu) k) (σ.left ≫ jFK (R := R) F) z J *
        val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) (σ.left ≫ jFK (R := R) F) z J) :=
  (val_pull hJ _ _ _).trans ((val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl).trans (by ac_rfl)))

def PhiVal {k : ℕ} (p : QkPt D F k) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (s t : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))) : Prop :=
  ∀ (α β : D.X), α + p.y = β → ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J),
    Good D.P.L z J → sval (t β) ρ.left z J = sval (s α) (ρ ≫ DegPre.trPt D F p.g.b).left z J *
      (uVal D F k α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J).val

variable (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k)
  (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
include hG hw

theorem phiRel_iff (s t : Fam D F k) : PhiRel D F k p w s t ↔ PhiVal p w s.s t.s := by
  constructor
  · rintro H α _ rfl T ρ z J hJ
    obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_phi hG p w hw α
    rw [← hv u hu hc T ρ z J hJ]
    exact (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (H α u hu hc) _ ρ.left z J hJ
  · intro H α u hu hc
    refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
    have := H α _ rfl _ (𝟙 _) y J hJ
    rw [← (gen_phi hG p w hw α).2 u hu hc _ (𝟙 _) y J hJ] at this
    exact this

omit hG hw in
theorem uVal_id (α : D.X) (m : TF (R := R) F ⟶ D.P.A) (y : (DegPre.BF D F).left) (J) :
    uVal D F k α m (𝟙 _) y J = cubN (th D y J) k (cP D _ α) (fst _ _ ≫ m) (DegPre.prB D F) *
      (th D y J (cP D _ α) (DegPre.prB D F) (fst _ _ ≫ m))⁻¹ := by
  simp only [uVal, Category.id_comp]

omit hG hw in
theorem uVal_tr (α : D.X) (m m' : TF (R := R) F ⟶ D.P.A) (y : (DegPre.BF D F).left) (J) :
    uVal D F k α m (DegPre.trPt D F m') y J =
      cubN (th D y J) k (cP D _ α) (fst _ _ ≫ m) (DegPre.prB D F * (fst _ _ ≫ m')) *
        (th D y J (cP D _ α) (DegPre.prB D F * (fst _ _ ≫ m')) (fst _ _ ≫ m))⁻¹ := by
  simp only [uVal]
  rw [← Category.assoc, tr_fst, tr_pr]

omit hG hw in
theorem tr_comm (m m' : TF (R := R) F ⟶ D.P.A) :
    DegPre.trPt D F m ≫ DegPre.trPt D F m' = DegPre.trPt D F m' ≫ DegPre.trPt D F m := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tr_fst]
  · show _ ≫ DegPre.prB D F = _ ≫ DegPre.prB D F
    simp only [Category.assoc, tr_pr, MonObj.comp_mul]
    simp only [← Category.assoc, tr_fst, tr_pr]
    exact mul_right_comm _ _ _

omit hG hw in
theorem units_comm (hB : D.TauBimult) (mu α : D.X) (y : (DegPre.BF D F).left) {J} (hJ : Good D.P.L y J) :
    uVal D F k α (cP D _ mu) (DegPre.trPt D F p.g.b) y J *
        val (DegPre.famMult D F k mu α) (fst (TF (R := R) F) D.P.A).left y J *
      (uVal D F k (α + k • mu) p.g.b (𝟙 _) y J *
        val (LB.mulGen D.P.L _ _ _ _ (p.g.s (α + k • mu)) w) (fst (TF (R := R) F) D.P.A).left y J) =
    uVal D F k α p.g.b (DegPre.trPt D F (cP D _ mu)) y J *
        val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (fst (TF (R := R) F) D.P.A).left y J *
      (uVal D F k (α + p.y) (cP D _ mu) (𝟙 _) y J *
        val (DegPre.famMult D F k mu (α + p.y)) (fst (TF (R := R) F) D.P.A).left y J) := by
  have C : IsCub (th D (T := DegPre.BF D F) y J) := isCub_cubV D.cub hJ
  have hm : fst (TF (R := R) F) D.P.A ≫ cP D _ mu = cP D _ mu := comp_cP D _ mu
  have hy : cP D (DegPre.BF D F) p.y = (fst (TF (R := R) F) D.P.A ≫ p.g.b) ^ k := by
    rw [← comp_cP D (fst (TF (R := R) F) D.P.A), cPoint_y]; exact map_pow (preHom (fst (TF (R := R) F) D.P.A)) _ _
  have t₁ := gt_nsmul (fst (TF (R := R) F) D.P.A) hJ p.g α mu k
  have t₂ := tau_mul (fst (TF (R := R) F) D.P.A) hJ hB α p.y mu
  have t₃ := chain_val (fst (TF (R := R) F) D.P.A) hJ p mu
  rw [hy, tau_symm _ hJ (α + p.y), tau_symm _ hJ α] at t₂
  have key := C.comm k _ _ _ (DegPre.prB D F) _ _ _ _ _ _ t₁ t₂ t₃
  rw [uVal_tr, uVal_tr, uVal_id, uVal_id, val_famMult _ hJ, val_famMult _ hJ, val_mul hJ, val_mul hJ, hm, cPoint_add, cPoint_add,
    cPoint_nsmul, hy]
  apply Additive.ofMul.injective
  have key' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at key' ⊢
  linear_combination (norm := abel) key'

omit hw in
theorem phi_fe (hB : D.TauBimult) (s : Fam D F k)
    (t : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))) (ht : PhiVal p w s.s t) :
    DegPre.FamFE D F k t := by
  intro mu β u hu hc
  obtain ⟨α, rfl⟩ : ∃ α, α + p.y = β := ⟨β - p.y, sub_add_cancel _ _⟩
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  have e₁ := ht (α + k • mu) (α + p.y + k • mu) (add_right_comm _ _ _) _ (𝟙 _) y J hJ
  have e₂ := ht α (α + p.y) rfl _ (DegPre.trPt D F (cP D _ mu)) y J hJ
  have e₃ := (gen_fe hG k mu (α + p.y)).2 u hu hc _ (𝟙 _) y J hJ
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := F) hG k mu α
  have e₄ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').1 (s.fe mu α u' hu' hc') _ (DegPre.trPt D F p.g.b).left y J hJ
  rw [hv' u' hu' hc' _ (DegPre.trPt D F p.g.b) y J hJ, trF_eq, tr_fst, ← Over.comp_left] at e₄
  rw [Category.id_comp, Category.id_comp, Over.id_left, e₄] at e₁
  rw [tr_fst, ← tr_comm] at e₂
  rw [Category.id_comp, Over.id_left] at e₃
  rw [Category.id_comp, trF_eq, e₁, e₂, e₃, _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul,
    units_comm p w hB mu α y hJ]

theorem exists_phi (hB : D.TauBimult) (s : Fam D F k) : ∃ t : Fam D F k, PhiVal p w s.s t.s := by
  have ex : ∀ β, ∃ t : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k)), ∀ α, α + p.y = β →
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
        sval t ρ.left z J = sval (s.s α) (ρ ≫ DegPre.trPt D F p.g.b).left z J *
          (uVal D F k α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J).val := by
    intro β
    obtain ⟨α₀, rfl⟩ : ∃ α₀, α₀ + p.y = β := ⟨β - p.y, sub_add_cancel _ _⟩
    obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_phi hG p w hw α₀
    obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := DegPre.famφ D F (α₀ + p.y)) (ε' := DegPre.famε k) (fun U _ h => by
        refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
          (c := ∏ i, h ((DegPre.trPt D F p.g.b).left ≫ DegPre.famφ D F α₀ i) ^ DegPre.famε k i) rfl
          (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
            (c := ∏ i, h (DegPre.famφ D F (α₀ + p.y) i) ^ DegPre.famε k i) rfl (prod_neg _ _ rfl))) ?_
        exact (mul_comm _ _).trans (inv_mul_cancel_right _ _)) (pullMulSec (s.s α₀) (DegPre.trPt D F p.g.b).left u hu)
    refine ⟨t, fun α hα T ρ z J hJ => ?_⟩
    obtain rfl : α = α₀ := add_right_cancel hα
    exact (ht _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans
      (congrArg₂ (· * ·) rfl (congrArg Units.val (hv u hu hc T ρ z J hJ))))
  choose t ht using ex
  exact ⟨⟨t, phi_fe hG p w hB s t fun α β h => ht β α h⟩, fun α β h => ht β α h⟩

omit hG hw in
theorem phi_unique {s : Fam D F k} {t t' : Fam D F k} (h : PhiVal p w s.s t.s) (h' : PhiVal p w s.s t'.s) : t = t' :=
  fam_ext fun β j => sec_ext_val D.P.isLB (fun y J hJ =>
    (h (β - p.y) β (sub_add_cancel _ _) _ (𝟙 _) y J hJ).trans
      (h' (β - p.y) β (sub_add_cancel _ _) _ (𝟙 _) y J hJ).symm) j

omit hG hw in
theorem sval_add (s t : Fam D F k) (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J}
    (hJ : Good D.P.L z J) : sval ((s + t).s α) r z J = sval (s.s α) r z J + sval (t.s α) r z J :=
  gs_add r z _ (hJ.mem _ r) _ _

omit hG hw in
theorem sval_smul (ζ : F) (s : Fam D F k) (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J}
    (hJ : Good D.P.L z J) : sval ((ζ • s).s α) r z J =
      gs (r ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) * sval (s.s α) r z J :=
  (gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) ((gs_res r z le_top (hJ.mem _ r) _).trans
    (gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _)) rfl)

omit hG hw in
theorem phiFun_of_globalFns (hG : GlobalFnsSt) : PhiFunStatement := by
  intro R _ _ I D F _ _ k _ p w hw
  choose Φ hΦ using exists_phi hG p w hw D.tau_bimult
  refine ⟨⟨⟨Φ, fun s s' => phi_unique p w (hΦ _) fun α β h T ρ z J hJ => ?_⟩,
    fun ζ s => phi_unique p w (hΦ _) fun α β h T ρ z J hJ => ?_⟩, fun s t => ?_⟩
  · rw [sval_add _ _ _ _ z hJ, sval_add _ _ _ _ z hJ, hΦ s α β h T ρ z J hJ, hΦ s' α β h T ρ z J hJ, add_mul]
  · have e : (ρ ≫ DegPre.trPt D.toPre F p.g.b).left ≫ (fst (TF (R := R) F) D.toPre.P.A).left =
        ρ.left ≫ (fst (TF (R := R) F) D.toPre.P.A).left := by
      rw [← Over.comp_left, Category.assoc, tr_fst, Over.comp_left]
    refine (sval_smul ζ (Φ s) β ρ.left z hJ).trans ?_
    rw [sval_smul _ _ _ _ z hJ, hΦ s α β h T ρ z J hJ, e, _root_.mul_assoc]
  · rw [phiRel_iff hG p w hw]
    exact ⟨fun h => phi_unique p w h (hΦ s), fun h => h ▸ hΦ s⟩

omit hG hw in
theorem phiFun_of (hL : ReciprocityTheory.ChartRestriction.G.Out.Laws) : PhiFunStatement := phiFun_of_globalFns hL.globalFns

end ReciprocityTheory.ChartRestriction.G.DVR
