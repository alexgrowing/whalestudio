import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordAdd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitLevels
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGrpActIterateEqOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLevelPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfWeightSum
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CombBijective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FourierJacobiExpansionOverFieldInjective
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.Transl

section Complete
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {U : PreU I D A G} {S : Type} [CommRing S] {φ : R →+* S} [IsLocalRing S]
open ReciprocityTheory.ChartRestriction.G.DVR FormalPoint

omit [IsDomain R] [IsLocalRing S] in

def levelPt (I : Ideal R) (φ : R →+* S) (e : ℕ) :
    (Over.map (thick R I e)).obj (Over.mk (levelMap I φ e)) ⟶ Over.mk (spMap φ) :=
  Over.homMk (adicLevelι (I.map φ) (e + 1)) (levelMap_thick I φ e).symm

theorem base_pow [IsHausdorff (I.map φ) S] {x : Over.mk (spMap φ) ⟶ G} {g : GtPt D (Over.mk (spMap φ))}
    (hr : U.Red x g) {N : ℕ} (hx : x ^ N = 1) : g.b ^ N = 1 := by
  refine Over.OverMorphism.ext (hom_ext_of_isHausdorff (I.map φ) fun e => ?_)
  obtain ⟨a, -, a₂, a₃⟩ := exists_level_point hr hx (levelPt I φ e)
  have : levelPt I φ e ≫ g.b ^ N = levelPt I φ e ≫ 1 := by
    rw [MonObj.comp_pow, ← a₂, ← map_pow, a₃, map_one, MonObj.comp_one]
  exact congrArg (fun q => q.left) this

omit [IsLocalRing S] in
theorem reduction_one (e : ℕ) : reduction I (1 : Over.mk (spMap φ) ⟶ G) e ≫ (U.gt e).pG.left =
    adicLevelι (I.map φ) (e + 1) ≫ (1 : Over.mk (spMap φ) ⟶ D.P.A).left := by
  have a : reduction I (1 : Over.mk (spMap φ) ⟶ G) e = (1 : Over.mk (levelMap I φ e) ⟶ thickObj R I e G).left := by
    rw [← cancel_mono (fstG I e G).left, reduction_fstG]
    exact congrArg (fun q => q.left) ((MonObj.comp_one (levelPt I φ e)).trans (map_one (upHom I e G _)).symm)
  rw [a]
  exact congrArg (fun q => q.left) ((map_one (imHom U e _)).trans (MonObj.comp_one (levelPt I φ e)).symm)

omit [IsLocalRing S] in
theorem wv_succ (e : ℕ) {Z : Scheme.{0}} {z : Z} {JG J} (hJG : Good U.P.L.L z JG) (hJ : Good D.P.L z J)
    (a : Z ⟶ (thickObj R I e G).left) : wv U (e + 1) z JG J (a ≫ thickMap R I e G) = wv U e z JG J a := by
  have h₄ : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [wv, Category.assoc, Category.assoc, U.gt_q, h₄]
  exact U.w_compat e Z a z _ _ (hJ (a ≫ (U.gt e).pG.left)) (hJG (a ≫ (fstG I e G).left))

theorem exists_frames [IsAdicComplete (I.map φ) S] {K : Type} [Fintype K] (p : K → (Over.mk (spMap φ) ⟶ G))
    (φG : K → (Spec (CommRingCat.of S) ⟶ G.left)) (φB : K → (Spec (CommRingCat.of S) ⟶ D.P.A.left)) (ε : K → ℤ)
    (hG : ∀ k, (p k).left = φG k)
    (hB : ∀ e k, reduction I (p k) e ≫ (U.gt e).pG.left = adicLevelι (I.map φ) (e + 1) ≫ φB k) :
    ∃ (f : LB.Gen (LB.LinComb U.P.L.L φG ε)) (w : LB.Gen (LB.LinComb D.P.L φB ε)), f.IsGen ∧ w.IsGen ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (l : Z ⟶ Spec (CommRingCat.of (S ⧸ I.map φ ^ (e + 1)))) (z : Z) (JG) (J),
        Good U.P.L.L z JG → Good D.P.L z J → val w (l ≫ adicLevelι (I.map φ) (e + 1)) z J =
          (∏ k, wv U e z JG J (l ≫ reduction I (p k) e) ^ ε k) * val f (l ≫ adicLevelι (I.map φ) (e + 1)) z JG := by
  obtain ⟨w, hw⟩ := exists_gen_of_local D.P.L D.P.isLB φB ε
  have H : ∀ e : ℕ, ∃ a : LB.Gen (LB.LinComb U.P.L.L (fun k => adicLevelι (I.map φ) (e + 1) ≫ φG k) ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (l : Z ⟶ Spec (CommRingCat.of (S ⧸ I.map φ ^ (e + 1)))) (z : Z) (J) (JG),
        Good D.P.L z J → Good U.P.L.L z JG → val w (l ≫ adicLevelι (I.map φ) (e + 1)) z J =
          (∏ k, wv U e z JG J (l ≫ reduction I (p k) e) ^ ε k) * val a l z JG := fun e =>
    exists_gen_of_iso D.P.isLB U.P.L.isLB (U.w e) (U.w_gen e)
      (fun k => reduction I (p k) e) (adicLevelι (I.map φ) (e + 1))
      (fun k => (reduction_fstG I (p k) e).trans (congrArg (_ ≫ ·) (hG k))) (hB e) w hw
  choose u hu vu using H
  obtain ⟨f, hf, vf⟩ := RedTotal.exists_gen_levels (I.map φ) U.P.L.isLB φG ε u hu (fun _ => 𝟙 _)
    (fun e _ _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ ε k) (Category.id_comp _).symm)
    (fun e z C hC => by
      obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
      have a := vu (e + 1) _ (adicLevelMap (I.map φ) (Nat.le_succ (e + 1))) z J C hJ hC
      have b := vu e _ (𝟙 _) z J C hJ hC
      rw [adicLevelMap_ι] at a
      rw [Category.id_comp, a] at b
      simp only [RedTotal.reduction_succ, wv_succ e hC hJ, Category.id_comp] at b
      rw [Category.comp_id]
      exact mul_left_cancel b)
  refine ⟨f, w, hf, hw, fun e Z l z JG J hJG hJ => ?_⟩
  rw [vu e Z l z J JG hJ hJG, ← vf e Z l z JG hJG, Category.comp_id]

theorem exists_frameRel [IsAdicComplete (I.map φ) S] {x : Over.mk (spMap φ) ⟶ G} {g : GtPt D (Over.mk (spMap φ))}
    (hr : U.Red x g) (N : ℕ) : ∃ f w, f.IsGen ∧ w.IsGen ∧ FrameRel U x g.b N f w := by
  obtain ⟨f, w, hf, hw, v⟩ := exists_frames (U := U) (φ := φ) ![1, x]
    ![(1 : Over.mk (spMap φ) ⟶ G).left, x.left] ![(1 : Over.mk (spMap φ) ⟶ D.P.A).left, g.b.left]
    ![(N : ℤ), -(N : ℤ)] (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
    (fun e => Fin.forall_fin_two.2 ⟨reduction_one e, (hr e _ _ _ (reduction_fstG I x e)).1⟩)
  refine ⟨f, w, hf, hw, fun e Z r o a ho ha z JG J hJG hJ => ?_⟩
  have c : r ≫ (Over.mk (spMap φ)).hom = (a ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w x, ← Category.assoc, ← ha, Category.assoc, Over.w (fstG I e G), Category.assoc]; rfl
  obtain ⟨l, hl⟩ := exists_factor_level I φ r _ c
  have e₁ : ∀ (q : Over.mk (spMap φ) ⟶ G) (b : Z ⟶ (thickObj R I e G).left), b ≫ (fstG I e G).left = r ≫ q.left →
      b = l ≫ reduction I q e := fun q b hb => by
    rw [← cancel_mono (fstG I e G).left, Category.assoc, reduction_fstG, hb, ← hl]
    exact Category.assoc _ _ _
  have k := v e Z l z JG J hJG hJ
  rw [Fin.prod_univ_two, hl] at k
  have k' : val w r z J = wv U e z JG J (l ≫ reduction I 1 e) ^ (N : ℤ) *
      wv U e z JG J (l ≫ reduction I x e) ^ (-(N : ℤ)) * val f r z JG := k
  rw [k', ← e₁ _ _ ho, ← e₁ _ _ ha, zpow_neg, zpow_natCast, zpow_natCast, mul_right_comm, inv_mul_cancel_right]

end Complete

section Generic
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))} {F : Type} [Field F] [Algebra (FractionRing R) F]
open ReciprocityTheory.ChartRestriction.G.DVR

def genHom (Z : Over (Spec (CommRingCat.of (FractionRing R)))) : (Z ⟶ A.A) →* (Over.mk (Z.hom ≫ jK R) ⟶ G) :=
  MonoidHom.mk' (fun a => toBase (A := G) (A' := (Over.pullback (jK R)).obj G) (g := pullback.fst G.hom (jK R))
    pullback.condition (a ≫ U.gen.inv)) fun a b => by
      have := U.gen_hom
      rw [MonObj.mul_comp, toBase_mul_pullback]

theorem genHom_injective (Z : Over (Spec (CommRingCat.of (FractionRing R)))) : Function.Injective (genHom U Z) :=
  fun a b h => by
    rw [← cancel_mono U.gen.inv]
    exact Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) h)
      ((Over.w (a ≫ U.gen.inv)).trans (Over.w (b ≫ U.gen.inv)).symm))

variable {U} in
theorem pow_eq_one_of_samePt {xA : TFK (R := R) F ⟶ A.A} {y : TF (R := R) F ⟶ G} (h : U.SamePt xA y) {N : ℕ}
    (hy : y ^ N = 1) : xA ^ N = 1 := by
  have e : genHom U _ xA = y := Over.OverMorphism.ext ((Category.assoc _ _ _).trans h)
  apply genHom_injective U
  rw [map_pow, map_one, e]; exact hy

def genτ (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (φ : TF (R := R) F ⟶ T) :
    Over.mk ((TFK (R := R) F ⊗ A.A).hom ≫ jK R) ⟶ T :=
  Over.homMk ((fst (TFK (R := R) F) A.A).left ≫ φ.left) (by
    have e₁ : φ.left ≫ T.hom = jFK (R := R) F ≫ jK R := Over.w φ
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ jK R) (Over.w (fst (TFK (R := R) F) A.A))))))

def wa {Z : Over (Spec (CommRingCat.of (FractionRing R)))} (z : Z.left) (JA : (Z.left ⟶ A.A.left) → A.L.ι)
    (JG : (Z.left ⟶ G.left) → U.P.L.L.ι) (a : Z ⟶ A.A) : (Z.left.presheaf.stalk z)ˣ :=
  gw U.wA (a ≫ U.gen.inv).left z (JG ((a ≫ U.gen.inv).left ≫ pullback.fst G.hom (jK R)))
    (fun _ => JA ((a ≫ U.gen.inv).left ≫ U.gen.hom.left))

theorem left_inv_hom {Z : Over (Spec (CommRingCat.of (FractionRing R)))} (a : Z ⟶ A.A) :
    (a ≫ U.gen.inv).left ≫ U.gen.hom.left = a.left := by
  rw [← Over.comp_left, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {U}

theorem genHom_transl {φ : TF (R := R) F ⟶ T} {x : T ⟶ G} {xA : TFK (R := R) F ⟶ A.A} (h : U.SamePt xA (φ ≫ x)) :
    genHom U _ (translPt A.A xA) = (genτ A φ ≫ x) * genHom U _ (snd (TFK (R := R) F) A.A) := by
  refine (map_mul (genHom U _) (fst _ _ ≫ xA) (snd _ _)).trans (congrArg (· * _) (Over.OverMorphism.ext ?_))
  have h' : xA.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = φ.left ≫ x.left := h
  show (((fst (TFK (R := R) F) A.A).left ≫ xA.left) ≫ U.gen.inv.left) ≫ pullback.fst G.hom (jK R) =
    ((fst (TFK (R := R) F) A.A).left ≫ φ.left) ≫ x.left
  rw [Category.assoc, Category.assoc, h', Category.assoc]

theorem theta_ratio (hG : GlobalFnsSt) {φ : TF (R := R) F ⟶ T} {x : T ⟶ G} {N : ℤ}
    (θ : ThetaGrp A.A A.L N (TFK (R := R) F)) (h : U.SamePt θ.pt (φ ≫ x))
    (t : LB.Gen (LB.LinComb U.P.L.L (K := Fin 2) ![(snd T G).left, ((fst T G ≫ x) * snd T G).left] ![N, -N]))
    (ht : t.IsGen) : ∃ c : Γ(Spec (CommRingCat.of F), ⊤)ˣ, ∀ (z : (TFK (R := R) F ⊗ A.A).left) (JA) (JG),
      Good A.L z JA → Good U.P.L.L z JG →
      wa U z JA JG (snd _ _) ^ N * val (L := A.L) θ.φ (𝟙 _) z JA =
        gm (fst (TFK (R := R) F) A.A).left z ⊤ c *
          val (Z := (TFK (R := R) F ⊗ A.A).left) t (lift (genτ A φ) (genHom U _ (snd (TFK (R := R) F) A.A))).left z JG *
          wa U z JA JG (translPt A.A θ.pt) ^ N := by
  obtain ⟨a, ha, va⟩ := exists_gen_of_iso U.P.L.isLB A.isLB U.wA U.wA_gen
    ![(snd (TFK (R := R) F) A.A ≫ U.gen.inv).left, (translPt A.A θ.pt ≫ U.gen.inv).left]
    (lift (genτ A φ) (genHom U _ (snd (TFK (R := R) F) A.A))).left
    (φ' := ![(snd (TFK (R := R) F) A.A).left, (translPt A.A θ.pt).left])
    (fun k => by
      fin_cases k
      exacts [left_inv_hom U _, left_inv_hom U _])
    (fun k => by
      fin_cases k
      · exact congrArg (fun q => q.left) (lift_snd (genτ A φ) (genHom U _ (snd (TFK (R := R) F) A.A))).symm
      · refine congrArg (fun q => q.left) ((genHom_transl h).trans ?_ : _ =
          lift (genτ A φ) (genHom U _ (snd (TFK (R := R) F) A.A)) ≫ ((fst T G ≫ x) * snd T G))
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]) t ht
  obtain ⟨ρ, hρ⟩ := TorusCoord.exists_ratio A.isLB (fun _ _ _ => rfl) θ.φ θ.isGen a ha
  obtain ⟨c, hc⟩ := exists_unit_base (fst (TFK (R := R) F) A.A).left (lift (𝟙 _) (1 : TFK (R := R) F ⟶ A.A)).left
    (congrArg (fun q => q.left) (lift_fst (𝟙 _) (1 : TFK (R := R) F ⟶ A.A))) (surj_fst hG A.isAb _) ρ
  refine ⟨c, fun z JA JG hA hJG => ?_⟩
  have k := va _ (𝟙 _) z JG JA hJG hA
  have k₁ := hρ _ (𝟙 _) z JA hA
  rw [hc, Category.id_comp] at k₁
  simp only [Category.id_comp, Fin.prod_univ_two] at k
  have k' : val (Z := (TFK (R := R) F ⊗ A.A).left) t
      (lift (genτ A φ) (genHom U _ (snd (TFK (R := R) F) A.A))).left z JG =
      wa U z JA JG (snd _ _) ^ N * wa U z JA JG (translPt A.A θ.pt) ^ (-N) * val a (𝟙 _) z JA := k
  rw [k', k₁, zpow_neg]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Generic

theorem act_alg {A : Type} [CommRing A] {N n : ℕ} {w₀ w₁ θ c v : Aˣ} {T T' : A} {a σ t : Fin n → A}
    (h₁ : w₀ ^ (N : ℤ) * θ = c * v * w₁ ^ (N : ℤ)) (h₂ : T' = θ.val * T) (h₃ : w₁.val ^ N * T = ∑ i, a i * σ i)
    (h₄ : ∀ i, w₀.val ^ N * t i = σ i * v.val) : T' = ∑ i, c.val * a i * t i := by
  rw [zpow_natCast, zpow_natCast] at h₁
  have h := congrArg Units.val h₁
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h
  refine (Units.mul_right_inj (w₀ ^ N)).1 ?_
  rw [Units.val_pow_eq_pow_val, h₂, ← _root_.mul_assoc, h, _root_.mul_assoc, h₃, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm (w₀.val ^ N), h₄]
  ring

theorem gs_scal_unit {F : Type} [CommRing F] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of F)) (z : Y)
    (c : Γ(Spec (CommRingCat.of F), ⊤)ˣ) (a : F) :
    gs (𝟙 Y) z ⊤ (scal p ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c.val * a)) =
      (gm p z ⊤ c).val * gs (𝟙 Y) z ⊤ (scal p a) := by
  rw [ExpLin.gs_scal_mul, gs_scal, Category.id_comp, Iso.hom_inv_id_apply, gs_unit p z ⊤ trivial]

theorem gs_scal_of {F : Type} [CommRing F] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of F)) (r : Y ⟶ Y)
    (h : r ≫ p = p) (z : Y) (a : F) : gs r z ⊤ (scal p a) = gs (𝟙 Y) z ⊤ (scal p a) := by
  rw [gs_scal, gs_scal, h, Category.id_comp]

section Field
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {U : PreU I D A G} {T : Over (Spec (CommRingCat.of R))} {F : Type} [Field F] [Algebra (FractionRing R) F]
open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_expF_sum {k : ℕ}
    (hlin : ∀ t t' t'' s s' s'' (c : F), U.ExpF F k t s → U.ExpF F k t' s' →
      (∀ j, t''.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j + t'.f j) →
      (∀ α j, (s'' α).f j = DegPre.constBF D F c _ * (s α).f j + (s' α).f j) → U.ExpF F k t'' s'')
    (n : ℕ) (c : Fin n → F) (t : Fin n → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s : Fin n → Raw D F k)
    (h : ∀ i, U.ExpF F k (t i) (s i)) : ∃ t₀ s₀, U.ExpF F k t₀ s₀ ∧
      (∀ z J, Good A.L z J → sval (L := A.L) t₀ (𝟙 _) z J =
        ∑ i, gs (𝟙 _) z ⊤ (scal (fst (TFK (R := R) F) A.A).left (c i)) * sval (L := A.L) (t i) (𝟙 _) z J) ∧
      ∀ α z J, Good D.P.L z J → sval (s₀ α) (𝟙 _) z J =
        ∑ i, gs (𝟙 _) z ⊤ (scal (fst (TF (R := R) F) D.P.A).left (c i)) * sval (s i α) (𝟙 _) z J := by
  induction n with
  | zero =>
    refine ⟨zeroSec _, fun _ => zeroSec _, ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0,
      fun Z rA y rG _ _ z JA JG _ _ => ?_, fun α Z rF rB _ z J _ => ?_⟩, fun z J _ => ?_, fun α z J _ => ?_⟩
    · exact ((congrArg (_ * ·) (sval_zeroSec _ _ _)).trans (mul_zero _)).trans (Fin.sum_univ_zero _).symm
    · exact (sval_zeroSec _ _ _).trans (Fin.sum_univ_zero _).symm
    · exact (sval_zeroSec _ _ _).trans (Fin.sum_univ_zero _).symm
    · exact (sval_zeroSec _ _ _).trans (Fin.sum_univ_zero _).symm
  | succ n ih =>
    obtain ⟨t₁, s₁, e, vt, vs⟩ := ih (fun i => c i.succ) (fun i => t i.succ) (fun i => s i.succ) fun i => h i.succ
    refine ⟨comb (scal (fst (TFK (R := R) F) A.A).left (c 0)) (t 0) t₁,
      fun α => comb (scal (fst (TF (R := R) F) D.P.A).left (c 0)) (s 0 α) (s₁ α),
      hlin _ _ _ _ _ _ (c 0) (h 0) e (fun _ => rfl) (fun _ _ => rfl), fun z J hJ => ?_, fun α z J hJ => ?_⟩
    · rw [Fin.sum_univ_succ, ← vt z J hJ]
      exact ExpLin.sval_comb _ (fun _ => rfl) _ z hJ
    · rw [Fin.sum_univ_succ, ← vs α z J hJ]
      exact ExpLin.sval_comb _ (fun _ => rfl) _ z hJ

theorem sval_translT {φ : TF (R := R) F ⟶ T} {x : T ⟶ G} {N : ℕ} {xA : TFK (R := R) F ⟶ A.A}
    (h : U.SamePt xA (φ ≫ x)) {t : LB.Sec (LPow A.A A.L (N : ℤ) (TFK (R := R) F))}
    {n : ℕ} {c : Fin n → F} {σ : Fin n → U.SecGT (𝟙_ _) N}
    (hE : ∀ (Z : Scheme.{0}) (rA : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (y : Z ⟶ ((Over.pullback (jK R)).obj G).left)
      (rG : Z ⟶ (𝟙_ _ ⊗ G).left), rA ≫ (snd _ A.A).left = y ≫ U.gen.hom.left →
      rG ≫ (snd _ G).left = y ≫ pullback.fst G.hom (jK R) →
      ∀ (z : Z) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
        (gw U.wA y z (JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => JA (y ≫ U.gen.hom.left))).val ^ N *
            sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (N : ℤ)) t rA z JA =
          ∑ i, gs rA z ⊤ (scal (fst (TFK (R := R) F) A.A).left (c i)) * sval (σ i) rG z JG)
    (z : (TFK (R := R) F ⊗ A.A).left) (JA) (JG) (hA : Good A.L z JA) (hG : Good U.P.L.L z JG) :
    (wa U z JA JG (translPt A.A xA)).val ^ N * sval (L := A.L) t (translT A.A xA).left z JA =
      ∑ i, gs (𝟙 _) z ⊤ (scal (fst (TFK (R := R) F) A.A).left (c i)) * sval (Z := (TFK (R := R) F ⊗ A.A).left) (σ i)
        (lift (toUnit _) ((genτ A φ ≫ x) * genHom U _ (snd (TFK (R := R) F) A.A))).left z JG := by
  have e : (translT A.A xA).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) A.A).left := by
    rw [← Over.comp_left, translT, lift_fst]
  have e₁ : lift (toUnit _) ((genτ A φ ≫ x) * genHom U _ (snd (TFK (R := R) F) A.A)) ≫ snd _ G =
      genHom U _ (translPt A.A xA) := (lift_snd _ _).trans (genHom_transl h).symm
  exact (hE _ (translT A.A xA).left (translPt A.A xA ≫ U.gen.inv).left
    (lift (toUnit _) ((genτ A φ ≫ x) * genHom U _ (snd (TFK (R := R) F) A.A))).left
    (by rw [left_inv_hom, ← Over.comp_left, translT, lift_snd])
    (congrArg (fun q => q.left) e₁) z JA JG hA hG).trans
    (Finset.sum_congr rfl fun i _ => congrArg (· * _) (gs_scal_of _ _ e z (c i)))

theorem sval_pullG {φ : TF (R := R) F ⟶ T} {N : ℕ} {σ : U.SecGT T N}
    {u : LB.Sec (LPow A.A A.L (N : ℤ) (TFK (R := R) F))} (hu : U.PullG F φ N σ u)
    (z : (TFK (R := R) F ⊗ A.A).left) (JA) (JG) (hA : Good A.L z JA) (hG : Good U.P.L.L z JG) :
    (wa U z JA JG (snd _ _)).val ^ N * sval (L := A.L) u (𝟙 _) z JA = sval (Z := (TFK (R := R) F ⊗ A.A).left) σ
      (lift (genτ A φ) (genHom U _ (snd (TFK (R := R) F) A.A))).left z JG :=
  hu _ (𝟙 _) (snd (TFK (R := R) F) A.A ≫ U.gen.inv).left
    (lift (genτ A φ) (genHom U _ (snd (TFK (R := R) F) A.A))).left
    ((Category.id_comp _).trans (left_inv_hom U _).symm)
    (congrArg (fun q => q.left) (lift_snd (genτ A φ) (genHom U _ (snd (TFK (R := R) F) A.A))))
    ((congrArg (fun q => q.left) (lift_fst (genτ A φ) (genHom U _ (snd (TFK (R := R) F) A.A)))).trans
      (Category.id_comp _).symm) z JA JG hA hG

theorem sval_act {φ : TF (R := R) F ⟶ T} {x : T ⟶ G} {N : ℕ} (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F))
    (h : U.SamePt θ.pt (φ ≫ x))
    {v : LB.Gen (LB.LinComb U.P.L.L (K := Fin 2) ![(snd T G).left, ((fst T G ≫ x) * snd T G).left] ![(N : ℤ), -(N : ℤ)])}
    {c₀ : Γ(Spec (CommRingCat.of F), ⊤)ˣ}
    (hc : ∀ (z : (TFK (R := R) F ⊗ A.A).left) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
      wa U z JA JG (snd _ _) ^ (N : ℤ) * val (L := A.L) θ.φ (𝟙 _) z JA =
        gm (fst (TFK (R := R) F) A.A).left z ⊤ c₀ *
          val (Z := (TFK (R := R) F ⊗ A.A).left) v (lift (genτ A φ) (genHom U _ (snd (TFK (R := R) F) A.A))).left z JG *
          wa U z JA JG (translPt A.A θ.pt) ^ (N : ℤ))
    {t t' : LB.Sec (LPow A.A A.L (N : ℤ) (TFK (R := R) F))} (hact : IsActOf A.A A.L (N : ℤ) θ t t')
    {n : ℕ} {c : Fin n → F} {σ : Fin n → U.SecGT (𝟙_ _) N}
    (hE : ∀ (Z : Scheme.{0}) (rA : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (y : Z ⟶ ((Over.pullback (jK R)).obj G).left)
      (rG : Z ⟶ (𝟙_ _ ⊗ G).left), rA ≫ (snd _ A.A).left = y ≫ U.gen.hom.left →
      rG ≫ (snd _ G).left = y ≫ pullback.fst G.hom (jK R) →
      ∀ (z : Z) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
        (gw U.wA y z (JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => JA (y ≫ U.gen.hom.left))).val ^ N *
            sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (N : ℤ)) t rA z JA =
          ∑ i, gs rA z ⊤ (scal (fst (TFK (R := R) F) A.A).left (c i)) * sval (σ i) rG z JG)
    {σ' : Fin n → U.SecGT T N}
    (hσ : ∀ i (T' : Over (Spec (CommRingCat.of R))) (τ : T' ⟶ T) (y : T' ⟶ G) (z : T'.left) (J), Good U.P.L.L z J →
      sval (σ' i) (lift τ y).left z J =
        sval (σ i) (lift (toUnit T') ((τ ≫ x) * y)).left z J * (val v (lift τ y).left z J).val)
    {u : Fin n → LB.Sec (LPow A.A A.L (N : ℤ) (TFK (R := R) F))} (hu : ∀ i, U.PullG F φ N (σ' i) (u i))
    (z) (JA) (hA : Good A.L z JA) : sval (L := A.L) t' (𝟙 _) z JA =
      ∑ i, gs (𝟙 _) z ⊤ (scal (fst (TFK (R := R) F) A.A).left
        ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c₀.val * c i)) * sval (L := A.L) (u i) (𝟙 _) z JA := by
  obtain ⟨JG, hG⟩ := exists_good_pt U.P.L.isLB z
  have h₂ := ThetaPowOrder.act_sval hact (𝟙 _) z hA
  rw [Category.id_comp] at h₂
  have h₄ : ∀ i, sval (Z := (TFK (R := R) F ⊗ A.A).left) (σ' i)
      (lift (genτ A φ) (genHom U _ (snd (TFK (R := R) F) A.A))).left z JG =
      sval (Z := (TFK (R := R) F ⊗ A.A).left) (σ i)
        (lift (toUnit _) ((genτ A φ ≫ x) * genHom U _ (snd (TFK (R := R) F) A.A))).left z JG *
      (val (Z := (TFK (R := R) F ⊗ A.A).left) v
        (lift (genτ A φ) (genHom U _ (snd (TFK (R := R) F) A.A))).left z JG).val :=
    fun i => hσ i _ (genτ A φ) (genHom U _ (snd (TFK (R := R) F) A.A)) z JG hG
  exact (act_alg (hc z JA JG hA hG) h₂ (sval_translT h hE z JA JG hA hG)
    fun i => (sval_pullG (hu i) z JA JG hA hG).trans (h₄ i)).trans
    (Finset.sum_congr rfl fun i _ => congrArg (· * _) (gs_scal_unit _ z c₀ (c i)).symm)

end Field

section Phi
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
  {T : Over (Spec (CommRingCat.of R))} {F : Type} [Field F] [Algebra (FractionRing R) F]
open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_line {φ : TF (R := R) F ⟶ T} {b : T ⟶ D.P.A} {b' : TF (R := R) F ⟶ D.P.A} (hb : b' = φ ≫ b) {N : ℕ}
    (w : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(1 : T ⟶ D.P.A).left, b.left] ![(N : ℤ), -(N : ℤ)])) (hw : w.IsGen)
    (c₀ : Γ(Spec (CommRingCat.of F), ⊤)ˣ) :
    ∃ w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b') (DegPre.lineε N)), w'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
        val w' r z J = gm (X := Spec (CommRingCat.of F)) r z ⊤ c₀ * val w (r ≫ φ.left) z J := by
  obtain ⟨a, ha, va⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b') (ε' := DegPre.lineε N) (fun U _ h => by
      have q : φ.left ≫ (1 : T ⟶ D.P.A).left = (DegPre.zeroF D F).left :=
        congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) φ)
      rw [Fin.prod_univ_two, Fin.prod_univ_two, hb]
      exact congrArg (fun q => h q ^ (N : ℤ) * _) q)
    (LB.pullGen D.P.L _ _ w φ.left) (pullGen_isGen _ _ _ _ hw _)
  exact ⟨scaleGen c₀ a, scaleGen_isGen _ ha, fun Z r z J hJ => (val_scaleGen _ _ _ hJ).trans
    (congrArg (_ * ·) ((va Z r z J hJ).trans (val_pull hJ _ _ _)))⟩

theorem val_phi (hG : GlobalFnsSt) {φ : TF (R := R) F ⟶ T} {g' : GtPt D T} {g : GtPtF D F}
    (hp : GtPt.IsPullF F φ.left g' g) {N : ℕ} (hb : g'.b ^ N = 1) {w} {c₀ : Γ(Spec (CommRingCat.of F), ⊤)ˣ}
    {w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε N))} (hw' : w'.IsGen)
    (vw : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      val w' r z J = gm (X := Spec (CommRingCat.of F)) r z ⊤ c₀ * val w (r ≫ φ.left) z J) (α : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε N))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w'))
    (z : (DegPre.BF D F).left) (J) (hJ : Good D.P.L z J) :
    val u (𝟙 _) z J = gm (X := Spec (CommRingCat.of F)) (fst (TF (R := R) F) D.P.A).left z ⊤ c₀ *
      fac g' N w α (fst (TF (R := R) F) D.P.A ≫ φ) (snd _ _) z J := by
  have e : g.b = φ ≫ g'.b := Over.OverMorphism.ext hp.1
  have hb' : g.b ^ N = 1 := by rw [e, ← MonObj.comp_pow, hb, MonObj.comp_one]
  have k := (gen_u D F hG N α (α + 0) g.b (by rw [add_zero, hb', _root_.mul_one]) _
    (mulGen_isGen _ _ _ _ _ _ _ (g.isGen α) hw') (fun U _ h => by
    refine (Fintype.prod_sum_type _).trans ?_
    rw [Fin.prod_univ_four, Fin.prod_univ_two]
    show h (cP D _ α * g.b).left ^ (-1 : ℤ) * h (cP D _ α).left ^ (1 : ℤ) * h g.b.left ^ (1 : ℤ) *
      h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) *
      (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (N : ℤ) * h g.b.left ^ (-(N : ℤ))) = _
    simp only [zpow_neg, zpow_one, zpow_natCast]
    ac_rfl)).2 u hu hc _ (𝟙 _) z J hJ
  have C : IsCub (th D (T := DegPre.BF D F) z J) := isCub_cubV D.cub hJ
  have hm : (fst (TF (R := R) F) D.P.A ≫ g.b) ^ N = 1 := by rw [← MonObj.comp_pow, hb', MonObj.comp_one]
  have e₁ : val (g.s α) (fst (TF (R := R) F) D.P.A).left z J =
      val (g'.s α) (fst (TF (R := R) F) D.P.A ≫ φ).left z J := (val_corr hJ (hp.2 α) _).trans (val_pull hJ _ _ _)
  rw [uVal, Category.id_comp, Category.id_comp, Category.id_comp, Over.id_left, val_mul hJ, C.N_split, hm, C.face₂,
    _root_.one_mul, C.s12, e₁, vw _ _ z J hJ] at k
  refine k.trans ?_
  rw [fac, Category.assoc, ← e, Over.comp_left]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem phiRaw_of (hG : GlobalFnsSt) {φ : TF (R := R) F ⟶ T} {g' : GtPt D T} {g : GtPtF D F}
    (hp : GtPt.IsPullF F φ.left g' g) {N : ℕ} (hb : g'.b ^ N = 1) {w} {c₀ : Γ(Spec (CommRingCat.of F), ⊤)ˣ}
    {w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε N))} (hw' : w'.IsGen)
    (vw : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      val w' r z J = gm (X := Spec (CommRingCat.of F)) r z ⊤ c₀ * val w (r ≫ φ.left) z J)
    {s s' : Raw D F N} {n : ℕ} {c : Fin n → F} {f : Fin n → ∀ α, SecBT D (𝟙_ _) N α}
    (hE : ∀ (α : D.X) (Z : Scheme.{0}) (rF : Z ⟶ (DegPre.BF D F).left) (rB : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
      rB ≫ (snd _ D.P.A).left = rF ≫ (DegPre.prB D F).left → ∀ (z : Z) (J), Good D.P.L z J →
        sval (s α) rF z J = ∑ i, gs rF z ⊤ (scal (fst (TF (R := R) F) D.P.A).left (c i)) * sval (f i α) rB z J)
    {f' : Fin n → ∀ α, SecBT D T N α}
    (hf' : ∀ i α (T' : Over (Spec (CommRingCat.of R))) (τ : T' ⟶ T) (y : T' ⟶ D.P.A) (z : T'.left) (J),
      Good D.P.L z J → sval (f' i α) (lift τ y).left z J =
        sval (f i α) (lift (toUnit T') ((τ ≫ g'.b) * y)).left z J * (fac g' N w α τ y z J).val)
    {r : Fin n → Raw D F N} (hr : ∀ i, PullB D F φ N (f' i) (r i))
    (hs : ∀ α z J, Good D.P.L z J → sval (s' α) (𝟙 _) z J =
      ∑ i, gs (𝟙 _) z ⊤ (scal (fst (TF (R := R) F) D.P.A).left
        ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c₀.val * c i)) * sval (r i α) (𝟙 _) z J) :
    PhiRaw D F N 0 g w' s s' := by
  intro α u hu hc
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).2 fun z J hJ => ?_
  have e : g.b = φ ≫ g'.b := Over.OverMorphism.ext hp.1
  have e₁ : φ ▷ D.P.A = lift (fst (TF (R := R) F) D.P.A ≫ φ) (snd _ _) := by ext <;> simp
  have e₂ : (DegPre.trPt D F g.b).left ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R) F) D.P.A).left :=
    congrArg (fun q => q.left) (tr_fst D F g.b)
  have h₁ := hE α _ (DegPre.trPt D F g.b).left
    (lift (toUnit _) (((fst (TF (R := R) F) D.P.A ≫ φ) ≫ g'.b) * snd (TF (R := R) F) D.P.A)).left
    (by rw [← Over.comp_left, ← Over.comp_left, lift_snd, tr_pr, e, mul_comm, Category.assoc]) z J hJ
  refine (congrArg (fun a => sval (s' a) (𝟙 _) z J) (add_zero α)).trans ((hs α z J hJ).trans ?_)
  rw [Category.id_comp, h₁, val_phi hG hp hb hw' vw α u hu hc z J hJ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_scal_unit, gs_scal_of _ _ e₂, hr i α z J hJ, e₁, hf' i α _ _ _ z J hJ, Units.val_mul]
  ring

end Phi

theorem main : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (φ : TF (R := V) F ⟶ TA V W) (N : ℕ), 1 ≤ N → ∀ (x : TA V W ⟶ G) (g' : GtPt D (TA V W)) (g : GtPtF D F) (xA : TFK (R := V) F ⟶ A.A), x ^ N = 1 → U.Red x g' → GtPt.IsPullF F φ.left g' g → U.SamePt xA (φ ≫ x) → U.Acts F N 0 g xA) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U W _ _ _ hW F _ _ φ N hN x g' g xA hx hr hp hA
  have := hW.2.2.2.2
  have hG := hL.globalFns
  have hb : g'.b ^ N = 1 := base_pow (φ := algebraMap V W) hr hx
  obtain ⟨f₀, w, hf₀, hw, hfr⟩ := exists_frameRel (φ := algebraMap V W) hr N
  obtain ⟨v, hv, vv⟩ := exists_thetaGen U.P.c x hx f₀ hf₀
  refine ⟨pow_eq_one_of_samePt hA (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]), fun θ hθ => ?_⟩
  subst hθ
  obtain ⟨c₀, hc⟩ := theta_ratio hG θ hA v hv
  obtain ⟨w', hw', vw⟩ := exists_line (b' := g.b) (Over.OverMorphism.ext hp.1) w hw c₀
  refine ⟨w', hw', fun t t' s s' ⟨n, c, σ, f, h₁, h₂, h₃⟩ hE' hact => ?_⟩
  choose σ' hσ using fun i => exists_translSec U.P.L.isLB x v hv (σ i)
  choose f' hf' using fun i α => exists_translFam g' hb w hw α (f i α)
  have hT : ∀ i, U.ExpT (TA V W) N (σ' i) (f' i) := fun i =>
    expT_transl hG hr hx hfr (fun T' τ y z J hJ => by rw [hσ i T' τ y z J hJ, vv T' τ y z J hJ]) (hf' i) (h₁ i)
  choose u hu using fun i => (PullSec.existsUnique_pullG U F φ N (σ' i)).exists
  choose r hr' using fun i => (PullSec.existsUnique_pullB D F φ N (f' i)).exists
  have hF : ∀ i, U.ExpF F N (u i) (r i) := fun i => by
    obtain ⟨f'', e, H⟩ := ExpExt.main hL hL2 V hV D A G U W hW N hN (σ' i)
    obtain rfl := (GlobalTheory.expT_eq_iff V hV D A G U W hW N _ _ _ _ (hT i) e).1 rfl
    exact H F φ _ _ (hu i) (hr' i)
  obtain ⟨t₀, s₀, e, vt, vs⟩ := exists_expF_sum (ExpLin.expF_linear V hV D A G U F N) n
    (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c₀.val * c i) u r hF
  obtain rfl : t' = t₀ := PullSec.sec_eq fun j => sec_ext_val A.isLB (fun z J hJ =>
    (sval_act θ hA hc hact h₂ hσ hu z J hJ).trans (vt z J hJ).symm) j
  obtain rfl := (ExpFUniq.main V hV D A G U F N _ _ _ _ hE' e).1 rfl
  exact phiRaw_of hG hp hb hw' vw h₃ hf' hr' vs

end GlobalTheory.UU.Transl
end
