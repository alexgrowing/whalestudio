import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjIsAbelianSchemeDimRigidifiedSym

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.LevelUnique

section Core

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits GlobalTheory.ThetaScalar

theorem exists_mul {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S} {m n : ℤ}
    (a : LB.Sec (LPow A L m T)) (b : LB.Sec (LPow A L n T)) : ∃ u : LB.Sec (LPow A L (m + n) T),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J, Good L z J →
        secVal u r z J = secVal a r z J * secVal b r z J := by
  obtain ⟨u, hu⟩ := exists_sec hL (K' := Fin 1) (φ' := fun _ => (snd T A).left) (ε' := fun _ => m + n)
    (formEq_of_add fun U _ h => by simp [Fintype.sum_sum_type, add_smul])
    (mulSec (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => m) (K' := Fin 1)
      (φ' := fun _ => (snd T A).left) (ε' := fun _ => n) a b)
  exact ⟨u, fun Z r z J hJ => (hu Z r z J hJ).trans (sval_mulSec _ _ r z hJ)⟩

theorem dense_translate {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    [IsIntegral (T ⊗ A).left] {m n : ℤ} (θ : ThetaGrp A L m T) {V : Type} {Z : Scheme.{0}} (z : Z)
    (r : V → (Z ⟶ (T ⊗ A).left)) (J₀ : (Z ⟶ A.left) → L.ι) (hJ₀ : Good L z J₀) (good : V → Prop)
    (s₀ : LB.Sec (LPow A L n T)) (hs : ∃ i, s₀.f i ≠ 0) (hg : ∀ v, secVal s₀ (r v) z J₀ ≠ 0 → good v)
    (dense : ∀ u : LB.Sec (LPow A L (m + n) T), (∀ v, secVal u (r v) z J₀ = 0) → ∀ j, u.f j = 0)
    (u : LB.Sec (LPow A L m T)) (hu : ∀ v, good v → secVal u (r v ≫ (translT A θ.pt).left) z J₀ = 0) (j) :
    u.f j = 0 := by
  obtain ⟨u', hu'⟩ := exists_actVal hL θ u
  obtain ⟨w, hw⟩ := exists_mul hL u' s₀
  have h0 := dense w fun v => by
    rw [hw _ _ z J₀ hJ₀]
    by_cases h : secVal s₀ (r v) z J₀ = 0
    · rw [h, MulZeroClass.mul_zero]
    · rw [hu' _ _ z J₀ hJ₀, hu v (hg v h), MulZeroClass.mul_zero, MulZeroClass.zero_mul]
  have h1 : ∀ j, u'.f j = 0 := eq_zero_of_sval (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => m) hL u'
    fun y J hJ => by
      have e : secVal w (𝟙 _) y J = 0 :=
        sval_eq_zero (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => m + n) w h0 _ y hJ
      rw [hw _ _ y J hJ] at e
      refine (mul_eq_zero.1 e).resolve_right fun e' => ?_
      obtain ⟨i, hi⟩ := hs
      exact hi (eq_zero_of_germ (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => n) s₀ y hJ e' i)
  refine eq_zero_of_sval (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => m) hL u (fun y J hJ => ?_) j
  have e := hu' _ (translT A θ.pt⁻¹).left y J hJ
  rw [← Over.comp_left, translT_mul, mul_inv_cancel, translT_one, Over.id_left] at e
  exact (Units.mul_right_eq_zero _).1 (e.symm.trans
    (sval_eq_zero (K := Fin 1) (φ := fun _ => (snd T A).left) (ε := fun _ => m) u' h1 _ y hJ))

theorem core (hL : Laws) {F : Type} [Field F] [IsAlgClosed F] [CharZero F] (P : PolAV (Spec (CommRingCat.of F)))
    (z : Sp F) (J₀ : (Sp F ⟶ P.A.left) → P.L.ι) (hJ₀ : Good P.L z J₀) {V : Type}
    (x : V → (baseOver (Spec (CommRingCat.of F)) ⟶ P.A)) (k : ℕ) (p p' : baseOver (Spec (CommRingCat.of F)) ⟶ P.A)
    (good : V → Prop) (s₀ : LB.Sec (LPow P.A P.L k (baseOver _))) (hk : 1 ≤ k) (hp : p ^ k = 1) (hp' : p' ^ k = 1)
    (dense : ∀ m : ℕ, 1 ≤ m → ∀ u : LB.Sec (LPow P.A P.L m (baseOver _)),
      (∀ v, secVal (Z := Sp F) u (ptSecT P.A (x v)).left z J₀ = 0) → ∀ j, u.f j = 0)
    (hs : ∃ i, s₀.f i ≠ 0) (hg : ∀ v, secVal (Z := Sp F) s₀ (ptSecT P.A (x v)).left z J₀ ≠ 0 → good v)
    (ratio : ∀ v, good v → ∀ t₁ t₂ : LB.Sec (LPow P.A P.L k (baseOver _)),
      secVal (Z := Sp F) t₁ (ptSecT P.A (x v * p)).left z J₀ * secVal (Z := Sp F) t₂ (ptSecT P.A (x v * p')).left z J₀ =
      secVal (Z := Sp F) t₂ (ptSecT P.A (x v * p)).left z J₀ * secVal (Z := Sp F) t₁ (ptSecT P.A (x v * p')).left z J₀) :
    p = p' := by
  haveI := P.isAb.comm
  haveI : IsIntegral (baseOver (Spec (CommRingCat.of F)) ⊗ P.A).left := isIntegral_fibre P (𝟙 _)
  have hk0 : (k : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hd : (p / p') ^ k = 1 := by rw [div_pow, hp, hp', div_one]
  obtain ⟨θ, hθ⟩ := exists_theta hL.weil P k (p / p') hd
  have ex := exists_theta hL.weil P (k + k) p' (by rw [pow_add, hp', _root_.mul_one])
  have den := dense (k + k + k) (by omega)
  rw [Nat.cast_add, Nat.cast_add] at den
  rw [Nat.cast_add] at ex
  obtain ⟨θ', hθ'⟩ := ex
  have e : ∀ a d : baseOver (Spec (CommRingCat.of F)) ⟶ P.A,
      (ptSecT P.A a).left ≫ (translT P.A d).left = (ptSecT P.A (a * d)).left := fun a d => by
    rw [← Over.comp_left, ptSecT_translT, mul_comm]
  obtain ⟨a, ha⟩ := exists_scalar P.isLB (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
    (finrank_pos_of_laws hL.globalSectionsRank P hk0) θ
    (cross_of_dense P.isLB θ (Z := Sp F) z (fun v : {v // good v} => (ptSecT P.A (x v * p')).left) J₀ hJ₀
      (fun u hu => dense_translate P.isLB θ' (Z := Sp F) z (fun v => (ptSecT P.A (x v)).left) J₀ hJ₀ good s₀ hs hg den u
        fun v hv => (congrArg (fun w => secVal (Z := Sp F) u w z J₀) ((e _ _).trans (by rw [hθ']))).trans (hu ⟨v, hv⟩))
      fun s t v => by
        have e' : (ptSecT P.A (x v * p')).left ≫ (translT P.A θ.pt).left = (ptSecT P.A (x v * p)).left := by
          rw [e, hθ, _root_.mul_assoc, mul_div_cancel]
        exact (congrArg (fun w => secVal (Z := Sp F) s w z J₀ * _) e').trans ((ratio v v.2 s t).trans
          (congrArg (fun w => secVal (Z := Sp F) t w z J₀ * _) e').symm))
  have := theta_pt_eq_one_of_actVal hL.weil hL.weilNondeg hL.globalSectionsRank P k hk0 θ (by rw [hθ]; exact hd) a ha
  rw [hθ] at this
  exact div_eq_one.1 this

theorem move {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {g : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (w : LB.Iso L' (L.pull g)) (hw : w.IsGen) (π : Y' ⟶ X') (q : Y ⟶ X) (h : Y' ⟶ Y) (h' : Y ⟶ Y')
    (hψ : π ≫ g = h ≫ q) (hh : h ≫ h' = 𝟙 _) (hh' : h' ≫ h = 𝟙 _) (m : ℤ) :
    (∀ t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => m)),
      ∃ a : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => π) (fun _ => m)),
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J J', Good L z J → Good L' z J' →
          sval t (r ≫ h) z J = (ConstFam.wVal w z J J' (r ≫ π) ^ m).val * sval a r z J') ∧
    (∀ a : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => π) (fun _ => m)),
      ∃ t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => m)),
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J J', Good L z J → Good L' z J' →
          sval t (r ≫ h) z J = (ConstFam.wVal w z J J' (r ≫ π) ^ m).val * sval a r z J') := by
  refine ⟨fun t => ?_, fun a => ?_⟩
  · obtain ⟨a, ha⟩ := ConstFam.exists_secThrough (φ' := fun _ : Fin 1 => π) hw hL hL' (fun _ => hψ) t
    refine ⟨a, fun Z r z J J' hJ hJ' => (ha.sval (fun _ => hψ) r hJ hJ').trans ?_⟩
    rw [Fin.prod_univ_one]
  · obtain ⟨t₀, ht₀⟩ := ConstFam.exists_sec_up ((isGen_iff w).1 hw) hL hL' a
    have H : ConstFam.SecThrough w (fun _ : Fin 1 => π) (fun _ => π ≫ g) (fun _ => m) a t₀ (𝟙 _) :=
      fun Z r z p q hp hq => by
        rw [Category.comp_id]
        exact ht₀ Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)
    have hq : h' ≫ π ≫ g = q := by rw [hψ, ← Category.assoc, hh', Category.id_comp]
    obtain ⟨t, ht⟩ := exists_sec hL (K' := Fin 1) (φ' := fun _ => q) (ε' := fun _ => m)
      (formEq_of_add fun U _ h => by rw [Fin.sum_univ_one, Fin.sum_univ_one, hq]) (pullSec t₀ h')
    refine ⟨t, fun Z r z J J' hJ hJ' => (ht Z _ z J hJ).trans ((sval_pullSec _ _ _ z hJ).trans ?_)⟩
    rw [Category.assoc, hh]
    refine (H.sval (fun _ => (Category.id_comp _).symm) r hJ hJ').trans ?_
    rw [Fin.prod_univ_one]

theorem toStk_sval {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {q : Y ⟶ X} {m : ℕ} (u : ArcPts.SecP L q m)
    (r : Sp F ⟶ Y) (z : Sp F) {J} (hJ : Good L z J) (j : L.ι) (hj : ⊤ ≤ (r ≫ q) ⁻¹ᵁ L.U j) :
    toStk z (ArcPts.sval u r j) =
      (trF (L := L) (fun _ : Fin 1 => q) (fun _ => (m : ℤ)) r z (fun _ => j) (fun _ => J (r ≫ q))).val *
        sval u r z J := by
  have hm : r z ∈ LB.wchart L (fun _ : Fin 1 => q) (fun _ => j) :=
    Set.mem_iInter.2 fun _ => (top_le_iff_mem (r ≫ q) _ z).1 hj
  exact (toStk_valF_gs r _ z hm _).trans (sec_trans u r z hm (hJ.mem _ r))

theorem fibre (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {F : Type} [Field F] [IsAlgClosed F] [CharZero F]
    (y : Sp F ⟶ S) {V : Type} (x : V → (Over.mk y ⟶ P.A)) (k : ℕ) (p p' : Over.mk y ⟶ P.A) (good : V → Prop)
    (s₀ : ArcPts.SecP P.L (pullback.fst P.A.hom y) k) (hk : 1 ≤ k) (hp : p ^ k = 1) (hp' : p' ^ k = 1)
    (dense : ∀ m, 1 ≤ m → ∀ u : ArcPts.SecP P.L (pullback.fst P.A.hom y) m,
      (∀ v j, ⊤ ≤ (x v).left ⁻¹ᵁ P.L.U j → ArcPts.sval u (ArcPts.fib (x v)) j = 0) → ∀ i, u.f i = 0)
    (hs : ∃ i, s₀.f i ≠ 0)
    (hgood : ∀ v j, ⊤ ≤ (x v).left ⁻¹ᵁ P.L.U j → ArcPts.sval s₀ (ArcPts.fib (x v)) j ≠ 0 → good v)
    (ratio : ∀ v, good v → ∀ (t₁ t₂ : ArcPts.SecP P.L (pullback.fst P.A.hom y) k) j j',
      ⊤ ≤ (x v * p).left ⁻¹ᵁ P.L.U j → ⊤ ≤ (x v * p').left ⁻¹ᵁ P.L.U j' →
      ArcPts.sval t₁ (ArcPts.fib (x v * p)) j * ArcPts.sval t₂ (ArcPts.fib (x v * p')) j' =
        ArcPts.sval t₂ (ArcPts.fib (x v * p)) j * ArcPts.sval t₁ (ArcPts.fib (x v * p')) j') : p = p' := by
  obtain ⟨P', g, hg, -, hmul, t, ht⟩ := hL.polBaseChange S (Spec (CommRingCat.of F)) y P
  obtain ⟨w, hw⟩ : LBIso P'.L (P.L.pull g) := LBIso.symm ⟨t, ht⟩
  let T := baseOver (Spec (CommRingCat.of F))
  let σ : P'.A ⟶ T ⊗ P'.A := lift (Over.homMk P'.A.hom (Category.comp_id _)) (𝟙 _)
  have h₁ : σ ≫ snd _ _ = 𝟙 _ := lift_snd _ _
  have h₂ : snd _ _ ≫ σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.mkIdTerminal.hom_ext _ _
    · rw [Category.assoc, h₁, Category.comp_id, Category.id_comp]
  have h₁' : σ.left ≫ (snd T P'.A).left = 𝟙 _ := congrArg CommaMorphism.left h₁
  have h₂' : (snd T P'.A).left ≫ σ.left = 𝟙 _ := congrArg CommaMorphism.left h₂
  have hh : ((snd T P'.A).left ≫ hg.isoPullback.hom) ≫ (hg.isoPullback.inv ≫ σ.left) = 𝟙 _ := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, h₂']
  have hh' : (hg.isoPullback.inv ≫ σ.left) ≫ ((snd T P'.A).left ≫ hg.isoPullback.hom) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc σ.left, h₁', Category.id_comp, Iso.inv_hom_id]
  have mv := move P.isLB P'.isLB w hw (snd T P'.A).left (pullback.fst P.A.hom y) _ _
    (by rw [Category.assoc, hg.isoPullback_hom_fst]) hh hh'
  let φ₀ : (Over.mk y ⟶ P.A) → (T ⟶ P'.A) := fun a =>
    Over.homMk (hg.lift a.left (𝟙 _) ((Over.w a).trans (Category.id_comp _).symm)) (hg.lift_snd _ _ _)
  have φg : ∀ a, (φ₀ a).left ≫ g = a.left := fun a => hg.lift_fst _ _ _
  have inj : ∀ a b : T ⟶ P'.A, a.left ≫ g = b.left ≫ g → a = b := fun a b e =>
    Over.OverMorphism.ext (hg.hom_ext e ((Over.w a).trans (Over.w b).symm))
  let io : Over.mk (T.hom ≫ y) ⟶ Over.mk y := Over.homMk (𝟙 _) rfl
  have tb : ∀ a, toBase hg.w (φ₀ a) = io ≫ a := fun a =>
    Over.OverMorphism.ext ((φg a).trans (Category.id_comp _).symm)
  let φ : (Over.mk y ⟶ P.A) →* (T ⟶ P'.A) := MonoidHom.mk' φ₀ fun a b => inj _ _ (by
    have e := hmul T (φ₀ a) (φ₀ b)
    rw [tb, tb, ← MonObj.comp_mul] at e
    exact (φg _).trans ((Category.id_comp _).symm.trans (congrArg CommaMorphism.left e).symm))
  have pt : ∀ a, (ptSecT P'.A (φ a)).left ≫ (snd T P'.A).left ≫ hg.isoPullback.hom = ArcPts.fib a := fun a => by
    have e : (ptSecT P'.A (φ a)).left ≫ (snd T P'.A).left = (φ₀ a).left :=
      congrArg CommaMorphism.left (lift_snd (𝟙 _) (φ a))
    rw [← Category.assoc, e]
    apply pullback.hom_ext
    · rw [Category.assoc, hg.isoPullback_hom_fst, φg]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, hg.isoPullback_hom_snd]
      exact (hg.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  have fq : ∀ a : Over.mk y ⟶ P.A, ArcPts.fib a ≫ pullback.fst P.A.hom y = a.left := fun a => pullback.lift_fst _ _ _
  let z : Sp F := IsLocalRing.closedPoint F
  obtain ⟨J, hJ⟩ := ConstFam.exists_good' P.isLB z
  obtain ⟨J', hJ'⟩ := ConstFam.exists_good' P'.isLB z
  have ch : ∀ a : Over.mk y ⟶ P.A, ⊤ ≤ a.left ⁻¹ᵁ P.L.U (J a.left) := fun a =>
    (top_le_iff_mem (F := F) a.left _ z).2 (hJ a.left)
  have rd : ∀ (m : ℕ) (a : Over.mk y ⟶ P.A) j, ⊤ ≤ a.left ⁻¹ᵁ P.L.U j → ∃ c : ((Sp F).presheaf.stalk z)ˣ,
      ∀ (u : ArcPts.SecP P.L (pullback.fst P.A.hom y) m) (u' : LB.Sec (LPow P'.A P'.L m T)),
        (∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ P'.A).left) (z : Z) J J', Good P.L z J → Good P'.L z J' →
          sval u (r ≫ (snd T P'.A).left ≫ hg.isoPullback.hom) z J =
            (ConstFam.wVal w z J J' (r ≫ (snd T P'.A).left) ^ (m : ℤ)).val * secVal u' r z J') →
        toStk z (ArcPts.sval u (ArcPts.fib a) j) = c.val * secVal (Z := Sp F) u' (ptSecT P'.A (φ a)).left z J' :=
    fun m a j hj => ⟨_ * _, fun u u' H => by
      have e := H (Sp F) (ptSecT P'.A (φ a)).left z J J' hJ hJ'
      refine (toStk_sval u _ z hJ j (by rw [fq]; exact hj)).trans ?_
      rw [Units.val_mul, _root_.mul_assoc]
      exact congrArg _ ((congrArg (fun r => sval u r z J) (pt a)).symm.trans e)⟩
  obtain ⟨s₁, hs₁⟩ := (mv k).1 s₀
  have main : φ p = φ p' := by
    refine core hL P' z J' hJ' (fun v => φ (x v)) k (φ p) (φ p') good s₁ hk (by rw [← map_pow, hp, map_one])
      (by rw [← map_pow, hp', map_one]) (fun m hm u' hu' => ?_) ?_ (fun v hv => ?_) fun v hv t₁ t₂ => ?_
    · obtain ⟨u, hu⟩ := (mv m).2 u'
      have h0 := dense m hm u fun v j hj => by
        obtain ⟨c, hc⟩ := rd m (x v) j hj
        refine (toStk z).injective ((hc u u' hu).trans ?_)
        rw [hu' v, MulZeroClass.mul_zero, map_zero]
      refine eq_zero_of_sval (K := Fin 1) (φ := fun _ => (snd T P'.A).left) (ε := fun _ => (m : ℤ)) P'.isLB u'
        fun b I' hI' => ?_
      obtain ⟨I, hI⟩ := ConstFam.exists_good' P.isLB b
      exact (Units.mul_right_eq_zero _).1 ((hu _ _ b I I' hI hI').symm.trans (sval_eq_zero u h0 _ b hI))
    · by_contra hn
      push Not at hn
      obtain ⟨i, hi⟩ := hs
      refine hi (eq_zero_of_sval P.isLB s₀ (fun b I hI => ?_) i)
      obtain ⟨I', hI'⟩ := ConstFam.exists_good' P'.isLB b
      have e := hs₁ _ (hg.isoPullback.inv ≫ σ.left) b I I' hI hI'
      rw [hh', sval_eq_zero s₁ hn _ b hI', MulZeroClass.mul_zero] at e
      exact e
    · obtain ⟨c, hc⟩ := rd k (x v) _ (ch _)
      refine hgood v _ (ch _) fun e => hv ?_
      have e' := hc s₀ s₁ hs₁
      rw [e, map_zero] at e'
      exact (Units.mul_right_eq_zero _).1 e'.symm
    · obtain ⟨u₁, h₁⟩ := (mv k).2 t₁
      obtain ⟨u₂, h₂⟩ := (mv k).2 t₂
      obtain ⟨c, hc⟩ := rd k (x v * p) _ (ch _)
      obtain ⟨c', hc'⟩ := rd k (x v * p') _ (ch _)
      have H := congrArg (toStk z) (ratio v hv u₁ u₂ _ _ (ch _) (ch _))
      rw [map_mul, map_mul, hc u₁ t₁ h₁, hc u₂ t₂ h₂, hc' u₁ t₁ h₁, hc' u₂ t₂ h₂, _root_.mul_mul_mul_comm,
        _root_.mul_mul_mul_comm c.val (secVal t₂ _ z J'), ← Units.val_mul, Units.mul_right_inj, map_mul, map_mul] at H
      exact H
  exact Over.OverMorphism.ext ((φg p).symm.trans ((congrArg (fun a => a.left ≫ g) main).trans (φg p')))

end Core

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem torsion_eq_of_same_ratios : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l bb s) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (y : Sp F ⟶ S) (V : Type) (x : V → (Over.mk y ⟶ o.t.G)) (k : ℕ) (p p' : Over.mk y ⟶ o.t.G) (good : V → Prop) (s₀ : SecP o.t.PP.L (pullback.fst o.t.G.hom y) k), 1 ≤ k → p ^ k = 1 → p' ^ k = 1 → (∀ m, 1 ≤ m → ∀ u : SecP o.t.PP.L (pullback.fst o.t.G.hom y) m, (∀ v j, ⊤ ≤ (x v).left ⁻¹ᵁ o.t.PP.L.U j → sval u (fib (x v)) j = 0) → ∀ i, u.f i = 0) → (∃ i, s₀.f i ≠ 0) → (∀ v j, ⊤ ≤ (x v).left ⁻¹ᵁ o.t.PP.L.U j → sval s₀ (fib (x v)) j ≠ 0 → good v) → (∀ v, good v → ∀ (t₁ t₂ : SecP o.t.PP.L (pullback.fst o.t.G.hom y) k) j j', ⊤ ≤ (x v * p).left ⁻¹ᵁ o.t.PP.L.U j → ⊤ ≤ (x v * p').left ⁻¹ᵁ o.t.PP.L.U j' → sval t₁ (fib (x v * p)) j * sval t₂ (fib (x v * p')) j' = sval t₂ (fib (x v * p)) j * sval t₁ (fib (x v * p')) j') → p = p' :=
  fun hL _ _ _ _ _ _ _ _ _ _ _ _ _ _ o _ _ _ _ y _ x k p p' good s₀ =>
    fibre hL (objPolAV o) y x k p p' good s₀

end GlobalTheory.LevelUnique
