import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch GlobalTheory.ArcPull GlobalTheory.FrameValue

noncomputable section
namespace GlobalTheory.Ex.Arch.FibRos

theorem exists_ros_down {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A]
    [IsCommMonObj A'] {f : S' ⟶ S} {Φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (gp : IsGrpPullback A' A f Φ) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull Φ)} (hw : w.IsGen) {a b : A ⟶ A} {a' b' : A' ⟶ A'}
    (a₁ : (1 : 𝟙_ (Over S') ⟶ A') ≫ a' = 1) (b₁ : (1 : 𝟙_ (Over S') ⟶ A') ≫ b' = 1)
    (ha : a'.left ≫ Φ = Φ ≫ a.left) (hb : b'.left ≫ Φ = Φ ≫ b.left)
    {r : LB.Gen (LB.LinComb L (rosatiφ A a b) rosatiε)} (hr : TorusExt.IsRos L a b r) :
    ∃ t : LB.Gen (LB.LinComb L' (rosatiφ A' a' b') rosatiε), TorusExt.IsRos L' a' b' t ∧
      ∀ {T' : Over S'} (x' y' : T' ⟶ A') (m : T'.left ⟶ (A ⊗ A).left), x'.left ≫ Φ = m ≫ (fst A A).left →
        y'.left ≫ Φ = m ≫ (snd A A).left → ∀ (z : T'.left) J J', Good L z J → Good L' z J' →
        val r m z J = (∏ k, om w z J J' ((lift x' y').left ≫ rosatiφ A' a' b' k) ^ rosatiε k) *
          val t (lift x' y').left z J' := by
  let Φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left := (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A'))).left
  have f₁ : (fst A' A').left ≫ Φ = Φ₂ ≫ (fst A A).left :=
    (congrArg (fun q => q.left) (lift_fst (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).symm
  have f₂ : (snd A' A').left ≫ Φ = Φ₂ ≫ (snd A A).left :=
    (congrArg (fun q => q.left) (lift_snd (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).symm
  have f₃ : (fst A' A' ≫ a').left ≫ Φ = Φ₂ ≫ (fst A A ≫ a).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, f₁, Category.assoc]
  have f₄ : (snd A' A' ≫ b').left ≫ Φ = Φ₂ ≫ (snd A A ≫ b).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hb, ← Category.assoc, f₂, Category.assoc]
  have hψ : ∀ i, rosatiφ A' a' b' i ≫ Φ = Φ₂ ≫ rosatiφ A a b i := fun i => by
    fin_cases i
    exacts [mul_push gp Φ₂ f₃ f₂, f₃, f₂, mul_push gp Φ₂ f₁ f₄, f₁, f₄]
  have cmp : ∀ {T' : Over S'} (x' y' : T' ⟶ A') (m : T'.left ⟶ (A ⊗ A).left), x'.left ≫ Φ = m ≫ (fst A A).left →
      y'.left ≫ Φ = m ≫ (snd A A).left → (lift x' y').left ≫ Φ₂ = m := fun x' y' m hx hy => by
    apply pullback.hom_ext
    · refine Eq.trans ?_ hx
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) f₁.symm).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_fst]
    · refine Eq.trans ?_ hy
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) f₂.symm).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
  obtain ⟨t, ht, vt⟩ := exists_down_om hw hL hL' Φ₂ hψ r hr.1
  refine ⟨t, ⟨ht, corr_of_val hL' fun y I' hI' => ?_⟩, fun x' y' m hx hy z J J' hJ hJ' => ?_⟩
  · obtain ⟨I, hI⟩ := DegPull.exists_good' hL y
    have o : lift (1 : 𝟙_ (Over S') ⟶ A') (1 : 𝟙_ (Over S') ⟶ A') = lift η[A'] η[A'] := by simp [Hom.one_def]
    have he : eSec A' ≫ Φ = f ≫ eSec A := (cubeMapOf gp).e_comm
    have o₁ : (1 : 𝟙_ (Over S') ⟶ A').left = eSec A' := Category.id_comp _
    have e := vt _ (lift (1 : 𝟙_ (Over S') ⟶ A') (1 : 𝟙_ (Over S') ⟶ A')).left y I I' hI hI'
    rw [prod_ros, cmp 1 1 (f ≫ zero2 A) (by
        rw [o₁, he, Category.assoc, ← Over.comp_left, lift_fst]; rfl) (by
        rw [o₁, he, Category.assoc, ← Over.comp_left, lift_snd]; rfl),
      a₁, b₁, _root_.mul_one, o] at e
    have e₁ := (val_pull hI _ _ _).symm.trans ((val_corr hI hr.2 f).trans (val_one _))
    rw [e₁] at e
    rw [val_pull hI', val_one, Category.id_comp]
    simpa using e.symm
  · have e := vt _ (lift x' y').left z J J' hJ hJ'
    rwa [cmp x' y' m hx hy] at e

theorem stalkUnits_symm_gm {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)ˣ) : (((TorusExt.stalkUnits z).symm (gm x z U a) : Fˣ) : F) = valF x U a.val := by
  refine (TorusExt.stalkConst z).injective ?_
  rw [← TorusExt.stalkUnits_val, MulEquiv.apply_symm_apply]
  exact (toStk_valF x U z h a).symm

theorem vF_eq_genVal {X Y Y' : Scheme.{0}} {L : LB X} {A : Over (Sp ℂ)} [GrpObj A] {L' : LB A.left} {g : ℕ}
    {u : HolUnif A L' g} (hL' : L'.IsLB) {Φ : A.left ⟶ X} {w : LB.Iso L' (L.pull Φ)} {J : (Sp ℂ ⟶ X) → L.ι}
    (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {fr : (Fin g → ℂ) → ℂˣ}
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ Φ), i)).val * u.fr i z)
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ A.left)} {ε : K → ℤ}
    (r : LB.Gen (LB.LinComb L φ ε)) {t : LB.Gen (LB.LinComb L' φ' ε)} (ht : t.IsGen) (m : Sp ℂ ⟶ Y) {y : Sp ℂ ⟶ Y'}
    {z : K → Fin g → ℂ} (hz : IsLift u φ' y z)
    (h : ∀ (p : Sp ℂ) J', Good L' p J' → val r m p J = (∏ k, om w p J J' (y ≫ φ' k) ^ ε k) * val t y p J') :
    vF r m J = genVal u hL' t y z * ((∏ k, fr (z k) ^ ε k : ℂˣ) : ℂ) := by
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have gJ : Good L p J := fun ψ => hJ ψ trivial
  have gJ' : Good L' p (chartAt hL') := fun ψ => le_chartAt hL' ψ trivial
  have e := congrArg (fun q => (((TorusExt.stalkUnits p).symm q : ℂˣ) : ℂ)) (h p _ gJ')
  simp only [map_mul, map_prod, map_zpow, Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val] at e ⊢
  have e₁ : (((TorusExt.stalkUnits p).symm (val r m p J) : ℂˣ) : ℂ) = vF r m J :=
    stalkUnits_symm_gm _ _ p (gJ.mem φ m) _
  have e₂ : (((TorusExt.stalkUnits p).symm (val t y p (chartAt hL')) : ℂˣ) : ℂ) =
      genVal u hL' t y z * frameProd u ε z fun k => chartAt hL' (y ≫ φ' k) :=
    (stalkUnits_symm_gm _ _ p (gJ'.mem φ' y) _).trans (valAt'_gen hL' ht hz (le_wchart_chartAt hL' φ' y))
  rw [e₁, e₂, mul_left_comm, frameProd, ← Finset.prod_mul_distrib] at e
  refine e.trans (congrArg _ (Finset.prod_congr rfl fun k _ => ?_))
  rw [← mul_zpow, hz k, hfr _ _ (le_chartAt hL' _)]
  refine congrArg (fun q => (q * _) ^ ε k) ?_
  have hm : (u.ex (z k)).left p ∈ (L.pull Φ).U (fun _ => J ((u.ex (z k)).left ≫ Φ)) ⊓
      L'.U (chartAt hL' (u.ex (z k)).left) := ⟨mem_pull.2 (gJ ((u.ex (z k)).left ≫ Φ)), gJ' _⟩
  exact stalkUnits_symm_gm _ _ p hm _

theorem fibRosSt : Laws → FibRosSt := by
  rintro - R _ _ _ D J g Λ Hm χ ex fr ⟨hJ, P', φ, w, u, hΛ, gp, hw, hAH, -, -, -, hex, hfr⟩ f f' - - F G hF hG r hr
  have down : ∀ (a : D.P.A ⟶ D.P.A) (H : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ z, ex (H z) = ex z ≫ a) →
      ∃ a' : P'.A ⟶ P'.A, a'.left ≫ φ = φ ≫ a.left ∧ (∀ z, u.ex (H z) = u.ex z ≫ a') ∧
        (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A) ≫ a' = 1 := fun a H hH => by
    let a' : P'.A ⟶ P'.A := Over.homMk (gp.1.lift (φ ≫ a.left) P'.A.hom
      (by rw [Category.assoc, Over.w, gp.1.w])) (gp.1.lift_snd _ _ _)
    have ha : a'.left ≫ φ = φ ≫ a.left := gp.1.lift_fst _ _ _
    have hu : ∀ z, u.ex (H z) = u.ex z ≫ a' := fun z =>
      Over.OverMorphism.ext (gp.1.hom_ext (by
        rw [← hex, hH, Over.comp_left, Over.comp_left, hex, Category.assoc, Category.assoc, ha]) (by rw [Over.w, Over.w]))
    refine ⟨a', ha, hu, ?_⟩
    have h0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
    rw [← h0, ← hu, map_zero]
  obtain ⟨a, ha, ua, a₁⟩ := down f F hF
  obtain ⟨b, hb, ub, b₁⟩ := down f' G hG
  obtain ⟨t, ht, vt⟩ := exists_ros_down gp D.P.isLB P'.isLB hw a₁ b₁ ha hb (r := r) hr
  obtain ⟨adj, one⟩ := genVal_rosati P'.isLB hAH ua ub t ht.1 ht.2
  refine ⟨adj, fun x z => ?_⟩
  have e := vF_eq_genVal P'.isLB hJ (fun z i hi => by rw [← hex]; exact hfr z i hi) r ht.1 (lift (ex x) (ex z)).left
    (isLift_rosati ua ub x z) (fun p J' hJ' => vt (u.ex x) (u.ex z) _
      ((hex x).symm.trans (congrArg (fun q => q.left) (lift_fst (ex x) (ex z)).symm))
      ((hex z).symm.trans (congrArg (fun q => q.left) (lift_snd (ex x) (ex z)).symm)) p J J'
      (fun ψ => hJ ψ trivial) hJ')
  rw [e, one, _root_.one_mul]
  simp only [Fin.prod_univ_six, rosatiLift, rosatiε, Matrix.cons_val, zpow_neg, zpow_one, Units.val_mul,
    Units.val_inv_eq_inv_val]
  field_simp

end GlobalTheory.Ex.Arch.FibRos
end
