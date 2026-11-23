import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.JetBC

open ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift GlobalTheory.ThetaPtMove

theorem gs_appLE' {X Y Z : Scheme.{0}} (F : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ F ⁻¹ᵁ U) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ V) (a : Γ(X, U)) : gs r z V ((F.appLE U V h).hom a) = gs (r ≫ F) z U a :=
  (gs_res r z h hz _).trans (gs_pull r F z U (h hz) a)

theorem valR_congr {B : Type} [CommRing B] {X X' : Scheme.{0}} {x : Sp B ⟶ X} {x' : Sp B ⟶ X'} {U : X.Opens}
    {U' : X'.Opens} {a : Γ(X, U)} {a' : Γ(X', U')} (hU : ∀ z, x' z ∈ U' ↔ x z ∈ U)
    (h : ∀ z, x' z ∈ U' → gs x z U a = gs x' z U' a') : valR x U a = valR x' U' a' := by
  by_cases h' : ⊤ ≤ x' ⁻¹ᵁ U'
  · have h₀ : ⊤ ≤ x ⁻¹ᵁ U := fun z hz => (hU z).1 (h' hz)
    rw [valR, valR, dif_pos h', dif_pos h₀]
    refine congrArg _ (fn_ext fun z hz => ?_)
    rw [gs_appLE' _ _ _ _ _ _ hz, gs_appLE' _ _ _ _ _ _ hz, Category.id_comp, Category.id_comp]
    exact h z (h' hz)
  · have h₀ : ¬ ⊤ ≤ x ⁻¹ᵁ U := fun e => h' fun z hz => (hU z).2 (e hz)
    rw [valR, valR, dif_neg h', dif_neg h₀]

theorem val_rigT' {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (rig : LB.Gen (L.pull (eSec A)))
    (T : Over S) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J : (Z ⟶ A.left) → L.ι) (hJ : Good L z J) :
    val (rigT A L rig T k) r z J = val rig (r ≫ T.hom) z J ^ k := by
  have hm2 : T.hom (r z) ∈ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)) :=
    Set.mem_iInter.2 fun _ => hJ (r ≫ T.hom ≫ eSec A)
  have key := gm_pull r T.hom z (LB.wchart L (fun _ : PUnit => eSec A) fun _ => J (r ≫ T.hom ≫ eSec A)) hm2
    (rig.s fun _ => J (r ≫ T.hom ≫ eSec A))
  have hm' : r z ∈ LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) (fun k => J (r ≫ T.hom ≫ eSec A)) :=
    hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  rw [val_of rig (r ≫ T.hom) z J (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => by rw [Category.assoc])]
  unfold val rigT
  rw [map_zpow]
  congr 1
  rw [gm_res r z _ hm']
  exact key

def Chartwise {X X' : Scheme.{0}} {L₀ : LB X} {L₁ : LB X'} {φ : X' ⟶ X} (w : LB.Iso L₁ (L₀.pull φ))
    (c : L₁.ι → L₀.ι) : Prop :=
  (∀ (x : X') i, x ∈ L₁.U i ↔ φ x ∈ L₀.U (c i)) ∧
    ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X') (z : Z) i, ψ z ∈ L₁.U i → gw w ψ z (c i) i = 1

theorem chartwise_id {X X' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (φ : X' ⟶ X) :
    Chartwise (Geo.Tor.idIso (L.pull φ)) (fun i => i PUnit.unit) :=
  ⟨fun _ _ => mem_pull, fun _ ψ z _ hi => gm_self (pull_isLB hL φ) ψ z hi⟩

section Move

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)} {c : L₁.ι → L₀.ι}

include hp in

theorem exists_gauge (hL₀ : L₀.IsLB) (hc : Chartwise w c) {Z : Scheme.{0}} (b : Z ⟶ S') {z : Z} {J'}
    (hJ' : Good L₁ z J') : ∃ J, Good L₀ z J ∧ ∀ ψ : Z ⟶ A.left, ψ ≫ A.hom = b →
      J (ψ ≫ φ) = c (J' ψ) ∧ wVal w z J J' ψ = 1 := by
  obtain ⟨J, hJ, e⟩ := exists_good L₀ hL₀ z (K := {ψ : Z ⟶ A.left // ψ ≫ A.hom = b}) (fun k => k.1 ≫ φ)
    (fun k => c (J' k.1)) (fun a a' h => by rw [hp.1.hom_ext h (a.2.trans a'.2.symm)])
    (fun k => (hc.1 _ _).1 (hJ' k.1))
  refine ⟨J, hJ, fun ψ h => ⟨e ⟨ψ, h⟩, ?_⟩⟩
  rw [wVal, e ⟨ψ, h⟩]
  exact hc.2 _ _ _ _ (hJ' ψ)

theorem symLift_chartwise [IsCommMonObj A] (hw : w.IsGen) (hc : Chartwise w c) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {k : ℤ}
    {n : ℕ} {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) {θ₀ : ThetaGrp G L₀ k T₀}
    (H₀ : SymLift G L₀ k n x₀ θ₀) : ∃ θ : ThetaGrp A L₁ k T, SymLift A L₁ k n x θ ∧
      ∀ s₀ s₀' s s', SecRel hp τ hτ w s s₀ → SecRel hp τ hτ w s' s₀' → IsActOf G L₀ k θ₀ s₀ s₀' →
        IsActOf A L₁ k θ s s' := by
  obtain ⟨rfl, hpow, ν₀, hν₀, hs⟩ := H₀
  obtain ⟨a, ha, v⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_tr' hp τ hτ x _ hx) θ₀.φ θ₀.isGen
  obtain ⟨ν, hν, u⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_neg hp τ hτ) ν₀ hν₀
  let θ : ThetaGrp A L₁ k T := ⟨x, a, ha⟩
  have t : ∀ {y : T ⟶ A} {y₀ : T₀ ⟶ G}, τ ≫ y₀.left = y.left ≫ φ →
      (𝟙 _ ≫ psi hp τ hτ) ≫ (translT G y₀).left = (𝟙 _ ≫ (translT A y).left) ≫ psi hp τ hτ :=
    fun h => by
      rw [Category.assoc, Category.assoc]
      exact congrArg _ (psi_transl hp τ hτ _ _ h).symm
  have o₁ : ∀ q : T ⊗ A ⟶ A, (𝟙 _ ≫ q.left) ≫ A.hom = (T ⊗ A).hom := fun q => by rw [Category.id_comp, Over.w]
  have o₂ : ∀ (p : T ⊗ A ⟶ T ⊗ A) (q : T ⊗ A ⟶ A), ((𝟙 _ ≫ p.left) ≫ q.left) ≫ A.hom = (T ⊗ A).hom := fun p q => by
    rw [Category.id_comp, Category.assoc, Over.w, Over.w]
  refine ⟨θ, ⟨rfl, corr_of_val hL₁ fun y J' hJ' => ?_, ν, hν, corr_of_val hL₁ fun y J' hJ' => ?_⟩,
    fun s₀ s₀' s s' h h' H => isTwistPull_move hp τ hτ hL₀ hL₁ (psi_tr' hp τ hτ x _ hx) ha v h h' H⟩
  · obtain ⟨J, hJ, g⟩ := exists_gauge hp hL₀ hc (T ⊗ A).hom hJ'
    have q := val_corr hJ hpow (𝟙 _ ≫ psi hp τ hτ)
    rw [val_powGen _ _ _ hJ, val_one] at q
    rw [val_powGen _ _ _ hJ', val_one]
    have e : ∀ i : ℕ, tval θ₀ ((𝟙 _ ≫ psi hp τ hτ) ≫ (translT G (θ₀.pt ^ i)).left) y J =
        tval θ (𝟙 _ ≫ (translT A (x ^ i)).left) y J' := fun i => by
      rw [t (over_pow hp τ hτ hx i)]
      refine (v _ _ _ _ _ hJ hJ').trans ?_
      rw [(g _ (o₂ _ _)).2, (g _ (o₂ _ _)).2, one_zpow, one_zpow, _root_.one_mul, _root_.one_mul]
      rfl
    simp only [e] at q
    exact q
  · obtain ⟨J, hJ, g⟩ := exists_gauge hp hL₀ hc (T ⊗ A).hom hJ'
    have q := val_corr hJ hs (𝟙 _ ≫ psi hp τ hτ)
    rw [val_symGen _ _ _ hJ, val_one] at q
    refine (val_symGen θ ν _ hJ').trans (Eq.trans ?_ (val_one _).symm)
    have n₀ : (𝟙 _ ≫ psi hp τ hτ) ≫ (negT G T₀).left = (𝟙 _ ≫ (negT A T).left) ≫ psi hp τ hτ := by
      rw [Category.assoc, Category.assoc]
      exact congrArg _ (psi_lift hp τ hτ (psi_neg hp τ hτ)).symm
    rw [t (over_inv hp τ hτ hx), n₀] at q
    have a₁ := v _ (𝟙 _ ≫ (translT A x⁻¹).left) y J J' hJ hJ'
    have a₂ := u _ (𝟙 _) y J J' hJ hJ'
    have a₃ := v _ (𝟙 _ ≫ (negT A T).left) y J J' hJ hJ'
    have a₄ := u _ (𝟙 _ ≫ (translT A x⁻¹).left) y J J' hJ hJ'
    rw [(g _ (o₂ _ _)).2, (g _ (o₂ _ _)).2, one_zpow, one_zpow, _root_.one_mul, _root_.one_mul] at a₁ a₃ a₄
    rw [(g _ (o₁ _)).2, (g _ (o₁ _)).2, one_zpow, one_zpow, _root_.one_mul, _root_.one_mul] at a₂
    exact (congrArg₂ (· * ·) (congrArg₂ (· * ·) a₁ a₂) (congrArg₂ (fun p q => p * q⁻¹) a₃ a₄)).symm.trans q

end Move

section Pol

variable {S S' : Scheme.{0}} {P₀ : PolAV S} {P : PolAV S'} {f : S' ⟶ S} {φ : P.A.left ⟶ P₀.A.left}
  (hp : IsGrpPullback P.A P₀.A f φ) {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {w : LB.Iso P.L (P₀.L.pull φ)} {c : P.L.ι → P₀.L.ι}
  {ρ₀ : LB.Gen (P₀.L.pull (eSec P₀.A))} {ρ : LB.Gen (P.L.pull (eSec P.A))}

theorem polAVSectionInverseImage_chartwisePullback {θ₀ : P₀.L.Sec} {θ : P.L.Sec}
    (hθ : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) j k, φ (r z) ∈ P₀.L.U j → r z ∈ P.L.U k →
      gs (r ≫ φ) z _ (θ₀.f j) = (gw w r z j k).val * gs r z _ (θ.f k))
    {th₀ th} (h : SecRel hp τ hτ w th th₀) (H : IsPolAVSectionInverseImage P₀ T₀ θ₀ th₀) : IsPolAVSectionInverseImage P T θ th := by
  intro i hi
  refine fn_ext fun y hy => ?_
  obtain ⟨J', hJ', e⟩ := exists_good P.L P.isLB y (fun _ : Unit => 𝟙 _ ≫ (snd T P.A).left) (fun _ => i)
    (fun _ _ _ => rfl) (fun _ => hi hy)
  obtain ⟨J, hJ⟩ := exists_good' P₀.isLB y
  have q := h _ (𝟙 _) y J J' hJ hJ'
  have e₀ : (𝟙 _ ≫ psi hp τ hτ) ≫ (snd T₀ P₀.A).left = (𝟙 _ ≫ (snd T P.A).left) ≫ φ := by
    rw [Category.assoc, Category.assoc, psi_snd']
  have m₀ := hJ.mem (fun _ : Fin 1 => (snd T₀ P₀.A).left) (𝟙 _ ≫ psi hp τ hτ)
  rw [e₀] at m₀
  have q₁ := (sval_of (φ := fun _ : Fin 1 => (snd T₀ P₀.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th₀ _ y J
    (fun _ => J ((𝟙 _ ≫ (snd T P.A).left) ≫ φ)) (fun _ => congrArg J e₀)).symm.trans q
  have q₂ := (congrArg (gs _ y _) (H _ (LB.wchart_le _ _ _ 0))).symm.trans q₁
  have q₃ := (gs_appLE' _ _ _ _ _ _ m₀ _).symm.trans q₂
  rw [e₀, hθ _ _ y _ (J' (𝟙 _ ≫ (snd T P.A).left)) (hJ _) (hJ' _)] at q₃
  have q₄ := (Units.mul_right_inj _).1 (q₃.trans (congrArg (fun u => Units.val u * _) (zpow_one _)))
  refine (sval_of (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th _ y J'
    (fun _ => i) (fun _ => e ())).symm.trans (q₄.symm.trans ?_)
  rw [e ()]
  exact (gs_appLE' _ _ _ _ _ _ hy _).symm

theorem tr_move (hw : w.IsGen) (hc : Chartwise w c) (he : eSec P.A ≫ φ = f ≫ eSec P₀.A)
    (hρ : PMaps w (fun _ : PUnit => eSec P.A) (fun _ => eSec P₀.A) (fun _ => 1) ρ ρ₀ f) {m : ℕ}
    {th₀ th t₀ t} (h : SecRel hp τ hτ w th th₀) (ht : SecRel hp τ hτ w t t₀) {U₀ U}
    (hU : ∀ s₀ s₀' s s', SecRel hp τ hτ w s s₀ → SecRel hp τ hτ w s' s₀' →
      IsActOf P₀.A P₀.L ((m ^ 2 : ℕ) : ℤ) U₀ s₀ s₀' → IsActOf P.A P.L ((m ^ 2 : ℕ) : ℤ) U s s')
    (H : Tr P₀ ρ₀ m th₀ U₀ t₀) : Tr P ρ m th U t := by
  obtain ⟨α₀, s₀, hα₀, hn, h₁, h₂⟩ := H
  obtain ⟨α, hα, v⟩ := exists_genThrough₂ hp τ hτ hw P₀.isLB P.isLB (psi_pow hp τ hτ m) α₀ hα₀
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw P₀.isLB P.isLB s₀
  refine ⟨α, s, hα, corr_of_val P.isLB fun y J' hJ' => ?_,
    isTwistPull_move hp τ hτ P₀.isLB P.isLB (psi_pow hp τ hτ m) hα v h hs h₁, hU _ _ _ _ hs ht h₂⟩
  obtain ⟨J, hJ, g⟩ := exists_gauge hp P₀.isLB hc T.hom hJ'
  have o : ∀ q : T ⊗ P.A ⟶ P.A, ((𝟙 _ ≫ (ptSecT P.A (1 : T ⟶ P.A)).left) ≫ q.left) ≫ P.A.hom = T.hom := fun q => by
    rw [Category.id_comp, Category.assoc, Over.w, Over.w]
  have q := val_corr hJ hn (𝟙 _ ≫ τ)
  have q₁ := v _ (𝟙 _ ≫ (ptSecT P.A (1 : T ⟶ P.A)).left) y J J' hJ hJ'
  rw [(g _ (o _)).2, (g _ (o _)).2, one_zpow, one_zpow, _root_.one_mul, _root_.one_mul, Category.assoc,
    psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc] at q₁
  have q₂ := pmaps_val (fun _ => he) hρ (𝟙 _ ≫ T.hom) hJ hJ'
  rw [Fintype.prod_unique, (g _ (by
    rw [Category.id_comp, Category.assoc]
    exact (congrArg _ (Over.w η[P.A])).trans (Category.comp_id _))).2, one_zpow, _root_.one_mul] at q₂
  rw [val_pull hJ, val_rigT' _ _ _ _ _ _ _ _ hJ, Category.assoc _ τ T₀.hom, hτ, ← Category.assoc, q₁] at q
  rw [val_pull hJ', val_rigT' _ _ _ _ _ _ _ _ hJ']
  exact q.trans (congrArg (· ^ _) q₂)

theorem valR_sec_move (hc : Chartwise w c) {k : ℤ} {t₀ : LB.Sec (LPow P₀.A P₀.L k T₀)} {t : LB.Sec (LPow P.A P.L k T)}
    (ht : SecRel hp τ hτ w t t₀) {B : Type} [CommRing B] (y : Sp B ⟶ (T ⊗ P.A).left) (i : P.L.ι) :
    valR (y ≫ psi hp τ hτ) ((LPow P₀.A P₀.L k T₀).U fun _ => c i) (t₀.f fun _ => c i) =
      valR y ((LPow P.A P.L k T).U fun _ => i) (t.f fun _ => i) := by
  have e₀ : (y ≫ psi hp τ hτ) ≫ (snd T₀ P₀.A).left = (y ≫ (snd T P.A).left) ≫ φ := by
    rw [Category.assoc, Category.assoc, psi_snd']
  have hU : ∀ z, (y ≫ (snd T P.A).left) z ∈ P.L.U i ↔
      ((y ≫ psi hp τ hτ) ≫ (snd T₀ P₀.A).left) z ∈ P₀.L.U (c i) := fun z => by
    rw [e₀]; exact hc.1 _ _
  refine valR_congr (fun z => ⟨fun h => Set.mem_iInter.2 fun _ => (hU z).1 (Set.mem_iInter.1 h 0),
    fun h => Set.mem_iInter.2 fun _ => (hU z).2 (Set.mem_iInter.1 h 0)⟩) fun z hz => ?_
  obtain ⟨J', hJ', e⟩ := exists_good P.L P.isLB z (fun _ : Unit => y ≫ (snd T P.A).left) (fun _ => i)
    (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hz 0)
  obtain ⟨J, hJ, g⟩ := exists_gauge hp P₀.isLB hc ((y ≫ (snd T P.A).left) ≫ P.A.hom) hJ'
  have q := ht _ y z J J' hJ hJ'
  rw [(g _ rfl).2, one_zpow, Units.val_one, _root_.one_mul] at q
  exact (sval_of (φ := fun _ : Fin 1 => (snd T₀ P₀.A).left) (ε := fun _ => k) t₀ _ z J (fun _ => c i)
    (fun _ => by rw [e₀, (g _ rfl).1, e ()])).symm.trans (q.trans
    (sval_of (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => k) t _ z J' (fun _ => i) (fun _ => e ())))

theorem valR_rig_move (hc : Chartwise w c) (he : eSec P.A ≫ φ = f ≫ eSec P₀.A)
    (hρ : PMaps w (fun _ : PUnit => eSec P.A) (fun _ => eSec P₀.A) (fun _ => 1) ρ ρ₀ f)
    {B : Type} [CommRing B] (s : Sp B ⟶ S') (i : P.L.ι) :
    valR (s ≫ f) ((P₀.L.pull (eSec P₀.A)).U fun _ => c i) (ρ₀.s fun _ => c i).val =
      valR s ((P.L.pull (eSec P.A)).U fun _ => i) (ρ.s fun _ => i).val := by
  have hU : ∀ z, (s ≫ eSec P.A) z ∈ P.L.U i ↔ ((s ≫ f) ≫ eSec P₀.A) z ∈ P₀.L.U (c i) := fun z => by
    rw [Category.assoc, ← he]; exact hc.1 _ _
  have hU' : ∀ z, s z ∈ (P.L.pull (eSec P.A)).U (fun _ => i) ↔
      (s ≫ f) z ∈ (P₀.L.pull (eSec P₀.A)).U (fun _ => c i) := fun z =>
    ⟨fun h => mem_pull.2 ((hU z).1 (mem_pull.1 h)), fun h => mem_pull.2 ((hU z).2 (mem_pull.1 h))⟩
  refine valR_congr hU' fun z hz => ?_
  have hz' : (s ≫ eSec P.A) z ∈ P.L.U i := mem_pull.1 hz
  have q := hρ _ s z (fun _ => c i) (fun _ => i) (fun _ => (hc.1 _ _).1 hz') (fun _ => hz')
  rw [Fintype.prod_unique, hc.2 _ _ _ _ hz', one_zpow, _root_.one_mul] at q
  exact (gs_unit _ z _ ((hU' z).1 hz) _).trans ((congrArg Units.val q).trans (gs_unit _ z _ hz _).symm)

include hp in

theorem thJetT_move (hw : w.IsGen) (hc : Chartwise w c) (hs : Function.Surjective c)
    (he : eSec P.A ≫ φ = f ≫ eSec P₀.A)
    (hρ : PMaps w (fun _ : PUnit => eSec P.A) (fun _ => eSec P₀.A) (fun _ => 1) ρ ρ₀ f) {θ₀ : P₀.L.Sec} {θ : P.L.Sec}
    (hθ : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) j k, φ (r z) ∈ P₀.L.U j → r z ∈ P.L.U k →
      gs (r ≫ φ) z _ (θ₀.f j) = (gw w r z j k).val * gs r z _ (θ.f k))
    {B : Type} [CommRing B] {s : Sp B ⟶ S'} {s₀ : Sp B ⟶ S} (e : s₀ = s ≫ f) {m : ℕ} {th₀} {I : Type}
    {pt₀ : I → (Over.mk s₀ ⟶ P₀.A)} {pt : I → (Over.mk s ⟶ P.A)} (hpt : ∀ i, (pt₀ i).left = (pt i).left ≫ φ) {g : ℕ}
    {y₀ : Fin g → (Sp (DualNumber B) ⟶ (Over.mk s₀ ⊗ P₀.A).left)}
    {y : Fin g → (Sp (DualNumber B) ⟶ (Over.mk s ⊗ P.A).left)}
    (hy₁ : ∀ j, y₀ j ≫ (fst (Over.mk s₀) P₀.A).left = y j ≫ (fst (Over.mk s) P.A).left)
    (hy₂ : ∀ j, y₀ j ≫ (snd (Over.mk s₀) P₀.A).left = y j ≫ (snd (Over.mk s) P.A).left ≫ φ) {ϑ J}
    (H₁ : IsPolAVSectionInverseImage P₀ (Over.mk s₀) θ₀ th₀) (H : ThJetT P₀ ρ₀ m s₀ th₀ pt₀ y₀ ϑ J) :
    ∃ th, IsPolAVSectionInverseImage P (Over.mk s) θ th ∧ ThJetT P ρ m s th pt y ϑ J := by
  subst e
  have := P.isAb.comm
  let τ : (Over.mk s).left ⟶ (Over.mk (s ≫ f)).left := 𝟙 (Sp B)
  have hτ : τ ≫ (Over.mk (s ≫ f)).hom = (Over.mk s).hom ≫ f := Category.id_comp _
  obtain ⟨U₀, t₀, i₀, d, h₁, h₂, h₃⟩ := H
  obtain ⟨i, rfl⟩ := hs i₀
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw P₀.isLB P.isLB th₀
  choose t ht using fun a => exists_secRel hp τ hτ hw P₀.isLB P.isLB (t₀ a)
  choose U hU hU' using fun a => symLift_chartwise hp τ hτ hw hc P₀.isLB P.isLB
    ((Category.id_comp _).trans (hpt a)) (h₁ a).1
  have ey : ∀ j, y₀ j = y j ≫ psi hp τ hτ := fun j => psi_ext
    (by rw [Category.assoc, psi_fst', hy₁]; exact congrArg _ (Category.comp_id _).symm)
    (by rw [Category.assoc, psi_snd', hy₂])
  refine ⟨th, polAVSectionInverseImage_chartwisePullback hp τ hτ hθ hth H₁, U, t, i, d,
    fun a => ⟨hU a, tr_move hp τ hτ hw hc he hρ hth (ht a) (hU' a) (h₁ a).2⟩, fun z hz => ?_, fun a j => ?_⟩
  · have q : ((s ≫ f) ≫ eSec P₀.A) z ∈ P₀.L.U (c i) := h₂ hz
    rw [Category.assoc, ← he] at q
    exact (hc.1 _ _).2 q
  · have q := h₃ a j
    rw [ey, valR_sec_move hp τ hτ hc (ht a), valR_rig_move hc he hρ] at q
    exact q

include hp in
theorem exists_ptEquiv {Z : Scheme.{0}} {s : Z ⟶ S'} {s₀ : Z ⟶ S} (e : s₀ = s ≫ f) :
    ∃ io : (Over.mk s₀ ⟶ P₀.A) ≃* (Over.mk s ⟶ P.A), ∀ a, a.left = (io a).left ≫ φ := by
  subst e
  have hb : Function.Bijective (pushHom hp (Over.mk s)) :=
    ⟨fun a b h => Over.OverMorphism.ext (hp.1.hom_ext (congrArg (fun q => q.left) h)
      ((Over.w a).trans (Over.w b).symm)),
    fun a => ⟨Over.homMk (hp.1.lift a.left s (Over.w a)) (hp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hp.1.lift_fst _ _ _)⟩⟩
  exact ⟨(MulEquiv.ofBijective _ hb).symm, fun a =>
    (congrArg (fun q => q.left) ((MulEquiv.ofBijective _ hb).apply_symm_apply a)).symm⟩

include hp in
theorem weilIs_move (hw : w.IsGen) {Z : Scheme.{0}} {s : Z ⟶ S'} {s₀ : Z ⟶ S} (e : s₀ = s ≫ f) (k : ℤ)
    {a₀ b₀ : Over.mk s₀ ⟶ P₀.A} {a b : Over.mk s ⟶ P.A} (ha : a₀.left = a.left ≫ φ) (hb : b₀.left = b.left ≫ φ)
    (z : Γ(Z, ⊤)ˣ) (H : WeilIs P.A P.L k a b z) : WeilIs P₀.A P₀.L k a₀ b₀ z := by
  subst e
  have := P.isAb.comm
  exact (weilIs_grpPullback_of_comm' _ _ P₀.A P.A f φ P₀.L P.L P₀.isLB P.isLB hp ⟨w, hw⟩ (Over.mk s) k a b a₀ b₀ z
    ha hb).1 H

end Pol

theorem exists_keyPB_chartwise {R R' : Type} [CommRing R] [CommRing R'] (x : KeyIn R) (f : R →+* R') :
    ∃ (x' : KeyIn R') (hg : x'.P.g = x.P.g) (φ : x'.P.A.left ⟶ x.P.A.left) (w : LB.Iso x'.P.L (x.P.L.pull φ))
      (c : x'.P.L.ι → x.P.L.ι), KeyPB x' x f ∧ IsGrpPullback x'.P.A x.P.A (spMap f) φ ∧ w.IsGen ∧ Chartwise w c ∧
      Function.Surjective c ∧ eSec x'.P.A ≫ φ = spMap f ≫ eSec x.P.A ∧
      PMaps w (fun _ : PUnit => eSec x'.P.A) (fun _ => eSec x.P.A) (fun _ => 1) x'.rig x.rig (spMap f) ∧
      (∀ (Z : Scheme.{0}) (r : Z ⟶ x'.P.A.left) (z : Z) j k, φ (r z) ∈ x.P.L.U j → r z ∈ x'.P.L.U k →
        gs (r ≫ φ) z _ (x.th.f j) = (gw w r z j k).val * gs r z _ (x'.th.f k)) ∧
      ∀ i, (x'.v (i.cast hg.symm)).left ≫ φ = spMap (dualMap f) ≫ (x.v i).left := by
  have h := isGrpPullback_pullback x.P.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj x.P.A).left ⟶ x.P.A.left := pullback.fst x.P.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := pull_isLB x.P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R') :=
    { A := (Over.pullback (spMap f)).obj x.P.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) x.P.A x.P.isAb
      g := x.P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 x.P.smoothDim
      L := x.P.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h x.P.rigid
      sym := PolBaseChange.sym_pull h x.P.sym
      ample := relAmple_pull h.1 x.P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) x.P.ample
      ktriv := kTriv_pull h x.P.isLB hL' hw x.P.ktriv }
  have he : eSec P'.A ≫ φ = spMap f ≫ eSec x.P.A := PolBaseChange.eSec_comm h
  have hr : (rigPullOf φ (spMap f) he x.P.L x.rig).IsGen :=
    Out.LBxP.isGen_pullAlong x.P.L φ (spMap f) (fun _ : PUnit => eSec x.P.A) (fun _ => 1) (fun _ => eSec P'.A)
      (fun _ => he) x.rig x.rig_gen
  obtain ⟨th', hth'⟩ := sec_pull_down hw x.P.isLB hL' x.th
  have c₁ : IsCommMonObj x.P.A := x.P.isAb.comm
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  obtain ⟨v', hb', hv'⟩ := exists_isLieBasis_baseChange R R' f x.P.A P'.A φ h x.P.isAb.smooth x.P.g x.v x.basis
  have hm : LB.Gen.Maps (LB.linCombIso (Geo.Tor.idIso (x.P.L.pull φ)) (K := PUnit) (fun _ => eSec P'.A) (fun _ => 1))
      (rigPullOf φ (spMap f) he x.P.L x.rig) (rigPullOf φ (spMap f) he x.P.L x.rig) := fun p => hr p.1 p.2
  refine ⟨⟨P', x.g_pos, _, hr, th', fun s => ?_, v', hb'⟩, rfl, φ, Geo.Tor.idIso _, fun i => i PUnit.unit,
    ⟨φ, he, Geo.Tor.idIso _, rfl, Chart.dualMapR f, h, idIso_isGen hL', hm,
      KeyPow.appLE_eq_of_stalk _ x.th th' (hth' _ (𝟙 _)), fun a => ?_, ?_, hv'⟩, h, idIso_isGen hL',
    chartwise_id x.P.isLB φ, fun i => ⟨fun _ => i, rfl⟩, he,
    (maps_iff _ _ _ _ _ _ _ _ (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).1 hm, hth', hv'⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne (spMap f s)
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
    have u₁ : IsUnit (gs φ y _ (x.th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
    have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end GlobalTheory.MBLow.JetBC

open GlobalTheory.MBLow.JetBC in

theorem GlobalTheory.MBLow.exists_keyPB_thJet : ∀ (K C : Type) [Field K] [Field C] (f : K →+* C) (x : KeyIn K), ∃ (xC : KeyIn C) (hg : xC.P.g = x.P.g) (io : (Over.mk (spMap f) ⟶ x.P.A) ≃* (baseOver (Sp C) ⟶ xC.P.A)), KeyPB xC x f ∧ (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs xC.P.A xC.P.L k (io a) (io b) z → WeilIs x.P.A x.P.L k a b z) ∧ ∀ (m : ℕ) (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap f)))) (I : Type) (pt : I → (Over.mk (spMap f) ⟶ x.P.A)) (y : Fin x.P.g → (Sp (DualNumber C) ⟶ (Over.mk (spMap f) ⊗ x.P.A).left)) (ϑ : I → C) (J : I → Fin x.P.g → C), IsPolAVSectionInverseImage x.P (Over.mk (spMap f)) x.th th → (∀ j, y j ≫ (fst (Over.mk (spMap f)) x.P.A).left = spMap (algebraMap C (DualNumber C)) ∧ y j ≫ (snd (Over.mk (spMap f)) x.P.A).left = spMap (dualMap f) ≫ (x.v j).left) → ThJetT x.P x.rig m (spMap f) th pt y ϑ J → ThJet xC hg m (fun i => io (pt i)) ϑ J := by
  intro K C _ _ f x
  obtain ⟨xC, hg, φ, w, c, hK, hp, hw, hc, hs, he, hρ, hθ, hv⟩ := exists_keyPB_chartwise x f
  have e : spMap f = 𝟙 (Sp C) ≫ spMap f := (Category.id_comp _).symm
  obtain ⟨io, hio⟩ := exists_ptEquiv hp e
  refine ⟨xC, hg, io, hK, fun k a b z H => weilIs_move hp hw e k (hio a) (hio b) z H,
    fun m th I pt y ϑ J H₁ hy H => thJetT_move hp hw hc hs he hρ hθ e (fun i => hio (pt i)) (fun j => ?_) (fun j => ?_) H₁ H⟩
  · rw [(hy j).1, epsLift, ← Over.comp_left, lift_fst]
    rfl
  · rw [(hy j).2, epsLift, ← Category.assoc, ← Over.comp_left, lift_snd, hv]

end
