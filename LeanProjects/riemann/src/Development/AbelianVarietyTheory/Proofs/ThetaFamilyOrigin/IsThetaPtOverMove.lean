import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaPtMove

open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift

section Value

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {n : ℤ} {T : Over S}
  {s : LB.Sec (LPow A L n T)} {x : T ⟶ A}
  {ρ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => n))} {c : Γ(T.left, ⊤)}

omit [GrpObj A] in
theorem ptSecT_snd (x : T ⟶ A) : (ptSecT A x).left ≫ (snd T A).left = x.left := by
  rw [← Over.comp_left, ptSecT, lift_snd]

omit [GrpObj A] in
theorem ptSecT_fst (x : T ⟶ A) : (ptSecT A x).left ≫ (fst T A).left = 𝟙 _ := by
  rw [← Over.comp_left, ptSecT, lift_fst, Over.id_left]

theorem sv_of_isValueAt (h : IsValueAt A L n s x ρ c) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J}
    (hJ : Good L z J) : VVRank.sv A s (r ≫ (ptSecT A x).left) z J = gs r z ⊤ c * (val ρ r z J).val := by
  have hz := hJ.mem (fun _ : Fin 1 => x.left) r
  refine (sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => n) s _ z J (fun _ => J (r ≫ x.left))
    (fun _ => by rw [Category.assoc, ptSecT_snd])).trans ?_
  exact ((gs_res r z _ hz _).trans (gs_pull r (ptSecT A x).left z _ (val_le A L x _ hz) _)).symm.trans
    ((congrArg (gs r z _) (h _)).trans ((gs_mul r z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_res r z le_top hz c) (gs_unit r z _ hz _))))

theorem isValueAt_of_sv (hL : L.IsLB) (h : ∀ y J, Good L y J →
    VVRank.sv A s (𝟙 _ ≫ (ptSecT A x).left) y J = gs (𝟙 _) y ⊤ c * (val ρ (𝟙 _) y J).val) :
    IsValueAt A L n s x ρ c := fun j => fn_ext fun y hy => by
  obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun _ : Fin 1 => x.left) j
    (fun a b _ => congrArg j (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 hy k)
  have q := h y J hJ
  rw [val_of ρ _ y J j (fun k => by rw [Category.id_comp]; exact e k)] at q
  have q' := (sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => n) s (𝟙 _ ≫ (ptSecT A x).left) y J j
    (fun k => by rw [Category.id_comp, ptSecT_snd]; exact e k)).symm.trans q
  exact ((gs_res _ y _ hy _).trans (gs_pull _ (ptSecT A x).left y _ (val_le A L x _ hy) _)).trans
    (q'.trans ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hy c) (gs_unit _ y _ hy _))).symm)

end Value

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)

def psi : (T ⊗ A).left ⟶ (T₀ ⊗ G).left := (psiO hp τ hτ).left

theorem psi_fst' : psi hp τ hτ ≫ (fst T₀ G).left = (fst T A).left ≫ τ := psi_fst hp τ hτ

theorem psi_snd' : psi hp τ hτ ≫ (snd T₀ G).left = (snd T A).left ≫ φ := psi_snd hp τ hτ

theorem psi_tr' (x : T ⟶ A) (x₀ : T₀ ⟶ G) (hx : τ ≫ x₀.left = x.left ≫ φ) :
    psi hp τ hτ ≫ (translPt G x₀).left = (translPt A x).left ≫ φ := psi_tr hp τ hτ x x₀ hx

section Points

include hp hτ

theorem over_iff (x : T ⟶ A) (x₀ : T₀ ⟶ G) : τ ≫ x₀.left = x.left ≫ φ ↔
    preHom (Over.homMk τ hτ : Over.mk (T.hom ≫ f) ⟶ T₀) x₀ = pushHom hp T x :=
  ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (fun q => q.left) h⟩

theorem over_one : τ ≫ (1 : T₀ ⟶ G).left = (1 : T ⟶ A).left ≫ φ :=
  (over_iff hp τ hτ _ _).2 (by rw [map_one, map_one])

theorem over_mul {x y : T ⟶ A} {x₀ y₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hy : τ ≫ y₀.left = y.left ≫ φ) :
    τ ≫ (x₀ * y₀).left = (x * y).left ≫ φ :=
  (over_iff hp τ hτ _ _).2 (by rw [map_mul, map_mul, (over_iff hp τ hτ _ _).1 hx, (over_iff hp τ hτ _ _).1 hy])

theorem over_pow {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (n : ℕ) :
    τ ≫ (x₀ ^ n).left = (x ^ n).left ≫ φ :=
  (over_iff hp τ hτ _ _).2 (by rw [map_pow, map_pow, (over_iff hp τ hτ _ _).1 hx])

theorem over_inv {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) :
    τ ≫ (x₀⁻¹).left = (x⁻¹).left ≫ φ :=
  (over_iff hp τ hτ _ _).2 (by rw [map_inv, map_inv, (over_iff hp τ hτ _ _).1 hx])

omit [GrpObj G] [GrpObj A] hp hτ in
theorem psi_ext {Z : Scheme.{0}} {a b : Z ⟶ (T₀ ⊗ G).left} (h₁ : a ≫ (fst T₀ G).left = b ≫ (fst T₀ G).left)
    (h₂ : a ≫ (snd T₀ G).left = b ≫ (snd T₀ G).left) : a = b :=
  pullback.hom_ext (f := T₀.hom) (g := G.hom) h₁ h₂

theorem psi_lift {m : T ⊗ A ⟶ A} {m₀ : T₀ ⊗ G ⟶ G} (h : psi hp τ hτ ≫ m₀.left = m.left ≫ φ) :
    (lift (fst T A) m).left ≫ psi hp τ hτ = psi hp τ hτ ≫ (lift (fst T₀ G) m₀).left := by
  have a₁ : (lift (fst T₀ G) m₀).left ≫ (fst T₀ G).left = (fst T₀ G).left := by rw [← Over.comp_left, lift_fst]
  have a₂ : (lift (fst T₀ G) m₀).left ≫ (snd T₀ G).left = m₀.left := by rw [← Over.comp_left, lift_snd]
  refine psi_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, psi_fst', a₁, psi_fst', ← Category.assoc, ← Over.comp_left, lift_fst]
  · rw [Category.assoc, Category.assoc, psi_snd', a₂, h, ← Category.assoc, ← Over.comp_left, lift_snd]

theorem psi_pow (n : ℕ) : psi hp τ hτ ≫ (snd T₀ G ^ n).left = (snd T A ^ n).left ≫ φ :=
  over_pow hp (T := T ⊗ A) (T₀ := T₀ ⊗ G) _ (Over.w (psiO hp τ hτ)) (psi_snd' hp τ hτ) n

theorem psi_neg : psi hp τ hτ ≫ (snd T₀ G ≫ (GrpObj.inv : G ⟶ G)).left =
    (snd T A ≫ (GrpObj.inv : A ⟶ A)).left ≫ φ :=
  over_inv hp (T := T ⊗ A) (T₀ := T₀ ⊗ G) _ (Over.w (psiO hp τ hτ)) (psi_snd' hp τ hτ)

theorem psi_ptSec {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) :
    (ptSecT A x).left ≫ psi hp τ hτ = τ ≫ (ptSecT G x₀).left := by
  refine psi_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, psi_fst', ptSecT_fst, ← Category.assoc, ptSecT_fst, Category.id_comp,
      Category.comp_id]
  · rw [Category.assoc, Category.assoc, psi_snd', ptSecT_snd, ← Category.assoc, ptSecT_snd, hx]

end Points

variable {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

def GenThrough (w : LB.Iso L₁ (L₀.pull φ)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} (ψ' : K → (Y' ⟶ A.left))
    (ψ : K → (Y ⟶ G.left)) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L₁ ψ' ε)) (t : LB.Gen (LB.LinComb L₀ ψ ε))
    (h : Y' ⟶ Y) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J J', Good L₀ z J → Good L₁ z J' →
    val t (r ≫ h) z J = (∏ k, wVal w z J J' (r ≫ ψ' k) ^ ε k) * val a r z J'

def SecRel (w : LB.Iso L₁ (L₀.pull φ)) {a : ℤ} (s : LB.Sec (LPow A L₁ a T)) (s₀ : LB.Sec (LPow G L₀ a T₀)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
    VVRank.sv G s₀ (r ≫ psi hp τ hτ) z J =
      (wVal w z J J' (r ≫ (snd T A).left) ^ a).val * VVRank.sv A s r z J'

theorem exists_secRel (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} (s₀ : LB.Sec (LPow G L₀ a T₀)) :
    ∃ s, SecRel hp τ hτ w s s₀ := by
  have e : ∀ _ : Fin 1, (snd T A).left ≫ φ = psi hp τ hτ ≫ (snd T₀ G).left := fun _ => (psi_snd' hp τ hτ).symm
  obtain ⟨s, hs⟩ := exists_secThrough (φ' := fun _ : Fin 1 => (snd T A).left) (φ := fun _ => (snd T₀ G).left)
    (ε := fun _ => a) hw hL₀ hL₁ e s₀
  refine ⟨s, fun Z r z J J' hJ hJ' => (hs.sval e r hJ hJ').trans ?_⟩
  rw [Fin.prod_univ_one]

theorem exists_genThrough₂ (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a b : ℤ} {m : T ⊗ A ⟶ A}
    {m₀ : T₀ ⊗ G ⟶ G} (h : psi hp τ hτ ≫ m₀.left = m.left ≫ φ)
    (α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, m₀.left] ![a, b])) (hα₀ : α₀.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, m.left] ![a, b]), α.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
        val α₀ (r ≫ psi hp τ hτ) z J =
          (wVal w z J J' (r ≫ (snd T A).left) ^ a * wVal w z J J' (r ≫ m.left) ^ b) * val α r z J' := by
  obtain ⟨α, hα, H⟩ := exists_gen_through (φ' := ![(snd T A).left, m.left]) (h := psi hp τ hτ) hw hL₀ hL₁
    (fun i => by
      fin_cases i
      · exact (psi_snd' hp τ hτ).symm
      · exact h.symm) α₀ hα₀
  refine ⟨α, hα, fun Z r z J J' hJ hJ' => (H Z r z J J' hJ hJ').trans ?_⟩
  rw [Fin.prod_univ_two]
  rfl

theorem isTwistPull_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a b : ℤ} {m : T ⊗ A ⟶ A}
    {m₀ : T₀ ⊗ G ⟶ G} (h : psi hp τ hτ ≫ m₀.left = m.left ≫ φ)
    {α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, m₀.left] ![a, -b])}
    {α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen)
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
        val α₀ (r ≫ psi hp τ hτ) z J =
          (wVal w z J J' (r ≫ (snd T A).left) ^ a * wVal w z J J' (r ≫ m.left) ^ (-b)) * val α r z J')
    {s₀ s₀' s s'} (hs : SecRel hp τ hτ w s s₀) (hs' : SecRel hp τ hτ w s' s₀')
    (H₀ : IsTwistPull G L₀ (lift (fst T₀ G) m₀) m₀ (lift_snd _ _) a b α₀ s₀ s₀') :
    IsTwistPull A L₁ (lift (fst T A) m) m (lift_snd _ _) a b α s s' := by
  refine VVRank.isTwistPull_of_sv A hL₁ hα fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL₀ y
  have q := VVRank.sv_of_isTwistPull G H₀ (𝟙 _ ≫ psi hp τ hτ) y hJ
  have e : (𝟙 _ ≫ (lift (fst T A) m).left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by
    rw [Category.assoc, ← Over.comp_left, lift_snd]
  rw [hs' _ _ _ _ _ hJ hJ', H _ _ _ _ _ hJ hJ', Category.assoc, ← psi_lift hp τ hτ h, ← Category.assoc,
    hs _ _ _ _ _ hJ hJ', e, zpow_neg] at q
  refine (Units.mul_right_inj _).1 (q.trans ?_)
  simp only [Units.val_mul]
  rw [mul_right_comm _ _ (val α _ y J').val, _root_.mul_assoc, Units.inv_mul_cancel_left, _root_.mul_assoc]

theorem isValueAt_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {x : T ⟶ A} {x₀ : T₀ ⟶ G}
    (hx : τ ≫ x₀.left = x.left ≫ φ)
    {ρ₀ : LB.Gen (LB.LinComb L₀ (Y := T₀.left) (K := Fin 1) (fun _ => x₀.left) (fun _ => a))}
    {ρ : LB.Gen (LB.LinComb L₁ (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))}
    (H : GenThrough w _ _ _ ρ ρ₀ τ) {s₀ s} (hs : SecRel hp τ hτ w s s₀) {c : Γ(T₀.left, ⊤)}
    (H₀ : IsValueAt G L₀ a s₀ x₀ ρ₀ c) : IsValueAt A L₁ a s x ρ (τ.appTop.hom c) := by
  refine isValueAt_of_sv hL₁ fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL₀ y
  have q := sv_of_isValueAt H₀ (𝟙 _ ≫ τ) y hJ
  rw [H _ _ _ _ _ hJ hJ', Category.assoc, ← psi_ptSec hp τ hτ hx, ← Category.assoc, hs _ _ _ _ _ hJ hJ',
    Category.assoc, ptSecT_snd, Fin.prod_univ_one, Units.val_mul, mul_left_comm] at q
  exact ((Units.mul_right_inj _).1 q).trans (congrArg (· * _) (gs_pull (𝟙 _) τ y ⊤ trivial c).symm)

theorem symLift_move [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {k : ℤ} {n : ℕ} {x : T ⟶ A}
    {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x ^ n = 1) {θ₀ : ThetaGrp G L₀ k T₀}
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
  have t₁ : ∀ y : T ⟶ A, (𝟙 _ ≫ (translT A y).left) ≫ (snd T A).left = (translPt A y).left := fun y => by
    rw [Category.id_comp, ThetaAct.translT_snd]
  have t₂ : ∀ y : T ⟶ A, (𝟙 _ ≫ (translT A y).left) ≫ (translPt A x).left = (translPt A (x * y)).left := fun y => by
    rw [Category.id_comp, ← Over.comp_left, ThetaAct.translT_translPt]
  refine ⟨θ, ⟨rfl, corr_of_val hL₁ fun y J' hJ' => ?_, ν, hν, corr_of_val hL₁ fun y J' hJ' => ?_⟩,
    fun s₀ s₀' s s' h h' H => isTwistPull_move hp τ hτ hL₀ hL₁ (psi_tr' hp τ hτ x _ hx) ha v h h' H⟩
  · obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    have q := val_corr hJ hpow (𝟙 _ ≫ psi hp τ hτ)
    rw [val_powGen _ _ _ hJ, val_one] at q
    rw [val_powGen _ _ _ hJ', val_one]
    let F : ℕ → ((T ⊗ A).left.presheaf.stalk y)ˣ := fun i => wVal w y J J' (translPt A (x ^ i)).left ^ k
    have e : ∀ i : ℕ, tval θ₀ ((𝟙 _ ≫ psi hp τ hτ) ≫ (translT G (θ₀.pt ^ i)).left) y J =
        F i / F (i + 1) * tval θ (𝟙 _ ≫ (translT A (x ^ i)).left) y J' := fun i => by
      rw [t (over_pow hp τ hτ hx i)]
      refine (v _ _ _ _ _ hJ hJ').trans ?_
      rw [t₁, t₂, ← pow_succ', zpow_neg, div_eq_mul_inv]
      rfl
    have e₀ : ∏ i : Fin n, F i / F (i + 1) = 1 := by
      rw [Fin.prod_univ_eq_prod_range (fun i => F i / F (i + 1)), Finset.prod_range_div', div_eq_one]
      simp only [F, hn, pow_zero]
    simp only [e, Finset.prod_mul_distrib, e₀, _root_.one_mul] at q
    exact q
  · obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    have q := val_corr hJ hs (𝟙 _ ≫ psi hp τ hτ)
    rw [val_symGen _ _ _ hJ, val_one] at q
    refine (val_symGen θ ν _ hJ').trans (Eq.trans ?_ (val_one _).symm)
    have n₀ : (𝟙 _ ≫ psi hp τ hτ) ≫ (negT G T₀).left = (𝟙 _ ≫ (negT A T).left) ≫ psi hp τ hτ := by
      rw [Category.assoc, Category.assoc]
      exact congrArg _ (psi_lift hp τ hτ (psi_neg hp τ hτ)).symm
    have n₁ : (𝟙 _ ≫ (negT A T).left) ≫ (snd T A).left = 𝟙 _ ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
      rw [Category.assoc, ← Over.comp_left, negT, lift_snd]
    have n₂ : (𝟙 _ ≫ (translT A x⁻¹).left) ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left =
        (𝟙 _ ≫ (negT A T).left) ≫ (translPt A x).left := by
      rw [Category.id_comp, Category.id_comp, ← Over.comp_left, ← Over.comp_left]
      congr 1
      show translT A x⁻¹ ≫ (snd T A)⁻¹ = negT A T ≫ ((fst T A ≫ x) * snd T A)
      rw [GrpObj.comp_inv, MonObj.comp_mul, translT, negT, lift_snd, lift_snd, lift_fst_assoc]
      show ((fst T A ≫ x⁻¹) * snd T A)⁻¹ = (fst T A ≫ x) * (snd T A)⁻¹
      rw [mul_inv, GrpObj.comp_inv, inv_inv]
    have n₃ : (translPt A (x * x⁻¹)).left = 𝟙 _ ≫ (snd T A).left := by
      rw [mul_inv_cancel, ThetaAct.translPt_one, Category.id_comp]
    rw [t (over_inv hp τ hτ hx), n₀] at q
    have a₁ := v _ (𝟙 _ ≫ (translT A x⁻¹).left) y J J' hJ hJ'
    have a₂ := u _ (𝟙 _) y J J' hJ hJ'
    have a₃ := v _ (𝟙 _ ≫ (negT A T).left) y J J' hJ hJ'
    have a₄ := u _ (𝟙 _ ≫ (translT A x⁻¹).left) y J J' hJ hJ'
    rw [t₂, n₃] at a₁
    rw [n₁] at a₃
    rw [n₂] at a₄
    have q' := (congrArg₂ (· * ·) (congrArg₂ (· * ·) a₁ a₂) (congrArg₂ (fun p q => p * q⁻¹) a₃ a₄)).symm.trans q
    refine Eq.trans ?_ q'
    have key : ∀ {U : Type} [CommGroup U] (p₁ p₂ p₃ p₄ a b c d : U), (a * b) * (c * d⁻¹) =
        (p₁ * p₂⁻¹ * a * (p₂ * p₃⁻¹ * b)) * (p₃ * p₄⁻¹ * c * (p₁ * p₄⁻¹ * d)⁻¹) := fun p₁ p₂ p₃ p₄ a b c d => by
      apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
    simp only [zpow_neg]
    exact key _ _ _ _ _ _ _ _

theorem exists_secRel_up [IsIso τ] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ}
    (s : LB.Sec (LPow A L₁ a T)) : ∃ s₀, SecRel hp τ hτ w s s₀ := by
  obtain ⟨χ, h₁, h₂⟩ := WeilPull.exists_psi_inv hp τ hτ
  obtain ⟨t, ht⟩ := exists_sec_up ((isGen_iff w).1 hw) hL₀ hL₁ (φ' := fun _ : Fin 1 => (snd T A).left)
    (ε := fun _ => a) s
  have h₁' : psi hp τ hτ ≫ χ = 𝟙 _ := h₁
  have h₂' : χ ≫ psi hp τ hτ = 𝟙 _ := h₂
  have e₀ : χ ≫ (snd T A).left ≫ φ = (snd T₀ G).left := by
    rw [← psi_snd' hp τ hτ, ← Category.assoc, h₂', Category.id_comp]
  refine ⟨VVRank.pullTo (φ' := fun _ : Fin 1 => (snd T₀ G).left) t χ fun _ => e₀, fun Z r z J J' hJ hJ' => ?_⟩
  refine (VVRank.sval_pullTo _ _ _ _ z hJ).trans ?_
  rw [Category.assoc, h₁', Category.comp_id]
  refine (ht Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
  simp only [pw, wVal, Fin.prod_univ_one, Category.assoc]

theorem sv_of_eq_mul {L : LB A.left} {a : ℤ} {s t : LB.Sec (LPow A L a T)} {c : Γ(T.left, ⊤)}
    (h : ∀ j, s.f j = liftFun A _ c * t.f j) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    VVRank.sv A s r z J = gs (r ≫ (fst T A).left) z ⊤ c * VVRank.sv A t r z J := by
  have e : SecM.ofSec A s = c • SecM.ofSec A t := Subtype.ext (funext h)
  exact (congrArg (fun q => ThetaAct.sv q r z J) e).trans (ThetaAct.sv_smul c _ r z hJ)

theorem isGenSec_move (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {B : Over S} (σ : T.left ⟶ B.left)
    [IsIso σ] (β : B ⟶ T₀) (hβ : σ ≫ β.left = τ) {th : LB.Sec (LPow A L₁ a T)} {th₀ : LB.Sec (LPow G L₀ a T₀)}
    (h : SecRel hp τ hτ w th th₀) (hg : IsGenSec G L₀ a (VVRank.pullS G a β th₀)) : IsGenSec A L₁ a th := by
  intro s
  have hσ : σ ≫ B.hom = T.hom ≫ f := by rw [← Over.w β, ← Category.assoc, hβ, hτ]
  obtain ⟨s₀, hs⟩ := exists_secRel_up hp σ hσ hw hL₀ hL₁ s
  obtain ⟨c, hc⟩ := hg s₀
  have e : psi hp σ hσ ≫ (β ▷ G).left = psi hp τ hτ := by
    refine psi_ext ?_ ?_
    · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst', psi_fst',
        Category.assoc, hβ]
    · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', psi_snd']
  have key : SecM.ofSec A s = σ.appTop.hom c • SecM.ofSec A th := ThetaAct.sv_ext hL₁ fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    have q := sv_of_eq_mul hc (𝟙 _ ≫ psi hp σ hσ) y hJ
    rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, Category.assoc (𝟙 _) _ (β ▷ G).left, e, hs _ _ _ _ _ hJ hJ',
      h _ _ _ _ _ hJ hJ', mul_left_comm, Category.assoc (𝟙 _) _ (fst B G).left, psi_fst', ← Category.assoc] at q
    refine Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ').symm
    exact ((Units.mul_right_inj _).1 q).trans (congrArg (· * _) (gs_pull _ σ y ⊤ trivial c).symm)
  exact ⟨σ.appTop.hom c, fun j => congrArg (fun q => q.1 j) key⟩

theorem isThetaPtOver_move {P₀ : PolAV S} {P : PolAV S'} {φ : P.A.left ⟶ P₀.A.left}
    (hp : IsGrpPullback P.A P₀.A f φ) (hw : LBIso P.L (P₀.L.pull φ)) {B : Over S} (σ : T.left ⟶ B.left) [IsIso σ]
    (β : B ⟶ T₀) (hβ : σ ≫ β.left = τ) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
    (hg : ∀ th₀, IsGenSec P₀.A P₀.L 1 th₀ → IsGenSec P₀.A P₀.L 1 (VVRank.pullS P₀.A 1 β th₀))
    {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {x₀ : I → (T₀ ⟶ P₀.A)} (hx : ∀ i, τ ≫ (x₀ i).left = (x i).left ≫ φ)
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {v₀ : I → Γ(T₀.left, ⊤)} (H : IsThetaPtOver P₀ k x₀ v₀) :
    IsThetaPtOver P k x (fun i => τ.appTop.hom (v₀ i)) := by
  obtain ⟨w, hw⟩ := hw
  have hL₀ := P₀.isLB
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨th₀, s₀, α₀, ρ₀, U₀, t₀, c₀, u₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := H
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ th₀
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  choose t ht using fun i => exists_secRel hp τ hτ hw hL₀ hL₁ (t₀ i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ k) α₀ h₂
  obtain ⟨ρ, hρ, vρ⟩ := exists_gen_through (φ' := fun _ : Fin 1 => (1 : T ⟶ P.A).left) (h := τ) hw hL₀ hL₁
    (fun _ => (over_one hp τ hτ).symm) ρ₀ h₃
  choose U hU hU' using fun i => symLift_move hp τ hτ hw hL₀ hL₁ (hx i) (hk i) (h₅ i)
  refine ⟨th, s, α, ρ, U, t, fun i => τ.appTop.hom (c₀ i), Units.map τ.appTop.hom.toMonoidHom u₀,
    isGenSec_move hp τ hτ hw hL₀ hL₁ σ β hβ hth (hg _ h₁), hα, hρ,
    isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ k) hα vα hth hs h₄, hU,
    fun i => hU' i _ _ _ _ hs (ht i) (h₆ i),
    fun i => isValueAt_move hp τ hτ hL₀ hL₁ (over_one hp τ hτ) vρ (ht i) (h₇ i), fun i => ?_⟩
  exact (congrArg τ.appTop.hom (h₈ i)).trans (map_mul _ _ _)

theorem isGenSec_pullS (hS : SecBaseChangeSt) [IsLocallyNoetherian S] [Subsingleton S] (p : S) (P : PolAV S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) ⊤).left)
    (th : LB.Sec (LPow P.A P.L 1 (overRes (T := baseOver S) ⊤))) (h : IsGenSec P.A P.L 1 th) :
    IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 (homAt t) th) := by
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl p
  obtain rfl : V = ⊤ := eq_top_iff.2 fun q _ => by rwa [Subsingleton.elim q p]
  obtain ⟨-, hsp⟩ := hb R t (fun i => VVRank.pullS P.A _ (homAt t) (b i)) fun i => VVRank.isPullSec_pullS _ _ _ _
  have hle : (⊤ : Submodule Γ((baseAt t).left, ⊤) (SecM P.A P.L 1 (baseAt t))) ≤
      Submodule.span _ {SecM.ofSec P.A (VVRank.pullS P.A 1 (homAt t) th)} := by
    refine hsp.ge.trans (Submodule.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    obtain ⟨r, hr⟩ := h (b i)
    have e : SecM.ofSec P.A (b i) = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
    refine Submodule.mem_span_singleton.2 ⟨(homAt t).left.appTop.hom r, ?_⟩
    exact ((VVRank.pullM P.A P.L 1 (homAt t)).map_smulₛₗ r _).symm.trans
      (congrArg (VVRank.pullM P.A P.L 1 (homAt t)) e.symm)
  intro s
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hle (Submodule.mem_top (x := SecM.ofSec P.A s)))
  exact ⟨c, fun j => (congrArg (fun q => q.1 j) hc).symm⟩

end GlobalTheory.ThetaPtMove
