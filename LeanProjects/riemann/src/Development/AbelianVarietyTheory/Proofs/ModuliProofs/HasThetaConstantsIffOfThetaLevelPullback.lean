import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaPtUp

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift GlobalTheory.ThetaPtMove

theorem exists_gen_up_iso {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} {χ : Y ⟶ Y'}
    (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (h₁ : h ≫ χ = 𝟙 _) (h₂ : χ ≫ h = 𝟙 _)
    (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J J', Good L z J → Good L' z J' →
        val t (r ≫ h) z J = (∏ k, wVal w z J J' (r ≫ φ' k) ^ ε k) * val a r z J' := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL hL' a ha
  obtain ⟨u, hu, hu'⟩ := VVRank.exists_gen_pullTo (φ' := φ) t ht χ fun k => by
    rw [hψ, ← Category.assoc, h₂, Category.id_comp]
  refine ⟨u, hu, fun Z r z J J' hJ hJ' => (hu' _ _ _ _ hJ).trans ?_⟩
  rw [Category.assoc, h₁, Category.comp_id]
  refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans ?_
  congr 1

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) [IsIso τ] (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

theorem exists_psi_inv' : ∃ χ : (T₀ ⊗ G).left ⟶ (T ⊗ A).left,
    psi hp τ hτ ≫ χ = 𝟙 _ ∧ χ ≫ psi hp τ hτ = 𝟙 _ := WeilPull.exists_psi_inv hp τ hτ

theorem exists_genThrough_up (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a b : ℤ} {m : T ⊗ A ⟶ A}
    {m₀ : T₀ ⊗ G ⟶ G} (h : psi hp τ hτ ≫ m₀.left = m.left ≫ φ)
    (α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, m.left] ![a, b])) (hα : α.IsGen) :
    ∃ α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, m₀.left] ![a, b]), α₀.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
        val α₀ (r ≫ psi hp τ hτ) z J =
          (wVal w z J J' (r ≫ (snd T A).left) ^ a * wVal w z J J' (r ≫ m.left) ^ b) * val α r z J' := by
  obtain ⟨χ, h₁, h₂⟩ := exists_psi_inv' hp τ hτ
  obtain ⟨α₀, hα₀, H⟩ := exists_gen_up_iso (φ := ![(snd T₀ G).left, m₀.left]) hw hL₀ hL₁ h₁ h₂
    (fun i => by
      fin_cases i
      · exact (psi_snd' hp τ hτ).symm
      · exact h.symm) α hα
  refine ⟨α₀, hα₀, fun Z r z J J' hJ hJ' => (H Z r z J J' hJ hJ').trans ?_⟩
  rw [Fin.prod_univ_two]
  rfl

theorem isTwistPull_up (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a b : ℤ} {m : T ⊗ A ⟶ A}
    {m₀ : T₀ ⊗ G ⟶ G} (h : psi hp τ hτ ≫ m₀.left = m.left ≫ φ)
    {α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, m₀.left] ![a, -b])}
    {α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα₀ : α₀.IsGen)
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
        val α₀ (r ≫ psi hp τ hτ) z J =
          (wVal w z J J' (r ≫ (snd T A).left) ^ a * wVal w z J J' (r ≫ m.left) ^ (-b)) * val α r z J')
    {s₀ s₀' s s'} (hs : SecRel hp τ hτ w s s₀) (hs' : SecRel hp τ hτ w s' s₀')
    (H₁ : IsTwistPull A L₁ (lift (fst T A) m) m (lift_snd _ _) a b α s s') :
    IsTwistPull G L₀ (lift (fst T₀ G) m₀) m₀ (lift_snd _ _) a b α₀ s₀ s₀' := by
  obtain ⟨χ, -, h₂⟩ := exists_psi_inv' hp τ hτ
  refine VVRank.isTwistPull_of_sv G hL₀ hα₀ fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
  have q := VVRank.sv_of_isTwistPull A H₁ χ y hJ'
  have e : (χ ≫ (lift (fst T A) m).left) ≫ (snd T A).left = χ ≫ m.left := by
    rw [Category.assoc, ← Over.comp_left, lift_snd]
  rw [← h₂, hs' _ _ _ _ _ hJ hJ', H _ _ _ _ _ hJ hJ', Category.assoc, ← psi_lift hp τ hτ h, ← Category.assoc,
    hs _ _ _ _ _ hJ hJ', e, zpow_neg, q]
  simp only [Units.val_mul]
  rw [mul_right_comm _ _ (val α _ y J').val, _root_.mul_assoc (_ * _), Units.inv_mul_cancel_left, _root_.mul_assoc]

theorem isValueAt_up (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {x : T ⟶ A} {x₀ : T₀ ⟶ G}
    (hx : τ ≫ x₀.left = x.left ≫ φ)
    {ρ₀ : LB.Gen (LB.LinComb L₀ (Y := T₀.left) (K := Fin 1) (fun _ => x₀.left) (fun _ => a))}
    {ρ : LB.Gen (LB.LinComb L₁ (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))}
    (H : GenThrough w _ _ _ ρ ρ₀ τ) {s₀ s} (hs : SecRel hp τ hτ w s s₀) {c : Γ(T.left, ⊤)}
    (H₁ : IsValueAt A L₁ a s x ρ c) : IsValueAt G L₀ a s₀ x₀ ρ₀ ((inv τ).appTop.hom c) := by
  refine isValueAt_of_sv hL₀ fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
  have q := sv_of_isValueAt H₁ (inv τ) y hJ'
  have g : gs (𝟙 _) y ⊤ ((inv τ).appTop.hom c) = gs (inv τ) y ⊤ c :=
    (gs_pull (𝟙 _) (inv τ) y ⊤ trivial c).trans (by rw [Category.id_comp])
  rw [g, ← IsIso.inv_hom_id τ, H _ _ _ _ _ hJ hJ', Category.assoc, ← psi_ptSec hp τ hτ hx, ← Category.assoc,
    hs _ _ _ _ _ hJ hJ', q, Category.assoc, ptSecT_snd, Fin.prod_univ_one, Units.val_mul, mul_left_comm]

theorem isGenSec_up (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ}
    {th : LB.Sec (LPow A L₁ a T)} {th₀ : LB.Sec (LPow G L₀ a T₀)}
    (h : SecRel hp τ hτ w th th₀) (hg : IsGenSec A L₁ a th) : IsGenSec G L₀ a th₀ := by
  intro s₀
  obtain ⟨χ, -, h₂⟩ := exists_psi_inv' hp τ hτ
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  obtain ⟨c, hc⟩ := hg s
  have e : χ ≫ (fst T A).left = (𝟙 _ ≫ (fst T₀ G).left) ≫ inv τ := by
    rw [← h₂, Category.assoc χ, psi_fst', Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have key : SecM.ofSec G s₀ = (inv τ).appTop.hom c • SecM.ofSec G th₀ := ThetaAct.sv_ext hL₀ fun y J hJ => by
    obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    have q := sv_of_eq_mul hc χ y hJ'
    have q₁ := hs _ χ y J J' hJ hJ'
    have q₂ := h _ χ y J J' hJ hJ'
    rw [h₂] at q₁ q₂
    refine Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm
    refine q₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) (gs_pull _ (inv τ) y ⊤ trivial c) q₂).symm)
    rw [q, e, mul_left_comm]
  exact ⟨(inv τ).appTop.hom c, fun j => congrArg (fun q => q.1 j) key⟩

theorem symLift_up [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {k : ℤ} {n : ℕ} {x : T ⟶ A}
    {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x ^ n = 1) {θ : ThetaGrp A L₁ k T}
    (H₁ : SymLift A L₁ k n x θ) : ∃ θ₀ : ThetaGrp G L₀ k T₀, SymLift G L₀ k n x₀ θ₀ ∧
      ∀ s₀ s₀' s s', SecRel hp τ hτ w s s₀ → SecRel hp τ hτ w s' s₀' → IsActOf A L₁ k θ s s' →
        IsActOf G L₀ k θ₀ s₀ s₀' := by
  obtain ⟨rfl, hpow, ν, hν, hs⟩ := H₁
  obtain ⟨χ, -, h₂⟩ := exists_psi_inv' hp τ hτ
  obtain ⟨a, ha, v⟩ := exists_genThrough_up hp τ hτ hw hL₀ hL₁ (psi_tr' hp τ hτ _ x₀ hx) θ.φ θ.isGen
  obtain ⟨ν₀, hν₀, u⟩ := exists_genThrough_up hp τ hτ hw hL₀ hL₁ (psi_neg hp τ hτ) ν hν
  let θ₀ : ThetaGrp G L₀ k T₀ := ⟨x₀, a, ha⟩
  have t : ∀ {y : T ⟶ A} {y₀ : T₀ ⟶ G}, τ ≫ y₀.left = y.left ≫ φ →
      (χ ≫ psi hp τ hτ) ≫ (translT G y₀).left = (χ ≫ (translT A y).left) ≫ psi hp τ hτ :=
    fun h => by
      rw [Category.assoc, Category.assoc]
      exact congrArg _ (psi_transl hp τ hτ _ _ h).symm
  have t₁ : ∀ y : T ⟶ A, (χ ≫ (translT A y).left) ≫ (snd T A).left = χ ≫ (translPt A y).left := fun y => by
    rw [Category.assoc, ThetaAct.translT_snd]
  have t₂ : ∀ y : T ⟶ A, (χ ≫ (translT A y).left) ≫ (translPt A θ.pt).left = χ ≫ (translPt A (θ.pt * y)).left :=
    fun y => by rw [Category.assoc, ← Over.comp_left, ThetaAct.translT_translPt]
  refine ⟨θ₀, ⟨rfl, corr_of_val hL₀ fun y J hJ => ?_, ν₀, hν₀, corr_of_val hL₀ fun y J hJ => ?_⟩,
    fun s₀ s₀' s s' h h' H => isTwistPull_up hp τ hτ hL₀ hL₁ (psi_tr' hp τ hτ _ x₀ hx) ha v h h' H⟩
  · obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    have q := val_corr hJ' hpow χ
    rw [val_powGen _ _ _ hJ', val_one] at q
    rw [val_powGen _ _ _ hJ, val_one, ← h₂]
    let F : ℕ → ((T₀ ⊗ G).left.presheaf.stalk y)ˣ := fun i => wVal w y J J' (χ ≫ (translPt A (θ.pt ^ i)).left) ^ k
    have e : ∀ i : ℕ, tval θ₀ ((χ ≫ psi hp τ hτ) ≫ (translT G (θ₀.pt ^ i)).left) y J =
        F i / F (i + 1) * tval θ (χ ≫ (translT A (θ.pt ^ i)).left) y J' := fun i => by
      rw [t (over_pow hp τ hτ hx i)]
      refine (v _ _ _ _ _ hJ hJ').trans ?_
      rw [t₁, t₂, ← pow_succ', zpow_neg, div_eq_mul_inv]
      rfl
    have e₀ : ∏ i : Fin n, F i / F (i + 1) = 1 := by
      rw [Fin.prod_univ_eq_prod_range (fun i => F i / F (i + 1)), Finset.prod_range_div', div_eq_one]
      simp only [F, hn, pow_zero]
    simp only [e, Finset.prod_mul_distrib, e₀, _root_.one_mul]
    exact q
  · obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    have q := val_corr hJ' hs χ
    rw [val_symGen _ _ _ hJ', val_one] at q
    refine (val_symGen θ₀ ν₀ _ hJ).trans (Eq.trans ?_ (val_one _).symm)
    have n₀ : (χ ≫ psi hp τ hτ) ≫ (negT G T₀).left = (χ ≫ (negT A T).left) ≫ psi hp τ hτ := by
      rw [Category.assoc, Category.assoc]
      exact congrArg _ (psi_lift hp τ hτ (psi_neg hp τ hτ)).symm
    have n₁ : (χ ≫ (negT A T).left) ≫ (snd T A).left = χ ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
      rw [Category.assoc, ← Over.comp_left, negT, lift_snd]
    have n₂ : (χ ≫ (translT A θ.pt⁻¹).left) ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left =
        (χ ≫ (negT A T).left) ≫ (translPt A θ.pt).left := by
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left]
      congr 2
      show translT A θ.pt⁻¹ ≫ (snd T A)⁻¹ = negT A T ≫ ((fst T A ≫ θ.pt) * snd T A)
      rw [GrpObj.comp_inv, MonObj.comp_mul, translT, negT, lift_snd, lift_snd, lift_fst_assoc]
      show ((fst T A ≫ θ.pt⁻¹) * snd T A)⁻¹ = (fst T A ≫ θ.pt) * (snd T A)⁻¹
      rw [mul_inv, GrpObj.comp_inv, inv_inv]
    have n₃ : χ ≫ (translPt A (θ.pt * θ.pt⁻¹)).left = χ ≫ (snd T A).left := by
      rw [mul_inv_cancel, ThetaAct.translPt_one]
    rw [← h₂, t (over_inv hp τ hτ hx), n₀]
    have a₁ := v _ (χ ≫ (translT A θ.pt⁻¹).left) y J J' hJ hJ'
    have a₂ := u _ χ y J J' hJ hJ'
    have a₃ := v _ (χ ≫ (negT A T).left) y J J' hJ hJ'
    have a₄ := u _ (χ ≫ (translT A θ.pt⁻¹).left) y J J' hJ hJ'
    rw [t₂, n₃] at a₁
    rw [n₁] at a₃
    rw [n₂] at a₄
    refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) a₁ a₂) (congrArg₂ (fun p q => p * q⁻¹) a₃ a₄)).trans
      (Eq.trans ?_ q)
    have key : ∀ {U : Type} [CommGroup U] (p₁ p₂ p₃ p₄ a b c d : U),
        (p₁ * p₂⁻¹ * a * (p₂ * p₃⁻¹ * b)) * (p₃ * p₄⁻¹ * c * (p₁ * p₄⁻¹ * d)⁻¹) = (a * b) * (c * d⁻¹) :=
      fun p₁ p₂ p₃ p₄ a b c d => by
        apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
    simp only [zpow_neg]
    exact key _ _ _ _ _ _ _ _

theorem isThetaPtOver_up {P₀ : PolAV S} {P : PolAV S'} {φ : P.A.left ⟶ P₀.A.left}
    (hp : IsGrpPullback P.A P₀.A f φ) (hw : LBIso P.L (P₀.L.pull φ)) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
    {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {x₀ : I → (T₀ ⟶ P₀.A)} (hx : ∀ i, τ ≫ (x₀ i).left = (x i).left ≫ φ)
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {v : I → Γ(T.left, ⊤)} (H : IsThetaPtOver P k x v) :
    IsThetaPtOver P₀ k x₀ (fun i => (inv τ).appTop.hom (v i)) := by
  obtain ⟨w, hw⟩ := hw
  have hL₀ := P₀.isLB
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨th₀, s₀, α₀, ρ₀, U₀, t₀, c₀, u₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := H
  obtain ⟨th, hth⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ th₀
  obtain ⟨s, hs⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ s₀
  choose t ht using fun i => exists_secRel_up hp τ hτ hw hL₀ hL₁ (t₀ i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough_up hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ k) α₀ h₂
  obtain ⟨ρ, hρ, vρ⟩ := exists_gen_up_iso (φ := fun _ : Fin 1 => (1 : T₀ ⟶ P₀.A).left) (h := τ) hw hL₀ hL₁
    (IsIso.hom_inv_id τ) (IsIso.inv_hom_id τ) (fun _ => (over_one hp τ hτ).symm) ρ₀ h₃
  choose U hU hU' using fun i => symLift_up hp τ hτ hw hL₀ hL₁ (hx i) (hk i) (h₅ i)
  refine ⟨th, s, α, ρ, U, t, fun i => (inv τ).appTop.hom (c₀ i), Units.map (inv τ).appTop.hom.toMonoidHom u₀,
    isGenSec_up hp τ hτ hw hL₀ hL₁ hth h₁, hα, hρ,
    isTwistPull_up hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ k) hα vα hth hs h₄, hU,
    fun i => hU' i _ _ _ _ hs (ht i) (h₆ i),
    fun i => isValueAt_up hp τ hτ hL₀ hL₁ (over_one hp τ hτ) vρ (ht i) (h₇ i), fun i => ?_⟩
  exact (congrArg (inv τ).appTop.hom (h₈ i)).trans (map_mul _ _ _)

theorem isThetaPtOver_down {P₀ : PolAV S} {P : PolAV S'} {φ : P.A.left ⟶ P₀.A.left}
    (hp : IsGrpPullback P.A P₀.A f φ) (hw : LBIso P.L (P₀.L.pull φ)) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
    {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {x₀ : I → (T₀ ⟶ P₀.A)} (hx : ∀ i, τ ≫ (x₀ i).left = (x i).left ≫ φ)
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {v₀ : I → Γ(T₀.left, ⊤)} (H : IsThetaPtOver P₀ k x₀ v₀) :
    IsThetaPtOver P k x (fun i => τ.appTop.hom (v₀ i)) := by
  refine isThetaPtOver_move τ hp hw τ (𝟙 T₀) (Category.comp_id _) hτ (fun th h s => ?_) hx hk H
  obtain ⟨r, hr⟩ := h s
  have e := VVRank.pullM_id P₀.A P₀.isLB 1 (SecM.ofSec P₀.A th)
  exact ⟨r, fun j => (hr j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e).symm)⟩

omit τ in

theorem isThetaPt_iff {P₀ : PolAV S} {P : PolAV S'} {φ : P.A.left ⟶ P₀.A.left}
    (hp : IsGrpPullback P.A P₀.A f φ) (hw : LBIso P.L (P₀.L.pull φ))
    {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {x₀ : I → (Over.mk (T.hom ≫ f) ⟶ P₀.A)}
    (hx : ∀ i, (x₀ i).left = (x i).left ≫ φ) (hk : ∀ i, x i ^ (k ^ 2) = 1) (v : I → Γ(T.left, ⊤)) :
    IsThetaPt P k x v ↔ IsThetaPt P₀ k x₀ v := by
  refine and_congr_right fun _ => and_congr_right fun _ =>
    forall_congr' fun p => exists_congr fun V => and_congr_right fun _ => ?_
  let V₀ : (Over.mk (T.hom ≫ f)).left.Opens := V
  let τ : (overRes V).left ⟶ (overRes V₀).left := 𝟙 V.toScheme
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 V.toScheme))
  have hτ : τ ≫ (overRes V₀).hom = (overRes V).hom ≫ f := (Category.id_comp _).trans (Category.assoc _ _ _).symm
  have mv : ∀ i, τ ≫ (overResι V₀ ≫ x₀ i).left = (overResι V ≫ x i).left ≫ φ := fun i =>
    (Category.id_comp _).trans ((congrArg (V.ι ≫ ·) (hx i)).trans (Category.assoc _ _ _).symm)
  have hk' : ∀ i, (overResι V ≫ x i) ^ (k ^ 2) = 1 := fun i => by
    rw [← MonObj.comp_pow, hk, MonObj.comp_one]
  have hi : inv τ = 𝟙 V.toScheme := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  refine ⟨fun H => ?_, fun H => isThetaPtOver_down τ hp hw hτ mv hk' H⟩
  have Q := isThetaPtOver_up τ hp hw hτ mv hk' H
  rw [hi] at Q
  exact Q

theorem map_linComb {S S' : Scheme.{0}} {A T : Over S} {A' T' : Over S'} [GrpObj A] [GrpObj A']
    (F : (T ⟶ A) →* (T' ⟶ A')) {r : ℕ} (y : Fin r → (T ⟶ A)) (a : Fin r → ℕ) :
    F (linComb y a) = linComb (fun i => F (y i)) a := by
  have h := map_list_prod F (List.ofFn fun i => y i ^ a i)
  rw [List.map_ofFn] at h
  exact h.trans (congrArg List.prod (congrArg List.ofFn (funext fun i => map_pow F (y i) (a i))))

theorem lab_pow {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) (a : Ix g k) : t.lab a ^ k = 1 := by
  have := t.ab.comm
  have cm : ∀ x y : baseOver S ⟶ t.A, Commute x y := fun x y => _root_.mul_comm x y
  refine List.prod_induction (fun y => y ^ k = 1) (fun x y hx hy => ?_) (one_pow _) fun y hy => ?_
  · rw [(cm x y).mul_pow, hx, hy, _root_.mul_one]
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hy
    rw [← pow_mul, Nat.mul_comm, pow_mul, t.torsion, one_pow]

theorem lab_over {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}
    {t : TObj g k J b s} {t' : TObj g k J b s'} {φ : t'.A.left ⟶ t.A.left} (hp : IsGrpPullback t'.A t.A f φ)
    (h : ∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) (a : Ix g k) :
    f ≫ (t.lab a).left = (t'.lab a).left ≫ φ := by
  have hf : f ≫ (baseOver S).hom = (baseOver S').hom ≫ f := (Category.comp_id _).trans (Category.id_comp _).symm
  refine (over_iff (T := baseOver _) (T₀ := baseOver _) hp f hf _ _).2 ?_
  rw [TObj.lab, TObj.lab, map_linComb, map_linComb]
  exact congrArg (linComb · _) (funext fun i => (over_iff (T := baseOver _) (T₀ := baseOver _) hp f hf _ _).1 (h i).symm)

end GlobalTheory.ThetaPtUp

theorem GlobalTheory.hasTh_iff_of_tmap : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (S' : Scheme.{0}) (s' : S' ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s') (f : S' ⟶ S) (R : Type) [CommRing R] (x : Sp R ⟶ S') (v : Ix g (N' ^ 2) → R), TMap t' t f → (t'.HasTh x v ↔ t.HasTh (x ≫ f) v) := by
  intro o _ g N' J b S s t S' s' t' f R _ x v ⟨φ, hp, hw, hpt, _⟩
  refine GlobalTheory.ThetaPtUp.isThetaPt_iff (P₀ := t.pol) (P := t'.pol) (T := Over.mk x) hp hw (fun a => ?_) (fun a => ?_) _
  · exact (Category.assoc x f _).trans ((congrArg (x ≫ ·) (GlobalTheory.ThetaPtUp.lab_over hp hpt a)).trans
      (Category.assoc _ _ _).symm)
  · exact (MonObj.comp_pow _ _ _).symm.trans
      ((congrArg (_ ≫ ·) (GlobalTheory.ThetaPtUp.lab_pow t' a)).trans (MonObj.comp_one _))

end
