import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibPrim
open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.FrameValue

theorem differentiable_quot {A : Over (Sp ℂ)} [GrpObj A] {X : Scheme.{0}} {L : LB X} {L' : LB A.left} (hL' : L'.IsLB)
    {φ : A.left ⟶ X} {w : LB.Iso L' (L.pull φ)} (hw : w.IsGen) {g : ℕ} (u : HolUnif A L' g)
    {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {fr : (Fin g → ℂ) → ℂ}
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      fr z = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ φ), i)).val * u.fr i z)
    {K : Type} [Fintype K] {ψ : K → (X ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L ψ ε)} (ht : t.IsGen)
    {z : (Fin g → ℂ) → K → Fin g → ℂ} (hd : ∀ k, Differentiable ℂ fun v => z v k)
    (hz : ∀ v k, ((u.ex v).left ≫ φ) ≫ ψ k = (u.ex (z v k)).left ≫ φ) :
    Differentiable ℂ fun v => vF t ((u.ex v).left ≫ φ) J / ∏ k, fr (z v k) ^ ε k := by
  intro v₀
  obtain ⟨j, hj⟩ : ∃ j, ⊤ ≤ ((u.ex v₀).left ≫ φ) ⁻¹ᵁ L.wchart ψ j :=
    ⟨_, (le_preimage_wchart _ L ψ _).2 fun _ => hJ _⟩
  obtain ⟨i, hi⟩ : ∃ i : K → L'.ι, ∀ k, ⊤ ≤ (u.ex (z v₀ k)).left ⁻¹ᵁ L'.U (i k) := ⟨_, fun _ => le_chartAt hL' _⟩
  have key : ∀ v, ⊤ ≤ ((u.ex v).left ≫ φ) ⁻¹ᵁ L.wchart ψ j → ∀ k,
      ⊤ ≤ (u.ex (z v k)).left ⁻¹ᵁ L.wchart (fun _ : PUnit => φ) (fun _ => j k) := fun v hv k =>
    (le_preimage_wchart _ L _ _).2 fun _ => hz v k ▸ (le_preimage_wchart _ L ψ _).1 hv k
  obtain ⟨ho, hh⟩ := u.hol (φ ⁻¹ᵁ L.wchart ψ j) ((φ.app _).hom (t.s j).val)
  have hn : {v | ⊤ ≤ ((u.ex v).left ≫ φ) ⁻¹ᵁ L.wchart ψ j} ∈ nhds v₀ := ho.mem_nhds hj
  have d₁ : DifferentiableAt ℂ (fun v => valAt' ((u.ex v).left ≫ φ) (L.wchart ψ j) (t.s j).val) v₀ := by
    refine (hh.differentiableAt (ho.mem_nhds hj)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
    exact ((valueRules _ (u.ex v).left).2.2.2.1 _ φ _ _).symm
  let G : K → (Fin g → ℂ) → ℂ := fun k x =>
    valAt' (u.ex x).left (L.wchart (fun _ : PUnit => φ) (fun _ => j k) ⊓ L'.U (i k)) (w.s (fun _ => j k, i k)).val *
      u.fr (i k) x
  have h₀ := fun k => (le_preimage_inf _ _ _).2 ⟨key v₀ hj k, hi k⟩
  have n₀ : ∀ k, G k (z v₀ k) ≠ 0 := fun k =>
    mul_ne_zero (val_unit_ne_zero _ valueRules (h₀ k) _) (u.fr_ne _ _ (hi k))
  have d₂ : DifferentiableAt ℂ (fun v => ∏ k, G k (z v k) ^ ε k) v₀ := by
    have a : ∀ k, DifferentiableAt ℂ (fun v => G k (z v k) ^ ε k) v₀ := fun k => by
      refine DifferentiableAt.zpow ?_ (Or.inl (n₀ k))
      refine DifferentiableAt.comp v₀ (g := G k) ?_ (hd k v₀)
      exact ((u.hol _ _).2.differentiableAt ((u.hol _ 0).1.mem_nhds (h₀ k))).fun_mul
        ((u.fr_hol (i k)).differentiableAt ((u.hol _ 0).1.mem_nhds (hi k)))
    classical
    exact (HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (a k).hasFDerivAt).differentiableAt
  refine (d₁.fun_mul (d₂.fun_inv (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (n₀ k)))).congr_of_eventuallyEq ?_
  have hn' : ∀ᶠ v in nhds v₀, ∀ k, ⊤ ≤ (u.ex (z v k)).left ⁻¹ᵁ L'.U (i k) :=
    Filter.eventually_all.2 fun k => (hd k v₀).continuousAt.preimage_mem_nhds ((u.hol _ 0).1.mem_nhds (hi k))
  filter_upwards [hn, hn'] with v hv hv'
  have hJv : ⊤ ≤ ((u.ex v).left ≫ φ) ⁻¹ᵁ L.wchart ψ fun k => J (((u.ex v).left ≫ φ) ≫ ψ k) :=
    (le_preimage_wchart _ L ψ _).2 fun _ => hJ _
  have e₁ := (val_gen _ valueRules t ht _ _ hJv hv).trans
    (congrArg (· * _) (val_linComb _ valueRules L ψ ε _ _ hJv hv))
  have e₂ : ∀ k, fr (z v k) = valAt' (((u.ex v).left ≫ φ) ≫ ψ k)
      (L.U (J (((u.ex v).left ≫ φ) ≫ ψ k)) ⊓ L.U (j k)) (L.g _ _).val * G k (z v k) := fun k => by
    rw [hfr _ _ (hv' k), hz v k, ← _root_.mul_assoc]
    refine congrArg (· * _) ((GlobalTheory.PowUnif.val_iso _ L L' (fun _ : PUnit => φ) w hw _ _ _ _
      ((le_preimage_wchart _ L _ _).2 fun _ => hJ _) (key v hv k) (hv' k) (hv' k)).trans ?_)
    rw [GlobalTheory.PowUnif.val_g_self hL' _ _ (hv' k), inv_one, _root_.mul_one, Fintype.prod_unique]
  have n : (∏ k, valAt' (((u.ex v).left ≫ φ) ≫ ψ k)
      (L.U (J (((u.ex v).left ≫ φ) ≫ ψ k)) ⊓ L.U (j k)) (L.g _ _).val ^ ε k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (val_unit_ne_zero _ valueRules
      ((le_preimage_inf _ _ _).2 ⟨hJ _, (le_preimage_wchart _ L ψ _).1 hv k⟩) _)
  simp only [e₂, mul_zpow, Finset.prod_mul_distrib]
  exact (congrArg (· / _) e₁).trans ((mul_div_mul_left _ _ n).trans (div_eq_mul_inv _ _))

theorem vF_eq_one {X Y Z : Scheme.{0}} {L : LB X} {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
    {K : Type} [Fintype K] {ψ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L ψ ε)} {e : Z ⟶ Y}
    (h : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t e) (LB.oneGen L)) (y : Sp ℂ ⟶ Z) : vF t (y ≫ e) J = 1 := by
  have h₁ : ⊤ ≤ y ⁻¹ᵁ L.wchart (fun k => e ≫ ψ k) fun k => J (y ≫ e ≫ ψ k) :=
    (le_preimage_wchart _ L _ _).2 fun _ => hJ _
  have h₂ : ⊤ ≤ y ⁻¹ᵁ L.wchart (PEmpty.elim : PEmpty → (Z ⟶ X)) PEmpty.elim :=
    (le_preimage_wchart _ L _ _).2 fun k => k.elim
  have h₃ := (le_preimage_inf y _ _).2 ⟨h₁, h₂⟩
  have := congrArg (fun q : Γ(Z, _)ˣ => valAt' y _ q.val) (h (fun k => J (y ≫ e ≫ ψ k)) PEmpty.elim
    (fun a b q => congrArg (fun q => J (y ≫ q)) q) (fun a => a.elim) (fun _ b => b.elim))
  have e₁ := (val_res y valueRules inf_le_left h₃ _).symm.trans (this.trans (val_res y valueRules inf_le_right h₃ _))
  obtain ⟨r, hr⟩ := (valueRules Z y).2.1 _ h₂
  exact ((val_res y valueRules _ h₁ _).trans (val_pullU y valueRules e _ _)).symm.trans
    (e₁.trans ((hr _).trans (map_one r)))

theorem fibPrim : FibPrimSt := by
  rintro R _ _ _ D J g Λ Hm χ ex fr ⟨hJ, P', φ, w, u, rfl, hφ, hw, hAH, -, -, -, hex, hfr⟩ f hf F hF hFf hH Ef hEf t ⟨ht, h₀⟩
  change u.IsAH Hm χ at hAH
  have hL := P'.isLB
  have add : ∀ z z', ex (z + z') = ex z * ex z' := fun z z' => Over.OverMorphism.ext (by
    rw [hex, u.ex_add, ← hφ.2 _ _ _ (pushPt hφ.1.w (u.ex z)) (pushPt hφ.1.w (u.ex z')) rfl rfl]
    exact mul_left_congr (Category.id_comp _) _ _ _ _ (hex z).symm (hex z').symm)
  have zero : ex 0 = 1 := mul_eq_left.1 ((add 0 0).symm.trans (by rw [add_zero]))
  have per : ∀ (l : u.Λ) z, (ex (z + l)).left = (ex z).left := fun l z => by
    rw [hex, hex, ex_add_period u z l l.2]
  have fac : ∀ (l : u.Λ) z, (fr z : ℂ) = ahFactor Hm χ l z * fr (z + l) := fun l z => by
    have hi := le_chartAt hL (u.ex z).left
    have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ P'.L.U (chartAt hL (u.ex z).left) := by
      rw [ex_add_period u z l l.2]; exact hi
    rw [hfr _ _ hi, hfr _ _ hi', hAH.2.2.2 l _ z hi, per, ex_add_period u z l l.2, mul_left_comm]
    rfl
  obtain ⟨V, hV⟩ : ∃ V : (Fin g → ℂ) → ℂ, ∀ v, V v = vF t (ex v).left J /
      (fr (v + F v) * ((fr v : ℂ) ^ 2)⁻¹ * (fr (F v) : ℂ)⁻¹ * fr 0 ^ 2) := ⟨_, fun _ => rfl⟩
  have dF : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have hd : Differentiable ℂ V := by
    have := differentiable_quot hL hw u hJ (fr := fun z => fr z) (fun z i hi => by rw [← hex]; exact hfr z i hi) ht
      (z := fun v => ![v + F v, v, F v, 0]) (fun k => by fin_cases k <;> simp <;> fun_prop) (fun v k => by
        rw [← hex, ← hex]
        fin_cases k
        · exact congrArg (fun m => m.left) (show ex v ≫ (𝟙 _ * f) = ex (v + F v) by
            rw [MonObj.comp_mul, Category.comp_id, ← hFf, add])
        · exact Category.comp_id _
        · exact congrArg (fun m => m.left) (hFf v).symm
        · exact congrArg (fun m => m.left) ((MonObj.comp_one (ex v)).trans zero.symm))
    convert this using 2 with v
    rw [hV, hex]
    simp [Fin.prod_univ_four]
  have hper : ∀ (l : u.Λ) v, V (v + l) = (-1) ^ Ef l ⟨F l, hF l l.2⟩ / χ l * V v := fun l v => by
    have a₁ := fac (l + ⟨F l, hF l l.2⟩) (v + F v)
    have a₂ := fac l v
    have a₃ := fac ⟨F l, hF l l.2⟩ (F v)
    have c := chi_add hL hAH l ⟨F l, hF l l.2⟩
    have s : Complex.exp (Real.pi * Complex.I * (hermForm Hm l (F l)).im) = (-1) ^ Ef l ⟨F l, hF l l.2⟩ := by
      rw [← hEf l ⟨F l, hF l l.2⟩, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
      congr 1
      push_cast
      ring
    have x : Complex.exp (Real.pi * hermForm Hm (v + F v) (l + F l) + Real.pi / 2 * hermForm Hm (l + F l) (l + F l)) =
        Complex.exp (Real.pi * hermForm Hm v l + Real.pi / 2 * hermForm Hm l l) ^ 2 *
        Complex.exp (Real.pi * hermForm Hm (F v) (F l) + Real.pi / 2 * hermForm Hm (F l) (F l)) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      simp only [EigenNorm.hermForm_add_left, EigenNorm.hermForm_add_right]
      push_cast
      linear_combination (-Real.pi : ℂ) * hH v l - (Real.pi / 2 : ℂ) * hH l l
    rw [s] at c
    rw [hV, hV, per, a₁, a₂, a₃, map_add, add_add_add_comm v]
    simp only [ahFactor, c, Submodule.coe_add, x]
    have n := chi_ne_zero hAH l
    have n' := chi_ne_zero hAH ⟨F l, hF l l.2⟩
    have n'' : (-1 : ℂ) ^ Ef l ⟨F l, hF l l.2⟩ ≠ 0 := zpow_ne_zero _ (by simp)
    field_simp
  have hc := const_of_norm_periodic u hd (fun l v => by
    rw [hper, norm_mul, norm_div, hAH.2.2.1, norm_zpow, norm_neg, norm_one, one_zpow, div_one, _root_.one_mul])
  have h1 : V 0 = 1 := by
    have e : (ex 0).left = (TF (R := R) ℂ).hom ≫ eSec D.P.A := by rw [zero, Hom.one_def]; simp [eSec]
    rw [hV, e, vF_eq_one hJ h₀, map_zero, add_zero]
    have := (fr 0).ne_zero
    field_simp
  refine ⟨fun l => ?_, fun z => ?_⟩
  · have := hper l 0
    rw [hc _ 0, h1, _root_.mul_one] at this
    exact ((div_eq_one_iff_eq (chi_ne_zero hAH l)).1 this.symm).symm
  · have := (hV z).symm.trans ((hc z 0).trans h1)
    have a := (fr z).ne_zero
    have b := (fr (F z)).ne_zero
    have c := (fr (z + F z)).ne_zero
    have d := (fr 0).ne_zero
    field_simp at this
    exact this

theorem fibPrim_of_laws : Laws → FibPrimSt := fun _ => fibPrim

end GlobalTheory.Ex.Arch.FibPrim
end
