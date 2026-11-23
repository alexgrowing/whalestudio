import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefVal
open TWM TWO CoefBasic

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
  {X : Scheme.{0}} {L : LB X}

theorem isDominant_ι : IsDominant (ιS hϖ hv).left := by
  refine ⟨?_⟩
  show DenseRange (PrimeSpectrum.comap (algebraMap (Ov v) F))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective (Ov v) F)]
  exact bot_le

theorem ι_inj [X.IsSeparated] : Function.Injective fun ψ : (TO hϖ hv).left ⟶ X => (ιS hϖ hv).left ≫ ψ := by
  intro a b h
  have := isDominant_ι hϖ hv
  have : IsReduced (TO hϖ hv).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (Ov v))))
  exact ext_of_isDominant (ιS hϖ hv).left h

theorem gs_ι (z : (TF (R := V) F).left) (a : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) :
    gs (ιS hϖ hv).left z ⊤ a = cst F z (ιr (v := v) a) := by
  rw [cst_eq, gs_eq _ z ⊤ trivial]
  exact congrArg ((TF (R := V) F).left.presheaf.germ ⊤ z trivial).hom
    (appTop_specMap (CommRingCat.ofHom (algebraMap (Ov v) F)) a)

theorem sec_int [X.IsSeparated] (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → ((TO hϖ hv).left ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε))
    (hf : ∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ X) → U), ∏ i, h ((ιS hϖ hv).left ≫ φ i) ^ ε i = 1) :
    ∃ a : F, 0 ≤ v a ∧ ∀ z J, Good L z J → sval s (ιS hϖ hv).left z J = cst F z a := by
  obtain ⟨s₀, hs⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
    refine Eq.trans ?_ ((hf U (Function.extend (fun ψ => (ιS hϖ hv).left ≫ ψ) h 1)).trans (Fintype.prod_empty _).symm)
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(ι_inj hϖ hv).extend_apply]) s
  have le : (⊤ : (TO hϖ hv).left.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → ((TO hϖ hv).left ⟶ X)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨ιr (v := v) (((TO hϖ hv).left.presheaf.map (homOfLE le).op).hom (s₀.f PEmpty.elim)), v_ιr _,
    fun z J hJ => ?_⟩
  rw [← hs _ _ z J hJ, sval_of s₀ _ z J PEmpty.elim (fun k => k.elim), ← gs_ι hϖ hv]
  exact (gs_res _ z le trivial _).symm

abbrev FS (V F : Type) [CommRing V] [IsDomain V] [Field F] [Algebra (FractionRing V) F] (X : Scheme.{0}) : Type 1 :=
  ∀ (U : Type) [CommGroup U], (((TF (R := V) F).left ⟶ X) → U) → U

def HV (L : LB X) (σ : FS V F X)
    (f : ∀ z : (TF (R := V) F).left, (((TF (R := V) F).left ⟶ X) → L.ι) → (TF (R := V) F).left.presheaf.stalk z)
    (x : F) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → ((TO hϖ hv).left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ X) → U), ∏ i, h ((ιS hϖ hv).left ≫ φ i) ^ ε i = σ U h) ∧
    ∀ z J, Good L z J → f z J = cst F z x * (val t (ιS hϖ hv).left z J).val

variable {hϖ hv}

theorem HV.mul {σ σ' : FS V F X} {f f'} {x x' : F} (H : HV hϖ hv L σ f x) (H' : HV hϖ hv L σ' f' x') :
    HV hϖ hv L (fun U _ h => σ U h * σ' U h) (fun z J => f z J * f' z J) (x * x') := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht', fun U _ h => ?_,
    fun z J hJ => ?_⟩
  · rw [Fintype.prod_sum_type]
    exact congrArg₂ (· * ·) (hs U h) (hs' U h)
  · rw [val_mul hJ]
    simp only [e z J hJ, e' z J hJ, cst_eq, map_mul, Units.val_mul]
    ring

theorem HV.one : HV hϖ hv L (fun _ _ _ => 1) (fun _ _ => 1) 1 :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L (Y := (TO hϖ hv).left),
    fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun U _ h => Fintype.prod_empty _, fun z J _ => by rw [val_one, cst_eq, map_one, Units.val_one, _root_.mul_one]⟩

theorem HV.congr {σ σ' : FS V F X} {f f'} {x : F} (H : HV hϖ hv L σ f x)
    (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h) (hf : ∀ z J, Good L z J → f' z J = f z J) :
    HV hϖ hv L σ' f' x := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  exact ⟨K, _, φ, ε, t, ht, fun U _ h => (hs U h).trans (hσ U h), fun z J hJ => (hf z J hJ).trans (e z J hJ)⟩

theorem HV.pow {σ : FS V F X} {f} {x : F} (H : HV hϖ hv L σ f x) (n : ℕ) :
    HV hϖ hv L (fun U _ h => σ U h ^ n) (fun z J => f z J ^ n) (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using HV.one
  | succ n ih => simpa only [pow_succ] using ih.mul H

theorem HV.smul {σ : FS V F X} {f} {x : F} (H : HV hϖ hv L σ f x) (c : F) :
    HV hϖ hv L σ (fun z J => cst F z c * f z J) (c * x) := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  refine ⟨K, _, φ, ε, t, ht, hs, fun z J hJ => ?_⟩
  simp only [e z J hJ, cst_eq, map_mul, _root_.mul_assoc]

theorem HV.le [X.IsSeparated] (hL : L.IsLB) {σ : FS V F X} {f} {x x' : F} (H : HV hϖ hv L σ f x)
    (H' : HV hϖ hv L σ f x') : v x ≤ v x' := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  have hu := mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ ht')
  obtain ⟨a, ha, hav⟩ := sec_int hϖ hv hL (Geo.Tor.genSec _ hu) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [hs, hs', mul_inv_cancel])
  obtain ⟨z⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  have b := hav z J hJ
  rw [sval_genSec _ hu _ z hJ, val_mul hJ, val_inv] at b
  have c : x' = x * a := by
    apply cstH_inj (R := V) z
    have d := (e z J hJ).symm.trans (e' z J hJ)
    rw [map_mul, ← cst_eq, ← cst_eq, ← cst_eq, ← b, Units.val_mul, ← _root_.mul_assoc, d, _root_.mul_assoc,
      Units.mul_inv, _root_.mul_one]
  rw [c, AddValuation.map_mul]
  exact le_add_of_nonneg_right ha

theorem HV.cmp [X.IsSeparated] (hL : L.IsLB) {σ σ' : FS V F X} {f f'} {x x' : F} (H : HV hϖ hv L σ f x)
    (H' : HV hϖ hv L σ' f' x') (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h)
    (hf : ∀ z J, Good L z J → f' z J = f z J) : v x = v x' :=
  le_antisymm ((H.congr hσ hf).le hL H') (H'.le hL (H.congr hσ hf))

variable {K : Type} [Fintype K] {ε : K → ℤ}

theorem hv_gen {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (r₀ : (TO hϖ hv).left ⟶ Y) {r : (TF (R := V) F).left ⟶ Y} (hr : (ιS hϖ hv).left ≫ r₀ = r) :
    HV hϖ hv L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => (val t r z J).val) 1 := by
  subst hr
  exact ⟨K, _, _, ε, LB.pullGen L φ ε t r₀, pullGen_isGen _ _ _ _ ht _, fun U _ h => by simp only [Category.assoc],
    fun z J hJ => by rw [val_pull hJ, cst_eq, map_one, _root_.one_mul]⟩

theorem hv_sec [X.IsSeparated] (hL : L.IsLB) {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (r₀ : (TO hϖ hv).left ⟶ Y) {r : (TF (R := V) F).left ⟶ Y} (hr : (ιS hϖ hv).left ≫ r₀ = r) :
    ∃ x, 0 ≤ v x ∧ HV hϖ hv L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => sval s r z J) x := by
  subst hr
  obtain ⟨t, ht⟩ := exists_gen_of_local (V := Ov v) L hL (fun i => r₀ ≫ φ i) ε
  have hi := invGen_isGen _ _ _ _ ht
  obtain ⟨a, ha, hav⟩ := sec_int hϖ hv hL (pullMulSec s r₀ _ hi) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
  refine ⟨a, ha, K, _, _, ε, t, ht, fun U _ h => by simp only [Category.assoc], fun z J hJ => ?_⟩
  have b := hav z J hJ
  rw [sval_pullMulSec _ _ _ hi _ z hJ, val_inv] at b
  rw [← b, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem hv_of_genV {φ : K → ((TF (R := V) F).left ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} {r : ℚ}
    (H : GenV hϖ hv t r) :
    ∃ x, v x = r ∧ HV hϖ hv L (fun _ _ h => ∏ i, h (φ i) ^ ε i) (fun z J => (val t (𝟙 _) z J).val) x := by
  obtain ⟨φ₀, h₀, t₀, ht₀, x, hx, e⟩ := H
  exact ⟨x, hx, K, _, φ₀, ε, t₀, ht₀, fun U _ h => by simp only [h₀], e⟩

theorem genV_unique [X.IsSeparated] (hL : L.IsLB) {φ : K → ((TF (R := V) F).left ⟶ X)}
    {t : LB.Gen (LB.LinComb L φ ε)} {r r' : ℚ} (H : GenV hϖ hv t r) (H' : GenV hϖ hv t r') : r = r' := by
  obtain ⟨x, hx, a⟩ := hv_of_genV H
  obtain ⟨x', hx', a'⟩ := hv_of_genV H'
  have := a.cmp hL a' (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  rw [hx, hx'] at this
  exact_mod_cast this

theorem exists_genV (hL : L.IsLB) {φ : K → ((TF (R := V) F).left ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (hφ : ∀ i, ∃ ψ, φ i = (ιS hϖ hv).left ≫ ψ) : ∃ r, GenV hϖ hv t r := by
  choose φ₀ h₀ using hφ
  obtain ⟨t₀, ht₀⟩ := exists_gen_of_local (V := Ov v) L hL φ₀ ε
  obtain ⟨c, hc, e⟩ := exists_ratio hL t ht (LB.pullGen L _ _ t₀ (ιS hϖ hv).left) (pullGen_isGen _ _ _ _ ht₀ _)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [h₀])
  obtain ⟨q, hq⟩ := wt_coe_of_ne (v := v) hc
  refine ⟨q, φ₀, h₀, t₀, ht₀, c, hq, fun z J hJ => ?_⟩
  have := e (TF (R := V) F).left (𝟙 (TF (R := V) F).left) z J hJ
  rw [val_pull hJ, Category.id_comp] at this
  exact this

end GlobalTheory.UT.CoefVal
end
