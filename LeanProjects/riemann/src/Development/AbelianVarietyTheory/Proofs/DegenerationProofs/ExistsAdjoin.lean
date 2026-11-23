import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRepresentativesModNsmul

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefField
open TWM TWO CoefBasic

section
variable (R : Type) [CommRing R] [IsDomain R] (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E]
  [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] {X : Scheme.{0}} {L : LB X}

omit [IsDomain R] in
theorem comp_jFK : Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫ jFK (R := R) E = jFK (R := R) F := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

def ιE : TF (R := R) F ⟶ TF (R := R) E :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E F)))
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) (comp_jFK R E F)))

omit [IsDomain R] in
theorem ι_inj : Function.Injective fun ψ : (TF (R := R) E).left ⟶ X => (ιE R E F).left ≫ ψ := by
  intro a b h
  have : Epi (ιE R E F).left := by
    show Epi (Spec.map (CommRingCat.ofHom (algebraMap E F)))
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap E F))) := inferInstance
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap E F))) :=
      ⟨fun u => ⟨IsLocalRing.closedPoint F, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective _
  exact (cancel_epi (ιE R E F).left).1 h

omit [IsDomain R] in
theorem gs_ι (z : (TF (R := R) F).left) (a : Γ(Spec (CommRingCat.of E), ⊤)) :
    gs (ιE R E F).left z ⊤ a = cst F z (algebraMap E F ((Scheme.ΓSpecIso (CommRingCat.of E)).hom.hom a)) := by
  rw [cst_eq, gs_eq _ z ⊤ trivial]
  exact congrArg ((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom
    (appTop_specMap (CommRingCat.ofHom (algebraMap E F)) a)

omit [IsDomain R] in

theorem sec_rat (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → ((TF (R := R) E).left ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε))
    (hf : ∀ (U : Type) [CommGroup U] (h : ((TF (R := R) F).left ⟶ X) → U), ∏ i, h ((ιE R E F).left ≫ φ i) ^ ε i = 1) :
    ∃ a : E, ∀ z J, Good L z J → sval s (ιE R E F).left z J = cst F z (algebraMap E F a) := by
  obtain ⟨s₀, hs⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
    refine Eq.trans ?_ ((hf U (Function.extend (fun ψ => (ιE R E F).left ≫ ψ) h 1)).trans (Fintype.prod_empty _).symm)
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(ι_inj R E F).extend_apply]) s
  have le : (⊤ : (TF (R := R) E).left.Opens) ≤
      LB.wchart L (PEmpty.elim : PEmpty → ((TF (R := R) E).left ⟶ X)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of E)).hom.hom
    (((TF (R := R) E).left.presheaf.map (homOfLE le).op).hom (s₀.f PEmpty.elim)), fun z J hJ => ?_⟩
  rw [← hs _ _ z J hJ, sval_of s₀ _ z J PEmpty.elim (fun k => k.elim), ← gs_ι R E F]
  exact (gs_res _ z le trivial _).symm

def HE (L : LB X) (σ : CoefVal.FS R F X)
    (f : ∀ z : (TF (R := R) F).left, (((TF (R := R) F).left ⟶ X) → L.ι) → (TF (R := R) F).left.presheaf.stalk z)
    (x : F) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → ((TF (R := R) E).left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : ((TF (R := R) F).left ⟶ X) → U), ∏ i, h ((ιE R E F).left ≫ φ i) ^ ε i = σ U h) ∧
    ∀ z J, Good L z J → f z J = cst F z x * (val t (ιE R E F).left z J).val

variable {R E F}

theorem HE.mul {σ σ' : CoefVal.FS R F X} {f f'} {x x' : F} (H : HE R E F L σ f x) (H' : HE R E F L σ' f' x') :
    HE R E F L (fun U _ h => σ U h * σ' U h) (fun z J => f z J * f' z J) (x * x') := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht', fun U _ h => ?_,
    fun z J hJ => ?_⟩
  · rw [Fintype.prod_sum_type]
    exact congrArg₂ (· * ·) (hs U h) (hs' U h)
  · rw [val_mul hJ]
    simp only [e z J hJ, e' z J hJ, cst_eq, map_mul, Units.val_mul]
    ring

theorem HE.one : HE R E F L (fun _ _ _ => 1) (fun _ _ => 1) 1 :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L (Y := (TF (R := R) E).left),
    fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun U _ h => Fintype.prod_empty _, fun z J _ => by rw [val_one, cst_eq, map_one, Units.val_one, _root_.mul_one]⟩

theorem HE.congr {σ σ' : CoefVal.FS R F X} {f f'} {x : F} (H : HE R E F L σ f x)
    (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h) (hf : ∀ z J, Good L z J → f' z J = f z J) :
    HE R E F L σ' f' x := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  exact ⟨K, _, φ, ε, t, ht, fun U _ h => (hs U h).trans (hσ U h), fun z J hJ => (hf z J hJ).trans (e z J hJ)⟩

theorem HE.pow {σ : CoefVal.FS R F X} {f} {x : F} (H : HE R E F L σ f x) (n : ℕ) :
    HE R E F L (fun U _ h => σ U h ^ n) (fun z J => f z J ^ n) (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using HE.one
  | succ n ih => simpa only [pow_succ] using ih.mul H

theorem HE.ratio (hL : L.IsLB) {σ σ' : CoefVal.FS R F X} {f f'} {x x' : F} (H : HE R E F L σ f x)
    (H' : HE R E F L σ' f' x') (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h) :
    ∃ a : E, ∀ z J, Good L z J → cst F z x' * f z J = cst F z (x * algebraMap E F a) * f' z J := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  have hu := mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ ht')
  obtain ⟨a, hav⟩ := sec_rat R E F hL (Geo.Tor.genSec _ hu) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [hs, hs', hσ, mul_inv_cancel])
  refine ⟨a, fun z J hJ => ?_⟩
  have b := hav z J hJ
  rw [sval_genSec _ hu _ z hJ, val_mul hJ, val_inv] at b
  have c : (val t (ιE R E F).left z J).val = cst F z (algebraMap E F a) * (val t' (ιE R E F).left z J).val := by
    rw [← b, Units.val_mul, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
  rw [e z J hJ, e' z J hJ, c]
  simp only [cst_eq, map_mul]
  ring

variable {K : Type} [Fintype K] {ε : K → ℤ}

theorem he_gen {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (r₀ : (TF (R := R) E).left ⟶ Y) {r : (TF (R := R) F).left ⟶ Y} (hr : (ιE R E F).left ≫ r₀ = r) :
    HE R E F L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => (val t r z J).val) 1 := by
  subst hr
  exact ⟨K, _, _, ε, LB.pullGen L φ ε t r₀, pullGen_isGen _ _ _ _ ht _, fun U _ h => by simp only [Category.assoc],
    fun z J hJ => by rw [val_pull hJ, cst_eq, map_one, _root_.one_mul]⟩

theorem he_sec (hL : L.IsLB) {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (r₀ : (TF (R := R) E).left ⟶ Y) {r : (TF (R := R) F).left ⟶ Y} (hr : (ιE R E F).left ≫ r₀ = r) :
    ∃ a : E, HE R E F L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => sval s r z J) (algebraMap E F a) := by
  subst hr
  obtain ⟨t, ht⟩ := exists_gen_of_local (V := E) L hL (fun i => r₀ ≫ φ i) ε
  have hi := invGen_isGen _ _ _ _ ht
  obtain ⟨a, hav⟩ := sec_rat R E F hL (pullMulSec s r₀ _ hi) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
  refine ⟨a, K, _, _, ε, t, ht, fun U _ h => by simp only [Category.assoc], fun z J hJ => ?_⟩
  have b := hav z J hJ
  rw [sval_pullMulSec _ _ _ hi _ z hJ, val_inv] at b
  rw [← b, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem exists_he (hL : L.IsLB) {φ : K → ((TF (R := R) F).left ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (hφ : ∀ i, ∃ ψ, φ i = (ιE R E F).left ≫ ψ) :
    ∃ x : F, x ≠ 0 ∧ HE R E F L (fun _ _ h => ∏ i, h (φ i) ^ ε i) (fun z J => (val t (𝟙 _) z J).val) x := by
  choose φ₀ h₀ using hφ
  obtain ⟨t₀, ht₀⟩ := exists_gen_of_local (V := E) L hL φ₀ ε
  obtain ⟨c, hc, e⟩ := exists_ratio hL t ht (LB.pullGen L _ _ t₀ (ιE R E F).left) (pullGen_isGen _ _ _ _ ht₀ _)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [h₀])
  refine ⟨c, hc, K, _, φ₀, ε, t₀, ht₀, fun U _ h => by simp only [h₀], fun z J hJ => ?_⟩
  have := e (TF (R := R) F).left (𝟙 (TF (R := R) F).left) z J hJ
  rw [val_pull hJ, Category.id_comp] at this
  exact this

end

theorem exists_adjoin {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (A : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType A.hom] (b : TF (R := R) F ⟶ A) :
    ∃ (T : Finset F) (b₁ : TF (R := R) (IntermediateField.adjoin (FractionRing R) (T : Set F)) ⟶ A),
      ιE R _ F ≫ b₁ = b := by
  classical
  let a : Spec (CommRingCat.of F) ⟶ A.left := b.left
  obtain ⟨B, i, _, t, ht⟩ : ∃ (B : CommRingCat.{0}) (i : Spec B ⟶ A.left) (_ : IsOpenImmersion i)
      (t : Spec B), i t = a (IsLocalRing.closedPoint F) := by
    obtain ⟨n, t, ht⟩ := A.left.affineCover.exists_eq (a (IsLocalRing.closedPoint F))
    exact ⟨_, A.left.affineCover.f n, A.left.affineCover.map_prop n, t, ht⟩
  have hr : Set.range a ⊆ Set.range i := by
    rintro _ ⟨u, rfl⟩
    exact ⟨t, ht.trans (congrArg a (Subsingleton.elim _ _))⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift i a hr)
  have hφa : Spec.map φ ≫ i = a := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (show Spec B ⟶ Spec (CommRingCat.of R) from i ≫ A.hom)
  have h₂ : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h₂
  have hc : ψ ≫ φ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) F) := by
    rw [← Spec.map_inj, Spec.map_comp, hψ, ← Category.assoc, hφa, Spec.map_comp]
    exact Over.w b
  let : Algebra R B := ψ.hom.toAlgebra
  obtain ⟨s, hs⟩ : (⊤ : Subalgebra R B).FG := (show Algebra.FiniteType R B from h₂).out
  let K := IntermediateField.adjoin (FractionRing R) ((s.image φ.hom : Finset F) : Set F)
  have hm : ∀ x : B, φ.hom x ∈ K := fun x => by
    have hx : x ∈ Algebra.adjoin R (s : Set B) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ (by simpa using ⟨x, hx, rfl⟩)
    | algebraMap r =>
      have e : φ.hom (algebraMap R B r) = algebraMap (FractionRing R) F (algebraMap R _ r) := congr($hc r)
      rw [e]; exact K.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have e : (ιE R K F).left ≫ Spec.map (CommRingCat.ofHom (φ.hom.codRestrict K hm)) ≫ i = b.left := by
    refine Eq.trans ?_ hφa
    show Spec.map _ ≫ _ = _
    rw [← Spec.map_comp_assoc]
    rfl
  refine ⟨s.image φ.hom, Over.homMk (Spec.map (CommRingCat.ofHom (φ.hom.codRestrict K hm)) ≫ i) ?_,
    Over.OverMorphism.ext e⟩
  apply ι_inj R K F
  show (ιE R K F).left ≫ _ ≫ _ = (ιE R K F).left ≫ _
  rw [← Category.assoc, e, Over.w, Over.w]

end GlobalTheory.UT.CoefField
end
