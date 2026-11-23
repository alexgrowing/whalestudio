import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
open GlobalTheory.AbLaw (rs pw)

noncomputable section

namespace GlobalTheory.VolFin

variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

def gen (U : X.Opens) (h : genericPoint X ∈ U) : Γ(X, U) →+* X.functionField :=
  (X.presheaf.germ U _ h).hom

theorem generic_mem {U : X.Opens} {x : X} (hx : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 ⟨x, trivial, hx⟩

theorem gen_rs {U V : X.Opens} (h : V ≤ U) (hV : genericPoint X ∈ V) (a : Γ(X, U)) :
    gen V hV (rs X h a) = gen U (h hV) a :=
  X.presheaf.germ_res_apply (homOfLE h) _ hV a

theorem gen_injective (U : X.Opens) (h : genericPoint X ∈ U) : Function.Injective (gen U h) :=
  germ_injective_of_isIntegral X _ h

theorem eq_of_gen {U : X.Opens} {a b : Γ(X, U)} (h : ∀ hU, gen U hU a = gen U hU b) : a = b := by
  by_cases hU : genericPoint X ∈ U
  · exact gen_injective U hU (h hU)
  · have hb : U = ⊥ := by
      ext x
      exact ⟨fun hx => (hU (generic_mem hx)).elim, fun hx => hx.elim⟩
    subst hb
    exact Subsingleton.elim _ _

theorem exists_gen_eq (U : X.Opens) (f : X.functionField)
    (hf : ∀ x ∈ U, ∃ (V : X.Opens) (hx : x ∈ V) (a : Γ(X, V)), gen V (generic_mem hx) a = f) :
    ∃ a : Γ(X, U), ∀ hU, gen U hU a = f := by
  choose V hx a ha using hf
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun x : U => U ⊓ V x.1 x.2) U
    (fun x => homOfLE inf_le_left)
    (fun x hxU => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hxU, hx x hxU⟩)
    (fun x => rs X inf_le_right (a x.1 x.2))
    (fun x y => eq_of_gen (X := X) fun h =>
      ((gen_rs inf_le_left h _).trans ((gen_rs _ _ _).trans (ha _ _))).trans
        ((gen_rs inf_le_right h _).trans ((gen_rs _ _ _).trans (ha _ _))).symm)
  refine ⟨s, fun hU => ?_⟩
  have h1 : rs X (inf_le_left : U ⊓ V _ hU ≤ U) s = rs X inf_le_right (a _ hU) := hs ⟨_, hU⟩
  exact (gen_rs (inf_le_left : U ⊓ V _ hU ≤ U) ⟨hU, hx _ hU⟩ s).symm.trans
    ((congrArg _ h1).trans ((gen_rs _ _ _).trans (ha _ _)))

def tr (N : LB X) (i j : N.ι) (hi : genericPoint X ∈ N.U i) (hj : genericPoint X ∈ N.U j) :
    X.functionField := gen (N.U i ⊓ N.U j) ⟨hi, hj⟩ (N.g i j).val

theorem tr_mul {N : LB X} (hN : N.IsLB) (i j k : N.ι) (hi) (hj) (hk) :
    tr N i j hi hj * tr N j k hj hk = tr N i k hi hk := by
  have h := congrArg (fun u => gen (N.U i ⊓ N.U j ⊓ N.U k) ⟨⟨hi, hj⟩, hk⟩ (Units.val u))
    (hN.cocycle i j k)
  simp only [Units.val_mul, map_mul] at h
  exact (congrArg₂ (· * ·) (gen_rs _ _ _) (gen_rs _ _ _)).symm.trans (h.trans (gen_rs _ _ _))

theorem tr_ne_zero (N : LB X) (i j : N.ι) (hi) (hj) : tr N i j hi hj ≠ 0 :=
  ((N.g i j).isUnit.map _).ne_zero

theorem tr_self {N : LB X} (hN : N.IsLB) (i : N.ι) (hi) : tr N i i hi hi = 1 :=
  mul_left_cancel₀ (tr_ne_zero N i i hi hi) ((tr_mul hN i i i hi hi hi).trans (_root_.mul_one _).symm)

theorem gen_sec {N : LB X} (s : N.Sec) (i j : N.ι) (hi) (hj) :
    gen _ hi (s.f i) = tr N i j hi hj * gen _ hj (s.f j) := by
  have h := congrArg (gen (N.U i ⊓ N.U j) ⟨hi, hj⟩) (s.compat i j)
  rw [map_mul] at h
  exact (gen_rs _ _ _).symm.trans (h.trans (congrArg _ (gen_rs _ _ _)))

theorem gen_constFn (p : X ⟶ Sp K) (U : X.Opens) (h) (a : K) :
    gen U h (constFn p U a) = gen ⊤ trivial (constFn p ⊤ a) := by
  rw [← gen_rs le_top h]
  congr 1
  exact (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := ⊤) (fun _ _ => trivial) (homOfLE (le_top : U ≤ ⊤)).op)).symm

theorem exists_sec {N : LB X} (hN : N.IsLB) (j₀ : N.ι) (h₀) {κ : Type} (W : κ → X.Opens)
    (c : κ → N.ι) (hW : ∀ i, W i ≤ N.U (c i)) (hη : ∀ i, genericPoint X ∈ W i)
    (hc : ∀ x, ∃ i, x ∈ W i) (f : X.functionField)
    (hf : ∀ i, ∃ a, gen (W i) (hη i) a = f * tr N (c i) j₀ (hW i (hη i)) h₀) :
    ∃ s : N.Sec, gen _ h₀ (s.f j₀) = f := by
  have H : ∀ j, ∃ a : Γ(X, N.U j), ∀ hj, gen _ hj a = tr N j j₀ hj h₀ * f := by
    intro j
    by_cases hj : genericPoint X ∈ N.U j
    · obtain ⟨a, ha⟩ := exists_gen_eq (N.U j) (tr N j j₀ hj h₀ * f) fun x hx => by
        obtain ⟨i, hi⟩ := hc x
        obtain ⟨a, ha⟩ := hf i
        refine ⟨N.U j ⊓ W i, ⟨hx, hi⟩,
          rs X (inf_le_inf_left _ (hW i)) (N.g j (c i)).val * rs X inf_le_right a, ?_⟩
        rw [map_mul, gen_rs, gen_rs, ha, ← tr_mul hN j (c i) j₀ hj (hW i (hη i)) h₀]
        unfold tr
        ring
      exact ⟨a, ha⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose a ha using H
  refine ⟨⟨a, fun i j => eq_of_gen fun h => ?_⟩, ?_⟩
  · rw [map_mul]
    refine (gen_rs _ _ _).trans ((ha i h.1).trans ?_)
    rw [← tr_mul hN i j j₀ h.1 h.2 h₀, _root_.mul_assoc, ← ha j h.2]
    exact congrArg _ (gen_rs (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) h (a j)).symm
  · rw [ha, tr_self hN, _root_.one_mul]

theorem lineBundle_global_sections_functionField_iff [Algebra K X.functionField] (p : X ⟶ Sp K)
    (halg : ∀ a, algebraMap K X.functionField a = gen ⊤ trivial (constFn p ⊤ a))
    {N : LB X} (hN : N.IsLB) (j₀ : N.ι) (h₀) {κ : Type} (W : κ → X.Opens)
    (c : κ → N.ι) (hW : ∀ i, W i ≤ N.U (c i)) (hη : ∀ i, genericPoint X ∈ W i)
    (hc : ∀ x, ∃ i, x ∈ W i) (V : Submodule K X.functionField)
    (hV : ∀ f, f ∈ V ↔ ∀ i, ∃ a, gen (W i) (hη i) a = f * tr N (c i) j₀ (hW i (hη i)) h₀) (r : ℕ) :
    SectionsHaveFiniteDimension p N r ↔ Module.Finite K V ∧ Module.finrank K V = r := by
  let θ : N.Sec → V := fun s => ⟨gen _ h₀ (s.f j₀), (hV _).2 fun i =>
    ⟨rs X (hW i) (s.f (c i)), by rw [gen_rs, gen_sec s (c i) j₀ _ h₀, _root_.mul_comm]⟩⟩
  have hθ : Function.Surjective θ := fun f => by
    obtain ⟨s, hs⟩ := exists_sec hN j₀ h₀ W c hW hη hc f ((hV f).1 f.2)
    exact ⟨s, Subtype.ext hs⟩
  have key : ∀ (s : Fin r → N.Sec) (t : N.Sec) (a : Fin r → K),
      (∀ j, t.f j = ∑ i, constFn p _ (a i) * (s i).f j) ↔ ∑ i, a i • θ (s i) = θ t := by
    intro s t a
    have e : ∀ j hj, gen _ hj (∑ i, constFn p _ (a i) * (s i).f j) =
        tr N j j₀ hj h₀ * ((∑ i, a i • θ (s i) : V) : X.functionField) := by
      intro j hj
      rw [map_sum, AddSubmonoidClass.coe_finset_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, gen_constFn, ← halg, gen_sec (s i) j j₀ hj h₀, SetLike.val_smul, Algebra.smul_def]
      ring
    constructor
    · intro h
      apply Subtype.ext
      have := e j₀ h₀
      rw [tr_self hN, _root_.one_mul, ← h j₀] at this
      exact this.symm
    · intro h j
      refine eq_of_gen fun hj => ?_
      rw [e, h, gen_sec t j j₀ hj h₀]
  constructor
  · rintro ⟨s, hs⟩
    have hb : Function.Bijective (Fintype.linearCombination K fun i => θ (s i)) := by
      rw [Function.bijective_iff_existsUnique]
      intro f
      obtain ⟨t, rfl⟩ := hθ f
      simpa only [key, Fintype.linearCombination_apply] using hs t
    have E := LinearEquiv.ofBijective _ hb
    exact ⟨Module.Finite.equiv E, by rw [← E.finrank_eq, Module.finrank_fin_fun]⟩
  · rintro ⟨hf, hr⟩
    let b := Module.finBasisOfFinrankEq K V hr
    choose s hs using fun i => hθ (b i)
    refine ⟨s, fun t => ?_⟩
    simp only [key, hs]
    refine ⟨b.equivFun (θ t), b.sum_equivFun _, fun a ha => ?_⟩
    rw [← ha, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

def ffMap (ψ : X ⟶ Y) (hψ : ψ (genericPoint X) = genericPoint Y) :
    Y.functionField →+* X.functionField :=
  (Y.presheaf.stalkSpecializes (x := ψ (genericPoint X)) (y := genericPoint Y)
    (hψ ▸ specializes_rfl) ≫ ψ.stalkMap (genericPoint X)).hom

theorem ffMap_gen (ψ : X ⟶ Y) (hψ) (U : Y.Opens) (h) (h') (a : Γ(Y, U)) :
    ffMap ψ hψ (gen U h a) = gen (ψ ⁻¹ᵁ U) h' ((ψ.app U).hom a) := by
  have := Y.presheaf.germ_stalkSpecializes_apply (x := ψ (genericPoint X)) h
    (hψ ▸ specializes_rfl) a
  exact (congrArg (ψ.stalkMap (genericPoint X)).hom this).trans
    (ψ.germ_stalkMap_apply U _ h' a)

omit [IsIntegral Y] in
theorem tr_linComb (N : LB Y) (ψ : X ⟶ Y) (ε : ℤ) (e : ℕ) (hε : ε = e) (J J' : PUnit → N.ι)
    (h) (h') (h'') :
    tr (LB.LinComb N (K := PUnit) (fun _ => ψ) (fun _ => ε)) J J' h h' =
      gen (ψ ⁻¹ᵁ (N.U (J ⟨⟩) ⊓ N.U (J' ⟨⟩))) h'' ((ψ.app _).hom (N.g _ _).val) ^ e := by
  subst hε
  unfold tr LB.LinComb
  dsimp only
  rw [Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  exact congrArg (· ^ e) (gen_rs _ _ _)

theorem tr_lbPow (N : LB X) (e : ℕ) (J J' : PUnit → N.ι) (h) (h') (k) (k') :
    tr (lbPow N e) J J' h h' = tr N (J ⟨⟩) (J' ⟨⟩) k k' ^ e := by
  rw [tr_linComb N (𝟙 X) e e rfl J J' h h' ⟨k, k'⟩]
  rfl

theorem tr_pull (N : LB Y) (ψ : X ⟶ Y) (hψ) (J J' : PUnit → N.ι) (h) (h') (k) (k') :
    tr (N.pull ψ) J J' h h' = ffMap ψ hψ (tr N (J ⟨⟩) (J' ⟨⟩) k k') := by
  have h'' : genericPoint X ∈ ψ ⁻¹ᵁ (N.U (J ⟨⟩) ⊓ N.U (J' ⟨⟩)) :=
    ⟨LB.wchart_le N _ J ⟨⟩ h, LB.wchart_le N _ J' ⟨⟩ h'⟩
  rw [tr_linComb N ψ 1 1 rfl J J' h h' h'', pow_one]
  exact (ffMap_gen ψ hψ _ _ _ _).symm

theorem tr_pw (N : LB X) (d : ℕ) (i j : N.ι) (h) (h') :
    tr (pw N d) i j h h' = tr N i j h h' ^ d := by
  unfold tr pw
  dsimp only
  rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow]

theorem mem_basicOpen_iff {U : X.Opens} (h) (a : Γ(X, U)) :
    genericPoint X ∈ X.basicOpen a ↔ gen U h a ≠ 0 :=
  (X.mem_basicOpen a _ h).trans (isUnit_iff_ne_zero (G₀ := X.functionField))

theorem eventually_mul_pow {W D : X.Opens} (hW : IsAffineOpen W) (h) (u : Γ(X, W))
    (hu : gen W h u ≠ 0) (hD : X.basicOpen u ≤ D) (hD') (a : Γ(X, D)) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ b, gen W h b = gen D hD' a * gen W h u ^ n := by
  have := hW.isLocalization_basicOpen u
  have hb := (mem_basicOpen_iff h u).2 hu
  obtain ⟨⟨b, _, m, rfl⟩, hm⟩ := IsLocalization.surj (Submonoid.powers u) (rs X hD a)
  have h1 : gen D hD' a * gen W h u ^ m = gen W h b := by
    have h2 := congrArg (gen _ hb) hm
    rw [map_mul, gen_rs] at h2
    have h3 : ∀ x : Γ(X, W), gen _ hb (algebraMap Γ(X, W) Γ(X, X.basicOpen u) x) = gen W h x :=
      fun x => gen_rs (X.basicOpen_le u) hb x
    rw [h3, h3, map_pow] at h2
    exact h2
  filter_upwards [Filter.eventually_ge_atTop m] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact ⟨b * u ^ k, by rw [map_mul, map_pow, ← h1, pow_add, _root_.mul_assoc]⟩

theorem exists_frac {D : X.Opens} (hD : IsAffineOpen D) (h) (t : X.functionField) :
    ∃ a b : Γ(X, D), gen D h b ≠ 0 ∧ t * gen D h b = gen D h a := by
  haveI : Nonempty D := ⟨⟨_, h⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X D hD
  obtain ⟨⟨a, b, hb⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, D)) t
  exact ⟨a, b, fun h0 => nonZeroDivisors.ne_zero hb (gen_injective D h (h0.trans (map_zero _).symm)),
    hab⟩

end GlobalTheory.VolFin
