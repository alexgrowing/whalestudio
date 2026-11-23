import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RankinSelbergEulerProduct

theorem finprod_split {α M : Type*} [CommMonoid M] (f : α → M) (S : Finset α)
    (hf : (Function.mulSupport f).Finite) :
    ∏ᶠ v, f v = (∏ v : S, f v.1) * ∏ᶠ v : {v // v ∉ S}, f v.1 := by
  have h := finprod_mem_inter_mul_diff' (f := f) (s := Set.univ) (t := (S : Set α))
    (hf.subset Set.inter_subset_right)
  simp only [Set.univ_inter, finprod_mem_univ] at h
  rw [← h, finprod_mem_coe_finset, Finset.prod_coe_sort S f]
  congr 1
  have e : Set.univ \ (S : Set α) = {v | v ∉ S} := by ext; simp
  rw [e, ← finprod_set_coe_eq_finprod_mem]
  rfl

theorem finAt_diag (v : Pl) (a : Jd) : finAt v (dg2 a 1) = dg2 (lc v a) 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem lc_symm (v : Pl) (p : (InfiniteAdeleRing ℚ)ˣ × Afˣ) :
    lc v ((IdeleGroup.prodEquiv ℚ).symm p) = lf v p.2 := by
  apply Units.ext
  change (((IdeleGroup.prodEquiv ℚ).symm p : Jd) : 𝔸[ℚ]).2 v = _
  rw [GroundTheory.Automorphic.GodementSection.val_symm_snd]
  rfl

theorem realPart_mul (g h : G2) : realPart (g * h) = realPart g * realPart h := by
  simp only [GroundTheory.Automorphic.GL2Classical.realPart, map_mul, Prod.fst_mul]

theorem realPart_eq_of_infAt {h : G2} (hh : ∀ w, infAt w h = 1) : realPart h = 1 := by
  have : (AdelicGLn.prodEquiv ℚ 2 h).1 = 1 := by
    apply Units.ext
    refine Matrix.ext fun i j => funext fun w => ?_
    have h2 : infAt w h i j = ((1 : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
      rw [hh w]
    rw [GroundTheory.Automorphic.Reduction.infAt_apply] at h2
    change (h i j).1 w = _
    rw [h2]
    fin_cases i <;> fin_cases j <;> simp <;> rfl
  simp [GroundTheory.Automorphic.GL2Classical.realPart, this]

theorem realPart_diag (a : (InfiniteAdeleRing ℚ)ˣ) (b b' : Afˣ) :
    realPart (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, b)) 1) =
      realPart (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, b')) 1) := by
  have : (AdelicGLn.prodEquiv ℚ 2 (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, b)) 1)).1 =
      (AdelicGLn.prodEquiv ℚ 2 (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, b')) 1)).1 := by
    apply Units.ext
    ext i j
    change ((dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, b)) 1 : G2) i j).1 = ((dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, b')) 1 : G2) i j).1
    fin_cases i <;> fin_cases j
    · change (((IdeleGroup.prodEquiv ℚ).symm (a, b) : Jd) : 𝔸[ℚ]).1 = (((IdeleGroup.prodEquiv ℚ).symm (a, b') : Jd) : 𝔸[ℚ]).1
      rw [GroundTheory.Automorphic.GodementSection.val_symm_fst, GroundTheory.Automorphic.GodementSection.val_symm_fst]
    all_goals rfl
  simp only [GroundTheory.Automorphic.GL2Classical.realPart, this]

open GroundTheory.Automorphic.GodementSection (infChar finChar infMod finMod) in
theorem lf_eq_finiteComponent (v : Pl) (b : Afˣ) : lf v b = IdeleGroup.finiteComponent v b := by
  apply Units.ext
  rw [IdeleGroup.coe_finiteComponent]
  rfl

theorem mulSupport_char_finite (c : HeckeCharacter ℚ) (b : Afˣ) :
    (Function.mulSupport fun v : Pl => ((localChar c v (lf v b) : ℂˣ) : ℂ)).Finite := by
  simpa only [lf_eq_finiteComponent, GroundTheory.Automorphic.GodementSection.coe_localChar] using
    c.finite_mulSupport_localComponent b

theorem toIdele_symm (c : HeckeCharacter ℚ) (a : (InfiniteAdeleRing ℚ)ˣ) (b : Afˣ) :
    (c.toIdele ((IdeleGroup.prodEquiv ℚ).symm (a, b)) : ℂ) =
      (GodementSection.infChar c a : ℂ) * ∏ᶠ v : Pl, ((localChar c v (lf v b) : ℂˣ) : ℂ) := by
  rw [GroundTheory.Automorphic.GodementSection.toIdele_eq_finChar_mul_infChar,
    GroundTheory.Automorphic.GodementSection.toInfinite_symm, GroundTheory.Automorphic.GodementSection.toFinite_symm]
  have h : ((GodementSection.finChar c b : Circle) : ℂ) = ∏ᶠ v : Pl, ((localChar c v (lf v b) : ℂˣ) : ℂ) := by
    simp only [lf_eq_finiteComponent, GroundTheory.Automorphic.GodementSection.coe_localChar]
    exact c.toIdele_ofFinite_eq_finprod b
  rw [Circle.coe_mul, h, mul_comm]

theorem mulSupport_norm_finite (b : Afˣ) :
    (Function.mulSupport fun v : Pl => ‖((lf v b : (Qv v)ˣ) : Qv v)‖).Finite :=
  IdeleGroup.finite_mulSupport_norm (IdeleGroup.ofFinite b)

theorem mp_eq (v : Pl) (a : (Qv v)ˣ) (z : ℂ) : mp a z = ((‖(a : Qv v)‖ : ℝ) : ℂ) ^ z := by
  rw [mp, GroundTheory.Automorphic.GodementSection.modulus_adicCompletion]

theorem mulSupport_mp_finite (b : Afˣ) (z : ℂ) :
    (Function.mulSupport fun v : Pl => mp (lf v b) z).Finite := by
  refine (mulSupport_norm_finite b).subset fun v hv h => hv ?_
  change mp (lf v b) z = 1
  have h' : ‖((lf v b : (Qv v)ˣ) : Qv v)‖ = 1 := h
  rw [mp_eq, h']
  simp

theorem finMod_cpow (b : Afˣ) (z : ℂ) :
    ((GodementSection.finMod b : ℝ) : ℂ) ^ z = ∏ᶠ v : Pl, mp (lf v b) z := by
  have h1 := mulSupport_norm_finite b
  have h2 := mulSupport_mp_finite b z
  have e : GodementSection.finMod b = ∏ᶠ v : Pl, ‖((lf v b : (Qv v)ˣ) : Qv v)‖ := rfl
  rw [e, finprod_eq_prod_of_mulSupport_subset (s := h1.toFinset ∪ h2.toFinset) _ (by
      intro v hv; simp only [Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inl hv),
    finprod_eq_prod_of_mulSupport_subset (s := h1.toFinset ∪ h2.toFinset) (fun v : Pl => mp (lf v b) z) (by
      intro v hv; simp only [Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inr hv),
    GroundTheory.Automorphic.GodementSection.ofReal_prod_cpow _ _ (fun _ => norm_nonneg _)]
  exact Finset.prod_congr rfl fun v _ => (mp_eq v _ z).symm

theorem modPow_symm (a : (InfiniteAdeleRing ℚ)ˣ) (b : Afˣ) (z : ℂ) :
    modPow ((IdeleGroup.prodEquiv ℚ).symm (a, b)) z =
      ((GodementSection.infMod a : ℝ) : ℂ) ^ z * ∏ᶠ v : Pl, mp (lf v b) z := by
  rw [GroundTheory.Automorphic.GodementSection.modPow_eq, GroundTheory.Automorphic.GodementSection.toInfinite_symm,
    GroundTheory.Automorphic.GodementSection.toFinite_symm, finMod_cpow]

section Loc
variable {N : ℕ} {ω : HeckeCharacter ℚ} {W : G2 → ℂ} {μ₁ μ₂ : ∀ v : Pl, (Qv v)ˣ →* ℂˣ}
  {φ₀ : ∀ v : Pl, (Fin 2 → Qv v) → ℂ}

theorem w_inv (hB : B0) (hM : M0) (hm : Mod N ω W μ₁ μ₂ φ₀) {v : Pl} (hv : ¬ pOf v ∣ N)
    {x : GL (Fin 2) (Qv v)} (hx : x ∈ integralGL (Qv v) 2) (g : GL (Fin 2) (Qv v)) :
    W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) (g * x) = W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) g := by
  obtain ⟨h1, h2, h3⟩ := hm.good v hv
  rw [h3]
  exact (hM (Qv v) (localAdelicChar ℚ v) (hB.1 v).1 (μ₁ v) (μ₂ v) (hm.u₁ v) (hm.u₂ v) h1 h2).2.2.1 x hx g

theorem w_one (hB : B0) (hM : M0) (hm : Mod N ω W μ₁ μ₂ φ₀) {v : Pl} (hv : ¬ pOf v ∣ N)
    {x : GL (Fin 2) (Qv v)} (hx : x ∈ integralGL (Qv v) 2) :
    W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) x = 1 := by
  have := w_inv hB hM hm hv hx 1
  rwa [one_mul, hm.one v] at this

theorem mulSupport_w_finite (hB : B0) (hM : M0) (hm : Mod N ω W μ₁ μ₂ φ₀) {S : Finset Pl}
    (hS : ∀ v, pOf v ∣ N → v ∈ S) (g : G2) :
    (Function.mulSupport fun v : Pl => W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) (finAt v g)).Finite := by
  have hf := hB.2.2.2.2.2.2.1 g
  refine (S.finite_toSet.union hf).subset fun v hv => ?_
  by_contra hc
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hc
  exact hv (w_one hB hM hm (fun h => hc.1 (hS v h)) hc.2)
end Loc

def Aloc (μ₁ μ₂ : ∀ v : Pl, (Qv v)ˣ →* ℂˣ) (φ₀ : ∀ v : Pl, (Fin 2 → Qv v) → ℂ) (c : HeckeCharacter ℚ) (s : ℂ)
    (S : Finset Pl) (x : ∀ v : S, Qv v.1) (κ : G2) (v : S) (a : (Qv v.1)ˣ) : ℂ :=
  W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1) (dg2 a 1 * finAt v.1 κ) *
    conj (W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1) (dg2 a 1 * finAt v.1 κ * uni2 (x v))) *
    ((localChar c v.1 a : ℂˣ) : ℂ) * mp a (s - 1)

def Gloc (μ₁ μ₂ : ∀ v : Pl, (Qv v)ˣ →* ℂˣ) (c : HeckeCharacter ℚ) (s : ℂ) (v : Pl) (a : (Qv v)ˣ) : ℂ :=
  W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) ind0 (dg2 a 1) *
    conj (W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) ind0 (dg2 a 1)) *
    ((localChar c v a : ℂˣ) : ℂ) * mp a (s - 1)

section Glob
variable {N : ℕ} {ω : HeckeCharacter ℚ} {W : G2 → ℂ} {μ₁ μ₂ : ∀ v : Pl, (Qv v)ˣ →* ℂˣ}
  {φ₀ : ∀ v : Pl, (Fin 2 → Qv v) → ℂ}

theorem local_prod (hB : B0) (hM : M0) (hm : Mod N ω W μ₁ μ₂ φ₀) {S : Finset Pl}
    (hS : ∀ v, pOf v ∣ N → v ∈ S) (c : HeckeCharacter ℚ) {x : ∀ v : S, Qv v.1} {h : G2} (hxh : IsUn S x h)
    (s : ℂ) {κ : G2} (hκ : ∀ v, finAt v κ ∈ integralGL (Qv v) 2) (a : (InfiniteAdeleRing ℚ)ˣ) (b : Afˣ)
    {g : G2} (hg : g = dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, b)) 1 * κ) :
    (∏ᶠ v : Pl, W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) (finAt v g)) *
      conj (∏ᶠ v : Pl, W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) (finAt v (g * h))) *
      (∏ᶠ v : Pl, ((localChar c v (lf v b) : ℂˣ) : ℂ)) * (∏ᶠ v : Pl, mp (lf v b) (s - 1)) =
    (∏ v : S, Aloc μ₁ μ₂ φ₀ c s S x κ v (lf v.1 b)) * ∏ᶠ v : {v : Pl // v ∉ S}, Gloc μ₁ μ₂ c s v.1 (lf v.1 b) := by
  have f1 := mulSupport_w_finite hB hM hm hS g
  have f2 := mulSupport_w_finite hB hM hm hS (g * h)
  have f3 := mulSupport_char_finite c b
  have f4 := mulSupport_mp_finite b (s - 1)
  have f2' : (Function.mulSupport fun v : Pl => conj (W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) (finAt v (g * h)))).Finite := by
    refine f2.subset fun v hv hc => hv ?_
    change conj _ = (1 : ℂ)
    rw [show W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) (finAt v (g * h)) = 1 from hc, map_one]
  have f12 := (f1.union f2').subset (Function.mulSupport_mul _ _)
  have f123 := (f12.union f3).subset (Function.mulSupport_mul _ _)
  have f1234 := (f123.union f4).subset (Function.mulSupport_mul _ _)
  rw [map_finprod (starRingEnd ℂ) f2, ← finprod_mul_distrib f1 f2', ← finprod_mul_distrib f12 f3,
    ← finprod_mul_distrib f123 f4, finprod_split _ S f1234]
  have hfin : ∀ v, finAt v g = dg2 (lf v b) 1 * finAt v κ := fun v => by
    rw [hg, GroundTheory.Automorphic.Reduction.finAt_mul, finAt_diag, lc_symm]
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [Aloc, GroundTheory.Automorphic.Reduction.finAt_mul, hfin, hxh.1 v]
  · refine finprod_congr fun v => ?_
    have hv : ¬ pOf v.1 ∣ N := fun h' => v.2 (hS _ h')
    rw [Gloc, GroundTheory.Automorphic.Reduction.finAt_mul, hxh.2.1 v.1 v.2, mul_one, hfin,
      w_inv hB hM hm hv (hκ v.1), (hm.good v.1 hv).2.2]

theorem pointwise (hB : B0) (hM : M0) (hm : Mod N ω W μ₁ μ₂ φ₀)
    (hE : ∀ g : G2, W g = W (realEmb (realPart g)) *
      ∏ᶠ v : Pl, W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) (finAt v g)) {S : Finset Pl}
    (hS : ∀ v, pOf v ∣ N → v ∈ S) (c : HeckeCharacter ℚ) {x : ∀ v : S, Qv v.1} {h : G2} (hxh : IsUn S x h)
    (s : ℂ) {κ : G2} (hκ : ∀ v, finAt v κ ∈ integralGL (Qv v) 2) (a : (InfiniteAdeleRing ℚ)ˣ) (b : Afˣ) :
    W (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, b)) 1 * κ) * conj (W (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, b)) 1 * κ * h)) *
        (c.toIdele ((IdeleGroup.prodEquiv ℚ).symm (a, b)) : ℂ) * modPow ((IdeleGroup.prodEquiv ℚ).symm (a, b)) (s - 1) =
      ((fun y => W (realEmb y) * conj (W (realEmb y)))
          (realPart (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, 1)) 1 * κ)) *
        (GodementSection.infChar c a : ℂ) * ((GodementSection.infMod a : ℝ) : ℂ) ^ (s - 1)) *
      ((∏ v : S, Aloc μ₁ μ₂ φ₀ c s S x κ v (lf v.1 b)) * ∏ᶠ v : {v : Pl // v ∉ S}, Gloc μ₁ μ₂ c s v.1 (lf v.1 b)) := by
  obtain ⟨g, hg⟩ : ∃ g, g = dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, b)) 1 * κ := ⟨_, rfl⟩
  have hr : realPart (g * h) = realPart g := by
    rw [realPart_mul, realPart_eq_of_infAt hxh.2.2, mul_one]
  have hr' : realPart (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, 1)) 1 * κ) = realPart g := by
    rw [hg, realPart_mul, realPart_mul, realPart_diag a b 1]
  rw [← local_prod hB hM hm hS c hxh s hκ a b hg, ← hg, hr', hE g, hE (g * h), hr, toIdele_symm, modPow_symm, map_mul]
  ring

theorem Ag_factor (hB : B0) (hM : M0) (hm : Mod N ω W μ₁ μ₂ φ₀)
    (hE : ∀ g : G2, W g = W (realEmb (realPart g)) *
      ∏ᶠ v : Pl, W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) (finAt v g)) {S : Finset Pl}
    (hS : ∀ v, pOf v ∣ N → v ∈ S) (c : HeckeCharacter ℚ) {x : ∀ v : S, Qv v.1} {h : G2} (hxh : IsUn S x h)
    (s : ℂ) {κ : G2} (hκ : ∀ v, finAt v κ ∈ integralGL (Qv v) 2) :
    Ag (fun g => W g * conj (W (g * h))) c s κ =
      (∫ a : (InfiniteAdeleRing ℚ)ˣ, (fun y => W (realEmb y) * conj (W (realEmb y)))
          (realPart (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, 1)) 1 * κ)) *
        (GodementSection.infChar c a : ℂ) * ((GodementSection.infMod a : ℝ) : ℂ) ^ (s - 1) ∂infiniteIdeleMeasure ℚ) *
      ∫ b : Afˣ, (∏ v : S, Aloc μ₁ μ₂ φ₀ c s S x κ v (lf v.1 b)) *
        ∏ᶠ v : {v : Pl // v ∉ S}, Gloc μ₁ μ₂ c s v.1 (lf v.1 b) ∂finiteIdeleMeasure ℚ := by
  rw [Ag, integral_ideleMeasure, ← integral_prod_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  obtain ⟨a, b⟩ := p
  exact pointwise hB hM hm hE hS c hxh s hκ a b
end Glob

theorem localChar_sq (c : HeckeCharacter ℚ) (v : Pl) : localChar (c * c) v = localChar c v * localChar c v := by
  ext a
  simp only [GroundTheory.Automorphic.GodementSection.coe_localChar, MonoidHom.mul_apply, Units.val_mul]
  rw [← GroundTheory.Automorphic.GodementSection.coe_localChar, ← GroundTheory.Automorphic.GodementSection.coe_localChar]
  rfl

section Unit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isUnit1_mul {a b : Fˣ →* ℂˣ} (ha : IsUnit1 a) (hb : IsUnit1 b) : IsUnit1 (a * b) :=
  ⟨ha.1.mul hb.1, fun x => by simp [ha.2 x, hb.2 x]⟩

theorem isUnit1_inv {a : Fˣ →* ℂˣ} (ha : IsUnit1 a) : IsUnit1 a⁻¹ :=
  ⟨ha.1.inv, fun x => by simp [ha.2 x]⟩
end Unit

section Core
variable {N : ℕ} {ω : HeckeCharacter ℚ} {W : G2 → ℂ} {μ₁ μ₂ : ∀ v : Pl, (Qv v)ˣ →* ℂˣ}
  {φ₀ : ∀ v : Pl, (Fin 2 → Qv v) → ℂ}

theorem integrable_Aloc (h1 : Loc2) (hB : B0) (hA : A10) (hm : Mod N ω W μ₁ μ₂ φ₀) {S : Finset Pl}
    (c : HeckeCharacter ℚ) (x : ∀ v : S, Qv v.1) {s : ℂ} (hs : 0 < s.re) {κ : G2}
    (hκ : ∀ v, finAt v κ ∈ integralGL (Qv v) 2) (v : S) :
    Integrable (Aloc μ₁ μ₂ φ₀ c s S x κ v) (multHaar (Qv v.1)) := by
  obtain ⟨m, hmK⟩ := hB.2.2.2.2.2.1
  haveI := (hmK v.1).1
  haveI := (hmK v.1).2
  have hstd := (hB.1 v.1).1
  have hW : W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1) ∈ V2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) :=
    Submodule.subset_span ⟨φ₀ v.1, hm.sb v.1, rfl⟩
  have hW' := (h1 (Qv v.1) (localAdelicChar ℚ v.1) hstd (μ₁ v.1) (μ₂ v.1) (hm.u₁ _) (hm.u₂ _)).1.stable _ hW (uni2 (x v))
  exact ((hA (Qv v.1) (localAdelicChar ℚ v.1) hstd (m v.1) (μ₁ v.1) (μ₂ v.1) (localChar c v.1) (hm.u₁ _) (hm.u₂ _)
    ((hB.1 v.1).2.2.2.2.2.2 c) _ hW _ hW').1 s hs).1 _ (hκ v.1)

theorem multipliable_local_l_factors (hB : B0) (hE2 : E2) (hm : Mod N ω W μ₁ μ₂ φ₀) (S : Finset Pl)
    (c : HeckeCharacter ℚ) {s : ℂ} (hs : 1 < s.re) :
    Multipliable fun v : {v : Pl // v ∉ S} => lf3 (μ₁ v.1 * (μ₂ v.1)⁻¹) (localChar c v.1) s := by
  have hc : ∀ v, IsUnit1 (localChar c v) := fun v => (hB.1 v).2.2.2.2.2.2 c
  have hν : ∀ v, IsUnit1 (μ₁ v * (μ₂ v)⁻¹) := fun v => isUnit1_mul (hm.u₁ v) (isUnit1_inv (hm.u₂ v))
  have m1 := (hE2 S s hs).2 (fun v => (μ₁ v * (μ₂ v)⁻¹) * localChar c v) fun v => isUnit1_mul (hν v) (hc v)
  have m2 := (hE2 S s hs).2 (fun v => localChar c v) hc
  have m3 := (hE2 S s hs).2 (fun v => (μ₁ v * (μ₂ v)⁻¹)⁻¹ * localChar c v)
    fun v => isUnit1_mul (isUnit1_inv (hν v)) (hc v)
  exact (m1.mul m2).mul m3

theorem core (h1 : Loc2) (hB : B0) (hA : A10) (hM : M0) (h4 : E4) (hE1 : E1) (hE2 : E2)
    (hm : Mod N ω W μ₁ μ₂ φ₀)
    (hE : ∀ g : G2, W g = W (realEmb (realPart g)) *
      ∏ᶠ v : Pl, W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) (finAt v g)) {S : Finset Pl}
    (hS : ∀ v, pOf v ∣ N → v ∈ S) (c : HeckeCharacter ℚ) (hc : ∀ v ∉ S, IsUnramifiedChar (localChar c v))
    {x : ∀ v : S, Qv v.1} {h : G2} (hxh : IsUn S x h) {s : ℂ} (hs : 1 < s.re) (κ : KA) :
    Ag (fun g => W g * conj (W (g * h))) c s κ.1 * partialLFunction (c * c) S (2 * s) =
      (∫ a : (InfiniteAdeleRing ℚ)ˣ, (fun y => W (realEmb y) * conj (W (realEmb y)))
          (realPart (dg2 ((IdeleGroup.prodEquiv ℚ).symm (a, 1)) 1 * κ.1)) *
        (GodementSection.infChar c a : ℂ) * ((GodementSection.infMod a : ℝ) : ℂ) ^ (s - 1) ∂infiniteIdeleMeasure ℚ) *
      (∏ v : S, Av (W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1))
        (fun g => W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1) (g * uni2 (x v))) (localChar c v.1) s (finAt v.1 κ.1)) *
      ((∏' v : {v : Pl // v ∉ S}, lf3 (μ₁ v.1 * (μ₂ v.1)⁻¹) (localChar c v.1) s) * Lp c S s) := by
  have hκ : ∀ v, finAt v κ.1 ∈ integralGL (Qv v) 2 := κ.2.2
  have hs0 : 0 < s.re := by linarith
  have hE4 : ∀ v ∉ S, _ := fun v (hv : v ∉ S) =>
    have hv' : ¬ pOf v ∣ N := fun h' => hv (hS _ h')
    h4 (Qv v) (localAdelicChar ℚ v) (hB.1 v).1 (μ₁ v) (μ₂ v) (localChar c v) (hm.u₁ v) (hm.u₂ v)
      ((hB.1 v).2.2.2.2.2.2 c) (hm.good v hv').1 (hm.good v hv').2.1 (hc v hv) s hs0 (Gloc μ₁ μ₂ c s v) fun _ => rfl
  obtain ⟨hmul, hint⟩ := hE1 S (Aloc μ₁ μ₂ φ₀ c s S x κ.1) (Gloc μ₁ μ₂ c s) s.re hs
    (integrable_Aloc h1 hB hA hm c x hs0 hκ) fun v hv => by
      obtain ⟨e1, e2, e3, e4, -⟩ := hE4 v hv
      refine ⟨e1, e2, e3, fun n => ?_⟩
      have := e4 n
      rwa [(hB.1 v).2.1] at this
  have h2s : 1 < (2 * s).re := by simp; linarith
  have hc2 : ∀ v ∉ S, IsUnramifiedChar (localChar (c * c) v) := fun v hv u hu => by
    rw [localChar_sq, MonoidHom.mem_ker, MonoidHom.mul_apply, hc v hv hu, mul_one]
  obtain ⟨-, hPL⟩ := (hE2 S (2 * s) h2s).1 (c * c) hc2
  have hLc := (hE2 S s hs).2 (fun v => localChar c v) fun v => (hB.1 v).2.2.2.2.2.2 c
  have key : (∏' v : {v : Pl // v ∉ S}, ∑' n : ℕ, Gloc μ₁ μ₂ c s v.1 (unifUnit (Qv v.1) ^ n)) *
      partialLFunction (c * c) S (2 * s) =
      (∏' v : {v : Pl // v ∉ S}, lf3 (μ₁ v.1 * (μ₂ v.1)⁻¹) (localChar c v.1) s) * Lp c S s := by
    rw [← hPL.tprod_eq, ← hmul.tprod_mul hPL.multipliable, Ad3.R.Lp,
      ← (multipliable_local_l_factors hB hE2 hm S c hs).tprod_mul hLc]
    refine tprod_congr fun v => ?_
    obtain ⟨-, -, -, -, e5⟩ := hE4 v.1 v.2
    rw [localChar_sq]
    exact e5
  rw [Ag_factor hB hM hm hE hS c hxh s hκ, hint, ← key]
  have hAv : ∀ v : S, ∫ a, Aloc μ₁ μ₂ φ₀ c s S x κ.1 v a ∂multHaar (Qv v.1) =
      Av (W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1))
        (fun g => W2 (localAdelicChar ℚ v.1) (μ₁ v.1) (μ₂ v.1) (φ₀ v.1) (g * uni2 (x v))) (localChar c v.1) s (finAt v.1 κ.1) :=
    fun v => rfl
  simp only [hAv]
  ring
end Core

theorem e6a : Loc2 → B0 → A10 → M0 → E4 → E0 → E1 → E2 → UnramifiedEulerProductIntegral := by
  intro h1 hB hA hM h4 h0 hE1 hE2 k N _ hk χ hχ f a hf ha ω φ hω hl μ₁ μ₂ φ₀ hm S hS c hc x h hxh s hs κ
  exact core h1 hB hA hM h4 hE1 hE2 hm (h0 k N hk χ hχ f a hf ha ω φ hω hl μ₁ μ₂ φ₀ hm) hS c hc hxh hs κ

end GlobalTheory.CompanionTheory.RankinSelbergEulerProduct
end
