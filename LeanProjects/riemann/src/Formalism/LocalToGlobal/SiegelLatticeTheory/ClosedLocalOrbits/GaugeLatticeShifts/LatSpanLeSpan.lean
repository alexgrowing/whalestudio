import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.Act

open Formalism.L2.SG.Pf Formalism.L2.SG.Saturated

open Formalism.L2.SG.Pf Formalism.L2.SG.Saturated

section Levi

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable (e f : Fin r → S.V)

def pX : S.V →ₗ[E] S.V := ∑ a, (S.hT (f a)).smulRight (e a)

def pY : S.V →ₗ[E] S.V := ∑ a, (S.hT (e a)).smulRight (f a)

theorem pX_apply (v : S.V) : pX e f v = ∑ a, S.hT (f a) v • e a := by
  simp [pX, LinearMap.sum_apply]

theorem pY_apply (v : S.V) : pY e f v = ∑ a, S.hT (e a) v • f a := by
  simp [pY, LinearMap.sum_apply]

theorem pj_eq (v : S.V) : pj e f v = v - pX e f v - pY e f v := by
  rw [pj_apply, pX_apply, pY_apply]

theorem decomp (v : S.V) : v = pX e f v + pY e f v + pj e f v := by
  rw [pj_eq]; abel

def lmap (δ : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V :=
  pj e f + (δ : S.V →ₗ[E] S.V) ∘ₗ pX e f + pY e f ∘ₗ (δ : S.V →ₗ[E] S.V) ∘ₗ pY e f

theorem lmap_apply (δ : S.V ≃ₗ[E] S.V) (v : S.V) :
    lmap e f δ v = pj e f v + δ (pX e f v) + pY e f (δ (pY e f v)) := by
  simp [lmap]

variable {e f}
variable (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)

include hef in
theorem hT_f_pX (v : S.V) (b : Fin r) : S.hT (f b) (pX e f v) = S.hT (f b) v := by
  simp [pX_apply, map_sum, hfe' hef]

include hee in
theorem hT_e_pX (v : S.V) (b : Fin r) : S.hT (e b) (pX e f v) = 0 := by
  simp [pX_apply, map_sum, hee]

include hef in
theorem hT_e_pY (v : S.V) (b : Fin r) : S.hT (e b) (pY e f v) = S.hT (e b) v := by
  simp [pY_apply, map_sum, hef]

include hff in
theorem hT_f_pY (v : S.V) (b : Fin r) : S.hT (f b) (pY e f v) = 0 := by
  simp [pY_apply, map_sum, hff]

include hff in
theorem pX_pY (v : S.V) : pX e f (pY e f v) = 0 := by
  rw [pX_apply]; simp [hT_f_pY hff]

include hee in
theorem pY_pX (v : S.V) : pY e f (pX e f v) = 0 := by
  rw [pY_apply]; simp [hT_e_pX hee]

include hef in
theorem pX_pX (v : S.V) : pX e f (pX e f v) = pX e f v := by
  rw [pX_apply e f (pX e f v)]; simp only [hT_f_pX hef]; rw [pX_apply]

include hef in
theorem pY_pY (v : S.V) : pY e f (pY e f v) = pY e f v := by
  rw [pY_apply e f (pY e f v)]; simp only [hT_e_pY hef]; rw [pY_apply]

include hff hef in
theorem pX_pj (v : S.V) : pX e f (pj e f v) = 0 := by
  rw [pX_apply]; simp [hT_f_pj hff hef]

include hee hef in
theorem pY_pj (v : S.V) : pY e f (pj e f v) = 0 := by
  rw [pY_apply]; simp [hT_e_pj hee hef]

include hee hef in
theorem pj_pX (v : S.V) : pj e f (pX e f v) = 0 := by
  rw [pj_eq, pX_pX hef, pY_pX hee]; abel

include hff hef in
theorem pj_pY (v : S.V) : pj e f (pY e f v) = 0 := by
  rw [pj_eq, pY_pY hef, pX_pY hff]; abel

include hef in
theorem pX_of_mem (x : S.V) (hx : x ∈ Submodule.span E (Set.range e)) : pX e f x = x := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
  rw [pX_apply]
  simp [map_sum, hfe' hef]

include hef in
theorem pY_of_mem (y : S.V) (hy : y ∈ Submodule.span E (Set.range f)) : pY e f y = y := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hy
  rw [pY_apply]
  simp [map_sum, hef]

include hee in
theorem pY_of_memX (x : S.V) (hx : x ∈ Submodule.span E (Set.range e)) : pY e f x = 0 := by
  rw [pY_apply]; simp [perpX_of_X hee x hx]

include hff in
theorem pX_of_memY (y : S.V) (hy : y ∈ Submodule.span E (Set.range f)) : pX e f y = 0 := by
  rw [pX_apply]; simp [perpX_of_X hff y hy]

theorem pX_mem (v : S.V) : pX e f v ∈ Submodule.span E (Set.range e) := by
  rw [pX_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem pY_mem (v : S.V) : pY e f v ∈ Submodule.span E (Set.range f) := by
  rw [pY_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

include hee hef in
theorem pj_of_memX (x : S.V) (hx : x ∈ Submodule.span E (Set.range e)) : pj e f x = 0 := by
  rw [pj_eq, pX_of_mem hef x hx, pY_of_memX hee x hx]; abel

include hff hef in
theorem pj_of_memY (y : S.V) (hy : y ∈ Submodule.span E (Set.range f)) : pj e f y = 0 := by
  rw [pj_eq, pY_of_mem hef y hy, pX_of_memY hff y hy]; abel

theorem hT_pX_left (v w : S.V) :
    S.hT (pX e f v) w = ∑ a, starRingEnd E (S.hT (f a) v) * S.hT (e a) w := by
  simp [pX_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]

theorem hT_pY_left (v w : S.V) :
    S.hT (pY e f v) w = ∑ a, starRingEnd E (S.hT (e a) v) * S.hT (f a) w := by
  simp [pY_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]

theorem hT_pY_right (w v : S.V) : S.hT w (pY e f v) = S.hT (pX e f w) v := by
  rw [hT_pX_left, pY_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul, ← S.herm.eq (f a) w, mul_comm]

include hee hff hef in
theorem hT_pj_left (v w : S.V) : S.hT (pj e f v) w = S.hT (pj e f v) (pj e f w) := by
  conv_lhs => rw [decomp (e := e) (f := f) w]
  have h0 : ∀ a, S.hT (pj e f v) (e a) = 0 := fun a => by
    rw [← S.herm.eq (e a) (pj e f v), hT_e_pj hee hef, map_zero]
  have h0' : ∀ a, S.hT (pj e f v) (f a) = 0 := fun a => by
    rw [← S.herm.eq (f a) (pj e f v), hT_f_pj hff hef, map_zero]
  have h1 : S.hT (pj e f v) (pX e f w) = 0 := by
    simp [pX_apply, map_sum, h0]
  have h2 : S.hT (pj e f v) (pY e f w) = 0 := by
    simp [pY_apply, map_sum, h0']
  simp [map_add, h1, h2]

include hee hff hef in

theorem hT_coord (v w : S.V) :
    S.hT v w = ∑ a, starRingEnd E (S.hT (f a) v) * S.hT (e a) w +
      ∑ a, starRingEnd E (S.hT (e a) v) * S.hT (f a) w + S.hT (pj e f v) (pj e f w) := by
  conv_lhs => rw [decomp (e := e) (f := f) v]
  rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hT_pX_left, hT_pY_left,
    hT_pj_left hee hff hef]

end Levi

section LeviIso

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {e f : Fin r → S.V}
variable (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)
  {δ : S.V ≃ₗ[E] S.V} (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
  (hX : ∀ x ∈ Submodule.span E (Set.range e), δ x ∈ Submodule.span E (Set.range e))

include hff hef in
theorem lmap_coordX (v : S.V) (b : Fin r) : S.hT (f b) (lmap e f δ v) = S.hT (f b) (δ (pX e f v)) := by
  rw [lmap_apply]
  simp [map_add, hT_f_pj hff hef, hT_f_pY hff]

include hee hef hX in
theorem lmap_coordY (v : S.V) (b : Fin r) : S.hT (e b) (lmap e f δ v) = S.hT (e b) (δ (pY e f v)) := by
  rw [lmap_apply]
  simp [map_add, hT_e_pj hee hef, hT_e_pY hef, perpX_of_X hee _ (hX _ (pX_mem v))]

include hee hff hef hX in
theorem pj_lmap (v : S.V) : pj e f (lmap e f δ v) = pj e f v := by
  rw [lmap_apply, map_add, map_add, pj_pj hee hff hef, pj_of_memX hee hef _ (hX _ (pX_mem v)),
    pj_pY hff hef]
  abel

include hee hff hef hδ hX in

theorem lmap_isom (v w : S.V) : S.hT (lmap e f δ v) (lmap e f δ w) = S.hT v w := by
  rw [hT_coord hee hff hef (lmap e f δ v), hT_coord hee hff hef v w]
  simp only [lmap_coordX hff hef, lmap_coordY hee hef hX, pj_lmap hee hff hef hX]
  have hx : ∀ u, δ (pX e f u) ∈ Submodule.span E (Set.range e) := fun u => hX _ (pX_mem u)
  have e1 : ∑ a, starRingEnd E (S.hT (f a) (δ (pX e f v))) * S.hT (e a) (δ (pY e f w)) =
      ∑ a, starRingEnd E (S.hT (f a) v) * S.hT (e a) w := by
    rw [← hT_pX_left, pX_of_mem hef _ (hx v), isom_apply hδ, hT_pX_left]
    simp only [hT_e_pY hef]
  have e2 : ∑ a, starRingEnd E (S.hT (e a) (δ (pY e f v))) * S.hT (f a) (δ (pX e f w)) =
      ∑ a, starRingEnd E (S.hT (e a) v) * S.hT (f a) w := by
    rw [← hT_pY_left]
    have h0 : S.hT (pY e f (δ (pY e f v))) (δ (pX e f w)) = S.hT (δ (pY e f v)) (δ (pX e f w)) := by
      conv_rhs => rw [decomp (e := e) (f := f) (δ (pY e f v))]
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hT_pX_left,
        hT_pj_left hee hff hef, pj_of_memX hee hef _ (hx w)]
      simp [perpX_of_X hee _ (hx w)]
    rw [h0, isom_apply hδ, hT_pY_left]
    simp only [hT_f_pX hef]
  rw [e1, e2]

include hee hff hef hδ hX in
theorem lmap_inj : Function.Injective (lmap e f δ) := by
  intro v w h
  have h0 : ∀ y, S.hT (v - w) y = 0 := fun y => by
    rw [← lmap_isom hee hff hef hδ hX, map_sub, h, sub_self, map_zero, LinearMap.zero_apply]
  exact sub_eq_zero.1 (S.nondeg.1 _ h0)

def lequiv : S.V ≃ₗ[E] S.V :=
  haveI := S.fd
  LinearEquiv.ofInjectiveEndo (lmap e f δ) (lmap_inj hee hff hef hδ hX)

theorem lequiv_apply (v : S.V) : lequiv hee hff hef hδ hX v = lmap e f δ v := rfl

theorem lequiv_isom : lequiv hee hff hef hδ hX ∈ Formalism.HermitianLatticesTheory.isom S.hT :=
  fun v w => lmap_isom hee hff hef hδ hX v w

theorem lequiv_e (b : Fin r) : lequiv hee hff hef hδ hX (e b) = δ (e b) := by
  have hb : e b ∈ Submodule.span E (Set.range e) := Submodule.subset_span ⟨b, rfl⟩
  rw [lequiv_apply, lmap_apply, pj_of_memX hee hef _ hb, pX_of_mem hef _ hb, pY_of_memX hee _ hb]
  simp

theorem lmap_perp (v : S.V) (hv : ∀ a, S.hT (e a) v = 0 ∧ S.hT (f a) v = 0) : lmap e f δ v = v := by
  have h1 : pX e f v = 0 := by rw [pX_apply]; simp [(hv _).2]
  have h2 : pY e f v = 0 := by rw [pY_apply]; simp [(hv _).1]
  rw [lmap_apply, pj_perp v hv, h1, h2]
  simp

end LeviIso

section LeviLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {e f : Fin r → S.V}

theorem mem_dual' {L : Submodule (𝓞 E) S.V} {x : S.V} :
    x ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔ ∀ m ∈ L, ∃ c : 𝓞 E, (c : E) = S.hT m x := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    Submodule.mem_one, LinearMap.restrictScalars_apply]

theorem int_of_unimod {Λ : Submodule (𝓞 E) S.V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {x y : S.V}
    (hx : x ∈ Λ) (hy : y ∈ Λ) : ∃ c : 𝓞 E, (c : E) = S.hT x y := by
  have hy' : y ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hU]; exact hy
  exact mem_dual'.1 hy' x hx

theorem latSpan_le_span (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V)
    (x : S.V) (hx : x ∈ latSpan aa v) : x ∈ Submodule.span E (Set.range v) := by
  have : latSpan aa v ≤ (Submodule.span E (Set.range v)).restrictScalars (𝓞 E) := by
    rw [latSpan, Submodule.span_le]
    rintro _ ⟨a, c, -, rfl⟩
    show c • v a ∈ Submodule.span E (Set.range v)
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a))
  exact this hx

variable (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)
  {δ : S.V ≃ₗ[E] S.V} (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
  (hX : ∀ x ∈ Submodule.span E (Set.range e), δ x ∈ Submodule.span E (Set.range e))
  (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {Λ L : Submodule (𝓞 E) S.V}
  (hΛ : Λ = latSpan aa e ⊔ L ⊔ latSpan (fun a => (aa a)⁻¹) f)
  (hLp : ∀ x ∈ L, ∀ a, S.hT (e a) x = 0 ∧ S.hT (f a) x = 0) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
  (hδ1 : ∀ x ∈ latSpan aa e, δ x ∈ Λ) (hδ2 : ∀ x ∈ latSpan aa e, δ.symm x ∈ Λ)

include hee hff hef hδ hX hΛ hLp hU hδ1 hδ2 in

theorem lmap_mem (v : S.V) (hv : v ∈ Λ) : lmap e f δ v ∈ Λ := by
  have hXΛ : latSpan aa e ≤ Λ := by rw [hΛ]; exact le_sup_left.trans le_sup_left
  have hLΛ : L ≤ Λ := by rw [hΛ]; exact le_sup_right.trans le_sup_left
  have hYΛ : latSpan (fun a => (aa a)⁻¹) f ≤ Λ := by rw [hΛ]; exact le_sup_right
  have hdec : ∀ w ∈ Λ, ∃ x ∈ latSpan aa e, ∃ l ∈ L, ∃ y ∈ latSpan (fun a => (aa a)⁻¹) f, w = x + l + y := by
    intro w hw
    rw [hΛ] at hw
    obtain ⟨xl, hxl, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
    obtain ⟨x, hx, l, hl, rfl⟩ := Submodule.mem_sup.1 hxl
    exact ⟨x, hx, l, hl, y, hy, rfl⟩
  have hpXw : ∀ x ∈ latSpan aa e, ∀ l ∈ L, ∀ y ∈ latSpan (fun a => (aa a)⁻¹) f, pX e f (x + l + y) = x := by
    intro x hx l hl y hy
    have hl0 : pX e f l = 0 := by rw [pX_apply]; simp [(hLp l hl _).2]
    rw [map_add, map_add, pX_of_mem hef _ (latSpan_le_span aa e x hx), hl0,
      pX_of_memY hff _ (latSpan_le_span _ f y hy)]
    abel
  obtain ⟨x, hx, l, hl, y, hy, rfl⟩ := hdec v hv
  have hxE := latSpan_le_span aa e x hx
  have hyE := latSpan_le_span _ f y hy
  have ex : lmap e f δ x = δ x := by
    rw [lmap_apply, pj_of_memX hee hef _ hxE, pX_of_mem hef _ hxE, pY_of_memX hee _ hxE]; simp
  have el : lmap e f δ l = l := lmap_perp l (hLp l hl)
  have ey : lmap e f δ y = pY e f (δ y) := by
    rw [lmap_apply, pj_of_memY hff hef _ hyE, pX_of_memY hff _ hyE, pY_of_mem hef _ hyE]; simp
  rw [map_add, map_add, ex, el, ey]
  refine Λ.add_mem (Λ.add_mem (hδ1 x hx) (hLΛ hl)) ?_
  have hd : pY e f (δ y) ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by
    refine mem_dual'.2 fun w hw => ?_
    obtain ⟨xw, hxw, lw, hlw, yw, hyw, rfl⟩ := hdec w hw
    rw [hT_pY_right, hpXw xw hxw lw hlw yw hyw, ← LinearEquiv.apply_symm_apply δ xw, isom_apply hδ]
    exact int_of_unimod hU (hδ2 xw hxw) (hYΛ hy)
  rwa [hU] at hd

include hee hff hef hδ hX hΛ hLp hU hδ1 hδ2 in

theorem gmap_lequiv : Formalism.HermitianLatticesTheory.gmap (lequiv hee hff hef hδ hX) Λ = Λ := by
  ext x
  rw [mem_gmap_iff]
  constructor
  · intro h
    have := lmap_mem hee hff hef hδ hX aa hΛ hLp hU hδ1 hδ2 _ h
    rwa [← lequiv_apply hee hff hef hδ hX, LinearEquiv.apply_symm_apply] at this
  · intro hx
    have hd : (lequiv hee hff hef hδ hX).symm x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by
      refine mem_dual'.2 fun w hw => ?_
      rw [← lequiv_isom hee hff hef hδ hX w, LinearEquiv.apply_symm_apply]
      exact int_of_unimod hU (lmap_mem hee hff hef hδ hX aa hΛ hLp hU hδ1 hδ2 w hw) hx
    rwa [hU] at hd

end LeviLat

section Witt

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem flagG_ext {T : E} {F1 F2 : FlagG S r T} (he : F1.e = F2.e) (hz : F1.z = F2.z) : F1 = F2 := by
  cases F1; cases F2; cases he; cases hz; rfl

theorem gram_fvec {T : E} (F : FlagG S r T) (i j : Fin (r + 1)) :
    S.hT (F.fvec i) (F.fvec j) = if i = Fin.last r ∧ j = Fin.last r then -T else 0 := by
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
  · simp [FlagG.fvec, F.z_norm]
  · have h := F.z_orth b
    rw [← S.herm.eq] at h
    simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc]
    rw [if_neg (fun h' => (Fin.castSucc_lt_last b).ne h'.2)]
    have h2 := congrArg (starRingEnd E) h
    simpa using h2
  · simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc]
    rw [if_neg (fun h' => (Fin.castSucc_lt_last a).ne h'.1), F.z_orth a]
  · simp only [FlagG.fvec, Fin.snoc_castSucc]
    rw [if_neg (fun h' => (Fin.castSucc_lt_last a).ne h'.1), F.e_iso a b]

theorem fvec_li {T : E} (hT : T ≠ 0) (F : FlagG S r T) : LinearIndependent E F.fvec := by
  unfold FlagG.fvec
  refine linearIndependent_finSnoc.2 ⟨F.e_indep, fun hz => hT ?_⟩
  have := hT_X_left F.z F.z_orth F.z hz
  rw [F.z_norm] at this
  exact neg_eq_zero.1 this

theorem frame_witt {T : E} (hT : T ≠ 0) (F1 F2 : FlagG S r T) :
    ∃ g : S.V ≃ₗ[E] S.V, g ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ a, g (F1.e a) = F2.e a) ∧ g F1.z = F2.z := by
  have := S.fd
  have l1 := fvec_li hT F1
  have l2 := fvec_li hT F2
  let b := Module.Basis.span l1
  let fm : Submodule.span E (Set.range F1.fvec) →ₗ[E] S.V :=
    (Finsupp.linearCombination E F2.fvec) ∘ₗ (b.repr : _ →ₗ[E] Fin (r + 1) →₀ E)
  have hfm : ∀ i, fm (b i) = F2.fvec i := fun i => by
    simp [fm, b.repr_self]
  have finj : Function.Injective fm :=
    (show Function.Injective (Finsupp.linearCombination E F2.fvec) from l2).comp b.repr.injective
  have hb : ∀ i, ((b i : Submodule.span E (Set.range F1.fvec)) : S.V) = F1.fvec i := fun i =>
    congrArg Subtype.val (Module.Basis.span_apply l1 i)
  have fiso : ∀ x y : Submodule.span E (Set.range F1.fvec), S.hT (fm x) (fm y) = S.hT x y := by
    intro x y
    rw [← b.sum_repr x, ← b.sum_repr y]
    simp only [map_sum, map_smul, hfm, Submodule.coe_sum, Submodule.coe_smul, hb, map_smulₛₗ,
      LinearMap.sum_apply, LinearMap.smul_apply, gram_fvec]
  obtain ⟨g, hg, hgf⟩ := witt_extension_theorem E S.V S.hT (fun x y => S.herm.eq x y) (fun x hx => S.nondeg.1 x hx)
    _ fm finj fiso
  have hgv : ∀ i, g (F1.fvec i) = F2.fvec i := fun i => by
    rw [← hb i, hgf, hfm]
  refine ⟨g, fun x y => hg x y, fun a => ?_, ?_⟩
  · have := hgv (Fin.castSucc a)
    simpa [FlagG.fvec] using this
  · have := hgv (Fin.last r)
    simpa [FlagG.fvec] using this

end Witt

section Lift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}

theorem mk_eq_of_eqv {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} {q p : GCar X u u' F0 F0' Λ Λ'}
    (hTR : ToTermRel X u u' F0 F0') (h : Relation.EqvGen (GRel X u u' F0 F0' Λ Λ') q p) :
    (TermDef.mk Λ (lf D F0) (TermDef.PD D Λ (lf D F0) u') ⟨mapLF q.1.2 (lf D F0'), q.2.2.2.2⟩ :
      TermDef.TermQ Λ (lf D F0) (TermDef.PD D Λ (lf D F0) u')) =
      TermDef.mk Λ (lf D F0) (TermDef.PD D Λ (lf D F0) u') ⟨mapLF p.1.2 (lf D F0'), p.2.2.2.2⟩ := by
  induction h with
  | rel x y hxy => exact Quot.sound (hTR Λ Λ' x y hxy)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem mapLF_eq {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {T : D.host.E} (F F' : FlagG (VS D) D.R.rS T) (he : ∀ a, γ (F.e a) = F'.e a) (hz : γ F.z = F'.z) :
    mapLF γ (lf D F) = lf D F' := by
  unfold mapLF
  rw [dif_pos hγ]
  have hfl : Formalism.L2.SG.TermOp.mapFlag γ hγ F = F' := flagG_ext (funext he) hz
  show (⟨Formalism.L2.SG.TermOp.mapFlag γ hγ F, γ F.z⟩ : LFlag (VS D) D.R.rS T) = ⟨F', F'.z⟩
  rw [hfl, hz]

theorem rowLat_map' (hLI : ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V), β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V,
        (Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 → Formalism.HermitianLatticesTheory.gmap β Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0) ∧
        (Submodule.IsLattice D.host.E Λ → Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap β Λ)) ∧
        (Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap β Λ)))
    {T : D.host.E} (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (h : IsRowLat D F0 Λ) : IsRowLat D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (Formalism.HermitianLatticesTheory.gmap β Λ) := by
  obtain ⟨hg, ⟨hlat, hun, hlift, hconv⟩, hX⟩ := h
  have hb := hLI β hβ Λ
  refine ⟨hb.1 hg, ⟨hb.2.1 hlat, hb.2.2 hun, (Formalism.L2.SG.Pf.IsLift_mapL β hβ Λ (lf D F0)).2 hlift,
    (Formalism.L2.SG.Pf.IsFixedConv_mapL β hβ (gS D) Λ (lf D F0)).2 hconv⟩, ?_⟩
  rw [show lf D (Formalism.L2.SG.Saturated.mapFlag β hβ F0) = mapL β hβ (lf D F0) from rfl, Formalism.L2.SG.Pf.XLam_mapL β hβ,
    Formalism.L2.SG.Pf.XS_mapFlag D β hβ, hX]

theorem liftOnto (hLI : ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V), β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V,
        (Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 → Formalism.HermitianLatticesTheory.gmap β Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0) ∧
        (Submodule.IsLattice D.host.E Λ → Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap β Λ)) ∧
        (Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap β Λ)))
    (hRP : ∀ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → ∃ x : X.B.I.GA, RatLink X x n)
    (Y : Full X) (u u' : D.what₂.Word) (hTR : ToTermRel X u u' (X.Fu u) (X.Fu u')) :
    LiftOnto X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') := by
  rintro ⟨Λ, hΛ, cls⟩
  obtain ⟨⟨⟨fl, zt⟩, hPD⟩, rfl⟩ := Quot.exists_rep cls
  obtain ⟨⟨hzΛ, hzt⟩, hAdm, hOK⟩ := hPD
  change zt = fl.z at hzt
  subst hzt
  have hT0 : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u').A.T_prime.ne_zero
  obtain ⟨γ0, hγ0, hγe, hγz⟩ := frame_witt hT0 (X.Fu u') fl
  obtain ⟨hgen, ⟨hlat, hun, -, -⟩, -⟩ := (Y.rowsOK u).1 Λ hΛ
  have hrow1 : IsRowLat D fl Λ := ⟨hgen, ⟨hlat, hun, ⟨hzΛ, rfl⟩, hOK.1⟩, hOK.2⟩
  have hrow2 := rowLat_map' hLI γ0⁻¹ (inv_mem hγ0) fl Λ hrow1
  have hflag : Formalism.L2.SG.Saturated.mapFlag γ0⁻¹ (inv_mem hγ0) fl = X.Fu u' := by
    refine flagG_ext (funext fun a => ?_) ?_
    · show γ0.symm (fl.e a) = (X.Fu u').e a
      rw [← hγe a, LinearEquiv.symm_apply_apply]
    · show γ0.symm fl.z = (X.Fu u').z
      rw [← hγz, LinearEquiv.symm_apply_apply]
  rw [hflag] at hrow2
  obtain ⟨Λ', ⟨hΛ'm, δ, ⟨hδi, hδX, hδz⟩, hδΛ⟩, -⟩ := (Y.rowsOK u').2 _ hrow2
  obtain ⟨f, L, hff, hef, hLp, hzL, hsplit⟩ := Y.split u' Λ' hΛ'm
  have hee := (X.Fu u').e_iso
  obtain ⟨-, ⟨-, hunΛ', -, -⟩, hXΛ'⟩ := (Y.rowsOK u').1 Λ' hΛ'm
  obtain ⟨-, -, hXΛ''⟩ := hrow2
  have hXX : ((X.Fu u').X).map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = (X.Fu u').X := by
    rw [← Xa_r' (X.Fu u')]; exact hδX _
  have hXd : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e),
      δ x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e) := fun x hx => by
    change δ x ∈ (X.Fu u').X
    rw [← hXX]
    exact Submodule.mem_map_of_mem hx
  have hXs : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e),
      δ.symm x ∈ Submodule.span D.host.E (Set.range (X.Fu u').e) := fun x hx => by
    change x ∈ (X.Fu u').X at hx
    rw [← hXX, Submodule.mem_map_equiv] at hx
    exact hx
  have hlatΛ' : latSpan (aaS D) (X.Fu u').e ≤ Λ' := by
    rw [hsplit]; exact le_sup_left.trans le_sup_left

  have hXLam : ∀ x ∈ latSpan (aaS D) (X.Fu u').e, x ∈ XLam Λ' (lf D (X.Fu u')) := fun x hx =>
    ⟨hlatΛ' hx, latSpan_le_span _ _ x hx⟩
  have hδ1 : ∀ x ∈ latSpan (aaS D) (X.Fu u').e, δ.symm x ∈ Λ' := fun x hx => by
    have h1 : x ∈ XLam (Formalism.HermitianLatticesTheory.gmap γ0⁻¹ Λ) (lf D (X.Fu u')) :=
      (hXΛ'.trans hXΛ''.symm).le (hXLam x hx)
    have h2 : x ∈ Formalism.HermitianLatticesTheory.gmap δ Λ' := by rw [hδΛ]; exact h1.1
    rwa [mem_gmap_iff] at h2
  have hδ2 : ∀ x ∈ latSpan (aaS D) (X.Fu u').e, δ.symm.symm x ∈ Λ' := fun x hx => by
    rw [LinearEquiv.symm_symm]
    have hx' := hXLam x hx
    have h1 : δ x ∈ XLam (Formalism.HermitianLatticesTheory.gmap γ0⁻¹ Λ) (lf D (X.Fu u')) := by
      refine ⟨?_, hXd x hx'.2⟩
      rw [← hδΛ]
      exact (gmap_apply_mem δ Λ' x).2 hx'.1
    exact ((hXΛ''.trans hXΛ'.symm).le h1).1
  let a := lequiv hee hff hef (δ := δ.symm) (inv_mem hδi) hXs
  have ha : Formalism.HermitianLatticesTheory.gmap a Λ' = Λ' :=
    gmap_lequiv hee hff hef (inv_mem hδi) hXs (aaS D) hsplit hLp hunΛ' hδ1 hδ2
  let γ := γ0 * δ * a
  have hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    mul_mem (mul_mem hγ0 hδi) (lequiv_isom hee hff hef (inv_mem hδi) hXs)
  have hγΛ : Formalism.HermitianLatticesTheory.gmap γ Λ' = Λ := by
    rw [gmap_mul_sat, gmap_mul_sat, ha, hδΛ, ← gmap_mul_sat, mul_inv_cancel, gmap_one_sat]
  have hγe' : ∀ b, γ ((X.Fu u').e b) = fl.e b := fun b => by
    show γ0 (δ (a ((X.Fu u').e b))) = fl.e b
    rw [show a ((X.Fu u').e b) = δ.symm ((X.Fu u').e b) from lequiv_e hee hff hef (inv_mem hδi) hXs b,
      LinearEquiv.apply_symm_apply, hγe]
  have hγz' : γ (X.Fu u').z = fl.z := by
    show γ0 (δ (a (X.Fu u').z)) = fl.z
    rw [show a (X.Fu u').z = (X.Fu u').z from lmap_perp _ (hLp _ hzL), hδz, hγz]
  have hmap := mapLF_eq hγ (X.Fu u') fl hγe' hγz'
  obtain ⟨x, hx⟩ := hRP γ hγ
  have hPD' : TermDef.PD D Λ (lf D (X.Fu u)) u' (mapLF γ (lf D (X.Fu u'))) :=
    (congrArg (TermDef.PD D Λ (lf D (X.Fu u)) u') hmap).mpr ⟨⟨hzΛ, rfl⟩, hAdm, hOK⟩
  let p : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ' := ⟨(x, γ), hx, hγ, hγΛ, hPD'⟩
  refine ⟨⟨Λ, hΛ, Λ', hΛ'm, Quot.mk _ p⟩, ?_⟩
  have h1 := mk_eq_of_eqv hTR (Quot.eqvGen_exact (Quot.out_eq (Quot.mk (GRel X u u' (X.Fu u) (X.Fu u') Λ Λ') p)))
  show TermDef.Term.mk Λ hΛ _ = TermDef.Term.mk Λ hΛ _
  congr 1
  refine h1.trans ?_
  exact congrArg (Quot.mk _) (Subtype.ext hmap)

end Lift

end Formalism.L2.SG.Pf.Act
