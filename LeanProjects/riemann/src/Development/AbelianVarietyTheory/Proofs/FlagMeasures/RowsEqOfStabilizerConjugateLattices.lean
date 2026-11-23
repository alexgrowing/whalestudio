import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.Uniq

section Gen
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) {r : ℕ}

def mix (c d : Fin r → V) : V →ₗ[K] V := ∑ a, (h (c a)).smulRight (d a)

theorem mix_apply (c d : Fin r → V) (v : V) : mix h c d v = ∑ a, h (c a) v • d a := by
  simp [mix]

def P (e c : Fin r → V) : V →ₗ[K] V := LinearMap.id - mix h c e

theorem P_apply (e c : Fin r → V) (v : V) : P h e c v = v - ∑ a, h (c a) v • e a := by
  simp [P, mix_apply]

variable {h}

theorem star_pair (hh : ∀ x y, star (h x y) = h y x) {x y : V} (H : h x y = 0) : h y x = 0 := by
  rw [← hh, H, star_zero]

theorem dual_symm (hh : ∀ x y, star (h x y) = h y x) {e c : Fin r → V}
    (hd : ∀ a b, h (e a) (c b) = if a = b then 1 else 0) (a b : Fin r) :
    h (c a) (e b) = if a = b then 1 else 0 := by
  rw [← hh, hd]
  by_cases hab : b = a
  · subst hab; simp
  · simp [hab, Ne.symm hab]

theorem pair_sum_e {e c : Fin r → V} (hd : ∀ a b, h (c a) (e b) = if a = b then 1 else 0)
    (s : Fin r → K) (b : Fin r) : h (c b) (∑ a, s a • e a) = s b := by
  simp [map_sum, map_smul, hd, Finset.sum_ite_eq]

theorem pair_sum_zero {x : V} {c : Fin r → V} (H : ∀ a, h x (c a) = 0) (s : Fin r → K) :
    h x (∑ a, s a • c a) = 0 := by
  simp [map_sum, map_smul, H]

theorem coord {e c : Fin r → V} (hd : ∀ a b, h (c a) (e b) = if a = b then 1 else 0) {v : V}
    (hv : v ∈ Submodule.span K (Set.range e)) : v = ∑ a, h (c a) v • e a := by
  obtain ⟨s, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv
  simp only [pair_sum_e hd]

theorem P_mem {e c : Fin r → V} (hee : ∀ a b, h (e a) (e b) = 0)
    (hd : ∀ a b, h (c a) (e b) = if a = b then 1 else 0) {u : V} (hu : ∀ a, h (e a) u = 0) (b : Fin r) :
    h (e b) (P h e c u) = 0 ∧ h (c b) (P h e c u) = 0 := by
  rw [P_apply, map_sub, map_sub, pair_sum_e hd, pair_sum_zero (hee b), hu, sub_zero, sub_self]
  exact ⟨rfl, rfl⟩

theorem P_P {e c c' : Fin r → V} (hd' : ∀ a b, h (c' a) (e b) = if a = b then 1 else 0) (v : V) :
    P h e c' (P h e c v) = P h e c' v := by
  rw [P_apply, P_apply, P_apply]
  simp only [map_sub, pair_sum_e hd', sub_smul, Finset.sum_sub_distrib]
  abel

end Gen
end GlobalTheory.RowsOrb.Uniq

namespace GlobalTheory.RowsOrb.Uniq
section Gen2
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {h : V →ₗ⋆[K] V →ₗ[K] K} {r : ℕ}

theorem pair_first (s : Fin r → K) (e : Fin r → V) (y : V) :
    h (∑ a, s a • e a) y = ∑ a, star (s a) * h (e a) y := by
  simp [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply]

theorem P_iso (hh : ∀ x y, star (h x y) = h y x) {e : Fin r → V} (hee : ∀ a b, h (e a) (e b) = 0)
    {u u' : V} (hu : ∀ a, h (e a) u = 0) (hu' : ∀ a, h (e a) u' = 0) (s s' : Fin r → K) :
    h (u - ∑ a, s a • e a) (u' - ∑ a, s' a • e a) = h u u' := by
  have h1 : ∀ a, h u (e a) = 0 := fun a => star_pair hh (hu a)
  have h2 : ∀ a, h (e a) (u' - ∑ b, s' b • e b) = 0 := by
    intro a; rw [map_sub, hu', pair_sum_zero (hee a), sub_zero]
  rw [LinearMap.map_sub₂, pair_first s e, map_sub (h u), pair_sum_zero h1, sub_zero,
    Finset.sum_eq_zero (fun a _ => by rw [h2 a, mul_zero]), sub_zero]

variable (h) in

def pi (e f : Fin r → V) : V →ₗ[K] V := LinearMap.id - mix h f e - mix h e f

theorem pi_apply (e f : Fin r → V) (v : V) :
    pi h e f v = v - ∑ a, h (f a) v • e a - ∑ a, h (e a) v • f a := by
  simp [pi, mix_apply]

theorem pi_mem {e f : Fin r → V} (hee : ∀ a b, h (e a) (e b) = 0) (hff : ∀ a b, h (f a) (f b) = 0)
    (hd : ∀ a b, h (e a) (f b) = if a = b then 1 else 0)
    (hd' : ∀ a b, h (f a) (e b) = if a = b then 1 else 0) (v : V) (b : Fin r) :
    h (e b) (pi h e f v) = 0 ∧ h (f b) (pi h e f v) = 0 := by
  rw [pi_apply]
  simp only [map_sub, pair_sum_e hd, pair_sum_e hd', pair_sum_zero (hee b), pair_sum_zero (hff b)]
  constructor <;> simp

theorem decomp_pair (hh : ∀ x y, star (h x y) = h y x) {e f : Fin r → V} (hee : ∀ a b, h (e a) (e b) = 0)
    (hff : ∀ a b, h (f a) (f b) = 0) (hd : ∀ a b, h (e a) (f b) = if a = b then 1 else 0)
    {w w' : V} (hw : ∀ a, h (e a) w = 0 ∧ h (f a) w = 0) (hw' : ∀ a, h (e a) w' = 0 ∧ h (f a) w' = 0)
    (s t s' t' : Fin r → K) :
    h (∑ a, s a • e a + ∑ a, t a • f a + w) (∑ a, s' a • e a + ∑ a, t' a • f a + w') =
      ∑ a, (star (s a) * t' a + star (t a) * s' a) + h w w' := by
  have hd' := dual_symm hh hd
  have he : ∀ b, h (e b) (∑ a, s' a • e a + ∑ a, t' a • f a + w') = t' b := by
    intro b; simp only [map_add, pair_sum_zero (hee b), pair_sum_e hd, (hw' b).1, zero_add, add_zero]
  have hf : ∀ b, h (f b) (∑ a, s' a • e a + ∑ a, t' a • f a + w') = s' b := by
    intro b; simp only [map_add, pair_sum_zero (hff b), pair_sum_e hd', (hw' b).2, zero_add, add_zero]
  have hwe : ∀ a, h w (e a) = 0 := fun a => star_pair hh (hw a).1
  have hwf : ∀ a, h w (f a) = 0 := fun a => star_pair hh (hw a).2
  have hww : h w (∑ a, s' a • e a + ∑ a, t' a • f a + w') = h w w' := by
    simp only [map_add, pair_sum_zero hwe, pair_sum_zero hwf, zero_add]
  rw [LinearMap.map_add₂, LinearMap.map_add₂, pair_first s e, pair_first t f, hww]
  simp only [he, hf, Finset.sum_add_distrib]
end Gen2
end GlobalTheory.RowsOrb.Uniq

namespace GlobalTheory.RowsOrb.Uniq
section Gam
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {h : V →ₗ⋆[K] V →ₗ[K] K} {r : ℕ} {e fY f1 f2 : Fin r → V} {W : Submodule K V}

variable (h e fY f1 f2 W) in

def gam (hcod : ∀ v, P h e fY (pi h e f1 v) ∈ W) (g : W ≃ₗ[K] W) : V →ₗ[K] V :=
  mix h f1 e + mix h e f2 +
    (P h e f2 ∘ₗ W.subtype ∘ₗ g.toLinearMap ∘ₗ LinearMap.codRestrict W (P h e fY ∘ₗ pi h e f1) hcod)

theorem gam_apply (hcod : ∀ v, P h e fY (pi h e f1 v) ∈ W) (g : W ≃ₗ[K] W) (v : V) :
    gam h e fY f1 f2 W hcod g v = ∑ a, h (f1 a) v • e a + ∑ a, h (e a) v • f2 a +
      P h e f2 (g (LinearMap.codRestrict W (P h e fY ∘ₗ pi h e f1) hcod v) : V) := by
  simp [gam, mix_apply]

theorem cod_val (hcod : ∀ v, P h e fY (pi h e f1 v) ∈ W) (v : V) :
    ((LinearMap.codRestrict W (P h e fY ∘ₗ pi h e f1) hcod v : W) : V) = P h e fY (pi h e f1 v) := rfl

theorem gam_iso (hh : ∀ x y, star (h x y) = h y x) (hee : ∀ a b, h (e a) (e b) = 0)
    (hW : ∀ v ∈ W, ∀ a, h (e a) v = 0)
    (hff1 : ∀ a b, h (f1 a) (f1 b) = 0) (hd1 : ∀ a b, h (e a) (f1 b) = if a = b then 1 else 0)
    (hff2 : ∀ a b, h (f2 a) (f2 b) = 0) (hd2 : ∀ a b, h (e a) (f2 b) = if a = b then 1 else 0)
    (hcod : ∀ v, P h e fY (pi h e f1 v) ∈ W) (g : W ≃ₗ[K] W) (hg : ∀ x y : W, h (g x : V) (g y : V) = h x y)
    (x y : V) : h (gam h e fY f1 f2 W hcod g x) (gam h e fY f1 f2 W hcod g y) = h x y := by
  have hd1' := dual_symm hh hd1
  have hd2' := dual_symm hh hd2
  have hWm : ∀ v, ∀ a, h (e a) (P h e f2 (g (LinearMap.codRestrict W (P h e fY ∘ₗ pi h e f1) hcod v) : V)) = 0 ∧
      h (f2 a) (P h e f2 (g (LinearMap.codRestrict W (P h e fY ∘ₗ pi h e f1) hcod v) : V)) = 0 :=
    fun v a => P_mem hee hd2' (hW _ (g _).2) a
  rw [gam_apply, gam_apply, decomp_pair hh hee hff2 hd2 (hWm x) (hWm y)]
  have hx : ∀ v, v = ∑ a, h (f1 a) v • e a + ∑ a, h (e a) v • f1 a + pi h e f1 v := by
    intro v; rw [pi_apply]; abel
  have hpi := pi_mem hee hff1 hd1 hd1'
  conv_rhs => rw [hx x, hx y]
  rw [decomp_pair hh hee hff1 hd1 (hpi x) (hpi y)]
  congr 1
  rw [P_apply, P_apply, P_iso hh hee (hW _ (g _).2) (hW _ (g _).2), hg, cod_val, cod_val, P_apply, P_apply,
    P_iso hh hee (fun a => (hpi x a).1) (fun a => (hpi y a).1)]

end Gam
end GlobalTheory.RowsOrb.Uniq

namespace GlobalTheory.RowsOrb.Uniq
section Gam2
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {h : V →ₗ⋆[K] V →ₗ[K] K} {r : ℕ} {e fY f1 f2 : Fin r → V} {W : Submodule K V}

theorem cod_zero (hcod : ∀ v, P h e fY (pi h e f1 v) ∈ W) {v : V} (hv : pi h e f1 v = 0) :
    LinearMap.codRestrict W (P h e fY ∘ₗ pi h e f1) hcod v = 0 :=
  Subtype.ext (by rw [cod_val, hv, map_zero]; rfl)

theorem gam_e (hh : ∀ x y, star (h x y) = h y x) (hee : ∀ a b, h (e a) (e b) = 0)
    (hd1 : ∀ a b, h (e a) (f1 b) = if a = b then 1 else 0)
    (hcod : ∀ v, P h e fY (pi h e f1 v) ∈ W) (g : W ≃ₗ[K] W) (b : Fin r) :
    gam h e fY f1 f2 W hcod g (e b) = e b := by
  have hd1' := dual_symm hh hd1
  have hpi : pi h e f1 (e b) = 0 := by
    rw [pi_apply]; simp [hd1', hee]
  rw [gam_apply, cod_zero hcod hpi]
  simp [hd1', hee]

theorem gam_f (hh : ∀ x y, star (h x y) = h y x) (hff1 : ∀ a b, h (f1 a) (f1 b) = 0)
    (hd1 : ∀ a b, h (e a) (f1 b) = if a = b then 1 else 0)
    (hcod : ∀ v, P h e fY (pi h e f1 v) ∈ W) (g : W ≃ₗ[K] W) (b : Fin r) :
    gam h e fY f1 f2 W hcod g (f1 b) = f2 b := by
  have hpi : pi h e f1 (f1 b) = 0 := by
    rw [pi_apply]; simp [hd1, hff1]
  rw [gam_apply, cod_zero hcod hpi]
  simp [hd1, hff1]

theorem gam_orth (hcod : ∀ v, P h e fY (pi h e f1 v) ∈ W) (g : W ≃ₗ[K] W) {l : V}
    (hl : ∀ a, h (e a) l = 0 ∧ h (f1 a) l = 0) :
    ∃ hm : P h e fY l ∈ W, gam h e fY f1 f2 W hcod g l = P h e f2 (g ⟨P h e fY l, hm⟩ : V) := by
  have hpi : pi h e f1 l = l := by
    rw [pi_apply]; simp [hl]
  refine ⟨hpi ▸ hcod l, ?_⟩
  rw [gam_apply]
  simp only [hl, zero_smul, Finset.sum_const_zero, zero_add]
  congr 3
  exact Subtype.ext (by show P h e fY (pi h e f1 l) = P h e fY l; rw [hpi])

theorem gam_inj (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {γ : V →ₗ[K] V}
    (hγ : ∀ x y, h (γ x) (γ y) = h x y) : Function.Injective γ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  exact hnd x (fun y => by rw [← hγ, hx, map_zero, LinearMap.zero_apply])

end Gam2
end GlobalTheory.RowsOrb.Uniq

namespace GlobalTheory.RowsOrb.Uniq
section Spec
variable {D : D7}

theorem hh (x y : (VS D).V) : star ((VS D).hT x y) = (VS D).hT y x := by
  have := (VS D).herm.eq x y
  rwa [starRingEnd_apply] at this

theorem hnd (x : (VS D).V) (H : ∀ y, (VS D).hT x y = 0) : x = 0 := (VS D).nondeg.1 x H

theorem fixedFrameOfWord_isotropicSpan_eq (X : HidaSetting D) (u : D.what₂.Word) :
    (GlobalTheory.TypeAsm.F0 X u).X = Submodule.span D.host.E (Set.range X.eX) := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b, ?_⟩
    show X.eX b = (X.Fu u).fvec b.castSucc
    rw [GlobalTheory.TypeAsm.fv_cast, HidaSetting.Fu_e]
  · rintro ⟨b, rfl⟩
    refine ⟨b, b.2, ?_⟩
    show (X.Fu u).fvec b.castSucc = X.eX b
    rw [GlobalTheory.TypeAsm.fv_cast, HidaSetting.Fu_e]

theorem orth_span {x : (VS D).V} {r : ℕ} {v : Fin r → (VS D).V} (H : ∀ b, (VS D).hT x (v b) = 0)
    {y : (VS D).V} (hy : y ∈ Submodule.span D.host.E (Set.range v)) : (VS D).hT x y = 0 := by
  obtain ⟨s, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hy
  exact pair_sum_zero H s

theorem latSpan_le {r : ℕ} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (v : Fin r → (VS D).V) {y : (VS D).V} (hy : y ∈ Formalism.L2.SG.Saturated.latSpan aa v) :
    y ∈ Submodule.span D.host.E (Set.range v) := by
  have : Formalism.L2.SG.Saturated.latSpan aa v ≤ (Submodule.span D.host.E (Set.range v)).restrictScalars (𝓞 D.host.E) := by
    apply Submodule.span_le.2
    rintro _ ⟨a, x, -, rfl⟩
    exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)
  exact this hy

end Spec
end GlobalTheory.RowsOrb.Uniq

namespace GlobalTheory.RowsOrb.Uniq
section Spec2
variable {D : D7}

theorem lmap_char (X : HidaSetting D) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (aa aa' : Fin D.R.rS → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    {f : Fin D.R.rS → (VS D).V} {L : Submodule (𝓞 D.host.E) (VS D).V}
    (hd : ∀ a b, (VS D).hT (X.eX a) (f b) = if a = b then 1 else 0)
    (hL : ∀ x ∈ L, ∀ a, (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (f a) x = 0)
    (hΛ : Λ = Formalism.L2.SG.Saturated.latSpan aa X.eX ⊔ L ⊔ Formalism.L2.SG.Saturated.latSpan aa' f)
    (w : GlobalTheory.RowsOrb.Wb X) :
    w ∈ GlobalTheory.RowsOrb.Lmap X u Λ ↔ ∃ l ∈ L, P (VS D).hT X.eX X.fY l = (w : (VS D).V) := by
  have hdY : ∀ a b, (VS D).hT (X.fY a) (X.eX b) = if a = b then 1 else 0 := dual_symm hh X.ef
  have hwWb := (GlobalTheory.RowsOrb.mem_Wb X w).1 w.2
  rw [GlobalTheory.RowsOrb.mem_Lmap, fixedFrameOfWord_isotropicSpan_eq]
  constructor
  · intro hw
    obtain ⟨lam, hlam, x, hx, hsum⟩ := Submodule.mem_sup.1 hw
    rw [hΛ] at hlam
    obtain ⟨y, hy, t, ht, rfl⟩ := Submodule.mem_sup.1 hlam
    obtain ⟨s, hs, l, hl, rfl⟩ := Submodule.mem_sup.1 hy
    have hx' : x ∈ Submodule.span D.host.E (Set.range X.eX) := hx
    have hs' := latSpan_le _ _ hs
    have ht' := latSpan_le _ _ ht
    have hta : ∀ a, (VS D).hT (X.eX a) t = 0 := by
      intro a
      have e1 := (hwWb a).1
      rw [← hsum] at e1
      simp only [map_add] at e1
      rw [orth_span (X.ee a) hs', (hL l hl a).1, orth_span (X.ee a) hx'] at e1
      simpa using e1
    have ht0 : t = 0 := by
      rw [coord hd ht']; simp [hta]
    subst ht0
    refine ⟨l, hl, ?_⟩
    have hdm : (w : (VS D).V) - P (VS D).hT X.eX X.fY l ∈ Submodule.span D.host.E (Set.range X.eX) := by
      rw [← hsum, P_apply]
      have : s + l + 0 + x - (l - ∑ a, (VS D).hT (X.fY a) l • X.eX a) =
          s + x + ∑ a, (VS D).hT (X.fY a) l • X.eX a := by abel
      rw [this]
      refine add_mem (add_mem hs' hx') (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
    have hPm := P_mem X.ee hdY (fun a => (hL l hl a).1)
    have hc : ∀ a, (VS D).hT (X.fY a) ((w : (VS D).V) - P (VS D).hT X.eX X.fY l) = 0 := by
      intro a; rw [map_sub, (hwWb a).2, (hPm a).2, sub_zero]
    have h0 := coord hdY hdm
    simp only [hc, zero_smul, Finset.sum_const_zero] at h0
    exact (sub_eq_zero.1 h0).symm
  · rintro ⟨l, hl, hPl⟩
    rw [← hPl, P_apply, sub_eq_add_neg]
    refine Submodule.mem_sup.2 ⟨l, ?_, -(∑ a, (VS D).hT (X.fY a) l • X.eX a), ?_, rfl⟩
    · rw [hΛ]; exact Submodule.mem_sup_left (Submodule.mem_sup_right hl)
    · show _ ∈ Submodule.span D.host.E (Set.range X.eX)
      exact neg_mem (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

end Spec2
end GlobalTheory.RowsOrb.Uniq

namespace GlobalTheory.RowsOrb.Uniq
section Spec3
variable {D : D7}

theorem map_latSpan {r : ℕ} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (v : Fin r → (VS D).V) :
    Submodule.map ((γ : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E))
      (Formalism.L2.SG.Saturated.latSpan aa v) = Formalism.L2.SG.Saturated.latSpan aa (fun a => γ (v a)) := by
  unfold Formalism.L2.SG.Saturated.latSpan
  rw [Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨a, x, hx, rfl⟩, rfl⟩
    exact ⟨a, x, hx, by simp⟩
  · rintro ⟨a, x, hx, rfl⟩
    exact ⟨x • v a, ⟨a, x, hx, rfl⟩, by simp⟩

end Spec3
end GlobalTheory.RowsOrb.Uniq

open GlobalTheory.RowsOrb.Uniq in
theorem GlobalTheory.RowsOrb.rows_eq_of_conj : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    GlobalTheory.TypeAsm.Std D large₂ → ∀ Λ₁ ∈ Y.what₂ u, ∀ Λ₂ ∈ Y.what₂ u, ∀ g : GlobalTheory.RowsOrb.Gz X u,
      g • GlobalTheory.RowsOrb.Lmap X u Λ₁ = GlobalTheory.RowsOrb.Lmap X u Λ₂ → Λ₁ = Λ₂ := by
  intro D large₂ X Y u _ Λ₁ h1 Λ₂ h2 g hg
  obtain ⟨f1, L1, hff1, hd1, hL1, hz1, hΛ1⟩ := Y.split u Λ₁ h1
  obtain ⟨f2, L2, hff2, hd2, hL2, hz2, hΛ2⟩ := Y.split u Λ₂ h2
  simp only [HidaSetting.Fu_e, HidaSetting.flagZVector] at hd1 hL1 hz1 hΛ1 hd2 hL2 hz2 hΛ2
  have hdY := dual_symm hh X.ef
  have hd1' := dual_symm hh hd1
  have hcod : ∀ v, P (VS D).hT X.eX X.fY (pi (VS D).hT X.eX f1 v) ∈ GlobalTheory.RowsOrb.Wb X :=
    fun v a => P_mem X.ee hdY (fun b => (pi_mem X.ee hff1 hd1 hd1' v b).1) a
  have hiso := gam_iso hh X.ee (fun v hv a => (hv a).1) hff1 hd1 hff2 hd2 hcod g.1.1 (fun x y => g.1.2 x y)
  let γ := LinearEquiv.ofInjectiveEndo _ (gam_inj hnd hiso)
  have hγ : ∀ v, γ v = gam (VS D).hT X.eX X.fY f1 f2 (GlobalTheory.RowsOrb.Wb X) hcod g.1.1 v := fun v => rfl
  have hP2 := dual_symm hh hd2
  have hγe : ∀ b, γ (X.eX b) = X.eX b := fun b => by rw [hγ]; exact gam_e hh X.ee hd1 hcod _ b
  have hγf : ∀ b, γ (f1 b) = f2 b := fun b => by rw [hγ]; exact gam_f hh hff1 hd1 hcod _ b
  have hz : γ (X.zu u) = X.zu u := by
    obtain ⟨hm, hgz⟩ := gam_orth hcod g.1.1 (hL1 _ hz1)
    have hPz : P (VS D).hT X.eX X.fY (X.zu u) = X.zu u := by
      rw [P_apply]; simp [(X.zu_orth u _).2]
    have e1 : (⟨P (VS D).hT X.eX X.fY (X.zu u), hm⟩ : GlobalTheory.RowsOrb.Wb X) = GlobalTheory.RowsOrb.zb X u := Subtype.ext hPz
    have hs : (g.1.1 : GlobalTheory.RowsOrb.Wb X ≃ₗ[D.host.E] GlobalTheory.RowsOrb.Wb X) (GlobalTheory.RowsOrb.zb X u) = GlobalTheory.RowsOrb.zb X u := g.2
    rw [hγ, hgz, e1, hs, GlobalTheory.RowsOrb.zb_coe, P_apply]
    simp [(hL2 _ hz2 _).2]
  have hγL : Submodule.map ((γ : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) L1 = L2 := by
    ext v
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨hm, hgl⟩ := gam_orth hcod g.1.1 (hL1 l hl)
      have hin : (⟨_, hm⟩ : GlobalTheory.RowsOrb.Wb X) ∈ GlobalTheory.RowsOrb.Lmap X u Λ₁ :=
        (lmap_char X u Λ₁ _ _ hd1 hL1 hΛ1 _).2 ⟨l, hl, rfl⟩
      have hin2 : g.1.1 ⟨_, hm⟩ ∈ GlobalTheory.RowsOrb.Lmap X u Λ₂ := by
        rw [← hg]; exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨_, hin, rfl⟩
      obtain ⟨l2, hl2, hPl2⟩ := (lmap_char X u Λ₂ _ _ hd2 hL2 hΛ2 _).1 hin2
      rw [hγ, hgl, ← hPl2, P_P hP2, P_apply]
      simpa [(hL2 l2 hl2 _).2] using hl2
    · intro hv
      have hm : P (VS D).hT X.eX X.fY v ∈ GlobalTheory.RowsOrb.Wb X :=
        fun a => P_mem X.ee hdY (fun b => (hL2 v hv b).1) a
      have hin2 : (⟨_, hm⟩ : GlobalTheory.RowsOrb.Wb X) ∈ GlobalTheory.RowsOrb.Lmap X u Λ₂ :=
        (lmap_char X u Λ₂ _ _ hd2 hL2 hΛ2 _).2 ⟨v, hv, rfl⟩
      rw [← hg] at hin2
      obtain ⟨b, hb, hgb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hin2
      obtain ⟨l1, hl1, hPl1⟩ := (lmap_char X u Λ₁ _ _ hd1 hL1 hΛ1 _).1 hb
      refine ⟨l1, hl1, ?_⟩
      obtain ⟨hm1, hgl1⟩ := gam_orth hcod g.1.1 (hL1 l1 hl1)
      have e1 : (⟨_, hm1⟩ : GlobalTheory.RowsOrb.Wb X) = b := Subtype.ext hPl1
      have hgb' : g.1.1 b = ⟨_, hm⟩ := hgb
      rw [hγ, hgl1, e1, hgb']
      show P (VS D).hT X.eX f2 (P (VS D).hT X.eX X.fY v) = v
      rw [P_P hP2, P_apply]
      simp [(hL2 v hv _).2]
  have hstab : γ ∈ stabF D (X.Fu u) := by
    refine ⟨fun x y => hiso x y, fun j => ?_, ?_⟩
    · simp only [Formalism.MainNotions.S.FlagG.Xa, HidaSetting.Fu_e]
      rw [Submodule.map_span, Set.image_image]
      simp only [LinearEquiv.coe_coe, hγe]
    · rw [HidaSetting.flagZVector]; exact hz
  have hmap : Formalism.HermitianLatticesTheory.gmap γ Λ₁ = Λ₂ := by
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [hΛ1, hΛ2, Submodule.map_sup, Submodule.map_sup, map_latSpan, map_latSpan, hγL]
    simp only [hγe, hγf]
  have hR := Y.rowsOK u
  refine (hR.2 Λ₂ (hR.1 Λ₂ h2)).unique ⟨h1, γ, hstab, hmap⟩ ⟨h2, 1, ?_, ?_⟩
  · refine ⟨fun x y => rfl, fun j => ?_, rfl⟩
    simp
  · ext v; simp [Formalism.HermitianLatticesTheory.gmap]
