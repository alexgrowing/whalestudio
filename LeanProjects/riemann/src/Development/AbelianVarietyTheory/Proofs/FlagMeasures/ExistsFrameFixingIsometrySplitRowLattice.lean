import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnram
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LoopC.RowSplit

section Lattices

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_proj (L : Submodule (𝓞 K) V) (hfg : L.FG) (hsp : Submodule.span K (L : Set V) = ⊤) (W : Submodule K V) :
    ∃ P : V →ₗ[K] V, (∀ v, P v ∈ W) ∧ (∀ w ∈ W, P w = w) ∧ ∀ v ∈ L, P v ∈ L := by
  classical
  let q : V →ₗ[𝓞 K] V ⧸ W := W.mkQ.restrictScalars (𝓞 K)
  let Lb : Submodule (𝓞 K) (V ⧸ W) := L.map q
  have hfin : Module.Finite (𝓞 K) Lb := Module.Finite.iff_fg.2 (hfg.map q)
  have hcancel : ∀ (d : 𝓞 K) (x : V ⧸ W), d ≠ 0 → d • x = 0 → x = 0 := by
    intro d x hd h
    rw [← IsScalarTower.algebraMap_smul K d x] at h
    exact (smul_eq_zero.1 h).resolve_left (by simpa using hd)
  have hflat : Module.Flat (𝓞 K) Lb := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨d, hd⟩
    have : (d : 𝓞 K) • (x : V ⧸ W) = 0 := congrArg Subtype.val hd
    exact Subtype.ext (hcancel d x (nonZeroDivisors.coe_ne_zero d) this)
  have hfp : Module.FinitePresentation (𝓞 K) Lb := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective (𝓞 K) Lb := Module.Flat.projective_of_finitePresentation
  let qL : L →ₗ[𝓞 K] Lb := q.submoduleMap L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property qL LinearMap.id (LinearMap.submoduleMap_surjective q L)
  have hs' : ∀ y : Lb, q (s y : V) = y := fun y => congrArg Subtype.val (LinearMap.congr_fun hs y)
  let p0 : L →ₗ[𝓞 K] V := L.subtype - L.subtype ∘ₗ s ∘ₗ qL
  have hp0 : ∀ x : L, p0 x = (x : V) - s (qL x) := fun x => rfl
  have hden : ∀ v : V, ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ L := by
    intro v
    have hv : v ∈ Submodule.span K (L : Set V) := by rw [hsp]; trivial
    obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (L : Set V) v hv
    rw [Submodule.span_eq] at hd
    exact ⟨d, nonZeroDivisors.coe_ne_zero d, hd⟩
  have hunit : ∀ x : nonZeroDivisors (𝓞 K), IsUnit (algebraMap (𝓞 K) (Module.End (𝓞 K) V) x) :=
    (isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K).map_units
  haveI hloc : IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype := by
    refine ⟨hunit, fun v => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    obtain ⟨d, hd, hv⟩ := hden v
    exact ⟨(⟨d • v, hv⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩
  let P0 : V →ₗ[𝓞 K] V := IsLocalizedModule.lift (nonZeroDivisors (𝓞 K)) L.subtype p0 hunit
  have hP0 : ∀ x : L, P0 (x : V) = p0 x := fun x => IsLocalizedModule.lift_apply _ L.subtype p0 hunit x
  let P : V →ₗ[K] V := P0.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K
  have hP : ∀ v, P v = P0 v := fun v => rfl
  have hW : ∀ x : L, p0 x ∈ W := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    change q (p0 x) = 0
    rw [hp0, map_sub, hs']
    exact sub_self _
  refine ⟨P, fun v => ?_, fun w hw => ?_, fun v hv => ?_⟩
  · obtain ⟨d, hd, hv⟩ := hden v
    rw [← Submodule.Quotient.mk_eq_zero]
    apply hcancel d _ hd
    change d • q (P0 v) = 0
    rw [← map_smul, ← map_smul, show d • v = ((⟨d • v, hv⟩ : L) : V) from rfl, hP0]
    exact (Submodule.Quotient.mk_eq_zero W).2 (hW _)
  · obtain ⟨d, hd, hv⟩ := hden w
    have h0 : qL ⟨d • w, hv⟩ = 0 := by
      apply Subtype.ext
      change q (d • w) = 0
      rw [map_smul]
      change d • (Submodule.Quotient.mk w : V ⧸ W) = 0
      rw [(Submodule.Quotient.mk_eq_zero W).2 hw, smul_zero]
    have h1 : d • P0 w = d • w := by
      rw [← map_smul, show d • w = ((⟨d • w, hv⟩ : L) : V) from rfl, hP0, hp0, h0, map_zero]
      simp
    rw [hP]
    rw [← IsScalarTower.algebraMap_smul K d, ← IsScalarTower.algebraMap_smul K d w] at h1
    exact smul_right_injective V (by simpa using hd) h1
  · rw [hP, show v = ((⟨v, hv⟩ : L) : V) from rfl, hP0, hp0]
    exact L.sub_mem hv (s _).2

end Lattices

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem hsym (x y : S.V) : star (S.hT x y) = S.hT y x := S.herm.eq x y

theorem hsmul (c : E) (x y : S.V) : S.hT (c • x) y = star c * S.hT x y := by
  simp [starRingEnd_apply]

theorem mem_orth {U : Submodule E S.V} {x : S.V} : x ∈ orth S U ↔ ∀ y ∈ U, S.hT y x = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem mem_orth_span {s : Set S.V} {x : S.V} :
    x ∈ orth S (Submodule.span E s) ↔ ∀ y ∈ s, S.hT y x = 0 := by
  rw [mem_orth]
  refine ⟨fun h y hy => h y (Submodule.subset_span hy), fun h y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => rw [hsmul, hx, mul_zero]

theorem exists_rep (φ : S.V →ₗ[E] E) : ∃ y, ∀ x, S.hT y x = φ x := by
  have h1 : (LinearMap.range S.hT).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    exact S.nondeg.2 x fun y => hx _ ⟨y, rfl⟩
  have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range S.hT)
  rw [h1, Submodule.dualAnnihilator_bot] at h2
  have h3 : φ ∈ LinearMap.range S.hT := h2 ▸ Submodule.mem_top
  obtain ⟨y, hy⟩ := h3
  exact ⟨y, fun x => by rw [← hy]⟩

abbrev FI (E : Type) [Field E] [NumberField E] : Type := FractionalIdeal (nonZeroDivisors (𝓞 E)) E

omit [StarRing E] in
theorem mem_one_iff (x : E) : x ∈ (1 : FI E) ↔ IsIntegral ℤ x := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.isIntegral_coe
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem star_int {x : E} (h : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  map_isIntegral_int (starRingEnd E) h

theorem mem_unimod {Λ : Submodule (𝓞 E) S.V} (hu : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (x : S.V) :
    x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (S.hT y x) := by
  conv_lhs => rw [← hu]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one]
  refine forall_congr' fun y => forall_congr' fun hy => ?_
  constructor
  · rintro ⟨o, ho⟩
    have ho' : (o : E) = S.hT y x := ho
    rw [← ho']
    exact o.isIntegral_coe
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

def StarStable (I : FI E) : Prop := ∀ x ∈ I, star x ∈ I

theorem starStable_one : StarStable (1 : FI E) := fun x hx =>
  (mem_one_iff _).2 (star_int ((mem_one_iff _).1 hx))

theorem StarStable.mul {I J : FI E} (hI : StarStable I) (hJ : StarStable J) : StarStable (I * J) := by
  intro x hx
  refine FractionalIdeal.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [star_mul']
    exact FractionalIdeal.mul_mem_mul (hI a ha) (hJ b hb)
  · rw [star_add]
    exact Submodule.add_mem (I * J : FI E).1 ha hb

omit [StarRing E] in
theorem mem_inv {I : FI E} (h0 : I ≠ 0) (x : E) : x ∈ I⁻¹ ↔ ∀ y ∈ I, IsIntegral ℤ (x * y) := by
  rw [FractionalIdeal.mem_inv_iff h0]
  simp only [mem_one_iff]

theorem StarStable.inv {I : FI E} (hI : StarStable I) (h0 : I ≠ 0) : StarStable I⁻¹ := by
  intro x hx
  rw [mem_inv h0] at hx ⊢
  intro y hy
  have := star_int (hx _ (hI y hy))
  rwa [star_mul, star_star, mul_comm] at this

theorem StarStable.pow {I : FI E} (hI : StarStable I) (n : ℕ) : StarStable (I ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact starStable_one
  | succ n ih => rw [pow_succ]; exact ih.mul hI

theorem StarStable.zpow {I : FI E} (hI : StarStable I) (h0 : I ≠ 0) (n : ℤ) : StarStable (I ^ n) := by
  cases n with
  | ofNat n => simpa using hI.pow n
  | negSucc n => rw [zpow_negSucc]; exact (hI.pow _).inv (pow_ne_zero _ h0)

def idSpan (I : Fin r → FI E) (v : Fin r → S.V) : Submodule (𝓞 E) S.V :=
  Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ I a ∧ y = x • v a}

theorem smul_mem_idSpan {I : Fin r → FI E} (v : Fin r → S.V) {a : Fin r} {x : E} (hx : x ∈ I a) :
    x • v a ∈ idSpan I v := Submodule.subset_span ⟨a, x, hx, rfl⟩

theorem osmul (o : 𝓞 E) (x : S.V) : o • x = (o : E) • x := (IsScalarTower.algebraMap_smul E o x).symm

def IsHyp (e f : Fin r → S.V) : Prop :=
  (∀ a b, S.hT (e a) (e b) = 0) ∧ (∀ a b, S.hT (f a) (f b) = 0) ∧
    ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0

theorem IsHyp.fe {e f : Fin r → S.V} (h : IsHyp e f) (a b : Fin r) :
    S.hT (f a) (e b) = if a = b then 1 else 0 := by
  rw [← hsym, h.2.2]
  by_cases hab : a = b
  · simp [hab]
  · simp [hab, Ne.symm hab]

theorem pair_idSpan {e f : Fin r → S.V} (h : IsHyp e f) {B : Fin r → FI E} (h0 : ∀ a, B a ≠ 0)
    {x : S.V} (hx : x ∈ idSpan (fun a => (B a)⁻¹) e) (a : Fin r) {β : E} (hβ : β ∈ B a) :
    IsIntegral ℤ (β * S.hT (f a) x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, c, hc, rfl⟩ := hx
    rw [map_smul, h.fe]
    split_ifs with hab
    · subst hab
      rw [smul_eq_mul, mul_one, mul_comm]
      exact (mem_inv (h0 a) c).1 hc β hβ
    · simpa using isIntegral_zero
  | zero => simpa using isIntegral_zero
  | add x y _ _ hx hy => rw [map_add, mul_add]; exact hx.add hy
  | smul c x _ hx =>
    rw [osmul, map_smul, smul_eq_mul, mul_left_comm]
    exact c.isIntegral_coe.mul hx

theorem exists_dual_frame (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) {e f : Fin r → S.V} (h : IsHyp e f) {z : S.V}
    (hez : ∀ a, S.hT (e a) z = 0) (hfz : ∀ a, S.hT (f a) z = 0)
    {B : Fin r → FI E} (h0 : ∀ a, B a ≠ 0) (hB : ∀ a, StarStable (B a))
    {Λ : Submodule (𝓞 E) S.V} (hl : Submodule.IsLattice E Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (hz : z ∈ Λ)
    (hX : Λ ⊓ toO S (Submodule.span E (Set.range e)) = idSpan (fun a => (B a)⁻¹) e)
    (hprim : ∀ (c : E), ∀ x ∈ Submodule.span E (Set.range e), x + c • z ∈ Λ → ∃ o : 𝓞 E, (o : E) = c) :
    ∃ f' : Fin r → S.V, IsHyp e f' ∧ (∀ a, S.hT (f' a) z = 0) ∧ ∀ a, ∀ β ∈ B a, β • f' a ∈ Λ := by
  obtain ⟨t, ht⟩ := GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram E hE
  obtain ⟨P, hPU, hPid, hPL⟩ := exists_proj Λ hl.fg hl.span_eq_top
    (Submodule.span E (Set.range e) ⊔ Submodule.span E {z})
  choose g hg using fun a => exists_rep (S := S) (S.hT (f a) ∘ₗ P)
  have hge : ∀ a b, S.hT (g a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [hg, LinearMap.comp_apply, hPid _ (Submodule.mem_sup_left (Submodule.subset_span ⟨b, rfl⟩)), h.fe]
  have heg : ∀ a b, S.hT (e a) (g b) = if a = b then 1 else 0 := by
    intro a b
    rw [← hsym, hge]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have hgz : ∀ a, S.hT (g a) z = 0 := by
    intro a
    rw [hg, LinearMap.comp_apply, hPid _ (Submodule.mem_sup_right (Submodule.subset_span rfl)), hfz]
  have hgL : ∀ a, ∀ β ∈ B a, β • g a ∈ Λ := by
    intro a β hβ
    rw [mem_unimod hu]
    intro y hy
    rw [← hsym, hsmul, hg, LinearMap.comp_apply]
    apply star_int
    obtain ⟨x, hx, w, hw, hxw⟩ := Submodule.mem_sup.1 (hPU y)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have hm : x + c • z ∈ Λ := hxw ▸ hPL y hy
    obtain ⟨o, rfl⟩ := hprim c x hx hm
    have hxL : x ∈ Λ := by
      have := Λ.sub_mem hm (Λ.smul_mem o hz)
      rwa [osmul, add_sub_cancel_right] at this
    rw [← hxw, map_add, map_smul, hfz, smul_zero, add_zero]
    exact pair_idSpan h h0 (hX ▸ ⟨hxL, hx⟩) a (hB a β hβ)
  refine ⟨fun b => g b - ∑ a, ((t : E) * S.hT (g a) (g b)) • e a, ⟨h.1, fun a b => ?_, fun a b => ?_⟩,
    fun a => ?_, fun b β hβ => ?_⟩
  · simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, hsmul, map_smul, h.1, hge, heg,
      smul_eq_mul, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, star_mul, hsym]
    linear_combination (-(S.hT (g a) (g b))) * ht
  · simp only [map_sub, map_sum, map_smul, h.1, heg, smul_eq_mul, mul_zero, Finset.sum_const_zero, sub_zero]
  · simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, hsmul, hez, hgz, mul_zero,
      Finset.sum_const_zero, sub_zero]
  · rw [smul_sub, Finset.smul_sum]
    refine Λ.sub_mem (hgL b β hβ) (Λ.sum_mem fun a _ => ?_)
    rw [smul_smul]
    have : (β * ((t : E) * S.hT (g a) (g b))) • e a ∈ idSpan (fun a => (B a)⁻¹) e := by
      apply smul_mem_idSpan
      rw [mem_inv (h0 a)]
      intro y hy
      have h1 := (mem_unimod hu _).1 (hgL b β hβ) _ (hgL a _ (hB a y hy))
      rw [hsmul, star_star, map_smul, smul_eq_mul] at h1
      have h2 := t.isIntegral_coe.mul h1
      have e1 : β * ((t : E) * S.hT (g a) (g b)) * y = (t : E) * (y * (β * S.hT (g a) (g b))) := by ring
      rw [e1]
      exact h2
    rw [← hX] at this
    exact this.1

def prj (e f : Fin r → S.V) : S.V →ₗ[E] S.V :=
  LinearMap.id - ∑ a, (S.hT (f a)).smulRight (e a) - ∑ a, (S.hT (e a)).smulRight (f a)

theorem prj_apply (e f : Fin r → S.V) (v : S.V) :
    prj e f v = v - ∑ a, S.hT (f a) v • e a - ∑ a, S.hT (e a) v • f a := by
  simp [prj, LinearMap.sum_apply]

theorem e_prj {e f : Fin r → S.V} (h : IsHyp e f) (a : Fin r) (v : S.V) : S.hT (e a) (prj e f v) = 0 := by
  simp [prj_apply, map_sum, h.1, h.2.2]

theorem f_prj {e f : Fin r → S.V} (h : IsHyp e f) (a : Fin r) (v : S.V) : S.hT (f a) (prj e f v) = 0 := by
  simp [prj_apply, map_sum, h.2.1, h.fe]

theorem prj_prj {e f : Fin r → S.V} (h : IsHyp e f) (u v : S.V) :
    S.hT (prj e f u) (prj e f v) = S.hT u v - ∑ a, S.hT (f a) v * star (S.hT (e a) u) -
      ∑ a, S.hT (e a) v * star (S.hT (f a) u) := by
  have h1 : S.hT (prj e f u) (prj e f v) = S.hT u (prj e f v) := by
    rw [prj_apply e f u]
    simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, hsmul, e_prj h, f_prj h, mul_zero,
      Finset.sum_const_zero, sub_zero]
  rw [h1, prj_apply]
  simp only [map_sub, map_sum, map_smul, smul_eq_mul, hsym]

def chg (e f f' : Fin r → S.V) : S.V →ₗ[E] S.V :=
  ∑ a, (S.hT (f' a)).smulRight (e a) + prj e f ∘ₗ prj e f' + ∑ a, (S.hT (e a)).smulRight (f a)

theorem chg_apply (e f f' : Fin r → S.V) (v : S.V) :
    chg e f f' v = ∑ a, S.hT (f' a) v • e a + prj e f (prj e f' v) + ∑ a, S.hT (e a) v • f a := by
  simp [chg, LinearMap.sum_apply]

theorem chg_isom {e f f' : Fin r → S.V} (h : IsHyp e f) (h' : IsHyp e f') (u v : S.V) :
    S.hT (chg e f f' u) (chg e f f' v) = S.hT u v := by
  have h1 : ∀ a v, S.hT (e a) (chg e f f' v) = S.hT (e a) v := by
    intro a v
    simp [chg_apply, map_sum, h.1, h.2.2, e_prj h]
  have h2 : ∀ a v, S.hT (f a) (chg e f f' v) = S.hT (f' a) v := by
    intro a v
    simp [chg_apply, map_sum, h.2.1, h.fe, f_prj h]
  have h3 : ∀ v, prj e f (chg e f f' v) = prj e f (prj e f' v) := by
    intro v
    rw [prj_apply e f (chg e f f' v)]
    simp only [h1, h2]
    rw [chg_apply]
    abel
  have h4 := prj_prj h (chg e f f' u) (chg e f f' v)
  have h5 := prj_prj h (prj e f' u) (prj e f' v)
  have h6 := prj_prj h' u v
  simp only [h1, h2, h3] at h4
  simp only [e_prj h', star_zero, mul_zero, zero_mul, Finset.sum_const_zero, sub_zero] at h5
  linear_combination h5 + h6 - h4

theorem chg_of_orth {e f f' : Fin r → S.V} (h' : IsHyp e f') {x : S.V} (hx : ∀ a, S.hT (e a) x = 0) :
    chg e f f' x = x - ∑ a, S.hT (f a) (prj e f' x) • e a := by
  rw [chg_apply, prj_apply e f]
  simp only [e_prj h', hx, zero_smul, Finset.sum_const_zero, sub_zero, add_zero]
  rw [prj_apply e f' x]
  simp only [hx, zero_smul, Finset.sum_const_zero, sub_zero]
  abel

theorem exists_chg {e f f' : Fin r → S.V} (h : IsHyp e f) (h' : IsHyp e f') :
    ∃ n : S.V ≃ₗ[E] S.V, n ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ ∀ v, n v = chg e f f' v := by
  have hi : Function.Injective (chg e f f') := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine S.nondeg.2 x fun y => ?_
    rw [← chg_isom h h', hx, map_zero]
  exact ⟨LinearEquiv.ofInjectiveEndo _ hi, fun x y => chg_isom h h' x y, fun v => rfl⟩

theorem exists_split (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) {e f : Fin r → S.V} (h : IsHyp e f) {z : S.V}
    (hez : ∀ a, S.hT (e a) z = 0) (hfz : ∀ a, S.hT (f a) z = 0)
    {B : Fin r → FI E} (h0 : ∀ a, B a ≠ 0) (hB : ∀ a, StarStable (B a))
    {Λ : Submodule (𝓞 E) S.V} (hl : Submodule.IsLattice E Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (hz : z ∈ Λ)
    (hX : Λ ⊓ toO S (Submodule.span E (Set.range e)) = idSpan (fun a => (B a)⁻¹) e)
    (hprim : ∀ (c : E), ∀ x ∈ Submodule.span E (Set.range e), x + c • z ∈ Λ → ∃ o : 𝓞 E, (o : E) = c) :
    ∃ n : S.V ≃ₗ[E] S.V, n ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ a, n (e a) = e a) ∧ n z = z ∧
      (∀ x ∈ orth S (Submodule.span E (Set.range e)), n x - x ∈ Submodule.span E (Set.range e)) ∧
      Formalism.HermitianLatticesTheory.gmap n Λ = idSpan (fun a => (B a)⁻¹) e ⊔
        (Formalism.HermitianLatticesTheory.gmap n Λ ⊓ toO S (orth S (Submodule.span E (Set.range e ∪ Set.range f)))) ⊔ idSpan B f := by
  obtain ⟨f', h', hf'z, hf'L⟩ := exists_dual_frame hE h hez hfz h0 hB hl hu hz hX hprim
  obtain ⟨n, hn, hnv⟩ := exists_chg h h'
  have hne : ∀ a, n (e a) = e a := by
    intro a
    have : prj e f' (e a) = 0 := by simp [prj_apply, h.1, h'.fe]
    rw [hnv, chg_of_orth h' (fun b => h.1 b a), this]
    simp
  have hnf : ∀ a, n (f' a) = f a := by
    intro a
    have : prj e f' (f' a) = 0 := by simp [prj_apply, h'.2.1, h'.2.2]
    rw [hnv, chg_apply, this]
    simp [h'.2.1, h'.2.2]
  have heL : ∀ a, ∀ x ∈ (B a)⁻¹, x • e a ∈ Λ := by
    intro a x hx
    have := smul_mem_idSpan (I := fun a => (B a)⁻¹) e hx
    rw [← hX] at this
    exact this.1
  refine ⟨n, hn, hne, ?_, fun x hx => ?_, le_antisymm ?_ (sup_le (sup_le ?_ inf_le_left) ?_)⟩
  · have : prj e f' z = z := by simp [prj_apply, hez, hf'z]
    rw [hnv, chg_of_orth h' hez, this]
    simp [hfz]
  · rw [hnv, chg_of_orth h' (fun a => mem_orth_span.1 hx _ ⟨a, rfl⟩), sub_sub_cancel_left]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  · rintro _ ⟨v, hv, rfl⟩
    have h1 : ∀ a, S.hT (f' a) v ∈ (B a)⁻¹ := by
      intro a
      rw [mem_inv (h0 a)]
      intro y hy
      have := (mem_unimod hu v).1 hv _ (hf'L a _ (hB a y hy))
      rwa [hsmul, star_star, mul_comm] at this
    have h2 : ∀ a, S.hT (e a) v ∈ B a := by
      intro a
      rw [← inv_inv (B a), mem_inv (inv_ne_zero (h0 a))]
      intro y hy
      have := (mem_unimod hu v).1 hv _ (heL a _ ((hB a).inv (h0 a) y hy))
      rwa [hsmul, star_star, mul_comm] at this
    have h3 : prj e f' v ∈ Λ := by
      rw [prj_apply]
      exact Λ.sub_mem (Λ.sub_mem hv (Λ.sum_mem fun a _ => heL a _ (h1 a)))
        (Λ.sum_mem fun a _ => hf'L a _ (h2 a))
    show n v ∈ _
    rw [hnv, chg_apply]
    refine Submodule.add_mem_sup (Submodule.add_mem_sup ?_ ⟨⟨_, h3, ?_⟩, ?_⟩) ?_
    · exact Submodule.sum_mem _ fun a _ => smul_mem_idSpan (I := fun a => (B a)⁻¹) e (h1 a)
    · show n _ = _
      rw [hnv, chg_apply]
      simp [e_prj h', f_prj h', prj_apply e f' (prj e f' v)]
    · refine mem_orth_span.2 ?_
      rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
      · exact e_prj h a _
      · exact f_prj h a _
    · exact Submodule.sum_mem _ fun a _ => smul_mem_idSpan f (h2 a)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, hx, rfl⟩
    refine ⟨_, heL a x hx, ?_⟩
    show n _ = _
    rw [map_smul, hne]
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, hx, rfl⟩
    refine ⟨_, hf'L a x hx, ?_⟩
    show n _ = _
    rw [map_smul, hnf]

theorem orth_iff (U : Submodule E S.V) (n : S.V ≃ₗ[E] S.V) (hi : n ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hn : ∀ x ∈ U, n x = x) (x : S.V) : n x ∈ orth S U ↔ x ∈ orth S U := by
  rw [mem_orth, mem_orth]
  refine forall_congr' fun y => forall_congr' fun hy => ?_
  have h := hi y x
  rw [hn y hy] at h
  rw [h]

theorem Lsub_gmap_le {T : E} (F : LFlag S r T) (Λ : Submodule (𝓞 E) S.V) (n : S.V ≃ₗ[E] S.V)
    (hi : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hn : ∀ x ∈ Xsp F, n x = x)
    (hq : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) :
    Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) F ≤ Lsub Λ F := by
  unfold Lsub
  refine inf_le_inf_right _ (sup_le ?_ le_sup_right)
  rintro _ ⟨⟨l, hl, rfl⟩, hlo⟩
  have hlo' : l ∈ orth S (Xsp F) := (orth_iff _ n hi hn l).1 hlo
  have e : n l = l + (n l - l) := by abel
  show n l ∈ _
  rw [e]
  exact Submodule.add_mem_sup ⟨hl, hlo'⟩ (hq l hlo')

theorem XLam_gmap {T : E} (F : LFlag S r T) (Λ : Submodule (𝓞 E) S.V) (n : S.V ≃ₗ[E] S.V)
    (hn : ∀ x ∈ Xsp F, n x = x) : XLam (Formalism.HermitianLatticesTheory.gmap n Λ) F = XLam Λ F := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, hyx⟩, hx⟩
    have : y = x := n.injective ((show n y = x from hyx).trans (hn x hx).symm)
    exact ⟨this ▸ hy, hx⟩
  · rintro ⟨hx, hx'⟩
    exact ⟨⟨x, hx, hn x hx'⟩, hx'⟩

end Generic

theorem ddS_ne_zero (D : D7) : ddS D ≠ 0 := by
  unfold ddS
  rw [FractionalIdeal.coeIdeal_ne_zero, Ne, Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective _ _)]
  exact differentIdeal_ne_bot

theorem starStable_ddS (D : D7) : StarStable (ddS D) := by
  intro x hx
  unfold ddS at hx ⊢
  obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
  clear hx
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    have : star (algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) w)) =
        algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) w) :=
      (D.sp.cm.fixed _).2 ⟨(w : D.host.F), rfl⟩
    rw [this]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem _ hw)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, star_add]; exact Submodule.add_mem (FractionalIdeal.coeToSubmodule _) ha hb
  | smul c a _ ha =>
    rw [smul_eq_mul, map_mul, star_mul, mul_comm]
    exact Submodule.smul_mem (FractionalIdeal.coeToSubmodule _)
      (⟨star (c : D.host.E), star_int c.isIntegral_coe⟩ : 𝓞 D.host.E) ha

theorem main : ∀ (D : D7) (u : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), IsBase D u F0 → IsRowLat D F0 Λ → 1 ≤ Tu D u → ∃ n : ((hS D).V ≃ₗ[D.host.E] (hS D).V), FixFr D (lf D F0) n ∧ IsSplit D F0 (Formalism.HermitianLatticesTheory.gmap n Λ) ∧ IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap n Λ) := by
  rintro D u F0 Λ ⟨he, hz⟩ ⟨hgen, ⟨hl, hu, hlift, hloc, hprim⟩, hX⟩ -
  have h : IsHyp (S := hS D) F0.e D.sp.hypF := by
    rw [he]; exact ⟨D.sp.hyp_ee, D.sp.hyp_ff, D.sp.hyp_ef⟩
  have hXS : XS D F0 = idSpan (S := hS D) (fun a => (ddS D ^ ((D.R.rS : ℤ) - (a : ℕ)))⁻¹) F0.e := by
    simp only [XS, idSpan, _root_.zpow_neg]
  have hfz : ∀ a, (hS D).hT (D.sp.hypF a) F0.z = 0 := by
    intro a
    rw [hz]
    show (hS D).hT (D.sp.hypF a) ((D.cOf u)⁻¹ • D.sp.zm) = 0
    rw [map_smul, ← hsym, (D.sp.hyp_orthz a).2]
    simp
  have hzo : F0.z ∈ orth (hS D) F0.X := mem_orth_span.2 (by rintro _ ⟨a, rfl⟩; exact F0.z_orth a)
  have hXo : ∀ x ∈ F0.X, x ∈ orth (hS D) F0.X := by
    intro x hx
    refine Submodule.span_le.2 ?_ hx
    rintro _ ⟨b, rfl⟩
    exact mem_orth_span.2 (by rintro _ ⟨a, rfl⟩; exact F0.e_iso a b)
  obtain ⟨n, hn, hne, hnz, hq, hs⟩ := exists_split (S := hS D) D.sp.cm.cmUnram h F0.z_orth hfz
    (B := fun a => ddS D ^ ((D.R.rS : ℤ) - (a : ℕ))) (fun a => zpow_ne_zero _ (ddS_ne_zero D))
    (fun a => (starStable_ddS D).zpow (ddS_ne_zero D) _) hl hu hlift.1 (hX.trans hXS) (by
      intro c x hx hm
      apply hprim c
      refine ⟨?_, Submodule.smul_mem (orth (hS D) F0.X) c hzo⟩
      have e : c • F0.z = (x + c • F0.z) + -x := by abel
      show c • F0.z ∈ _
      rw [e]
      exact Submodule.add_mem_sup ⟨hm, Submodule.add_mem (orth (hS D) F0.X) (hXo x hx)
        (Submodule.smul_mem _ c hzo)⟩ (F0.X.neg_mem hx))
  have hnX : ∀ x ∈ F0.X, n x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hne a
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  have hXL := XLam_gmap (lf D F0) Λ n hnX
  obtain ⟨-, -, -, hu', hl'⟩ := Formalism.HermitianLatticesTheory.isomAct _ _ _ (hS D).hT n hn Λ
  obtain ⟨heq, hsg, -⟩ := Formalism.HermitianLatticesTheory.genusBasic (𝓞 D.host.E) D.host.E _ (hS D).hT (hS D).herm
    (fun r => ⟨⟨_, star_int r.isIntegral_coe⟩, rfl⟩)
  refine ⟨n, ⟨hn, fun b => ?_, hq⟩, ?_, ⟨hl'.2 hl, heq.trans hgen.2 (hsg Λ n hn)⟩,
    ⟨hl'.2 hl, hu'.2 hu, ⟨⟨_, hlift.1, hnz⟩, rfl⟩, ?_, fun c hc => ?_⟩, hXL.trans hX⟩
  · refine Fin.lastCases ?_ (fun a => ?_) b
    · simpa [frame, FlagG.fvec] using hnz
    · simpa [frame, FlagG.fvec] using hne a
  · unfold IsSplit
    rw [hXS, Wb, ← he]
    exact hs
  · rw [hXL]; exact hloc
  · exact hprim c (Lsub_gmap_le (lf D F0) Λ n hn hnX hq hc)

end GlobalTheory.LoopC.RowSplit

end
