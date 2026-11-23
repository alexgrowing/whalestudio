import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

noncomputable section

namespace GlobalTheory.ShFam.DatOf

open NumberField Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.Pj.DatLin
open scoped TensorProduct Pointwise nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lattice

open FractionalIdeal

def lat (D : D7) (S : HSpace D.host.E) : Submodule (𝓞 D.host.E) S.V :=
  Submodule.span (𝓞 D.host.E) {v | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ S.L0, v = a • x}

def formQ (D : D7) (S : HSpace D.host.E) : lat D S →ₗ[ℤ] lat D S →ₗ[ℤ] ℚ :=
  LinearMap.mk₂ ℤ (fun x y => Algebra.trace ℚ D.host.E (D.host.xi0 * S.hT x y))
    (fun x x' y => by simp [map_add, mul_add])
    (fun c x y => by simp [map_zsmul]; rw [mul_left_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul])
    (fun x y y' => by simp [map_add, mul_add])
    (fun c x y => by simp [map_zsmul]; rw [mul_left_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul])

def FormInt (D : D7) (S : HSpace D.host.E) : Prop := ∀ x y : lat D S, ∃ n : ℤ, formQ D S x y = n

theorem formQ_adj (D : D7) (S : HSpace D.host.E) (a : 𝓞 D.host.E) (x y : lat D S) :
    formQ D S (a • x) y = formQ D S x (barE D a • y) := by
  simp only [formQ, LinearMap.mk₂_apply, Submodule.coe_smul]
  rw [← algebraMap_smul D.host.E a (x : S.V), ← algebraMap_smul D.host.E (barE D a) (y : S.V),
    LinearMap.map_smulₛₗ₂, map_smul]
  rfl

theorem formQ_alt (D : D7) (S : HSpace D.host.E) (x : lat D S) : formQ D S x x = 0 := by
  simp only [formQ, LinearMap.mk₂_apply]
  have hh : IsCMField.complexConj D.host.E (S.hT x x) = S.hT x x :=
    LinearMap.isSymm_def.1 S.herm x x
  have hz : IsCMField.complexConj D.host.E (D.host.xi0 * S.hT x x) =
      -(D.host.xi0 * S.hT x x) := by
    rw [map_mul, conj_xi0_alt, hh, neg_mul]
  have ht := Formalism.L2.Pj.trace_cc D (D.host.xi0 * S.hT x x)
  rw [hz, map_neg] at ht
  linarith

theorem lat_fin (D : D7) (S : HSpace D.host.E) : Module.Finite (𝓞 D.host.E) (lat D S) := by
  obtain ⟨a, ha, hAA⟩ := D.host.AA.isFractional
  have ha0 : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero ha (IsFractionRing.injective _ D.host.E (h0.trans (map_zero _).symm))
  let f : S.V →ₗ[𝓞 D.host.E] S.V :=
    (LinearMap.lsmul D.host.E S.V (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹).restrictScalars (𝓞 D.host.E)
  have hN : (S.L0.map f).FG := S.standardTuple_isLattice.fg.map f
  have hle : lat D S ≤ S.L0.map f := by
    rw [lat, Submodule.span_le]
    rintro v ⟨b, hb, x, hx, rfl⟩
    obtain ⟨d, hd⟩ := hAA b hb
    refine ⟨d • x, S.L0.smul_mem d hx, ?_⟩
    show (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ • (d • x) = b • x
    rw [← algebraMap_smul D.host.E d x, hd, Algebra.smul_def, smul_smul, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
  exact Module.Finite.iff_fg.2 (isNoetherian_submodule.1 (isNoetherian_of_fg_of_noetherian _ hN) _ hle)

theorem lat_proj (D : D7) (S : HSpace D.host.E) : Module.Projective (𝓞 D.host.E) (lat D S) := by
  have := lat_fin D S
  have hF : Module.Flat (𝓞 D.host.E) (lat D S) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨⟨r, hr⟩, hrx⟩ := (Submodule.mem_torsion_iff x).1 hx
    have h0 : r • x = 0 := hrx
    have h1 : r • (x : S.V) = 0 := by rw [← Submodule.coe_smul, h0]; rfl
    rw [← algebraMap_smul D.host.E r (x : S.V), smul_eq_zero] at h1
    rcases h1 with h | h
    · exact absurd (IsFractionRing.injective _ D.host.E (h.trans (map_zero _).symm)) (nonZeroDivisors.ne_zero hr)
    · exact (Submodule.mem_bot _).2 (Subtype.ext h)
  have := Module.finitePresentation_of_finite (𝓞 D.host.E) (lat D S)
  exact Module.Flat.projective_of_finitePresentation

theorem exists_smul_mem_base (D : D7) (S : HSpace D.host.E) (y : S.V) :
    ∃ s ∈ (𝓞 D.host.E)⁰, s • y ∈ S.L0 := by
  have hy : y ∈ Submodule.span D.host.E (S.L0 : Set S.V) := by
    rw [S.standardTuple_isLattice.span_eq_top]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_mem _, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_mem _, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add x z _ _ hx hz =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    rw [smul_add, mul_comm s t, mul_smul, mul_comm t s, mul_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ t hsx) (Submodule.smul_mem _ s htz)
  | smul c x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) c
    refine ⟨b * s, mul_mem hb hs, ?_⟩
    have hb0 : algebraMap (𝓞 D.host.E) D.host.E b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have e : (b * s) • ((algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E b) • x)
        = a • (s • x) := by
      rw [← algebraMap_smul D.host.E (b * s), ← algebraMap_smul D.host.E a, ← algebraMap_smul D.host.E s,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [e]
    exact Submodule.smul_mem _ a hsx

theorem exists_smul_mem_lat (D : D7) (S : HSpace D.host.E) (y : S.V) :
    ∃ s ∈ (𝓞 D.host.E)⁰, s • y ∈ lat D S := by
  obtain ⟨s, hs, hsy⟩ := exists_smul_mem_base D S y
  set n : 𝓞 D.host.E := ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E)
  have hn : algebraMap (𝓞 D.host.E) D.host.E n = ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) := by
    simp [n]
  have hn0 : n ∈ (𝓞 D.host.E)⁰ := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    apply normK_ne_zero D
    rw [← hn, h0, map_zero]
  refine ⟨n * s, mul_mem hn0 hs, ?_⟩
  rw [mul_smul, ← algebraMap_smul D.host.E n, hn]
  exact Submodule.subset_span ⟨_, normK_mem_AA D, s • y, hsy, rfl⟩

theorem lat_isLocalized (D : D7) (S : HSpace D.host.E) :
    IsLocalizedModule (𝓞 D.host.E)⁰ (lat D S).subtype where
  map_units x := by
    rw [Module.End.isUnit_iff]
    have hx0 : algebraMap (𝓞 D.host.E) D.host.E x ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
    have e : ∀ v : S.V, algebraMap (𝓞 D.host.E) (Module.End (𝓞 D.host.E) S.V) x v =
        algebraMap (𝓞 D.host.E) D.host.E x • v := by
      intro v
      rw [Module.algebraMap_end_apply, algebraMap_smul]
    constructor
    · intro v w h
      rw [e, e] at h
      exact smul_right_injective _ hx0 h
    · intro v
      refine ⟨(algebraMap (𝓞 D.host.E) D.host.E x)⁻¹ • v, ?_⟩
      rw [e, smul_smul, mul_inv_cancel₀ hx0, one_smul]
  surj y := by
    obtain ⟨s, hs, hsy⟩ := exists_smul_mem_lat D S y
    exact ⟨(⟨s • y, hsy⟩, ⟨s, hs⟩), rfl⟩
  exists_of_eq {x₁ x₂} h := ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext h⟩

theorem lat_finrank (D : D7) (S : HSpace D.host.E) :
    Module.finrank (𝓞 D.host.E) (lat D S) = Module.finrank D.host.E S.V := by
  have := lat_isLocalized D S
  rw [IsFractionRing.finrank_right_eq (R := 𝓞 D.host.E) (S := D.host.E) (N := S.V)]
  exact (IsLocalizedModule.finrank_eq (p := (𝓞 D.host.E)⁰) (f := (lat D S).subtype) le_rfl).symm

theorem herm_int (D : D7) (S : HSpace D.host.E) {x y : S.V} (hx : x ∈ S.L0) (hy : y ∈ S.L0) :
    S.hT x y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  have hy' : y ∈ Formalism.HermitianLatticesTheory.dual S.hT S.L0 := by
    rw [S.baseLattice_isUnimodular]; exact hy
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hy'
  exact hy' x hx

theorem herm_gen_mem (D : D7) (S : HSpace D.host.E) {a b : D.host.E} (ha : a ∈ D.host.AA) (hb : b ∈ D.host.AA)
    {x y : S.V} (hx : x ∈ S.L0) (hy : y ∈ S.L0) :
    S.hT (a • x) (b • y) ∈ NAA D := by
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (herm_int D S hx hy)
  have e : S.hT (a • x) (b • y) = r • (b * D.host.conj a) := by
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    have hs : (starRingEnd D.host.E) a = D.host.conj a := bridge_star_holds D.R D.host a
    rw [Algebra.smul_def, hr, hs]; ring
  rw [e]
  exact Submodule.smul_mem _ r (mul_mem_mul hb (conj_mem_AAbar D ha))

theorem herm_lat_mem (D : D7) (S : HSpace D.host.E) {v w : S.V} (hv : v ∈ lat D S) (hw : w ∈ lat D S) :
    S.hT v w ∈ NAA D := by
  induction hv using Submodule.span_induction generalizing w with
  | mem v hv =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hv
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨b, hb, y, hy, rfl⟩ := hw
      exact herm_gen_mem D S ha hb hx hy
    | zero => simp
    | add w w' _ _ h h' => rw [map_add]; exact add_mem h h'
    | smul c w _ h =>
      rw [← algebraMap_smul D.host.E c w, map_smul, smul_eq_mul, ← Algebra.smul_def]
      exact Submodule.smul_mem _ c h
  | zero => simp
  | add v v' _ _ h h' => rw [map_add, LinearMap.add_apply]; exact add_mem (h hw) (h' hw)
  | smul c v _ h =>
    rw [← algebraMap_smul D.host.E c v, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    have hc : (starRingEnd D.host.E) (algebraMap (𝓞 D.host.E) D.host.E c) =
        algebraMap (𝓞 D.host.E) D.host.E (barE D c) := (barE_eq_star D c).symm
    rw [hc, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (h hw)

theorem formInt (D : D7) (S : HSpace D.host.E) : FormInt D S := fun x y =>
  trace_int_of_mem Formalism.IndefR.Fin.factPrincipalDatum D (herm_lat_mem D S x.2 y.2)

def repOf (D : D7) (S : HSpace D.host.E) (f : lat D S →ₗ[ℤ] ℤ) (y : lat D S) : D.host.E :=
  (trace_rep D (f.comp ((LinearMap.toSpanSingleton (𝓞 D.host.E) (lat D S) y).restrictScalars ℤ))).choose

theorem repOf_spec (D : D7) (S : HSpace D.host.E) (f : lat D S →ₗ[ℤ] ℤ) (y : lat D S) (c : 𝓞 D.host.E) :
    Algebra.trace ℚ D.host.E (repOf D S f y * algebraMap (𝓞 D.host.E) D.host.E c) = f (c • y) :=
  (trace_rep D _).choose_spec c

def repMap (D : D7) (S : HSpace D.host.E) (f : lat D S →ₗ[ℤ] ℤ) : lat D S →ₗ[𝓞 D.host.E] D.host.E where
  toFun := repOf D S f
  map_add' y y' := by
    have := trace_sep D (w := repOf D S f (y + y') - (repOf D S f y + repOf D S f y')) (fun c => by
      rw [sub_mul, add_mul, map_sub, map_add, repOf_spec, repOf_spec, repOf_spec, smul_add, map_add]
      push_cast; ring)
    exact sub_eq_zero.1 this
  map_smul' c' y := by
    have := trace_sep D (w := repOf D S f (c' • y) - algebraMap (𝓞 D.host.E) D.host.E c' * repOf D S f y) (fun c => by
      rw [sub_mul, map_sub, repOf_spec,
        show algebraMap (𝓞 D.host.E) D.host.E c' * repOf D S f y * algebraMap (𝓞 D.host.E) D.host.E c =
          repOf D S f y * algebraMap (𝓞 D.host.E) D.host.E (c * c') by rw [map_mul]; ring,
        repOf_spec, mul_smul, sub_self])
    rw [RingHom.id_apply, Algebra.smul_def]
    exact sub_eq_zero.1 this

theorem formQ_surj (hP : Formalism.BasicNotions.FactPrincipalDatum) (D : D7) (S : HSpace D.host.E) (hI : FormInt D S)
    (f : lat D S →ₗ[ℤ] ℤ) : ∃ x : lat D S, intForm (formQ D S) hI x = f := by
  have := lat_isLocalized D S
  have hξ := cmHost_imaginaryGenerator_ne_zero hP D
  have hAA := AA_ne_zero hP D
  let lam : S.V →ₗ[𝓞 D.host.E] D.host.E :=
    IsLocalizedModule.lift (nonZeroDivisors (𝓞 D.host.E)) (lat D S).subtype (repMap D S f) (fun s => isUnit_end s)
  let lamE : S.V →ₗ[D.host.E] D.host.E :=
    D.host.xi0⁻¹ • lam.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 D.host.E)) D.host.E
  obtain ⟨x, hx⟩ := riesz S lamE
  have hxy : ∀ y : lat D S, D.host.xi0 * S.hT x y = repOf D S f y := by
    intro y
    rw [hx]
    simp only [lamE, LinearMap.smul_apply, LinearMap.extendScalarsOfIsLocalization_apply', smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hξ, one_mul]
    exact IsLocalizedModule.lift_apply _ _ _ _ y
  have h3 : ∀ y (hy : y ∈ lat D S), S.hT x y ∈ D.host.AA * D.host.AAbar := by
    intro y hy
    have hz : repOf D S f ⟨y, hy⟩ ∈
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)]
      intro a ha
      rw [mem_one_iff] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [Algebra.traceForm_apply, repOf_spec]
      exact ⟨_, eq_intCast (algebraMap ℤ ℚ) _⟩
    rw [← dual_eq hP D, ← hxy ⟨y, hy⟩] at hz
    have h4 := mul_mem_mul (mem_spanSingleton_self (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹) hz
    have e1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹ *
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar) =
        D.host.AA * D.host.AAbar := by
      rw [mul_assoc, ← mul_assoc, spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hξ, spanSingleton_one, one_mul]
    rw [e1, ← mul_assoc, inv_mul_cancel₀ hξ, one_mul] at h4
    exact h4
  have h5 : ∀ y0 ∈ S.L0, S.hT x y0 ∈ D.host.AAbar := by
    intro y0 hy0
    have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (S.hT x y0) * D.host.AA ≤
        D.host.AA * D.host.AAbar := by
      rw [spanSingleton_mul_le_iff]
      intro b hb
      have := h3 (b • y0) (Submodule.subset_span ⟨b, hb, y0, hy0, rfl⟩)
      rw [map_smul, smul_eq_mul] at this
      have e : S.hT x y0 * b = b * S.hT x y0 := mul_comm _ _
      rw [e]; exact this
    have hle2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (S.hT x y0) ≤ D.host.AAbar := by
      calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (S.hT x y0)
          = D.host.AA⁻¹ * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (S.hT x y0) * D.host.AA) := by
            rw [mul_comm _ D.host.AA, ← mul_assoc, inv_mul_cancel₀ hAA, one_mul]
        _ ≤ D.host.AA⁻¹ * (D.host.AA * D.host.AAbar) := CovariantClass.elim D.host.AA⁻¹ hle
        _ = D.host.AAbar := by rw [← mul_assoc, inv_mul_cancel₀ hAA, one_mul]
    exact hle2 (mem_spanSingleton_self _ _)
  have h6 : ∀ c ∈ D.host.AA⁻¹, c • x ∈ S.L0 := by
    intro c hc
    rw [← S.baseLattice_isUnimodular]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
    intro y0 hy0
    show S.hT y0 (c • x) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)
    have hs : star (S.hT x y0) = D.host.conj (S.hT x y0) := bridge_star_holds D.R D.host _
    rw [map_smul, smul_eq_mul, ← LinearMap.isSymm_def.1 S.herm x y0, starRingEnd_apply, hs]
    have hm := mul_mem_mul hc (conj_mem_AA D (h5 y0 hy0))
    rw [inv_mul_cancel₀ hAA, mem_one_iff] at hm
    exact Submodule.mem_one.2 hm
  have h7 : ∀ e ∈ D.host.AA * D.host.AA⁻¹, e • x ∈ lat D S := by
    intro e he
    refine FractionalIdeal.mul_induction_on (C := fun e => e • x ∈ lat D S) he (fun a ha c hc => ?_) (fun u w hu hw => ?_)
    · show (a * c) • x ∈ lat D S
      rw [mul_smul]; exact Submodule.subset_span ⟨a, ha, c • x, h6 c hc, rfl⟩
    · show (u + w) • x ∈ lat D S
      rw [add_smul]; exact add_mem hu hw
  have hxmem : x ∈ lat D S := by
    have := h7 1 (by rw [mul_inv_cancel₀ hAA]; exact one_mem_one _)
    rwa [one_smul] at this
  refine ⟨⟨x, hxmem⟩, LinearMap.ext fun y => Int.cast_injective (α := ℚ) ?_⟩
  refine (intForm_cast (formQ D S) hI ⟨x, hxmem⟩ y).trans ?_
  show Algebra.trace ℚ D.host.E (D.host.xi0 * S.hT x y) = _
  have := repOf_spec D S f y 1
  rw [map_one, mul_one, one_smul] at this
  rw [hxy y, this]

theorem formQ_inj (hP : Formalism.BasicNotions.FactPrincipalDatum) (D : D7) (S : HSpace D.host.E) (hI : FormInt D S) :
    Function.Injective (intForm (formQ D S) hI) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h0 : ∀ y : lat D S, S.hT x y = 0 := by
    intro y
    have hz : D.host.xi0 * S.hT x y = 0 := trace_sep D (fun c => by
      have h1 := LinearMap.congr_fun hx (c • y)
      have h2 := intForm_cast (formQ D S) hI x (c • y)
      rw [h1, LinearMap.zero_apply, Int.cast_zero] at h2
      simp only [formQ, LinearMap.mk₂_apply, Submodule.coe_smul] at h2
      rw [← algebraMap_smul D.host.E c (y : S.V), map_smul, smul_eq_mul] at h2
      rw [show D.host.xi0 * S.hT x y * algebraMap (𝓞 D.host.E) D.host.E c =
        D.host.xi0 * (algebraMap (𝓞 D.host.E) D.host.E c * S.hT x y) by ring]
      exact h2.symm)
    exact (mul_eq_zero.1 hz).resolve_left (cmHost_imaginaryGenerator_ne_zero hP D)
  have h1 : ∀ v, S.hT x v = 0 := by
    intro v
    obtain ⟨s, hs, hsv⟩ := exists_smul_mem_lat D S v
    have h2 := h0 ⟨_, hsv⟩
    change S.hT x (s • v) = 0 at h2
    rw [← algebraMap_smul D.host.E s v, map_smul, smul_eq_mul] at h2
    have hs0 : algebraMap (𝓞 D.host.E) D.host.E s ≠ 0 := by
      intro h0'
      exact nonZeroDivisors.ne_zero hs (IsFractionRing.injective _ D.host.E (h0'.trans (map_zero _).symm))
    exact (mul_eq_zero.1 h2).resolve_left hs0
  exact Subtype.ext (S.nondeg.1 x h1)

end Lattice

section Complex

open ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable

def coord (D : D7) (S : HSpace D.host.E) : ℝ ⊗[ℤ] lat D S →ₗ[ℝ] (cmTypeOfSqrt D → Fin S.rank → ℂ) :=
  theta S.frame (cmTypeOfSqrt D) (lat D S)

theorem coord_tmul (D : D7) (S : HSpace D.host.E) (x : ℝ) (v : lat D S) :
    coord D S (x ⊗ₜ v) = fun (τ : cmTypeOfSqrt D) i => (x : ℂ) * (τ : D.host.E →+* ℂ) (S.frame.repr v i) :=
  theta_tmul _ _ _ x v

theorem coord_bijective (D : D7) (S : HSpace D.host.E) : Function.Bijective (coord D S) :=
  theta_bijective _ _ (cm_type_mem_iff_conj_not_mem D) (lat_fin D S) (exists_smul_mem_lat D S)

attribute [irreducible] coord

def gramAt (D : D7) (S : HSpace D.host.E) (τ : D.host.E →+* ℂ) : Matrix (Fin S.rank) (Fin S.rank) ℂ :=
  S.gram.map τ

theorem herm_emb (D : D7) (S : HSpace D.host.E) (τ : D.host.E →+* ℂ) (v w : S.V) :
    τ (S.hT v w) = star (fun i => τ (S.frame.repr v i)) ⬝ᵥ
      (gramAt D S τ *ᵥ fun i => τ (S.frame.repr w i)) := by
  rw [sesq_repr S.hT S.frame v w]
  simp only [map_sum, map_mul, emb_star D, dotProduct, mulVec, gramAt, HSpace.gram, Matrix.map_apply,
    Pi.star_apply, Complex.star_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))

theorem formR_formula (D : D7) (S : HSpace D.host.E) (ε : ℤ) (hI : FormInt D S) (x y : ℝ ⊗[ℤ] lat D S) :
    (ε • intForm (formQ D S) hI).baseChange ℝ x y =
      ∑ τ : cmTypeOfSqrt D, 2 * (((ε : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0) *
        (star (coord D S x τ) ⬝ᵥ (gramAt D S τ *ᵥ coord D S y τ))).re := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x1 x2 h1 h2 =>
    rw [map_add, LinearMap.add_apply, h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    simp only [map_add, Pi.add_apply, star_add, add_dotProduct, mul_add, Complex.add_re]
    try ring
  | tmul a v =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y1 y2 h1 h2 =>
      rw [map_add, h1, h2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      simp only [map_add, Pi.add_apply, mulVec_add, dotProduct_add, mul_add, Complex.add_re]
      try ring
    | tmul a' w =>
      rw [LinearMap.BilinForm.baseChange_tmul, coord_tmul, coord_tmul]
      simp only [dot_smul_real, ← herm_emb]
      rw [LinearMap.smul_apply, LinearMap.smul_apply, zsmul_eq_mul, zsmul_eq_mul]
      have hq : ((intForm (formQ D S) hI v w : ℤ) : ℝ) =
          ∑ τ ∈ cmTypeOfSqrt D, 2 * (τ (D.host.xi0 * S.hT (v : S.V) w)).re := by
        rw [← trace_eq_sum_psi (cmTypeOfSqrt D) (cm_type_mem_iff_conj_not_mem D)]
        have h := congrArg (fun q : ℚ => (q : ℝ)) (intForm_cast (formQ D S) hI v w)
        simp only [Rat.cast_intCast] at h
        exact h
      push_cast
      rw [hq, ← Finset.sum_coe_sort (cmTypeOfSqrt D), Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [map_mul]
      have e : (ε : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0 * ((a : ℂ) * (a' : ℂ) *
          (τ : D.host.E →+* ℂ) (S.hT (v : S.V) w)) =
          (((ε : ℝ) * (a * a') : ℝ) : ℂ) * ((τ : D.host.E →+* ℂ) D.host.xi0 *
          (τ : D.host.E →+* ℂ) (S.hT (v : S.V) w)) := by
        push_cast; ring
      rw [e, Complex.re_ofReal_mul]
      ring

def mulAt (D : D7) (S : HSpace D.host.E) (a : 𝓞 D.host.E) :
    (cmTypeOfSqrt D → Fin S.rank → ℂ) →ₗ[ℝ] (cmTypeOfSqrt D → Fin S.rank → ℂ) :=
  blk (fun τ : cmTypeOfSqrt D => ((τ : D.host.E →+* ℂ) (a : D.host.E)) •
    (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ))

theorem coord_mulAt (D : D7) (S : HSpace D.host.E) (a : 𝓞 D.host.E) (A : ℝ ⊗[ℤ] lat D S →ₗ[ℝ] ℝ ⊗[ℤ] lat D S)
    (hA : ∀ x : lat D S, A ((1 : ℝ) ⊗ₜ x) = (1 : ℝ) ⊗ₜ (a • x)) (z : ℝ ⊗[ℤ] lat D S) :
    coord D S (A z) = mulAt D S a (coord D S z) := by
  have h1 : ∀ m : lat D S, coord D S ((1 : ℝ) ⊗ₜ (a • m)) = mulAt D S a (coord D S ((1 : ℝ) ⊗ₜ m)) := by
    intro m
    funext τ i
    rw [mulAt, blk_apply, coord_tmul, coord_tmul, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_one, one_mul, Submodule.coe_smul]
    rw [← algebraMap_smul D.host.E a (m : S.V), LinearEquiv.map_smul, Finsupp.smul_apply,
      smul_eq_mul, map_mul]
    try rfl
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z1 z2 h1' h2' => rw [map_add, map_add, h1', h2', map_add (coord D S), map_add (mulAt D S a)]
  | tmul x m =>
    have e : x ⊗ₜ[ℤ] m = x • ((1 : ℝ) ⊗ₜ[ℤ] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, LinearMap.map_smul, hA, LinearMap.map_smul, h1, LinearMap.map_smul, LinearMap.map_smul]

theorem mulAt_comm (D : D7) (S : HSpace D.host.E) (a : 𝓞 D.host.E)
    (K : cmTypeOfSqrt D → Matrix (Fin S.rank) (Fin S.rank) ℂ) :
    blk K ∘ₗ mulAt D S a = mulAt D S a ∘ₗ blk K := by
  rw [mulAt, blk_comp, blk_comp]
  congr 1
  funext τ
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem trace_mulAt (D : D7) (S : HSpace D.host.E) (a : 𝓞 D.host.E) :
    LinearMap.trace ℝ _ (mulAt D S a) =
      ∑ τ : cmTypeOfSqrt D, 2 * (((τ : D.host.E →+* ℂ) (a : D.host.E)) * (S.rank : ℂ)).re := by
  rw [mulAt, trace_blk]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]

theorem trace_comp_mulAt (D : D7) (S : HSpace D.host.E) (a : 𝓞 D.host.E)
    (K : cmTypeOfSqrt D → Matrix (Fin S.rank) (Fin S.rank) ℂ) :
    LinearMap.trace ℝ _ (blk K ∘ₗ mulAt D S a) =
      ∑ τ : cmTypeOfSqrt D, 2 * (((τ : D.host.E →+* ℂ) (a : D.host.E)) * (K τ).trace).re := by
  rw [mulAt, blk_comp, trace_blk]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]

def HasCplx (D : D7) (S : HSpace D.host.E) (p q : ℕ) (EF : LinearMap.BilinForm ℤ (lat D S)) : Prop :=
  ∃ J : ℝ ⊗[ℤ] lat D S →ₗ[ℝ] ℝ ⊗[ℤ] lat D S, (∀ x, J (J x) = -x) ∧
    (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
    ∀ (a : 𝓞 D.host.E) (A : ℝ ⊗[ℤ] lat D S →ₗ[ℝ] ℝ ⊗[ℤ] lat D S) (t : ℂ),
      (∀ x : lat D S, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) →
      t = ∑ τ ∈ Finset.univ.filter (fun τ : D.host.E →+* ℂ => τ (rtE D : D.host.E) = D.host.φ₀ D.host.sqrtMinusD),
        ((p : ℂ) * τ (a : D.host.E) + (q : ℂ) * starRingEnd ℂ (τ (a : D.host.E))) →
      J ∘ₗ A = A ∘ₗ J ∧ LinearMap.trace ℝ _ A = 2 * t.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im

set_option maxHeartbeats 1600000 in
theorem exists_hasCplx (D : D7) (S : HSpace D.host.E) (p q : ℕ) (hok : S.SigOK)
    (hpq : ∀ τ ∈ cmTypeOfSqrt D, S.sig τ = (p, q)) (hr : S.rank = p + q) (hI : FormInt D S) :
    ∃ ε : ℤ, ε = 1 ∧ HasCplx D S p q (ε • intForm (formQ D S) hI) := by
  classical
  set ε : ℤ := if 0 < (D.host.φ₀ D.host.sqrtMinusD).im then 1 else -1 with hεdef
  refine ⟨ε, if_pos (GlobalTheory.Member.Inhab.sqrt_im_pos D), ?_⟩
  have hc : ∀ τ : cmTypeOfSqrt D, 0 < ((ε : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0).im :=
    fun τ => xi0_embedding_im_pos D τ τ.2
  obtain ⟨θ, hθ⟩ : ∃ θ : (ℝ ⊗[ℤ] lat D S) ≃ₗ[ℝ] (cmTypeOfSqrt D → Fin S.rank → ℂ),
      ∀ x, θ x = coord D S x := ⟨LinearEquiv.ofBijective _ (coord_bijective D S), fun _ => rfl⟩
  have hsig : ∀ τ : cmTypeOfSqrt D, ∃ K : Matrix (Fin S.rank) (Fin S.rank) ℂ,
      (∀ u, K *ᵥ (K *ᵥ u) = -u) ∧
      (∀ u w, star (K *ᵥ u) ⬝ᵥ (gramAt D S τ *ᵥ (K *ᵥ w)) = star u ⬝ᵥ (gramAt D S τ *ᵥ w)) ∧
      (∀ u, u ≠ 0 → ∃ ρ : ℝ, 0 < ρ ∧ star (K *ᵥ u) ⬝ᵥ (gramAt D S τ *ᵥ u) = -(Complex.I * ρ)) ∧
      K.trace = Complex.I * ((p : ℂ) - q) := by
    intro τ
    have h1 := hok (τ : D.host.E →+* ℂ)
    rw [hpq τ τ.2] at h1
    obtain ⟨e, P, hP⟩ := h1
    exact exists_cplx_str _ _ _ e P hP
  choose K hK1 hK2 hK3 hK4 using hsig
  obtain ⟨J, hJdef⟩ : ∃ J : ℝ ⊗[ℤ] lat D S →ₗ[ℝ] ℝ ⊗[ℤ] lat D S,
      J = θ.symm.toLinearMap ∘ₗ blk K ∘ₗ θ.toLinearMap := ⟨_, rfl⟩
  have hJ : ∀ x, coord D S (J x) = blk K (coord D S x) := by
    intro x
    rw [← hθ, ← hθ, hJdef, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  ·
    intro x
    apply θ.injective
    rw [hθ, hθ, hJ, hJ, map_neg]
    funext τ
    simp only [blk_apply, hK1, Pi.neg_apply]
  ·
    intro x y
    rw [formR_formula, formR_formula]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [hJ, hJ, blk_apply, blk_apply, hK2]
  ·
    intro x hx
    rw [formR_formula]
    have hu : coord D S x ≠ 0 := by
      intro h0
      apply hx
      apply θ.injective
      rw [hθ, h0, map_zero]
    obtain ⟨τ0, hτ0⟩ := Function.ne_iff.1 hu
    have hterm : ∀ τ : cmTypeOfSqrt D, 0 ≤ 2 * (((ε : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0) *
          (star (coord D S (J x) τ) ⬝ᵥ (gramAt D S τ *ᵥ coord D S x τ))).re ∧
        (coord D S x τ ≠ 0 → 0 < 2 * (((ε : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0) *
          (star (coord D S (J x) τ) ⬝ᵥ (gramAt D S τ *ᵥ coord D S x τ))).re) := by
      intro τ
      rw [hJ, blk_apply]
      exact term_pos _ (hc τ) (K τ) (gramAt D S τ) (hK3 τ) (coord D S x τ)
    exact Finset.sum_pos' (fun τ _ => (hterm τ).1) ⟨τ0, Finset.mem_univ _, (hterm τ0).2 hτ0⟩
  ·
    intro a A t hA ht
    have hA' : ∀ z, θ (A z) = mulAt D S a (θ z) := fun z =>
      (hθ (A z)).trans ((coord_mulAt D S a A hA z).trans (congrArg (mulAt D S a) (hθ z).symm))
    have hJ' : ∀ z, θ (J z) = blk K (θ z) := fun z =>
      (hθ (J z)).trans ((hJ z).trans (congrArg (blk K) (hθ z).symm))
    have hconjA : θ.conj A = mulAt D S a := by
      apply LinearMap.ext
      intro u
      rw [LinearEquiv.conj_apply_apply, hA', LinearEquiv.apply_symm_apply]
    have hconjJA : θ.conj (J ∘ₗ A) = blk K ∘ₗ mulAt D S a := by
      apply LinearMap.ext
      intro u
      rw [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, hJ', hA', LinearEquiv.apply_symm_apply,
        LinearMap.comp_apply]
    have hcomm' : J ∘ₗ A = A ∘ₗ J := by
      apply LinearMap.ext
      intro z
      apply θ.injective
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hJ', hA', hA', hJ']
      exact LinearMap.congr_fun (mulAt_comm D S a K) (θ z)
    have htrA : LinearMap.trace ℝ _ A = LinearMap.trace ℝ _ (mulAt D S a) := by
      rw [← hconjA, LinearMap.trace_conj']
    have htrJA : LinearMap.trace ℝ _ (J ∘ₗ A) = LinearMap.trace ℝ _ (blk K ∘ₗ mulAt D S a) := by
      rw [← hconjJA, LinearMap.trace_conj']
    rw [sum_filter_eq_sum_cm_type D] at ht
    subst ht
    refine ⟨?_, ?_, ?_⟩
    · exact hcomm'
    · rw [htrA, trace_mulAt, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [hr]
      simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.conj_re,
        Complex.conj_im]
      push_cast
      ring
    · rw [htrJA, trace_comp_mulAt, Complex.im_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [hK4]
      simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
        Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im]
      ring

end Complex

theorem exists_tauEmb (D : D7) {τ : D.host.E →+* ℂ} (hτ : τ ∈ cmTypeOfSqrt D) : ∃ t : D.what₂.Tau, τ = DV.tauEmb D t := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 τ
  have h : D.host.emb g D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) :=
    ((mem_cm_type_iff D _).1 hτ).trans D.host.φ₀_mem
  refine ⟨D.eTau.symm ⟨g, ((factEmb D.R D.host).2 g).1 h⟩, ?_⟩
  simp [DV.tauEmb]

theorem bar_eq {D : D7} (A : Amb D) (a : 𝓞 D.host.E) : A.H.bar a = barE D a := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact A.H.bar_eq a

theorem smul_form_cast (D : D7) (S : HSpace D.host.E) (hI : FormInt D S) (ε : ℤ) (x y : lat D S) :
    (((ε • intForm (formQ D S) hI) x y : ℤ) : ℚ) =
      (ε : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 * S.hT (x : S.V) (y : S.V)) := by
  have h : ((intForm (formQ D S) hI x y : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (D.host.xi0 * S.hT (x : S.V) (y : S.V)) := intForm_cast (formQ D S) hI x y
  rw [← h, ← Int.cast_mul]
  simp only [LinearMap.smul_apply]
  congr 1

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem exists_datum (D : D7) (A : Amb D) (S : HSpace D.host.E) (p q : ℕ) (hok : S.SigOK)
    (hpq : ∀ τ ∈ cmTypeOfSqrt D, S.sig τ = (p, q)) (hr : S.rank = p + q) :
    ∃ Dw : Datum A.H, IsDatOf S Dw ∧ Dw.p = p ∧ Dw.q = q := by
  have hI := formInt D S
  obtain ⟨ε, hε, hd⟩ := exists_hasCplx D S p q hok hpq hr hI
  have hb : Function.Bijective (intForm (formQ D S) hI) :=
    ⟨formQ_inj Formalism.IndefR.Fin.factPrincipalDatum D S hI,
      fun f => formQ_surj Formalism.IndefR.Fin.factPrincipalDatum D S hI f⟩
  have hu : Function.Bijective (ε • intForm (formQ D S) hI) := by
    rw [hε, one_smul]; exact hb
  refine ⟨{ La := lat D S
            fin := lat_fin D S
            proj := lat_proj D S
            EF := ε • intForm (formQ D S) hI
            alt := fun x => ?_
            unimod := hu
            adj := fun a x y => ?_
            p := p
            q := q
            rank := ?_
            dom := ?_ }, ⟨(lat D S).subtype, Subtype.val_injective, Submodule.range_subtype _, fun x y => ?_⟩, rfl, rfl⟩
  · simp only [LinearMap.smul_apply]
    rw [Int.cast_injective (α := ℚ) ((intForm_cast _ hI x x).trans ((formQ_alt D S x).trans Int.cast_zero.symm)),
      smul_zero]
  · simp only [LinearMap.smul_apply]
    congr 1
    rw [bar_eq A a]
    exact Int.cast_injective (α := ℚ)
      ((intForm_cast _ hI _ _).trans ((formQ_adj D S a x y).trans (intForm_cast _ hI _ _).symm))
  · rw [lat_finrank, S.rank_eq, hr]
  · rw [A.rt_eq, A.cmHost_rootComplex_eq_pm_sqrt]
    exact hd
  · have h := smul_form_cast D S hI ε x y
    have h1 : (ε : ℚ) = 1 := by rw [hε, Int.cast_one]
    rw [h1, one_mul] at h
    exact h.trans (neg_trace_hD S _ _).symm

end GlobalTheory.ShFam.DatOf

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

theorem GlobalTheory.ShFam.exists_isDatOf : ∀ (D : D7) (A : Amb D) (w : Formalism.L2.Geo.Dat D (Lv A)),
    ∃ Dw : Datum A.H, IsDatOf w.S Dw ∧ Dw.p = w.j ∧ Dw.p + Dw.q = w.N := by
  intro D A w
  have hle : w.j ≤ w.N := w.j_le
  obtain ⟨Dw, h, hp, hq⟩ := DatOf.exists_datum D A w.S w.j (w.N - w.j) w.sigOK
    (fun τ hτ => by
      obtain ⟨t, rfl⟩ := DatOf.exists_tauEmb D hτ
      exact w.hsig t)
    (by show w.N = _; omega)
  exact ⟨Dw, h, hp, by omega⟩
