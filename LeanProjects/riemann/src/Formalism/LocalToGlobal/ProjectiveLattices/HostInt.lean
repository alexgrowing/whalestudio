import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

namespace Formalism.L2.Pj

open NumberField Formalism.BasicNotions FractionalIdeal
open scoped Pointwise

section HostInt

local instance instStarHermitianHost (D : D7) : StarRing D.host.E := D.host.cmStar

theorem algebraMap_conj_smul (D : D7) (z : 𝓞 D.host.E) :
    algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • z) = D.host.conj (algebraMap (𝓞 D.host.E) D.host.E z) := rfl

theorem bB_ne (D : D7) :
    ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 ∧
    ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
  have hne : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) ≠ ⊥ := differentIdeal_ne_bot
  have hspec : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) = D.host.𝔟 * (D.host.conj • D.host.𝔟) := D.host.𝔟_spec.1
  rw [hspec] at hne
  refine ⟨?_, ?_⟩
  · rw [Ne, coeIdeal_eq_zero]; rintro h; exact hne (by rw [h]; simp)
  · rw [Ne, coeIdeal_eq_zero]; rintro h; exact hne (by rw [h]; simp)

theorem conj_mem_AAbar (D : D7) {a : D.host.E} (ha : a ∈ D.host.AA) : D.host.conj a ∈ D.host.AAbar := by
  obtain ⟨hB, hB'⟩ := bB_ne D
  unfold Host.AA Host.AA0 at ha
  unfold Host.AAbar
  rw [← div_eq_mul_inv] at ha ⊢
  rw [mem_div_iff_of_ne_zero hB] at ha
  rw [mem_div_iff_of_ne_zero hB']
  intro y hy
  obtain ⟨z, hz, rfl⟩ := (mem_coeIdeal _).1 hy
  have hz0 : D.host.conj⁻¹ • z ∈ D.host.𝔟 := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hz
  obtain ⟨w, hw, hw'⟩ := (mem_coeIdeal _).1 (ha _ ((mem_coeIdeal _).2 ⟨_, hz0, rfl⟩))
  refine (mem_coeIdeal _).2 ⟨D.host.conj • w, Ideal.smul_mem_pointwise_smul _ _ _ hw, ?_⟩
  rw [algebraMap_conj_smul, hw', map_mul, ← algebraMap_conj_smul, smul_inv_smul]

theorem hT_int (D : D7) (j : ℕ) {x y : (D.sp.W j).V} (hx : x ∈ (D.sp.W j).L0) (hy : y ∈ (D.sp.W j).L0) :
    (D.sp.W j).hT x y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  have hy' : y ∈ Formalism.HermitianLatticesTheory.dual (D.sp.W j).hT (D.sp.W j).L0 := by
    rw [(D.sp.W j).baseLattice_isUnimodular]; exact hy
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hy'
  exact hy' x hx

abbrev NAA (D : D7) : Submodule (𝓞 D.host.E) D.host.E :=
  ((D.host.AA * D.host.AAbar : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    Submodule (𝓞 D.host.E) D.host.E)

theorem hT_gen_mem (D : D7) (j : ℕ) {a b : D.host.E} (ha : a ∈ D.host.AA) (hb : b ∈ D.host.AA)
    {x y : (D.sp.W j).V} (hx : x ∈ (D.sp.W j).L0) (hy : y ∈ (D.sp.W j).L0) :
    (D.sp.W j).hT (a • x) (b • y) ∈ NAA D := by
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hT_int D j hx hy)
  have e : (D.sp.W j).hT (a • x) (b • y) = r • (b * D.host.conj a) := by
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    have hs : (starRingEnd D.host.E) a = D.host.conj a := bridge_star_holds D.R D.host a
    rw [Algebra.smul_def, hr, hs]; ring
  rw [e]
  exact Submodule.smul_mem _ r (mul_mem_mul hb (conj_mem_AAbar D ha))

theorem hT_lat_mem (D : D7) (j : ℕ) {v w : (D.sp.W j).V} (hv : v ∈ latW D j) (hw : w ∈ latW D j) :
    (D.sp.W j).hT v w ∈ NAA D := by
  induction hv using Submodule.span_induction generalizing w with
  | mem v hv =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hv
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨b, hb, y, hy, rfl⟩ := hw
      exact hT_gen_mem D j ha hb hx hy
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

theorem trace_int_of_mem (hP : Formalism.BasicNotions.FactPrincipalDatum) (D : D7) {z : D.host.E} (hz : z ∈ NAA D) :
    ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * z) = n := by
  have h1 := hP D.R D.host
  have hJ : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar =
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [eq_inv_of_mul_eq_one_left h1, Host.ddE, coeIdeal_differentIdeal ℤ ℚ D.host.E (𝓞 D.host.E), inv_inv]
  have hm : D.host.xi0 * z ∈ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar := by
    rw [mul_assoc]
    exact mul_mem_mul (mem_spanSingleton_self _ _) hz
  rw [hJ, mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)] at hm
  obtain ⟨n, hn⟩ := hm 1 (one_mem_one _)
  refine ⟨n, ?_⟩
  rw [Algebra.traceForm_apply, mul_one] at hn
  rw [← hn]; simp

theorem datInt_of (hP : Formalism.BasicNotions.FactPrincipalDatum) (D : D7) (j : ℕ) : DatInt D j := by
  intro x y
  exact trace_int_of_mem hP D (hT_lat_mem D j x.2 y.2)

end HostInt

section Unimod

local instance instStarUnitaryHost (D : D7) : StarRing D.host.E := D.host.cmStar

theorem algebraMap_gal_smul (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (z : 𝓞 D.host.E) :
    algebraMap (𝓞 D.host.E) D.host.E (σ • z) = σ (algebraMap (𝓞 D.host.E) D.host.E z) := rfl

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  rw [← bridge_star_holds D.R D.host x, ← bridge_star_holds D.R D.host (star x)]
  exact star_star x

theorem conj_inv_apply (D : D7) (x : D.host.E) : (D.host.conj⁻¹ : D.host.E ≃ₐ[ℚ] D.host.E) x = D.host.conj x := by
  rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, conj_conj]

theorem conj_mem_AA (D : D7) {a : D.host.E} (ha : a ∈ D.host.AAbar) : D.host.conj a ∈ D.host.AA := by
  obtain ⟨hB, hB'⟩ := bB_ne D
  unfold Host.AA Host.AA0
  unfold Host.AAbar at ha
  rw [← div_eq_mul_inv] at ha ⊢
  rw [mem_div_iff_of_ne_zero hB'] at ha
  rw [mem_div_iff_of_ne_zero hB]
  intro y hy
  obtain ⟨z, hz, rfl⟩ := (mem_coeIdeal _).1 hy
  have hz1 : D.host.conj • z ∈ D.host.conj • D.host.𝔟 := Ideal.smul_mem_pointwise_smul _ _ _ hz
  obtain ⟨w, hw, hw'⟩ := (mem_coeIdeal _).1 (ha _ ((mem_coeIdeal _).2 ⟨_, hz1, rfl⟩))
  have hw0 : D.host.conj⁻¹ • w ∈ D.host.ccE := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hw
  refine (mem_coeIdeal _).2 ⟨D.host.conj⁻¹ • w, hw0, ?_⟩
  rw [algebraMap_gal_smul, conj_inv_apply, hw', algebraMap_gal_smul, map_mul, conj_conj]

theorem AA_ne_zero (hP : Formalism.BasicNotions.FactPrincipalDatum) (D : D7) : D.host.AA ≠ 0 := by
  intro h
  have h1 := hP D.R D.host
  rw [h, mul_zero, zero_mul, zero_mul] at h1
  exact zero_ne_one h1

theorem cmHost_imaginaryGenerator_ne_zero (hP : Formalism.BasicNotions.FactPrincipalDatum) (D : D7) : D.host.xi0 ≠ 0 := by
  intro h
  have h1 := hP D.R D.host
  rw [h, spanSingleton_zero, zero_mul, zero_mul, zero_mul] at h1
  exact zero_ne_one h1

theorem dual_eq (hP : Formalism.BasicNotions.FactPrincipalDatum) (D : D7) :
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar =
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  rw [eq_inv_of_mul_eq_one_left (hP D.R D.host), Host.ddE, coeIdeal_differentIdeal ℤ ℚ D.host.E (𝓞 D.host.E), inv_inv]

theorem exists_smul_mem_base_lattice (D : D7) (j : ℕ) (v : (D.sp.W j).V) :
    ∃ t ∈ nonZeroDivisors (𝓞 D.host.E), t • v ∈ (D.sp.W j).L0 := by
  have hv : v ∈ Submodule.span D.host.E ((D.sp.W j).L0 : Set (D.sp.W j).V) := by
    rw [(D.sp.W j).standardTuple_isLattice.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_mem _, by rw [one_smul]; exact hv⟩
  | zero => exact ⟨1, one_mem _, by rw [smul_zero]; exact zero_mem _⟩
  | add v w _ _ hv hw =>
    obtain ⟨s, hs, hsv⟩ := hv
    obtain ⟨t, ht, htw⟩ := hw
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    rw [smul_add, mul_comm s t, mul_smul, mul_comm t s, mul_smul]
    exact add_mem ((D.sp.W j).L0.smul_mem t hsv) ((D.sp.W j).L0.smul_mem s htw)
  | smul e v _ hv =>
    obtain ⟨s, hs, hsv⟩ := hv
    obtain ⟨⟨c, t⟩, hct⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 D.host.E)) e
    refine ⟨(t : 𝓞 D.host.E) * s, mul_mem t.2 hs, ?_⟩
    have : ((t : 𝓞 D.host.E) * s) • (e • v) = c • (s • v) := by
      rw [← algebraMap_smul D.host.E ((t : 𝓞 D.host.E) * s), ← algebraMap_smul D.host.E c, smul_smul,
        ← algebraMap_smul D.host.E s, smul_smul, map_mul, ← hct]
      congr 1; ring
    rw [this]
    exact (D.sp.W j).L0.smul_mem c hsv

theorem trace_sep (D : D7) {w : D.host.E}
    (h : ∀ c : 𝓞 D.host.E, Algebra.trace ℚ D.host.E (w * algebraMap (𝓞 D.host.E) D.host.E c) = 0) : w = 0 := by
  apply (traceForm_nondegenerate ℚ D.host.E).1 w
  intro e
  obtain ⟨n, hn, hint⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset D.host.E)
  have h1 := h ⟨n • e, hint e (Finset.mem_singleton_self e)⟩
  have h2 : Algebra.trace ℚ D.host.E (w * (n • e)) = 0 := h1
  rw [mul_smul_comm, map_zsmul, smul_eq_zero] at h2
  rw [Algebra.traceForm_apply]
  exact h2.resolve_left hn

theorem trace_rep (D : D7) (g : 𝓞 D.host.E →ₗ[ℤ] ℤ) : ∃ z : D.host.E, ∀ c : 𝓞 D.host.E,
    Algebra.trace ℚ D.host.E (z * algebraMap (𝓞 D.host.E) D.host.E c) = g c := by
  have hB := traceForm_nondegenerate ℚ D.host.E
  let db := (Algebra.traceForm ℚ D.host.E).dualBasis hB (integralBasis D.host.E)
  refine ⟨∑ i, ((g (RingOfIntegers.basis D.host.E i) : ℤ) : ℚ) • db i, ?_⟩
  have key : ∀ i k, Algebra.trace ℚ D.host.E (db i * integralBasis D.host.E k) = if k = i then 1 else 0 := by
    intro i k
    rw [← Algebra.traceForm_apply]
    exact (Algebra.traceForm ℚ D.host.E).apply_dualBasis_left hB _ i k
  have hj : ∀ k, Algebra.trace ℚ D.host.E ((∑ i, ((g (RingOfIntegers.basis D.host.E i) : ℤ) : ℚ) • db i) *
      algebraMap (𝓞 D.host.E) D.host.E (RingOfIntegers.basis D.host.E k)) = g (RingOfIntegers.basis D.host.E k) := by
    intro k
    rw [← integralBasis_apply, Finset.sum_mul, map_sum]
    simp_rw [smul_mul_assoc, map_smul, key]
    simp
  intro c
  conv_lhs => rw [← (RingOfIntegers.basis D.host.E).sum_repr c]
  conv_rhs => rw [← (RingOfIntegers.basis D.host.E).sum_repr c]
  simp only [map_sum, map_zsmul, Finset.mul_sum, mul_smul_comm, hj, Int.cast_sum, smul_eq_mul, Int.cast_mul]
  simp only [zsmul_eq_mul]

theorem riesz {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (l : S.V →ₗ[E] E) :
    ∃ x, ∀ v, S.hT x v = l v := by
  let T : S.V →ₗ[E] (Fin S.rank → E) :=
    { toFun := fun x i => star (S.hT x (S.frame i))
      map_add' := by intro x y; ext i; simp [map_add, star_add]
      map_smul' := by
        intro e x; ext i
        simp [LinearMap.map_smulₛₗ, star_mul', starRingEnd_apply, star_star] }
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : ∀ i, S.hT x (S.frame i) = 0 := fun i => by
      have := congrFun hx i
      simpa [T] using this
    have h1 : S.hT x = 0 := S.frame.ext (fun i => by rw [h0 i]; rfl)
    exact S.nondeg.1 x (fun y => by rw [h1]; rfl)
  have hfr : Module.finrank E S.V = Module.finrank E (Fin S.rank → E) := by
    rw [S.rank_eq, Module.finrank_fin_fun]
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hT
    (fun i => star (l (S.frame i)))
  refine ⟨x, fun v => ?_⟩
  have h2 : S.hT x = l := S.frame.ext (fun i => by
    have := congrFun hx i
    simpa [T] using this)
  rw [h2]

end Unimod

section Main

local instance instStarModuleHost (D : D7) : StarRing D.host.E := D.host.cmStar

theorem isUnit_end {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module E W] [Module (𝓞 E) W]
    [IsScalarTower (𝓞 E) E W] (s : nonZeroDivisors (𝓞 E)) :
    IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) W) s) := by
  have hs : algebraMap (𝓞 E) E s ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero s.2 (IsFractionRing.injective _ E (h0.trans (map_zero _).symm))
  rw [Module.End.isUnit_iff]
  refine ⟨fun x y hxy => ?_, fun y => ⟨(algebraMap (𝓞 E) E s)⁻¹ • y, ?_⟩⟩
  · simp only [Module.algebraMap_end_apply] at hxy
    rw [← algebraMap_smul E (s : 𝓞 E) x, ← algebraMap_smul E (s : 𝓞 E) y] at hxy
    exact smul_right_injective W hs hxy
  · simp only [Module.algebraMap_end_apply]
    rw [← algebraMap_smul E (s : 𝓞 E), smul_smul, mul_inv_cancel₀ hs, one_smul]

theorem int_exists_smul_mem_latW (hP : Formalism.BasicNotions.FactPrincipalDatum) (D : D7) (j : ℕ) (v : (D.sp.W j).V) :
    ∃ s ∈ nonZeroDivisors (𝓞 D.host.E), s • v ∈ latW D j := by
  obtain ⟨α, hα, hαA⟩ := exists_ne_zero_mem_isInteger (AA_ne_zero hP D)
  obtain ⟨t, ht, htv⟩ := exists_smul_mem_base_lattice D j v
  refine ⟨α * t, mul_mem (mem_nonZeroDivisors_of_ne_zero hα) ht, ?_⟩
  rw [mul_smul, ← algebraMap_smul D.host.E α]
  exact Submodule.subset_span ⟨_, hαA, _, htv, rfl⟩

theorem isLoc (hP : Formalism.BasicNotions.FactPrincipalDatum) (D : D7) (j : ℕ) :
    IsLocalizedModule (nonZeroDivisors (𝓞 D.host.E)) (latW D j).subtype where
  map_units s := isUnit_end s
  surj v := by
    obtain ⟨s, hs, hsv⟩ := int_exists_smul_mem_latW hP D j v
    exact ⟨(⟨_, hsv⟩, ⟨s, hs⟩), rfl⟩
  exists_of_eq h := ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext h⟩

def zOf (D : D7) (j : ℕ) (f : latW D j →ₗ[ℤ] ℤ) (y : latW D j) : D.host.E :=
  (trace_rep D (f.comp ((LinearMap.toSpanSingleton (𝓞 D.host.E) (latW D j) y).restrictScalars ℤ))).choose

theorem zOf_spec (D : D7) (j : ℕ) (f : latW D j →ₗ[ℤ] ℤ) (y : latW D j) (c : 𝓞 D.host.E) :
    Algebra.trace ℚ D.host.E (zOf D j f y * algebraMap (𝓞 D.host.E) D.host.E c) = f (c • y) :=
  (trace_rep D _).choose_spec c

def phiOf (D : D7) (j : ℕ) (f : latW D j →ₗ[ℤ] ℤ) : latW D j →ₗ[𝓞 D.host.E] D.host.E where
  toFun := zOf D j f
  map_add' y y' := by
    have := trace_sep D (w := zOf D j f (y + y') - (zOf D j f y + zOf D j f y')) (fun c => by
      rw [sub_mul, add_mul, map_sub, map_add, zOf_spec, zOf_spec, zOf_spec, smul_add, map_add]
      push_cast; ring)
    exact sub_eq_zero.1 this
  map_smul' c' y := by
    have := trace_sep D (w := zOf D j f (c' • y) - algebraMap (𝓞 D.host.E) D.host.E c' * zOf D j f y) (fun c => by
      rw [sub_mul, map_sub, zOf_spec,
        show algebraMap (𝓞 D.host.E) D.host.E c' * zOf D j f y * algebraMap (𝓞 D.host.E) D.host.E c =
          zOf D j f y * algebraMap (𝓞 D.host.E) D.host.E (c * c') by rw [map_mul]; ring,
        zOf_spec, mul_smul, sub_self])
    rw [RingHom.id_apply, Algebra.smul_def]
    exact sub_eq_zero.1 this

theorem efQ_surj (hP : Formalism.BasicNotions.FactPrincipalDatum) (D : D7) (j : ℕ) (hI : DatInt D j)
    (f : latW D j →ₗ[ℤ] ℤ) : ∃ x : latW D j, intForm (efQ D j) hI x = f := by
  have := isLoc hP D j
  have hξ := cmHost_imaginaryGenerator_ne_zero hP D
  have hAA := AA_ne_zero hP D
  let lam : (D.sp.W j).V →ₗ[𝓞 D.host.E] D.host.E :=
    IsLocalizedModule.lift (nonZeroDivisors (𝓞 D.host.E)) (latW D j).subtype (phiOf D j f) (fun s => isUnit_end s)
  let lamE : (D.sp.W j).V →ₗ[D.host.E] D.host.E :=
    D.host.xi0⁻¹ • lam.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 D.host.E)) D.host.E
  obtain ⟨x, hx⟩ := riesz (D.sp.W j) lamE
  have hxy : ∀ y : latW D j, D.host.xi0 * (D.sp.W j).hT x y = zOf D j f y := by
    intro y
    rw [hx]
    simp only [lamE, LinearMap.smul_apply, LinearMap.extendScalarsOfIsLocalization_apply', smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hξ, one_mul]
    exact IsLocalizedModule.lift_apply _ _ _ _ y
  have h3 : ∀ y (hy : y ∈ latW D j), (D.sp.W j).hT x y ∈ D.host.AA * D.host.AAbar := by
    intro y hy
    have hz : zOf D j f ⟨y, hy⟩ ∈
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)]
      intro a ha
      rw [mem_one_iff] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [Algebra.traceForm_apply, zOf_spec]
      exact ⟨_, eq_intCast (algebraMap ℤ ℚ) _⟩
    rw [← dual_eq hP D, ← hxy ⟨y, hy⟩] at hz
    have h4 := mul_mem_mul (mem_spanSingleton_self (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹) hz
    have e1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹ *
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar) =
        D.host.AA * D.host.AAbar := by
      rw [mul_assoc, ← mul_assoc, spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hξ, spanSingleton_one, one_mul]
    rw [e1, ← mul_assoc, inv_mul_cancel₀ hξ, one_mul] at h4
    exact h4
  have h5 : ∀ y0 ∈ (D.sp.W j).L0, (D.sp.W j).hT x y0 ∈ D.host.AAbar := by
    intro y0 hy0
    have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((D.sp.W j).hT x y0) * D.host.AA ≤
        D.host.AA * D.host.AAbar := by
      rw [spanSingleton_mul_le_iff]
      intro b hb
      have := h3 (b • y0) (Submodule.subset_span ⟨b, hb, y0, hy0, rfl⟩)
      rw [map_smul, smul_eq_mul] at this
      have e : (D.sp.W j).hT x y0 * b = b * (D.sp.W j).hT x y0 := mul_comm _ _
      rw [e]; exact this
    have hle2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((D.sp.W j).hT x y0) ≤ D.host.AAbar := by
      calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((D.sp.W j).hT x y0)
          = D.host.AA⁻¹ * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((D.sp.W j).hT x y0) * D.host.AA) := by
            rw [mul_comm _ D.host.AA, ← mul_assoc, inv_mul_cancel₀ hAA, one_mul]
        _ ≤ D.host.AA⁻¹ * (D.host.AA * D.host.AAbar) := CovariantClass.elim D.host.AA⁻¹ hle
        _ = D.host.AAbar := by rw [← mul_assoc, inv_mul_cancel₀ hAA, one_mul]
    exact hle2 (mem_spanSingleton_self _ _)
  have h6 : ∀ c ∈ D.host.AA⁻¹, c • x ∈ (D.sp.W j).L0 := by
    intro c hc
    rw [← (D.sp.W j).baseLattice_isUnimodular]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
    intro y0 hy0
    show (D.sp.W j).hT y0 (c • x) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)
    have hs : star ((D.sp.W j).hT x y0) = D.host.conj ((D.sp.W j).hT x y0) := bridge_star_holds D.R D.host _
    rw [map_smul, smul_eq_mul, ← LinearMap.isSymm_def.1 (D.sp.W j).herm x y0, starRingEnd_apply, hs]
    have hm := mul_mem_mul hc (conj_mem_AA D (h5 y0 hy0))
    rw [inv_mul_cancel₀ hAA, mem_one_iff] at hm
    exact Submodule.mem_one.2 hm
  have h7 : ∀ e ∈ D.host.AA * D.host.AA⁻¹, e • x ∈ latW D j := by
    intro e he
    refine FractionalIdeal.mul_induction_on (C := fun e => e • x ∈ latW D j) he (fun a ha c hc => ?_) (fun u w hu hw => ?_)
    · show (a * c) • x ∈ latW D j
      rw [mul_smul]; exact Submodule.subset_span ⟨a, ha, c • x, h6 c hc, rfl⟩
    · show (u + w) • x ∈ latW D j
      rw [add_smul]; exact add_mem hu hw
  have hxmem : x ∈ latW D j := by
    have := h7 1 (by rw [mul_inv_cancel₀ hAA]; exact one_mem_one _)
    rwa [one_smul] at this
  refine ⟨⟨x, hxmem⟩, LinearMap.ext fun y => Int.cast_injective (α := ℚ) ?_⟩
  refine (intForm_cast (efQ D j) hI ⟨x, hxmem⟩ y).trans ?_
  show Algebra.trace ℚ D.host.E (D.host.xi0 * (D.sp.W j).hT x y) = _
  have := zOf_spec D j f y 1
  rw [map_one, mul_one, one_smul] at this
  rw [hxy y, this]

theorem efQ_inj (hP : Formalism.BasicNotions.FactPrincipalDatum) (D : D7) (j : ℕ) (hI : DatInt D j) :
    Function.Injective (intForm (efQ D j) hI) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h0 : ∀ y : latW D j, (D.sp.W j).hT x y = 0 := by
    intro y
    have hz : D.host.xi0 * (D.sp.W j).hT x y = 0 := trace_sep D (fun c => by
      have h1 := LinearMap.congr_fun hx (c • y)
      have h2 := intForm_cast (efQ D j) hI x (c • y)
      rw [h1, LinearMap.zero_apply, Int.cast_zero] at h2
      simp only [efQ, LinearMap.mk₂_apply, Submodule.coe_smul] at h2
      rw [← algebraMap_smul D.host.E c (y : (D.sp.W j).V), map_smul, smul_eq_mul] at h2
      rw [show D.host.xi0 * (D.sp.W j).hT x y * algebraMap (𝓞 D.host.E) D.host.E c =
        D.host.xi0 * (algebraMap (𝓞 D.host.E) D.host.E c * (D.sp.W j).hT x y) by ring]
      exact h2.symm)
    exact (mul_eq_zero.1 hz).resolve_left (cmHost_imaginaryGenerator_ne_zero hP D)
  have h1 : ∀ v, (D.sp.W j).hT x v = 0 := by
    intro v
    obtain ⟨s, hs, hsv⟩ := int_exists_smul_mem_latW hP D j v
    have h2 := h0 ⟨_, hsv⟩
    change (D.sp.W j).hT x (s • v) = 0 at h2
    rw [← algebraMap_smul D.host.E s v, map_smul, smul_eq_mul] at h2
    have hs0 : algebraMap (𝓞 D.host.E) D.host.E s ≠ 0 := by
      intro h0'
      exact nonZeroDivisors.ne_zero hs (IsFractionRing.injective _ D.host.E (h0'.trans (map_zero _).symm))
    exact (mul_eq_zero.1 h2).resolve_left hs0
  exact Subtype.ext ((D.sp.W j).nondeg.1 x h1)

theorem efW_unimod_of (hP : Formalism.BasicNotions.FactPrincipalDatum) (D : D7) (j : ℕ) (hI : DatInt D j) :
    Function.Bijective (efW D j hI) := by
  have hb : Function.Bijective (intForm (efQ D j) hI) := ⟨efQ_inj hP D j hI, fun f => efQ_surj hP D j hI f⟩
  unfold efW
  by_cases h : ∃ hI' : DatInt D j, DomFor D j (intForm (efQ D j) hI')
  · rw [sgnW, if_pos h, one_smul]; exact hb
  · rw [sgnW, if_neg h]
    have e : ⇑((-1 : ℤ) • intForm (efQ D j) hI) = Neg.neg ∘ ⇑(intForm (efQ D j) hI) := by
      funext y; simp
    rw [e]; exact neg_involutive.bijective.comp hb

end Main

end Formalism.L2.Pj
