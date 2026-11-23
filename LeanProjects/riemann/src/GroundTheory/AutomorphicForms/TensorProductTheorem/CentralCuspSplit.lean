import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.CentralCusp
import GroundTheory.AutomorphicForms.TensorProductTheorem.PeterssonComplement
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableCartan
import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspCentral

noncomputable section

namespace GroundTheory.Automorphic

namespace AutomorphicForm

open NumberField MeasureTheory Filter Topology CuspidalSpectrum Polynomial UnitaryAdmissible

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem exists_aeval_uActionCusp_laplacianU_eq_zero (φ : cuspForms K n) {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra)
    (ε : Fin d → ℝ) (B : LinearMap.BilinForm ℝ (isExpLieAlgebra K n).lieSubalgebra)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y : (isExpLieAlgebra K n).lieSubalgebra, B X Y = B Y X)
    (hinv : ∀ X Y Z : (isExpLieAlgebra K n).lieSubalgebra, B ⁅X, Y⁆ Z = -B Y ⁅X, Z⁆)
    (hK : ∀ i, ε i = -1 → ∀ t : ℝ,
      (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (b i)) ∈ archCompact K n) :
    ∃ P : ℂ[X], P.Monic ∧ 0 < P.natDegree ∧
      aeval (uActionCusp K n (laplacianU K n b)) P φ = 0 := by
  obtain ⟨P, hPm, hPd, hP⟩ := IsSmoothKZ.exists_aeval_laplacian_sliceL_eq_zero φ.2.1.isSmoothKZ b ε B
    hε horth hsymm hinv hK
  refine ⟨P, hPm, hPd, ?_⟩
  set incl : cuspForms K n →ₗ[ℂ] archSmooth K n :=
    Submodule.inclusion (cuspForms_le_automorphicForms.trans automorphicForms_le_archSmooth) with hincl
  have h1 := map_aeval_apply_of_intertwine incl (A := uActionCusp K n (laplacianU K n b))
    (B := AutomorphicForm.uAction (laplacianU K n b)) (fun m => rfl) P φ
  apply Subtype.ext
  funext g
  have h2 := map_aeval_apply_of_intertwine (sliceL g) (A := AutomorphicForm.uAction (laplacianU K n b))
    (B := (isExpLieAlgebra K n).laplacian (F := ℂ) b)
    (fun m => by rw [sliceL_uAction, rightUAction_laplacianU]) P (incl φ)
  rw [← h1] at h2
  have h3 := congrArg (fun f : (isExpLieAlgebra K n).smoothFuns (F := ℂ) => (f : archGroup K n → ℂ) 1)
    (h2.trans (hP g))
  simp only [archSlice_apply, coe_sliceL, mul_one, map_one] at h3
  exact h3

theorem exists_map_eq_mul_map_conj (P : ℂ[X]) :
    ∃ p : ℝ[X], p.map (algebraMap ℝ ℂ) = P * P.map (starRingEnd ℂ) := by
  have hmem : P * P.map (starRingEnd ℂ) ∈ Polynomial.lifts (algebraMap ℝ ℂ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    have hc : starRingEnd ℂ ((P * P.map (starRingEnd ℂ)).coeff k) = (P * P.map (starRingEnd ℂ)).coeff k := by
      rw [← Polynomial.coeff_map, Polynomial.map_mul, Polynomial.map_map,
        show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ from RingHom.ext Complex.conj_conj,
        Polynomial.map_id, mul_comm]
    exact ⟨((P * P.map (starRingEnd ℂ)).coeff k).re, Complex.conj_eq_iff_re.1 hc⟩
  exact Polynomial.mem_lifts _ |>.1 hmem

theorem ρ_centralZ_eq_zero {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n) :
    (gkModuleCusp K n).ρ (centralZ K n) φ = 0 := by
  apply Subtype.ext
  funext g
  have h := hasDerivAt_apply_mul_expG φ (centralZ K n) g 0
  have e : (fun t : ℝ => (φ : AdelicGLn.AdelicGL K n → ℂ)
      (g * infEmb K n ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (centralZ K n))))) =
      fun _ => (φ : AdelicGLn.AdelicGL K n → ℂ) g := by
    funext t
    rw [expG_centralZ, infEmb_zInf]
    exact apply_mul_centralSection_of_mem hφ g _
  rw [e] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
  simpa using h0

theorem finite_image_translates {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) {v : V}
    (hv : IsOpen (stabilizerOf ρ v : Set G)) {C : Set G} (hC : IsCompact C) :
    ((fun g => ρ g v) '' C).Finite := by
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun c : G => (fun x => c⁻¹ * x) ⁻¹' (stabilizerOf ρ v : Set G))
    (fun c => hv.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, show x⁻¹ * x ∈ (stabilizerOf ρ v : Set G) by
      rw [inv_mul_cancel]; exact one_mem _⟩)
  refine ((t.finite_toSet).image fun c => ρ c v).subset ?_
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨c, hc, hck⟩ := Set.mem_iUnion₂.1 (ht hk)
  refine ⟨c, hc, ?_⟩
  have h1 : ρ (c⁻¹ * k) v = v := hck
  change ρ c v = ρ k v
  conv_lhs => rw [← h1]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem exists_average {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : cuspForms K n →ₗ[ℂ] H)
    (hι : ∀ g, ∀ a ∈ centralCuspForms K n, ∀ b ∈ centralCuspForms K n,
      inner ℂ (ι (finRepCusp K n g a)) (ι (finRepCusp K n g b)) = inner ℂ (ι a) (ι b))
    (U : Submodule ℂ (cuspForms K n)) (hU : U ≤ centralCuspForms K n)
    (hUτ : ∀ g, ∀ φ ∈ U, finRepCusp K n g φ ∈ U) (U₀ : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n))
    (hU₀ : (U₀ : Set (AdelicGLn.FiniteAdelicGL K n)) ⊆ AdelicGLn.integralFiniteGL K n)
    {u : cuspForms K n} (hu : u ∈ U) :
    ∃ e ∈ U, (∀ h ∈ U₀, finRepCusp K n h e = e) ∧
      ∀ w ∈ centralCuspForms K n, (∀ h ∈ U₀, finRepCusp K n h w = w) →
        inner ℂ (ι u) (ι w) = inner ℂ (ι e) (ι w) := by
  classical
  set R := finRepCusp K n
  obtain ⟨U₁, -, hU₁⟩ := exists_openSubgroup_rightInvariant u.2.1.isSmooth u.2.1.isKFinite
  have hst : IsOpen (stabilizerOf R u : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    Subgroup.isOpen_mono (H₁ := (U₁ : Subgroup (AdelicGLn.FiniteAdelicGL K n)))
      (fun y hy => Subtype.ext (funext fun g => hU₁ g y hy)) U₁.isOpen
  have hC : IsCompact (U₀ : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset U₀.isClosed hU₀
  have hfin := finite_image_translates R hst hC
  set O : Finset (cuspForms K n) := hfin.toFinset with hO
  have hmemO : ∀ v, v ∈ O ↔ ∃ g ∈ (U₀ : Set (AdelicGLn.FiniteAdelicGL K n)), R g u = v := by
    intro v
    rw [hO, Set.Finite.mem_toFinset]
    rfl
  have hinj : ∀ h, Function.Injective (R h) := fun h a b hab => by
    have := congrArg (R h⁻¹) hab
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel, map_one] at this
  have hperm : ∀ h ∈ U₀, O.image (R h) = O := by
    intro h hh
    refine Finset.eq_of_subset_of_card_le (fun v hv => ?_) (Finset.card_image_of_injective _ (hinj h)).ge
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨g, hg, rfl⟩ := (hmemO w).1 hw
    refine (hmemO _).2 ⟨h * g, U₀.mul_mem hh hg, ?_⟩
    rw [map_mul, Module.End.mul_apply]
  have huO : u ∈ O := (hmemO u).2 ⟨1, U₀.one_mem, by rw [map_one, Module.End.one_apply]⟩
  have hN : (O.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem huO)
  have hOU : ∀ v ∈ O, v ∈ U := fun v hv => by
    obtain ⟨g, -, rfl⟩ := (hmemO v).1 hv
    exact hUτ g u hu
  refine ⟨(O.card : ℂ)⁻¹ • ∑ v ∈ O, v, U.smul_mem _ (U.sum_mem hOU), fun h hh => ?_, fun w hw hwf => ?_⟩
  · rw [map_smul, map_sum]
    congr 1
    conv_rhs => rw [← hperm h hh]
    rw [Finset.sum_image fun a _ b _ hab => hinj h hab]
  · rw [map_smul, map_sum, inner_smul_left, sum_inner, map_inv₀, Complex.conj_natCast]
    have hterm : ∀ v ∈ O, inner ℂ (ι v) (ι w) = inner ℂ (ι u) (ι w) := by
      intro v hv
      obtain ⟨g, hg, rfl⟩ := (hmemO v).1 hv
      calc inner ℂ (ι (R g u)) (ι w) = inner ℂ (ι (R g u)) (ι (R g w)) := by rw [hwf g hg]
        _ = inner ℂ (ι u) (ι w) := hι g u (hU hu) w hw
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

section Relative

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

def orthRel (ι : M →ₗ[ℂ] H) (Vc U : Submodule ℂ M) : Submodule ℂ M where
  carrier := {v | v ∈ Vc ∧ ∀ u ∈ U, inner ℂ (ι u) (ι v) = 0}
  zero_mem' := ⟨Vc.zero_mem, fun u _ => by rw [map_zero, inner_zero_right]⟩
  add_mem' {v w} hv hw := ⟨Vc.add_mem hv.1 hw.1, fun u hu => by
    rw [map_add, inner_add_right, hv.2 u hu, hw.2 u hu, add_zero]⟩
  smul_mem' c v hv := ⟨Vc.smul_mem c hv.1, fun u hu => by
    rw [map_smul, inner_smul_right, hv.2 u hu, mul_zero]⟩

theorem orthRel_le (ι : M →ₗ[ℂ] H) (Vc U : Submodule ℂ M) : orthRel ι Vc U ≤ Vc := fun _ hv => hv.1

theorem inf_orthRel_eq_bot {ι : M →ₗ[ℂ] H} {Vc U : Submodule ℂ M} (hU : U ≤ Vc)
    (hinj : ∀ a ∈ Vc, ι a = 0 → a = 0) : U ⊓ orthRel ι Vc U = ⊥ := by
  rw [eq_bot_iff]
  intro v ⟨hvU, hvO⟩
  have h := hvO.2 v hvU
  rw [inner_self_eq_zero] at h
  rw [hinj v (hU hvU) h]
  exact Submodule.zero_mem _

theorem sup_orthRel_eq {ι : M →ₗ[ℂ] H} {Vc U : Submodule ℂ M} (hU : U ≤ Vc)
    (h : ∀ v ∈ Vc, ∃ W : Submodule ℂ M, W ≤ Vc ∧ FiniteDimensional ℂ W ∧ v ∈ W ∧
      ∀ u ∈ U, ∃ u' ∈ U ⊓ W, ∀ w ∈ W, inner ℂ (ι u) (ι w) = inner ℂ (ι u') (ι w)) :
    U ⊔ orthRel ι Vc U = Vc := by
  refine le_antisymm (sup_le hU (orthRel_le ι Vc U)) fun v hv => ?_
  obtain ⟨W, hWV, hWf, hvW, hW⟩ := h v hv
  set N : Submodule ℂ H := (U ⊓ W).map ι with hN
  have : FiniteDimensional ℂ (U ⊓ W : Submodule ℂ M) :=
    Submodule.finiteDimensional_of_le (inf_le_right : U ⊓ W ≤ W)
  have : FiniteDimensional ℂ N := by rw [hN]; infer_instance
  have hp : N.starProjection (ι v) ∈ N := Submodule.starProjection_apply_mem N (ι v)
  obtain ⟨a, haUW, hax⟩ := Submodule.mem_map.1 hp
  have horth : ι v - N.starProjection (ι v) ∈ Nᗮ := Submodule.sub_starProjection_mem_orthogonal _
  refine Submodule.mem_sup.2 ⟨a, haUW.1, v - a, ⟨hWV (W.sub_mem hvW haUW.2), fun u hu => ?_⟩,
    add_sub_cancel _ _⟩
  obtain ⟨u', hu'UW, hu'⟩ := hW u hu
  rw [hu' (v - a) (W.sub_mem hvW haUW.2), map_sub, hax]
  exact Submodule.inner_right_of_mem_orthogonal (Submodule.mem_map_of_mem hu'UW) horth

theorem inner_aeval_map_rel {ι : M →ₗ[ℂ] H} {Vc : Submodule ℂ M} {T : Module.End ℂ M}
    (hTV : ∀ x ∈ Vc, T x ∈ Vc)
    (hT : ∀ x ∈ Vc, ∀ y ∈ Vc, inner ℂ (ι (T x)) (ι y) = inner ℂ (ι x) (ι (T y))) (p : ℝ[X]) :
    ∀ x ∈ Vc, ∀ y ∈ Vc, inner ℂ (ι (aeval T (p.map (algebraMap ℝ ℂ)) x)) (ι y) =
      inner ℂ (ι x) (ι (aeval T (p.map (algebraMap ℝ ℂ)) y)) := by
  induction p using Polynomial.induction_on with
  | C a =>
    intro x _ y _
    simp only [Polynomial.map_C, aeval_C, Module.algebraMap_end_apply, map_smul, inner_smul_left,
      inner_smul_right, Complex.coe_algebraMap, Complex.conj_ofReal]
  | add p q hp hq =>
    intro x hx y hy
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, inner_add_left, inner_add_right,
      hp x hx y hy, hq x hx y hy]
  | monomial k a ih =>
    intro x hx y hy
    have e : ((C a * X ^ (k + 1) : ℝ[X]).map (algebraMap ℝ ℂ)) =
        (C a * X ^ k : ℝ[X]).map (algebraMap ℝ ℂ) * X := by
      rw [pow_succ, ← mul_assoc, Polynomial.map_mul, Polynomial.map_X]
    rw [e, map_mul, aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih (T x) (hTV x hx) y hy,
      hT x hx _ (PeterssonComplement.aeval_mem hTV _ y hy), PeterssonComplement.apply_aeval_comm]

theorem exists_apply_eq_zero_inner_eq_rel {ι : M →ₗ[ℂ] H} {Vc : Submodule ℂ M}
    (hinj : ∀ a ∈ Vc, ι a = 0 → a = 0) {T : Module.End ℂ M} (hTV : ∀ x ∈ Vc, T x ∈ Vc)
    (hT : ∀ x ∈ Vc, ∀ y ∈ Vc, inner ℂ (ι (T x)) (ι y) = inner ℂ (ι x) (ι (T y))) (p : ℝ[X])
    (Z : Submodule ℂ M) (hZV : Z ≤ Vc) [FiniteDimensional ℂ Z] (hZ : ∀ z ∈ Z, T z ∈ Z) {x : M} (hx : x ∈ Z) :
    ∃ m ∈ Z, aeval T (p.map (algebraMap ℝ ℂ)) m = 0 ∧
      ∀ w ∈ Vc, aeval T (p.map (algebraMap ℝ ℂ)) w = 0 →
        inner ℂ (ι x) (ι w) = inner ℂ (ι m) (ι w) := by
  set S := aeval T (p.map (algebraMap ℝ ℂ)) with hS
  have hSym := inner_aeval_map_rel hTV hT p
  have hSZ : ∀ z ∈ Z, S z ∈ Z := PeterssonComplement.aeval_mem hZ _
  set S' : Z →ₗ[ℂ] Z := S.restrict hSZ with hS'
  have hdisj : Disjoint (LinearMap.ker S') (LinearMap.range S') := by
    rw [Submodule.disjoint_def]
    rintro y hyk ⟨z, rfl⟩
    have h1 : S (S z) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hyk)
    have hzV : (z : M) ∈ Vc := hZV z.2
    have hSzV : S z ∈ Vc := hZV (hSZ z z.2)
    have h2 : inner ℂ (ι (S z)) (ι (S z)) = 0 := by
      rw [hSym _ hzV _ hSzV, h1, map_zero, inner_zero_right]
    rw [inner_self_eq_zero] at h2
    exact Subtype.ext (hinj _ hSzV h2)
  have hcompl : IsCompl (LinearMap.ker S') (LinearMap.range S') :=
    (Submodule.isCompl_iff_disjoint _ _ (by
      rw [add_comm, LinearMap.finrank_range_add_finrank_ker])).2 hdisj
  obtain ⟨m, hm, r, ⟨z, rfl⟩, hmr⟩ :=
    Submodule.mem_sup.1 (hcompl.sup_eq_top ▸ Submodule.mem_top : (⟨x, hx⟩ : Z) ∈ _)
  refine ⟨m, m.2, congrArg Subtype.val (LinearMap.mem_ker.1 hm), fun w hw hwk => ?_⟩
  have hxe : x = (m : M) + S z := congrArg Subtype.val hmr.symm
  rw [hxe, map_add, inner_add_left, hSym _ (hZV z.2) _ hw, hwk, map_zero, inner_zero_right, add_zero]

theorem sup_orthRel_eq_of_symmetric {ι : M →ₗ[ℂ] H} {Vc U : Submodule ℂ M} (hU : U ≤ Vc)
    (hinj : ∀ a ∈ Vc, ι a = 0 → a = 0) {T : Module.End ℂ M} (hTV : ∀ x ∈ Vc, T x ∈ Vc)
    (hT : ∀ x ∈ Vc, ∀ y ∈ Vc, inner ℂ (ι (T x)) (ι y) = inner ℂ (ι x) (ι (T y)))
    (hUT : ∀ u ∈ U, T u ∈ U)
    (h : ∀ v ∈ Vc, ∃ V₀ : Submodule ℂ M, V₀ ≤ Vc ∧ v ∈ V₀ ∧ (∀ z ∈ V₀, T z ∈ V₀) ∧
      (∀ x ∈ V₀, ∃ p : ℝ[X], aeval T (p.map (algebraMap ℝ ℂ)) x = 0 ∧
        FiniteDimensional ℂ (V₀ ⊓ LinearMap.ker (aeval T (p.map (algebraMap ℝ ℂ))) : Submodule ℂ M)) ∧
      ∀ u ∈ U, ∃ e ∈ U ⊓ V₀, ∀ w ∈ V₀, inner ℂ (ι u) (ι w) = inner ℂ (ι e) (ι w)) :
    U ⊔ orthRel ι Vc U = Vc := by
  refine sup_orthRel_eq hU fun v hv => ?_
  obtain ⟨V₀, hV₀V, hvV₀, hV₀T, hfin, havg⟩ := h v hv
  obtain ⟨p, hpv, hpfin⟩ := hfin v hvV₀
  refine ⟨V₀ ⊓ LinearMap.ker (aeval T (p.map (algebraMap ℝ ℂ))), inf_le_left.trans hV₀V, hpfin,
    ⟨hvV₀, hpv⟩, fun u hu => ?_⟩
  obtain ⟨e, ⟨heU, heV₀⟩, he⟩ := havg u hu
  obtain ⟨q, hqe, hqfin⟩ := hfin e heV₀
  set Z : Submodule ℂ M := U ⊓ (V₀ ⊓ LinearMap.ker (aeval T (q.map (algebraMap ℝ ℂ)))) with hZ
  have : FiniteDimensional ℂ Z := Submodule.finiteDimensional_of_le (inf_le_right : Z ≤ _)
  have hZT : ∀ z ∈ Z, T z ∈ Z := by
    rintro z ⟨hzU, hzV₀, hzk⟩
    refine ⟨hUT z hzU, hV₀T z hzV₀, ?_⟩
    show T z ∈ LinearMap.ker _
    rw [LinearMap.mem_ker, ← PeterssonComplement.apply_aeval_comm,
      LinearMap.mem_ker.1 (hzk : z ∈ LinearMap.ker _), map_zero]
  obtain ⟨m, ⟨hmU, hmV₀, -⟩, hmk, hm⟩ := exists_apply_eq_zero_inner_eq_rel hinj hTV hT p Z
    (fun z hz => hV₀V hz.2.1) hZT (⟨heU, heV₀, hqe⟩ : e ∈ Z)
  exact ⟨m, ⟨hmU, hmV₀, hmk⟩, fun w ⟨hwV₀, hwk⟩ => (he w hwV₀).trans (hm w (hV₀V hwV₀) hwk)⟩

theorem map_mem_orthRel {ι : M →ₗ[ℂ] H} {Vc U : Submodule ℂ M} {A A' : M → M}
    (hAV : ∀ x ∈ Vc, A x ∈ Vc)
    (hA : ∀ x ∈ U, ∀ y ∈ Vc, inner ℂ (ι (A' x)) (ι y) = inner ℂ (ι x) (ι (A y)))
    (hU : ∀ u ∈ U, A' u ∈ U) {v : M} (hv : v ∈ orthRel ι Vc U) : A v ∈ orthRel ι Vc U :=
  ⟨hAV v hv.1, fun u hu => by
    rw [← hA u hu v hv.1]
    exact hv.2 _ (hU u hu)⟩

end Relative

theorem exists_isCompl_of_finite {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : cuspForms K n →ₗ[ℂ] H)
    (hinj : ∀ a ∈ centralCuspForms K n, ι a = 0 → a = 0)
    (hτ : ∀ g, ∀ a ∈ centralCuspForms K n, ∀ c ∈ centralCuspForms K n,
      inner ℂ (ι (finRepCusp K n g a)) (ι (finRepCusp K n g c)) = inner ℂ (ι a) (ι c))
    (hσ : ∀ k, ∀ a ∈ centralCuspForms K n, ∀ c ∈ centralCuspForms K n,
      inner ℂ (ι ((gkModuleCusp K n).σ k a)) (ι ((gkModuleCusp K n).σ k c)) = inner ℂ (ι a) (ι c))
    (hρ : ∀ X, ∀ a ∈ centralCuspForms K n, ∀ c ∈ centralCuspForms K n,
      inner ℂ (ι ((gkModuleCusp K n).ρ X a)) (ι c) + inner ℂ (ι a) (ι ((gkModuleCusp K n).ρ X c)) = 0)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra)
    (hΔ : ∀ φ : cuspForms K n, ∃ P : ℂ[X], P.Monic ∧ 0 < P.natDegree ∧
      aeval (uActionCusp K n (laplacianU K n b)) P φ = 0)
    (hHC : ∀ U₀ : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n),
      (U₀ : Set (AdelicGLn.FiniteAdelicGL K n)) ⊆ AdelicGLn.integralFiniteGL K n →
      ∀ P : ℂ[X], P.Monic → 0 < P.natDegree → ∀ S : Submodule ℂ (cuspForms K n),
        (∀ φ ∈ S, aeval (uActionCusp K n (laplacianU K n b)) P φ = 0 ∧
          (gkModuleCusp K n).ρ (centralZ K n) φ = 0 ∧ ∀ u ∈ U₀, finRepCusp K n u φ = φ) →
        FiniteDimensional ℂ S)
    (U : Submodule ℂ (cuspForms K n)) (hU : U ≤ centralCuspForms K n)
    (hUρ : ∀ X, ∀ φ ∈ U, (gkModuleCusp K n).ρ X φ ∈ U)
    (hUσ : ∀ k, ∀ φ ∈ U, (gkModuleCusp K n).σ k φ ∈ U)
    (hUτ : ∀ g, ∀ φ ∈ U, finRepCusp K n g φ ∈ U) :
    ∃ C : Submodule ℂ (cuspForms K n), C ≤ centralCuspForms K n ∧
      (∀ X, ∀ φ ∈ C, (gkModuleCusp K n).ρ X φ ∈ C) ∧ (∀ k, ∀ φ ∈ C, (gkModuleCusp K n).σ k φ ∈ C) ∧
      (∀ g, ∀ φ ∈ C, finRepCusp K n g φ ∈ C) ∧ U ⊓ C = ⊥ ∧ U ⊔ C = centralCuspForms K n := by
  classical
  let Δ := uActionCusp K n (laplacianU K n b)
  have hΔsum : ∀ φ : cuspForms K n, Δ φ = ∑ i, (gkModuleCusp K n).ρ (b i) ((gkModuleCusp K n).ρ (b i) φ) := by
    intro φ
    simp only [Δ, laplacianU, map_sum, map_mul, LinearMap.sum_apply, Module.End.mul_apply]
    rfl
  have hΔV : ∀ φ ∈ centralCuspForms K n, Δ φ ∈ centralCuspForms K n :=
    fun φ hφ => uActionCusp_mem_centralCuspForms _ hφ
  have hXX : ∀ X, ∀ a ∈ centralCuspForms K n, ∀ c ∈ centralCuspForms K n,
      inner ℂ (ι ((gkModuleCusp K n).ρ X ((gkModuleCusp K n).ρ X a))) (ι c) =
      inner ℂ (ι a) (ι ((gkModuleCusp K n).ρ X ((gkModuleCusp K n).ρ X c))) := by
    intro X a ha c hc
    have h1 := hρ X _ (ρ_mem_centralCuspForms X ha) c hc
    have h2 := hρ X a ha _ (ρ_mem_centralCuspForms X hc)
    linear_combination h1 - h2
  have hT : ∀ x ∈ centralCuspForms K n, ∀ y ∈ centralCuspForms K n,
      inner ℂ (ι (Δ x)) (ι y) = inner ℂ (ι x) (ι (Δ y)) := by
    intro x hx y hy
    rw [hΔsum, hΔsum, map_sum, map_sum, sum_inner, inner_sum]
    exact Finset.sum_congr rfl fun i _ => hXX (b i) x hx y hy
  have hUΔ : ∀ φ ∈ U, Δ φ ∈ U := fun φ hφ => by
    rw [hΔsum]
    exact U.sum_mem fun i _ => hUρ _ _ (hUρ _ _ hφ)
  have hsup := sup_orthRel_eq_of_symmetric (ι := ι) hU hinj hΔV hT hUΔ (fun v hv => by
    obtain ⟨U₀, hU₀sub, hU₀⟩ := exists_openSubgroup_rightInvariant v.2.1.isSmooth v.2.1.isKFinite
    let V₀ : Submodule ℂ (cuspForms K n) :=
      { carrier := {x | x ∈ centralCuspForms K n ∧ ∀ h ∈ U₀, finRepCusp K n h x = x}
        zero_mem' := ⟨Submodule.zero_mem _, fun h _ => map_zero _⟩
        add_mem' := fun {x y} hx hy => ⟨Submodule.add_mem _ hx.1 hy.1, fun h hh => by
          rw [map_add, hx.2 h hh, hy.2 h hh]⟩
        smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, fun h hh => by
          rw [map_smul, hx.2 h hh]⟩ }
    refine ⟨V₀, fun x hx => hx.1, ⟨hv, fun h hh => Subtype.ext (funext fun g => hU₀ g h hh)⟩,
      fun z hz => ⟨hΔV z hz.1, fun h hh => ?_⟩, fun x hx => ?_, fun u hu => ?_⟩
    · show finRepCusp K n h (uActionCusp K n (laplacianU K n b) z) = uActionCusp K n (laplacianU K n b) z
      rw [← uActionCusp_finRepCusp, hz.2 h hh]
    · obtain ⟨P, hPm, hPd, hP⟩ := hΔ x
      obtain ⟨p, hp⟩ := exists_map_eq_mul_map_conj P
      have hQm : (p.map (algebraMap ℝ ℂ)).Monic := hp ▸ hPm.mul (hPm.map _)
      have hQd : 0 < (p.map (algebraMap ℝ ℂ)).natDegree := by
        rw [hp, hPm.natDegree_mul (hPm.map _)]
        omega
      refine ⟨p, ?_, hHC U₀ hU₀sub _ hQm hQd _ fun φ hφ =>
        ⟨hφ.2, ρ_centralZ_eq_zero hφ.1.1, hφ.1.2⟩⟩
      show aeval Δ (p.map (algebraMap ℝ ℂ)) x = 0
      rw [hp, mul_comm, map_mul, Module.End.mul_apply, hP, map_zero]
    · obtain ⟨e, heU, hefix, he⟩ := exists_average ι hτ U hU hUτ U₀ hU₀sub hu
      exact ⟨e, ⟨heU, hU heU, hefix⟩, fun w hw => he w hw.1 hw.2⟩)
  refine ⟨orthRel ι (centralCuspForms K n) U, orthRel_le _ _ _, fun X φ hφ => ?_, fun k φ hφ => ?_,
    fun g φ hφ => ?_, inf_orthRel_eq_bot hU hinj, hsup⟩
  · refine map_mem_orthRel (A := (gkModuleCusp K n).ρ X) (A' := fun y => -(gkModuleCusp K n).ρ X y)
      (fun x hx => ρ_mem_centralCuspForms X hx) (fun x hx y hy => ?_) (fun u hu => U.neg_mem (hUρ X u hu)) hφ
    rw [map_neg, inner_neg_left, neg_eq_iff_add_eq_zero]
    exact hρ X x (hU hx) y hy
  · refine map_mem_orthRel (A := (gkModuleCusp K n).σ k) (A' := (gkModuleCusp K n).σ k⁻¹)
      (fun x hx => σ_mem_centralCuspForms k hx) (fun x hx y hy => ?_) (fun u hu => hUσ k⁻¹ u hu) hφ
    rw [← hσ k _ (σ_mem_centralCuspForms k⁻¹ (hU hx)) y hy, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  · refine map_mem_orthRel (A := finRepCusp K n g) (A' := finRepCusp K n g⁻¹)
      (fun x hx => finRepCusp_mem_centralCuspForms g hx) (fun x hx y hy => ?_) (fun u hu => hUτ g⁻¹ u hu) hφ
    rw [← hτ g _ (finRepCusp_mem_centralCuspForms g⁻¹ (hU hx)) y hy, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]

end AutomorphicForm

end GroundTheory.Automorphic
