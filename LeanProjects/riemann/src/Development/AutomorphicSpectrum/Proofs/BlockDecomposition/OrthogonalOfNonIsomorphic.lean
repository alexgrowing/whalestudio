import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleDiscreteSpaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqL2InnerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslateIsometryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointBisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentationUnitaryAverageStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantProjectionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDimCompactStableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenCompactSubgroupLeStatement

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDisc.Orth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def fixS (V : Submodule ℂ (Sm E N)) (L : Subgroup (GL (Fin N) (Af E))) : Submodule ℂ (Sm E N) where
  carrier := {x | x ∈ V ∧ ∀ u ∈ L, finRep E N u x = x}
  add_mem' := fun {x y} hx hy => ⟨V.add_mem hx.1 hy.1, fun u hu => by rw [map_add, hx.2 u hu, hy.2 u hu]⟩
  zero_mem' := ⟨V.zero_mem, fun u _ => map_zero _⟩
  smul_mem' := fun c x hx => ⟨V.smul_mem c hx.1, fun u hu => by rw [map_smul, hx.2 u hu]⟩

theorem mem_l2_of_discrete (μ : Measure (GA E N)) [μ.IsHaarMeasure] {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {x : Sm E N}
    (hx : x ∈ V) : x ∈ squareIntegrableSmoothSubmoduleGL μ := mem_l2Sub_of_isAutForm μ (hV.aut x hx) (hV.sqInt x hx)

theorem cont_of_mem {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {x : Sm E N} (hx : x ∈ V) : Continuous x.1 :=
  ContAut.continuous_of_isOpen_stab E N x (hV.aut x hx).level

theorem eq_zero_of_l2Map_eq_zero_of_isDiscrete (μ : Measure (GA E N)) [μ.IsHaarMeasure] {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {x : Sm E N}
    (hx : x ∈ V) (h0 : l2Map μ x = 0) : x = 0 := by
  by_contra hne
  have := re_l2Form_pos μ (mem_l2_of_discrete μ hV hx) (cont_of_mem hV hx) hne
  simp [l2Form, h0] at this

def stabS (x : Sm E N) : Subgroup (GL (Fin N) (Af E)) where
  carrier := {k | finRep E N k x = x}
  mul_mem' := fun {a b} ha hb => by
    change finRep E N (a * b) x = x
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by
    change finRep E N 1 x = x
    rw [map_one, Module.End.one_apply]
  inv_mem' := fun {a} ha => by
    change finRep E N a⁻¹ x = x
    have h : finRep E N a⁻¹ (finRep E N a x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [ha] at h

theorem exists_repr (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {V V' : Submodule ℂ (Sm E N)}
    (hV : IsDiscrete V) (hV' : IsDiscrete V') {x : Sm E N} (hx : x ∈ V) :
    ∃ y ∈ V', ∀ z ∈ V', ⟪l2Map μ z, l2Map μ x⟫_ℂ = ⟪l2Map μ z, l2Map μ y⟫_ℂ := by
  obtain ⟨L, hLS, hLo, hLc⟩ := GlobalTheory.T.exists_open_compact_subgroup_le E N (stabS x) (hV.aut x hx).level
  have hunit : ∀ (k : Kinf E N) {W W' : Submodule ℂ (Sm E N)}, IsDiscrete W → IsDiscrete W' → ∀ a ∈ W, ∀ b ∈ W',
      ⟪l2Map μ (cptRep E N k a), l2Map μ (cptRep E N k b)⟫_ℂ = ⟪l2Map μ a, l2Map μ b⟫_ℂ :=
    fun k _ _ h h' a ha b hb => (GlobalTheory.T.right_translate_isometry E N μ _ a b (mem_l2_of_discrete μ h ha) (mem_l2_of_discrete μ h' hb)).2
  letI : MeasurableSpace (Kinf E N) := borel _
  haveI : BorelSpace (Kinf E N) := ⟨rfl⟩
  haveI : CompactSpace (Kinf E N) := GlobalTheory.KinfCompactness.compactSpace_Kinf E N
  have key := GlobalTheory.T.representation_unitary_average (Measure.haar : Measure (Kinf E N)) (cptRep E N) (l2Map μ) (fixS V L) (fixS V' L)
    (fun g : GA E N => (LinearMap.proj g).comp (Sm E N).subtype)
    (fun k a ha b hb => hunit k hV' hV a ha.1 b hb.1)
    (fun k a ha b hb => hunit k hV' hV' a ha.1 b hb.1)
    (fun a ha => by
      obtain ⟨A, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_finite_dim_compact_stable E N V hV L a ha.1 ha.2
      exact ⟨A, h1, h2, fun b hb => h3 b hb, h4, h5⟩)
    (fun a ha => by
      obtain ⟨A, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_finite_dim_compact_stable E N V' hV' L a ha.1 ha.2
      exact ⟨A, h1, h2, fun b hb => h3 b hb, h4, h5⟩)
    (fun W hW => by
      haveI := GlobalTheory.CompanionTheory.AdmDiscFin.admissible_discrete_spaces E N L W hLo hW V' hV'
      refine Submodule.finiteDimensional_of_le (Submodule.span_mono (t := {φ | φ ∈ V' ∧ TypeB L W φ}) ?_)
      rintro a ⟨ha, hW'⟩
      exact ⟨ha.1, fun u hu g => congrFun (congrArg Subtype.val (ha.2 u hu)) g, hW'⟩)
  have hfx : ∀ u ∈ L, finRep E N u x = x := fun u hu => hLS hu
  obtain ⟨y, hy, hyz⟩ := key x ⟨hx, hfx⟩
  refine ⟨y, hy.1, fun z hz => ?_⟩
  obtain ⟨z', hz', hfix, e⟩ := GlobalTheory.T.exists_invariant_projection E N μ V' hV' L hLc z hz
  rw [e x (mem_l2_of_discrete μ hV hx) hfx, e y (mem_l2_of_discrete μ hV' hy.1) hy.2]
  exact hyz z' ⟨hz', hfix⟩

theorem exists_adj (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (o : Op E N) :
    ∃ o' : Op E N, ∀ {V W : Submodule ℂ (Sm E N)}, IsDiscrete V → IsDiscrete W → ∀ x ∈ V, ∀ y ∈ W,
      ⟪l2Map μ x, l2Map μ (act o y)⟫_ℂ = ⟪l2Map μ (act o' x), l2Map μ y⟫_ℂ := by
  cases o with
  | fin k =>
    refine ⟨.fin k⁻¹, fun {V W} hV hW x hx y hy => ?_⟩
    have h := (GlobalTheory.T.right_translate_isometry E N μ (finGL E N k) (act (.fin k⁻¹) x) y (mem_l2_of_discrete μ hV (hV.stable _ x hx)) (mem_l2_of_discrete μ hW hy)).2
    rw [← h]
    congr 2
    change x = finRep E N k (finRep E N k⁻¹ x)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  | cpt k =>
    refine ⟨.cpt k⁻¹, fun {V W} hV hW x hx y hy => ?_⟩
    have h := (GlobalTheory.T.right_translate_isometry E N μ (infGL E N (Unitary.toUnits k)) (act (.cpt k⁻¹) x) y (mem_l2_of_discrete μ hV (hV.stable _ x hx)) (mem_l2_of_discrete μ hW hy)).2
    rw [← h]
    congr 2
    change x = cptRep E N k (cptRep E N k⁻¹ x)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  | lie X =>
    refine ⟨.lie (-X), fun {V W} hV hW x hx y hy => ?_⟩
    have hxX := hV.stable (.lie X) x hx
    have hyX := hW.stable (.lie X) y hy
    have h := GlobalTheory.T.lie_skew_adjoint_l2' E N μ X x y (cont_of_mem hV hx) (cont_of_mem hW hy) (cont_of_mem hV hxX) (cont_of_mem hW hyX)
      (mem_l2_of_discrete μ hV hx) (mem_l2_of_discrete μ hW hy) (mem_l2_of_discrete μ hV hxX) (mem_l2_of_discrete μ hW hyX)
    have e : act (.lie (-X)) x = - lie E N X x := by
      change lie E N (-X) x = _
      rw [map_neg]; rfl
    rw [e, map_neg, inner_neg_left]
    exact h

theorem isoV_of_ne (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {V V' : Submodule ℂ (Sm E N)}
    (hV : IsDiscrete V) (hV' : IsDiscrete V') {x₀ y₀ : Sm E N} (hx₀ : x₀ ∈ V) (hy₀ : y₀ ∈ V')
    (hne : ⟪l2Map μ y₀, l2Map μ x₀⟫_ℂ ≠ 0) : IsoV V V' := by
  have uniq : ∀ a ∈ V', ∀ b ∈ V', (∀ z ∈ V', ⟪l2Map μ z, l2Map μ a⟫_ℂ = ⟪l2Map μ z, l2Map μ b⟫_ℂ) → a = b := by
    intro a ha b hb h
    have h1 := h (a - b) (V'.sub_mem ha hb)
    rw [← sub_eq_zero, ← inner_sub_right, ← map_sub, inner_self_eq_zero] at h1
    exact sub_eq_zero.1 (eq_zero_of_l2Map_eq_zero_of_isDiscrete μ hV' (V'.sub_mem ha hb) h1)
  choose T hTm hT using fun x : V => exists_repr μ hV hV' x.2
  let Tl : V →ₗ[ℂ] V' :=
    { toFun := fun x => ⟨T x, hTm x⟩
      map_add' := fun x y => Subtype.ext (uniq _ (hTm _) _ (V'.add_mem (hTm x) (hTm y)) fun z hz => by
        rw [← hT _ z hz]
        simp only [Submodule.coe_add, map_add, inner_add_right]
        rw [← hT x z hz, ← hT y z hz])
      map_smul' := fun c x => Subtype.ext (uniq _ (hTm _) _ (V'.smul_mem c (hTm x)) fun z hz => by
        rw [← hT _ z hz]
        simp only [Submodule.coe_smul, map_smul, inner_smul_right, RingHom.id_apply]
        rw [← hT x z hz]) }
  have hTl : ∀ x : V, (Tl x).1 = T x := fun _ => rfl
  have eqv : ∀ (o : Op E N) (x y : V), y.1 = act o x.1 → (Tl y).1 = act o (Tl x).1 := by
    intro o x y hxy
    obtain ⟨o', ho'⟩ := exists_adj μ o
    refine uniq _ (hTm y) _ (hV'.stable o _ (hTm x)) fun z hz => ?_
    rw [hTl, ← hT y z hz, hxy, ho' hV' hV z hz _ x.2, ho' hV' hV' z hz _ (hTm x),
      hT x _ (hV'.stable o' z hz)]
  have hnz : Tl ≠ 0 := by
    intro h0
    apply hne
    have h1 : T ⟨x₀, hx₀⟩ = 0 := congrArg Subtype.val (LinearMap.congr_fun h0 ⟨x₀, hx₀⟩)
    rw [hT ⟨x₀, hx₀⟩ y₀ hy₀, h1, map_zero, inner_zero_right]
  have hker : LinearMap.ker Tl = ⊥ := by
    have hst : IsStable ((LinearMap.ker Tl).map V.subtype) := by
      rintro o _ ⟨x, hx, rfl⟩
      refine ⟨⟨_, hV.stable o _ x.2⟩, ?_, rfl⟩
      refine Subtype.ext ?_
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hx
      rw [eqv o x _ rfl, hx]
      simp
    rcases hV.irred _ (Submodule.map_subtype_le _ _) hst with h | h
    · exact Submodule.map_injective_of_injective V.injective_subtype (by rwa [Submodule.map_bot])
    · exfalso
      refine hnz (LinearMap.ext fun x => ?_)
      have : x.1 ∈ (LinearMap.ker Tl).map V.subtype := by rw [h]; exact x.2
      obtain ⟨x', hx', e⟩ := this
      obtain rfl : x' = x := Subtype.ext e
      exact hx'
  have hran : LinearMap.range Tl = ⊤ := by
    have hst : IsStable ((LinearMap.range Tl).map V'.subtype) := by
      rintro o _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨Tl ⟨_, hV.stable o _ x.2⟩, ⟨_, rfl⟩, eqv o x _ rfl⟩
    rcases hV'.irred _ (Submodule.map_subtype_le _ _) hst with h | h
    · exfalso
      have h1 : LinearMap.range Tl = ⊥ :=
        Submodule.map_injective_of_injective V'.injective_subtype (by rwa [Submodule.map_bot])
      exact hnz (LinearMap.range_eq_bot.1 h1)
    · rw [eq_top_iff]
      intro y _
      have : y.1 ∈ (LinearMap.range Tl).map V'.subtype := by rw [h]; exact y.2
      obtain ⟨y', hy', e⟩ := this
      obtain rfl : y' = y := Subtype.ext e
      exact hy'
  refine ⟨LinearEquiv.ofBijective Tl ⟨LinearMap.ker_eq_bot.1 hker, LinearMap.range_eq_top.1 hran⟩, ?_⟩
  intro o x y hxy
  exact eqv o x y hxy

end GlobalTheory.CompanionTheory.FinDisc.Orth

open GlobalTheory.CompanionTheory.FinDisc.Orth in

theorem GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ →
  ∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → ¬ IsoV V V' →
    ∀ φ ∈ V, ∀ ψ ∈ V', ∫ x in F, φ.1 x * (starRingEnd ℂ) (ψ.1 x) ∂μ = 0 := by
  intro E _ _ _ N mG bG μ _ F hF V V' hV hV' hno φ hφ ψ hψ
  obtain rfl : mG = borel _ := bG.measurable_eq
  haveI := GlobalTheory.T.haar_right_invariant E N μ
  rw [GlobalTheory.T.integral_eq_l2_inner E N μ F hF φ ψ (mem_l2_of_discrete μ hV hφ) (mem_l2_of_discrete μ hV' hψ)]
  by_contra hne
  exact hno (isoV_of_ne μ hV hV' hφ hψ hne)

end
