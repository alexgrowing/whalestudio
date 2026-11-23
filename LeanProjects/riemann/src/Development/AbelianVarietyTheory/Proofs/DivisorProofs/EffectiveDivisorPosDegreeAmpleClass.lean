import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntersectionEqLineBundleIntersectiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleClassCechPicardClassIffAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrHomEqAndIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberGlobalSectionEqSumCycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberZeroSmallImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultResCycIndicatorSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimClosureOfCoheightField
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.NefEffectiveCones.EventuallyEvalNegOfCoeffNeg
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.EffPos

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Cartier

theorem exists_coheight_eq_one_notMem {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {M : LB X}
    (hM : M.IsLB) (s : M.Sec) (hs : genericPoint X ∈ nonzeroLocus s) {x : X} (hx : x ∉ nonzeroLocus s) :
    ∃ w : X, Order.coheight w = 1 ∧ w ∉ nonzeroLocus s := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ M.U i := by
    have : x ∈ (⨆ i, M.U i : X.Opens) := by rw [hM.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  set g := X.presheaf.germ _ x hi (s.f i) with hgdef
  have hg0 : g ≠ 0 := GlobalTheory.MixHt.CycLoc.germ_ne_zero hs hi
  have hgu : ¬ IsUnit g := fun h =>
    hx ((Cartier.mem_nonzeroLocus_iff s i hi).2 ((Scheme.mem_basicOpen _ _ _ _).2 h))
  have hle : Ideal.span {g} ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (Ideal.span_singleton_le_iff_mem _).2 ((IsLocalRing.mem_maximalIdeal _).2 hgu)
  obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le hle
  have hPp : P.IsPrime := hP.1.1
  have h1 : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
  have hgP : g ∈ P := hP.1.2 (Ideal.subset_span rfl)
  have hP0 : (⊥ : Ideal (X.presheaf.stalk x)) < P := bot_lt_iff_ne_bot.2 fun h =>
    hg0 (by rw [h] at hgP; simpa using hgP)
  have e0 := Ideal.height_add_one_le_of_lt_of_isPrime hP0
  rw [Ideal.height_bot, zero_add] at e0
  refine ⟨X.fromSpecStalk x ⟨P, hPp⟩, ?_, ?_⟩
  · rw [GlobalTheory.MixHt.CycLoc.coheight_fromSpecStalk]
    exact le_antisymm h1 e0
  · rw [GlobalTheory.MixHt.CycLoc.mem_nonzeroLocus_iff_notMem s hi, not_not]
    exact hgP

end GlobalTheory.AV.EffPos

namespace GlobalTheory.AV.EffPos

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Cartier

theorem interNumRed_pos {K : Type} [Field K] (A : AbVar K) (n : ℕ) (hdim : A.dim = n + 1)
    (L : LB A.X.left) (hL : L.IsLB) (hLa : IsAmpleLB L) {w : A.X.left} (hw : Order.coheight w = 1) :
    letI := A.algΓ
    0 < interNumRed K (⟨closure {w}, isClosed_closure⟩ : Closeds A.X.left) (fun _ : Fin n => L) := by
  letI := A.algΓ
  obtain ⟨hint, hnoeth, -⟩ := isIntegral_isLocallyNoetherian_compactSpace K A
  obtain ⟨hstr, hproj⟩ := AbVarProj.strHom_eq_and_isProjOver K A
  have hp : IsProjOver (strHom K A.X.left) := hstr ▸ hproj
  have hX : topologicalKrullDim A.X.left = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_dim, hdim]
  have : LocallyOfFiniteType (strHom K A.X.left) := by
    obtain ⟨N, j, _, h⟩ := hp
    exact h ▸ inferInstance
  set C : Closeds A.X.left := ⟨closure {w}, isClosed_closure⟩ with hC
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  letI := algebraΓAlong K (redι C)
  rw [interNumRed_def, interNumSub_def,
    interNumOn_eq_interNum_pull (k := K) (f := redι C) (fun _ => rfl) (fun _ => hL)]
  have hd : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal C).subscheme = (n : WithBot ℕ∞) := by
    rw [topologicalKrullDim_red]
    exact VdmRec.CutSec.dim_closure_of_coheight_field (strHom K A.X.left) hX hw
  exact CompanionTheory.NefKleiman.interNum_top_pos_of_isAmpleLB K _ (PullVanish.isProjOver_red hp C) n hd _
    (hLa.pull_of_isClosedImmersion (redι C))

theorem inter_cons_pos : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), A.dim = n + 1 → ∀ (c : Pic A.X.left), IsAmpleCls c → ∀ (M : LB A.X.left) (hM : M.IsLB) (s : LB.Sec M), Out.nonzeroLocus s ≠ ⊥ → Out.nonzeroLocus s ≠ ⊤ → 0 < inter A (Fin.cons (cls M hM) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left) := by
  intro K _ A n hdim c hc M hM s hbot htop
  obtain ⟨L, hL, hrel, rfl⟩ := hc
  have hLa : IsAmpleLB L := (AmpleClsIff.isAmpleCls_cls_iff K A L hL).1 ⟨L, hL, hrel, rfl⟩
  letI := A.algΓ
  obtain ⟨hint, hnoeth, hcpt⟩ := isIntegral_isLocallyNoetherian_compactSpace K A
  obtain ⟨hstr, hproj⟩ := AbVarProj.strHom_eq_and_isProjOver K A
  have hp : IsProjOver (strHom K A.X.left) := hstr ▸ hproj
  have hX : topologicalKrullDim A.X.left = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_dim, hdim]
  have hcons : ∀ j, ((Fin.cons M (fun _ : Fin n => L) : Fin (n + 1) → LB A.X.left) j).IsLB :=
    fun j => Fin.cases hM (fun _ => hL) j
  have hfam : (Fin.cons (cls M hM) (fun _ : Fin n => cls L hL) : Fin (n + 1) → Pic A.X.left) =
      fun j => cls ((Fin.cons M (fun _ : Fin n => L) : Fin (n + 1) → LB A.X.left) j) (hcons j) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp
  rw [hfam, T.abelianVariety_intersection_eq_lineBundleIntersection K A (Fin (n + 1)) _ hcons]
  have hs : genericPoint A.X.left ∈ nonzeroLocus s := by
    obtain ⟨y, hy⟩ : (nonzeroLocus s : Set A.X.left).Nonempty := by
      by_contra h
      exact hbot (TopologicalSpace.Opens.ext (Set.not_nonempty_iff_eq_empty.1 h))
    exact ((genericPoint_spec A.X.left).mem_open_set_iff (nonzeroLocus s).isOpen).2 ⟨y, trivial, hy⟩
  rw [SecCycle.interNum_cons_eq_finsum_mult K A.X.left hp n hX.le M hM (fun _ => L) (fun _ => hL) s hs]
  obtain ⟨x, hx⟩ : ∃ x, x ∉ nonzeroLocus s := by
    by_contra h
    push_neg at h
    exact htop (eq_top_iff.2 fun x _ => h x)
  obtain ⟨w, hw1, hws⟩ := exists_coheight_eq_one_notMem hM s hs hx
  have hfs := (divOfSec hM s hs).finite_support_mult
  have hterm : ∀ v, 0 ≤ (divOfSec hM s hs).mult v *
      interNumRed K (⟨closure {v}, isClosed_closure⟩ : Closeds A.X.left) (fun _ : Fin n => L) := by
    intro v
    by_cases hv : (divOfSec hM s hs).mult v = 0
    · rw [hv, zero_mul]
    · exact mul_nonneg (mult_divOfSec_nonneg v)
        (interNumRed_pos A n hdim L hL hLa (CartierDiv.coheight_eq_one_of_mult_ne_zero hv)).le
  have hmw : (divOfSec hM s hs).mult w ≠ 0 := SecCycle.mult_divOfSec_ne_zero hM s hs hw1 hws
  have hw0 : 0 < (divOfSec hM s hs).mult w *
      interNumRed K (⟨closure {w}, isClosed_closure⟩ : Closeds A.X.left) (fun _ : Fin n => L) :=
    mul_pos (lt_of_le_of_ne (mult_divOfSec_nonneg w) (Ne.symm hmw)) (interNumRed_pos A n hdim L hL hLa hw1)
  rw [finsum_eq_sum_of_support_subset _ (s := hfs.toFinset) ?_]
  · exact Finset.sum_pos' (fun v _ => hterm v) ⟨w, by simpa using hmw, hw0⟩
  · intro v hv
    simpa using Function.support_mul_subset_left _ _ hv

end GlobalTheory.AV.EffPos
