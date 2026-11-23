import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.TrBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics
import Development.AutomorphicArithmetic.TwistedTraces.ExistsUniqueEigenlineOfRankOneOccurs
import Development.AutomorphicArithmetic.TwistedTraces.IntegralOpEigenlineScalarOfTwist

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.Gal.InertialTypesAlt.G.StableBaseChangeTwists

private theorem test_ind {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {J : Subgroup G} (hJ : CO J)
    {χ : G → ℂ} (hχ : IsChr J χ) : Test ((J : Set G).indicator fun x => conj (χ x)) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_,
    HasCompactSupport.intro hJ.1 fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ (J : Set G)
  · filter_upwards [hJ.2.mem_nhds hx, (IsLocallyConstant.iff_eventually_eq _).1 hχ.1 x] with y hy hy2
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, hy2]
  · have hcl : IsClosed (J : Set G) := Subgroup.isClosed_of_isOpen J hJ.2
    filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem cmp_surj {v : Pl F} (w : PlacesOver E v) (h : ∀ u : PlacesOver E v, u = w) :
    Function.Surjective (GM.cmp (n := n) w) := by
  have hev : Function.Bijective (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) := by
    letI : Unique (PlacesOver E v) := ⟨⟨w⟩, h⟩
    constructor
    · intro a b e
      funext u
      obtain rfl := h u
      exact e
    · intro z
      refine ⟨fun u => (h u).symm ▸ z, ?_⟩
      show ((h w).symm ▸ z : (w.1.adicCompletion E)) = z
      rfl
  let e := RingEquiv.ofBijective _ hev
  intro y
  refine ⟨mapGL n (e.symm : _ →+* _) y, ?_⟩
  exact Units.ext (Matrix.ext fun a b => e.apply_symm_apply _)

variable [IsGalois F E] {σ : E ≃ₐ[F] E} {q : Pl F} {w₀ : PlacesOver E q}

private theorem stabV (T : Ty σ n q w₀) (v : Pl F) (h : ∀ u : PlacesOver E v, u = T.mk' v)
    {a : Gw n (T.mk' v).1 →* Gw n (T.mk' v).1} (ha : IsLocGal σ (T.mk' v) a) (x : Gw n (T.mk' v).1) (hx : x ∈ T.J (T.mk' v).1) :
    a x ∈ T.J (T.mk' v).1 ∧ T.χ (T.mk' v).1 (a x) = T.χ (T.mk' v).1 x := by
  obtain ⟨g, rfl⟩ := cmp_surj (T.mk' v) h x
  letI : Unique (PlacesOver E v) := ⟨⟨T.mk' v⟩, h⟩
  have hall : ∀ u : PlacesOver E v, GM.cmp u g ∈ T.J u.1 := fun u => by
    obtain rfl := h u
    exact hx
  obtain ⟨h1, h2⟩ := T.stable v g hall
  rw [finprod_unique, finprod_unique] at h2
  have e : (default : PlacesOver E v) = T.mk' v := rfl
  rw [e] at h2
  rw [← ha]
  exact ⟨h1 _, h2⟩

end Loc

end UpperTheory.Gal.InertialTypesAlt.G.StableBaseChangeTwists

open UpperTheory.Gal.InertialTypesAlt.G.StableBaseChangeTwists in
theorem UpperTheory.Gal.InertialTypesAlt.G.baseTw :
    UpperTheory.Gal.InertialTypesAlt.G.BaseTw := by
  intro F E _ _ _ _ _ _ _ _ σ hgen hpr n hn μ _ V hV q w₀ T v hU hrk hne _ _ m hm τ s I hocc hs hI
  haveI := hm
  have hco := T.co (T.mk' v).1
  have hch := T.chr (T.mk' v).1
  have hT := test_ind hco hch
  refine ⟨hT, ?_⟩
  have h0 : m (T.J (T.mk' v).1) ≠ 0 := (hco.2.measure_pos m ⟨1, Subgroup.one_mem _⟩).ne'
  have ht : m (T.J (T.mk' v).1) ≠ ⊤ := hco.1.measure_lt_top.ne
  have hd0 : (m (T.J (T.mk' v).1))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ht
  have hdt : (m (T.J (T.mk' v).1))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  obtain ⟨mm, hmm⟩ : ∃ mm, mm = (m (T.J (T.mk' v).1))⁻¹ • m := ⟨_, rfl⟩
  haveI hmmH : mm.IsHaarMeasure := hmm ▸ Measure.IsHaarMeasure.smul _ hd0 hdt
  have hmm1 : mm (T.J (T.mk' v).1) = 1 := by
    rw [hmm, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 ht]
  have hback : (m (T.J (T.mk' v).1)) • mm = m := by
    rw [hmm, smul_smul, ENNReal.mul_inv_cancel h0 ht, one_smul]
  obtain ⟨e, he0, he1, he2⟩ := UpperTheory.exists_unique_eigenline_of_rankOne_occurs E n μ V hV (T.mk' v).1 τ hocc (T.J (T.mk' v).1) (T.χ (T.mk' v).1)
    hco hch hrk hne
  obtain ⟨-, -, h3⟩ := UpperTheory.ConvolutionTheory.C.occursBasics E n μ V (T.mk' v).1 mm hV
  obtain ⟨_, A, hA, -⟩ := h3 τ hocc _ hT
  obtain ⟨t, ht0, htt⟩ := UpperTheory.integralOp_eigenline_scalar_of_twist (Gw n (T.mk' v).1) mm τ I s (T.J (T.mk' v).1) (T.χ (T.mk' v).1) A e hco hch
    hmm1 hA he0 he1 he2 (stabV T v hU hs) hI
  have hsc := ((UpperTheory.Gal.InertialTypesAlt.G.trBasic _ mm τ I _).2.2 _ ht).2 t htt
  rw [hback] at hsc
  refine ⟨_, mul_ne_zero (Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨h0, ht⟩)) ht0, hsc⟩
