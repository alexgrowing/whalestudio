import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerRegularLeviCommutativeNoncompactStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientMeasureFibrationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeHypothesisFormsAgreeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviMonotoneInParabolicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncationCoefficientsInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularCentralizerNoncompactStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTestVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingProjectionStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.LeviOrb

section Quot

variable {H : Type} [Group H] [MeasurableSpace H] {T : Subgroup H} {dt : Measure T} {dh : Measure H}

theorem hasQuotInt_const_mul {g : H → ℂ} (h : HasQuotInt T dt dh g 0) (c : ℂ) :
    HasQuotInt T dt dh (fun x => c * g x) 0 := by
  refine ⟨h.1.const_mul c, ?_⟩
  have e := h.2
  unfold quotInt GlobalTheory.AutomorphicL2Unitary.descend at e ⊢
  rw [integral_const_mul, e, mul_zero]

theorem hasQuotInt_sum {ι : Type} (s : Finset ι) {g : ι → H → ℂ} (h : ∀ i ∈ s, HasQuotInt T dt dh (g i) 0) :
    HasQuotInt T dt dh (fun x => ∑ i ∈ s, g i x) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · exact integrable_zero _ _ _
    · simp [quotInt, GlobalTheory.AutomorphicL2Unitary.descend]
  | insert i s hi ih =>
    have h1 := h i (Finset.mem_insert_self i s)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert hi]
    refine ⟨h1.1.add h2.1, ?_⟩
    have e : quotInt T dt dh (fun x => g i x + ∑ i ∈ s, g i x) =
        quotInt T dt dh (g i) + quotInt T dt dh (fun x => ∑ i ∈ s, g i x) := integral_add h1.1 h2.1
    rw [e, h1.2, h2.2, add_zero]

theorem quotInt_eq_zero_of_sub {F G : H → ℂ} (hF : Integrable (GlobalTheory.AutomorphicL2Unitary.descend T F) (quotMeas T dt dh))
    (hG : HasQuotInt T dt dh G 0) (hS : quotInt T dt dh (fun x => F x - G x) = 0) : quotInt T dt dh F = 0 := by
  have e : quotInt T dt dh (fun x => F x - G x) = quotInt T dt dh F - quotInt T dt dh G :=
    integral_sub hF hG.1
  rw [e, hG.2, sub_zero] at hS
  exact hS

end Quot

theorem mk_mem_cent_iff {A B H : Type} [Group A] [Group B] [Group H] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace H] (e : A × B ≃ₜ* H) (a a0 : A) (b b0 : B) :
    e (a, b) ∈ cent (e (a0, b0)) ↔ a ∈ cent a0 ∧ b ∈ cent b0 := by
  rw [mem_cent, mem_cent, mem_cent, ← map_mul, ← map_mul, e.injective.eq_iff, Prod.mk_mul_mk, Prod.mk_mul_mk,
    Prod.mk.injEq]

section Tensor
variable {D : D7} {V : HSp D}

theorem tensor_split (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ)
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (g : GAd D.sp.cm.sig V.gram) :
    tensor D.sp.cm.sig V.gram fa ff g = (∏ v : S, ff v (proj D.sp.cm.sig V.gram v g)) *
      ((∏ w, fa w (projArch D.sp.cm.sig V.gram w g)) *
        ∏ᶠ (v) (_ : v ∈ (S : Set (HeightOneSpectrum (𝓞 D.host.F)))ᶜ), ff v (proj D.sp.cm.sig V.gram v g)) := by
  have hfin := hff.finite_mulSupport (projFin D.sp.cm.sig V.gram g)
  simp only [projFinLoc_projFin] at hfin
  rw [tensor, ← finprod_mem_univ, ← Set.union_compl_self (S : Set (HeightOneSpectrum (𝓞 D.host.F))),
    finprod_mem_union' disjoint_compl_right (hfin.inter_of_right _) (hfin.inter_of_right _),
    finprod_mem_coe_finset, ← Finset.prod_coe_sort S]
  ring

end Tensor

variable {D : D7} {V : HSp D}

section Proj

variable (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (x : ∀ v : S, GLoc D.sp.cm.sig V.gram v)
  (bb : awayPts D.sp.cm.sig V.gram S) (g : GAd D.sp.cm.sig V.gram)

theorem proj_conj_at (v : S) :
    proj D.sp.cm.sig V.gram v ((embAt D.sp.cm.sig V.gram S x * bb)⁻¹ * g * (embAt D.sp.cm.sig V.gram S x * bb)) =
      (x v)⁻¹ * proj D.sp.cm.sig V.gram v g * x v := by
  rw [map_mul, map_mul, map_inv, map_mul, proj_embAt, mem_awayPts.1 bb.2 v v.2, mul_one]

theorem proj_conj_away {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ S) :
    proj D.sp.cm.sig V.gram v ((embAt D.sp.cm.sig V.gram S x * bb)⁻¹ * g * (embAt D.sp.cm.sig V.gram S x * bb)) =
      proj D.sp.cm.sig V.gram v ((bb : GAd D.sp.cm.sig V.gram)⁻¹ * g * bb) := by
  have h1 : proj D.sp.cm.sig V.gram v (embAt D.sp.cm.sig V.gram S x) = 1 :=
    (mem_atPts.1 (embAt_mem D.sp.cm.sig V.gram S x)).2 v hv
  rw [map_mul, map_mul, map_inv, map_mul, h1, one_mul, map_mul, map_mul, map_inv]

theorem projArch_conj (w : InfinitePlace D.host.F) :
    projArch D.sp.cm.sig V.gram w ((embAt D.sp.cm.sig V.gram S x * bb)⁻¹ * g * (embAt D.sp.cm.sig V.gram S x * bb)) =
      projArch D.sp.cm.sig V.gram w ((bb : GAd D.sp.cm.sig V.gram)⁻¹ * g * bb) := by
  have h1 : projArch D.sp.cm.sig V.gram w (embAt D.sp.cm.sig V.gram S x) = 1 :=
    mem_finPts_iff_forall.1 (mem_atPts.1 (embAt_mem D.sp.cm.sig V.gram S x)).1 w
  rw [map_mul, map_mul, map_inv, map_mul, h1, one_mul, map_mul, map_mul, map_inv]

theorem projAt_embAt_mul : projAt D.sp.cm.sig V.gram S (embAt D.sp.cm.sig V.gram S x * bb) = x :=
  funext fun v => by rw [projAt_apply, map_mul, proj_embAt, mem_awayPts.1 bb.2 v v.2, mul_one]

theorem conjFn_tensor_split (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ)
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) :
    conjFn g (tensor D.sp.cm.sig V.gram fa ff) (embAt D.sp.cm.sig V.gram S x * bb) =
      (∏ v : S, ff v ((x v)⁻¹ * proj D.sp.cm.sig V.gram v g * x v)) *
        ((∏ w, fa w (projArch D.sp.cm.sig V.gram w ((bb : GAd D.sp.cm.sig V.gram)⁻¹ * g * bb))) *
          ∏ᶠ (v) (_ : v ∈ (S : Set (HeightOneSpectrum (𝓞 D.host.F)))ᶜ),
            ff v (proj D.sp.cm.sig V.gram v ((bb : GAd D.sp.cm.sig V.gram)⁻¹ * g * bb))) := by
  rw [conjFn, tensor_split fa ff hff S]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => by rw [proj_conj_at]
  · congr 1
    · exact Finset.prod_congr rfl fun w _ => by rw [projArch_conj]
    · exact finprod_mem_congr rfl fun v hv => by rw [proj_conj_away S x bb g hv]

end Proj

theorem sum_erase_split {ι : Type} [DecidableEq ι] (s : Finset ι) {i0 : ι} (h0 : i0 ∈ s) (c d : ι → ℂ)
    (hd : d i0 = 1) (wv A B : ℂ) (hw : wv = ∑ Q ∈ s, c Q * d Q) :
    wv * (A * B) - c i0 * (A * B) = ∑ Q ∈ s.erase i0, (d Q * B) * (c Q * A) := by
  rw [hw, ← Finset.add_sum_erase _ _ h0, hd, mul_one, add_mul, add_sub_cancel_left, Finset.sum_mul]
  exact Finset.sum_congr rfl fun Q _ => by ring

theorem hasQuotInt_types (hTC : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V)
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ)
    (hF : IsTestFin T U μf ff) (hμ : ∀ v, (μf v).IsHaarMeasure)
    (hH : GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ) (Φ : WittFrame V) (P : Finset (SV (wittIndex V)))
    (hP : IsPar P) (γ : GF V) (hγ : IsRegSS γ.1.1) (hγP : rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) P)
    (Q : Finset (SV (wittIndex V))) (hQ : Q ∈ parF (aP P) ∅) (hQ0 : Q ≠ ∅) (C : GAd D.sp.cm.sig V.gram → ℂ) (hc : Continuous C)
    (hi : LeftInv (cent (rat V γ)) C)
    (hn : ∀ u ∈ Q, ∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), LeftInv (NA (IsoFlag.single hW)) C)
    (dg : Measure (∀ v : T.S, GLoc D.sp.cm.sig V.gram v)) [dg.IsHaarMeasure]
    (dt : Measure (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ)))) [dt.IsHaarMeasure] :
    HasQuotInt (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ))) dt dg (fun x => C (embAt D.sp.cm.sig V.gram T.S x) *
      ∏ v : T.S, ff v ((x v)⁻¹ * proj D.sp.cm.sig V.gram v (rat V γ) * x v)) 0 := by
  obtain ⟨hQpar, hQle, -⟩ := mem_parF.1 hQ
  obtain ⟨u, hu⟩ := Finset.nonempty_of_ne_empty hQ0
  have hu0 : u ≠ 0 := fun h => hQpar.1 (h ▸ hu)
  have hvec : vec u ∈ aP P := hQle (Submodule.subset_span ⟨u, hu, rfl⟩)
  exact GlobalTheory.T.regular_semisimple_test_vanishing hTC D V T U μf ff hF hμ hH Φ u γ hu0 hγ (GlobalTheory.T.levi_monotone_in_parabolic D V Φ (AF D.host.F) P hP u hvec hγP) C hc
    hi (hn u hu) dg dt

theorem quotInt_inner (hTC : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V)
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ)
    (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ)
    (hF : IsTestFin T U μf ff) (hμ : ∀ v, (μf v).IsHaarMeasure)
    (hH : GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ) (Φ : WittFrame V) (P : Finset (SV (wittIndex V)))
    (hP : IsPar P) (γ : GF V) (hγ : IsRegSS γ.1.1) (hγP : rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) P)
    (hle : cent (rat V γ) ≤ Φ.levi D.sp.cm (AF D.host.F) P)
    (C Dd : Finset (SV (wittIndex V)) → GAd D.sp.cm.sig V.gram → ℂ)
    (hC : ∀ Q ∈ parF (aP P) ∅, Continuous (C Q) ∧ (∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∀ y, C Q (m * y) = C Q y) ∧
      ∀ u ∈ Q, ∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), ∀ n ∈ NA (IsoFlag.single hW), ∀ y, C Q (n * y) = C Q y)
    (hD1 : ∀ z, Dd ∅ z = 1) (wf : GAd D.sp.cm.sig V.gram → ℂ)
    (hsplit : ∀ y ∈ atPts D.sp.cm.sig V.gram T.S, ∀ z ∈ awayPts D.sp.cm.sig V.gram T.S,
      wf (y * z) = ∑ Q ∈ parF (aP P) ∅, C Q y * Dd Q z)
    (bb : awayPts D.sp.cm.sig V.gram T.S)
    (dg : Measure (∀ v : T.S, GLoc D.sp.cm.sig V.gram v)) [dg.IsHaarMeasure]
    (dt : Measure (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ)))) [dt.IsHaarMeasure] :
    quotInt (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ))) dt dg (fun x =>
      wf (embAt D.sp.cm.sig V.gram T.S x * bb) *
          conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) (embAt D.sp.cm.sig V.gram T.S x * bb) -
        C ∅ (embAt D.sp.cm.sig V.gram T.S (projAt D.sp.cm.sig V.gram T.S (embAt D.sp.cm.sig V.gram T.S x * bb))) *
          conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) (embAt D.sp.cm.sig V.gram T.S x * bb)) = 0 := by
  have h0 : (∅ : Finset (SV (wittIndex V))) ∈ parF (aP P) ∅ :=
    mem_parF.2 ⟨⟨Finset.notMem_empty _, by simp⟩, by simp [aP], subset_rfl⟩
  have hff := hF.isFinFamily
  have hsum := hasQuotInt_sum (T := cent (projAt D.sp.cm.sig V.gram T.S (rat V γ))) (dt := dt) (dh := dg)
    ((parF (aP P) ∅).erase ∅)
    (g := fun Q x => (Dd Q bb * ((∏ w, fa w (projArch D.sp.cm.sig V.gram w ((bb : GAd D.sp.cm.sig V.gram)⁻¹ * rat V γ * bb))) *
          ∏ᶠ (v) (_ : v ∈ (T.S : Set (HeightOneSpectrum (𝓞 D.host.F)))ᶜ),
            ff v (proj D.sp.cm.sig V.gram v ((bb : GAd D.sp.cm.sig V.gram)⁻¹ * rat V γ * bb)))) *
        (C Q (embAt D.sp.cm.sig V.gram T.S x) *
          ∏ v : T.S, ff v ((x v)⁻¹ * proj D.sp.cm.sig V.gram v (rat V γ) * x v)))
    fun Q hQ => by
      have hQ' := Finset.mem_of_mem_erase hQ
      exact hasQuotInt_const_mul (hasQuotInt_types hTC T U μf ff hF hμ hH Φ P hP γ hγ hγP Q hQ'
        (Finset.ne_of_mem_erase hQ) (C Q) (hC Q hQ').1 (fun t ht y => (hC Q hQ').2.1 t (hle ht) y)
        (hC Q hQ').2.2 dg dt) _
  refine Eq.trans (congrArg _ (funext fun x => ?_)) hsum.2
  beta_reduce
  rw [conjFn_tensor_split T.S x bb (rat V γ) fa ff hff, projAt_embAt_mul]
  exact sum_erase_split _ h0 _ _ (hD1 bb) _ _ _ (hsplit _ (embAt_mem _ _ T.S x) bb bb.2)

set_option maxHeartbeats 400000 in

theorem wOrbInt_eq_zero : GlobalTheory.Published.LabesseWaldspurger → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ (Φ : GlobalTheory.TruncKer.WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ γ : GlobalTheory.TruncKer.GF V, IsRegSS γ.1.1 → ∀ P, GlobalTheory.TruncKer.IsMinLevi Φ γ P → P ≠ ∅ → ∀ (dt : Measure (cent (GlobalTheory.TruncKer.rat V γ))) [dt.IsHaarMeasure] (Tr : _), wOrbInt (cent (GlobalTheory.TruncKer.rat V γ)) dt μ (GlobalTheory.TruncKer.rat V γ) (fun x => GlobalTheory.TruncKer.weight Φ (levelAll D.sp.cm.sig V.gram L a) (GlobalTheory.Chamber.aP P) Tr x) (tensor D.sp.cm.sig V.gram fa ff) = 0 := by
  intro hLW hPar hTC hRS D V lam S M T U μa μf μ _ _ fa ff hTD Φ L a hG γ hγ P hP hP0 dt _ Tr
  obtain ⟨-, -, -, hNF, hRP, hA, hF⟩ := hTD
  have hff := hF.isFinFamily
  haveI : ∀ w, (μa w).IsHaarMeasure := hRP.haar_arch
  haveI : ∀ v, (μf v).IsHaarMeasure := hRP.haar_loc
  obtain ⟨hPar', hγP, -⟩ := hP
  obtain ⟨hcomm, hle, hnc⟩ := GlobalTheory.T.centralizer_regular_levi_commutative_noncompact D V Φ P hPar' γ hγ hγP
  obtain ⟨C, Dd, hC, hD1, hsplit, hinv⟩ := GlobalTheory.T.truncation_coefficients_invariant hLW D V Φ L a hG P hPar' Tr
  obtain ⟨hH, -⟩ := GlobalTheory.T.typeHypothesis_forms_agree D V T hNF
  have hlevi : ∀ (S' : Finset (HeightOneSpectrum (𝓞 D.host.F))) t, t ∈ Φ.levi D.sp.cm (AF D.host.F) P →
      embAt D.sp.cm.sig V.gram S' (projAt D.sp.cm.sig V.gram S' t) ∈ Φ.levi D.sp.cm (AF D.host.F) P :=
    fun S' t ht => GlobalTheory.T.levi_embedding_projection D V Φ P S' t ht
  have h0 : (∅ : Finset (SV (wittIndex V))) ∈ parF (aP P) ∅ :=
    mem_parF.2 ⟨⟨Finset.notMem_empty _, by simp⟩, by simp [aP], subset_rfl⟩
  have hinvC : ∀ Q ∈ parF (aP P) ∅, LeftInv (cent (rat V γ)) (C Q) := fun Q hQ t ht y => (hC Q hQ).2.1 t (hle ht) y
  have hinvb0 : LeftInv (cent (rat V γ))
      (fun x => C ∅ (embAt D.sp.cm.sig V.gram T.S (projAt D.sp.cm.sig V.gram T.S x))) := fun t ht x => by
    simp only [map_mul]
    exact (hC ∅ h0).2.1 _ (hlevi T.S t (hle ht)) _
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have hF0 := GlobalTheory.T.regular_centralizer_noncompact D V S M μa fa ff (fun w => inferInstance) hA hff γ hγ w (hnc hP0 w)
    (fun x => C ∅ (embAt D.sp.cm.sig V.gram T.S (projAt D.sp.cm.sig V.gram T.S x)))
    ((hC ∅ h0).1.comp ((continuous_embAt _ _ T.S).comp (continuous_projAt _ _ T.S))) hinvb0
    (fun g x => by
      have : projAt D.sp.cm.sig V.gram T.S (embArch D.sp.cm.sig V.gram w g * x) = projAt D.sp.cm.sig V.gram T.S x :=
        funext fun v => by simp
      simp only [this]) μ dt
  unfold wOrbInt
  by_cases hint : Integrable (GlobalTheory.AutomorphicL2Unitary.descend (cent (rat V γ))
    (fun x => (weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr x : ℂ) * conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x))
    (quotMeas (cent (rat V γ)) dt μ)
  swap
  · exact integral_undef hint
  refine quotInt_eq_zero_of_sub hint hF0 ?_

  let e := (atAwayContEquiv D.sp.cm.sig V.gram T.S).symm
  have he : ∀ a b, e (a, b) = embAt D.sp.cm.sig V.gram T.S a * (b : GAd D.sp.cm.sig V.gram) := fun a b => rfl
  have hΓe : e (projAt D.sp.cm.sig V.gram T.S (rat V γ), partAway D.sp.cm.sig V.gram T.S (rat V γ)) = (rat V γ) :=
    embAt_mul_partAway D.sp.cm.sig V.gram T.S (rat V γ)
  have hprod : ∀ a b, e (a, b) ∈ cent (rat V γ) ↔
      a ∈ cent (projAt D.sp.cm.sig V.gram T.S (rat V γ)) ∧ b ∈ cent (partAway D.sp.cm.sig V.gram T.S (rat V γ)) := fun a b => by
    have := mk_mem_cent_iff e a (projAt D.sp.cm.sig V.gram T.S (rat V γ)) b (partAway D.sp.cm.sig V.gram T.S (rat V γ))
    rwa [hΓe] at this
  haveI : LocallyCompactSpace (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ))) := (isClosed_cent _).locallyCompactSpace
  have hinvW : LeftInv (cent (rat V γ)) (fun x => (weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr x : ℂ)) :=
    fun t ht x => by simp only [hinv t (hle ht) x]
  have hcf := leftInv_conjFn (le_refl (cent (rat V γ))) (tensor D.sp.cm.sig V.gram fa ff)
  refine GlobalTheory.T.quotient_measure_fibration _ _ _ e (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ))) (cent (partAway D.sp.cm.sig V.gram T.S (rat V γ))) (cent (rat V γ))
    hprod (isClosed_cent (rat V γ)) hcomm μ dt Measure.haar Measure.haar _ ?_ (hint.sub hF0.1) ?_
  · intro t ht x
    simp only [hinvW t ht x, hcf t ht x, hinvb0 t ht x]
  intro bb
  have hq := quotInt_inner hTC T U μf fa ff hF (fun v => inferInstance) hH Φ P hPar' γ hγ hγP hle C Dd hC hD1
    (fun x => (weight Φ (levelAll D.sp.cm.sig V.gram L a) (aP P) Tr x : ℂ)) (fun y hy z hz => hsplit T.S y hy z hz) bb
    Measure.haar Measure.haar
  simp only [he]
  beta_reduce at hq ⊢
  exact hq

end GlobalTheory.LeviOrb
