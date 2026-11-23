import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EWtApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsWeightEqParameterSubRhoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainComplexFormsEqAlgebraicModularFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainFormsRationalIffFrameValuesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleIntegralFormsRowPlaceByPlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.Col2.TwP.weightedInner_twisted : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ (o : Formalism.L2.Forms.FrP (I.rec7 l Z)), o.IsON → ∀ (z z' : (I.per l u a).Wrow) (Pc Qc : (I.fm l u a).clsP → MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) ℂ), (∀ c, Pc c ∈ CSpan (I.fm l u a).sg) → (∀ c, Qc c ∈ CSpan (I.fm l u a).sg) → (∀ c, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z c = fnOf _ (shiftOf (sgTG (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Pc c)) → (∀ c, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z' c = fnOf _ (shiftOf (sgTG (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Qc c)) → (I.fm l u a).ipP z z' = ∑ c, ((Nat.card ((I.fm l u a).stabilizer₂ c) : ℕ) : ℂ)⁻¹ * nfAll (I.fm l u a).sg (Qc c) (Pc c) := by
  intro B X I hI hP l Z u a o ho z z' Pc Qc _ _ hz hz'
  have hgP : gramP (I.rec7 l Z) = 1 := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.1
  have hG : ∀ τ, gramC (gramP (I.rec7 l Z)) (Formalism.L2.Forms.embT (I.rec7 l Z)) τ = 1 := fun τ => by
    rw [hgP, gramC_one]
  have hsh : shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := by
    refine congrArg shiftOf (funext fun τ => ?_)
    obtain ⟨t, ht⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (t + 1) := by
      rw [ht, show B.R.m * (2 * t + 1 + 1) = 2 * (B.R.m * (t + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = t + 1 := by omega
    show Formalism.L2.Forms.shW _ _ = GlobalTheory.Mem.Col2.shW _ _
    simp only [Formalism.L2.Forms.shW, GlobalTheory.Mem.Col2.shW]
    congr 1
    funext i
    show ((I.perIn u a).sg τ).w i - ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) = ((I.perIn u a).sg τ).w i + -((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
    rw [e1, e2]
    push_cast
    ring
  have hl : nfAll (I.perIn u a).sgT = nfAll (I.fm l u a).sg :=
    MetricTie.nfAll_shift _ _ _ fun _ _ => rfl
  show (I.perIn u a).ipP B.fields.emb B.embLL (l.per u a) z z' = _
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 : z c = fun s => fnOf _ (shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Pc c) (id s : Formalism.L2.Forms.FrP (I.rec7 l Z)) := hz c
  have e2 : z' c = fun s => fnOf _ (shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a))) (fun τ => (o.1 τ)⁻¹) (Qc c) (id s : Formalism.L2.Forms.FrP (I.rec7 l Z)) := hz' c
  show (I.perIn u a).wt c * ipVal B.fields.emb B.embLL (I.perIn u a).sgT (z c) (z' c) = _
  rw [e1, e2]
  exact congrArg₂ (· * ·) rfl (MetricTie.ipVal_step B.fields.emb B.embLL (I.perIn u a).sgT hl hsh hG id (fun _ => rfl) o ho (Pc c) (Qc c))

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.Col2.TwP.norm_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (K : ClassesAtPrimes (I.fm l u a) bad) {okW : (I.rec7 l Z).what₂.places.Pl → Prop} (V : ValuationAtPrimes K okW), (∀ z, V.eW z = GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z) → NormPTieG V := by
  intro B X I hI hP l Z u a bad K okW V hV s x Pc hPc o ho
  have hgP : gramP (I.rec7 l Z) = 1 := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.1
  have hsh : shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := by
    refine congrArg shiftOf (funext fun τ => ?_)
    obtain ⟨t, ht⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (t + 1) := by
      rw [ht, show B.R.m * (2 * t + 1 + 1) = 2 * (B.R.m * (t + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = t + 1 := by omega
    show Formalism.L2.Forms.shW _ _ = GlobalTheory.Mem.Col2.shW _ _
    simp only [Formalism.L2.Forms.shW, GlobalTheory.Mem.Col2.shW]
    congr 1
    funext i
    show ((I.perIn u a).sg τ).w i - ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) = ((I.perIn u a).sg τ).w i + -((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
    rw [e1, e2]
    push_cast
    ring
  have hl : nfAll (I.perIn u a).sgT = nfAll (I.fm l u a).sg :=
    MetricTie.nfAll_shift _ _ _ fun _ _ => rfl
  have h := @MetricTie.norm_step _ _ _ _ _ _ _ _ _ _ _ B.fields.emb B.embLL (I.perIn u a).sgT (I.stX a) (base_fOk B)
    (l.per u a).step (l.fmL u a).famP ((I.perIn u a).clFin (l.per u a)) _ hl _ hsh _ _
    (fun τ => by rw [hgP, gramC_one]; rfl) (fun y => (y : Formalism.L2.Forms.FrP (I.rec7 l Z))) (fun _ => rfl) s x Pc
    (fun c z => by
      have e := (congrFun (hV ((I.fm l u a).ptEmb x)) c).symm.trans (hPc c)
      exact congrFun e z) o ho
  refine h.trans (Finset.sum_congr rfl fun c _ => ?_)
  congr 2
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
  rfl

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mem.Col2.TwP.forms_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∃ V : ValuationAtPrimes K (okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T), NormPTieG V ∧ ∀ z c (s : FrP (I.rec7 l Z)) s', s'.1 = s.1 → V.eW z c s = z c s' := by
  intro B X I hI hP l Z u a Q K hQ hQv hK
  let V : ValuationAtPrimes K (okPT (I.rec7 l Z) Q ((I.rec7 l Z).mem u).A.T) :=
    { sg := GlobalTheory.T.rowForms_weight_eq_parameter_sub_rho I hI hP l Z u a
      eW := GlobalTheory.Mem.Col2.TwP.eWt I l Z u a
      ptC := GlobalTheory.T.tupleChain_complexForms_eq_algebraicModularForms I hI hP l Z u a Q K hQ hQv hK
      ipP := GlobalTheory.Mem.Col2.TwP.weightedInner_twisted I hI hP l Z u a
      rat := GlobalTheory.T.tupleChain_forms_rational_iff_frame_values I hI hP l Z u a
      lat := GlobalTheory.T.tuple_integralForms_row_place_by_place I hI hP l Z u a Q K hQ hQv hK }
  refine ⟨V, GlobalTheory.Mem.Col2.TwP.norm_tw I hI hP l Z u a K V fun _ => rfl, fun z c s s' h => ?_⟩
  exact GlobalTheory.Mem.Col2.TwP.eWt_apply I l Z u a z c s s' h

end
