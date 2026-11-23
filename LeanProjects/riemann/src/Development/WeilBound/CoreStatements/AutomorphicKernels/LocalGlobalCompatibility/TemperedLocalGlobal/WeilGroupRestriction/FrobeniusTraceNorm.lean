import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjugateDualTwistByTwistOfConjSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPolyOfRecTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompNormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResGRangeSpec
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.GlobalArtinReciprocity
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K

namespace FrobeniusTraceNorm

theorem sum_eq_zero_of_map_mul {B : Multiset ℂˣ} {ζ : ℂˣ} (hζ : ζ ≠ 1) (h : B.map (· * ζ) = B) :
    (B.map fun b : ℂˣ => (b : ℂ)).sum = 0 := by
  have e : (B.map fun b : ℂˣ => (b : ℂ)).sum = (B.map fun b : ℂˣ => (b : ℂ)).sum * (ζ : ℂ) := by
    conv_lhs => rw [← h]
    rw [Multiset.map_map]
    simp only [Function.comp_def, Units.val_mul]
    exact Multiset.sum_map_mul_right
  have hz : (ζ : ℂ) ≠ 1 := fun e => hζ (Units.ext e)
  have h2 : (B.map fun b : ℂˣ => (b : ℂ)).sum * ((ζ : ℂ) - 1) = 0 := by
    rw [mul_sub, mul_one, ← e, sub_self]
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hz)

theorem trace_eq_zero_of_frobPoly {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {m : ℕ} (hm : 1 ≤ m)
    (M : Matrix (Fin m) (Fin m) (Qbar l)) (q : ℕ) (s : Multiset ℂ) (hs : Multiset.card s = m) (h0 : s.sum = 0)
    (h : M.charpoly.map (ι : Qbar l →+* ℂ) = GlobalTheory.SphPar.frobPoly q m s) : M.trace = 0 := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
  have e2 : (s.map fun a => X - C (a * (((q : ℝ) ^ (((m : ℝ) - 1) / 2) : ℝ) : ℂ))) =
      ((s.map fun a => a * (((q : ℝ) ^ (((m : ℝ) - 1) / 2) : ℝ) : ℂ)).map fun x => X - C x) := by
    rw [Multiset.map_map]; rfl
  have hcard : Multiset.card (s.map fun a => a * (((q : ℝ) ^ (((m : ℝ) - 1) / 2) : ℝ) : ℂ)) = m := by
    rw [Multiset.card_map, hs]
  have e1 : (ι : Qbar l →+* ℂ) (M.charpoly.coeff (m - 1)) = 0 := by
    rw [← Polynomial.coeff_map, h, GlobalTheory.SphPar.frobPoly, e2]
    have key := Polynomial.multiset_prod_X_sub_C_coeff_card_pred
      (s.map fun a => a * (((q : ℝ) ^ (((m : ℝ) - 1) / 2) : ℝ) : ℂ)) (by rw [hcard]; omega)
    rw [hcard] at key
    rw [key, Multiset.sum_map_mul_right, Multiset.map_id', h0, zero_mul, neg_zero]
  have e3 : M.charpoly.coeff (m - 1) = 0 := by
    have : ι (M.charpoly.coeff (m - 1)) = ι 0 := by rw [map_zero]; exact e1
    exact ι.injective this
  rw [e3, neg_zero]

theorem trace_frob_inv_eq_zero (HL : GlobalTheory.Published.LocalLanglandsGL) {E Ω : Type} [Field E] [NumberField E] [IsCMField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} {χ : HChar (maximalRealSubfield E)} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : IsGalRepOf π χ ι r wt HT) {w : HeightOneSpectrum (𝓞 E)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {B : Multiset ℂˣ} (hB : GlobalTheory.LFun.HasSatGL w (π.locRep w) B)
    (h0 : (B.map fun b : ℂˣ => (b : ℂ)).sum = 0) {A : ValuationSubring Ω} (hA : IsPlaceOver A w) {g : G E Ω}
    (hg : IsFrob (F := E) A (normV w) g) :
    ((r g⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = 0 := by
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL E a π w
  obtain ⟨α, rfl, hα⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π hB hσ
  have hrc := ParLaws.isRec_locRec HL hA
  have e := GlobalTheory.frobPoly_of_rec_twist hA hl ι H.cont hrc (σ := ParLaws.toRep σ) hα (H.wdOf_eq hl hrc hσ) hg
  exact trace_eq_zero_of_frobPoly ι ha _ _ _ (by simp) h0 e

theorem map_mul_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {π : CuspSub E a} {η : HChar E}
    (hI : (π.twist η).Iso π) {w : HeightOneSpectrum (𝓞 E)} (hu : η.UnrAt w) {B : Multiset ℂˣ}
    (hB : GlobalTheory.LFun.HasSatGL w (π.locRep w) B) : B.map (· * η.val w) = B :=
  (CuspSub.Iso.hasSatGL hI (GlobalTheory.SphGal.hasSatGL_twist E a π η w B hu hB)).unique hB

theorem finite_under {E M : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    {R : Set (HeightOneSpectrum (𝓞 E))} (hR : R.Finite) :
    {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 E) ∈ R}.Finite := by
  refine (hR.biUnion fun v _ => Ideal.finite_factors (I := Ideal.map (algebraMap (𝓞 E) (𝓞 M)) v.asIdeal)
    (Ideal.map_ne_bot_of_ne_bot v.ne_bot)).subset ?_
  intro w hw
  refine Set.mem_biUnion hw ?_
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
  exact le_rfl

theorem finite_dvd (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    {v : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
  have hl : ((l : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 E)})
    (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])).subset ?_
  intro v hv
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem isPlaceOver_under {E M Ω : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω] [Algebra E M]
    [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 M)}
    (h : IsPlaceOver A w) : IsPlaceOver A (w.under (𝓞 E)) := by
  intro x
  have e : algebraMap M Ω ((algebraMap (𝓞 E) (𝓞 M) x : 𝓞 M) : M) = algebraMap E Ω (x : E) := by
    rw [IsScalarTower.algebraMap_apply E M Ω]
    rfl
  rw [← e, h]
  rfl

theorem normV_eq_absNorm {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem isFrob_resG {E M Ω : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω] [Algebra E M]
    [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω] {A : ValuationSubring Ω} {q : ℕ} {σ : G M Ω}
    (h : IsFrob (F := M) A q σ) : IsFrob (F := E) A q (resG E σ) :=
  ⟨resG_mem_Dec (A := A) h.1, fun x hx => h.2 x hx⟩

end FrobeniusTraceNorm

open FrobeniusTraceNorm in
theorem frobenius_trace_place_norm : ContinuationThroughChart := by
  intro HL E Ω _ _ _ _ _ _ a ha π X hGal hp l _ ι r wt HT H η hη1 hηp hsplit hI g hg

  obtain ⟨art, hart, hfull⟩ := GlobalTheory.Published.HeckeLAdicCharacter.full PositivityTheory.Stage1.PM.heckeLAdicCharacter E Ω
  obtain ⟨-, hex, huniq⟩ := hfull l ι
  obtain ⟨ψ, ⟨hψc, -, hψ⟩, -⟩ := hex _ hp.pos η hηp
  have hψ1 : ψ ≠ 1 := by
    rintro rfl
    have hc1 : Continuous (1 : G E Ω →* (Qbar l)ˣ) := continuous_const
    obtain ⟨χ0, -, hχ0⟩ := huniq _ hp.pos 1 hc1 (one_pow _)
    have e1 := hχ0 η ⟨hηp, hψ⟩
    have e2 := hχ0 1 ⟨one_pow _, fun x σ _ => by simp [infPow_zero, lPow_zero]⟩
    exact hη1 (e1.trans e2.symm)

  have hψM : ∀ τ : G X.M Ω, ψ (resG E τ) = 1 := by
    have hT := Filter.eventually_cofinite.1 hsplit
    have hRM := finite_under (M := X.M) (GlobalTheory.Mem.UnrAe.finite_ramified η)
    have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := X.M) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
      (hT.union hRM)
    have hcl : IsClosed ((fun τ : G X.M Ω => ψ (resG E τ)) ⁻¹' {1}) :=
      isClosed_singleton.preimage (hψc.comp continuous_resG)
    intro τ
    refine closure_minimal ?_ hcl (hD τ)
    rintro σ ⟨w, hw, hdeg, B, hB, hF⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
    obtain ⟨hwT, hwR⟩ := hw
    have hBv := isPlaceOver_under (E := E) hB
    obtain ⟨f, hf⟩ := exists_normV_pow hBv hB
    have hpr : (normV w).Prime := by
      rw [normV_eq_absNorm]
      exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified X.M).1 w).2 hdeg
    have hf1 : f = 1 := by
      rw [hf] at hpr
      exact hpr.eq_one_of_pow
    subst hf1
    have hv1 : η.val (w.under (𝓞 E)) = 1 := by
      simpa using hwT 1 hf
    have hFv : IsFrob (F := E) B (normV (w.under (𝓞 E))) (resG E σ) := by
      rw [hf, pow_one] at hF
      exact isFrob_resG hF
    have e := hψ.frob_unr hart (Or.inr rfl) hwR hBv hFv
    rw [hv1] at e
    show ψ (resG E σ) = 1
    exact Units.ext (by rw [e]; simp)

  obtain ⟨-, -, -, hopen, hidx, -⟩ := GlobalTheory.DelGlob.resG_range_spec Ω E X.M
  have hidx' : (resG E (E' := X.M) (Ω := Ω)).range.index = Module.finrank E X.M := hidx
  have hopen' : IsOpen ((resG E (E' := X.M) (Ω := Ω)).range : Set (G E Ω)) := hopen
  have hker : (resG E (E' := X.M) (Ω := Ω)).range ≤ ψ.ker := by
    rintro _ ⟨τ, rfl⟩
    exact hψM τ
  have hne : ∀ g, g ∉ (resG E (E' := X.M) (Ω := Ω)).range → ψ g ≠ 1 := by
    intro g hg h1
    have hdvd : ψ.ker.index ∣ Module.finrank E X.M := hidx' ▸ Subgroup.index_dvd_of_le hker
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · apply hψ1
      have hk := Subgroup.index_eq_one.1 h
      refine MonoidHom.ext fun x => ?_
      have : x ∈ ψ.ker := by rw [hk]; exact Subgroup.mem_top x
      simpa using this
    · have hrel := Subgroup.relIndex_mul_index hker
      rw [h, hidx'] at hrel
      have h1' : (resG E (E' := X.M) (Ω := Ω)).range.relIndex ψ.ker = 1 :=
        Nat.eq_of_mul_eq_mul_right hp.pos (hrel.trans (one_mul _).symm)
      exact hg (Subgroup.relIndex_eq_one.1 h1' (MonoidHom.mem_ker.2 h1))

  have hcont : Continuous fun x : G E Ω => ((r x⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace :=
    ((Units.continuous_val.comp H.cont).comp continuous_inv).matrix_trace
  have hZ : IsClosed {x : G E Ω | ((r x⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = 0} :=
    isClosed_eq hcont continuous_const
  have hS : ({v : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ v.asIdeal} ∪ {v | ¬ η.UnrAt v} ∪
      {v | ¬ ∃ C, GlobalTheory.LFun.HasSatGL v (π.locRep v) C}).Finite :=
    ((finite_dvd E l).union (GlobalTheory.Mem.UnrAe.finite_ramified η)).union
      (Filter.eventually_cofinite.1 (UnrSat.eventually_hasSatGL_locRep CuspFormAutomorphicBounds.automorphicFormsFiniteGL E a π))
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
  have hU : IsOpen (((resG E (E' := X.M) (Ω := Ω)).range : Set (G E Ω))ᶜ) :=
    (Subgroup.isClosed_of_isOpen _ hopen').isOpen_compl
  have hsub : (((resG E (E' := X.M) (Ω := Ω)).range : Set (G E Ω))ᶜ) ⊆
      {x : G E Ω | ((r x⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = 0} := by
    refine (hD.open_subset_closure_inter hU).trans (closure_minimal ?_ hZ)
    rintro σ ⟨hσM, v, hv, -, B, hB, hF⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hv
    obtain ⟨⟨hl, hu⟩, ⟨C, hC⟩⟩ := hv
    have hψσ := hne σ hσM
    have e := hψ.frob_unr hart (Or.inr rfl) hu hB hF
    have hval : η.val v ≠ 1 := by
      intro h1
      apply hψσ
      refine Units.ext ?_
      rw [e, h1]
      simp
    have h0 := sum_eq_zero_of_map_mul hval (map_mul_eq hI hu hC)
    exact trace_frob_inv_eq_zero HL ha H hl hC h0 hB hF
  have hgi : g⁻¹ ∈ (((resG E (E' := X.M) (Ω := Ω)).range : Set (G E Ω))ᶜ) := fun h =>
    hg (by simpa using (resG E (E' := X.M) (Ω := Ω)).range.inv_mem h)
  have := hsub hgi
  simpa using this

end PositivityTheory.Pf1.CLGD.K

end
