import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs
import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LeftInvOfUnitary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicCuspFormAutomorphicBoundedSquareIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpaceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsOpenStabilizerCompletedLatticeAdelicUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedRealStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicative
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective

noncomputable section

namespace GlobalTheory.VolPairExists

section Vol

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField Matrix Topology
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def stab (V : HSp D) : Subgroup (GA D V) where
  carrier := {h : GA D V | ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
    (finMat D.sp.cm.sig V.gram h).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)}
  one_mem' := fun y => by
    rw [GlobalTheory.SmoothForms.RealPts.finMat_eq V, map_one, Units.val_one, Matrix.one_mulVec]
  mul_mem' := fun {a b} ha hb y => by
    rw [GlobalTheory.SmoothForms.RealPts.finMat_eq V, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := fun {a} ha y => by
    refine Iff.trans ?_ (ha _).symm
    rw [GlobalTheory.SmoothForms.RealPts.finMat_eq V, GlobalTheory.SmoothForms.RealPts.finMat_eq V, Matrix.mulVec_mulVec,
      ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]

theorem mem_stab_of_real (V : HSp D) {a : GA D V} (ha : a ∈ GinfC V) : a ∈ stab V := fun y => by
  have ha' : finHom V a = 1 := ha
  rw [GlobalTheory.SmoothForms.RealPts.finMat_eq V, ha', Units.val_one, Matrix.one_mulVec]

theorem exists_volMeas (V : HSp D) (hs : V.SigOK) :
    ∃ μ, IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ := by
  obtain ⟨θ₀, hθ₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  let θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun ρ => θ₀ (tauE D ρ)
  have hθ : IsInfFam θ := fun ρ => hθ₀ _
  have hsp := (GlobalTheory.Member.Arch.archM_spec D V θ₀ hθ₀).1
  have hc : ∀ ρ, Continuous fun h => infMat D.sp.cm.sig V.gram (θ ρ) h := fun ρ => (hsp (tauE D ρ)).2.2.2.1
  have hmul : ∀ ρ g h, infMat D.sp.cm.sig V.gram (θ ρ) (g * h) =
      infMat D.sp.cm.sig V.gram (θ ρ) g * infMat D.sp.cm.sig V.gram (θ ρ) h := fun ρ => (hsp (tauE D ρ)).2.1
  have hu : ∀ ρ h, (infMat D.sp.cm.sig V.gram (θ ρ) h)ᴴ * gramAt D V ρ * infMat D.sp.cm.sig V.gram (θ ρ) h =
      gramAt D V ρ := fun ρ h => (GlobalTheory.Member.Arch.unit_iff _ _ _).1 ((hsp (tauE D ρ)).2.2.2.2 h)
  choose A L hA hl hr using fun ρ => exists_frame (hs (tauE D ρ))
  choose ψ hψ hψm using fun ρ => exists_hom _ (hc ρ) (hmul ρ) (hu ρ) (hA ρ) (hl ρ) (hr ρ)
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : ∀ P Q, IsTopologicalGroup (UpqT P Q) := fun P Q => inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  have : ∀ P Q, BorelSpace (UpqT P Q) := fun P Q => ⟨rfl⟩
  have : ∀ P Q, LocallyCompactSpace (UpqT P Q) := fun P Q =>
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : ∀ P Q, SecondCountableTopology (UpqT P Q) := fun P Q =>
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
  have := D.cd.haar
  have := fun P Q => GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P Q (D.cd.cd P Q) (D.cd.haar P Q)
  have hback : ∀ ρ h, infMat D.sp.cm.sig V.gram (θ ρ) h = L ρ * UpqT.mat (ψ ρ h) * A ρ := fun ρ h => by
    rw [hψm]
    simp only [← Matrix.mul_assoc, hl, Matrix.one_mul]
    rw [Matrix.mul_assoc, hl, Matrix.mul_one]
  obtain ⟨μ, hμ, hμs⟩ := exists_haar_image (stab V) (GlobalTheory.T.isOpen_stabilizer_completedLattice_adelicUnitary D V)
    (Measure.pi fun ρ => D.cd.cd (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) (Pi.monoidHom ψ)
    (continuous_pi hψ) (fun t => by
      obtain ⟨g, hg, hgu⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ V).2 (fun ρ => L ρ * UpqT.mat (t ρ) * A ρ)
        (fun ρ => conj_unitary_back (hA ρ) (hr ρ) (t ρ))
      refine ⟨g, mem_stab_of_real V hg, funext fun ρ => mat_injective ?_⟩
      show UpqT.mat (ψ ρ g) = _
      rw [hψm, hgu]
      simp only [← Matrix.mul_assoc, hr, Matrix.one_mul]
      rw [Matrix.mul_assoc, hr, Matrix.mul_one])
    (fun t => by
      let f : (∀ ρ, UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → ℝ :=
        fun s => ∑ ρ, ∑ i, ∑ j, ‖(L ρ * UpqT.mat (s ρ) * A ρ) i j‖
      have hf : Continuous f := continuous_finset_sum _ fun ρ _ => continuous_finset_sum _ fun i _ =>
        continuous_finset_sum _ fun j _ => (((continuous_const.matrix_mul
          (continuous_mat.comp (continuous_apply ρ))).matrix_mul continuous_const).matrix_elem i j).norm
      obtain ⟨K, hK, hKm⟩ := GlobalTheory.T.exists_compact_lattice_stabilizer_bounded_real D V θ hθ (f t + 1)
      refine ⟨{s | f s < f t + 1}, (isOpen_lt hf continuous_const).mem_nhds (lt_add_one (f t)), K, hK, fun h hh => ?_⟩
      refine hKm h hh.1 fun ρ i j => le_trans ?_ (le_of_lt hh.2)
      rw [hback]
      refine le_trans ?_ (Finset.single_le_sum (f := fun ρ => ∑ i, ∑ j, ‖(L ρ * UpqT.mat (ψ ρ h) * A ρ) i j‖)
        (fun _ _ => by positivity) (Finset.mem_univ ρ))
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖(L ρ * UpqT.mat (ψ ρ h) * A ρ) i j‖)
        (fun _ _ => by positivity) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j => ‖(L ρ * UpqT.mat (ψ ρ h) * A ρ) i j‖)
        (fun _ _ => by positivity) (Finset.mem_univ j))
  refine ⟨μ, hμ, ⟨θ, hθ⟩, fun θ' hθ' => ?_⟩
  obtain rfl : θ = θ' := (GlobalTheory.SmoothForms.RealPts.realPoints D).1 _ _ hθ hθ'
  refine ⟨⟨A, hA⟩, fun A' hA' B hB => ?_⟩
  let u := fun ρ => mkU (A' ρ * L ρ) (change_unitary (hA ρ) (hr ρ) (hA' ρ))
  have hm : ∀ ρ, MeasurableSet ((fun b => b * (u ρ)⁻¹) ⁻¹' ((fun b => u ρ * b) ⁻¹' B ρ)) := fun ρ =>
    measurable_mul_const _ (measurable_const_mul _ (hB ρ))
  have h1 := hμs _ (MeasurableSet.univ_pi hm)
  rw [Measure.pi_pi] at h1
  simp only [measure_preimage_mul_right, measure_preimage_mul] at h1
  rw [← h1]
  congr 1
  ext h
  refine and_comm.trans (and_congr ?_ Iff.rfl)
  rw [Set.mem_preimage, Set.mem_univ_pi]
  exact forall_congr' fun ρ => read_iff (hl ρ) (hr ρ) (u ρ) rfl (ψ ρ h) (hψm ρ h) (B ρ)

theorem exists_volPair (V : HSp D) (hs : V.SigOK) :
    ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2 := by
  obtain ⟨μ, hμ⟩ := exists_volMeas V hs
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := GlobalTheory.T.discreteTopology_rationalPoints_hermitianSpace D V
  obtain ⟨F, -, -, hF⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (GQ V)
  exact ⟨(μ, F), hμ, hF μ⟩

end Vol

section Main

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem sum_toLp_ae {α : Type} [MeasurableSpace α] (μ : Measure α) {m : ℕ} (φ : Fin m → α → ℂ)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (g : Fin m → ℂ) (s : Finset (Fin m)) :
    ((∑ i ∈ s, g i • (hφ i).toLp (φ i) : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] ∑ i ∈ s, g i • φ i := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact Lp.coeFn_zero ℂ 2 μ
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine (Lp.coeFn_add _ _).trans (Filter.EventuallyEq.add ?_ ih)
    exact (Lp.coeFn_smul _ _).trans (((hφ i).coeFn_toLp).const_smul (g i))

set_option maxHeartbeats 1000000 in

theorem phiJ_linearIndependent {D : D7} (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m : ℕ) (b : Fin m → T.cuspA j a n)
    (hb : LinearIndependent T.Q.c.F b) : LinearIndependent ℂ fun i => T.phiJ j σ a (b i : T.R j) := by
  have hU : IsUnf (T.U j σ) := h.unf j hj σ hσ
  have hli : LinearIndependent T.Q.c.F (fun i => (b i : T.R j)) :=
    hb.map' (T.cuspA j a n).subtype (Submodule.ker_subtype _)
  have h1 := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ (T.Q.Xo j) T.Q.c σ _
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU) a n).1 m
    (fun i => (b i : T.R j)) (fun i => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (b i).2) hli
  replace h1 : LinearIndependent ℂ fun i => rdU (T.U j σ) (b i : T.R j) := h1
  rw [Fintype.linearIndependent_iff] at h1 ⊢
  intro w hw
  refine h1 w ?_
  obtain ⟨th, hr, -, hd⟩ := h.dictU j hj σ hσ
  have hmem : (∑ i, w i • rdU (T.U j σ) (b i : T.R j)) ∈ holSub (T.U j σ).X (laU (T.U j σ) a n) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (((mem_cusp _ _ _ a n _).1 (b i).2).2 σ hσ)
  have hEq := eqv_holSub (T.U j σ).X _ hmem
  have hz : ∀ g, (∑ i, w i • rdU (T.U j σ) (b i : T.R j)) (T.dict j σ g).1 (T.dict j σ g).2 = 0 := by
    intro g
    have e := congrFun hw g
    have e2 : (∑ i, w i • T.phiJ j σ a (b i : T.R j)) g =
        ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) * (T.cE j σ (T.dict j σ g).1 * T.mu j σ g)) *
          (∑ i, w i • rdU (T.U j σ) (b i : T.R j)) (T.dict j σ g).1 (T.dict j σ g).2 := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, CoreJ.phiJ, adel_muPin, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e2] at e
    refine (mul_eq_zero.1 e).resolve_left (mul_ne_zero ?_ (mul_ne_zero ?_ ?_))
    · exact_mod_cast (lieFac_pos _ _ _).ne'
    · exact norm_ne_zero_iff.1 (by rw [h.cUnit j hj σ hσ]; exact one_ne_zero)
    · exact norm_ne_zero_iff.1 (by rw [(h.muUnit j hj σ hσ).2.1]; exact one_ne_zero)
  funext k x
  by_cases hx : x ∈ ((T.U j σ).X k).dom
  · obtain ⟨g, γ, hγ, c, hc, hg⟩ := hd.2.2.2.2.1 k x hx
    have hdom := hd.2.2.2.1 g
    have h0 := hz g
    rw [hg] at h0 hdom
    exact eq_zero_of_orbit _ _ _ (hEq.1 k) (hEq.2 k) hx hγ hc hdom h0
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : rdU (T.U j σ) (b i : T.R j) k x = 0 := by
      classical
      exact dif_neg hx
    rw [this, mul_zero]

set_option maxHeartbeats 1000000 in

theorem adelic_linearIndependent : ∀ (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n), (∀ (m : ℕ) (b : Fin m → T.cuspA j a n), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun i => T.phiJ j σ a (b i : T.R j)) ∧ JInj (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) (h.cuspidalL2Subspace j hj σ hσ a n hD) := by
  intro D T h j hj σ hσ a n hD
  refine ⟨phiJ_linearIndependent T h j hj σ hσ a n, fun m b hb => ?_⟩
  have h1 := phiJ_linearIndependent T h j hj σ hσ a n m b hb
  rw [Fintype.linearIndependent_iff] at h1 ⊢
  intro w hw
  refine h1 w ?_
  have hs : (T.V j σ).SigOK := by rw [h.spaceW j hj σ hσ]; exact D.sp.W_sig j
  have hQ : QuotSupp (T.V j σ) := quotSupp_of _ (h.finVol j hj σ hσ) (exists_volPair _ hs)
  have had := fun i => GlobalTheory.T.adelic_cuspForm_automorphic_bounded_square_integrable D T h j hj σ hσ a n hD (b i) (b i).2
  have hae := sum_toLp_ae (muQ1 (T.V j σ))
    (fun i => jFn (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) (b i))
    (fun i => h.cuspidalL2Subspace j hj σ hσ a n hD (b i)) w Finset.univ
  have hae2 : (∑ i, w i • jFn (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) (b i)) =ᵐ[muQ1 (T.V j σ)] 0 := by
    refine hae.symm.trans ?_
    have hw' : (∑ i, w i • (h.cuspidalL2Subspace j hj σ hσ a n hD (b i)).toLp
      (jFn (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) (b i)) : Lp ℂ 2 (muQ1 (T.V j σ))) = 0 := hw
    rw [hw']
    exact Lp.coeFn_zero ℂ 2 _
  funext g
  refine hQ _ ?_ (fun γ hγ g => ?_) ?_ g
  · rw [show (∑ i, w i • T.phiJ j σ a (b i : T.R j)) = fun g => ∑ i, w i * T.phiJ j σ a (b i : T.R j) g from
      funext fun g => by simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
    exact continuous_finset_sum _ fun i _ => continuous_const.mul (had i).2.2.1
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [(had i).1 γ hγ g]
  · filter_upwards [hae2] with q hq
    have e : onQ (T.V j σ) (∑ i, w i • T.phiJ j σ a (b i : T.R j)) q =
        ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) * T.cE j σ (T.dict j σ q.out).1) *
          (∑ i, w i • jFn (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) (b i)) q := by
      show (∑ i, w i • T.phiJ j σ a (b i : T.R j)) q.out = _
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, CoreJ.phiJ, adel_muPin, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show jFn (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) (b i) q =
        T.mu j σ q.out * rdU (T.U j σ) (b i : T.R j) (T.dict j σ q.out).1 (T.dict j σ q.out).2 from rfl]
      ring
    rw [e, hq]
    exact mul_zero _

end Main

end GlobalTheory.VolPairExists
