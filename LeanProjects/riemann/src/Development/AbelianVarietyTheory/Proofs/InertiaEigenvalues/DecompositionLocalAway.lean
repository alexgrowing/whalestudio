import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TateDualMatrixRepContinuousCrystalline
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInclusion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsUEqCycLL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousTwistedDualRhoO
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section
namespace GlobalTheory.CrysChiOne

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem locC_cont' (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) : Continuous fun g => TruncatedSeriesCountingIdentities.locC C M g := by
  refine continuous_matrix fun a b => ?_
  have h1 : Continuous fun g : Br.G D.nbr i w hw => M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) a b :=
    (hM.matrix_elem a b).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
  have h2 : Continuous fun y : D.nd.O i => (((D.nbr i w hw).eO y : ↥(OL (D.nbr i w hw).LL)) :
      ↥(D.nbr i w hw).LL.1) := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have h3 : Continuous fun y : ↥(D.nbr i w hw).LL.1 => C.inc y :=
    Continuous.subtype_mk continuous_subtype_val _
  exact h3.comp (h2.comp h1)

theorem rx_crys (h41 : SumRepresentations.Conclusion41 D) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (hl0 : D.nd.l i ≠ D.host.g 0) (hl1 : D.nd.l i ≠ D.host.g 1)
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := by
  have h1 := ((((h41 i).2.2 r hr).2.1 w hw).1 hl0 hl1 x).1
  have h2 : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x))) :=
    ((D.loc_tie i w hw).2.1 D.R.nV (r x) (by simpa [rO] using (hr x).1)).1.1 h1
  exact GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw (D.nbr i w hw).LL C.LL C.le
    D.R.nV _ h2

theorem sub_crys (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
    (hcr : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π))))
    (hcont : Continuous fun g => rO D.nd i r π g)
    {k : ℕ} (N : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hN : Continuous fun g => N g)
    (B : Matrix (Fin D.R.nV) (Fin k) (KK D.nd i)) (A : Matrix (Fin k) (Fin D.R.nV) (KK D.nd i))
    (hAB : A * B = 1)
    (hint : ∀ g, mapM (toK D.nd i) (rO D.nd i r π) g * B = B * mapM (toK D.nd i) N g) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C N)) := by
  let φ := GlobalTheory.HTW.RecS.Model.phiK i w hw C
  let Bt : Matrix (Fin D.R.nV) (Fin k) ↥C.LL.1 := B.map φ
  have hinj : Function.Injective Bt.mulVec := by
    have h1 : A.map φ * Bt = 1 := by
      rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero φ) (map_one φ)]
    intro u v huv
    have := congrArg (A.map φ).mulVec huv
    simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this
  have hcN : ∀ (_ : Unit) (v : Fin k → ↥C.LL.1), Continuous fun g => (TruncatedSeriesCountingIdentities.locC C N g).mulVec v :=
    fun _ v => (locC_cont' C N hN).matrix_mulVec continuous_const
  have hcR : ∀ (_ : Unit) (v : Fin D.R.nV → ↥C.LL.1), Continuous fun g => (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π) g).mulVec v :=
    fun _ v => (locC_cont' C _ hcont).matrix_mulVec continuous_const
  have hsub : IsSubOfSums (GRep.mat (Qp := ℚ_[D.nd.l i]) (O := ↥(OL C.LL)) (fun _ : Unit => TruncatedSeriesCountingIdentities.locC C N) hcN ()).ρ
      (fun _ : Unit => ⇑(TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π))) := by
    refine ⟨1, fun _ => (), LinearMap.pi fun _ => Matrix.mulVecLin Bt, ?_, fun g v => ?_⟩
    · intro u v huv
      exact hinj (congrFun huv 0)
    · have key : ∀ (u : Fin k → ↥C.LL.1), Bt.mulVec ((TruncatedSeriesCountingIdentities.locC C N g).mulVec u) =
          (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π) g).mulVec (Bt.mulVec u) := by
        intro u
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        congr 1
        rw [GlobalTheory.HTW.RecS.Model.locC_eq_map, GlobalTheory.HTW.RecS.Model.locC_eq_map]
        simp only [Bt]
        rw [← Matrix.map_mul, ← Matrix.map_mul, hint]
      funext a
      exact key v
  exact (subsum_crys (fun _ : Unit => TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π)) hcR hF (S := fun _ => Set.univ)
    (fun _ => hcr) (fun _ _ _ _ => Set.mem_univ _) _ hsub).1

def chiM (c : ℕ) : GE D.nd →* Matrix (Fin 1) (Fin 1) (D.nd.O i) :=
  twistM (1 : GE D.nd →* Matrix (Fin 1) (Fin 1) (D.nd.O i)) (chiU D.nd i c)

theorem decomp_rho (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π) :
    ∃ (B : Matrix (Fin D.R.nV) (Fin D.R.r) (KK D.nd i)) (A : Matrix (Fin D.R.r) (Fin D.R.nV) (KK D.nd i)),
      A * B = 1 ∧ ∀ g, mapM (toK D.nd i) (rO D.nd i r π) g * B = B * mapM (toK D.nd i) (rhoO D.nd i ρ π) g := by
  obtain ⟨e, he⟩ := hd
  refine ⟨LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inl (KK D.nd i) _ _),
    LinearMap.toMatrix' (LinearMap.fst (KK D.nd i) _ _ ∘ₗ e.toLinearMap), ?_, fun g => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_apply, Matrix.toLin'_apply,
      LinearEquiv.coe_coe]
    apply e.injective
    rw [he]
    simp
    rfl

theorem decomp_chi (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π) :
    ∃ (B : Matrix (Fin D.R.nV) (Fin 1) (KK D.nd i)) (A : Matrix (Fin 1) (Fin D.R.nV) (KK D.nd i)),
      A * B = 1 ∧ ∀ g, mapM (toK D.nd i) (rO D.nd i r π) g * B = B * mapM (toK D.nd i) (chiM (D := D) (i := i) 1) g := by
  obtain ⟨e, he⟩ := hd
  have ht : 0 < D.R.t := by
    have := D.R.rank_add_five_le
    omega
  let c0 : Fin D.R.t := ⟨0, ht⟩
  let L : (Fin 1 → KK D.nd i) →ₗ[KK D.nd i] (Fin D.R.t → KK D.nd i) :=
    LinearMap.single (KK D.nd i) (fun _ => KK D.nd i) c0 ∘ₗ LinearMap.proj 0
  let L' : (Fin D.R.t → KK D.nd i) →ₗ[KK D.nd i] (Fin 1 → KK D.nd i) :=
    LinearMap.pi fun _ => LinearMap.proj c0
  refine ⟨LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inr (KK D.nd i) _ _ ∘ₗ L),
    LinearMap.toMatrix' (L' ∘ₗ LinearMap.snd (KK D.nd i) _ _ ∘ₗ e.toLinearMap), ?_, fun g => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [L, L']
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_apply, Matrix.toLin'_apply,
      LinearEquiv.coe_coe]
    apply e.injective
    rw [he]
    simp only [LinearEquiv.apply_symm_apply, LinearMap.inr_apply]
    ext c
    · simp
    · simp only [L, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply]
      by_cases hc : c = c0
      · subst hc
        simp [chiM, twistM, mapM, Matrix.mulVec, dotProduct, c0]
      · simp [Pi.single_apply, hc]

theorem chiM_cont (c : ℕ) : Continuous fun g => chiM (D := D) (i := i) c g := by
  have : (fun g => chiM (D := D) (i := i) c g) = fun g => ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i) • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
    funext g
    simp [chiM, twistM]
  rw [this]
  exact (D.nd.chi_cont i c).smul continuous_const

theorem locC_chiM_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g : Br.G D.nbr i w hw) :
    TruncatedSeriesCountingIdentities.locC C (chiM (D := D) (i := i) 1) g 0 0 = ((TruncatedSeriesCountingIdentities.chi1C C g : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
  simp [TruncatedSeriesCountingIdentities.locC, TruncatedSeriesCountingIdentities.chi1C, chiM, twistM, Br.loc, Br.locChi, Br.locM, Br.locO, Br.chiG, mapM, LocBridge.toLL]

theorem chi1inv_crys (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hcr : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π))))
    (hcont : Continuous fun g => rO D.nd i r π g) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) := by
  obtain ⟨B, A, hAB, hint⟩ := decomp_chi r ρ π hd
  have h1 : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiM (D := D) (i := i) 1))) :=
    sub_crys C hF r π hcr hcont _ (chiM_cont 1) B A hAB hint
  have h2 := (GlobalTheory.HTW.Rec.tateDual_matRep_crys (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    (TruncatedSeriesCountingIdentities.locC C (chiM (D := D) (i := i) 1)) hF.2.2.1 (locC_cont' C _ (chiM_cont 1)) h1).2
  have h3 : IsCrys (Br.PD D.loc D.nbr i w hw)
      (WeaklyAdmissibleFiltrations.charRep ((TruncatedSeriesCountingIdentities.chi1C C)⁻¹ * cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1)) := by
    refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv _ (LinearEquiv.funUnique (Fin 1) ↥C.LL.1 ↥C.LL.1) ?_ h2
    intro g v
    simp only [LinearEquiv.funUnique_apply, Function.eval]
    change ((twistM (dualM (TruncatedSeriesCountingIdentities.locC C (chiM (D := D) (i := i) 1))) _ g).mulVec v) 0 = _
    simp [twistM, dualM, Matrix.mulVec, dotProduct, WeaklyAdmissibleFiltrations.charRep, locC_chiM_apply]
    left
    rw [mul_comm]
    rfl
  exact (GlobalTheory.BlockCrys.isCrys_mul_cyc _ _).1 h3

theorem twist_crys (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL))
    {k : ℕ} (M : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥C.LL.1) (χ : Br.G D.nbr i w hw →* (↥C.LL.1)ˣ)
    (hM : Continuous fun g => M g) (hM' : Continuous fun g => twistM M χ g)
    (hχ : IsCrys (Br.PD D.loc D.nbr i w hw) (WeaklyAdmissibleFiltrations.charRep χ))
    (hcr : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep M)) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (twistM M χ)) := by
  have hc : ∀ (_ : Unit) (v : Fin k → ↥C.LL.1), Continuous fun g => (M g).mulVec v :=
    fun _ v => hM.matrix_mulVec continuous_const
  have hc' : ∀ (_ : Unit) (v : Fin k → ↥C.LL.1), Continuous fun g => (twistM M χ g).mulVec v :=
    fun _ v => hM'.matrix_mulVec continuous_const
  refine (hF.2.1 (GRep.mat (Qp := ℚ_[D.nd.l i]) (O := ↥(OL C.LL)) (fun _ : Unit => M) hc ())
    (GRep.mat (Qp := ℚ_[D.nd.l i]) (O := ↥(OL C.LL)) (fun _ : Unit => twistM M χ) hc' ()) χ
    ⟨LinearEquiv.refl _ _, fun g x => ?_⟩ hχ hcr).1
  have key : ∀ u : Fin k → ↥C.LL.1, (twistM M χ g).mulVec u = ((χ g : (↥C.LL.1)ˣ) : ↥C.LL.1) • (M g).mulVec u := by
    intro u
    ext j
    simp [twistM, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  exact key x

theorem locC_WpO (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) :
    TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π) = twistM (TruncatedSeriesCountingIdentities.locC C (rhoO D.nd i ρ π)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ := by
  apply MonoidHom.ext
  intro g
  apply Matrix.ext
  intro a b
  have key : ∀ u v : D.nd.O i, C.inc ((D.nbr i w hw).toLL (u * v)) =
      C.inc ((D.nbr i w hw).toLL u) * C.inc ((D.nbr i w hw).toLL v) := by
    intro u v
    rw [map_mul, map_mul]
  exact key _ _

theorem cyc_locC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g : Br.G D.nbr i w hw) :
    ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g : (↥C.LL.1)ˣ) : ↥C.LL.1) =
      C.inc ((D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) := by
  have h := congrArg (fun u : (Br.LL D.nbr i w hw)ˣ => C.inc (u : Br.LL D.nbr i w hw))
    (GlobalTheory.CycBridge.locChi_epsU D i w hw g)
  refine Eq.trans ?_ h.symm
  exact ((IntermediateField.inclusion C.le).commutes _).symm

theorem locC_rDuO (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (x : D.nd.X i) :
    TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x) =
      twistM (dualM (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1) := by
  ext g a b
  simp only [twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.smul_apply, Matrix.transpose_apply,
    smul_eq_mul, cyc_locC]
  congr 1
  show C.inc ((D.nbr i w hw).toLL (rDuO D.nd i r x (decS D.nd w (Br.iota D.nbr i w hw g)) a b)) =
    C.inc ((D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) *
      C.inc ((D.nbr i w hw).toLL (rTwO D.nd i r x (decS D.nd w (Br.iota D.nbr i w hw g⁻¹)) b a))
  rw [← map_mul, ← map_mul, map_inv, map_inv]
  congr 2
  all_goals (simp [rDuO, rTwO, T2O, WpO, twistM, dualM] <;> ring)

theorem locC_T2O (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) :
    TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π) =
      twistM (dualM (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1) := by
  ext g a b
  simp only [twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.smul_apply, Matrix.transpose_apply,
    smul_eq_mul, cyc_locC]
  congr 1
  show C.inc ((D.nbr i w hw).toLL (T2O D.nd i ρ π (decS D.nd w (Br.iota D.nbr i w hw g)) a b)) =
    C.inc ((D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) *
      C.inc ((D.nbr i w hw).toLL (WpO D.nd i ρ π (decS D.nd w (Br.iota D.nbr i w hw g⁻¹)) b a))
  rw [← map_mul, ← map_mul, map_inv, map_inv]
  congr 2
  all_goals (simp [rDuO, rTwO, T2O, WpO, twistM, dualM] <;> ring)

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), SumRepresentations.Conclusion41 D → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i → GoodR D.nd i r → (Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) ∧ (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x)))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) ∧ IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) := by
  intro D i r ρ π h41 hfont hr hρc hd hl0 hl1 w hw C
  have hF := hfont w hw C
  have hcA : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r := continuous_family_of D i r hr
  have hrx := rx_crys h41 r hr hl0 hl1 C
  have hchi := chi1inv_crys C hF r ρ π hd (hrx π) (hcA π)
  have hTw : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
    intro x
    have hc' := locC_cont' C _ (rTwO_cont D i r hcA x)
    rw [locC_rTwO] at hc' ⊢
    exact twist_crys C hF _ _ (locC_cont' C _ (hcA x)) hc' hchi (hrx x)
  obtain ⟨B, A, hAB, hint⟩ := decomp_rho r ρ π hd
  have hrho := sub_crys C hF r π (hrx π) (hcA π) (rhoO D.nd i ρ π) hρc B A hAB hint
  have hWc : Continuous fun g => WpO D.nd i ρ π g := by
    have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
      have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
          fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
        funext g
        rw [map_inv]
        rfl
      rw [e]
      exact (D.nd.chi_cont i 1).comp continuous_inv
    exact h1.smul hρc
  have hW : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) := by
    have hc' := locC_cont' C _ hWc
    rw [locC_WpO] at hc' ⊢
    exact twist_crys C hF _ _ (locC_cont' C _ hρc) hc' hchi hrho
  refine ⟨hchi, fun x => ?_, hW, ?_⟩
  · rw [locC_rDuO]
    exact (GlobalTheory.HTW.Rec.tateDual_matRep_crys (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL _ hF.2.2.1
      (locC_cont' C _ (rTwO_cont D i r hcA x)) (hTw x)).2
  · rw [locC_T2O]
    exact (GlobalTheory.HTW.Rec.tateDual_matRep_crys (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL _ hF.2.2.1
      (locC_cont' C _ hWc) hW).2

end GlobalTheory.CrysChiOne
