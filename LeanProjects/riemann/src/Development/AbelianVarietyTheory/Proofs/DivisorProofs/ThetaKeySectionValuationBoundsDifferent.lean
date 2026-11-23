import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthDvdOfNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyScalarIsUnitOnIntegralModelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPoint
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsValuationSubringComapEqNonunits
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush

noncomputable section

namespace GlobalTheory.KeyIntegralVal

section Valuation

open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem exists_mem_different_vLa {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] (σ : E →+* F)
    (w : HeightOneSpectrum (𝓞 F)) : ∃ δ : 𝓞 E, δ ∈ differentIdeal ℤ (𝓞 E) ∧ δ ≠ 0 ∧
      vLa (R := 𝓞 F) w (σ (δ : E)) = (ord_vw w (conjDifferent σ) : ℤ) := by
  have hinj : Function.Injective (RingOfIntegers.mapRingHom σ) := fun a b h =>
    Subtype.ext (σ.injective (congrArg (fun x : 𝓞 F => (x : F)) h))
  have hJ : conjDifferent σ ≠ 0 := fun h =>
    differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E) ((Ideal.map_eq_bot_iff_of_injective hinj).1 h)
  have hfin : FiniteMultiplicity w.asIdeal (conjDifferent σ) := FiniteMultiplicity.of_prime_left w.prime hJ
  have h1 : conjDifferent σ ≤ w.asIdeal ^ ord_vw w (conjDifferent σ) := Ideal.le_of_dvd (pow_multiplicity_dvd _ _)
  have h2 : ¬ conjDifferent σ ≤ w.asIdeal ^ (ord_vw w (conjDifferent σ) + 1) := fun h =>
    hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _) (Ideal.dvd_iff_le.2 h)
  generalize ord_vw w (conjDifferent σ) = n at h1 h2 ⊢
  rw [conjDifferent, Ideal.map_le_iff_le_comap] at h1 h2
  obtain ⟨δ, hδ, hn⟩ := Set.not_subset.1 h2
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hn (Ideal.zero_mem _)
  refine ⟨δ, hδ, hδ0, ?_⟩
  have e : σ (δ : E) = algebraMap (𝓞 F) F (RingOfIntegers.mapRingHom σ δ) := rfl
  have hne : w.intValuation (RingOfIntegers.mapRingHom σ δ) ≠ 0 :=
    w.intValuation_ne_zero _ ((map_ne_zero_iff _ hinj).2 hδ0)
  have a1 := (w.intValuation_le_pow_iff_mem _ n).2 (h1 hδ)
  have a2 := mt (w.intValuation_le_pow_iff_mem (RingOfIntegers.mapRingHom σ δ) (n + 1)).1 hn
  rw [← WithZero.log_le_iff_le_exp hne] at a1 a2
  rw [vLa, e, HeightOneSpectrum.valuation_of_algebraMap]
  push_cast at a2
  omega

theorem nval_bounds {F : Type} [Field F] [NumberField F] {w : HeightOneSpectrum (𝓞 F)} {T : CDVR} {io : F →+* T.Fr}
    {e : ℕ} (ho : OverLa w T.V io e) {ι : Type} [Fintype ι] (x : ι → F) (z : ι → T.V) (n : ι → ℕ) (D : T.V)
    (u : T.Vˣ) (hx : ∀ i, x i ≠ 0) (hz : ∀ i, algebraMap T.V T.Fr (z i) = io (x i)) (hD : D ∣ ∏ i, z i ^ n i) :
    0 ≤ nval T.V e (algebraMap T.V T.Fr (D ^ 4 * (u : T.V))) ∧
      nval T.V e (algebraMap T.V T.Fr (D ^ 4 * (u : T.V))) ≤
        ((4 * ∑ i, (n i : ℝ) * (vLa (R := 𝓞 F) w (x i) : ℝ) : ℝ) : EReal) := by
  classical
  have nn : ∀ a : T.V, 0 ≤ vV T.V (algebraMap T.V T.Fr a) := fun a => by
    by_cases h : algebraMap T.V T.Fr a = 0
    · simp [h, vV]
    have := (WithZero.log_le_log (valV_ne_zero (V := T.V) h) one_ne_zero).2
      (HeightOneSpectrum.valuation_le_one _ a)
    rw [WithZero.log_one] at this
    rw [vV]; omega
  have pw : ∀ (a : T.Fr) (k : ℕ), vV T.V (a ^ k) = k * vV T.V a := fun a k => by simp [vV]
  have hp : ∀ s : Finset ι, vV T.V (∏ i ∈ s, io (x i) ^ n i) = ∑ i ∈ s, n i * (e * vLa w (x i)) := fun s => by
    induction s using Finset.induction_on with
    | empty => simp [vV]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, vV_mul (pow_ne_zero _ ((map_ne_zero io).2 (hx a)))
        (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ ((map_ne_zero io).2 (hx i))), ih, pw, ho.2]
  obtain ⟨q, hq⟩ := hD
  have hq' : algebraMap T.V T.Fr D * algebraMap T.V T.Fr q = ∏ i, io (x i) ^ n i := by
    rw [← map_mul, ← hq, map_prod]
    simp only [map_pow, hz]
  have hne : algebraMap T.V T.Fr D * algebraMap T.V T.Fr q ≠ 0 :=
    hq' ▸ Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ ((map_ne_zero io).2 (hx i))
  have h1 := hp Finset.univ
  rw [← hq', vV_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)] at h1
  have hu : ∀ u : T.Vˣ, algebraMap T.V T.Fr u ≠ 0 := fun u => (u.isUnit.map _).ne_zero
  have hu0 : vV T.V (algebraMap T.V T.Fr u) = 0 := by
    have h := vV_mul (V := T.V) (hu u) (hu u⁻¹)
    rw [← map_mul, Units.mul_inv, map_one, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h
    have := nn u
    have := nn (u⁻¹ : T.Vˣ)
    omega
  have hD0 := pow_ne_zero 4 (left_ne_zero_of_mul hne)
  have he : (0 : ℝ) < e := by exact_mod_cast ho.1
  rw [map_mul, map_pow, nval, if_neg (mul_ne_zero hD0 (hu u)), vV_mul hD0 (hu u), hu0, pw, add_zero]
  have h2 : (0 : ℝ) ≤ vV T.V (algebraMap T.V T.Fr D) := by exact_mod_cast nn D
  have h3 : (vV T.V (algebraMap T.V T.Fr D) : ℝ) ≤ ∑ i, (n i : ℝ) * (e * (vLa w (x i) : ℝ)) := by
    have := nn q
    exact_mod_cast (by omega : vV T.V (algebraMap T.V T.Fr D) ≤ ∑ i, n i * (e * vLa w (x i)))
  refine ⟨EReal.coe_nonneg.2 (by push_cast; positivity), EReal.coe_le_coe_iff.2 ?_⟩
  rw [div_le_iff₀ he, mul_assoc, Finset.sum_mul]
  push_cast
  refine mul_le_mul_of_nonneg_left (h3.trans_eq (Finset.sum_congr rfl fun i _ => by ring)) (by norm_num)

end Valuation

section Lie

open AlgebraicGeometry CategoryTheory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre

theorem exists_lie_matrices {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (act : OAct O G) {n : ℕ} {w : Fin n → (epsR R ⟶ G)} (hw : IsLieBasis w) {I : Type} (τ : I → O →+* R)
    {m : I → ℕ} (u : ∀ i, Fin (m i) → (epsR R ⟶ G)) (h₁ : ∀ i k, IsTangent (u i k))
    (h₂ : ∀ i k a, (u i k ≫ act.act a).left = spMap (epsScaleR (τ i a)) ≫ (u i k).left)
    (h₃ : ∀ i x, IsTangent x → (∀ a, (x ≫ act.act a).left = spMap (epsScaleR (τ i a)) ≫ x.left) →
      ∃ cf, IsLieComb cf (u i) x) :
    ∃ (A : O →+* Matrix (Fin n) (Fin n) R) (U : ∀ i, Fin (m i) → Fin n → R),
      (∀ i (x : Fin n → R), (∀ a, (A a).mulVec x = τ i a • x) → ∃ cf : Fin (m i) → R, x = ∑ k, cf k • U i k) ∧
      (∀ i k a, (A a).mulVec (U i k) = τ i a • U i k) ∧ ∀ i k, IsLieComb (U i k) w (u i k) := by
  let b := Lie.basis act hw
  let A : O →+* Matrix (Fin n) (Fin n) R :=
    (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom.comp (Module.toModuleEnd R (Lie act))
  have hA : ∀ a (x : Lie act), (A a).mulVec (b.equivFun x) = b.equivFun (a • x) := fun a x =>
    LinearMap.toMatrix_mulVec_repr b b (Module.toModuleEnd R (Lie act) a) x
  let u' : ∀ i, Fin (m i) → Lie act := fun i k => Lie.mk act (u i k) (h₁ i k)
  refine ⟨A, fun i k => b.equivFun (u' i k), fun i x hx => ?_, fun i k a => ?_, fun i k => ?_⟩
  · obtain ⟨x, rfl⟩ := b.equivFun.surjective x
    have hm : x ∈ Lie.eig act (τ i) := fun a => b.equivFun.injective (by rw [← hA, hx, map_smul])
    obtain ⟨cf, hcf⟩ := h₃ i x.hom x.isTangent (Lie.mem_eig_iff_left.1 hm)
    refine ⟨cf, ?_⟩
    have : x = ∑ k, cf k • u' i k := Lie.ext ((Lie.isLieComb_iff cf (u' i) x.hom).1 hcf)
    rw [this, map_sum]
    simp only [map_smul]
  · have hm : u' i k ∈ Lie.eig act (τ i) := Lie.mem_eig_iff_left.2 (h₂ i k)
    rw [hA, hm a, map_smul]
  · have hw' : w = fun k => (b k).hom := funext fun k => (Lie.hom_basis (a := act) hw k).symm
    rw [hw', Lie.isLieComb_iff, b.sum_equivFun]
    rfl

theorem isTan_iff_isTangent {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] (w : epsR V ⟶ G) :
    IsTan (V := V) (R := V) (G := G) w ↔ IsTangent w := by
  have : (1 : ptOver V V ⟶ G).left = η[G].left := by
    show spMap (algebraMap V V) ≫ _ = _
    rw [show spMap (algebraMap V V) = 𝟙 _ from Spec.map_id _]
    exact Category.id_comp _
  unfold IsTan IsTangent
  rw [this]

end Lie

section Model

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_model (Xo : Moduli Dw l) (c : Coeff l) (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    (la : HeightOneSpectrum (𝓞 c.F)) : ∃ (W : ValuationSubring ℂ) (p : ℕ) (Y : Model Xo c (c.V W).subtype),
      c.V W = (la.valuation c.F).valuationSubring ∧ p.Prime ∧ Y.LevelStructureConditions p ∧ Y.N3 ∧ Y.N4 ∧ Y.SplitFibres := by
  classical
  obtain ⟨p, hp, hpl⟩ := GlobalTheory.Reg.exists_prime_natCast_mem la
  obtain ⟨W, hWe, hWn⟩ := GlobalTheory.Reg.exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom
    (la.valuation c.F).valuationSubring
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring (la.valuation c.F)).lt_one_iff_lt_one]
    have := (la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).2 hpl
    simpa using this
  have hW : (p : ℂ) ∈ W.nonunits := by simpa using hWn _ hpU
  have key : ∀ X : ∀ l : Level H, Moduli Dw l, ∃ Y : Model (X l) c (c.V W).subtype,
      Y.LevelStructureConditions p ∧ Y.N3 ∧ Y.N4 ∧ Y.SplitFibres := fun X => by
    obtain ⟨Y, hY, -⟩ := GlobalTheory.partI_closed.2 E H Dw hpq X
    obtain ⟨h1, h2⟩ := hY p W hp hW
    obtain ⟨h3, h4, h5⟩ := h2 ⟨l, c, hg p hp⟩
    exact ⟨_, h1.1 ⟨l, c, hg p hp⟩, h4, h5, h3⟩
  have h := key (Function.update (fun l' => Classical.choice (GlobalTheory.Moduli.moduli_scheme_exists E H Dw l' hpq)) l Xo)
  rw [Function.update_self] at h
  obtain ⟨Y, hY⟩ := h
  exact ⟨W, p, Y, hWe, hp, hY⟩

theorem key_unit {κ : KeyRule} (hκ : IsKeyRule κ) (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e)
    {x : Sp T.Fr ⟶ Xo.X} (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) {n : ℕ} {w : Fin n → (epsR T.V ⟶ G.G)} (hw : IsLieBasis w)
    {θ : G.PP.L.Sec} (hθ : Generates (X := G.G) θ) (k : KeyIn T.Fr)
    (hk : IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr)) :
    ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  obtain ⟨W, p, Y, hW, hp, h2, h3, h4, h5⟩ := exists_model Xo c hpq hg la
  obtain ⟨b, hb⟩ := GlobalTheory.EtaVal.exists_base_map_of_overLa (β := (c.V W).subtype)
    (fun a => (Valuation.mem_valuationSubring_iff _ _).1 (hW ▸ a.2)) T io e ho
  have hcond : x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [hxs, GlobalTheory.EtaVal.spMap_comp_spMap]
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift x (spMap io) hcond
  have hzs : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hzf : z ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨yt, h1, -⟩ := extPt Y T b z hx
  obtain ⟨tP, ⟨mP'⟩⟩ : ∃ t : SAB H (Sp T.V), Nonempty (SABMap t Y.t yt) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t t' (pullback.fst _ _) z Y.m0.toSABMap
    (PullbackSections.sabMapCast m1 hzf.symm)
  obtain ⟨mJ, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF
  have hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt := h1.symm
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t tP t' yt (Out.jK T.V) mP' (PullbackSections.sabMapCast mJ hj)
  have hprop : IsProper t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) m1.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance G tP t' hprop m2 mK
  obtain ⟨n', -⟩ := sabComp pullCubComp E H _ _ _ Y.t tP G yt (𝟙 _) mP' ψ
  exact (((GlobalTheory.T.thetaKeyScalar_isUnit_on_integralModels κ hκ E H Dw l Xo c _ _ Y p hpq (isBaseRing_local c W) hp h2 h3 h4 h5).1 T.V T.Fr z yt h1 G
    (PullbackSections.sabMapCast n' (Category.id_comp yt)) n w hw θ k hk).1 hθ).1

theorem isFibreOf_of_sabMap {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {G : SAB H (Sp S)}
    (P : GlobalTheory.CM.PAT H (Sp S')) (n : SABMap P.t G (spMap φ)) (hp : 1 ≤ P.g) {θ : G.PP.L.Sec} {σ : P.t.PP.L.Sec}
    (hσ : ∀ s : Sp S', ∃ q : P.t.G.left, P.t.G.hom q = s ∧ q ∈ Out.nonzeroLocus σ)
    {w : LB.Iso P.t.PP.L (G.PP.L.pull n.φ)} {θ₂ : (G.PP.L.pull n.φ).Sec} (hw : RigIso n w) (hm : IsoMaps w σ θ₂)
    (hθ : PullSec n.φ θ θ₂) {v : Fin P.g → (epsR S ⟶ G.G)} {v' : Fin P.g → (epsR S' ⟶ P.t.G)} (hb : IsLieBasis v')
    (hv : ∀ i, (v' i).left ≫ n.φ = spMap (Chart.dualMapR φ) ≫ (v i).left) :
    IsFibreOf ⟨P.pol, hp, P.t.PP.rig, P.t.PP.rigGen, σ, hσ, v', hb⟩ G.G G.PP.L G.PP.rig θ v φ := by
  have he : eSec P.t.G ≫ n.φ = spMap φ ≫ eSec G.G := n.cm.e_comm.trans (congrArg (· ≫ eSec G.G) n.base)
  have hr : ∀ (e : Sp S' ⟶ Sp S) (_ : n.cm.e = e) (he : eSec P.t.G ≫ n.φ = e ≫ eSec G.G),
      rigPullOf n.φ e he G.PP.L G.PP.rig = n.cm.rigPull G.PP.L G.PP.rig := by
    rintro _ rfl _
    rfl
  refine ⟨n.φ, he, w, rfl, Chart.dualMapR φ, n.cart, hw.1, ?_, fun j i h => ?_, fun a => ?_, ?_, hv⟩
  · exact (hr _ n.base he).symm ▸ hw.2
  · refine Eq.trans ?_ (hm j i)
    have le : (G.PP.L.pull n.φ).U j ≤ n.φ ⁻¹ᵁ G.PP.L.U (j PUnit.unit) := fun y hy => mem_pull.1 hy
    rw [hθ j le, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

theorem exists_tied_det {κ : KeyRule} (hκ : IsKeyRule κ) (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {r : ℕ} (ho : OverLa la T.V io r)
    (τ' : (E →+* ℂ) → (𝓞 E →+* T.V)) (hτ : ∀ τ a, algebraMap T.V T.Fr (τ' τ a) = io (embK c τ a))
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (hy : Integral T io y) :
    letI := io.toAlgebra
    ∃ (Φ : FibKey Xo T.Fr y.x) (A : 𝓞 E →+* Matrix (Fin g) (Fin g) T.V)
      (U : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin g → T.V) (u : T.Vˣ), Tied e y.s y.u Φ ∧
      (∀ τ (x : Fin g → T.V), (∀ a, (A a).mulVec x = τ' τ a • x) →
        ∃ cf : Fin (Dw.mult τ) → T.V, x = ∑ k, cf k • U τ k) ∧
      (∀ τ k a, (A a).mulVec (U τ k) = τ' τ a • U τ k) ∧
      (κ T.Fr Φ.key : T.Fr) =
        algebraMap T.V T.Fr ((Matrix.of fun j k => U (e j).1 (e j).2 k).det ^ 4 * (u : T.V)) := by
  letI := io.toAlgebra
  obtain ⟨G, t', m1, m2, ⟨ub, u1, u2, u3, u4⟩, θ, hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, hp, hs⟩ := hy
  obtain ⟨U₀, hU₀, hg₀⟩ := GlobalTheory.CM.exists_pat_of_obj E H Dw l _ _ _ _ Xo.univ
  obtain ⟨⟨P, rfl, hPg⟩, -⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ y.x U₀ t' (hU₀ ▸ m1)
  obtain ⟨Ψ, -, hΨ, -⟩ := exists_tied E H Dw l Xo c g e T.Fr y hpq
  have hgp : 1 ≤ g := hΨ ▸ Ψ.g_pos
  obtain rfl : P.g = g := hPg.trans (hg₀.trans (card_frame_index Dw e))
  have ht : SecTie m1 σ y.s := ⟨w1, s1, r1, i1, hs⟩
  have hne := ((SecTieEx.secTie_exists_unique E H Dw l Xo T.Fr y.x P.t m1).2.2 σ _ ht).2.1
    (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo T.Fr _ _ y.gen)
  have hB := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c T.Fr y.x y.u P.g e y.tan y.eig).1 y.basis
  obtain ⟨-, hb⟩ := GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo T.Fr y.x P.t.G m1.φ m1.cart
  choose u' hu₁ hu₂ using u4
  have hov : ∀ τ i, u' τ i ≫ P.t.G.hom = (epsR T.Fr).hom := fun τ i => by
    have : IsPreimmersion (spMap (algebraMap T.V T.Fr)) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors T.V)
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu₂,
      Category.assoc, Over.w]
    exact (GlobalTheory.EtaVal.spMap_comp_spMap _ _).trans ((congrArg spMap (RingHom.ext fun a => by
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])).trans (GlobalTheory.EtaVal.spMap_comp_spMap _ _).symm)
  let v : Fin P.g → (epsR T.Fr ⟶ P.t.G) := fun j => Over.homMk (u' (e j).1 (e j).2) (hov _ _)
  have hv : IsLieBasis v := (hb _ v).2 (by
    rw [show (fun j => (v j).left ≫ m1.φ) = fun j => y.u (e j).1 (e j).2 from funext fun j => hu₁ _ _]
    exact hB)
  obtain ⟨n, w, hw⟩ := Chart.exists_isLieBasis G.G G.semi.smooth
  obtain ⟨w', hw', hww⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ _ G.G P.t.G m2.φ m2.cart G.semi.smooth n w hw
  obtain rfl : P.g = n := by
    simpa using Fintype.card_congr ((GlobalTheory.Serre.Lie.basis P.t.act hv).indexEquiv (GlobalTheory.Serre.Lie.basis P.t.act hw'))
  have inj := IsFractionRing.injective T.V T.Fr
  obtain ⟨A, U, a1, a2, a3⟩ := exists_lie_matrices G.act hw τ' (m := Dw.mult) ub
    (fun τ k => (isTan_iff_isTangent _).1 (u1 τ k)) (fun τ k a => u2 τ k a _ (hτ τ a))
    (fun τ x hx he => (u3 τ x ((isTan_iff_isTangent _).2 hx) fun a z hz => by
      rw [inj (hz.trans (hτ τ a).symm)]
      exact he a).exists)
  obtain ⟨u, hu⟩ := key_unit hκ hpq hg ho y.x_over m1 m2 hw hθ _
    (isFibreOf_of_sabMap _ P m2 hgp hne r2 i2 hp hw' hww)
  refine ⟨⟨P, m1, hgp, σ, hne, v, hv⟩, A, U, u, ⟨ht, rfl, fun j => hu₁ _ _⟩, a1, a2, ?_⟩
  have h := hκ.1 T.Fr P.pol hgp P.t.PP.rig P.t.PP.rigGen σ hne w' hw' σ hne v hv 1
    ((Matrix.of fun j k => U (e j).1 (e j).2 k).map (algebraMap T.V T.Fr)) (fun i => by simp [constFn])
    (fun j => Chart.comb_baseChange _ m2.cart (a3 (e j).1 (e j).2) hww (hu₂ _ _))
  rw [one_pow, one_mul, hu] at h
  rw [map_mul, map_pow, RingHom.map_det]
  exact h

end Model

section Main

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem key_valuation_bounds : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : (Rul Xo c)ˣ), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (K : Rul Xo c) ∧ v (K : Rul Xo c) ≤ ((4 * ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) : ℝ) : EReal) := by
  intro κ hκ E _ _ _ H Dw l Xo c g e K hpq hg _ hK w v hv
  classical
  obtain ⟨⟨_, T, io, r, ho, y, -, η, -, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  choose τ' hτ using fun τ : E →+* ℂ => GlobalTheory.EtaVal.exists_base_map_of_overLa (β := embK c τ)
    (fun a => w.valuation_le_one (K := c.F) (RingOfIntegers.mapRingHom (embF c τ) a)) T io r ho
  replace hτ : ∀ τ a, algebraMap T.V T.Fr (τ' τ a) = io (embK c τ a) := fun τ a => DFunLike.congr_fun (hτ τ) a
  have hinj : Function.Injective τ' := fun τ₁ τ₂ h =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a =>
      congrArg Subtype.val (io.injective ((hτ τ₁ a).symm.trans ((h ▸ rfl : _ = _).trans (hτ τ₂ a)))))
  obtain ⟨Φ, A, U, u, hΦ, a1, a2, hu⟩ := exists_tied_det hκ hpq hg e ho τ' hτ y.1 y.2.2
  choose δ hδ hδ0 hδv using fun τ : E →+* ℂ => exists_mem_different_vLa (embF c τ) w
  have hD := GlobalTheory.ColengthDifferent.colength_dvd E T.Fr T.V (E →+* ℂ) τ' Dw.mult g e A U hinj (Embeddings.card E ℂ) inferInstance a1 a2 δ hδ
  have hb := nval_bounds ho (fun τ => embF c τ (δ τ)) (fun τ => τ' τ (δ τ)) Dw.mult _ u
    (fun τ => (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 (hδ0 τ))) (fun τ => hτ τ (δ τ)) hD
  rw [← hu, ← hK T.Fr y.1 Φ hΦ] at hb
  simp only [hδv, Int.cast_natCast] at hb
  exact hb

end Main

end GlobalTheory.KeyIntegralVal
