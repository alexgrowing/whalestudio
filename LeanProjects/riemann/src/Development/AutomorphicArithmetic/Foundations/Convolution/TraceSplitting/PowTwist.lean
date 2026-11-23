import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsRigClosed
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdUnique
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport

noncomputable section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

open GlobalTheory.CuspRep GroundTheory.Global.IdeleGroup PositivityTheory.RgJS

namespace UpperTheory.ConvolutionTheory.T.Pw

variable {K : Type} [Field K] [NumberField K]

private def powHom (K : Type) [Field K] [NumberField K] (s : ℂ) : Neutral.B1.Ideles K →* ℂˣ where
  toFun x := Units.mk0 ((((GroundTheory.Global.IdeleGroup.ideleModule K x).1 : ℝ) : ℂ) ^ s)
    (by
      have := (GroundTheory.Global.IdeleGroup.ideleModule K x).2
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h => by exact_mod_cast this.ne' (by exact_mod_cast h.1))
  map_one' := by
    apply Units.ext
    simp
  map_mul' x y := by
    apply Units.ext
    have hx := (GroundTheory.Global.IdeleGroup.ideleModule K x).2
    have hy := (GroundTheory.Global.IdeleGroup.ideleModule K y).2
    simp only [map_mul, Units.val_mk0, Units.val_mul, Positive.val_mul, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg hx.le hy.le s

private theorem powHom_apply (s : ℂ) (x : Neutral.B1.Ideles K) : ((powHom K s x : ℂˣ) : ℂ) =
    (((GroundTheory.Global.IdeleGroup.ideleModule K x).1 : ℝ) : ℂ) ^ s := rfl

private theorem continuous_powHom (s : ℂ) : Continuous (powHom K s) := by
  refine Units.isEmbedding_val₀.continuous_iff.2 ?_
  refine Continuous.cpow (Complex.continuous_ofReal.comp (continuous_subtype_val.comp
    GroundTheory.Global.IdeleGroup.continuous_ideleModule)) continuous_const fun x => ?_
  exact Or.inl (by simpa using (GroundTheory.Global.IdeleGroup.ideleModule K x).2)

private def powChar (K : Type) [Field K] [NumberField K] (s : ℂ) : HChar K :=
  ⟨powHom K s, continuous_powHom s, fun k => by
    apply Units.ext
    have := GroundTheory.Global.IdeleGroup.ideleModule_diagonal (K := K) k
    rw [powHom_apply]
    have e : GroundTheory.Global.IdeleGroup.ideleModule K (Neutral.B1.diagUnits K k) = 1 := this
    rw [e]
    simp⟩

private theorem isPow_powChar (s : ℂ) : UpperTheory.ConvolutionTheory.T.IsPow (powChar K s) s := fun _ => rfl

private theorem IsPow.inv {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) : UpperTheory.ConvolutionTheory.T.IsPow χ⁻¹ (-s) := fun x => by
  rw [Complex.cpow_neg, ← h x]
  exact Units.val_inv_eq_inv_val (χ.1 x)

private theorem module_local (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((GroundTheory.Global.IdeleGroup.ideleModule K (Neutral.B1.localIdele K v x)).1 : ℝ) = ‖(x : v.adicCompletion K)‖ := by
  have : Neutral.B1.localIdele K v x = GroundTheory.Global.IdeleGroup.finiteEmbedding v x := by
    apply Units.ext
    rfl
  rw [this]
  exact GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x

private theorem norm_of_val (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) (n : ℤ)
    (h : Valued.v x = WithZero.exp n) : ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  rw [FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp [WithZero.exp]

private theorem pow_loc {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← module_local]
  exact h _

private theorem pow_unr {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (v : HeightOneSpectrum (𝓞 K)) : χ.UnrAt v := fun x hx => by
  apply Units.ext
  rw [pow_loc h, norm_of_val v _ 0 (by simpa [Formalism.L2.Host.IsUnitAt] using hx)]
  simp

private theorem pow_val {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (v : HeightOneSpectrum (𝓞 K)) :
    ((χ.val v : ℂˣ) : ℂ) = ((Formalism.ConjugateSelfDual.normV v : ℕ) : ℂ) ^ (-s) := by
  have e : χ.val v = χ.loc v (Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v)) := rfl
  have e2 : (Formalism.ConjugateSelfDual.normV v : ℕ) = Ideal.absNorm v.asIdeal := rfl
  rw [e, pow_loc h, norm_of_val v _ (-1) (Formalism.L2.Host.unif_spec v), e2, zpow_neg_one, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (by positivity)]
      exact Real.pi_pos.ne), Complex.cpow_neg]
  simp

section Expo

variable [IsTotallyComplex K]

private theorem module_infId (u : (Cinf K)ˣ) :
    ((GroundTheory.Global.IdeleGroup.ideleModule K (infId K u)).1 : ℝ) = ∏ w, ‖(u : Cinf K) w‖ ^ 2 := by
  have h1 : GlobalTheory.Mem.Chr.CharModel.finPart K (infId K u) = 1 := Units.ext (by
    change (1 : Af K) - 0 + 0 = 1
    simp)
  have h2 : ((GlobalTheory.Mem.Chr.CharModel.infPart K (infId K u) : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = infEq K u := by
    change (1 : InfiniteAdeleRing K) - infEq K 1 + infEq K u = _
    simp
  have h1' : ∀ v, ((infId K u : Neutral.B1.Ideles K) : NumberField.AdeleRing (𝓞 K) K).2 v = 1 := fun v =>
    congrArg (fun t : (FiniteAdeleRing (𝓞 K) K)ˣ => ((t : FiniteAdeleRing (𝓞 K) K) v)) h1
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  rw [finprod_eq_one_of_forall_eq_one (fun v => by rw [h1' v, norm_one]), mul_one]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h3 : ‖infEq K u w‖ = ‖(u : Cinf K) w‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm) _
  have h4 : ((infId K u : Neutral.B1.Ideles K) : NumberField.AdeleRing (𝓞 K) K).1 w = infEq K u w :=
    congrFun h2 w
  rw [h4, h3, InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w))]

private theorem pow_expo {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (τ : K →+* ℂ) : expo χ τ = s := by
  refine expo_eq_of_exp χ τ s s fun z => ?_
  have e := chiInf_expU_atEmb (GlobalTheory.CuspRep.Model.absC K s) τ z
  rw [GlobalTheory.CuspRep.Model.expo_absC, GlobalTheory.CuspRep.Model.expo_absC] at e
  rw [← e]
  change ((χ.1 (infId K _) : ℂˣ) : ℂ) = Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm K (infId K (expU (atEmb τ z))))
  rw [h, GlobalTheory.CuspRep.Model.logNorm_infId, module_infId]
  have hp : ∀ w, 0 < ‖((expU (atEmb τ z) : (Cinf K)ˣ) : Cinf K) w‖ := fun w =>
    norm_pos_iff.2 (Complex.exp_ne_zero _)
  have hP : 0 < ∏ w, ‖((expU (atEmb τ z) : (Cinf K)ˣ) : Cinf K) w‖ ^ 2 :=
    Finset.prod_pos fun w _ => pow_pos (hp w) 2
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hP.ne'), ← Complex.ofReal_log hP.le,
    Real.log_prod (fun w _ => (pow_pos (hp w) 2).ne'), mul_comm]
  simp [Real.log_pow]

end Expo

section Twist

variable {n : ℕ} [IsTotallyComplex K]

private theorem twist_twist_inv (π : CuspSub K n) (χ : HChar K) : (π.twist χ).twist χ⁻¹ = π := by
  rw [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]

private theorem inf_twist_iff {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (π : CuspSub K n) (t : K →+* ℂ) (m : Multiset ℂ) :
    (π.twist χ).HasInfChar t m ↔ π.HasInfChar t (m.map (· - s)) := by
  constructor
  · intro H
    have := H.twist χ⁻¹
    rwa [twist_twist_inv, pow_expo (IsPow.inv h)] at this
  · intro H
    have := H.twist χ
    rw [pow_expo h, Multiset.map_map] at this
    simpa using this

end Twist

section Lift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsTotallyComplex F] [IsTotallyComplex E] {n : ℕ}

private theorem val_pow {χ : HChar F} {χ' : HChar E} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (h' : UpperTheory.ConvolutionTheory.T.IsPow χ' s)
    (w : HeightOneSpectrum (𝓞 E)) (f : ℕ) (hf : Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 F)) ^ f) :
    χ'.val w = χ.val (w.under (𝓞 F)) ^ f := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, pow_val h, pow_val h', hf, Nat.cast_pow, ← Complex.cpow_nat_mul,
    Complex.natCast_cpow_natCast_mul]

private theorem isLift_twist {χ : HChar F} {χ' : HChar E} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (h' : UpperTheory.ConvolutionTheory.T.IsPow χ' s)
    (π : CuspSub F n) (P : CuspSub E n) (H : UpperTheory.ConvolutionTheory.T.IsLift (.cx π) (.cx P)) :
    UpperTheory.ConvolutionTheory.T.IsLift (.cx (π.twist χ)) (.cx (P.twist χ')) := by
  refine ⟨Filter.Eventually.mono H.1 fun w hw f hf => ?_, fun τ m => ?_⟩
  · obtain ⟨B, hB, hB'⟩ := hw f hf
    refine ⟨B.map (· * χ.val (w.under (𝓞 F))), ?_, ?_⟩
    · have := satake_twist_holds F n (CG.mk π) χ _ B (pow_unr h _) hB
      rwa [CG.twist_mk] at this
    · have := satake_twist_holds E n (CG.mk P) χ' w _ (pow_unr h' _) hB'
      rw [CG.twist_mk] at this
      change (CG.mk (P.twist χ')).HasSat w _
      convert this using 1
      simp [Multiset.map_map, val_pow h h' w f hf, mul_pow]
  · change (π.twist χ).HasInfChar _ m ↔ (P.twist χ').HasInfChar τ m
    rw [inf_twist_iff h, inf_twist_iff h']
    exact H.2 τ _

end Lift

section Local

open scoped GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal
open GroundTheory.Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem norm_completionMap_unit (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v)
    (hs : Function.Surjective (completionMap v w.1)) (x : (v.adicCompletion F)ˣ) :
    ‖completionMap v w.1 (x : v.adicCompletion F)‖ = ‖(x : v.adicCompletion F)‖ := by
  obtain ⟨w, hw⟩ := w
  obtain rfl : GroundTheory.Global.AdeleBaseChange.below F w = v := (GroundTheory.Global.AdeleBaseChange.below_eq_iff w v).2 hw
  haveI := hw
  have hs' : Function.Surjective (algebraMap ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (w.adicCompletion E)) := hs
  have hfr : Module.finrank ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (w.adicCompletion E) = 1 := by
    have := (LinearEquiv.ofBijective (Algebra.linearMap ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (w.adicCompletion E))
      ⟨(algebraMap ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (w.adicCompletion E)).injective, hs'⟩).finrank_eq
    simpa using this.symm
  let y : (w.adicCompletion E)ˣ := Units.map (algebraMap ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (w.adicCompletion E)).toMonoidHom x
  have hn : GroundTheory.LocalField.normUnits ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (w.adicCompletion E) y = x := by
    apply Units.ext
    rw [GroundTheory.LocalField.coe_normUnits]
    change Algebra.norm _ (algebraMap _ (w.adicCompletion E) (x : (GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F)) = _
    rw [Algebra.norm_algebraMap, hfr, pow_one]
  have h2 := GroundTheory.Global.ideleNorm_finiteEmbedding (K := F) w y
  rw [hn] at h2
  have h3 := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F) (GroundTheory.Global.IdeleGroup.finiteEmbedding w y)
  rw [h2] at h3
  have h4 := congrArg Subtype.val h3
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at h4
  exact h4.symm

variable [IsTotallyComplex F] [IsTotallyComplex E] {n : ℕ}

private theorem locDet_map {χ : HChar F} {χ' : HChar E} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (h' : UpperTheory.ConvolutionTheory.T.IsPow χ' s)
    (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v) (hs : Function.Surjective (completionMap v w.1))
    (g : GL (Fin n) (v.adicCompletion F)) :
    CuspSub.locDet n χ v g = CuspSub.locDet n χ' w.1 (mapGL n (completionMap v w.1) g) := by
  apply Units.ext
  rw [CuspSub.locDet, CuspSub.locDet, MonoidHom.comp_apply, MonoidHom.comp_apply, pow_loc h, pow_loc h']
  congr 2
  have e : ((Matrix.GeneralLinearGroup.det (mapGL n (completionMap v w.1) g) : (w.1.adicCompletion E)ˣ) : w.1.adicCompletion E) =
      completionMap v w.1 ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
    exact (RingHom.map_det (completionMap v w.1) g.val).symm
  rw [e, norm_completionMap_unit v w hs]

private theorem locIso_twist {χ : HChar F} {χ' : HChar E} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (h' : UpperTheory.ConvolutionTheory.T.IsPow χ' s)
    (π : CuspSub F n) (P : CuspSub E n) (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v)
    (hs : Function.Surjective (completionMap v w.1))
    (H : ∀ τ τ', (Cusp.cx π).locComp v τ → (Cusp.cx P).locComp w.1 τ' → UpperTheory.ConvolutionTheory.T.LocIso w τ τ') (τ τ')
    (h1 : (Cusp.cx (π.twist χ)).locComp v τ) (h2 : (Cusp.cx (P.twist χ')).locComp w.1 τ') : UpperTheory.ConvolutionTheory.T.LocIso w τ τ' := by
  have a1 : π.IsLocComp v (τ.twist (CuspSub.locDet n χ⁻¹ v) (CuspSub.isOpen_ker_locDet χ⁻¹ v)) := by
    have := CuspSub.IsLocComp.twist (π := π.twist χ) h1 χ⁻¹
    rwa [twist_twist_inv] at this
  have a2 : P.IsLocComp w.1 (τ'.twist (CuspSub.locDet n χ'⁻¹ w.1) (CuspSub.isOpen_ker_locDet χ'⁻¹ w.1)) := by
    have := CuspSub.IsLocComp.twist (π := P.twist χ') h2 χ'⁻¹
    rwa [twist_twist_inv] at this
  obtain ⟨e, he⟩ := H _ _ a1 a2
  let e' : τ.V ≃ₗ[ℂ] τ'.V := e
  have he' : ∀ g (x : τ.V), e' (((CuspSub.locDet n χ⁻¹ v g : ℂˣ) : ℂ) • τ.ρ g x) =
      ((CuspSub.locDet n χ'⁻¹ w.1 (mapGL n (completionMap v w.1) g) : ℂˣ) : ℂ) •
        τ'.ρ (mapGL n (completionMap v w.1) g) (e' x) := he
  refine ⟨e', fun g x => ?_⟩
  have h3 := he' g x
  rw [map_smul, ← locDet_map (IsPow.inv h) (IsPow.inv h') v w hs g] at h3
  exact smul_right_injective _ (Units.ne_zero _) h3

end Local

section Conj

open scoped NumberField.AdeleRing
open Formalism.L2.Host

private theorem denseInf (u : InfinitePlace K) :
    DenseRange (algebraMap K u.Completion) := by
  have h1 : DenseRange (fun x : WithAbs u.1 => (x : UniformSpace.Completion (WithAbs u.1))) :=
    UniformSpace.Completion.denseRange_coe
  have h2 : DenseRange (InfinitePlace.Completion.ofCompletion : _ → u.Completion) :=
    (InfinitePlace.Completion.equiv u).symm.surjective.denseRange
  have h3 := h2.comp h1 (InfinitePlace.Completion.continuous_ofCompletion u)
  refine h3.mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨x.ofAbs, rfl⟩

private theorem normAlg (w : InfinitePlace K) (x : K) :
    ‖algebraMap K w.Completion x‖ = w x :=
  InfinitePlace.Completion.norm_coe (K := K) (v := w) _

private theorem norm_infEquiv (j : K ≃+* K) (u : InfinitePlace K)
    (y : (u.comap j.toRingHom).Completion) : ‖CT.infEquiv j u y‖ = ‖y‖ := by
  have h := (denseInf (u.comap j.toRingHom)).equalizer
    (continuous_norm.comp (CT.continuous_infEquiv j u)) continuous_norm (funext fun x => ?_)
  · exact congrFun h y
  simp only [Function.comp_apply]
  rw [CT.infEquiv_algebraMap, normAlg, normAlg]
  rfl

private theorem mult_comap_equiv (j : K ≃+* K) (u : InfinitePlace K) :
    (u.comap j.toRingHom).mult = u.mult := by
  have h : (u.comap j.toRingHom).IsReal ↔ u.IsReal := InfinitePlace.isReal_comap_iff (f := j)
  unfold InfinitePlace.mult
  by_cases hu : u.IsReal
  · rw [if_pos (h.2 hu), if_pos hu]
  · rw [if_neg (mt h.1 hu), if_neg hu]

private def infPerm (j : K ≃+* K) : InfinitePlace K ≃ InfinitePlace K where
  toFun u := u.comap j.toRingHom
  invFun u := u.comap j.symm.toRingHom
  left_inv u := by
    ext x
    show u (j (j.symm x)) = u x
    rw [RingEquiv.apply_symm_apply]
  right_inv u := by
    ext x
    show u (j.symm (j x)) = u x
    rw [RingEquiv.symm_apply_apply]

private def finPerm (j : K ≃+* K) :
    HeightOneSpectrum (𝓞 K) ≃ HeightOneSpectrum (𝓞 K) where
  toFun v := CT.plMap j.symm v
  invFun v := CT.plMap j v
  left_inv v := CT.plMap_plMap_symm j v
  right_inv v := CT.plMap_symm_plMap j v

private theorem module_map (σ : K ≃+* K) (x : (𝔸[K])ˣ) :
    (GroundTheory.Global.IdeleGroup.ideleModule K (Units.map (CT.adMap σ).toMonoidHom x) : ℝ) =
      GroundTheory.Global.IdeleGroup.ideleModule K x := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  congr 1
  · refine Fintype.prod_equiv (infPerm σ) _ _ fun u => ?_
    show ‖CT.infEquiv σ u ((x : 𝔸[K]).1 (u.comap σ.toRingHom))‖ ^ u.mult =
      ‖(x : 𝔸[K]).1 (u.comap σ.toRingHom)‖ ^ (u.comap σ.toRingHom).mult
    rw [norm_infEquiv, mult_comap_equiv]
  · have h : ∀ v : HeightOneSpectrum (𝓞 K),
        ‖((Units.map (CT.adMap σ).toMonoidHom x : (𝔸[K])ˣ) : 𝔸[K]).2 v‖ =
          ‖(x : 𝔸[K]).2 (finPerm σ v)‖ := fun v => by
      show ‖(CT.compEquiv σ.symm v).symm ((x : 𝔸[K]).2 (CT.plMap σ.symm v))‖ = _
      have e := CT.norm_compEquiv σ.symm v ((CT.compEquiv σ.symm v).symm ((x : 𝔸[K]).2 (CT.plMap σ.symm v)))
      rw [RingEquiv.apply_symm_apply] at e
      exact e.symm
    exact (finprod_congr h).trans
      (finprod_comp_equiv (finPerm σ) (f := fun w => ‖(x : 𝔸[K]).2 w‖))

variable [IsTotallyComplex K] {n : ℕ}

private theorem galAd_eq (σ : K ≃+* K) (S : Ad K ≃+* Ad K) (h : UpperTheory.CBC.IsGalAd σ S) : S.toRingHom = CT.adMap σ :=
  UpperTheory.ConvolutionTheory.K.adUnique K σ S.toRingHom h.1 h.2.1

private theorem chiDet_gal {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (σ : K ≃+* K) (S : Ad K ≃+* Ad K)
    (hS : UpperTheory.CBC.IsGalAd σ S) (g : GA K n) :
    chiDet n χ (Matrix.GeneralLinearGroup.map S.toRingHom g) = chiDet n χ g := by
  apply Units.ext
  have e : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map S.toRingHom g) =
      Units.map (CT.adMap σ).toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
    apply Units.ext
    rw [← galAd_eq σ S hS]
    exact (RingHom.map_det S.toRingHom g.val).symm
  change ((χ.1 (Matrix.GeneralLinearGroup.det _) : ℂˣ) : ℂ) = ((χ.1 (Matrix.GeneralLinearGroup.det _) : ℂˣ) : ℂ)
  rw [e, h, h, module_map]

private theorem conj_twist {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (P : CuspSub K n) (σ : K ≃+* K)
    (hC : (Cusp.cx P).ConjIso σ) : (Cusp.cx (P.twist χ)).ConjIso σ := by
  intro S hS
  obtain ⟨P', hsp, hI⟩ := hC S hS
  cases P' with
  | re Q => exact hI.elim
  | cx Q =>
    refine ⟨.cx (Q.twist χ), ?_, CuspSub.Iso.twist hI χ⟩
    have key := fun g : GA K n => chiDet_gal (n := n) h σ S hS g
    ext f
    constructor
    · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
      have m : ψ.1 ∈ (Cusp.cx Q).space := ⟨ψ, hψ, rfl⟩
      rw [hsp] at m
      obtain ⟨_, ⟨ρ, hρ, rfl⟩, e⟩ := m
      refine ⟨(mulChi n χ ρ).1, ⟨mulChi n χ ρ, ⟨ρ, hρ, rfl⟩, rfl⟩, ?_⟩
      funext g
      have e' := congrFun e g
      change (mulChi n χ ρ).1 _ = (mulChi n χ ψ).1 g
      rw [mulChi_apply, mulChi_apply, key, ← e']
    · rintro ⟨_, ⟨_, ⟨ρ, hρ, rfl⟩, rfl⟩, rfl⟩
      have m : (fun g : GA K n => ρ.1 (Matrix.GeneralLinearGroup.map S.toRingHom g)) ∈ (Cusp.cx Q).space := by
        rw [hsp]
        exact ⟨ρ.1, ⟨ρ, hρ, rfl⟩, rfl⟩
      obtain ⟨ψ, hψ, e⟩ := m
      refine ⟨mulChi n χ ψ, ⟨ψ, hψ, rfl⟩, ?_⟩
      funext g
      have e' := congrFun e g
      change (mulChi n χ ρ).1 _ = (mulChi n χ ψ).1 g
      rw [mulChi_apply, mulChi_apply, key]
      exact congrArg (· * _) e'

end Conj

end UpperTheory.ConvolutionTheory.T.Pw

open UpperTheory.ConvolutionTheory.T.Pw in
theorem UpperTheory.ConvolutionTheory.T.powTwist :
    UpperTheory.ConvolutionTheory.T.PowTwist := by
  intro F E _ _ _ _ _ _ _
  refine ⟨fun s => ⟨⟨_, isPow_powChar s⟩, ⟨_, isPow_powChar s⟩⟩, fun s χ χ' h h' =>
    ⟨IsPow.inv h, IsPow.inv h', fun n _ => ⟨fun π => twist_twist_inv π χ, fun P => twist_twist_inv P χ',
      fun π P H => isLift_twist h h' π P H, fun P g hC => conj_twist h' P g hC,
      fun π P v w hs H τ τ' h1 h2 => locIso_twist h h' π P v w hs H τ τ' h1 h2⟩⟩⟩
