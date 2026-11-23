import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeWeylDS
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHCut
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CdHaarScale
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

noncomputable section

open scoped Classical InnerProductSpace ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section HS

variable {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

theorem sum_norm_sq_eq_trace {ι : Type} [Fintype ι] (A : Wq →L[ℂ] Wp) (b : OrthonormalBasis ι ℂ Wq) :
    ∑ i, ‖A (b i)‖ ^ 2 =
      (LinearMap.trace ℂ Wq (((ContinuousLinearMap.adjoint A).comp A : Wq →L[ℂ] Wq) : Wq →ₗ[ℂ] Wq)).re := by
  have := FiniteDimensional.complete ℂ Wq
  rw [LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm

theorem hsNormSq_eq_sum {ι : Type} [Fintype ι] (A : Wq →L[ℂ] Wp) (b : OrthonormalBasis ι ℂ Wq) :
    hsNormSq A = ∑ i, ‖A (b i)‖ ^ 2 := by
  have h0 : hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
    unfold hsNormSq hsInner
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [h0, sum_norm_sq_eq_trace A b, sum_norm_sq_eq_trace A (stdOrthonormalBasis ℂ Wq)]

variable {Wq' Wp' : Type} [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [CompleteSpace Wp']

theorem hsNormSq_of_iso (A : Wq →L[ℂ] Wp) (A' : Wq' →L[ℂ] Wp') (V : Wq ≃ₗᵢ[ℂ] Wq') (g : Wp → Wp')
    (hg : ∀ y, ‖g y‖ = ‖y‖) (h : ∀ x, A' (V x) = g (A x)) : hsNormSq A' = hsNormSq A := by
  let b := stdOrthonormalBasis ℂ Wq
  rw [hsNormSq_eq_sum A' (b.map V), hsNormSq_eq_sum A b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [OrthonormalBasis.map_apply, h, hg]

theorem hsNormSq_of_semi (A : Wq →L[ℂ] Wp) (A' : Wq' →L[ℂ] Wp') (f : Wq →+ Wq')
    (hfs : ∀ (c : ℂ) x, f (c • x) = conj c • f x) (hfi : ∀ x y, ⟪f x, f y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hsurj : Function.Surjective f) (g : Wp → Wp') (hg : ∀ y, ‖g y‖ = ‖y‖)
    (h : ∀ x, A' (f x) = g (A x)) : hsNormSq A' = hsNormSq A := by
  let b := stdOrthonormalBasis ℂ Wq
  have hon : Orthonormal ℂ (fun i => f (b i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hfi, (orthonormal_iff_ite.1 b.orthonormal) j i]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun i => f (b i)) := by
    intro y _
    obtain ⟨x, rfl⟩ := hsurj y
    have hx : f x = ∑ i, conj (⟪b i, x⟫_ℂ) • f (b i) := by
      conv_lhs => rw [← b.sum_repr' x]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => hfs _ _
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' := OrthonormalBasis.mk hon hsp
  rw [hsNormSq_eq_sum A' b', hsNormSq_eq_sum A b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [OrthonormalBasis.coe_mk, h, hg]

theorem opNorm_le_hs (A : Wq →L[ℂ] Wp) :
    ‖A‖ ≤ (Module.finrank ℂ Wq : ℝ) * ‖Formalism.L2.SG.PackageTie.hsEmb A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  let b := stdOrthonormalBasis ℂ Wq
  have hcomp : ∀ i, ‖A (b i)‖ ≤ ‖Formalism.L2.SG.PackageTie.hsEmb A‖ := by
    intro i
    have h1 : ‖A (b i)‖ ^ 2 ≤ ‖Formalism.L2.SG.PackageTie.hsEmb A‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      exact Finset.single_le_sum (f := fun j => ‖(Formalism.L2.SG.PackageTie.hsEmb A) j‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i)
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
  calc ‖A x‖ = ‖∑ i, ⟪b i, x⟫_ℂ • A (b i)‖ := by
        conv_lhs => rw [← b.sum_repr' x]
        rw [map_sum]
        simp only [map_smul]
    _ ≤ ∑ i, ‖⟪b i, x⟫_ℂ • A (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℂ Wq), ‖x‖ * ‖Formalism.L2.SG.PackageTie.hsEmb A‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul]
        have h1 : ‖⟪b i, x⟫_ℂ‖ ≤ ‖x‖ := by
          have := norm_inner_le_norm (𝕜 := ℂ) (b i) x
          rwa [b.orthonormal.1 i, one_mul] at this
        exact mul_le_mul h1 (hcomp i) (norm_nonneg _) (norm_nonneg _)
    _ = (Module.finrank ℂ Wq : ℝ) * ‖Formalism.L2.SG.PackageTie.hsEmb A‖ * ‖x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end HS

section Iso

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {Word Tau : Type} [Fintype Tau] {hc : Word → Tau → HCParam R}

theorem kmat_iso (s s' : Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc) (I : SIso s s') (u u' : Word)
    (x : s.Cu u') : Kmat s' u u' (I.eCu u' x) = I.eCu u (Kmat s u u' x) := by
  have := FiniteDimensional.complete ℂ (s.Cu u)
  have := FiniteDimensional.complete ℂ (s.Cu u')
  have := FiniteDimensional.complete ℂ s.HH
  have := FiniteDimensional.complete ℂ (s'.Cu u)
  have := FiniteDimensional.complete ℂ (s'.Cu u')
  have := FiniteDimensional.complete ℂ s'.HH
  have hc0 : ∀ w, Formalism.MainNotions.S.c0 s w = Formalism.MainNotions.S.c0 s' w := fun w => by unfold Formalism.MainNotions.S.c0; rw [I.volN, I.volH]
  have hadj : ∀ y, ContinuousLinearMap.adjoint (s'.Pu u) (I.eHH y) =
      I.eCu u (ContinuousLinearMap.adjoint (s.Pu u) y) := by
    intro y
    refine ext_inner_left ℂ fun w => ?_
    obtain ⟨z, rfl⟩ := (I.eCu u).surjective w
    rw [ContinuousLinearMap.adjoint_inner_right, ← I.Pu_eq, LinearIsometryEquiv.inner_map_map,
      LinearIsometryEquiv.inner_map_map, ContinuousLinearMap.adjoint_inner_right]
  unfold Kmat
  rw [hc0 u, hc0 u']
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul]
  rw [← I.Pu_eq, hadj]

theorem isoNorm : IsoNorm := by
  intro R F E _ _ _ _ _ sig Word Tau _ hc s s' I u u'
  have := FiniteDimensional.complete ℂ (s.Cu u)
  have := FiniteDimensional.complete ℂ (s'.Cu u)
  exact (hsNormSq_of_iso (Kmat s u u') (Kmat s' u u') (I.eCu u') (I.eCu u) (fun y => (I.eCu u).norm_map y)
    (kmat_iso s s' I u u')).symm

end Iso

section Tr

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word} {hK : X.LevelSubgroupCharacter}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} {cs : ColSys X u what₂} {cs' : ColSys X u' rows'}
  {hinj : Function.Injective (sharp hK cs)} {hinj' : Function.Injective (sharp hK cs')}

theorem norm_shT (T : ColT hinj) : ‖shT hinj T‖ = ‖T‖ := by
  have h1 : ‖shT hinj T‖ ^ 2 = ‖T‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ) T, inner_colT hinj T T]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

def shTAdd (hinj : Function.Injective (sharp hK cs)) : ColT hinj →+ CM cs where
  toFun := shT hinj
  map_zero' := shT_zero hinj
  map_add' := shT_add hinj

variable (hb : Function.Bijective (shT hinj)) (hb' : Function.Bijective (shT hinj'))

theorem norm_shInv (x : CM cs) : ‖shInv hb x‖ = ‖x‖ := by
  rw [← norm_shT, shT_shInv]

theorem norm_tr_le (A : CM cs' →L[ℂ] CM cs) : ‖tr hb hb' A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun T' => ?_
  rw [tr_apply, norm_shInv, ← norm_shT T']
  exact A.le_opNorm _

def trAdd : (CM cs' →L[ℂ] CM cs) →+ (ColT hinj' →L[ℂ] ColT hinj) where
  toFun := tr hb hb'
  map_zero' := by
    ext1 T'
    rw [tr_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply]
    apply shT_injective hinj
    rw [shT_shInv, shT_zero]
  map_add' A B := by
    ext1 T'
    rw [ContinuousLinearMap.add_apply, tr_apply, tr_apply, tr_apply, ContinuousLinearMap.add_apply, shInv_add]

theorem continuous_trAdd : Continuous (trAdd hb hb') :=
  AddMonoidHomClass.continuous_of_bound (trAdd hb hb') 1 fun A => by
    rw [one_mul]
    exact norm_tr_le hb hb' A

end Tr

section Ties

open Formalism.L2.SG.Full

variable {D : D7} {X : HidaSetting D} {Y : Full X} (hF : FinX Y)

theorem dimPi_nonneg (u : D.what₂.Word) : 0 ≤ dimPi (hc := D.hcW) u :=
  Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _

theorem weightConst_nonneg (u : D.what₂.Word) : 0 ≤ Formalism.MainNotions.S.c0 (sOf hF) u := by
  unfold Formalism.MainNotions.S.c0
  exact div_nonneg (mul_nonneg (hF.volPos u).1.le (hF.volPos u).2.le) (dimPi_nonneg u)

include hF in

theorem normalizing_constant_eq_of_dimTie {u : D.what₂.Word} (hd : DimTie (X := X) u) : c0X X u (Y.FN u) = Formalism.MainNotions.S.c0 (sOf hF) u := by
  rw [Y.poincare_constant_eq u, hd]
  rfl

theorem kmat_eq {u u' : D.what₂.Word} (hd : DimTie (X := X) u) (hd' : DimTie (X := X) u')
    (K : CM (Y.cs u') →L[ℂ] CM (Y.cs u))
    (hK : ∀ (T : Cu X u Y.hK) (T' : Cu X u' Y.hK),
      Kform X u u' Y.hK (Y.Dt u) (Y.Dt u') (Y.FN u) (Y.FN u') T T' =
        ⟪K (sharp Y.hK (Y.cs u') T'), sharp Y.hK (Y.cs u) T⟫_ℂ) :
    Kmat (sOf hF) u u' = tr (hF.shBij u) (hF.shBij u') K := by
  have := finiteDimensional_colT (hF.shBij u)
  have := finiteDimensional_colT (hF.shBij u')
  have := FiniteDimensional.complete ℂ (ColT (hF.shInj u))
  have := FiniteDimensional.complete ℂ (ColT (hF.shInj u'))
  have : FiniteDimensional ℂ (HHX X) := hF.finHH
  have := FiniteDimensional.complete ℂ (HHX X)
  have aux : ∀ (T : ColT (hF.shInj u)) (T' : ColT (hF.shInj u')),
      ⟪T, (Kmat (sOf hF) u u' T' : ColT (hF.shInj u))⟫_ℂ = ⟪T, tr (hF.shBij u) (hF.shBij u') K T'⟫_ℂ := by
    intro T T'
    rw [inner_colT _ T (tr _ _ K T'), shT_tr]
    refine Eq.trans ?_ (hK T T')
    have hc : (Formalism.MainNotions.S.c0 (sOf hF) u * Formalism.MainNotions.S.c0 (sOf hF) u') ^ (-(1 / 2 : ℝ)) =
        (Real.sqrt (c0X X u (Y.FN u) * c0X X u' (Y.FN u')))⁻¹ := by
      rw [normalizing_constant_eq_of_dimTie hF hd, normalizing_constant_eq_of_dimTie hF hd', Real.sqrt_eq_rpow,
        ← Real.rpow_neg (mul_nonneg (weightConst_nonneg hF u) (weightConst_nonneg hF u'))]
    change ⟪T, (((Formalism.MainNotions.S.c0 (sOf hF) u * Formalism.MainNotions.S.c0 (sOf hF) u') ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        (ContinuousLinearMap.adjoint (puC hF u)) (puC hF u' T')⟫_ℂ = _
    rw [inner_smul_right, ContinuousLinearMap.adjoint_inner_right, hc]
    rfl
  exact ContinuousLinearMap.ext fun T' => ext_inner_left ℂ fun T => aux T T'

include hF in
theorem summable_op_fib {u u' : D.what₂.Word} (hA : (Y.tO u u').AbsConv) :
    Summable fun s : TT Y u u' => ‖aT hF u u' s‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun s => ?_)
    (hA.1.mul_left (Module.finrank ℂ (CM (Y.cs u')) : ℝ))
  exact (norm_tr_le _ _ _).trans (opNorm_le_hs _)

theorem kTie (u u' : D.what₂.Word) : KTie hF u u' := by
  intro hd hd' hE hA
  obtain ⟨K, hsum, hK⟩ := hE
  have hKm := kmat_eq hF hd hd' K hK
  have h1 : HasSum (fun s : TT Y u u' => aT hF u u' s) (tr (hF.shBij u) (hF.shBij u') K) :=
    hsum.map (trAdd (hF.shBij u) (hF.shBij u')) (continuous_trAdd _ _)
  let e := Equiv.sigmaFiberEquiv (fun s : TT Y u u' => s.toTerm)
  refine ⟨?_, ?_⟩
  · change HasSum (fun t => aR hF u u' t) (Kmat (sOf hF) u u')
    rw [hKm]
    have h2 := (e.hasSum_iff (f := fun s : TT Y u u' => aT hF u u' s)).2 h1
    refine h2.sigma fun t => ?_
    letI : Fintype {x : TT Y u u' // x.toTerm = t} := hF.fibFT t
    unfold aR
    exact hasSum_fintype _
  · change Summable fun t => ‖aR hF u u' t‖
    have hs := (e.summable_iff (f := fun s : TT Y u u' => ‖aT hF u u' s‖)).2 (summable_op_fib hF hA)
    have hs2 := (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).1 hs
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun t => ?_) hs2.2
    letI : Fintype {x : TT Y u u' // x.toTerm = t} := hF.fibFT t
    rw [tsum_fintype]
    unfold aR
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    rfl

theorem normTie (u u' : D.what₂.Word) : NormTie hF u u' := by
  intro hd hd' hE hA hId hK2
  obtain ⟨K, hsum, hK⟩ := hE
  have hKm := kmat_eq hF hd hd' K hK
  have hs : ∀ S : Set (TT Y u u'), Summable (S.indicator (Y.tO u u').op) := fun S =>
    Summable.of_norm_bounded hA.1 fun t => by
      by_cases h : t ∈ S
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, norm_zero]; exact norm_nonneg _
  rw [Formalism.L2.SG.PackageTie.K0_eq_K_of_degSet_eq_zero hs hId hK2]
  have hKK : (Y.tO u u').K = Formalism.L2.SG.PackageTie.hsEmb K :=
    (hsum.map (Formalism.L2.SG.PackageTie.hsEmb (Wq := CM (Y.cs u')) (Wp := CM (Y.cs u)))
      (LinearMap.continuous_of_finiteDimensional _)).tsum_eq
  rw [hKK, Formalism.L2.SG.PackageTie.norm_hsEmb_sq, hKm]
  have := finiteDimensional_colT (hF.shBij u)
  have := finiteDimensional_colT (hF.shBij u')
  have := FiniteDimensional.complete ℂ (ColT (hF.shInj u))
  exact (hsNormSq_of_semi (tr (hF.shBij u) (hF.shBij u') K) K (shTAdd (hF.shInj u'))
    (fun c x => shT_smul _ c x) (fun x y => (inner_colT _ y x).symm) (hF.shBij u').2
    (shT (hF.shInj u)) norm_shT (fun x => (shT_tr _ _ K x).symm))

end Ties

section Dim

variable {D : D7} (X : HidaSetting D)

theorem finrank_loc (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    (Module.finrank ℂ (X.Vloc u v) : ℝ) =
      ((dimPiU D.R.k (fun i => ((D.hcW u (X.pl v)).u i : ℝ)) : ℕ) : ℝ) := by
  have hanti : StrictAnti (fun i => ((D.hcW u (X.pl v)).u i : ℝ)) :=
    (Formalism.MainNotions.S.Inh.obj_isHCParam_u D.R (D.hcW u (X.pl v))).1
  have h1 := ReciprocityTheory.ChartRestriction.DS.HW.weyl_dimension_formula_unitary D.R.k _ (X.Vloc u v) (X.piLoc u v) hanti (X.piLoc_type u v)
  have hne : {d | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (π : Matrix (Fin D.R.k) (Fin D.R.k) ℂ → (H →L[ℂ] H)),
        IsHCTypeU D.R.k (fun i => ((D.hcW u (X.pl v)).u i : ℝ)) π ∧ Module.finrank ℂ H = d}.Nonempty :=
    ⟨_, X.Vloc u v, inferInstance, inferInstance, X.piLoc u v, X.piLoc_type u v, rfl⟩
  obtain ⟨H, i1, i2, π, hπ, hd⟩ := Nat.sInf_mem hne
  unfold dimPiU
  rw [← hd, h1]
  exact (ReciprocityTheory.ChartRestriction.DS.HW.weyl_dimension_formula_unitary D.R.k _ H π hanti hπ).symm

theorem tens_mem_span (u : D.what₂.Word) (x : ∀ v, X.Vloc u v) :
    X.tensU u x ∈ Submodule.span ℂ (Set.range fun i : (∀ v, Fin (Module.finrank ℂ (X.Vloc u v))) =>
      X.tensU u (fun v => stdOrthonormalBasis ℂ (X.Vloc u v) (i v))) := by
  set b := fun v => stdOrthonormalBasis ℂ (X.Vloc u v)
  set e := fun i : (∀ v, Fin (Module.finrank ℂ (X.Vloc u v))) => X.tensU u (fun v => b v (i v)) with he_def
  have he : Orthonormal ℂ e := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [e, X.tensU_inner]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact Finset.prod_eq_one fun v _ => by rw [orthonormal_iff_ite.1 (b v).orthonormal, if_pos rfl]
    · rw [if_neg hij]
      obtain ⟨v, hv⟩ := Function.ne_iff.1 hij
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by rw [orthonormal_iff_ite.1 (b v).orthonormal, if_neg hv])
  have hc : ∀ i, ‖⟪e i, X.tensU u x⟫_ℂ‖ ^ 2 = ∏ v, ‖⟪b v (i v), x v⟫_ℂ‖ ^ 2 := by
    intro i
    rw [he_def]
    simp only [X.tensU_inner, norm_prod, Finset.prod_pow]
  have hy : ‖X.tensU u x‖ ^ 2 = ∏ v, ‖x v‖ ^ 2 := by
    have h := congrArg norm (X.tensU_inner u x x)
    rw [norm_prod] at h
    simp only [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at h
    exact h
  set y := X.tensU u x
  set c := fun i => ⟪e i, y⟫_ℂ
  set s := ∑ i, c i • e i
  have hss : ⟪s, s⟫_ℂ = ∑ i, conj (c i) * c i := he.inner_sum c c Finset.univ
  have hsy : ⟪s, y⟫_ℂ = ∑ i, conj (c i) * c i := by
    simp only [s, sum_inner, inner_smul_left, c]
  have hnorm_s : ‖s‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hss, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hnorm_y : ‖y‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    simp only [c, hc]
    rw [hy, ← Fintype.prod_sum (fun v j => ‖⟪b v j, x v⟫_ℂ‖ ^ 2)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← (b v).repr.norm_map (x v), EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [OrthonormalBasis.repr_apply_apply]
  have horth : ⟪s, y - s⟫_ℂ = 0 := by rw [inner_sub_right, hsy, hss, sub_self]
  have hpy : ‖y‖ ^ 2 = ‖s‖ ^ 2 + ‖y - s‖ ^ 2 := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero s (y - s) horth
    rw [sq, sq, sq]
    rwa [add_sub_cancel] at this
  have h0 : ‖y - s‖ = 0 := by
    have : ‖y - s‖ ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  have hys : y = s := sub_eq_zero.1 (norm_eq_zero.1 h0)
  rw [hys]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem finrank_Vpi (u : D.what₂.Word) :
    Module.finrank ℂ (X.Vpi u) = ∏ v, Module.finrank ℂ (X.Vloc u v) := by
  set b := fun v => stdOrthonormalBasis ℂ (X.Vloc u v)
  set e := fun i : (∀ v, Fin (Module.finrank ℂ (X.Vloc u v))) => X.tensU u (fun v => b v (i v))
  have he : Orthonormal ℂ e := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [e, X.tensU_inner]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact Finset.prod_eq_one fun v _ => by rw [orthonormal_iff_ite.1 (b v).orthonormal, if_pos rfl]
    · rw [if_neg hij]
      obtain ⟨v, hv⟩ := Function.ne_iff.1 hij
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by rw [orthonormal_iff_ite.1 (b v).orthonormal, if_neg hv])
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range e) := by
    rw [← X.tensU_span u, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact tens_mem_span X u x
  rw [Module.finrank_eq_card_basis (Module.Basis.mk he.linearIndependent htop), Fintype.card_pi]
  simp only [Fintype.card_fin]

theorem dimTie (u : D.what₂.Word) : DimTie (X := X) u := by
  unfold DimTie dimPi
  rw [finrank_Vpi, Nat.cast_prod]
  exact Fintype.prod_equiv X.pl _ _ fun v => finrank_loc X u v

end Dim

section FinX

open Formalism.L2.SG.Full

variable {D : D7} {X : HidaSetting D} (Y : Full X)

theorem sharp_bij (u : D.what₂.Word) (hCL : ColsLink X u Y.hK) :
    Function.Bijective (sharp Y.hK (Y.cs u)) := by
  have hst : Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u Y.hK) :=
    Formalism.L2.SG.ColsDim.stabTriv_mono (iotaF X u) hCL.1 hCL.2.1
  let cls : (Y.cs u).Cl → Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u Y.hK) :=
    fun ρ => DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) ((Y.cs u).h ρ)
  have hcls : Function.Bijective cls := by
    refine ⟨fun ρ ρ' h => ?_, fun c => ?_⟩
    · obtain ⟨a, ⟨γ, rfl⟩, κ, hκ, hab⟩ := (DoubleCoset.eq _ _ _ _).1 h
      obtain ⟨ρ0, _, huniq⟩ := Y.colReps u ((Y.cs u).h ρ')
      have h1 := huniq ρ ⟨γ, ⟨κ, hκ⟩, hab⟩
      have h2 := huniq ρ' ⟨1, 1, by simp⟩
      exact h1.trans h2.symm
    · induction c using Quotient.inductionOn' with
      | h g =>
        obtain ⟨ρ, ⟨γ, κ, hg⟩, _⟩ := Y.colReps u g
        refine ⟨ρ, ?_⟩
        show DoubleCoset.mk _ _ _ = DoubleCoset.mk _ _ g
        rw [DoubleCoset.eq]
        exact ⟨iotaF X u γ, ⟨γ, rfl⟩, κ, κ.2, hg⟩
  let ec := Equiv.ofBijective cls hcls
  let s : Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u Y.hK) → Hfin X u := fun c => (Y.cs u).h (ec.symm c)
  have hs : ∀ c, DoubleCoset.mk (iotaF X u).range (Ku X u Y.hK) (s c) = c := fun c => ec.apply_symm_apply c
  obtain ⟨e, he⟩ := Formalism.L2.SG.ColsDim.columns_decomposition (Gam X u) (Hinf X u) (Hfin X u) ℂ (X.Vpi u) (iotaI X u)
    (iotaF X u) (Ku X u Y.hK) (psiK X u Y.hK) (piRep X u) s hs hst
  have key : ∀ T ρ, (sharp Y.hK (Y.cs u) T) ρ =
      (InnerProductSpace.toDual ℂ (X.Vpi u)).symm (LinearMap.toContinuousLinearMap (e T (cls ρ))) := by
    intro T ρ
    have hsρ : s (cls ρ) = (Y.cs u).h ρ := by
      show (Y.cs u).h (ec.symm (ec ρ)) = _
      rw [ec.symm_apply_apply]
    show (InnerProductSpace.toDual ℂ (X.Vpi u)).symm
      (LinearMap.toContinuousLinearMap ((LinearMap.proj ((1 : Hinf X u), (Y.cs u).h ρ)).comp T.1)) = _
    congr 2
    refine LinearMap.ext fun ξ => ?_
    refine Eq.trans ?_ (he T (cls ρ) ξ).symm
    rw [hsρ]
    rfl
  refine ⟨fun T T' h => ?_, fun x => ?_⟩
  · apply e.injective
    funext c
    obtain ⟨ρ, rfl⟩ := hcls.2 c
    have h1 : (sharp Y.hK (Y.cs u) T) ρ = (sharp Y.hK (Y.cs u) T') ρ := by rw [h]
    rw [key T ρ, key T' ρ] at h1
    exact LinearMap.toContinuousLinearMap.injective ((InnerProductSpace.toDual ℂ (X.Vpi u)).symm.injective h1)
  · let d : Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u Y.hK) → Module.Dual ℂ (X.Vpi u) :=
      fun c => LinearMap.toContinuousLinearMap.symm (InnerProductSpace.toDual ℂ (X.Vpi u) (x (ec.symm c)))
    refine ⟨e.symm d, ?_⟩
    ext ρ
    refine (key (e.symm d) ρ).trans ?_
    rw [e.apply_symm_apply]
    show (InnerProductSpace.toDual ℂ (X.Vpi u)).symm (LinearMap.toContinuousLinearMap
      (LinearMap.toContinuousLinearMap.symm (InnerProductSpace.toDual ℂ (X.Vpi u) (x (ec.symm (ec ρ)))))) = x ρ
    rw [LinearEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply, ec.symm_apply_apply]

theorem finX_of (hCL : ∀ u, ColsLink X u Y.hK) (hin : ∀ u, InHH X u Y.hK) (hfin : FiniteDimensional ℂ (HHX X))
    (hfib : ∀ u u' (t : RT Y u u'), Finite (fib Y t))
    (hpi : ∀ u u' (s₁ s₂ s₁' s₂' : TT Y u u'), s₁.toTerm = s₁'.toTerm → s₂.toTerm = s₂'.toTerm →
      rowOf Y.TR (Y.cs u) (Y.cs u') s₁ = rowOf Y.TR (Y.cs u) (Y.cs u') s₂ →
      rowOf Y.TR (Y.cs u) (Y.cs u') s₁' = rowOf Y.TR (Y.cs u) (Y.cs u') s₂' →
      s0T s₁ s₂ = s0T s₁' s₂' ∧ (liftScalar s₁ s₂ ↔ liftScalar s₁' s₂')) (hG : ∀ u u' (t : RT Y u u'), t.G ∈ D.host.F)
    (hvol : VolPosC) : FinX Y where
  shInj u := (sharp_bij Y u (hCL u)).1
  shSurj u := (sharp_bij Y u (hCL u)).2
  inHH := hin
  puLin u := Formalism.L2.SG.PoincareInHH.Cut.puLinear_holds X u Y.hK (Y.Dt u)
  finHH := hfin
  fibFin := hfib
  pairIndep := hpi
  Greal := hG
  cdEx n ε := cd_haar_scaling D.cd n ε
  volPos u := hvol D X Y u (Formalism.L2.SG.Closed.level_subgroup_properties X)

end FinX

end Formalism.L2.SG.Pf
