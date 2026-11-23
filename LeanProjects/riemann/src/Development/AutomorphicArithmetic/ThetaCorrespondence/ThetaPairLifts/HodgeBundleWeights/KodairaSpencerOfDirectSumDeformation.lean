import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFlagHodgeIndexVanishing
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsKodairaSpencerFlagTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFlagHodgeIndexVanishingStatement

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.CatCoh GlobalTheory.Published GlobalTheory.Published.AbelianDeRham DividedPowers
variable {R : Type} [CommRing R]
end GlobalTheory.DeRham
namespace GlobalTheory.FlagTan
open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published ReciprocityTheory.ChartRestriction.G.PullbackSections
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]
theorem kodaira_spencer_direct_sum : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K]
    (y : FrPt Xo c K) (ι : Type) [Fintype ι] [DecidableEq ι] (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X),
    1 ≤ Dw.p + Dw.q → X ≫ Xo.s = sOf c _ → spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x →
    ∀ N : ι → HIx Dw (psiSet H) → K,
      (∀ k, IsKS (psiSet H) y (spMap (dir c (Pi.single k (1 : K))).toRingHom ≫ X) (N k)) →
      ∀ M : ι → K, IsKS (psiSet H) y (spMap (dir c M).toRingHom ≫ X) (∑ k, M k • N k) := by
  intro Pr E _ _ _ H Dw l Xo c K _ _ y ι _ _ X hpq hXs hXy N hN M
  have P := Pr.p5
  have e₀ : ∀ m : ι → K, DeRham.epsRed K ≫ spMap (dir c m).toRingHom =
      spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom := fun m => by
    rw [← Cris.spMap_comp]
    exact congrArg spMap (RingHom.ext fun z => fst_dir (c := c) m z)
  have tan : IsTanX y (spMap (dir c M).toRingHom ≫ X) := by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, hXs]
      unfold sOf
      rw [← Cris.spMap_comp]
      exact congrArg spMap (RingHom.ext fun r => (dir c M).commutes _)
    · rw [← Category.assoc, ← hXy]
      exact congrArg (· ≫ X) (e₀ M)
  obtain ⟨M₀, A, _, A', _, π, π', i, hi, ψ, ub, hb, hπ, hπ', hiπ, hpol, hu, hl, what₂⟩ :=
    _root_.GlobalTheory.T.exists_kodaira_spencer_flag_tangent Pr E H Dw l Xo c K y _ hpq tan
  obtain ⟨C, _, πC, hC⟩ := exists_isGrpPullback Xo.univ.t.G X
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have aC := PolPull.isAbelianScheme_of_isGrpPullback hU hC
  have gC := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hC.1 hg
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hL := (P.2.1 K A _ hA gA).1
  obtain ⟨φ, hφ, eφ⟩ : ∃ φ : A'.left ⟶ C.left, IsGrpPullback A' C (spMap (dir c M).toRingHom) φ ∧ φ ≫ πC = π' := by
    have w : π' ≫ Xo.univ.t.G.hom = (A'.hom ≫ spMap (dir c M).toRingHom) ≫ X :=
      hπ'.1.w.trans (Category.assoc _ _ _).symm
    exact ⟨hC.1.lift _ _ w, hC.cancel (hπ'.congr rfl (hC.1.lift_fst _ _ w).symm) (hC.1.lift_snd _ _ w),
      hC.1.lift_fst _ _ w⟩
  have h₀ := (hi.comp hφ).congr (e₀ M) rfl
  refine ⟨A, _, A', _, π, π', i, hi, ψ, ub, hb, hπ, hπ', hiπ, hpol, hu, hl, fun τ a => ?_⟩
  obtain ⟨-, -, f, hf, hd, -⟩ := what₂ τ a
  obtain ⟨gs, hgs⟩ := exists_isFilLift_dir P aC gC h₀ hf
  have row : ∀ k, ∃ w, IsLieComb (fun b => N k ⟨τ, a, b⟩) (ub τ.1) w ∧ DeRham.IsLieImage (gs k) w := fun k => by
    obtain ⟨B, _, χ, hχ⟩ := exists_isGrpPullback C (spMap (dir c (Pi.single k (1 : K))).toRingHom)
    have w : (i ≫ φ) ≫ C.hom = (A.hom ≫ DeRham.epsRed K) ≫ spMap (dir c (Pi.single k (1 : K))).toRingHom := by
      rw [Category.assoc _ (DeRham.epsRed K), e₀]
      exact h₀.1.w
    have sq : hχ.1.lift _ _ w ≫ χ = i ≫ φ := hχ.1.lift_fst _ _ _
    have hj : IsGrpPullback A B (DeRham.epsRed K) (hχ.1.lift _ _ w) :=
      hχ.cancel (h₀.congr (e₀ _).symm sq.symm) (hχ.1.lift_snd _ _ _)
    obtain ⟨v, hc, hv⟩ := (hN k).row P hj hπ (hχ.comp hC)
      (by rw [← Category.assoc, sq, Category.assoc, eφ, hiπ]) hpol hu hl τ a hf hd
    obtain ⟨v', hv', -⟩ := hL.1 (gs k)
    have fl := hgs (Pi.single k 1) B χ _ hj hχ sq
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at fl
    obtain rfl := IsKSValue.unique P (PolPull.isAbelianScheme_of_isGrpPullback aC hχ)
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hχ.1 gC) hv ⟨_, fl, hv'⟩
    exact ⟨_, hc, hv'⟩
  choose w hwc hwl using row
  let e := (Fintype.equivFin ι).symm
  refine ⟨lieComb (fun q => M (e q)) (fun q => w (e q)), ?_, f, hf, hd, _, ?_,
    isLieImage_lieComb _ (f := fun q => gs (e q)) fun q => hwl _⟩
  · obtain ⟨V, _, _, v, -, -, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo K y.x
    choose n hn using fun σ k => (htan _).1 (y.tan σ k)
    have key : ∀ {m : ℕ} (cf : Fin m → K) (u : Fin m → (epsR K ⟶ A)) (b : Fin m → V) (w : epsR K ⟶ A),
        (∀ j, (u j).left ≫ π = v (b j)) → (IsLieComb cf u w ↔ w.left ≫ π = v (∑ j, cf j • b j)) :=
      fun cf u b w hu => by rw [isLieComb_iff_isCombAt hπ, funext hu, hcomb]
    have hun : ∀ j, (ub τ.1 j).left ≫ π = v (n τ.1 j) := fun j => (hu _ j).trans (hn _ j).symm
    rw [key _ _ _ _ hun, (key _ _ _ _ fun q => (key _ _ _ _ hun).1 (hwc (e q))).1 (isLieComb_lieComb _ _),
      e.sum_comp fun k => M k • ∑ j, N k ⟨τ, a, j⟩ • n τ.1 j]
    congr 1
    simp only [Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul]
    exact Finset.sum_comm
  · rw [e.sum_comp fun k => M k • gs k]
    exact hgs M A' φ i hi hφ rfl
end GlobalTheory.FlagTan
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_spencer_of_direct_sum_deformation : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (ι : Type) [Fintype ι] [DecidableEq ι] (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → X ≫ Xo.s = sOf c _ → spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x → ∀ N : ι → GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, (∀ k, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c (Pi.single k (1 : K))).toRingHom ≫ X) (N k)) → ∀ M : ι → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) (∑ k, M k • N k) := by
  first | exact @_root_.GlobalTheory.FlagTan.kodaira_spencer_direct_sum | exact _root_.GlobalTheory.FlagTan.kodaira_spencer_direct_sum | (intros; apply _root_.GlobalTheory.FlagTan.kodaira_spencer_direct_sum <;> assumption)
end
