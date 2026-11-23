import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingMapsIntoGoodExtension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsOfConjugatesMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysIffOfTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PrimeTypeRows
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationOverSumChar
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.CrystallineCyclotomic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiCrysOfConstituent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndepOnOfInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaxUnramifiedOfCrystallineRatio
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepresentationHomFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwiStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingsRegularPhiSurjectiveFilStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TateDualCrys

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

section Local

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem fracInv_of_tied (T : LocTied l P AI) (K : FinExt l) : FracInv (P.PD K) := by
  intro x y hx h
  refine GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K y x hx fun g hg => ?_
  have h1 := h ⟨g, hg⟩
  rw [P.PD_actB, P.PD_actB] at h1
  rw [mul_comm, h1, mul_comm]

theorem lineUnit_of_tied (T : LocTied l P AI) (K : FinExt l) : LineUnit (P.PD K) := by
  intro b hb h
  refine (GlobalTheory.T.periodRings_regular_phi_surjective_fil l P AI T).1 K b hb fun g hg => ?_
  obtain ⟨x, hx⟩ := h ⟨g, hg⟩
  exact ⟨x, by rw [← P.PD_actB K ⟨g, hg⟩, hx, Algebra.smul_def]⟩

theorem matRep_apply {L Γ : Type} [CommRing L] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) L)
    (g : Γ) (x : Fin k → L) : matRep M g x = (M g).mulVec x := rfl

theorem dot_dual {L Γ : Type} [CommRing L] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) L)
    (g : Γ) (x y : Fin k → L) : (M g).mulVec x ⬝ᵥ (M g⁻¹).transpose.mulVec y = x ⬝ᵥ y := by
  rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]

theorem tateDual (T : LocTied l P AI) (K LL : FinExt l)
    (hs : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1) {k : ℕ}
    (M M' : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)
    (hM : ∀ g, M' g = ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) • (M g⁻¹).transpose)
    (hc : IsCrys (P.PD K) (matRep M)) :
    IsCrys (P.PD K) (matRep M') ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ),
      multV (P.PD K) (matRep M') τ a = multV (P.PD K) (matRep M) τ (-a - 1) := by
  have := LL.2
  have : IsDomain P.R.B := isDomain_of_tied T K
  have hf := fracInv_of_tied T K
  have hu := lineUnit_of_tied T K
  constructor
  · have h1 : IsCrys (P.PD K) (matRep (dualM M)) := by
      refine subCrys (P.PD K) ↥LL.1 hf _ _ _ _ (dotProductEquiv ↥LL.1 (Fin k)).toLinearMap ?_
        (dotProductEquiv ↥LL.1 (Fin k)).injective (dualCrys (P.PD K) ↥LL.1 hf hu _ _ hc)
      intro g x
      refine LinearMap.ext fun y => ?_
      change (M g⁻¹).transpose.mulVec x ⬝ᵥ y = x ⬝ᵥ (M g⁻¹).mulVec y
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
    refine GlobalTheory.TwistCrys.isCrys_twist (P.PD K) (tensorCrys (P.PD K) ↥LL.1 hf hu)
      (quotCrys (P.PD K) ↥LL.1 hf hu) (matRep (dualM M)) (matRep M')
      (WeaklyAdmissibleFiltrations.charRep (cycLL (P.PD K) ↥LL.1 ^ (1 : ℤ))) (fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1))
      LinearMap.id 1 rfl (fun g x => ?_) (fun g x => ?_)
      (GlobalTheory.CycPow.cyc_zpow_crys_dR_jump l P AI T K LL 1).1 h1
    · rw [zpow_one]; rfl
    · rw [matRep_apply, hM, Matrix.smul_mulVec]; rfl
  · intro τ a
    have h := (GlobalTheory.DRDual.twisted_dual_deRham l P AI T K LL _ (matRep M) _ (matRep M')
      (dotProductEquiv ↥LL.1 (Fin k)).toLinearMap 1 (dotProductEquiv ↥LL.1 (Fin k)).bijective
      (fun g x y => by
        change (M g).mulVec x ⬝ᵥ (M' g).mulVec y = _ * (x ⬝ᵥ y)
        rw [hM, Matrix.smul_mulVec, dotProduct_smul, dot_dual, zpow_one, smul_eq_mul])
      (GlobalTheory.T.isDeRham_of_isCrystalline_span l P AI T K LL _ _ hc).1).2 τ (-a - 1) hs
    rwa [show -(-a - 1) - 1 = a by ring] at h

def sumRep {L Γ : Type} [CommRing L] [Group Γ] {m k : ℕ} (M : Fin m → (Γ →* Matrix (Fin k) (Fin k) L)) :
    Representation L Γ (Fin m → Fin k → L) where
  toFun g := LinearMap.pi fun a => matRep (M a) g ∘ₗ LinearMap.proj a
  map_one' := by
    refine LinearMap.ext fun v => funext fun a => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun v => funext fun a => ?_
    simp

theorem isCrys_of_isSubOfSums (T : LocTied l P AI) (K LL : FinExt l) {ι : Type} {k : ℕ}
    (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (hc : ∀ x, IsCrys (P.PD K) (matRep (Ms x)))
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
    (h : IsSubOfSums ρ (fun x g => Ms x g)) : IsCrys (P.PD K) ρ := by
  have := LL.2
  have : IsDomain P.R.B := isDomain_of_tied T K
  have hf := fracInv_of_tied T K
  have hu := lineUnit_of_tied T K
  obtain ⟨m, xs, j, hj, he⟩ := h
  refine subCrys (P.PD K) ↥LL.1 hf _ (sumRep fun a => Ms (xs a)) _ ρ j (fun g v => he g v) hj ?_
  rw [isCrys_iff_span (P.PD K) hf hu]
  refine eq_top_of_tmul _ fun b v => ?_
  rw [← Finset.univ_sum_single v, TensorProduct.tmul_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  refine tmul_mem_span (P.PD K) (ρ := matRep (Ms (xs a)))
    (f := LinearMap.single ↥LL.1 (fun _ : Fin m => Fin k → ↥LL.1) a) (fun g x => ?_)
    ((isCrys_iff_span (P.PD K) hf hu _).1 (hc _)) b (v a)
  funext a'
  change Pi.single (M := fun _ => Fin k → ↥LL.1) a (matRep (Ms (xs a)) g x) a' =
    matRep (Ms (xs a')) g (Pi.single (M := fun _ => Fin k → ↥LL.1) a x a')
  by_cases ha : a' = a
  · subst ha; simp
  · simp [ha]

end Local

theorem loc_rDuO (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (g : Br.G D.nbr i w hw) :
    mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)) g =
      ((cycLL (Br.PD D.loc D.nbr i w hw) ↥LL'.1 g : (↥LL'.1)ˣ) : ↥LL'.1) •
        (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)) g⁻¹).transpose := by
  have h1 : ((cycLL (Br.PD D.loc D.nbr i w hw) ↥LL'.1 g : (↥LL'.1)ˣ) : ↥LL'.1) =
      IntermediateField.inclusion h
        ((Br.locChi D.nbr i w hw (epsU D.nd i) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) := by
    rw [GlobalTheory.CycBridge.locChi_epsU]
    exact ((IntermediateField.inclusion h).commutes _).symm
  rw [h1]
  let F : D.nd.O i →+* ↥LL'.1 := (IntermediateField.inclusion h).toRingHom.comp
    ((algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))).comp (D.nbr i w hw).eO.toRingHom)
  let γ : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.ι (D.nbr i w hw))
  ext a b
  congr 1
  change F (((chiU D.nd i 1 (γ g) * epsU D.nd i (γ g) : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (γ g)⁻¹ b a) =
    F ((epsU D.nd i (γ g) : (D.nd.O i)ˣ) : D.nd.O i) *
      F ((((chiU D.nd i 1 (γ g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (γ g⁻¹) b a)
  rw [map_inv γ, map_inv (chiU D.nd i 1), inv_inv, ← map_mul, Units.val_mul]
  congr 1
  ring

theorem crystalline_and_jumps : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocTied (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) → ∀ (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x))))) → (∀ (V : Type) [AddCommGroup V] [Module ↥LL'.1 V] [Module ℚ_[D.nd.l i] V] [IsScalarTower ℚ_[D.nd.l i] ↥LL'.1 V] [FiniteDimensional ↥LL'.1 V] (ρ₁ : Representation ↥LL'.1 (Br.G D.nbr i w hw) V), IsSubOfSums ρ₁ (fun x g => mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)) g) → IsCrys (Br.PD D.loc D.nbr i w hw) ρ₁ ∧ ∀ (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (a : ℤ), IsJumpV (Br.PD D.loc D.nbr i w hw) ρ₁ τ' a → ∃ x, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) τ' (-a - 1)) ∧ ∀ π, (∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e) → (∀ (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' a ≤ 1) → IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)))) ∧ ∀ (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (a : ℤ), ((IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ∧ ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ))) → multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)))) τ' a = 1) ∧ (¬ (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ∧ ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ))) → multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)))) τ' a = 0) := by
  intro D i w hw T LL' h r ρ hc
  have hs : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := by
    have := (D.nbr i w hw).Kw.2
    have := LL'.2
    have h1 := (GlobalTheory.splits_of_conjugates_mem _ (D.nbr i w hw).Kw LL' (fun τ x => h
      ((D.nbr i w hw).LL_split τ x)) inferInstance).2
    rw [Nat.card_eq_fintype_card, h1]
  have hd := fun x => tateDual T (D.nbr i w hw).Kw LL' hs _ _ (loc_rDuO D i w hw LL' h r x) (hc x)
  have hj := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero _ _ _ T (D.nbr i w hw).Kw LL'
  refine ⟨fun V _ _ _ _ _ ρ₁ hsub => ⟨isCrys_of_isSubOfSums T (D.nbr i w hw).Kw LL' _
    (fun x => (hd x).1) V ρ₁ hsub, fun τ' a ha => ?_⟩, fun π hπ hle => ?_⟩
  · refine GlobalTheory.SubSumJumps.jumpsInV_of_isSubOfSums (Br.PD D.loc D.nbr i w hw) ρ₁ _ τ'
      {a | ∃ x, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
        (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) τ' (-a - 1)} hsub (fun x b hb => ⟨x, ?_⟩) a ha
    refine (hj _ _ τ' _).2.2.2 ?_
    rw [← (hd x).2]
    exact (hj _ _ τ' _).2.2.1 hb
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.crystalline_summand_and_dual_from_inverse_character_twist D i w hw T LL' h r ρ π hπ
    obtain ⟨-, -, h3⟩ := h2 (GlobalTheory.T.isDeRham_of_isCrystalline_span _ _ _ T (D.nbr i w hw).Kw LL' _ _ (hc π)).1
    refine ⟨(h1 (hc π)).2, fun τ' a => ?_⟩
    have e1 := (h3 τ' a).2
    have e2 := (h3 τ' (-a - 1)).1
    have e3 := hle τ' (-a - 1)
    have e4 : 0 ≤ multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
      (Br.loc D.nbr i w hw (WpO D.nd i ρ π)))) τ' (-a - 1) := (hj _ _ τ' _).2.1
    have e5 : IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
        (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ↔
      multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
        (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ≠ 0 := (hj _ _ τ' _).2.2
    rw [e5, e1]
    split_ifs at e2 with hh <;> omega

end GlobalTheory.TateDualCrys
