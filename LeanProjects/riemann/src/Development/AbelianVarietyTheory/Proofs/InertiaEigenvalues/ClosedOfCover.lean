import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrobeniusPeriod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingCoreCrystallineDeRhamInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOfCrystallineBreuilKisinFrameStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfBreuilKisinFrameIsDeRhamStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdaptedBasisThetaGaloisFixedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisElemCyclotomicPeriodNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistableBoundedJumpsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisDeRhamLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisAtEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHodgeTateIffDiagonalAdaptedBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateOperatorPowEqSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetEqOfPowerSumsZpowEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaConjBoundedCompatibleBreuilKisinFramesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFrameLimitLatticeBreuilKisinTowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LayerDdRBoundsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamCrystallineOfLatticeReadsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableLatticeInMatrixAlgebraLayerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePowEqAlongLatticeTowerCoverStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CovClose

variable {l : ℕ} [Fact l.Prime]

theorem exists_gal_inv {K : FinExt l} (τ' : ↥K.1 →ₐ[ℚ_[l]] Om l) : ∃ σ : GQ l, ∀ x : ↥K.1, σ (τ' x) = (x : Om l) := by
  let φ : Om l →ₐ[ℚ_[l]] Om l := τ'.liftNormal (Om l)
  have hb : Function.Bijective φ := Algebra.IsAlgebraic.algHom_bijective φ
  let e : Om l ≃ₐ[ℚ_[l]] Om l := AlgEquiv.ofBijective φ hb
  refine ⟨e.symm, fun x => ?_⟩
  have h1 : φ (algebraMap ↥K.1 (Om l) x) = τ' x := AlgHom.liftNormal_commutes τ' (Om l) x
  have h2 : e (x : Om l) = τ' x := h1
  rw [← h2]
  exact e.symm_apply_apply _

def modelOf {Γ : Type} [Group Γ] {a : ℕ} (ρ₁ : Γ →* GL (Fin a) (Om l)) (L : FinExt l)
    (h : ∀ g i j, (ρ₁ g).val i j ∈ L.1) : Γ →* GL (Fin a) ↥L.1 :=
  MonoidHom.toHomUnits
    { toFun := fun g => Matrix.of fun i j => (⟨(ρ₁ g).val i j, h g i j⟩ : ↥L.1)
      map_one' := by
        ext i j
        simp only [Matrix.of_apply, Units.val_one, Matrix.one_apply, map_one]
        split_ifs <;> simp
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply, Units.val_mul] }

theorem modelOf_apply {Γ : Type} [Group Γ] {a : ℕ} (ρ₁ : Γ →* GL (Fin a) (Om l)) (L : FinExt l)
    (h : ∀ g i j, (ρ₁ g).val i j ∈ L.1) (g : Γ) (i j : Fin a) :
    (((modelOf ρ₁ L h g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j := by
  simp [modelOf]

def repOf {Γ : Type} [Group Γ] {a : ℕ} {L : FinExt l} (r : Γ →* GL (Fin a) ↥L.1) :
    Representation ↥L.1 Γ (Fin a → ↥L.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥L.1 ≃ₐ[↥L.1] _) : _ →* _).comp ((Units.coeHom _).comp r)

theorem repOf_apply {Γ : Type} [Group Γ] {a : ℕ} {L : FinExt l} (r : Γ →* GL (Fin a) ↥L.1) (g : Γ) (v : Fin a → ↥L.1) :
    repOf r g v = (r g).val *ᵥ v := by
  simp [repOf, Matrix.toLinAlgEquiv'_apply]

theorem isSst_resQ' (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsSst P (GlobalTheory.PstCoeff.resQ ρ) := by
  have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
    ext x
    simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
  have e : Module.finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) =
      Module.finrank ℚ_[l] LL * Module.finrank LL ↥(Dst P ρ) := by
    rw [hD, Module.finrank_mul_finrank]
    rfl
  rw [IsSst, e, h, ← Module.finrank_mul_finrank ℚ_[l] LL V]
  ring

theorem isDR_of_isSst (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) {K L : FinExt l} {a : ℕ}
    (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)) (h : IsSst P R) : Formalism.MainNotions.N.IsDR (P.PD K) R := by
  haveI := L.2
  haveI : FiniteDimensional ℚ_[l] (Fin a → ↥L.1) := Module.Finite.trans ↥L.1 _
  exact (GlobalTheory.PstCoeff.isDR_resQ_iff P R).mp
    (GlobalTheory.sst_isDR l P AI T K _ (GlobalTheory.PstCoeff.resQ R) (isSst_resQ' P R h))

theorem conj_diag {k : Type} [Field k] {a : ℕ} (W : Matrix (Fin a) (Fin a) k) (hW : IsUnit W) (d : Fin a → k) :
    (W * diagonal d * W⁻¹) * W = W * diagonal d ∧
      ∀ n : ℕ, ((W * diagonal d * W⁻¹) ^ n).trace = ∑ i, d i ^ n := by
  have hdet : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det W).mp hW
  refine ⟨by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul W hdet, Matrix.mul_one], fun n => ?_⟩
  have e : W⁻¹ = ((hW.unit⁻¹ : (Matrix (Fin a) (Fin a) k)ˣ) : Matrix (Fin a) (Fin a) k) := by
    rw [Matrix.coe_units_inv, IsUnit.unit_spec]
  have e2 : W * diagonal d * W⁻¹ = ((hW.unit : (Matrix (Fin a) (Fin a) k)ˣ) : Matrix (Fin a) (Fin a) k) * diagonal d *
      ((hW.unit⁻¹ : (Matrix (Fin a) (Fin a) k)ˣ) : Matrix (Fin a) (Fin a) k) := by
    rw [← e, IsUnit.unit_spec]
  rw [e2, Units.conj_pow]
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

theorem map_eq_of_count {a : ℕ} (f : Fin a → ℤ) (J : Multiset ℤ)
    (h : ∀ n : ℤ, (((Finset.univ.filter fun i => f i = n).card : ℕ) : ℤ) = (J.count n : ℤ)) :
    Finset.univ.val.map f = J := by
  ext n
  rw [Multiset.count_map]
  have h1 : (Multiset.filter (fun i => n = f i) Finset.univ.val).card =
      (Finset.univ.filter fun i => f i = n).card := by
    rw [Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr fun x _ => eq_comm
  rw [h1]
  exact_mod_cast h n

theorem sum_pow_eq {k : Type} [Field k] {a : ℕ} (f : Fin a → ℤ) (z : k) (n : ℕ) :
    ∑ i, (z ^ f i) ^ n = ((Finset.univ.val.map f).map fun h => (z ^ h) ^ n).sum := by
  rw [Multiset.map_map]
  rfl

theorem lay_pos {Γ : Type} [Group Γ] [TopologicalSpace Γ] {a : ℕ} (ha : 1 ≤ a) {L₀ : FinExt l}
    {r : Γ →* GL (Fin a) (Om l)} {Cl : Set (Γ →* GL (Fin a) (Om l))} (Cv : Cover L₀ r Cl) : 0 < (Cv.lay 1).m := by
  by_contra hm
  have hm0 : (Cv.lay 1).m = 0 := by omega
  have hd' : Cv.tw.d' 1 = 0 := by
    by_contra hd
    have h0 := (Cv.lay 1).indep.ne_zero ⟨0, by omega⟩
    apply h0
    funext k
    exact absurd k.2 (by omega)
  haveI : IsEmpty (Fin (Cv.tw.d' 1)) := by rw [hd']; infer_instance
  have hd : Cv.d = 0 := by
    by_contra hd
    obtain ⟨S, hS⟩ := (Cv.tw.onto 1).surj
    have h1 := hS ⟨0, by omega⟩ ⟨0, by omega⟩
    have h1' : (l : ℤ_[l]) ∣ 1 := by simpa [Matrix.mul_apply, Matrix.one_apply] using h1
    have hu := PadicInt.isUnit_iff.mp (isUnit_of_dvd_one h1')
    rw [PadicInt.norm_p] at hu
    have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    rw [inv_eq_one] at hu
    linarith
  haveI : IsEmpty (Fin Cv.d) := by rw [hd]; infer_instance
  have h1 := Cv.reads.one
  simp at h1
  have h2 := congrFun (congrFun h1 ⟨0, ha⟩) ⟨0, ha⟩
  simp at h2

end GlobalTheory.CovClose

namespace GlobalTheory.CovClose

set_option maxHeartbeats 1000000 in

theorem closed_of_cover : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ), 1 ≤ a → (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ L₀.1) → ∀ (r : ↥(GK K) →* GL (Fin a) (Om l)) (Cl : Set (↥(GK K) →* GL (Fin a) (Om l))) (Cv : Cover L₀ r Cl) (J : (↥K.1 →ₐ[ℚ_[l]] Om l) → Multiset ℤ), (∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ), multV (P.PD K) R τ n = ((J (L.1.val.comp τ)).count n : ℤ))) → ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (r g).val i j) → Formalism.MainNotions.N.IsDR (P.PD K) R ∧ (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ), multV (P.PD K) R τ n = ((J (L.1.val.comp τ)).count n : ℤ)) ∧ ((∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsCrys (P.PD K) R)) → IsCrys (P.PD K) R) := by
  intro l _ K L₀ P AI T a ha hL₀ r Cl Cv J hCl L r' R hL hR hr'
  obtain ⟨bk⟩ := GlobalTheory.BSP.nonempty_bk_of_finExt l K
  obtain ⟨τp, hτp⟩ := GlobalTheory.BSP.exists_isPer l K bk
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have hCd : C.InvdR := hC.invdR
  have hξ : Ideal.span {bk.ev bk.E} = RingHom.ker (Per.θ l) := bk.span_ev
  haveI := K.2

  let N : ℕ := Finset.univ.sup fun τ' : ↥K.1 →ₐ[ℚ_[l]] Om l => ((J τ').map Int.natAbs).sup
  have hN : ∀ τ', ∀ n ∈ J τ', |n| ≤ (N : ℤ) := by
    intro τ' n hn
    rw [Int.abs_eq_natAbs]
    have h1 : n.natAbs ≤ ((J τ').map Int.natAbs).sup := Multiset.le_sup (Multiset.mem_map_of_mem _ hn)
    have h2 : ((J τ').map Int.natAbs).sup ≤ N :=
      Finset.le_sup (f := fun τ' : ↥K.1 →ₐ[ℚ_[l]] Om l => ((J τ').map Int.natAbs).sup) (Finset.mem_univ τ')
    exact_mod_cast h1.trans h2

  have hsstCl : ∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1)
      (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) →
      (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R :=
    fun ρ₁ h L r' R h1 h2 h3 => (hCl ρ₁ h L r' R h1 h2 h3).1
  have hsst : ∀ m, IsSst P (qRep (Cv.tw.ρ' m)) := fun m =>
    (GlobalTheory.T.isSemistable_latticeInMatrixAlgebraLayer l K L₀ P AI T a Cl _ (Cv.tw.ρ' m) (Cv.lay m)).1 hsstCl
  have hfr : ∀ m, ∃ F : Frame bk N (Cv.tw.d' m) (fun g => (Cv.tw.ρ' m g).val),
      F.IsDR ∧ (IsCrys (P.PD K) (qRep (Cv.tw.ρ' m)) → F.IsCr) := fun m =>
    GlobalTheory.T.exists_breuilKisinFrame_semistable_boundedJumps l K bk τp hτp P AI T N _ (Cv.tw.ρ' m) (Cv.cont' m) (hsst m)
      (GlobalTheory.T.layer_DdR_bounds_alt l K L₀ P AI T a Cl J N hL₀ hN _ (Cv.tw.ρ' m) (Cv.lay m) hCl)
  choose F hFdr hFcr using hfr
  obtain ⟨F₀, hF₀dr, hF₀cr, rr, hlink⟩ := GlobalTheory.T.exists_deRhamFrame_limitLattice_breuilKisinTower l K bk τp hτp Cv.d N Cv.ρ Cv.tw F hFdr
  have hdr0 : Formalism.MainNotions.N.IsDR (P.PD K) (qRep Cv.ρ) := GlobalTheory.T.isDeRham_of_breuilKisinFrame_isDeRham l K bk τp hτp P AI T N Cv.d Cv.ρ F₀ hF₀dr
  have hread := GlobalTheory.T.deRham_crystalline_of_lattice_reads l K L₀ P AI T a Cv.d Cv.ρ r Cv.b Cv.e Cv.reads L r' R hL hR hr'
  have hdrR : Formalism.MainNotions.N.IsDR (P.PD K) R := hread.1 hdr0
  refine ⟨hdrR, ?_, fun hcr => hread.2 (GlobalTheory.T.isCrys_of_crystallineBreuilKisinFrame l K bk τp hτp P AI T N Cv.d Cv.ρ F₀
    (hF₀cr fun m => hFcr m ((GlobalTheory.T.isSemistable_latticeInMatrixAlgebraLayer l K L₀ P AI T a Cl _ (Cv.tw.ρ' m) (Cv.lay m)).2 hcr)))⟩

  intro τK
  obtain ⟨σ, hσ⟩ := exists_gal_inv (L.1.val.comp τK)
  have hσ' : ∀ x : ↥K.1, σ ((τK x : ↥L.1) : Om l) = (x : Om l) := hσ
  obtain ⟨g, z, hz, hzr⟩ := GlobalTheory.T.exists_galois_elem_cyclotomic_period_not_root_of_unity l K bk
  have hz0 : z ≠ 0 := by
    obtain ⟨w, -, hw⟩ := hz
    rintro rfl
    simp at hw

  have hex : ∀ m, ∃ (H : Hodge C (bk.ev bk.E) (fun g => (Cv.tw.ρ' m g).val.map (zOm l)) K)
      (Y : Matrix (Fin (Cv.tw.d' m)) (Fin (Cv.tw.d' m)) (Ainf l))
      (U' : Matrix (Fin (Cv.tw.d' m)) (Fin (Cv.tw.d' m)) ℂ_[l]),
      Y.map (inclW l) = inclW l τp ^ N • (F m).T ∧
      U' * Y.map ((Per.θD l).comp (aDp l)) = Y.map ((Per.θD l).comp (aDp l)) * ((F m).ε g).map ((Per.θD l).comp (aDp l)) ∧
      U' * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal fun i => z ^ ((H.p i : ℤ) - H.q) := by
    intro m
    obtain ⟨H, -⟩ := GlobalTheory.T.exists_hodge_basis_deRham_lattice l K P AI T C hC (bk.ev bk.E) hξ _ (Cv.tw.ρ' m)
      (GlobalTheory.sst_isDR l P AI T K _ (qRep (Cv.tw.ρ' m)) (hsst m))
    obtain ⟨Y, -, hY, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τp hτp N _ _ (F m).toPre
    obtain ⟨U', h1, h2⟩ := (GlobalTheory.T.adaptedBasis_theta_galoisFixed_poles l K bk τp hτp C hCd N _ _ (F m) Y (hFdr m) hY H).1 g z hz
    exact ⟨H, Y, U', hY, h1, h2⟩
  choose Hm Ym U' hYm hU'Y hU'V using hex
  obtain ⟨H0, -⟩ := GlobalTheory.T.exists_hodge_basis_deRham_lattice l K P AI T C hC (bk.ev bk.E) hξ _ Cv.ρ hdr0
  obtain ⟨Y0, -, hY0, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τp hτp N _ _ F₀.toPre
  obtain ⟨U, hUY, hUV⟩ := (GlobalTheory.T.adaptedBasis_theta_galoisFixed_poles l K bk τp hτp C hCd N _ _ F₀ Y0 hF₀dr hY0 H0).1 g z hz
  obtain ⟨Bd, hBd⟩ := GlobalTheory.T.theta_conj_bounded_compatible_breuilKisin_frames l K bk τp hτp N
  have hBdm := fun (m n : ℕ) => hBd N Cv.d (Cv.tw.d' m) n _ _ F₀ (F m) Y0 (Ym m) rfl hY0 (hYm m) g U (U' m) hUY (hU'Y m)
  have hUb : ∀ i j, ‖U i j‖ ≤ Bd := (hBdm 0 0).1
  have hU'b : ∀ m i j, ‖U' m i j‖ ≤ Bd := fun m => (hBdm m 0).2.1
  have hcomp : ∀ n, ∃ m, n ≤ m ∧ ∀ i j, ‖(U * (Cv.tw.Pi m).map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) -
      (Cv.tw.Pi m).map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) * U' m) i j‖ ≤ Bd * ((l : ℝ) ^ n)⁻¹ := by
    intro n
    obtain ⟨m, hnm, R₁, -, hdiv, -⟩ := hlink n
    exact ⟨m, hnm, (hBdm m n).2.2 (Cv.tw.Pi m) R₁
      (fun g i j => (pow_dvd_pow _ hnm).trans ((Cv.tw.onto m).equi g i j)) hdiv⟩

  let S : ℕ → ℂ_[l] := fun n => ((J (L.1.val.comp τK)).map fun h => (z ^ h) ^ n).sum

  have hlay : ∀ m (k : Fin (Cv.lay m).m), ∃ u : Matrix (Fin a) (Fin a) ℂ_[l], ∀ n,
      (∑ i, ((U' m ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l ((Cv.lay m).e s))) i •
        ((Cv.lay m).b i k).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = (u ^ n).trace ∧
      (u ^ n).trace = S n := by
    intro m k
    let rk := modelOf ((Cv.lay m).rep k) ((Cv.lay m).L k) ((Cv.lay m).rep_mem k)
    have hrk : ∀ g i j, (((rk g).val i j : ↥((Cv.lay m).L k).1) : Om l) = ((Cv.lay m).rep k g).val i j :=
      fun g i j => modelOf_apply _ _ _ g i j
    obtain ⟨hsk, hmk⟩ := hCl ((Cv.lay m).rep k) ((Cv.lay m).mem k) ((Cv.lay m).L k) rk (repOf rk) ((Cv.lay m).le k) (repOf_apply rk) hrk
    let τk : ↥K.1 →ₐ[ℚ_[l]] ↥((Cv.lay m).L k).1 :=
      (L.1.val.comp τK).codRestrict ((Cv.lay m).L k).1.toSubalgebra (fun x => (Cv.lay m).le k (hL₀ _ x))
    have hσk : ∀ x : ↥K.1, σ ((τk x : ↥((Cv.lay m).L k).1) : Om l) = (x : Om l) := hσ
    obtain ⟨K', Hk, hKK', hcard⟩ := GlobalTheory.T.exists_hodge_basis_at_embedding l K ((Cv.lay m).L k) P AI T C hC (bk.ev bk.E) hξ a rk (repOf rk)
      (repOf_apply rk) (isDR_of_isSst P AI T _ hsk) τk σ hσk
    have hcτ : ((Cv.lay m).L k).1.val.comp τk = L.1.val.comp τK := AlgHom.ext fun _ => rfl
    have hms : Finset.univ.val.map (fun i => (Hk.p i : ℤ) - Hk.q) = J (L.1.val.comp τK) :=
      map_eq_of_count _ _ fun n => by rw [hcard n, hmk τk n, hcτ]
    have hW : IsUnit (Hk.V.map (Per.θD l)) := Hk.unit.map (Per.θD l).mapMatrix
    obtain ⟨huW, htr⟩ := conj_diag _ hW fun i => z ^ ((Hk.p i : ℤ) - Hk.q)
    have hHT := (GlobalTheory.T.isHodgeTate_iff_diagonal_adapted_basis l K K' C hCd (bk.ev bk.E) hξ a _ Hk z _ hKK').1 huW
    have hρ : (fun g => (rk g).val.map fun x => σ (x : Om l)) = fun g => ((Cv.lay m).rep k g).val.map σ := by
      funext g
      ext i j
      simp only [Matrix.map_apply, hrk]
    have hmv : ∀ u, IsHT C (bk.ev bk.E) (fun g => (rk g).val.map fun x => σ (x : Om l)) z u →
        IsHT C (bk.ev bk.E) (fun g => ((Cv.lay m).rep k g).val.map σ) z u := fun u h => hρ ▸ h
    replace hHT := hmv _ hHT
    refine ⟨Hk.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((Hk.p i : ℤ) - Hk.q)) * (Hk.V.map (Per.θD l))⁻¹,
      fun n => ⟨?_, ?_⟩⟩
    · exact (congrArg Matrix.trace (GlobalTheory.T.hodgeTateOperator_pow_eq_sum l K C (bk.ev bk.E) a _ (Cv.tw.ρ' m) ((Cv.lay m).rep k) (fun s => (Cv.lay m).b s k) (Cv.lay m).e
        ((Cv.lay m).reads k) σ z (Hm m) (U' m) _ (hU'V m) hHT n)).symm
    · rw [htr n, sum_pow_eq (fun i => (Hk.p i : ℤ) - Hk.q) z n, hms]
  have hS0 : S 0 = a := by
    obtain ⟨u, hu⟩ := hlay 1 ⟨0, lay_pos ha Cv⟩
    rw [← (hu 0).2, pow_zero, Matrix.trace_one, Fintype.card_fin]
  have hlayS : ∀ m k n, (∑ i, ((U' m ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l ((Cv.lay m).e s))) i •
      ((Cv.lay m).b i k).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = S n := by
    intro m k n
    obtain ⟨u, hu⟩ := hlay m k
    exact (hu n).1.trans (hu n).2
  have hcov := GlobalTheory.T.trace_pow_eq_along_latticeTowerCover l (↥(GK K)) L₀ a ha r Cl Cv σ U U' Bd S hS0 hUb hU'b hcomp hlayS

  obtain ⟨K', HR, hKK', hcard⟩ := GlobalTheory.T.exists_hodge_basis_at_embedding l K L P AI T C hC (bk.ev bk.E) hξ a r' R hR hdrR τK σ hσ'
  have hW : IsUnit (HR.V.map (Per.θD l)) := HR.unit.map (Per.θD l).mapMatrix
  obtain ⟨huW, htr⟩ := conj_diag _ hW fun i => z ^ ((HR.p i : ℤ) - HR.q)
  have hHT := (GlobalTheory.T.isHodgeTate_iff_diagonal_adapted_basis l K K' C hCd (bk.ev bk.E) hξ a _ HR z _ hKK').1 huW
  have hρ : (fun g => (r' g).val.map fun x => σ (x : Om l)) = fun g => (r g).val.map σ := by
    funext g
    ext i j
    simp only [Matrix.map_apply, hr']
  have hmv : ∀ u, IsHT C (bk.ev bk.E) (fun g => (r' g).val.map fun x => σ (x : Om l)) z u →
      IsHT C (bk.ev bk.E) (fun g => (r g).val.map σ) z u := fun u h => hρ ▸ h
  replace hHT := hmv _ hHT
  have hnat := GlobalTheory.T.hodgeTateOperator_pow_eq_sum l K C (bk.ev bk.E) a Cv.d Cv.ρ r Cv.b Cv.e Cv.reads σ z H0 U _ hUV hHT
  have hpow : ∀ n : ℕ, ((Finset.univ.val.map fun i => (HR.p i : ℤ) - HR.q).map fun h => (z ^ h) ^ n).sum =
      ((J (L.1.val.comp τK)).map fun h => (z ^ h) ^ n).sum := by
    intro n
    rw [← sum_pow_eq]
    exact (htr n).symm.trans ((congrArg Matrix.trace (hnat n)).trans (hcov n))
  have hms := GlobalTheory.T.multiset_eq_of_power_sums_zpow_eq ℂ_[l] z hz0 hzr _ _ hpow
  intro n
  rw [← hcard n, ← hms, Multiset.count_map]
  have h1 : (Multiset.filter (fun i => n = (HR.p i : ℤ) - HR.q) Finset.univ.val).card =
      (Finset.univ.filter fun i => (HR.p i : ℤ) - HR.q = n).card := by
    rw [Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr fun x _ => eq_comm
  rw [h1]

end GlobalTheory.CovClose
