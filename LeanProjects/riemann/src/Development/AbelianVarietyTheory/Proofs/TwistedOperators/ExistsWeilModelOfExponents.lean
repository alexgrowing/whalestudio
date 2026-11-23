import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTransStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumKeepsAdmissibleFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumIsUnitaryAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilDatumAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSchroedingerModelSiegelRuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubledSchrodingerModelTransposedSiegelRulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumCompGroupSwappingSymplecticEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivConjOfGramTransposeEqNeg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTransposeGramCoordinateHomeomorphSymplecti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHomTransposeGramDarboux
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualGOfGQ
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNegConjMemberHermitianLatticeSpaceData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTauEOverRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
import Formalism.LocalToGlobal.IndefiniteReal.DatumLemmas
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.PairDarboux

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexOrder

theorem submatrix_mul_id {R : Type} [CommRing R] {m n p k : ℕ} (M : Matrix (Fin m) (Fin n) R) (N : Matrix (Fin n) (Fin p) R)
    (e : Fin k → Fin m) : (M * N).submatrix e id = M.submatrix e id * N := by
  ext i j
  simp [Matrix.mul_apply]

theorem actE_eq_of_conj_related {R : Type} [CommRing R] {n m k : ℕ} (e : Fin k ≃ Fin m) (P : Matrix (Fin n) (Fin n) R)
    (x : Matrix (Fin n) (Fin m) R) (Q : Matrix (Fin m) (Fin m) R) (G H : Matrix (Fin n) (Fin n) R)
    (M₁ : Matrix (Fin k) (Fin k) R) (Lx : Matrix (Fin k) (Fin n) R) (M₂ : Matrix (Fin n) (Fin n) R)
    (hLx : Lx = xᵀ.submatrix e id * G) (h₁ : M₁ = Qᵀ.submatrix e e) (h₂ : M₂ = H) (hu : Pᵀ * G = G * H) :
    ((P * x * Q)ᵀ.submatrix e id) * G = M₁ * Lx * M₂ := by
  subst hLx h₁ h₂
  rw [Matrix.transpose_mul, Matrix.transpose_mul, submatrix_mul_id, ← Matrix.mul_assoc (Qᵀ.submatrix e e),
    Matrix.submatrix_mul_equiv, submatrix_mul_id]
  simp only [Matrix.mul_assoc]
  rw [hu]

theorem unit_aux {R : Type} [CommRing R] {n : ℕ} (c : R →+* R) (P P' K G : Matrix (Fin n) (Fin n) R)
    (hPP : P * P' = 1) (hK : Kᵀ = -G) (h : (P.map c)ᵀ * K * P = K) : Pᵀ * G = G * P'.map c := by
  have h' := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, hK,
    Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h'
  have hc : P.map c * P'.map c = 1 := by
    rw [← Matrix.map_mul, hPP]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  calc Pᵀ * G = Pᵀ * G * (P.map c * P'.map c) := by rw [hc, Matrix.mul_one]
    _ = (Pᵀ * G * P.map c) * P'.map c := by simp only [Matrix.mul_assoc]
    _ = G * P'.map c := by rw [h']

theorem eq_submatrix_symm {α : Type} {a b : ℕ} (f : Fin a ≃ Fin b) (M : Matrix (Fin b) (Fin b) α)
    (N : Matrix (Fin a) (Fin a) α) (h : M.submatrix f f = N) : M = N.submatrix f.symm f.symm := by
  subst h
  ext i j
  simp

theorem incM_neg_refl {D : D7} {n : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (-(G.submatrix (Equiv.refl (Fin n)) (Equiv.refl (Fin n)))) = -(G.map (incA D)) := by
  ext i j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, Matrix.neg_apply, Matrix.submatrix_apply,
    Equiv.refl_apply, map_neg]

theorem eq_map_conj {D : D7} {n : ℕ} (P Q : Matrix (Fin n) (Fin n) (AE D)) (h : Q = P.map (cA D)) : P = Q.map (cA D) := by
  subst h
  ext i j
  simp [Formalism.L2.Theta.cA_cA]

theorem eq_inv_transpose {R : Type} [CommRing R] {n : ℕ} (P P' B B' : Matrix (Fin n) (Fin n) R) (hP : P' * P = 1)
    (hB : B * B' = 1) (h : B = P'ᵀ) : P = B'ᵀ := by
  have h1 : Pᵀ * B = 1 := by rw [h, ← Matrix.transpose_mul, hP, Matrix.transpose_one]
  have h2 : B' = Pᵀ := by
    calc B' = (Pᵀ * B) * B' := by rw [h1, Matrix.one_mul]
      _ = Pᵀ := by rw [Matrix.mul_assoc, hB, Matrix.mul_one]
  rw [h2, Matrix.transpose_transpose]

theorem sgn_gram_eq {D : D7} (ε : Bool) (S : HSp D) : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
  cases ε
  · show S.gram = _
    simp
  · show (neg S).gram = _
    rw [neg_gram]
    simp

theorem gram_neg_sgn {D : D7} (ε : Bool) (S : HSp D) {J : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    (hJ : J = (if ε then 1 else -1 : D.host.E) • S.gram) : J = -(sgn ε S).gram := by
  rw [sgn_gram_eq, hJ]
  cases ε <;> simp

theorem conj_herm {D : D7} (V : HSp D) :
    (GlobalTheory.WeilSchrodinger.sesq D V.gramᵀ).IsSymm ∧ (GlobalTheory.WeilSchrodinger.sesq D V.gramᵀ).Nondegenerate ∧
      ∃ L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E), L.IsLattice D.host.E ∧
        Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D V.gramᵀ) L := by
  have hdet : V.gramᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact gram_det_ne V
  have hs : ∀ i j, star (V.gram i j) = V.gram j i := GlobalTheory.TripleSpace.star_gram V
  have hsd := GlobalTheory.PlaceModel.isSelfDualC_latFrame V
  refine ⟨⟨fun x y => ?_⟩, ⟨fun x hx => ?_, fun y hy => ?_⟩, Formalism.L2.Col.starLat D.host.E (GlobalTheory.PlaceModel.latFrame V),
    Formalism.L2.Col.brp_starLat_lattice _ _ hsd.1, ?_⟩
  · simp only [GlobalTheory.WeilSchrodingerHerm.sesq_apply, starRingEnd_apply, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star,
      Pi.star_apply, Matrix.transpose_apply, hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · have h1 : star x ᵥ* V.gramᵀ = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [← Matrix.dotProduct_mulVec, ← GlobalTheory.WeilSchrodingerHerm.sesq_apply]
      exact hx v
    have h2 : star x = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
    simpa using congrArg star h2
  · have h1 : V.gramᵀ *ᵥ y = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [dotProduct_comm]
      have := hy (star v)
      rwa [GlobalTheory.WeilSchrodingerHerm.sesq_apply, star_star] at this
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1
  · show Formalism.E.hdual _ _ = _
    ext x
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
    rw [GlobalTheory.TripleSpace.mem_starLat_iff_form V hsd x]
    refine forall₂_congr fun y _ => ?_
    rw [GlobalTheory.WeilSchrodingerHerm.sesq_transpose_eq_form, GlobalTheory.WeilSchrodingerHerm.mem_one_iff]
    have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((-1 : D.host.E) • V.gram) x y =
        -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig V.gram x y := by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, Matrix.neg_mulVec]
    rw [e]
    exact ⟨fun h => h.neg, fun h => by simpa using h.neg⟩

theorem isCartan_conj {n : ℕ} {G S : Matrix (Fin n) (Fin n) ℂ} {κ : ℝ} (hκ : 0 < κ) (h : IsCartanInv G S) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan ((κ : ℂ) • G) (S.map (starRingEnd ℂ)) := by
  obtain ⟨hSS, hSGS, hGS⟩ := h
  have hSG : Sᴴ * G = G * S := by
    calc Sᴴ * G = Sᴴ * G * (S * S) := by rw [hSS, Matrix.mul_one]
      _ = (Sᴴ * G * S) * S := by simp only [Matrix.mul_assoc]
      _ = G * S := by rw [hSGS]
  have hT : (S.map (starRingEnd ℂ))ᵀ = Sᴴ := by
    ext i j; simp [Matrix.conjTranspose_apply]
  have hMM : (S.map (starRingEnd ℂ)).map star = S := by
    ext i j; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, hSS, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [hT, hMM, Matrix.mul_smul, Matrix.smul_mul, hSGS]
  · intro x hx
    have hy : star x ≠ 0 := by simpa using hx
    have hv : S.map (starRingEnd ℂ) *ᵥ x = star (S *ᵥ star x) := by
      ext i; simp [Matrix.mulVec, dotProduct, star_sum, Pi.star_apply, mul_comm]
    have hpos : ((κ : ℂ) • (G * S)).PosDef := hGS.smul (by exact_mod_cast hκ)
    have key : (S.map (starRingEnd ℂ) *ᵥ x) ⬝ᵥ ((κ : ℂ) • G) *ᵥ star x =
        star (star x) ⬝ᵥ (((κ : ℂ) • (G * S)) *ᵥ star x) := by
      rw [hv, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_smul, hSG]
    rw [key]
    have := hpos.dotProduct_mulVec_pos hy
    exact (Complex.lt_def.1 this).1

theorem isVac_of_bot {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (hY : Y.L = ⊥) (ψ : AddChar (AF F) ℂ) (θ : 𝓞 E) (hθ : (θ : E) + σ θ = 1) (v : HeightOneSpectrum (𝓞 F)) :
    Mo.IsVac ψ v (Set.indicator {x : Fin n × Fin d → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  refine ⟨GlobalTheory.StdVacuum.indicator_mem_SB v, fun h => ?_, θ, hθ, fun γ hγ => ?_⟩
  · have := congrFun h 0
    simp [Set.indicator, zero_mem] at this
  · have h0 : γ = 0 := by
      have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Y Z v ≤ ⊥ := by
        refine (AddSubgroup.closure_le _).2 ?_
        rintro z ⟨a, -, -, x, hx, y, -, rfl⟩
        rw [hY, Submodule.mem_bot] at hx
        subst hx
        show _ = 0
        ext i j
        simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
      exact this hγ
    subst h0
    intro r _
    funext x
    simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens]

set_option maxHeartbeats 1600000 in

theorem exists_weil_transp {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (hJ : Vs.J = GlobalTheory.RealDict.sgE (D := D) ε • S.gram)
    (hJW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)))
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws)
    (hrat : ∀ x : Matrix (Fin S.rank) (Fin X.rank) D.host.E, ∃ y z : Fin S.rank × Fin X.rank → D.host.F,
      M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
        (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)))
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep S X) (hω : IsWeil ψ ε S X χ χ' ω) :
    ∃ om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Vs Ws, M.IsWeil ψ χ χ' om ∧
      GlobalTheory.TripleRead.IsTransp ψ ε M om ω (Equiv.refl (Fin X.rank)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S (GlobalTheory.RealDict.sgE (D := D) ε) hJ)
        (GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJW) := by
  have hω' : IsWeilDatumO ψ (sgn ε S) X χ χ' (ω.toSgn ε) := hω
  obtain ⟨h1, h2, L0, hL0, h3⟩ := conj_herm (neg (sgn ε S))
  let Th : HSp D := GlobalTheory.WeilSchrodinger.hspOf D (k := S.rank) (neg (sgn ε S)).gramᵀ h1 h2 L0 hL0 h3 (fun _ => (0, 0))
  let Sh : HSp D := GlobalTheory.DualSwap.dualSp (neg X) _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame (neg X))
  have hTg : Th.gram = (neg (sgn ε S)).gramᵀ := GlobalTheory.WeilSchrodinger.gram_hspOf _ _ _ _ _ _ _
  have hSg : Sh.gram = (neg X).gram⁻¹ᵀ := GlobalTheory.DualSwap.dualSp_gram _ _ _
  let e : Fin X.rank ≃ Fin X.rank := Equiv.refl _
  have hT' : Th.gramᵀ = -((sgn ε S).gram.submatrix (Equiv.refl (Fin S.rank)) (Equiv.refl (Fin S.rank))) := by
    rw [hTg]
    rfl
  have hS' : Sh.gram⁻¹ = -(X.gramᵀ.submatrix e.symm e.symm) := by
    refine Matrix.inv_eq_left_inv ?_
    have key : (neg X).gramᵀ * (neg X).gram⁻¹ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne (neg X))), Matrix.transpose_one]
    rw [hSg]
    exact key

  obtain ⟨φ', hφ'c, hφ'Q, hφ'm, hφ'S, hφ'd⟩ := GlobalTheory.GrpConj.exists_conj_equiv D (sgn ε S) Th (Equiv.refl _) hT'
  obtain ⟨φ, hφc, hφQ, hφm, hφS, hφd⟩ := GlobalTheory.InvTransposeIso.grp_contra D X Sh e.symm hS'
  obtain ⟨L, hL1, hL2, hLc, hLc', hLQ, hLi, hLf⟩ := GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec D (sgn ε S) X Sh Th (Equiv.refl _) e.symm
  have hsy := GlobalTheory.DarbouxSymp.symplO_darboux D (sgn ε S) X Sh Th (Equiv.refl _) e.symm hT' hS'
  have hLx : ∀ u : Matrix (Fin S.rank) (Fin X.rank) (AE D), L u = (HMul.hMul (uᵀ.submatrix e id) ((sgn ε S).gram.map (incA D)) :
      Matrix (Fin X.rank) (Fin S.rank) (AE D)) := fun u => (hL1 u).trans rfl
  have hpt : ∀ x : Matrix (Fin X.rank) (Fin S.rank) (AE D), GlobalTheory.TripleRead.ptO (sgn ε S).gram e x = L.symm x :=
    fun x => ((hL2 x).trans rfl).symm

  have hact : ∀ (g : GA D Sh) (h : GA D Th) (x : WO Sh Th), L (actO Sh Th g h x) = actO (sgn ε S) X (φ' h) (φ g) (L x) := by
    intro g h x
    have hg : Formalism.L2.Theta.mt X (φ g) = ((Formalism.L2.Theta.mt Sh g⁻¹)ᵀ).submatrix e e :=
      eq_submatrix_symm e.symm _ _ (hφm g)
    have hh : Formalism.L2.Theta.mt (sgn ε S) (φ' h)⁻¹ = (Formalism.L2.Theta.mt Th h⁻¹).map (cA D) := by
      rw [← map_inv]
      exact hφ'm h⁻¹
    have hTinc : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM Th.gram)ᵀ = -((sgn ε S).gram.map (incA D)) := by
      have e0 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM Th.gram)ᵀ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM Th.gramᵀ := rfl
      rw [e0, hT']
      exact incM_neg_refl _
    have hPP : Formalism.L2.Theta.mt Th h * Formalism.L2.Theta.mt Th h⁻¹ = 1 := by
      simp only [Formalism.L2.Theta.mt, map_inv, Units.mul_inv]
    have hu := unit_aux (cA D) _ _ _ _ hPP hTinc (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram Th h)
    exact (hLx _).trans (actE_eq_of_conj_related e _ x _ _ _ _ _ _ (hLx x) hg hh hu)

  obtain ⟨ω', hω'', hrel⟩ := GlobalTheory.T.isWeilDatum_comp_group_swapping_symplectic_equiv D ψ (sgn ε S) X Sh Th rfl rfl L φ.toMonoidHom φ'.toMonoidHom hLc hLc' hLQ
    (fun x y => by rw [hL1, hL1]; exact hsy x y) hLi hLf hφc hφ'c hφQ hφ'Q hact hφS hφ'S hφd hφ'd χ χ' (ω.toSgn ε) hω'
  have hA : Vs.J = Th.gramᵀ := (gram_neg_sgn ε S hJ).trans hT'.symm
  have hB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • Sh.gram⁻¹) := by
    rw [hS', hJW]
    funext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, e]
  obtain ⟨om, hom⟩ := GlobalTheory.T.exists_weilDatum_transport_adelicSchwartz_thetaTransform D ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin X.rank) M.co hrat ω' hω''
  have h2 := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin X.rank) M.co hrat ω' hω'' om hom
  have h3 := GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms D ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin X.rank) M.co hrat ω' hω'' om hom
  have h4 := GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin X.rank) M.co hrat ω' hω'' om hom
  have h5 := GlobalTheory.T.continuous_transported_weilDatum_adelicSchwartz D ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin X.rank) M.co hrat ω' hω'' om hom
  have h6 := GlobalTheory.T.exists_doubledWeil_blockEmbedding_acts_on_first_boxFactor D ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin X.rank) M.co hrat ω' hω'' om hom
  have h7 := GlobalTheory.T.exists_doubled_schrodingerModel_transposed_siegelRule D ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin X.rank) M.co hrat ω' hω'' om hom
  have hsp : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ M.co
      (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) om := ⟨⟨h2.1, h2.2, h3⟩, h4, h5⟩
  have hW : M.IsWeil ψ χ χ' om :=
    ⟨⟨GlobalTheory.WeilSchrodinger.isUSplitting_inr hsp, h6⟩, ⟨GlobalTheory.WeilSchrodinger.transD _ M.co, GlobalTheory.WeilSchrodinger.transD_e M.co,
      GlobalTheory.WeilSchrodinger.isUSplitting_inl hsp, h7⟩, h5⟩
  refine ⟨om, hW, ?_⟩
  intro Φ hΦ g h
  have hm : Formalism.L2.Theta.mt (sgn ε S) ((ofSgn ε S).symm g) = Formalism.L2.Theta.mt S g := by
    rw [← mt_ofSgn, MulEquiv.apply_symm_apply]
  have h0 := hφ'm (φ'.symm ((ofSgn ε S).symm g))
  rw [MulEquiv.apply_symm_apply] at h0
  have ha : Formalism.L2.Theta.mt Th (φ'.symm ((ofSgn ε S).symm g)) = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S _ hJ g).1.1 :=
    eq_map_conj _ _ (hm.symm.trans h0)
  have h1 := hφm (φ.symm h)
  rw [MulEquiv.apply_symm_apply] at h1
  have hP : Formalism.L2.Theta.mt Sh (φ.symm h)⁻¹ * Formalism.L2.Theta.mt Sh (φ.symm h) = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv, Units.inv_mul]
  have hb : Formalism.L2.Theta.mt Sh (φ.symm h) = ((GlobalTheory.TripleRead.toUX X e hJW h)⁻¹).1.1ᵀ :=
    eq_inv_transpose _ _ _ _ hP (Units.mul_inv (GlobalTheory.TripleRead.toUX X e hJW h).1) h1
  obtain ⟨-, ht⟩ := hom (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S _ hJ g) (GlobalTheory.TripleRead.toUX X e hJW h) (φ.symm h)
    (φ'.symm ((ofSgn ε S).symm g)) ha hb Φ hΦ
  have hth : ∀ (Ψ : (Fin S.rank × Fin X.rank → AF D.host.F) → ℂ) (u : WO Sh Th),
      GlobalTheory.TripleRead.thO M ψ (sgn ε S).gram e Ψ (L u) = GlobalTheory.WeilSchrodinger.thetaTr D.host.F M.co ψ Ψ u := fun Ψ u => by
    unfold GlobalTheory.TripleRead.thO
    rw [hpt, LinearEquiv.symm_apply_apply]
    rfl
  funext x
  obtain ⟨u, rfl⟩ := L.surjective x
  have hΦf : GlobalTheory.WeilSchrodinger.thetaTr D.host.F M.co ψ Φ = fun u => GlobalTheory.TripleRead.thO M ψ (sgn ε S).gram e Φ (L u) :=
    funext fun u => (hth Φ u).symm
  have k1 := congrFun ht u
  have k2 := congrArg (fun F => ω' (φ.symm h, φ'.symm ((ofSgn ε S).symm g)) F u) hΦf
  have k3 := congrFun (hrel (φ.symm h) (φ'.symm ((ofSgn ε S).symm g)) (GlobalTheory.TripleRead.thO M ψ (sgn ε S).gram e Φ)) u
  refine (hth _ u).trans (k1.trans (k2.trans (k3.trans ?_)))
  simp [WRep.toSgn, e]

theorem exists_pair_darboux : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∃ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ ∧ GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ := by
  intro _ D ψ θ hψ _ ε M X A B χS χT ω eS eT hω _
  have hω' : IsWeilDatumO ψ (sgn ε M) X χS χT (ω.toSgn ε) := hω
  have hcm : IsCMExt D.host.F D.host.E D.sp.cm.sig := GlobalTheory.AdelicU.isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hcm.2.2.1
  choose τf hτf using (GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace (D := D))
  let τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w := fun w => ⟨_, hτf w⟩
  have hτ : ∀ w x, (τ w).1 x = conj (tauE D (τf w) x) := fun _ _ => rfl
  let Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank :=
    ⟨GlobalTheory.RealDict.sgE (D := D) ε • M.gram, ⊥, fun w => (if ε then 1 else -1 : ℂ) • A.cart (τf w), fun _ => 1⟩
  let Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank :=
    ⟨D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)), ⊥,
      fun w => (B.cart (τf w)).map conj, fun _ => 1⟩
  have hXJ : Xs.J = -(sgn ε M).gram := gram_neg_sgn ε M rfl
  have hWJ : Ws.J = D.host.xi0 • X.gramᵀ := rfl
  have hc : GlobalTheory.RealDict.sgE (D := D) ε ≠ 0 := by cases ε <;> simp [GlobalTheory.RealDict.sgE]
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have hXh : ∀ i j, D.sp.cm.sig (Xs.J j i) = Xs.J i j := fun i j => by
    rw [hXJ]
    show star (-(sgn ε M).gram j i) = -(sgn ε M).gram i j
    rw [star_neg, GlobalTheory.TripleSpace.star_gram]
  have hXd : Xs.J.det ≠ 0 := by
    rw [hXJ]
    exact gram_det_ne (neg (sgn ε M))
  have hWs : ∀ i j, D.sp.cm.sig (Ws.J j i) = -Ws.J i j := fun i j => by
    show star (D.host.xi0 * X.gram i j) = -(D.host.xi0 * X.gram j i)
    rw [star_mul', Formalism.IndefR.Datum.Brg.star_purely_imaginary_eq_neg, GlobalTheory.TripleSpace.star_gram, neg_mul]
  have hWd : Ws.J.det ≠ 0 := by
    rw [hWJ, Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hξ) (gram_det_ne X)
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star (R := D.host.E) x
  obtain ⟨co, hrat⟩ := GlobalTheory.RatDarboux.exists_darboux (AF D.host.F) h2 D.sp.cm.sig hσ hXh hWs hXd hWd
  obtain ⟨μ, 𝓕, hμ, h𝓕⟩ := GlobalTheory.ConstRatio.exists_meas M
  obtain ⟨hμ', h𝓕'⟩ := GlobalTheory.ConjUTransport.map_isHaar_isFundamentalDomain M (J := Xs.J) _ hc rfl μ 𝓕 hμ h𝓕
  obtain ⟨o, ho⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified D.host.F D.host.E D.sp.cm.sig hcm
    (by haveI := GlobalTheory.InertOfConj.unram D; infer_instance)
  let Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws :=
    ⟨co, fun v => Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers D.host.F} 1,
      μ.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (J := Xs.J) _ rfl), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (J := Xs.J) _ rfl '' 𝓕⟩
  have hgood : Mo.IsGood ψ :=
    { rat := hrat
      vac := fun v => isVac_of_bot Mo rfl ψ o ho v
      std := Filter.Eventually.of_forall fun _ => rfl
      haar := hμ'
      dom := h𝓕' }
  obtain ⟨om, hom, htr⟩ := exists_weil_transp ψ ε M X Xs Ws rfl rfl Mo hrat χS χT ω hω
  refine ⟨Xs, Ws, Mo, ψ, χS, χT, om, τ, ⟨hcm, GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ, hXh, hXd, hWs, hWd,
    GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ hω'.resS, GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ hω'.resT,
    hω'.hecS, hω'.hecT, hom, fun w => ?_, fun w => ?_⟩,
    ⟨rfl, rfl, rfl, fun w => ⟨τf w, hτ w, rfl, rfl⟩, hgood, htr⟩⟩
  · have h := GlobalTheory.TripleSpace.isCartan_neg_conj
      (isCartanInv_sgn ε M (τf w) (GlobalTheory.CompactFockAction.cart_isCartanInv A (τf w)))
    have e1 : Xs.J.map (τ w).1 = -((gramAt D (sgn ε M) (τf w)).map star) := by
      rw [hXJ]
      ext a b
      simp [gramAt, hτ]
    have e2 : Xs.θ w = -sgnM ε (A.cart (τf w)) := by
      cases ε <;> simp [Xs, sgnM]
    rw [e1, e2]
    exact h
  · have h := isCartan_conj (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (GlobalTheory.CompactFockAction.cart_isCartanInv B (τf w))
    have e0 : Complex.I * conj (tauE D (τf w) D.host.xi0) = ((tauE D (τf w) D.host.xi0).im : ℂ) := by
      apply Complex.ext <;> simp [Formalism.IndefR.Fock.CCR.realPlace_imaginaryGenerator_re_eq_zero]
    have e1 : Complex.I • Ws.J.map (τ w).1 = ((tauE D (τf w) D.host.xi0).im : ℂ) • gramAt D X (τf w) := by
      ext a b
      have e3 : conj (tauE D (τf w) (X.gram b a)) = tauE D (τf w) (X.gram a b) := by
        rw [← GlobalTheory.TripleSpace.star_gram X b a]
        exact (hcm.2.2.2 (tauE D (τf w)) (X.gram b a)).symm
      show Complex.I * conj (tauE D (τf w) (D.host.xi0 * X.gram b a)) = _ * tauE D (τf w) (X.gram a b)
      rw [map_mul, map_mul, ← mul_assoc, e0, e3]
    rw [e1]
    exact h

end GlobalTheory.PairDarboux

end
