import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTransStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumKeepsAdmissibleFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumIsUnitaryAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilDatumAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSchroedingerModelSiegelRuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubledSchrodingerModelTransposedSiegelRulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumCompGroupSwappingSymplecticEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivConjOfGramTransposeEqNegStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEquivInvTransposeOfGramInvStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTransposeGramCoordinateHomeomorphSymplectiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHomTransposeGramDarbouxStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

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

theorem neg_incM_eq {D : D7} {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (hJ : IsUnit J.det) {ξ : D.host.E} (hξ : ξ ≠ 0) :
    (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (ξ • (-ξ • J⁻¹)⁻¹) := by
  have e1 : (-ξ • J⁻¹)⁻¹ = (-ξ)⁻¹ • J := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ, inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul]
  have e2 : ξ • (-ξ)⁻¹ • J = -J := by
    rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
  rw [e1, e2]
  funext i j
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]

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

theorem gram_hspOf_transpose {D : D7} {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E)
    (h1 : (GlobalTheory.WeilSchrodinger.sesq D Jᵀ).IsSymm) h2 L hL h3 (sg : (D.host.E →+* ℂ) → ℕ × ℕ) :
    (GlobalTheory.WeilSchrodinger.hspOf D Jᵀ h1 h2 L hL h3 sg).gramᵀ = J := by
  rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
  exact Matrix.transpose_transpose J

set_option maxHeartbeats 1600000 in

theorem exists_weil_of_oriented : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ (χ χ' : (AE D)ˣ →* Circle) (ω : WRep S X), IsWeil ψ ε S X χ χ' ω →
    ∃ om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Vs Ws, M.IsWeil Bs.ψ χ χ' om ∧
      ∀ Φ f, IsDatum M ψ cS Φ f → ∀ g h,
        IsDatum M ψ cS (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S _ hJ g, kapX X e hJW h) Φ) (ω (g, h) f) := by
  intro D ψ θ _hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW _hcart M hM cS hcS χ χ' ω hω
  subst hψ
  have hω' : IsWeilDatumO Bs.ψ (sgn ε S) X χ χ' (ω.toSgn ε) := hω
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular D Bs hBs S.rank Vs r s hV
  obtain ⟨hJd, L0, hL0, h4, h5, h6⟩ := GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular D Bs hBs d Ws r' s' hW
  let Th := GlobalTheory.WeilSchrodinger.hspOf D Vs.Jᵀ h1 h2 Vs.L hV.lat h3 (fun _ => (r, s))
  let Sh := GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Ws.J⁻¹) h4 h5 L0 hL0 h6 (fun _ => (s', r'))
  have hTt : Th.gramᵀ = Vs.J := gram_hspOf_transpose _ _ _ _ _ _ _
  have hSg : Sh.gram = -D.host.xi0 • Ws.J⁻¹ := GlobalTheory.WeilSchrodinger.gram_hspOf _ _ _ _ _ _ _
  have hdX : X.rank = d := Fin.equiv_iff_eq.mp ⟨e⟩
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D

  have hT' : Th.gramᵀ = -((sgn ε S).gram.submatrix (Equiv.refl (Fin S.rank)) (Equiv.refl (Fin S.rank))) := by
    rw [hTt, Equiv.coe_refl, Matrix.submatrix_id_id]
    exact gram_neg_sgn ε S hJ
  have hS' : Sh.gram⁻¹ = -(X.gramᵀ.submatrix e.symm e.symm) := by
    refine Matrix.inv_eq_left_inv ?_
    have hK : D.host.xi0 • X.gramᵀ.submatrix e.symm e.symm = Ws.J := by rw [hJW]; rfl
    have key : (-(X.gramᵀ.submatrix e.symm e.symm)) * (-D.host.xi0 • Ws.J⁻¹) = 1 := by
      rw [neg_mul, Matrix.mul_smul, neg_smul, neg_neg, ← Matrix.smul_mul, hK]
      exact Matrix.mul_nonsing_inv _ hJd
    rw [hSg]
    exact key

  obtain ⟨φ', hφ'c, hφ'Q, hφ'm, hφ'S, hφ'd⟩ := GlobalTheory.T.exists_unitary_equiv_conj_of_gram_transpose_eq_neg D (sgn ε S) Th (Equiv.refl _) hT'
  obtain ⟨φ, hφc, hφQ, hφm, hφS, hφd⟩ := GlobalTheory.T.exists_unitary_equiv_inv_transpose_of_gram_inv D X Sh e.symm hS'
  obtain ⟨L, hL1, -, hLc, hLc', hLQ, hLi, hLf⟩ := GlobalTheory.T.exists_transposeGram_coordinate_homeomorph_symplectic D (sgn ε S) X Sh Th (Equiv.refl _) e.symm
  have hsy := GlobalTheory.T.symplectic_hom_transpose_gram_darboux D (sgn ε S) X Sh Th (Equiv.refl _) e.symm hT' hS'
  have hLx : ∀ u : Matrix (Fin S.rank) (Fin d) (AE D), L u = (HMul.hMul (uᵀ.submatrix e id) ((sgn ε S).gram.map (incA D)) :
      Matrix (Fin X.rank) (Fin S.rank) (AE D)) := fun u => (hL1 u).trans rfl
  have hcL : ∀ u, cS u = L u := fun u => by
    rw [hcS, hLx, sgn_gram_eq]
    rfl

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

  obtain ⟨ω', hω'', hrel⟩ := GlobalTheory.T.isWeilDatum_comp_group_swapping_symplectic_equiv D Bs.ψ (sgn ε S) X Sh Th hdX.symm rfl L φ.toMonoidHom φ'.toMonoidHom hLc hLc' hLQ
    (fun x y => by rw [hL1, hL1]; exact hsy x y) hLi hLf hφc hφ'c hφQ hφ'Q hact hφS hφ'S hφd hφ'd χ χ' (ω.toSgn ε) hω'
  have hA : Vs.J = Th.gramᵀ := hTt.symm
  have hB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • Sh.gram⁻¹) := by
    rw [hSg]
    exact neg_incM_eq Ws.J hJd hξ
  obtain ⟨om, hom⟩ := GlobalTheory.T.exists_weilDatum_transport_adelicSchwartz_thetaTransform D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω''
  have h2 := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have h3 := GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have h4 := GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have h5 := GlobalTheory.T.continuous_transported_weilDatum_adelicSchwartz D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have h6 := GlobalTheory.T.exists_doubledWeil_blockEmbedding_acts_on_first_boxFactor D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have h7 := GlobalTheory.T.exists_doubled_schrodingerModel_transposed_siegelRule D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have hsp : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) Bs.ψ M.co
      (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) om := ⟨⟨h2.1, h2.2, h3⟩, h4, h5⟩
  have hW : M.IsWeil Bs.ψ χ χ' om :=
    ⟨⟨GlobalTheory.WeilSchrodinger.isUSplitting_inr hsp, h6⟩, ⟨GlobalTheory.WeilSchrodinger.transD _ M.co, GlobalTheory.WeilSchrodinger.transD_e M.co,
      GlobalTheory.WeilSchrodinger.isUSplitting_inl hsp, h7⟩, h5⟩
  refine ⟨om, hW, ?_⟩

  intro Φ f hΦ g h
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
  have hb : Formalism.L2.Theta.mt Sh (φ.symm h) = ((kapX X e hJW h)⁻¹).1.1ᵀ :=
    eq_inv_transpose _ _ _ _ hP (Units.mul_inv (kapX X e hJW h).1) h1
  obtain ⟨hs, ht⟩ := hom (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S _ hJ g) (kapX X e hJW h) (φ.symm h) (φ'.symm ((ofSgn ε S).symm g))
    ha hb Φ hΦ.1
  refine ⟨hs, fun u => ?_⟩
  have hΦf : GlobalTheory.WeilSchrodinger.thetaTr D.host.F M.co Bs.ψ Φ = fun u => f (L u) := funext fun u => by
    rw [← hcL]
    exact hΦ.2 u
  have k1 := congrFun ht u
  have k2 := congrArg (fun F => ω' (φ.symm h, φ'.symm ((ofSgn ε S).symm g)) F u) hΦf
  have k3 := congrFun (hrel (φ.symm h) (φ'.symm ((ofSgn ε S).symm g)) f) u
  rw [hcL]
  refine k1.trans (k2.trans (k3.trans ?_))
  simp [WRep.toSgn]

end GlobalTheory.SquareAgree
