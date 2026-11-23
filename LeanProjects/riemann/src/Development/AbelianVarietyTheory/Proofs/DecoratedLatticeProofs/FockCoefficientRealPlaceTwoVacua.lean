import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsMatrixCoefficientsEqFockRepresentatio
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsAtOneRealPlaceOverVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperators
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsRealPlaceActAsFockPolynomials
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceGroupsActUnitarilyWeaklyOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoGradedIsometry
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyGrpData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyFockModelUnitaryDualPair

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacCoefAtPlace

open GlobalTheory.ArchRec GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

theorem foldr_lin {ι X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}
    (hA : ∀ i f, P f → P (A i f))
    (hl : ∀ i (a : ℂ) f f', P f → P f' → A i (a • f + f') = a • A i f + A i f')
    (a : ℂ) {f f' : X → ℂ} (hf : P f) (hf' : P f') (l : List ι) :
    l.foldr (fun i g => A i g) (a • f + f') =
      a • l.foldr (fun i g => A i g) f + l.foldr (fun i g => A i g) f' := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact hl i a _ _ (GlobalTheory.FockIndep.foldr_mem hA hf l) (GlobalTheory.FockIndep.foldr_mem hA hf' l)

theorem pure_lin {ι X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}
    (hA : ∀ i f, P f → P (A i f))
    (hl : ∀ i (a : ℂ) f f', P f → P f' → A i (a • f + f') = a • A i f + A i f')
    (a : ℂ) {f f' : X → ℂ} (hf : P f) (hf' : P f') (Q : MvPolynomial ι ℂ) :
    pureTensorL A (a • f + f') Q = a • pureTensorL A f Q + pureTensorL A f' Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial]
    unfold opPow
    rw [foldr_lin hA hl a hf hf', smul_add, smul_comm c a]
  | add p q hp hq =>
    rw [map_add, map_add, map_add, hp, hq, smul_add]
    abel

theorem polar {Y : Type} [AddCommGroup Y] [Module ℂ Y] {vac : Y → Prop}
    (hv : ∀ (a : ℂ) x y, vac x → vac y → vac (a • x + y)) (E : Y → Y → ℂ)
    (h1 : ∀ (a : ℂ) x y z, vac x → vac y → vac z → E (a • x + y) z = a * E x z + E y z)
    (h2 : ∀ (a : ℂ) x y z, vac x → vac y → vac z → E z (a • x + y) = conj a * E z x + E z y)
    (h0 : ∀ x, vac x → E x x = 0) {x y : Y} (hx : vac x) (hy : vac y) : E x y = 0 := by
  have hs : ∀ a : ℂ, E (a • x + y) (a • x + y) = a * (conj a * E x x + E x y) + (conj a * E y x + E y y) := by
    intro a
    rw [h1 a x y _ hx hy (hv a x y hx hy), h2 a x y x hx hy hx, h2 a x y y hx hy hy]
  have e1 := hs 1
  have e2 := hs Complex.I
  rw [h0 _ (hv _ x y hx hy), h0 x hx, h0 y hy] at e1 e2
  simp only [map_one, Complex.conj_I] at e1 e2
  linear_combination (-1 / 2 : ℂ) * e1 + (Complex.I / 2) * e2 + ((E x y - E y x) / 2) * Complex.I_sq

theorem exists_signCompat {n : ℕ} (ε : Fin n → Bool) : ∃ (p q : ℕ) (e : Ix p q ≃ Fin n), SignCompat ε e := by
  classical
  refine ⟨Fintype.card {a : Fin n // ε a = true}, Fintype.card {a : Fin n // ¬ ε a = true},
    (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans (Equiv.sumCompl _), ?_⟩
  intro a
  rcases a with a | a
  · simpa using ((Fintype.equivFin {a : Fin n // ε a = true}).symm a).2
  · simpa using ((Fintype.equivFin {a : Fin n // ¬ ε a = true}).symm a).2

theorem fockIp_one {ι : Type} : fockIp (1 : MvPolynomial ι ℂ) 1 = 1 := by
  classical
  simp [fockIp, MvPolynomial.support_one]

theorem exists_cov {p q n : ℕ} (T : GrpData p q) {fr G : Mn n} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n}
    (hfr : IsUnit fr) (hG : frᴴ * Formalism.REAL.Jm ε * fr = G) (hs : SignCompat ε e) {g : Mn n}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) : ∃ x : T.G, phiFr fr true e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) = g := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hfr
  have e1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have e2 : fr⁻¹ * fr = 1 := Matrix.nonsing_inv_mul _ hd
  have hg' : gᴴ * G * g = G := hg
  set h : Mn n := fr * g * fr⁻¹ with hh
  have hJ : hᴴ * Formalism.REAL.Jm ε * h = Formalism.REAL.Jm ε := by
    calc hᴴ * Formalism.REAL.Jm ε * h = (fr⁻¹)ᴴ * (gᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * g) * fr⁻¹ := by
          simp only [hh, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (fr⁻¹)ᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * fr⁻¹ := by rw [hG, hg']
      _ = (fr * fr⁻¹)ᴴ * Formalism.REAL.Jm ε * (fr * fr⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [e1]; simp
  have hJ0 : Matrix.reindex e.symm e.symm (Formalism.REAL.Jm ε) = Formalism.UG.Jpq p q := by
    rw [← reindex_form hs]; simp
  set Y : Mat p q := Matrix.reindex e.symm e.symm h with hY
  have hYJ : Yᴴ * Formalism.UG.Jpq p q * Y = Formalism.UG.Jpq p q := by
    rw [← hJ0, hY]
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hJ]
  have hJc : (Formalism.UG.Jpq p q).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp [Formalism.UG.Jpq, Matrix.one_apply] <;> split_ifs <;> simp
  set Z : Mat p q := Y.map (starRingEnd ℂ) with hZ
  have hZJ : Zᴴ * Formalism.UG.Jpq p q * Z = Formalism.UG.Jpq p q := by
    have := congrArg (fun A : Mat p q => A.map (starRingEnd ℂ)) hYJ
    simp only [Matrix.map_mul, hJc] at this
    rw [hZ]
    convert this using 3
    ext a b; simp [Matrix.conjTranspose_apply]
  have hJJ : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
    simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
  have hZu : IsUnit Z.det := by
    refine Matrix.isUnit_det_of_left_inverse (B := Formalism.UG.Jpq p q * Zᴴ * Formalism.UG.Jpq p q) ?_
    rw [show Formalism.UG.Jpq p q * Zᴴ * Formalism.UG.Jpq p q * Z = Formalism.UG.Jpq p q * (Zᴴ * Formalism.UG.Jpq p q * Z) by
      simp only [Matrix.mul_assoc], hZJ, hJJ]
  let gZ : GL (Ix p q) ℂ := Matrix.GeneralLinearGroup.mk'' Z hZu
  have hmem : gZ ∈ Formalism.UG.Upq p q := by
    show Formalism.UG.cT (starRingEnd ℂ) Z * Formalism.UG.Jpq p q * Z = Formalism.UG.Jpq p q
    rw [show Formalism.UG.cT (starRingEnd ℂ) Z = Zᴴ by ext a b; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]]
    exact hZJ
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((gZ : Mat p q).det) two_pos
  have h0 : w ≠ 0 := by
    rintro rfl
    exact gZ.det_ne_zero (by rw [← hw]; simp)
  obtain ⟨x, hx, -⟩ := T.bij gZ hmem (Units.mk0 w h0) hw
  refine ⟨x, ?_⟩
  have hc : ((T.cov x : GL (Ix p q) ℂ) : Mat p q) = Z := by rw [hx.1]; rfl
  rw [hc, phiFr, phi, if_pos rfl]
  have hb : barMat e Z = h := by
    ext a b; simp [barMat, hZ, hY]
  rw [hb, hh, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul, Matrix.mul_assoc, e2, Matrix.mul_one]

end GlobalTheory.VacCoefAtPlace

namespace GlobalTheory.VacCoefAtPlace

open GlobalTheory.ArchRec GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

theorem ptAt_theta (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (sS : Mn V.rank) (sT : Mn W.rank)
    (BS : Mn V.rank) (BT : Mn W.rank) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (P : LPol W.rank V.rank) :
    IsThetaFunO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ sS sT BS BT f P) :=
  GlobalTheory.FockIndep.pure_mem (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun a _ => GlobalTheory.OrientedHeis.theta_smul a)
    (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) hf P

theorem ptAt_lin (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (sS : Mn V.rank) (sT : Mn W.rank)
    (BS : Mn V.rank) (BT : Mn W.rank) (a : ℂ) {f f' : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hf' : IsThetaFunO ψ V W f') (P : LPol W.rank V.rank) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ sS sT BS BT (a • f + f') P =
      a • GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ sS sT BS BT f P + GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ sS sT BS BT f' P :=
  pure_lin (P := IsThetaFunO ψ V W) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h)
    (fun _ b _ _ h h' => by
      rw [GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ (GlobalTheory.OrientedHeis.theta_smul b h) h',
        GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ b h]) a hf hf' P

theorem vac_lin (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (J : Matrix (Fin W.rank) (Fin V.rank) ℂ → Matrix (Fin W.rank) (Fin V.rank) ℂ) (a : ℂ) {f f' : WO V W → ℂ}
    (hf : IsThetaFunO ψ V W f) (hf' : IsThetaFunO ψ V W f') (vf : IsFockVacAt (heisO ψ V W) θ τ J f)
    (vf' : IsFockVacAt (heisO ψ V W) θ τ J f') : IsFockVacAt (heisO ψ V W) θ τ J (a • f + f') := fun z => by
  rw [GlobalTheory.FockIndep.annih_add hψ hθ _ _ _ (GlobalTheory.OrientedHeis.theta_smul a hf) hf',
    GlobalTheory.FockIndep.annih_smul hψ hθ _ _ _ a hf, vf z, vf' z, smul_zero, add_zero]

theorem coef_vac {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    {m : Measure (WO V W)} {X : Set (WO V W)} (hX : IsCovolOne (ratL W V) m X) (τ : D.what₂.Tau)
    {g : Mn V.rank} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (P Q : LPol W.rank V.rank) :
    ∃ K : ℂ, ∀ f, IsThetaFunO ψ V W f → IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f → f ≠ 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X
                   (ω (atTau θ V τ g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) f P))
                   (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) f Q) =
        GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f * K := by
  have hψ := hω.std
  obtain ⟨hμ, h𝓕, -⟩ := hX
  have fS := isFrameOf_model M τ
  have fT := isFrameOf_model M' τ
  obtain ⟨p, q, e, he⟩ := exists_signCompat (M.ε τ)
  obtain ⟨r, s, e', he'⟩ := exists_signCompat (M'.ε τ)
  by_cases hn : 1 ≤ p + q
  · obtain ⟨aS, haS⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ χS _ τ hθ hω.hecS hω.resS
    obtain ⟨aT, haT⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ χT _ τ hθ hω.hecT hω.resT
    obtain ⟨mT, hmT, -⟩ := id haT
    obtain ⟨κ, k1, -, k3⟩ := GlobalTheory.ArchRec.SignedRename.exists_isPolyIso_graded_isometry p q r s _ _ (M.ε τ) (M'.ε τ)
      e e' he he'
    obtain ⟨T₀⟩ := GlobalTheory.DetSqrtCover.nonempty_grpData (p * r + q * s) (p * s + q * r)
    obtain ⟨T₁⟩ := GlobalTheory.DetSqrtCover.nonempty_grpData p q
    obtain ⟨T₂⟩ := GlobalTheory.DetSqrtCover.nonempty_grpData r s
    obtain ⟨F⟩ := GlobalTheory.nonempty_fockData_pair p q r s T₀ T₁ T₂
    obtain ⟨g₁, hg₁⟩ := exists_cov T₁ (M.fr_unit τ) (M.fr_gram τ) he hg
    refine ⟨((T₁.sq g₁ : ℂˣ) : ℂ) ^ mT * ⟪F.ι (κ Q), F.π (g₁, 1) (F.ι (κ P))⟫_ℂ, fun f hf hv h0 => ?_⟩
    obtain ⟨c1, c2⟩ := GlobalTheory.OnePlaceFock.fock_at_one_place D ψ θ V W τ hψ hθ _ _ _ _ _ _ fS fT f hf hv
    obtain ⟨cinj, c3⟩ := c2 h0
    obtain ⟨N, n1, n2⟩ := c3 m X hμ h𝓕
    have hL := GlobalTheory.ArchRec.LieAtPlace.lieAt_of_vacAt D ψ θ V W χS χT ω τ hθ hω aS aT haS haT _ _ _ _ _ _ fS fT f hf hv
    let pt : LPol W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorL (fun k : Fin W.rank × Fin V.rank =>
      aPlus (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) (unitMap (M.fr τ)⁻¹ (M'.fr τ)⁻¹ k.1 k.2)) f
    obtain ⟨s1, -⟩ := GlobalTheory.ArchRec.SideAt.side_at D ψ θ V W ω τ hθ _ _ _ _ _ _ fS fT aS aT pt cinj hL p q r s e e' he he'
      κ k1
    obtain ⟨Θ, t1, -⟩ := GlobalTheory.ThetaL2InnerProduct.exists_l2_unitary_theta_of_fundamentalDomain D ψ θ V W χS χT ω τ hθ hω (M.fr τ) (M.ε τ) (M'.fr τ) (M'.ε τ)
      aS aT pt c1 hL m X hμ h𝓕
    have hF : Fischer pt (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X) κ N :=
      ⟨n1, fun P Q => by rw [k3]; exact n2 P Q⟩
    have hC := GlobalTheory.ArchRec.FockCoef.coef_of_side p q r s V.rank T₀ T₁ T₂ F _ _ (gramAt D V τ) (M.fr τ) (M.ε τ) true e
      (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.actSrc θ ω τ) pt (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X) Θ κ aT mT N hn (M.fr_unit τ) (M.fr_gram τ) he hmT s1 t1 hF
    have hN : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f = N := by
      have := n2 1 1
      rw [LinearEquiv.refl_apply, fockIp_one, mul_one] at this
      simpa only [GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt, GlobalTheory.FockIndep.pure_one] using this
    have h2 := hC.2.2 g₁ P Q
    rw [hg₁] at h2
    rw [hN, ← mul_assoc]
    exact h2
  · have hV : V.rank = 0 := by
      have := Fintype.card_congr e
      simp at this
      omega
    have g1 : g = 1 := by
      ext i j
      have := i.2
      omega
    refine ⟨fockIp P Q, fun f hf hv h0 => ?_⟩
    obtain ⟨-, c2⟩ := GlobalTheory.OnePlaceFock.fock_at_one_place D ψ θ V W τ hψ hθ _ _ _ _ _ _ fS fT f hf hv
    obtain ⟨-, c3⟩ := c2 h0
    obtain ⟨N, -, n2⟩ := c3 m X hμ h𝓕
    have hN : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f = N := by
      have := n2 1 1
      rw [LinearEquiv.refl_apply, fockIp_one, mul_one] at this
      simpa only [GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt, GlobalTheory.FockIndep.pure_one] using this
    rw [g1, GlobalTheory.PointAtPlaceHom.atTau_one hθ, Prod.mk_one_one, map_one, Module.End.one_apply, hN]
    exact n2 P Q

end GlobalTheory.VacCoefAtPlace

namespace GlobalTheory.VacCoefAtPlace

open GlobalTheory.ArchRec GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

theorem coef_at_place : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (m : Measure (WO V W)) (X : Set (WO V W)), IsCovolOne (ratL W V) m X → ∀ (τ : D.what₂.Tau) (f F F' : WO V W → ℂ), (∀ x ∈ [f, F, F'], IsThetaFunO ψ V W x ∧ IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) x) → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ P Q : LPol W.rank V.rank, let pt := GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ); GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (atTau θ V τ g, 1) (pt F P)) (pt F' Q) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f = GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (atTau θ V τ g, 1) (pt f P)) (pt f Q) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X F F' := by
  intro D V W S S' M M' θ ψ χS χT ω hθ hω m X hX τ f F F' hall g hg P Q pt
  have hψ := hω.std
  obtain ⟨K, hK⟩ := coef_vac M M' hθ hω hX τ hg P Q
  obtain ⟨hμ, h𝓕, -⟩ := hX
  let vac : (WO V W → ℂ) → Prop := fun x =>
    IsThetaFunO ψ V W x ∧ IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) x
  have th : ∀ x y, vac x → vac y → IsThetaFunO ψ V W (ω (atTau θ V τ g, 1) (pt x P)) ∧ IsThetaFunO ψ V W (pt y Q) :=
    fun x y hx hy => ⟨hω.om_pres _ _ (ptAt_theta hψ hθ _ _ _ _ _ hx.1 P), ptAt_theta hψ hθ _ _ _ _ _ hy.1 Q⟩
  have hv : ∀ (a : ℂ) x y, vac x → vac y → vac (a • x + y) := fun a x y hx hy =>
    ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul a hx.1) hy.1, vac_lin hψ hθ τ _ a hx.1 hy.1 hx.2 hy.2⟩
  let E : (WO V W → ℂ) → (WO V W → ℂ) → ℂ := fun x y =>
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (atTau θ V τ g, 1) (pt x P)) (pt y Q) - K * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X x y
  have h1 : ∀ (a : ℂ) x y z, vac x → vac y → vac z → E (a • x + y) z = a * E x z + E y z := by
    intro a x y z hx hy hz
    simp only [E, pt]
    rw [ptAt_lin hψ hθ _ _ _ _ _ a hx.1 hy.1, map_add, map_smul]
    simp only [GlobalTheory.ThetaL2InnerProduct.ipTh_eq]
    rw [GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 (GlobalTheory.OrientedHeis.theta_smul a (th x z hx hz).1) (th y z hy hz).1
        (th x z hx hz).2, GlobalTheory.Size.ipO_smul_left,
      GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 (GlobalTheory.OrientedHeis.theta_smul a hx.1) hy.1 hz.1, GlobalTheory.Size.ipO_smul_left]
    ring
  have h2 : ∀ (a : ℂ) x y z, vac x → vac y → vac z → E z (a • x + y) = conj a * E z x + E z y := by
    intro a x y z hx hy hz
    simp only [E, pt]
    rw [ptAt_lin hψ hθ _ _ _ _ _ a hx.1 hy.1]
    simp only [GlobalTheory.ThetaL2InnerProduct.ipTh_eq]
    rw [GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 (th z x hz hx).1 (GlobalTheory.OrientedHeis.theta_smul a (th z x hz hx).2)
        (th z y hz hy).2, GlobalTheory.Size.ipO_smul_right,
      GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 hz.1 (GlobalTheory.OrientedHeis.theta_smul a hx.1) hy.1, GlobalTheory.Size.ipO_smul_right]
    ring
  have h0 : ∀ x, vac x → E x x = 0 := by
    intro x hx
    by_cases hx0 : x = 0
    · have z0 : ∀ R, pt 0 R = 0 := fun R => by
        have h := ptAt_lin hψ hθ τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) (-1)
          (GlobalTheory.ThetaL2InnerProduct.thetaSpace ψ V W).zero_mem (GlobalTheory.ThetaL2InnerProduct.thetaSpace ψ V W).zero_mem R
        rw [smul_zero, add_zero, neg_one_smul, neg_add_cancel] at h
        exact h
      simp only [E, hx0, z0, map_zero, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh]
      simp
    · simp only [E]
      rw [hK x hx.1 hx.2 hx0]
      ring
  have key : ∀ x y, vac x → vac y →
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (atTau θ V τ g, 1) (pt x P)) (pt y Q) = K * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X x y :=
    fun x y hx hy => sub_eq_zero.1 (polar hv E h1 h2 h0 hx hy)
  have hf : vac f := hall f (by simp)
  have hF : vac F := hall F (by simp)
  have hF' : vac F' := hall F' (by simp)
  rw [key F F' hF hF', key f f hf hf]
  ring

end GlobalTheory.VacCoefAtPlace
