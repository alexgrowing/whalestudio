import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentMatrixLocalSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixSandwichTraceEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrderStatement

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

def cornerHom {Γ R : Type} [CommRing Γ] [CommRing R] {h n : ℕ}
    (ρ : Γ →+* Matrix (Fin h) (Fin h) R) (e : Γ) (i : Matrix (Fin h) (Fin n) R)
    (q : Matrix (Fin n) (Fin h) R) (hqi : q * i = 1) (hiq : i * q = ρ e) :
    Γ →+* Matrix (Fin n) (Fin n) R where
  toFun x := q * ρ x * i
  map_one' := by simp [hqi]
  map_mul' x y := by
    have h1 : q * ρ e = q := by rw [← hiq, ← Matrix.mul_assoc, hqi, Matrix.one_mul]
    have h2 : ρ x * ρ e = ρ e * ρ x := by rw [← map_mul, ← map_mul, mul_comm]
    calc q * ρ (x * y) * i = (q * ρ e) * (ρ x * ρ y) * i := by rw [h1, map_mul]
      _ = q * (ρ x * ρ e) * ρ y * i := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = q * ρ x * i * (q * ρ y * i) := by rw [← hiq]; simp only [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul]

theorem corner_lift {Γ Λ R : Type} [CommRing Γ] [CommRing Λ] [CommRing R] {h n : ℕ}
    (π : Γ →+* Λ) (hπ : Function.Surjective π) (e : Γ) (hk : RingHom.ker π = Ideal.span {1 - e})
    (ρ : Γ →+* Matrix (Fin h) (Fin h) R) (i : Matrix (Fin h) (Fin n) R)
    (q : Matrix (Fin n) (Fin h) R) (hqi : q * i = 1) (hiq : i * q = ρ e) :
    ∃ ρ' : Λ →+* Matrix (Fin n) (Fin n) R, ∀ x, ρ' (π x) = q * ρ x * i := by
  have hker : RingHom.ker π ≤ RingHom.ker (cornerHom ρ e i q hqi hiq) := by
    rw [hk, Ideal.span_le, Set.singleton_subset_iff]
    show cornerHom ρ e i q hqi hiq (1 - e) = 0
    rw [map_sub, map_one]
    show 1 - q * ρ e * i = 0
    rw [← hiq, ← Matrix.mul_assoc, hqi, Matrix.one_mul, hqi, sub_self]
  exact ⟨π.liftOfSurjective hπ ⟨_, hker⟩, fun x => π.liftOfRightInverse_comp_apply _ _ ⟨_, hker⟩ x⟩

theorem phiInv_ofPadic_apply (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (c : ℤ_[p]) :
    phiInv p O (ofPadic p O c) = ofPadic p O c := by
  unfold phiInv ofPadic
  ext n
  simp only [RingHom.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (Subsingleton.elim
    (((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p))) (ZMod.castHom (dvd_refl p) (PreTilt O p))) _

theorem datum_idempotent_part : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Γ : Type) [CommRing Γ] [Algebra ℤ_[p] Γ] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (π : Γ →ₐ[ℤ_[p]] Λ) (e : Γ), IsIdempotentElem e → Function.Surjective π → RingHom.ker π = Ideal.span {1 - e} → ∀ (h : ℕ) (D : Datum ε h Γ), ∃ (h' : ℕ) (D' : Datum ε h' Λ) (iT : Matrix (Fin h) (Fin h') ℤ_[p]) (pT : Matrix (Fin h') (Fin h) ℤ_[p]) (iM : Matrix (Fin h) (Fin h') (Ainf p O)) (pM : Matrix (Fin h') (Fin h) (Ainf p O)), pT * iT = 1 ∧ iT * pT = D.ρT e ∧ pM * iM = 1 ∧ iM * pM = D.ρM e ∧ D'.F = pM * D.F * iT.map (ofPadic p O) ∧ D'.G = pT.map (ofPadic p O) * D.G * iM ∧ (∀ x, D'.ρT (π x) = pT * D.ρT x * iT) ∧ ∀ x, D'.ρM (π x) = pM * D.ρM x * iM := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Γ _ _ Λ _ _ π e he hπ hk h D
  obtain ⟨hdom, hloc, -, -, hν, hξ, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  obtain ⟨-, -, -, hΨ, hΨ'⟩ := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Γ h D
  have hμ : mu ε ≠ 0 := by
    rw [← xi_mul_nu]
    refine mul_ne_zero hξ ?_
    intro h0
    exact hν (by rw [h0, map_zero])
  obtain ⟨n, iT, pT, hT1, hT2, hT3⟩ := GlobalTheory.T.idempotent_matrix_local_split ℤ_[p] h (D.ρT e) (by rw [← map_mul, he.eq])
  obtain ⟨n', iM, pM, hM1, hM2, hM3⟩ :=
    GlobalTheory.T.idempotent_matrix_local_split (Ainf p O) h (D.ρM e) (by rw [← map_mul, he.eq])
  have htr := (GlobalTheory.T.matrix_sandwich_trace_eq (Ainf p O) h (mu ε) D.F D.G _ _ hμ D.G_mul_F (D.F_act e)).2.2
  have hnn : n' = n := by
    have h1 : ((D.ρT e).map (ofPadic p O)).trace = (n : Ainf p O) := by
      rw [← AddMonoidHom.map_trace (ofPadic p O), hT3, map_natCast]
    rw [hM3, h1] at htr
    have h2 := congrArg (fun x => algebraMap O C (WittVector.fontaineTheta O p x)) htr
    simpa using h2
  subst hnn
  obtain ⟨rT, hrT⟩ := corner_lift (π : Γ →+* Λ) hπ e hk (D.ρT : Γ →+* _) iT pT hT1 hT2
  obtain ⟨rM, hrM⟩ := corner_lift (π : Γ →+* Λ) hπ e hk D.ρM iM pM hM1 hM2
  have hrT' : ∀ x, rT (π x) = pT * D.ρT x * iT := hrT
  have hrM' : ∀ x, rM (π x) = pM * D.ρM x * iM := hrM
  have hpM : pM * D.ρM e = pM := by rw [← hM2, ← Matrix.mul_assoc, hM1, Matrix.one_mul]
  have hiM : D.ρM e * iM = iM := by rw [← hM2, Matrix.mul_assoc, hM1, Matrix.mul_one]
  have hiT : D.ρT e * iT = iT := by rw [← hT2, Matrix.mul_assoc, hT1, Matrix.mul_one]
  have hφ : (iT.map (ofPadic p O)).map (phiInv p O) = iT.map (ofPadic p O) := by
    ext1 i j
    simp only [Matrix.map_apply, phiInv_ofPadic_apply]
  have hφe : iM.map (phiInv p O) * pM.map (phiInv p O) = (D.ρM e).map (phiInv p O) := by
    rw [← Matrix.map_mul, hM2]
  refine ⟨n',
    { F := pM * D.F * iT.map (ofPadic p O)
      G := pT.map (ofPadic p O) * D.G * iM
      Ψ := pM * D.Ψ * iM.map (phiInv p O)
      Ψ' := pM.map (phiInv p O) * D.Ψ' * iM
      ρT := { rT with
        commutes' := by
          intro c
          show rT (algebraMap ℤ_[p] Λ c) = _
          rw [← π.commutes, hrT', AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
            Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hT1] }
      ρM := rM
      G_mul_F := ?_
      F_eq := ?_
      Ψ_mul := ?_
      F_act := ?_ }, iT, pT, iM, pM, hT1, hT2, hM1, hM2, rfl, rfl, hrT', hrM'⟩
  · calc pT.map (ofPadic p O) * D.G * iM * (pM * D.F * iT.map (ofPadic p O))
        = pT.map (ofPadic p O) * D.G * ((iM * pM) * D.F) * iT.map (ofPadic p O) := by
          simp only [Matrix.mul_assoc]
      _ = pT.map (ofPadic p O) * (D.G * D.F) * ((D.ρT e).map (ofPadic p O) * iT.map (ofPadic p O)) := by
          rw [hM2, ← D.F_act e]; simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [← Matrix.map_mul, hiT, D.G_mul_F, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
            ← Matrix.map_mul, hT1, Matrix.map_one _ (map_zero _) (map_one _)]
  · symm
    calc pM * D.Ψ * iM.map (phiInv p O) * (pM * D.F * iT.map (ofPadic p O)).map (phiInv p O)
        = pM * (D.Ψ * (iM.map (phiInv p O) * pM.map (phiInv p O))) * D.F.map (phiInv p O) *
            iT.map (ofPadic p O) := by
          rw [Matrix.map_mul, Matrix.map_mul, hφ]; simp only [Matrix.mul_assoc]
      _ = (pM * D.ρM e) * (D.Ψ * D.F.map (phiInv p O)) * iT.map (ofPadic p O) := by
          rw [hφe, hΨ]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hpM, ← D.F_eq]
  · calc pM * D.Ψ * iM.map (phiInv p O) * (pM.map (phiInv p O) * D.Ψ' * iM)
        = pM * D.Ψ * ((iM.map (phiInv p O) * pM.map (phiInv p O)) * D.Ψ') * iM := by
          simp only [Matrix.mul_assoc]
      _ = pM * (D.Ψ * D.Ψ') * (D.ρM e * iM) := by
          rw [hφe, ← hΨ']; simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hiM, D.Ψ_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hM1]
  · intro a
    obtain ⟨x, rfl⟩ := hπ a
    show _ * (rT (π x)).map (ofPadic p O) = rM (π x) * _
    have hc : D.ρM e * D.ρM x = D.ρM x * D.ρM e := by rw [← map_mul, ← map_mul, mul_comm]
    rw [hrT', hrM']
    calc pM * D.F * iT.map (ofPadic p O) * (pT * D.ρT x * iT).map (ofPadic p O)
        = pM * (D.F * (iT * pT).map (ofPadic p O)) * (D.ρT x).map (ofPadic p O) *
            iT.map (ofPadic p O) := by
          simp only [Matrix.map_mul, Matrix.mul_assoc]
      _ = pM * D.ρM e * (D.F * (D.ρT x).map (ofPadic p O)) * iT.map (ofPadic p O) := by
          rw [hT2, D.F_act e]; simp only [Matrix.mul_assoc]
      _ = pM * (D.ρM e * D.ρM x) * D.F * iT.map (ofPadic p O) := by
          rw [D.F_act x]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hc, ← hM2]; simp only [Matrix.mul_assoc]

end GlobalTheory.DetInv
