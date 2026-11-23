import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionArtinianRing
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WittS

section Abstract

variable {A B : Type} [CommRing A] [CommRing B]

theorem map_mul_of_mul (Q : B →+ A) (hQ : ∀ y y', Q (y * y') = Q y * Q y')
    {a b c : Type} [Fintype b] (X : Matrix a b B) (Y : Matrix b c B) :
    (X * Y).map Q = X.map Q * Y.map Q := by
  ext i j
  simp [Matrix.mul_apply, map_sum, hQ]

theorem exists_lift {m : Type} [Fintype m] [DecidableEq m] (c : A →+* A) (s : B →+* B) (P : A →+* B)
    (Q : B →+ A) (e : A) (hQs : ∀ y, Q (s y) = c (Q y)) (hQP : ∀ x, Q (P x) = e * x)
    (hQ : ∀ y y', Q (y * y') = Q y * Q y') (J : Matrix m m A) (g g' : Matrix m m B)
    (hgg' : g * g' = 1) (hg'g : g' * g = 1) (hU : (g.map s)ᵀ * J.map P * g = J.map P) :
    ∃ h h' : Matrix m m A, h * h' = 1 ∧ h' * h = 1 ∧ (h.map c)ᵀ * J * h = J ∧
      e • (h - 1) = h - 1 ∧
      ∀ (ι : Type) (N N' : Matrix m ι A), e • N = N → e • N' = N' → g * N.map P = N'.map P →
        h * N = N' := by
  have hQ1 : Q 1 = e := by simpa using hQP 1
  have hQe : ∀ y, e * Q y = Q y := fun y => by rw [← hQ1, ← hQ, one_mul]
  have hee : e * e = e := by simpa [hQ1] using hQe 1
  have hce : c e = e := by rw [← hQ1, ← hQs, map_one]
  have hGe : ∀ {a b : Type} (X : Matrix a b B), e • X.map Q = X.map Q := by
    intro a b X
    ext i j
    simp [hQe]
  have hfz : ∀ {a b : Type} (X : Matrix a b B), (1 - e) • X.map Q = 0 := by
    intro a b X
    rw [sub_smul, one_smul, hGe, sub_self]
  have h1Q : (1 : Matrix m m B).map Q = e • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hQ1]
    · simp [Matrix.one_apply_ne hij]
  have hPQ : ∀ {a b : Type} (X : Matrix a b A), (X.map P).map Q = e • X := by
    intro a b X
    ext i j
    simp [hQP]
  have hfe : (1 - e) * (1 - e) = 1 - e := by linear_combination hee
  have hef : e * (1 - e) = 0 := by linear_combination -hee
  have hsum : ∀ {a b : Type} (X : Matrix a b A), e • X + (1 - e) • X = X := by
    intro a b X
    rw [← add_smul]
    simp
  have hmul : ∀ {a b c : Type} [Fintype b] (X : Matrix a b B) (Y : Matrix b c B),
      (X * Y).map Q = X.map Q * Y.map Q := fun X Y => map_mul_of_mul Q hQ X Y
  have hinv : ∀ u v : Matrix m m B, u * v = 1 →
      (u.map Q + (1 - e) • 1) * (v.map Q + (1 - e) • 1) = 1 := by
    intro u v huv
    rw [add_mul, mul_add, mul_add, ← hmul, huv, h1Q]
    simp only [smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hfz, smul_smul, hfe, add_zero,
      zero_add]
    exact hsum 1
  have hstar : ((g.map Q + (1 - e) • (1 : Matrix m m A)).map c)ᵀ =
      ((g.map s)ᵀ).map Q + (1 - e) • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hQs, hce]
    · simp [hQs, hce, Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  refine ⟨g.map Q + (1 - e) • 1, g'.map Q + (1 - e) • 1, hinv _ _ hgg', hinv _ _ hg'g, ?_, ?_, ?_⟩
  · rw [hstar]
    have hJ : ((g.map s)ᵀ).map Q * J * g.map Q = e • J := by
      have h0 : ((g.map s)ᵀ).map Q * (e • J) = ((g.map s)ᵀ).map Q * J := by
        rw [mul_smul_comm, ← smul_mul_assoc, hGe]
      rw [← h0, ← hPQ J, ← hmul, ← hmul, hU]
    have hL : (1 - e) • (((g.map s)ᵀ).map Q * J) = 0 := by
      rw [← smul_mul_assoc, hfz, zero_mul]
    have hR : (1 - e) • (J * g.map Q) = 0 := by
      rw [← mul_smul_comm, hfz, mul_zero]
    simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hJ, hL, hR,
      smul_smul, hfe, add_zero, zero_add]
    exact hsum J
  · have h1 : g.map Q + (1 - e) • (1 : Matrix m m A) - 1 = g.map Q - e • 1 := by
      rw [sub_smul, one_smul]
      abel
    rw [h1, smul_sub, hGe, smul_smul, hee]
  · intro ι N N' hN hN' hg
    have hz : (1 - e) • N = 0 := by
      rw [sub_smul, one_smul, hN, sub_self]
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hz, add_zero]
    have h2 : g.map Q * N = g.map Q * (e • N) := by rw [hN]
    rw [h2, ← hPQ N, ← hmul, hg, hPQ, hN']

end Abstract

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_mem_HR_of_gram (σ : E →ₐ[F] E) (hCM : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J)
    (Ad : Type) [CommRing Ad] [Algebra F Ad] (R : Type) [CommRing R] [Algebra F R]
    [IsArtinianRing R] [IsReduced R] (e : Ad ⊗[F] E)
    (P : Ad ⊗[F] E →+* R ⊗[F] E) (Q : R ⊗[F] E →+ Ad ⊗[F] E)
    (hPinc : ∀ x, P (inclR Ad x) = inclR R x)
    (hPc : ∀ x, P (sigR Ad σ x) = sigR R σ (P x))
    (hQs : ∀ y, Q (sigR R σ y) = sigR Ad σ (Q y)) (hPQ : ∀ y, P (Q y) = y)
    (hQP : ∀ x, Q (P x) = e * x) (hQm : ∀ y y', Q (y * y') = Q y * Q y')
    (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι E) (hΓ : Γ.det ≠ 0)
    (N N' : Matrix (Fin M) ι (Ad ⊗[F] E)) (hN : e • N = N) (hN' : e • N' = N')
    (hG : (HMul.hMul (N.map (sigR Ad σ))ᵀ (HMul.hMul (J.map (inclR Ad) : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N : Matrix (Fin M) ι (Ad ⊗[F] E)) : Matrix ι ι (Ad ⊗[F] E)) = e • Γ.map (inclR Ad))
    (hG' : (HMul.hMul (N'.map (sigR Ad σ))ᵀ (HMul.hMul (J.map (inclR Ad) : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N' : Matrix (Fin M) ι (Ad ⊗[F] E)) : Matrix ι ι (Ad ⊗[F] E)) = e • Γ.map (inclR Ad)) :
    ∃ h : HR Ad σ J, e • ((h.1 : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) - 1) =
        (h.1 : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) - 1 ∧
      (HMul.hMul (h.1 : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N : Matrix (Fin M) ι (Ad ⊗[F] E)) = N' := by
  have hQ1 : Q 1 = e := by simpa using hQP 1
  have hPe : P e = 1 := by rw [← hQ1, hPQ]
  let eqv := Fintype.equivFin ι
  have gramX : ∀ N₀ : Matrix (Fin M) ι (Ad ⊗[F] E),
      (HMul.hMul (N₀.map (sigR Ad σ))ᵀ (HMul.hMul (J.map (inclR Ad) : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N₀ : Matrix (Fin M) ι (Ad ⊗[F] E)) : Matrix ι ι (Ad ⊗[F] E)) = e • Γ.map (inclR Ad) →
      gramR R σ J (fun a i => P (N₀ i (eqv.symm a))) =
        (Γ.submatrix eqv.symm eqv.symm).map (inclR R) := by
    intro N₀ h₀
    ext a b
    have h := congrArg (fun X : Matrix ι ι (Ad ⊗[F] E) => P (X (eqv.symm a) (eqv.symm b))) h₀
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
      smul_eq_mul, map_sum, map_mul, hPc, hPe, one_mul, hPinc, Finset.mul_sum] at h
    simp only [gramR, hR, Formalism.UG.hform, JR, Matrix.map_apply, Matrix.submatrix_apply, mul_assoc]
    exact h
  have hXY := (gramX N hG).trans (gramX N' hG').symm
  have hdet : IsUnit (gramR R σ J (fun a i => P (N i (eqv.symm a)))).det := by
    rw [gramX N hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_submatrix_equiv_self]
    exact (isUnit_iff_ne_zero.mpr hΓ).map _
  obtain ⟨hU, hact⟩ := GlobalTheory.CompanionTheory.SW.WittTuples.exists_actW_eq_of_gramR_eq F E σ hCM M J hJ R _ _ _
    hXY hdet
  let g : GL (Fin M) (R ⊗[F] E) := HeckeCharacterZeroLocus.SiegelWeilU.HA.mat R σ J hU
  have hJP : (J.map (inclR Ad)).map P = J.map (inclR R) := by
    ext i j
    simp [hPinc]
  have hmem : ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (sigR R σ))ᵀ *
      (J.map (inclR Ad)).map P * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (J.map (inclR Ad)).map P := by
    rw [hJP]
    let h' : HeckeCharacterZeroLocus.SiegelWeilU.HR R σ J := hU
    exact h'.2
  have hgN : (HMul.hMul (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (N.map P) : Matrix (Fin M) ι (R ⊗[F] E)) = N'.map P := by
    ext i k
    have := congrFun (congrFun hact (eqv k)) i
    simpa [GlobalTheory.CompanionTheory.SW.actW, HeckeCharacterZeroLocus.SiegelWeilU.actTup, Matrix.mulVec, dotProduct, Matrix.mul_apply, g]
      using this
  obtain ⟨h, h', h1, h2, h3, h4, h5⟩ := exists_lift (sigR Ad σ) (sigR R σ) P Q e hQs hQP hQm
    (J.map (inclR Ad)) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    ((g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (by simp) (by simp) hmem
  let u : GL (Fin M) (Ad ⊗[F] E) := ⟨h, h', h1, h2⟩
  have hu : u ∈ HR Ad σ J := h3
  exact ⟨⟨u, hu⟩, h4, h5 ι N N' hN hN' hgN⟩

end General

theorem exists_unitary_off_S : (∀ (D : D7) (S : Finset (Pl D)) (e : AE D), IsIdem S e → ∃ (R : Type) (_ : CommRing R) (_ : Algebra D.host.F R) (_ : IsArtinianRing R) (_ : IsReduced R) (P : AE D →+* R ⊗[D.host.F] D.host.E) (Q : R ⊗[D.host.F] D.host.E →+ AE D), (∀ x, P (incA D x) = inclR R x) ∧ (∀ x, P (cA D x) = sigR R D.sp.cm.sig (P x)) ∧ (∀ y, Q (sigR R D.sp.cm.sig y) = cA D (Q y)) ∧ (∀ y, P (Q y) = y) ∧ (∀ x, Q (P x) = e * x) ∧ ∀ y y', Q (y * y') = Q y * Q y') → ∀ (D : D7) (V : HSp D) (S : Finset (Pl D)) (e : AE D), IsIdem S e → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι D.host.E), Γ.det ≠ 0 → ∀ N N' : Matrix (Fin V.rank) ι (AE D), e • N = N → e • N' = N' → (HMul.hMul (N.map (cA D))ᵀ (HMul.hMul (gA V) N : Matrix (Fin V.rank) ι (AE D)) : Matrix ι ι (AE D)) = e • Γ.map (incA D) → (HMul.hMul (N'.map (cA D))ᵀ (HMul.hMul (gA V) N' : Matrix (Fin V.rank) ι (AE D)) : Matrix ι ι (AE D)) = e • Γ.map (incA D) → ∃ h : GA D V, e • (mt V h - 1) = mt V h - 1 ∧ (HMul.hMul (mt V h) N : Matrix (Fin V.rank) ι (AE D)) = N' := by
  intro H D V S e he ι _ _ Γ hΓ N N' hN hN' hG hG'
  obtain ⟨R, _, _, _, _, P, Q, hPinc, hPc, hQs, hPQ, hQP, hQm⟩ := H D S e he
  obtain ⟨h, h1, h2⟩ := exists_mem_HR_of_gram D.sp.cm.sig (isCMExt_host D) V.gram (isHermND_gram V)
    (AF D.host.F) R e P Q hPinc hPc hQs hPQ hQP hQm ι Γ hΓ N N' hN hN' hG hG'
  exact ⟨h, h1, h2⟩

end GlobalTheory.CompanionTheory.WittS
