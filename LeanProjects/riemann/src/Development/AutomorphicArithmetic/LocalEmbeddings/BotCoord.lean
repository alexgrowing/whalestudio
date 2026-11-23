import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BotMatch

section Mat

variable {K : Type} [CommRing K] {a d k : Type} [Fintype a] [Fintype d] [Fintype k] [DecidableEq a] [DecidableEq d]
  [DecidableEq k]

theorem coord_fst (e : k ≃ d) (x : Matrix d a K) {G G' : Matrix a a K} (hG : G' * G = 1) (β : Matrix a a K) {b b' : Matrix a a K}
    (hb : b * b' = 1) {c c' : Matrix k k K} (hc : c * c' = 1) (γ : Matrix d d K) :
    (βᵀ * Gᵀ * b) * (b' * ((x * G')ᵀ.submatrix id e) * c'ᵀ) * (γ.submatrix e e * c)ᵀ = (γ * x * β)ᵀ.submatrix id e := by
  have h1 : c'ᵀ * cᵀ = 1 := by rw [← transpose_mul, hc, transpose_one]
  have h2 : Gᵀ * G'ᵀ = 1 := by rw [← transpose_mul, hG, transpose_one]
  have h3 : (x * G')ᵀ.submatrix id e = G'ᵀ * xᵀ.submatrix id e := by
    rw [transpose_mul]; ext i j; simp [Matrix.mul_apply]
  have h4 : (γ * x * β)ᵀ.submatrix id e = βᵀ * (xᵀ.submatrix id e * (γ.submatrix e e)ᵀ) := by
    rw [transpose_submatrix, Matrix.submatrix_mul_equiv, transpose_mul, transpose_mul]
    ext i j; simp [Matrix.mul_apply]
  rw [h3, h4, transpose_mul]
  calc _ = βᵀ * (Gᵀ * (b * b') * G'ᵀ) * xᵀ.submatrix id e * (c'ᵀ * cᵀ) * (γ.submatrix e e)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hb, Matrix.mul_one, h2, h1]; simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]

theorem coord_snd (e : k ≃ d) (y : Matrix a d K) {G G' : Matrix a a K} (hG : G * G' = 1) (β : Matrix a a K) {b b' : Matrix a a K}
    (hb : b * b' = 1) {c c' : Matrix k k K} (hc : c * c' = 1) (H γ : Matrix d d K) (ξ : K) :
    (β * G' * b'ᵀ) * (-(bᵀ * (-G) * ((G' * y).submatrix id e) * (ξ • Hᵀ.submatrix e e)ᵀ * c)) * (c' * γ.submatrix e e) =
      (ξ • (β * (G' * y * H) * γ)).submatrix id e := by
  have h1 : b'ᵀ * bᵀ = 1 := by rw [← transpose_mul, hb, transpose_one]
  have h3 : (G' * y).submatrix id e = G' * y.submatrix id e := by ext i j; simp [Matrix.mul_apply]
  have h4 : (ξ • (β * (G' * y * H) * γ)).submatrix id e = ξ • (β * G' * (y.submatrix id e * H.submatrix e e * γ.submatrix e e)) := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    simp only [Matrix.mul_assoc]
    ext i j; simp [Matrix.mul_apply]
  have h5 : (ξ • Hᵀ.submatrix e e)ᵀ = ξ • H.submatrix e e := rfl
  rw [h3, h4, h5]
  calc _ = ξ • (β * G' * ((b'ᵀ * bᵀ) * (G * G') * y.submatrix id e * H.submatrix e e * (c * c') * γ.submatrix e e)) := by
        simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, neg_neg, smul_neg, Matrix.mul_smul, Matrix.smul_mul]
    _ = _ := by rw [h1, hG, hc]; simp only [Matrix.mul_one, Matrix.one_mul]

end Mat

variable {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem piW_atPl (y : Fv D.host.F v) : piW τ (atPl (splitPrime τ) (complEquiv τ (splitPrime_under τ) y)) = y := by
  classical
  exact (complEquiv τ (splitPrime_under τ)).injective
    (by rw [GlobalTheory.FlipMatch.isPlaceIso_complEquiv τ, (atPl_spec _ _).2, Pi.single_eq_same])

theorem piW_atPl_one : piW τ (atPl (D := D) (splitPrime τ) 1) = 1 := by
  have := piW_atPl τ 1
  rwa [map_one] at this

theorem piW_conj_atPl_one : piW (τ.comp D.sp.cm.sig) (atPl (D := D) (splitPrime τ) 1) = 0 := by
  classical
  exact (complEquiv (τ.comp D.sp.cm.sig) (splitPrime_under _)).injective (by
    rw [GlobalTheory.FlipMatch.isPlaceIso_complEquiv (τ.comp D.sp.cm.sig), (atPl_spec _ _).2,
      Pi.single_eq_of_ne (splitPrime_comp_ne (isCMExt_host D) τ), map_zero])

theorem atPl_mul_eq_zero {z : AE D} (h : piW τ z = 0) : atPl (splitPrime τ) 1 * z = 0 := by
  classical
  refine ae_ext (by rw [RingHom.map_mul, (atPl_spec _ _).1, zero_mul, map_zero]) fun Q => ?_
  rw [RingHom.map_mul, RingHom.map_mul, (atPl_spec _ _).2, map_zero, map_zero]
  by_cases hQ : Q = splitPrime τ
  · subst hQ
    rw [← GlobalTheory.FlipMatch.isPlaceIso_complEquiv τ z, h, map_zero, mul_zero]
  · rw [Pi.single_eq_of_ne hQ, zero_mul]

theorem exists_map_piW {m n : Type} (U : Matrix m n (Fv D.host.F v)) : ∃ u : Matrix m n (AE D), u.map (piW τ) = U :=
  ⟨U.map fun y => atPl (splitPrime τ) (complEquiv τ (splitPrime_under τ) y), Matrix.ext fun _ _ => piW_atPl τ _⟩

theorem piW_incA (x : D.host.E) : piW τ (incA D x) = τ x :=
  (GlobalTheory.FlipMatch.piW_tmul τ 1 x).trans (by rw [map_one, one_mul])

theorem evW_eToEAf (x : D.host.E) : evW τ (eToEAf D x) = τ x := (evW_toEAf τ (incA D x)).trans (piW_incA τ x)

theorem half_iff {m n : ℕ} (hsum : atPl (D := D) (splitPrime τ) 1 + cA D (atPl (splitPrime τ) 1) =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1)) (u : Matrix (Fin m) (Fin n) (AE D)) :
    ((At (evFin D.host.F v) u ∧ u.map (piW (τ.comp D.sp.cm.sig)) = 0) ↔ IsHalf (atPl (splitPrime τ) 1) u) ∧
    ((At (evFin D.host.F v) u ∧ u.map (piW τ) = 0) ↔ IsHalf (cA D (atPl (splitPrime τ) 1)) u) := by
  have hat := GlobalTheory.FlipMatch.at_atPl τ 1
  have hat' := GlobalTheory.FlipMatch.RowChart.at_cA hat
  have hone : At (evFin D.host.F v) u → ∀ p q, atPl (splitPrime τ) 1 * u p q + cA D (atPl (splitPrime τ) 1) * u p q = u p q :=
    fun h p q => by
      have h1 := h (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
      rw [sub_smul, one_smul, sub_eq_zero] at h1
      rw [← add_mul, hsum, ← Algebra.smul_def]
      exact (congrFun (congrFun h1 p) q).symm
  have hAt : ∀ b : AE D, At (evFin D.host.F v) b → IsHalf b u → At (evFin D.host.F v) u := fun b hb h c hc => by
    ext p q
    rw [Matrix.smul_apply, ← h p q, ← smul_mul_assoc, hb c hc, zero_mul, Matrix.zero_apply]
  refine ⟨⟨fun h p q => ?_, fun h => ⟨hAt _ hat h, Matrix.ext fun p q => ?_⟩⟩,
    ⟨fun h p q => ?_, fun h => ⟨hAt _ hat' h, Matrix.ext fun p q => ?_⟩⟩⟩
  · have h1 := congrArg (cA D) (atPl_mul_eq_zero τ (z := cA D (u p q))
      ((GlobalTheory.FlipMatch.RowChart.piW_cA_eq τ _).trans (congrFun (congrFun h.2 p) q)))
    rw [RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA, map_zero] at h1
    have h2 := hone h.1 p q
    rwa [h1, add_zero] at h2
  · rw [Matrix.map_apply, ← h p q, RingHom.map_mul, piW_conj_atPl_one, zero_mul, Matrix.zero_apply]
  · have h2 := hone h.1 p q
    rwa [atPl_mul_eq_zero τ (congrFun (congrFun h.2 p) q), zero_add] at h2
  · rw [Matrix.map_apply, ← h p q, RingHom.map_mul, GlobalTheory.FlipMatch.RowChart.piW_cA_eq, piW_conj_atPl_one, zero_mul,
      Matrix.zero_apply]

theorem gram_inv_map (S : HSp D) : (S.gram⁻¹).map τ * S.gram.map τ = 1 := by
  have := Matrix.map_mul (L := S.gram⁻¹) (M := S.gram) (f := (τ : D.host.E →+* Fv D.host.F v))
  rw [Matrix.nonsing_inv_mul _ (Formalism.L2.Theta.gram_det_ne S).isUnit, Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this.symm

theorem frMapO_coX (S X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βX : GL (Fin X.rank) (Lev.EAf D)) (b : GL (Fin S.rank) (Fv D.host.F v)) (c : GL (Fin k) (Fv D.host.F v)) (x : WO S X) :
    ((βS.val.map (evW τ))ᵀ * (S.gram.map τ)ᵀ * b.val) * ((b⁻¹).val * (GlobalTheory.TripleRead.ptO S.gram e x).map (piW τ) * (c⁻¹).valᵀ) *
      ((((βX⁻¹).val.map (evW τ)).submatrix e e) * c.val)ᵀ = (((frMapO S X βS βX x).map (evW τ))ᵀ).submatrix id e := by
  have h1 : (GlobalTheory.TripleRead.ptO S.gram e x).map (piW τ) = (x.map (piW τ) * (S.gram⁻¹).map τ)ᵀ.submatrix id e := by
    have : (S.gram⁻¹).map τ = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹).map (piW τ) := Matrix.ext fun _ _ => (piW_incA τ _).symm
    rw [this, ← Matrix.map_mul]
    rfl
  have h2 : (frMapO S X βS βX x).map (evW τ) = (βX⁻¹).val.map (evW τ) * x.map (piW τ) * βS.val.map (evW τ) := by
    have : x.map (piW τ) = (x.map (toEAf D)).map (evW τ) := Matrix.ext fun _ _ => (evW_toEAf τ _).symm
    rw [this, ← Matrix.map_mul, ← Matrix.map_mul]
    rfl
  rw [h1, h2]
  exact coord_fst e _ (gram_inv_map τ S) _ b.mul_inv c.mul_inv _

theorem dualCoord_coY (S X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βX : GL (Fin X.rank) (Lev.EAf D)) (b : GL (Fin S.rank) (Fv D.host.F v)) (c : GL (Fin k) (Fv D.host.F v)) (y : WO S X) :
    ((βS⁻¹).val.map (evW τ) * (S.gram⁻¹).map τ * (b⁻¹).valᵀ) *
      (-(b.valᵀ * ((-1 : D.host.E) • S.gram).map τ * (GlobalTheory.TripleRead.ptO S.gram e y).map (piW (τ.comp D.sp.cm.sig)) *
        ((D.host.xi0 • (X.gramᵀ).submatrix e e).map τ)ᵀ * c.val)) * ((c⁻¹).val * (βX.val.map (evW τ)).submatrix e e) =
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S X βS βX y).map (evW τ)).submatrix id e := by
  have hs : (S.gram⁻¹).map star = (S.gram⁻¹)ᵀ := by
    have h0 : S.gramᴴ = S.gram := Matrix.ext fun a b => S.herm.eq _ _
    have := Matrix.conjTranspose_nonsing_inv S.gram
    rw [h0] at this
    ext a b
    exact congrFun (congrFun this b) a
  have h1 : (GlobalTheory.TripleRead.ptO S.gram e y).map (piW (τ.comp D.sp.cm.sig)) =
      ((S.gram⁻¹).map τ * ((y.map (cA D)).map (piW τ))ᵀ).submatrix id e := by
    have e1 : (S.gram⁻¹).map τ = ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹).map (piW (τ.comp D.sp.cm.sig)))ᵀ :=
      Matrix.ext fun a b => ((piW_incA (τ.comp D.sp.cm.sig) _).trans (congrArg τ (congrFun (congrFun hs b) a))).symm
    have e2 : (y.map (cA D)).map (piW τ) = y.map (piW (τ.comp D.sp.cm.sig)) :=
      Matrix.ext fun _ _ => GlobalTheory.FlipMatch.RowChart.piW_cA_eq τ _
    rw [e1, e2, ← transpose_mul, ← Matrix.map_mul]
    rfl
  have h2 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S X βS βX y).map (evW τ) = τ D.host.xi0 • ((βS⁻¹).val.map (evW τ) *
      ((S.gram⁻¹).map τ * ((y.map (cA D)).map (piW τ))ᵀ * X.gram.map τ) * βX.val.map (evW τ)) := by
    have e1 : ∀ {p : ℕ} (M : Matrix (Fin p) (Fin p) D.host.E), M.map τ = (M.map (incA D)).map (piW τ) := fun M =>
      Matrix.ext fun _ _ => (piW_incA τ _).symm
    have e2 : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) (AE D)), M.map (piW τ) = (M.map (toEAf D)).map (evW τ) := fun M =>
      Matrix.ext fun _ _ => (evW_toEAf τ _).symm
    rw [e1, e1 X.gram, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, e2, ← Matrix.map_mul, ← Matrix.map_mul,
      ← evW_eToEAf]
    exact Matrix.ext fun _ _ => map_mul (evW τ) _ _
  have h3 : ((-1 : D.host.E) • S.gram).map τ = -S.gram.map τ := Matrix.ext fun _ _ => by simp
  have h4 : (D.host.xi0 • (X.gramᵀ).submatrix e e).map τ = τ D.host.xi0 • (X.gram.map τ)ᵀ.submatrix e e :=
    Matrix.ext fun _ _ => map_mul τ _ _
  rw [h1, h2, h3, h4]
  exact coord_snd e _ (mul_eq_one_comm.1 (gram_inv_map τ S)) _ b.mul_inv c.mul_inv _ _ _

end GlobalTheory.BotMatch

end
