import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.LaTwInvT

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14 Formalism.MainNotions.SourceCleaning
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul map_Pol mem_Pol
  dE invT_mul_D w_ne p_eq pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF flat_Ar)
open Formalism.L2.G.Model.TS

theorem Aa_dual2 {K : Type} [Field K] {m : ℕ} (vec : Bool) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : IsUnit M.det) : Aa vec ((M⁻¹).transpose) * (Aa vec M).transpose = 1 := by
  have hMt : IsUnit ((M⁻¹).transpose).det := by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv]; exact hM.ringInverse
  cases vec
  · simp only [Aa, Bool.false_eq_true, if_false]
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hMt, Matrix.transpose_one]
  · simp only [Aa, if_true]
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM, Matrix.transpose_one]

section

variable {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ} {d : Fin n' → ℕ}

theorem subst_Lin (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (r : ℕ)
    (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g)
    (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (hF : F ∈ Pol (KK O) (m + 1) d) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    map (kapR hS) (subst p n' O w n' r g F) = (algebraMap O Kf w ^ Avec (vecE n') d) •
      Lin (fun x => Aa (vecE n' x) (Mx ι σ w φ r (fun x => x) hmat g x))
        (Lin (fun x => Aa (vecE n' x) (la_tw ι σ x.val hmat)⁻¹) (map (kapR hS) F)) := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  have hw := w_ne hS
  have hF' := (pol_iff hS _ _ _).1 hF
  have h1 : map (kapR hS) (subst p n' O w n' r g F) =
      Lin (Bm ι σ w φ r (vecE n') (fun x => x) g) (map (kapR hS) F) :=
    lift_eq hS φ hφ r (LLT n') (fun x => x) (fun _ => rfl) g hg F
  have hB : Bm ι σ w φ r (vecE n') (fun x => x) g = fun x => (if vecE n' x then algebraMap O Kf w else 1) •
      (Aa (vecE n' x) (la_tw ι σ x.val hmat)⁻¹ * Aa (vecE n' x) (Mx ι σ w φ r (fun x => x) hmat g x)) :=
    funext fun x => Bm_eq hw φ r (vecE n') (fun x => x) hmat hh g hg x
  rw [h1, hB, Lin_smul _ _ _ hF', Lin_comp]
  congr 1
  unfold Avec
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro x _
  split_ifs <;> simp

variable (thK : ↥(Pol Kf (ι := Fin n') (m + 1) d) ≃ₗ[Kf] ↥(Vsp Kf (flW (m := m) d)))

theorem pair_formula (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ)
    (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < m + 1)
    (hthK : ∀ P, ((thK P : ↥(Vsp Kf (flW (m := m) d))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecE n') (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf)) (κ : ℕ)
    (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det)
    (g gv : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g) (hgv : IsGLW gv)
    (hb : IsUnit (hmat * ((matQ φ g)⁻¹).transpose).det)
    (hrel : ((matQ φ gv)⁻¹).transpose =
      ((hmat * ((matQ φ g)⁻¹).transpose)⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq))
    (Θ Θv : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)))
    (hΘ : IsTrueTheta hS d (flW d) (vecE n') hmat Θ) (hΘv : IsTrueTheta hS d (flW d) (vecE n') 1 Θv)
    (F Fv : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    be p r (flW d) (Θ F) (TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) (Θv Fv)) =
      kapR hS ((p : KK O) ^ κ * fock (subst p n' O w n' r g (F : MvPolynomial (TV n' (m + 1)) (KK O)))
        (subst p n' O w n' r gv (Fv : MvPolynomial (TV n' (m + 1)) (KK O))) /
          (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O)) := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  have h1d : IsUnit (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq).det := by simp
  let P : ↥(Pol Kf (ι := Fin n') (m + 1) d) :=
    ⟨Lin (fun x => Aa (vecE n' x) (la_tw ι σ x.val hmat)⁻¹) (map (kapR hS) F.1),
      Lin_Pol _ _ ((pol_iff hS _ _ _).1 F.2)⟩
  let Q : ↥(Pol Kf (ι := Fin n') (m + 1) d) :=
    ⟨Lin (fun x => Aa (vecE n' x) (la_tw ι σ x.val (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq))⁻¹)
      (map (kapR hS) Fv.1), Lin_Pol _ _ ((pol_iff hS _ _ _).1 Fv.2)⟩
  have eF : Θ F = thK P := Subtype.ext (by rw [hΘ F, hthK]; rfl)
  have eFv : Θv Fv = thK Q := Subtype.ext (by rw [hΘv Fv, hthK]; rfl)
  have hdual : ∀ s : Fin n', Aa (vecE n' s) (Mx ι σ w φ r (fun x => x) 1 gv s) *
      (Aa (vecE n' s) (Mx ι σ w φ r (fun x => x) hmat g s)).transpose = 1 := by
    intro s
    have e1 : Mx ι σ w φ r (fun x => x) 1 gv s = ((Mx ι σ w φ r (fun x => x) hmat g s)⁻¹).transpose := by
      unfold Mx
      rw [Matrix.one_mul, hrel]
      exact dualM hS s.val r _ hb
    rw [e1]
    exact Aa_dual2 _ _ (Mx_det (w_ne hS) φ r (fun x => x) hmat hh g hg s)
  have hL : be p r (flW d) (Θ F) (TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) (Θv Fv)) =
      (p : Kf) ^ Ar r (flW (m := m) d) * (((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) *
        fockR (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf) (Q : MvPolynomial (Fin n' × Fin (m + 1)) Kf)) := by
    unfold be
    rw [eF, eFv, map_smul, smul_eq_mul, TY_apply]
  rw [hL, map_div₀, map_mul, map_pow, map_natCast, map_natCast, fock_eq_fockR, ← fockR_map,
    subst_Lin hS φ hφ r hmat hh g hg F.1 F.2, subst_Lin hS φ hφ r 1 h1d gv hgv Fv.1 Fv.2, tsact_smul_left,
    tsact_smul_right, fockR_Lin_dual _ _ hdual, flat_Ar r hr1 hr2 (vecE n') d (flW d) (isFlat_flW d), zpow_natCast,
    p_eq hS]
  show _ = _ * (_ * (_ * fockR (P : MvPolynomial (Fin n' × Fin (m + 1)) Kf)
    (Q : MvPolynomial (Fin n' × Fin (m + 1)) Kf))) / _
  ring

theorem exists_gv (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) {k : ℕ} (X : Matrix (Fin k) (Fin k) Qq)
    (h : colSpan W X = colSpan W (1 : Matrix (Fin k) (Fin k) Qq)) :
    ∃ gv : Matrix (Fin k) (Fin k) (WF p n'), IsGLW gv ∧ matQ φ gv = X := by
  have := hS.frac_alt
  have hinj : Function.Injective (algebraMap W Qq) := IsFractionRing.injective W Qq
  have h1 : ∀ c : Fin k, ∃ y : Fin k → W, (fun i => X i c) =
      (1 : Matrix (Fin k) (Fin k) Qq).mulVec (fun a => algebraMap W Qq (y a)) := by
    intro c
    apply (mem_colSpan _ _).1
    rw [← h]
    exact Submodule.subset_span ⟨c, rfl⟩
  have h2 : ∀ c : Fin k, ∃ y : Fin k → W, (fun i => (1 : Matrix (Fin k) (Fin k) Qq) i c) =
      X.mulVec (fun a => algebraMap W Qq (y a)) := by
    intro c
    apply (mem_colSpan _ _).1
    rw [h]
    exact Submodule.subset_span ⟨c, rfl⟩
  choose Y hY using h1
  choose Y' hY' using h2
  let Cm : Matrix (Fin k) (Fin k) W := fun i c => Y c i
  let Cm' : Matrix (Fin k) (Fin k) W := fun i c => Y' c i
  have hX : X = Cm.map (algebraMap W Qq) := by
    ext i c
    have := congrFun (hY c) i
    rw [Matrix.one_mulVec] at this
    exact this
  have hprod : Cm * Cm' = 1 := by
    apply Matrix.map_injective hinj
    show (Cm * Cm').map (algebraMap W Qq) = (1 : Matrix (Fin k) (Fin k) W).map (algebraMap W Qq)
    rw [Matrix.map_mul, ← hX, Matrix.map_one _ (map_zero _) (map_one _)]
    ext i c
    have := congrFun (hY' c) i
    rw [Matrix.mul_apply]
    exact this.symm
  have hdet : IsUnit Cm.det := by
    have : Cm.det * Cm'.det = 1 := by rw [← Matrix.det_mul, hprod, Matrix.det_one]
    exact IsUnit.of_mul_eq_one _ this
  refine ⟨(φ.symm : W →+* WF p n').mapMatrix Cm, ?_, ?_⟩
  · unfold IsGLW
    rw [← RingHom.map_det]
    exact hdet.map _
  · rw [hX]
    ext a c
    simp [matQ, RingHom.mapMatrix_apply, Matrix.map_apply]

end

end Formalism.MainNotions.TestSideCounting
