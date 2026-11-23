import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LaTwInvT
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCZ

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf.TF

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS
  letterWt_anti tensor_lattice_twist_eq tens_Le edgeLat_of la_tw_mul la_tw_transpose la_tw_inv dE invT_mul_D dual_edgeBasis w_ne p_eq
  pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF gen_equiv gen_A gen_R mem_scale2 edgePlane)
open Formalism.L2.G.Model.TS

section

variable {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jO : W →+* O} {w : O}

theorem Avec_eq {m : ℕ} (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) :
    (Avec (vecH TT) (hhDegs TT aT bT) : ℤ) = AHH TT aT bT := by
  unfold Avec AHH
  push_cast
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, vecH, hhDegs, if_true, Bool.false_eq_true, if_false, add_zero]
  exact Finset.sum_coe_sort TT (fun s => (hhDeg aT bT s true : ℤ))

theorem flatTheta (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m : ℕ)
    (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (hm : 1 ≤ m) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (hh : IsUnit h.det) :
    ∃ Θ : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
        ↥(VHH (m := m) Kf TT aT bT),
      IsFlatTheta ι σ jO w φ TT aT bT h Θ ∧
      ∀ F, ((Θ F : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
        thF hS m (vecH TT) (fun x => la_tw ι σ x.1.val.val h) F.1 := by
  letI : Algebra (WF p n') O := algOfIdent jO φ
  have hw := w_ne hS
  obtain ⟨Θ0, hΘ0⟩ := gen_equiv hS m hm (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT)
    (fun x => la_tw ι σ x.1.val.val h) (fun x => la_tw_det _ _ _ _ hh)
  have hV : VS Kf m (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) = VHH (m := m) Kf TT aT bT := rfl
  let Θ : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
      ↥(VHH (m := m) Kf TT aT bT) := Θ0.trans ((LinearEquiv.ofEq _ _ hV).restrictScalars O)
  have hΘ : ∀ F, ((Θ F : ↥(VHH (m := m) Kf TT aT bT)) :
      MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      thF hS m (fun x : TT × Bool => x.2) (fun x => la_tw ι σ x.1.val.val h) F.1 := fun F => hΘ0 F
  refine ⟨Θ, ⟨?_, ?_, ?_⟩, hΘ⟩
  · intro F
    rw [gen_A hS m hm (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT)
      (fun x => la_tw ι σ x.1.val.val h) (fun x => la_tw_det _ _ _ _ hh) F.1 F.2, ← hΘ F,
      ← tensor_lattice_twist_eq hS m (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) (fun x => x.1.val) h hh]
    rfl
  · intro g hg e he F i
    have h1 : InWjRg p n' O w 1 (Formalism.MainNotions.ColumnSystems.hhLetters TT) g F.1 i ↔
        ∃ y ∈ tensorLat O Kf (fun s : TT × Bool => nablaLTw O Kf m
            (letterWt m (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT s) s.2) (Mx ι σ w φ 1 (fun x : TT × Bool => x.1.val) h g s)),
          thF hS m (fun x : TT × Bool => x.2) (fun x => la_tw ι σ x.1.val.val h) F.1 =
            (algebraMap O Kf w ^ ((i : ℤ) -
              (Avec (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) : ℤ))) • y :=
      gen_R hS φ hφ m hm 1 (Formalism.MainNotions.ColumnSystems.hhLetters TT) (fun x => x.1.val) (fun _ => rfl)
        (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) h hh g hg F.1 F.2 i
    rw [h1, ← hΘ F, ← tens_Le hS φ m 1 (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) (fun x => x.1.val)
      h hh g hg e he]
    have hA : (Avec (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) : ℤ) = AHH TT aT bT :=
      Avec_eq (m := m) TT aT bT
    have h2 := mem_scale2 (O := O) (VHH (m := m) Kf TT aT bT)
      (HHten O TT aT bT fun s => LeAt p ι σ w s.val e) (algebraMap O Kf w ^ (i : ℤ))
      (algebraMap O Kf w ^ (-AHH TT aT bT)) (zpow_ne_zero _ hw) (zpow_ne_zero _ hw) (Θ F)
    have e1 : algebraMap O Kf w ^ (i : ℤ) * algebraMap O Kf w ^ (-AHH TT aT bT) = algebraMap O Kf w ^
        ((i : ℤ) - (Avec (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) : ℤ)) := by
      rw [← zpow_add₀ hw, ← sub_eq_add_neg, ← hA]
    rw [e1] at h2
    exact h2.symm
  · intro e he hsrc
    exact (edgePlane p n' W Qq O Kf ι σ jO w hS φ hφ m 1 h hh).1 e he hsrc

theorem matQ_one (φ : WF p n' ≃+* W) (k : ℕ) : matQ (Qq := Qq) φ (1 : Matrix (Fin k) (Fin k) (WF p n')) = 1 := by
  ext a b
  simp only [matQ, Matrix.one_apply]
  split_ifs <;> simp

theorem mul_matQ_one (φ : WF p n' ≃+* W) {k : ℕ} (h : Matrix (Fin k) (Fin k) Qq) :
    h * ((matQ φ (1 : Matrix (Fin k) (Fin k) (WF p n')))⁻¹).transpose = h := by
  rw [matQ_one]
  simp

theorem isGLW_one (k : ℕ) : IsGLW (1 : Matrix (Fin k) (Fin k) (WF p n')) := by
  simp [IsGLW]

theorem Aa_dual' {K : Type} [Field K] {m : ℕ} (vec : Bool) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : IsUnit M.det) : Aa vec ((M⁻¹).transpose) * (Aa vec M).transpose = 1 := by
  cases vec
  · simp [Aa, Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hM, Matrix.mul_nonsing_inv _ hM]
  · simp [Aa, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM]

theorem lift_Pol (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m : ℕ)
    (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g)
    (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) (hF : F ∈ Pol (KK O) (m + 1) (hhDegs TT aT bT)) :
    letI : Algebra (WF p n') O := algOfIdent jO φ
    liftSubst p n' O w 1 (hhLetters TT) g F ∈ Pol (KK O) (m + 1) (hhDegs TT aT bT) := by
  letI : Algebra (WF p n') O := algOfIdent jO φ
  rw [pol_iff hS, lift_eq hS φ hφ 1 (hhLetters TT) (fun x => x.1.val) (fun _ => rfl) g hg F]
  exact Lin_Pol _ _ ((pol_iff hS _ _ _).1 hF)

theorem lift_one (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m : ℕ)
    (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit h.det)
    (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) (hF : F ∈ Pol (KK O) (m + 1) (hhDegs TT aT bT)) :
    letI : Algebra (WF p n') O := algOfIdent jO φ
    map (kapR hS) (liftSubst p n' O w 1 (hhLetters TT) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) F) =
      (algebraMap O Kf w ^ Avec (vecH TT) (hhDegs TT aT bT)) •
        Lin (fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val h * lb_D (m + 1) 1 (algebraMap O Kf w)))
          (Lin (fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val h)⁻¹) (map (kapR hS) F)) := by
  letI : Algebra (WF p n') O := algOfIdent jO φ
  have hw := w_ne hS
  set c := algebraMap O Kf w with hc
  have hF' := (pol_iff hS _ _ _).1 hF
  rw [lift_eq hS φ hφ 1 (hhLetters TT) (fun x => x.1.val) (fun _ => rfl) 1 (isGLW_one _) F]
  have hB : Bm ι σ w φ 1 (hhLetters TT).vec (fun x : TT × Bool => x.1.val) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) =
      fun x => (if (hhLetters TT).vec x then c else 1) •
      (Aa ((hhLetters TT).vec x) (la_tw ι σ x.1.val.val h)⁻¹ *
        Aa ((hhLetters TT).vec x) (Mx ι σ w φ 1 (fun x : TT × Bool => x.1.val) h 1 x)) :=
    funext fun x => Bm_eq hw φ 1 (hhLetters TT).vec (fun x : TT × Bool => x.1.val) h hh 1 (isGLW_one _) x
  rw [hB, Lin_smul _ _ _ hF', Lin_comp]
  have hprod : ∏ x : TT × Bool, (if (hhLetters TT).vec x then c else 1) ^ hhDegs TT aT bT x =
      c ^ Avec (vecH TT) (hhDegs TT aT bT) := by
    unfold Avec
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro x _
    show (if x.2 = true then c else 1) ^ _ = c ^ (if x.2 = true then _ else 0)
    split_ifs <;> simp
  rw [hprod]
  have hfun : (fun x : TT × Bool => Aa ((hhLetters TT).vec x) (la_tw ι σ x.1.val.val h)⁻¹ *
        Aa ((hhLetters TT).vec x) (Mx ι σ w φ 1 (fun x : TT × Bool => x.1.val) h 1 x)) =
      fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val h)⁻¹ * Aa x.2 (la_tw ι σ x.1.val.val h * lb_D (m + 1) 1 c) := by
    funext x
    unfold Mx
    rw [mul_matQ_one]
    rfl
  rw [hfun]

end

end Formalism.MainNotions.ColumnSystems.Pf.TF
