import Formalism.HermitianCurvature.HermitianCurvatureProofs.Tower

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem lintegral_zWeight_closedBall_ne_infty (k : ℕ) (T T' R : ℝ) :
    ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (B2.zWeight k T T' ζ) < ⊤ := by
  have hb : ∀ ζ ∈ Metric.closedBall (0 : ℂ) R,
      ENNReal.ofReal (B2.zWeight k T T' ζ) ≤ ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) := by
    intro ζ hζ
    apply ENNReal.ofReal_le_ofReal
    unfold B2.zWeight
    split_ifs with h
    · apply pow_le_pow_left₀ (by linarith)
      have h1 : Complex.normSq ζ ≤ R ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
        have := mem_closedBall_zero_iff.mp hζ
        have h0 : 0 ≤ ‖ζ‖ := norm_nonneg _
        nlinarith
      have h2 : -(T * T') ≤ |T * T'| := neg_le_abs _
      linarith
    · positivity
  calc ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (B2.zWeight k T T' ζ)
      ≤ ∫⁻ _ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) :=
        setLIntegral_mono measurable_const (fun ζ hζ => hb ζ hζ)
    _ = ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) * volume (Metric.closedBall (0 : ℂ) R) :=
        setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

theorem ph_cast {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k n ρ : ℕ} (hn : n = 1 + ρ)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn.symm (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn.symm (liftVec k 1 ρ zs'))
    (hzs : inWb k ρ zs) (hzs' : inWb k ρ zs')
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)}
    {πs : Mx k ρ → (Wp →L[ℂ] Wp)} {πs' : Mx k ρ → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn.symm (ιLev k 1 ρ y))) (hπ' : ∀ y, πs' y = π' (D.castM hn.symm (ιLev k 1 ρ y)))
    (X : ActualOps k n z z' π π') (Xs : ActualOps k ρ zs zs' πs πs')
    (L : R.LevelData (Pr (RadSp k n z z' π π')) n) (st : Fr.Start (Pr (RadSp k n z z' π π')))
    (Ls : R.LevelData (Pr (RadSp k ρ zs zs' πs πs')) ρ) (sts : Fr.Start (Pr (RadSp k ρ zs zs' πs πs')))
    (s : ℂ) (μ : Measure (Mt k n)) (μs : Measure (Mt k ρ))
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y)
    (hμ : B.IsHaarOn (Glev k n (Fin.last n)) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs)
    (hlaw : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k n z z' (Fin.last n) (Matrix.of x)) ∂μ =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k n z) (Tz k n z') ζ) * ψ ζ)
    (hlaws : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k ρ zs zs' (Fin.last ρ) (Matrix.of x)) ∂μs =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k ρ zs) (Tz k ρ zs') ζ) * ψ ζ)
    (t : ℂ) (ht : t ≠ 0) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k ρ zs zs' πs πs',
      (∀ Φ c g, (T Φ : Fn k ρ (Wq →L[ℂ] Wp)) c g =
        (Φ : Fn k n (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast hn l)) (D.castM hn.symm (ιLev k 1 ρ g))) ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)) (x y : Wd.Ix S → RadSp k n z z' π π')
        (c : Fin n → ℂ) (c₀ : Fin ρ → ℂ),
        P5.ph L st μ ⟨0, by omega⟩ w x y c t =
          ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
            P5.RRform Ls sts μs 0 w (fun a => T (P5.act (P5.bTl L ⟨0, by omega⟩ w) x a))
              (fun a => T (P5.act (P5.bTl L ⟨0, by omega⟩ w) y a)) c₀ := by
  subst hn
  have ez : z = liftVec k 1 ρ zs := by
    rw [hz]; funext i; simp [D.castV]
  have ez' : z' = liftVec k 1 ρ zs' := by
    rw [hz']; funext i; simp [D.castV]
  have eπ : πs = fun y => π (ιLev k 1 ρ y) := by
    funext y; rw [hπ y]; congr 1
  have eπ' : πs' = fun y => π' (ιLev k 1 ρ y) := by
    funext y; rw [hπ' y]; congr 1
  subst ez ez' eπ eπ'
  have hmap : μs.map (B2.levM k ρ) = μ := by
    refine map_levM_eq hμ hμs (fun ζ => ENNReal.ofReal (B2.zWeight k (Tz k ρ zs) (Tz k ρ zs') ζ))
      (fun R => lintegral_zWeight_closedBall_ne_infty k _ _ R) ?_ hlaws
    intro ψ hψ
    rw [hlaw ψ hψ, tz_iota, tz_iota]
  refine ⟨trL ht zs zs' π π', ?_, ?_⟩
  · intro Φ c g
    (try simp [D.castM]) <;> rfl
  · intro S _ _ w x y c c₀
    exact ph_tr ht hzs hzs' hL hLs hst hsts hmap w x y c c₀

def RadTransportPl : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j + 1 ≤ P.r)
    (X : Q.ActualOps (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π')
    (μ : Measure (Mt P.k (P.r - j))) (L) (st)
    (Xs : Q.ActualOps (JC.parLev P (j + 1)).k (JC.parLev P (j + 1)).r (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z'
      (p.T.bs (j + 1)).π (p.T.bs (j + 1)).π')
    (μs : Measure (Mt P.k (P.r - (j + 1)))) (Ls) (sts),
    P5.IsData (JC.parLev P j) (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π' X μ L st p.l0 →
    KB.ZetaNorm (p.T.bs j) μ →
    P5.IsData (JC.parLev P (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' (p.T.bs (j + 1)).π
      (p.T.bs (j + 1)).π' Xs μs Ls sts p.l0 →
    KB.ZetaNorm (p.T.bs (j + 1)) μs →
    ∀ t : ℂ, t ≠ 0 →
      ∃ T : Q.RadSp P.k (P.r - j) (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π' →ₗ[ℂ]
          Q.RadSp P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' (p.T.bs (j + 1)).π
            (p.T.bs (j + 1)).π',
        (∀ Φ c g, (T Φ : Q.Fn P.k (P.r - (j + 1)) (Wq →L[ℂ] Wp)) c g =
          (Φ : Q.Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast (by omega) l))
            (D.castM (by omega) (ιLev P.k 1 (P.r - (j + 1)) g))) ∧
        ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S))
          (x y : Wd.Ix S → Q.RadSp P.k (P.r - j) (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π')
          (c : Fin (P.r - j) → ℂ) (c₀ : Fin (P.r - (j + 1)) → ℂ),
          P5.ph L st μ (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) w x y c t =
            ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
              P5.RRform Ls sts μs 0 w
                (fun a => T (P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) w) x a))
                (fun a => T (P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) w) y a))
                c₀

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

theorem radial_transport_plus : Formalism.FourierDecayAlt.P.PBH.RadTransportPl := by
  intro Wp Wq _ _ _ _ _ _ P p j hj X μ L st Xs μs Ls sts hD hZ hDs hZs t ht
  exact ph_cast (n := P.r - j) (ρ := P.r - (j + 1)) (by omega)
    (levTower_bs_z_eq_castV_liftVec p.T j hj) (levTower_bs_z'_eq_castV_liftVec p.T j hj) hDs.1.2.1 hDs.1.2.2.1
    (tower_π p.T j hj) (tower_π' p.T j hj) X Xs L st Ls sts _ μ μs
    hD.2.2.1 hDs.2.2.1 hD.2.2.2.1 (fun Y => (hDs.2.2.2.1 Y).trans rfl) hD.2.1 hDs.2.1 hZ.2 hZs.2 t ht

end Formalism.FourierDecayAlt.P
