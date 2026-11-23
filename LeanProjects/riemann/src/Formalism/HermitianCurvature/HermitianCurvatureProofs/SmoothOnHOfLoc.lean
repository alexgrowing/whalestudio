import Formalism.HermitianCurvature.HermitianCurvatureProofs.CharacterStabilizerEqOne

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def KrAA : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)), KB.CptCoef Bs F → ∀ (u : ℂ), ∀ x ∈ B.GV k r,
      PBG.Kr Bs (C3.AAop k r r le_rfl u F) x = C3.AAop k r r le_rfl u (PBG.Kr Bs F) x

section point

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem ptSize_app (h : C.LPt) (s : ℕ) (t : ℂ) : D.ptSize (h ++ [(s, t)]) = D.ptSize h + s := by
  simp [D.ptSize]

theorem smoothOnH_of_loc {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : ∀ x ∈ B.GV k r, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ⊤ f x) : SmoothOnH (Hpk k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hf', fun g hg hgG => hfe g hg hgG⟩

theorem pt_poly (hKA : KrAA) (Bs : B.RealPlaceData k r Wp Wq) {G : B.Mat k r → (Wq →L[ℂ] Wp)} (hG : KB.CptCoef Bs G)
    (h : C.LPt) (s : ℕ) (t : ℂ) (hs : 2 ≤ s) (hq : D.IsLocPt (h ++ [(s, t)]) (r + 1)) {γ : B.Mat k r}
    (hγ : γ ∈ B.GV k r) (hZγ : Zhat k r Bs.z Bs.z' γ = D.ptMatN (h ++ [(s, t)]) (r + 1))
    (hpos : 0 < Gf k r Bs.z Bs.z' γ) {x : Mt k r × Mt k r}
    (hx : (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧ (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r) :
    ∃ c : Fin (D.ptSize h + 1) → (Wq →L[ℂ] Wp),
      c (Fin.last _) = ((-1) ^ (s - 1) / t) • PBG.Kr Bs G ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * γ) ∧
      ∀ y : ℝ, PBG.Kr Bs (PBN.aaTop Bs y G) ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * γ) =
        ∑ n : Fin (D.ptSize h + 1), ((y : ℂ) ^ (n : ℕ)) • c n := by
  set σ : B.Mat k r := (Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2 : B.Mat k r)⁻¹ with hσ
  set Gσ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => G (σ * g) with hGσdef
  have hGσ : KB.CptCoef Bs Gσ := cpt_left Bs hG hx
  have hp := inSS_pL Bs hx
  have hσS : σ ∈ Sset k r Bs.z :=
    ⟨(Matrix.of x.1 : B.Mat k r)⁻¹, Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hx.1, (Matrix.of x.2 : B.Mat k r)⁻¹,
      Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hx.2, rfl⟩
  have h1S : (1 : B.Mat k r) ∈ Sset k r Bs.z := ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, 1, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one,
    (Matrix.mul_one 1).symm⟩
  have h1S' : (1 : B.Mat k r) ∈ Sset k r Bs.z' := ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, 1, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_one,
    (Matrix.mul_one 1).symm⟩
  have hdσ : ∀ (g : B.Mat k r) (l : Fin (r + 2)), Dmin k r Bs.z Bs.z' (σ * g) l = Dmin k r Bs.z Bs.z' g l := by
    intro g l
    have := Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g l
    rwa [sgs_pL] at this

  have hsz : D.ptSize h + s = r + 1 := by rw [← ptSize_app h s t]; exact hq.2
  have ht : t ≠ 0 := (hq.1 (s, t) (by simp)).2
  set i0 := D.ptSize h with hi0
  set hh := D.ptMatN h i0 with hhh
  have hZ : ∀ a b : Fin (r + 1), Zhat k r Bs.z Bs.z' γ a b = C3.Zb i0 s hh t a.val b.val := by
    intro a b
    rw [hZγ]
    exact ptMatN_zb h s t (r + 1) hsz.symm a b
  have hDlast : Dmin k r Bs.z Bs.z' γ (Fin.last (r + 1)) ≠ 0 := by
    intro h0
    have hTT : 0 ≤ Tz k r Bs.z * Tz k r Bs.z' := mul_nonneg Bs.T_pos.le Bs.T'_pos.le
    have : Gf k r Bs.z Bs.z' γ ≤ 0 := by
      unfold Gf
      rw [h0, map_zero]
      nlinarith [Complex.normSq_nonneg (Dmin k r Bs.z Bs.z' γ ⟨r, by omega⟩)]
    linarith
  have hdet : hh.det ≠ 0 := by
    intro h0
    apply hDlast
    rw [dmin_zb Bs.z Bs.z' γ i0 s hh t hZ]
    have := (Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb i0 s hh t).2
    rw [show ((Fin.last (r + 1) : Fin (r + 2)) : ℕ) = i0 + s by simp; omega, this, h0]
    ring
  have hT' : herm (Hpk k r) Bs.z' Bs.z' ≠ 0 := by
    intro h0
    have := Bs.T'_pos
    unfold Tz at this
    rw [h0] at this
    simp at this
  obtain ⟨n0, hn0, yb, hyb, hzy, hnf1, hnf2⟩ :=
    nf_top Bs.z Bs.z' Bs.z'_mem hT' γ hγ i0 s hs hsz hh hdet t ht hZ
  have hn0N : n0 ∈ Formalism.QuantumDeterminants.Nset k r := stabilizer_mem_unipotent hn0
  have hn0S : n0 ∈ Sset k r Bs.z' := ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _, n0, hn0N, (Matrix.one_mul n0).symm⟩
  have hx₁G : γ * n0 ∈ B.GV k r := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hγ hn0N.1
  have hZ₁ : ∀ a b : Fin (r + 1), Zhat k r Bs.z Bs.z' (γ * n0) a b = C3.Zb i0 s hh t a.val b.val := by
    intro a b; rw [corner_matrix_right_translate Bs.z Bs.z' γ n0 hn0]; exact hZ a b
  have hD₁ : ∀ l : Fin (r + 2), Dmin k r Bs.z Bs.z' (γ * n0) l = Dmin k r Bs.z Bs.z' γ l := by
    intro l; unfold Dmin; rw [corner_matrix_right_translate Bs.z Bs.z' γ n0 hn0]

  set K : B.Mat k r → (Wq →L[ℂ] Wp) := PBG.Kr Bs Gσ with hKdef
  have hKloc := loc_kr Bs hGσ
  have hKn0 : ∀ g, K (g * n0) = K g := by
    intro g
    rw [hKdef, PBG.kr_rightEq Bs Gσ g n0 hn0N, character_stabilizer_eq_one Bs.z'_mem cStd hn0, one_smul]
  have hKσ : ∀ g, K g = PBG.Kr Bs G (σ * g) := fun g => kr_left Bs G σ g
  have hR : ∀ g ∈ Q.Glev k r 0 ∩ Set.univ, ∀ p q, C3.InNp k r p q →
      Q.EH k r p q K g = C3.dpsiP k r Bs.z' p q • K g :=
    fun g _ p q hpq => PBG.kr_rule Bs Gσ g p q hpq
  obtain ⟨c, hc, hcy⟩ := top_poly isOpen_univ Bs.z Bs.z' yb i0 s hs hsz hh t hdet ht (γ * n0)
    ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 _).2 hx₁G, Set.mem_univ _⟩ Bs.z'_mem hyb hzy hnf1 hnf2 hZ₁ K
    (smoothLev_of_loc hKloc) hR
  refine ⟨c, ?_, fun y => ?_⟩
  · rw [hc, hKn0, hKσ]
  · rw [← hcy y, hD₁]
    set u : ℂ := (y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2 with hu

    have hX1 := (Formalism.FourierDecayAlt.P.operators_commute_translations' (Wq →L[ℂ] Wp) k r Bs.z Bs.z' r le_rfl u 0 K Bs.z_mem Bs.z'_mem
      (smoothOnH_of_loc hKloc) 1 h1S n0 hn0S γ hγ).1
    have e1 : (fun g => K (1 * g * n0)) = K := by
      funext g; rw [Matrix.one_mul, hKn0]
    rw [e1, Matrix.one_mul] at hX1
    rw [← hX1]

    have hleft : ∀ g ∈ B.GV k r, PBN.aaTop Bs y G (σ * g) = PBN.aaTop Bs y Gσ g := by
      intro g hg
      unfold PBN.aaTop
      rw [hdσ]
      have hX0 := (Formalism.FourierDecayAlt.P.operators_commute_translations' (Wq →L[ℂ] Wp) k r Bs.z Bs.z' r le_rfl u 0 G Bs.z_mem Bs.z'_mem
        (smoothOnH_of_ckOn hG.1) σ hσS 1 h1S' g hg).1
      have e2 : (fun x => G (σ * x * 1)) = Gσ := by funext x; rw [Matrix.mul_one]
      rw [e2, Matrix.mul_one] at hX0
      rw [hX0]
    have hKA' := hKA k r Wp Wq Bs Gσ hGσ u γ hγ
    calc PBG.Kr Bs (PBN.aaTop Bs y G) (σ * γ)
        = PBG.Kr Bs (fun g => PBN.aaTop Bs y G (σ * g)) γ := (kr_left Bs _ σ γ).symm
      _ = PBG.Kr Bs (PBN.aaTop Bs y Gσ) γ := kr_congr Bs hleft hγ
      _ = (Dmin k r Bs.z Bs.z' γ (Fin.last _))⁻¹ • PBG.Kr Bs (C3.AAop k r r le_rfl u Gσ) γ :=
          kr_dmin Bs (C3.AAop k r r le_rfl u Gσ) (Fin.last _) γ
      _ = (Dmin k r Bs.z Bs.z' γ (Fin.last _))⁻¹ • C3.AAop k r r le_rfl u K γ := by rw [hKA']

end point

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
