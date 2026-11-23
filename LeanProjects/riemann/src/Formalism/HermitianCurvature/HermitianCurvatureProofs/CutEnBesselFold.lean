import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCVLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBesselEigen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothnessOnGoodSet

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem foldCV_memB {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Q.Mx k r)}
    (hcl : ∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (Y : ℝ) (s : ℂ), s • Q.CV k r (Y : ℂ) J ∈ Q.FFl k r z z' π π' 0 Dm)
    {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm) (s : ℂ) :
    ∀ a : List C.Letter, foldCV k r s a J ∈ Q.FFl k r z z' π π' 0 Dm
  | [] => hJ
  | x :: a => hcl _ (foldCV_memB hcl hJ s a) x.2 s

theorem mem_level_zero_of_mem_group {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem JF_smul' {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (c : ℂ)
    (G : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) : B.JF D (c • G) g = c • B.JF D G g := by
  show ∫ p, JF.xiP D p • B.rho D p (c • G) g ∂D.μSS = c • ∫ p, JF.xiP D p • B.rho D p G g ∂D.μSS
  rw [← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [B.rho, Pi.smul_apply, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [smul_comm]

theorem thr_budget (k r N : ℕ) (A₀ : ℝ) (hk : 2 ≤ k)
    (hA : 100 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀)
    (m : ℕ) (hm : m ≤ (2 * r + k + 1) * (N + 1)) :
    JF.TransportedAlt k r (A₀ - 2 * ((r : ℝ) + 1) * (((2 * r + k + 1) * (N + 1) : ℕ) : ℝ)) m := by
  unfold JF.TransportedAlt
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  set R : ℝ := (r : ℝ) + 1 with hRdef
  have hcast : ((2 * r + k + 1 : ℕ) : ℝ) = n := by rw [hn]; push_cast; ring
  have hMc : (((2 * r + k + 1) * (N + 1) : ℕ) : ℝ) = n * ((N : ℝ) + 1) := by rw [hn]; push_cast; ring
  have hmr : (m : ℝ) ≤ n * ((N : ℝ) + 1) := by rw [← hMc]; exact_mod_cast hm
  have hn3 : (3 : ℝ) ≤ n := by rw [hn]; linarith
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hR1 : (1 : ℝ) ≤ R := by rw [hRdef]; linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have h4 : R ≤ R ^ 4 := by
    have : (1 : ℝ) ≤ R ^ 3 := one_le_pow₀ hR1
    calc R = R * 1 := by ring
      _ ≤ R * R ^ 3 := by gcongr
      _ = R ^ 4 := by ring
  set P : ℝ := (N : ℝ) * n ^ 2 + n ^ 3 with hP
  have hP0 : 0 ≤ P := by positivity
  have hA' : 100 * R * P ≤ A₀ := le_trans (by gcongr) hA
  have hnn : n ≤ n ^ 2 := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ n by linarith) hn0
    calc n = n * 1 := by ring
      _ ≤ n * n := this
      _ = n ^ 2 := by ring
  have hn23 : 3 * n ^ 2 ≤ n ^ 3 := by
    have := mul_le_mul_of_nonneg_right hn3 (sq_nonneg n)
    calc 3 * n ^ 2 ≤ n * n ^ 2 := this
      _ = n ^ 3 := by ring
  have hn1 : 3 * n ≤ n ^ 2 := by
    have := mul_le_mul_of_nonneg_right hn3 hn0
    calc 3 * n ≤ n * n := this
      _ = n ^ 2 := by ring
  have i1 : 8 * (n * (N : ℝ)) ≤ 100 * ((N : ℝ) * n ^ 2) := by
    have := mul_le_mul_of_nonneg_right hnn hN0
    nlinarith
  have i2 : 8 * n + 9 * n ^ 2 < 100 * n ^ 3 := by nlinarith
  have inner : 8 * (n * ((N : ℝ) + 1)) + 9 * n ^ 2 < 100 * P := by rw [hP]; nlinarith
  have key : R * (8 * (n * ((N : ℝ) + 1)) + 9 * n ^ 2) < R * (100 * P) := mul_lt_mul_of_pos_left inner hR0
  have hrm : 6 * (r : ℝ) * (m : ℝ) ≤ 6 * R * (n * ((N : ℝ) + 1)) := by
    have h6 : 6 * (r : ℝ) ≤ 6 * R := by rw [hRdef]; linarith
    calc 6 * (r : ℝ) * (m : ℝ) ≤ 6 * R * (m : ℝ) := by gcongr
      _ ≤ 6 * R * (n * ((N : ℝ) + 1)) := by gcongr
  rw [hcast, hMc, lt_div_iff₀ (by positivity)]
  have e1 : R * (100 * P) = 100 * R * P := by ring
  have e2 : R * (8 * (n * ((N : ℝ) + 1)) + 9 * n ^ 2) =
      2 * R * (n * ((N : ℝ) + 1)) + 6 * R * (n * ((N : ℝ) + 1)) + n ^ 2 * (9 * R) := by ring
  rw [e1, e2] at key
  linarith

theorem besselFoldBuilt_of (hC : CVInCC) : BesselFoldBuilt := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v hcl ε hε hJF
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, _, hk2, hA, _⟩, _, _, _⟩ := hB
  obtain ⟨hcut, hv⟩ := hbuilt
  obtain ⟨_, _, _, _, hCC, _⟩ := hv v
  set Db := (T v).base with hDb
  set s : ℂ := M.sgn (D.parOf S v) (S.l + 1) with hs
  set F := D.cutF Db χ (f v) ε with hF
  set n : ℕ := 2 * S.G.r + S.G.k + 1 with hn
  set N : ℕ := S.Ntop with hN
  set A : ℝ := A₀ - 2 * ((S.G.r : ℝ) + 1) * ((n * (N + 1) : ℕ) : ℝ) with hAdef
  have hThr : ∀ m, m ≤ n * (N + 1) → JF.TransportedAlt S.G.k S.G.r A m := fun m hm =>
    thr_budget S.G.k S.G.r N A₀ hk2 hA m hm
  have hFcc : B.InCC A (n * (N + 1)) F :=
    Formalism.FourierDecayAlt.P.PBE.cutF_inCC Db hcut hCC hε A (n * (N + 1)) (by rw [hAdef]; linarith)

  have hreg : ∀ a : List C.Letter, a.length ≤ N →
      B.InCC A (n * (N + 1 - a.length)) (foldCV S.G.k S.G.r s a F) := by
    intro a
    induction a with
    | nil => intro _; simp only [List.length_nil, Nat.sub_zero]; exact hFcc
    | cons x a ih =>
      intro hl
      simp only [List.length_cons] at hl
      have h1 := ih (by omega)
      have e : n * (N + 1 - a.length) = n * (N + 1 - (a.length + 1)) + (2 * S.G.r + S.G.k + 1) := by
        rw [← hn, ← Nat.mul_succ]; congr 1; omega
      rw [e] at h1
      have h2 := hC S.G.k S.G.r _ A _ _ (x.2 : ℂ) s h1
      simp only [List.length_cons]
      exact h2
  have hOp : IsOpen (Q.OmPlus S.G.k S.G.r Db.z Db.z') := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus _ _
  intro a
  induction a with
  | nil => intro _ g _; rfl
  | cons x a ih =>
    intro hl g hg
    simp only [List.length_cons] at hl
    have ih' := ih (by omega)
    set H := foldCV S.G.k S.G.r s a F with hH
    set m : ℕ := n * (N + 1 - a.length) with hm
    have hHcc : B.InCC A m H := hreg a (by omega)
    have hnm : 2 * S.G.r + S.G.k + 1 ≤ m := by
      rw [hm, ← hn]; exact Nat.le_mul_of_pos_right n (by omega)
    have hmM : m ≤ n * (N + 1) := by rw [hm]; exact Nat.mul_le_mul_left n (by omega)
    have hThm := hThr m hmM
    have hCkn : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (B.GV S.G.k S.G.r) H :=
      Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast hnm) hHcc.choose_spec.1

    have hswap : B.JF Db (Q.CV S.G.k S.G.r (x.2 : ℂ) H) g = Q.CV S.G.k S.G.r (x.2 : ℂ) (B.JF Db H) g := by
      rw [Formalism.FourierDecayAlt.P.casimir_under_jacquet_integral S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A m H (x.2 : ℂ) hnm hThm hHcc g hg]
      show ∫ p, JF.xiP Db p • B.rho Db p (Q.CV S.G.k S.G.r (x.2 : ℂ) H) g ∂Db.μSS = _
      refine integral_congr_ae ?_
      filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS Db] with p hp
      rw [Formalism.FourierDecayAlt.P.capelli_rho_commute S.G.k S.G.r _ _ Db (x.2 : ℂ) H p hp hCkn g hg.1]

    have hJHk : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (Q.OmPlus S.G.k S.G.r Db.z Db.z' ∩ B.GV S.G.k S.G.r)
        (B.JF Db H) := by
      intro g₀ hg₀
      obtain ⟨U, F', hU, hgU, hc, he⟩ :=
        (Formalism.FourierDecayAlt.P.jacquet_derivative_formula S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A m H hThm hHcc).1 g₀
          ⟨mem_level_zero_of_mem_group hg₀.2, hg₀.1⟩
      exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast hnm), fun g hgU hgG => he g hgU (mem_level_zero_of_mem_group hgG)⟩
    have hfold : foldCV S.G.k S.G.r s a (B.JF Db F) ∈
        Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v) := foldCV_memB hcl hJF s a
    have hfk : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (Q.OmPlus S.G.k S.G.r Db.z Db.z' ∩ B.GV S.G.k S.G.r)
        (foldCV S.G.k S.G.r s a (B.JF Db F)) := by
      intro g₀ hg₀
      obtain ⟨U, F', hU, hgU, hc, he⟩ := hfold.1 g₀
        ⟨mem_level_zero_of_mem_group hg₀.2, hg₀.1.2, fun b => hg₀.1.1 _ (by simp <;> omega)⟩
      exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast le_top), fun g hgU hgG => he g hgU (mem_level_zero_of_mem_group hgG)⟩
    have hloc := coefficient_vector_locality S.G.k S.G.r _ (Q.OmPlus S.G.k S.G.r Db.z Db.z') (B.JF Db H)
      (foldCV S.G.k S.G.r s a (B.JF Db F)) (x.2 : ℂ) hOp hJHk hfk
      (fun g' hg' => ih' g' ⟨hg'.2, hg'.1⟩) g ⟨hg.2, hg.1⟩
    show B.JF Db (s • Q.CV S.G.k S.G.r (x.2 : ℂ) H) g = (s • Q.CV S.G.k S.G.r (x.2 : ℂ) (foldCV S.G.k S.G.r s a (B.JF Db F))) g
    rw [JF_smul', hswap, hloc, Pi.smul_apply]

end Formalism.FourierDecayAlt.P.CutMP.En
