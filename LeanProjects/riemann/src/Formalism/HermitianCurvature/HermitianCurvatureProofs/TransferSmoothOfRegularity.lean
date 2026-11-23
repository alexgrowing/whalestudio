import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSDistEigen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGradedRegFFM

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section ellw

variable {d : ℕ}

def pdc : List (Fin d) → ((Fin d → ℝ) → ℂ) → (Fin d → ℝ) → ℂ
  | [], u => u
  | i :: w, u => fun x => fderiv ℝ (pdc w u) x (Pi.single i 1)

structure SOp (d : ℕ) where
  ord : ℕ
  a : (k : Fin (ord + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ

def SOp.app (P : SOp d) (u : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x

def SOp.tr (P : SOp d) (φ : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d,
    (-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x

def SOp.symb (P : SOp d) (x ξ : Fin d → ℝ) : ℂ :=
  ∑ w : Fin P.ord → Fin d, (∏ i, (ξ (w i) : ℂ)) * P.a (Fin.last P.ord) w x

end ellw

def EllRegW : Prop :=
  ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : ι → SOp d) (U : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ),
    IsOpen U → (∀ j k w, ContDiffOn ℝ ∞ ((P j).a k w) U) → ContinuousOn u U →
    (∀ j (φ : (Fin d → ℝ) → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, u x * (P j).tr φ x = 0) →
    (∀ x ∈ U, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → ∃ j, (P j).symb x ξ ≠ 0) →
    ContDiffOn ℝ ∞ u U

def GRegJ : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (u u' : ℕ → ℝ) (J : B.Mat k r → (Wq →L[ℂ] Wp)),
    Q.IsType k r D.z D.π u → Q.IsType k r D.z' D.π' u' →
    J ∈ Gr.FFlM ((2 * r + k + 1 : ℕ) : ℕ∞) k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') →
    (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ JF.Om k r D.z D.z', Q.CV k r (Y : ℂ) J g = c • J g) →
    Q.SmoothLev k r 0 (Q.OmPlus k r D.z D.z') J

theorem transfer_smooth_of_regularity (hR : GRegJ) : JfSmoothBuilt := by
  refine ⟨100, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  have hce := JfS.class_eigenvalue_constant 100 E Wp Wq S T f χ ν' m₀ top A₀ le_rfl hB v
  obtain ⟨_, _, _, hbuilt, _, _, _, _, _, _, hk2, hA, _⟩ := hB
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, hplace, hCC, _⟩ := hv v
  have hpos : 0 ≤ ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by positivity
  have hA' : 100 * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ A₀ := hA
  have hThr : JF.TransportedAlt S.G.k S.G.r A₀ (2 * S.G.r + S.G.k + 1) :=
    Formalism.FourierDecayAlt.P.CutMP.thr_of_budget S.G.k S.G.r (S.Ntop : ℝ) A₀ hk2 (Nat.cast_nonneg _) hA'
  have hF := Gr.jf_mem_FFlM (T v).base A₀ (2 * S.G.r + S.G.k + 1) (f v) hThr (hCC _)
  obtain ⟨_, _, _, _, _, hTy, hTy'⟩ := hplace
  have hS := hR S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base _ _ (B.JF (T v).base (f v)) hTy hTy' hF
    (fun Y => ⟨_, hce.2 Y⟩)
  have hsub : ∀ g, g ∈ Q.Glev S.G.k S.G.r 0 ∩ OmP S T v →
      g ∈ Q.Glev S.G.k S.G.r 0 ∩ Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' :=
    fun g hg => ⟨hg.1, (JfS.mem_om_of_mem_omP S T v hg.1.1 hg.2).2⟩
  obtain ⟨_, hL, hRt, hU⟩ := hF
  refine ⟨fun g₀ hg₀ => hS g₀ (hsub g₀ hg₀), fun g hg n hn => hL g (hsub g hg) n hn,
    fun g hg n hn => hRt g (hsub g hg) n hn, fun g hg h hh h' hh' => hU g (hsub g hg) h hh h' hh'⟩

theorem model_place_of_regularity (hR : GRegJ) (h3 : ModelPlaceBuilt3) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_3' (transfer_smooth_of_regularity hR) h3

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
