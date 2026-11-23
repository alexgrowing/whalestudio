import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section defs

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def capA (k r : ℕ) (y : ℂ) (F : Q.Mx k r → X) : Q.Mx k r → X := C3.AAop k r r le_rfl (Q.uC k r 0 y) F

def capAv (k r : ℕ) (y : ℂ) (F : Q.Mx k r → X) : Q.Mx k r → X :=
  C3.AAvop k r r le_rfl (y - ((2 * r + k : ℕ) : ℂ) / 2) F

def capBeta (k r : ℕ) (c : Fin r → Fin (2 * r + k + 1)) (g : Q.Mx k r) : ℂ :=
  Matrix.det (Matrix.of fun a l : Fin r => herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE le_rfl a))))

def capAlphaV (k r : ℕ) (B : Fin r → Fin (2 * r + k + 1)) (g : Q.Mx k r) : ℂ :=
  Matrix.det (Matrix.of fun a l : Fin r => ((Hpk k r * gᴴ * Hpk k r) *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l))

end defs

def JDACapRep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (y : ℂ),
    ∃ Θ Θv : B.DiffOp k r Wp Wq,
      PolyOp (2 * r + k + 1) ((r + 1) * (2 * r + k + 1)) Θ ∧ PolyOp (2 * r + k + 1) ((r + 1) * (2 * r + k + 1)) Θv ∧
      B.opOrder Θ = r ∧ B.opOrder Θv = r ∧
      (∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), g ∈ B.GV k r → B.CkOn (B.opOrder Θ : ℕ∞) {g} F →
        B.opApply Θ F g = capA k r y F g) ∧
      ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), g ∈ B.GV k r → B.CkOn (B.opOrder Θv : ℕ∞) {g} F →
        B.opApply Θv F g = capAv k r y F g

def JDACapInv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ (y : ℂ) (Θ : B.DiffOp P.k P.r Wp Wq), P.r ≤ B.opOrder Θ →
      ((∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = capA P.k P.r y F g) →
        B.Commutes Bs (B.GPos Bs) Θ) ∧
      ((∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r), g ∈ B.GV P.k P.r →
          B.CkOn (B.opOrder Θ : ℕ∞) {g} F → B.opApply Θ F g = capAv P.k P.r y F g) →
        B.Commutes Bs (B.GPos Bs) Θ)

def JDACapToda : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        Q.resG P.k P.r (Fin.last P.r) (capA P.k P.r y J) c g =
          dMul (drF P.r) (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)) c g

def JDACapTodaV : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        Q.resG P.k P.r (Fin.last P.r) (capAv P.k P.r y J) c g =
          dMul (drbF P.r) (Q.crd (Q.cmp (vABm P.r y P.r) 0) (Q.resG P.k P.r (Fin.last P.r) J)) c g

section assembly

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem capa_J_ck (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) {J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs)) {c : Fin P.r → ℂ} (hc : c ∈ OmX P.r)
    {g : Q.Mx P.k P.r} (hg : g ∈ Q.Glev P.k P.r (Fin.last P.r))
    (hcg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs) (m : ℕ∞) :
    Q.wCell P.k P.r (Fin.last P.r) c * g ∈ B.GV P.k P.r ∧ B.CkOn m {Q.wCell P.k P.r (Fin.last P.r) c * g} J := by
  have hGV : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ B.GV P.k P.r := Formalism.FourierDecayAlt.P.PBF.wCell_mul_GV hc hg
  refine ⟨hGV, fun g₀ hg₀ => ?_⟩
  rw [Set.mem_singleton_iff] at hg₀
  subst hg₀
  have hG0 : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Q.Glev P.k P.r 0 :=
    ⟨hGV, fun a ha => absurd ha (Nat.not_lt_zero _)⟩
  obtain ⟨U, F, hU, hmem, hF, hJF⟩ := hJ.1 _ ⟨hG0, hcg⟩
  refine ⟨U, F, hU, hmem, hF.of_le ?_, fun x hx hxG => hJF x hx ⟨hxG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩⟩
  exact_mod_cast le_top

end assembly

theorem jDAGrp_of_parts (hR : JDACapRep) (hI : JDACapInv) (hT : JDACapToda) (hTv : JDACapTodaV) : JDAGrp := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -, -, -, -, -, -, hk, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  obtain ⟨Θ, Θv, hP, hPv, hO, hOv, hA, hAv⟩ := hR S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) y
  refine ⟨Θ, Θv, hP, hPv, (hI _ _ (D.parOf S v) (T v).base hpl hk y Θ hO.ge).1 hA,
    (hI _ _ (D.parOf S v) (T v).base hpl hk y Θv hOv.ge).2 hAv, fun J hJ c hc g hg hcg => ⟨?_, ?_⟩⟩
  · obtain ⟨hGV, hCk⟩ := capa_J_ck (D.parOf S v) (T v).base hJ hc hg hcg (B.opOrder Θ)
    rw [← hT _ _ (D.parOf S v) (T v).base hpl hk y J hJ c hc g hg hcg]
    simp only [Q.resG]
    rw [hA J _ hGV hCk]
  · obtain ⟨hGV, hCk⟩ := capa_J_ck (D.parOf S v) (T v).base hJ hc hg hcg (B.opOrder Θv)
    rw [← hTv _ _ (D.parOf S v) (T v).base hpl hk y J hJ c hc g hg hcg]
    simp only [Q.resG]
    rw [hAv J _ hGV hCk]

end

end Formalism.FourierDecayAlt.P.CutMP
