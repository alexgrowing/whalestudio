import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCVPresFF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOrbitSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem foldCV_nil (k r : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) (H : B.Mat k r → E) :
    foldCV k r s [] H = H := rfl

theorem foldCV_cons (k r : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) (x : C.Letter)
    (a : List C.Letter) (H : B.Mat k r → E) :
    foldCV k r s (x :: a) H = s • Q.CV k r (x.2 : ℂ) (foldCV k r s a H) := rfl

theorem foldCV_mem {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Q.Mx k r)}
    (hcl : ∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (Y : ℝ) (s : ℂ), s • Q.CV k r (Y : ℂ) J ∈ Q.FFl k r z z' π π' 0 Dm)
    {J : Q.Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ Q.FFl k r z z' π π' 0 Dm) (s : ℂ) :
    ∀ a : List C.Letter, foldCV k r s a J ∈ Q.FFl k r z z' π π' 0 Dm
  | [] => hJ
  | x :: a => hcl _ (foldCV_mem hcl hJ s a) x.2 s

theorem om_sub {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    g ∈ Q.Glev k r 0 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  obtain ⟨hU, hD, hG⟩ := hg
  refine ⟨⟨hU, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hG, fun a => hD _ ?_⟩
  show (a : ℕ) + 1 ≤ r
  omega

theorem energyTr_of_parts (hR : FoldRev) (hL : AdmLen) (hBF : BesselFoldBuilt) (hL2 : L2BoundAtTowerPlace) (hBe : BetaFrame) :
    EnergyTr := by
  refine ⟨100, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hcl ε hε hJF a hadm
  have hB' := hB
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, _, _, _, _⟩, _, _, _⟩ := hB'
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, hplace, _, _⟩ := hv v
  have hlen : a.length ≤ S.Ntop := hL E Wp Wq S v a hadm
  set Db := (T v).base with hDb
  set s : ℂ := M.sgn (D.parOf S v) (S.l + 1) with hs
  set F := D.cutF Db χ (f v) ε with hF
  set J₁ := foldCV S.G.k S.G.r s a.reverse (B.JF Db F) with hJ₁
  have hJ₁m : J₁ ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v) := foldCV_mem hcl hJF s _
  have hOpen : IsOpen (OmP S T v) := (isDom_omP Db.z_mem Db.z'_mem).1

  have hae : ∀ᵐ p ∂(volume : Measure ((Fin S.G.r → ℂ) × ℂ)),
      bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p = 0 ∨
        B.JF Db (foldCV S.G.k S.G.r s a F) (B.gq Db p) = J₁ (B.gq Db p) := by
    have h0 := ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_restrict Db)
    filter_upwards [h0] with p hp
    by_cases hq : p ∈ B.Qset Db
    · right
      have hg := Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db p (hp hq)
      rw [hBF E Wp Wq S T f χ ν' m₀ top A₀ hB v hcl ε hε hJF a hlen _ hg]
      exact (hR _ _ _ _ _ _ _ _ _ hOpen hcl _ hJF s a _ (om_sub hg)).symm
    · left
      exact le_antisymm (not_lt.1 hq) (Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ p)
  have hN1 : jNormSq S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z')
      (fun q => B.hsVec (J₁ (B.gq Db q))) ≠ ⊤ := by
    have h := hL2 E Wp Wq S T f χ ν' m₀ top A₀ hB v ε hε a hlen
    unfold B.normSq at h
    unfold jNormSq at h ⊢
    rwa [lintegral_congr_ae (hae.mono fun p hp => ?_)] at h
    rcases hp with hp | hp
    · rw [show bcWeight S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z') p = 0 from hp]
      simp
    · show ENNReal.ofReal (_ * ‖B.hsVec (B.JF Db (foldCV S.G.k S.G.r s a F) (B.gq Db p))‖ ^ 2) = _
      rw [hp]
  have hN2 : jNormSq S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z')
      (fun q => B.hsVec (B.JF Db F (B.gq Db q))) ≠ ⊤ :=
    hL2 E Wp Wq S T f χ ν' m₀ top A₀ hB v ε hε [] (Nat.zero_le _)
  have hBeq := hBe E Wp Wq S T v hplace e hFr J₁ hJ₁m (B.JF Db F) hJF hN1 hN2
  unfold C7.principalHermitianLattice B.beta
  show _ = MA.ipA (D.parOf S v) (trJ S T v e J₁) (trJ S T v e (B.JF Db F))
  rw [← hBeq]
  unfold betaBig
  refine integral_congr_ae (hae.mono fun p hp => ?_)
  rcases hp with hp | hp
  · show ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) * _ =
      ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) * _
    rw [hp]; simp
  · show ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) *
        inner ℂ (B.hsVec (B.JF Db F (B.gq Db p))) (B.hsVec (B.JF Db (foldCV S.G.k S.G.r s a F) (B.gq Db p))) =
      ((bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') p : ℝ) : ℂ) *
        inner ℂ (B.hsVec (B.JF Db F (B.gq Db p))) (B.hsVec (J₁ (B.gq Db p)))
    rw [hp]

end Formalism.FourierDecayAlt.P.CutMP.En
