import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsAgree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDiagonalMap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def qOf (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : (Fin r → ℂ) × ℂ :=
  (fun a => Formalism.QuantumDeterminants.cmin k r z z' g a, Formalism.QuantumDeterminants.zeta k r z z' g)

theorem qOf_contOn (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    ContinuousOn (qOf k r z z') (Q.OmPlus k r z z') := by
  refine ContinuousOn.prodMk ?_ ?_
  · refine continuousOn_pi.2 fun a => ?_
    unfold Formalism.QuantumDeterminants.cmin
    exact (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn.div (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn
      (fun g hg => hg.1 _ (Nat.le_of_lt a.isLt))
  · unfold Formalism.QuantumDeterminants.zeta
    exact (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn.div (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn
      (fun g hg => hg.1 _ le_rfl)

theorem qOf_sgs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p)
    (g : B.Mat k r) : qOf k r D.z D.z' (B.sgs p g) = qOf k r D.z D.z' g := by
  unfold qOf Formalism.QuantumDeterminants.cmin Formalism.QuantumDeterminants.zeta
  simp only [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs D hp]

theorem qOf_gq {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ}
    (hq : q ∈ JF.QDom k r D.z D.z') : qOf k r D.z D.z' (B.gq D q) = q :=
  Prod.ext (funext fun a => Formalism.FourierDecayAlt.P.BigCellZetaMinors.cmin_gq D hq a) (Formalism.FourierDecayAlt.P.BigCellZetaMinors.zeta_gq D hq)

theorem self_adjoint_locality_holds : SALocal := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ _hΘ K hK V hV hVQ hK0 y hy
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  let O : Set (B.Mat S.G.k S.G.r) := Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
    qOf S.G.k S.G.r (T v).base.z (T v).base.z' ⁻¹' V
  have hOo : IsOpen O :=
    (qOf_contOn _ _ _ _).isOpen_inter_preimage (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open _ _) hV
  have hD : ∀ x ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z', x ∈ Q.Glev S.G.k S.G.r 0 ∩
      {g | 0 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' g ∧
        ∀ a : Fin S.G.r, Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} :=
    fun x hx => ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hx.1, Formalism.FourierDecayAlt.P.CutMP.jdc_of_om _ _ hx⟩
  have hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset S.G.k S.G.r, n ∈ Q.Nlev S.G.k S.G.r 0 :=
    fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩
  have hKz : ∀ x ∈ B.GV S.G.k S.G.r, x ∈ O → K x = 0 := by
    intro x hxG hxO
    have hxOm : x ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hxG, hxO.1⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := Formalism.FourierDecayAlt.P.psiOnto_true _ _ _ _ (T v).base _ hxOm
    have hqV : q ∈ V := by
      have h1 : qOf S.G.k S.G.r (T v).base.z (T v).base.z' (B.sgs p (B.gq (T v).base q)) ∈ V := hxO.2
      rwa [qOf_sgs (T v).base hp, qOf_gq (T v).base hq] at h1
    have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
    have := LT.agree_sgs (T v).base K (fun _ => 0)
      (fun y hy n hn => hK.2.1 y (hD y hy) n (hNl n hn))
      (fun y hy n hn => hK.2.2.1 y (hD y hy) n (hNl n hn))
      (fun y hy h hh h' hh' => hK.2.2.2 y (hD y hy) h hh h' hh')
      (fun _ _ _ _ => (smul_zero _).symm) (fun _ _ _ _ => (smul_zero _).symm)
      (fun _ _ _ _ _ _ => by simp)
      hp hgq (hK0 q hqV)
    exact this
  have hyQ : y ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' :=
    ⟨(hVQ hy).1, by rw [← hTT]; exact (hVQ hy).2⟩
  have hg0 := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hyQ
  have hg0O : B.gq (T v).base y ∈ O := by
    refine ⟨hg0.2, ?_⟩
    show qOf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base y) ∈ V
    rw [qOf_gq (T v).base hyQ]; exact hy
  unfold B.opApply
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨Tm, _, rfl⟩ := List.mem_map.1 hx
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hOo Tm.word_lie hKz _ hg0.1 hg0O, map_zero]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA

end
