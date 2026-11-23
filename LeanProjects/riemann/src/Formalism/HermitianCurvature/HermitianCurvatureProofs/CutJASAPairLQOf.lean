import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsAgree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

variable {k r : ℕ}

def qOf (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : (Fin r → ℂ) × ℂ :=
  (fun a => Formalism.QuantumDeterminants.cmin k r z z' g a, Formalism.QuantumDeterminants.zeta k r z z' g)

theorem qOf_contOn (z z' : Fin (2 * r + k + 1) → ℂ) : ContinuousOn (qOf z z') (Q.OmPlus k r z z') := by
  refine ContinuousOn.prodMk ?_ ?_
  · refine continuousOn_pi.2 fun a => ?_
    show ContinuousOn (fun g : B.Mat k r => Dmin k r z z' g ⟨a.val + 1, by omega⟩ / Dmin k r z z' g ⟨a.val, by omega⟩) _
    exact (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn.div (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn
      fun g hg => hg.1 ⟨a.val, by omega⟩ (by simp)
  · show ContinuousOn (fun g : B.Mat k r => Dmin k r z z' g (Fin.last (r + 1)) / Dmin k r z z' g ⟨r, by omega⟩) _
    exact (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn.div (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn
      fun g hg => hg.1 ⟨r, by omega⟩ le_rfl

theorem isOpen_qOf (z z' : Fin (2 * r + k + 1) → ℂ) {U : Set ((Fin r → ℂ) × ℂ)} (hU : IsOpen U) :
    IsOpen (Q.OmPlus k r z z' ∩ qOf z z' ⁻¹' U) :=
  (qOf_contOn z z').isOpen_inter_preimage (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open z z') hU

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem qOf_sgs (Bs : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : Bs.inSS p) (g : B.Mat k r) :
    qOf Bs.z Bs.z' (B.sgs p g) = qOf Bs.z Bs.z' g := by
  unfold qOf Formalism.QuantumDeterminants.cmin Formalism.QuantumDeterminants.zeta
  simp only [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]

theorem qOf_gq (Bs : B.RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ JF.QDom k r Bs.z Bs.z') :
    qOf Bs.z Bs.z' (B.gq Bs q) = q :=
  Prod.ext (funext fun a => Formalism.FourierDecayAlt.P.BigCellZetaMinors.cmin_gq Bs hq a) (Formalism.FourierDecayAlt.P.BigCellZetaMinors.zeta_gq Bs hq)

theorem om_eq_sgs (Bs : B.RealPlaceData k r Wp Wq) {g : B.Mat k r} (hg : g ∈ JF.Om k r Bs.z Bs.z') :
    ∃ p, Bs.inSS p ∧ qOf Bs.z Bs.z' g ∈ JF.QDom k r Bs.z Bs.z' ∧ g = B.sgs p (B.gq Bs (qOf Bs.z Bs.z' g)) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := Formalism.FourierDecayAlt.P.psiOnto_true k r Wp Wq Bs g hg
  rw [qOf_sgs Bs hp, qOf_gq Bs hq]
  exact ⟨p, hp, hq, rfl⟩

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem agree_qOf (Bs : B.RealPlaceData k r Wp Wq) (J F : B.Mat k r → (Wq →L[ℂ] Wp)) (U : Set ((Fin r → ℂ) × ℂ))
    (hJ : J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0})
    (hag : ∀ q ∈ JF.QDom k r Bs.z Bs.z', q ∈ U → J (B.gq Bs q) = B.JF Bs F (B.gq Bs q)) :
    ∀ g ∈ JF.Om k r Bs.z Bs.z', qOf Bs.z Bs.z' g ∈ U → J g = B.JF Bs F g := by
  intro g hg hgU
  obtain ⟨p, hp, hq, hge⟩ := om_eq_sgs Bs hg
  set q := qOf Bs.z Bs.z' g with hqdef
  rw [hge]
  have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom Bs hq
  have hD : ∀ y ∈ JF.Om k r Bs.z Bs.z', y ∈ Q.Glev k r 0 ∩ {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := fun y hy =>
    ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hy.1, Formalism.FourierDecayAlt.P.CutMP.jdc_of_om _ _ hy⟩
  have hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, n ∈ Q.Nlev k r 0 := fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Bs.z Bs.z' cStd Bs.π Bs.π' Bs.μW Bs.μN Bs.μW' F Bs.z_mem Bs.z'_mem
    Bs.haarN.conc (fun n₀ h => Bs.haarN.left n₀ h)
  refine LT.agree_sgs Bs J (B.JF Bs F)
    (fun y hy n hn => hJ.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hJ.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hJ.2.2.2 y (hD y hy) h hh h' hh')
    (fun y _ n hn => ?_) (fun y _ n hn => ?_)
    (fun y _ h hh h' hh' => Formalism.FourierDecayAlt.P5.jf_uEquiv Bs F y hh hh')
    hp hgq (hag q hq hgU)
  · have e := hN y n hn 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z'_mem, mul_one] at e
    exact e
  · have e := hN y 1 WeylGroupFacts.mem_n_one n hn
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z_mem, one_mul] at e
    exact e

end Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO

end
