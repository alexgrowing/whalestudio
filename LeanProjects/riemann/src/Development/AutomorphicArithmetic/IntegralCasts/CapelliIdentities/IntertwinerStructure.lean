import Mathlib
import Formalism.HermitianCurvature.StatementMA
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreCut
import Formalism.HermitianCurvature.StatementM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeCut
import Formalism.HermitianCurvature.StatementB

noncomputable def UpperTheory.Reformulated.B.IntertwinerStructure.Intw :
    {Wp Wq : Type} →
      [inst : NormedAddCommGroup Wp] →
        [inst_1 : InnerProductSpace ℂ Wp] →
          [inst_2 : NormedAddCommGroup Wq] →
            [inst_3 : InnerProductSpace ℂ Wq] →
              [FiniteDimensional ℂ Wq] →
                (P : Formalism.FourierDecayAlt.M.Par) →
                  (Bs : Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq) →
                    (Formalism.FourierDecayAlt.M.Ty P → ℂ → Wq →L[ℂ] Wp) →
                      Formalism.FourierDecayAlt.Q.Pr ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') →
                        Formalism.FourierDecayAlt.MA.A P (Formalism.FourierDecayAlt.MA.DQ P) → Prop :=
    fun {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
        [FiniteDimensional ℂ Wq] (P : Formalism.FourierDecayAlt.M.Par) (Bs : Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq)
        (e : Formalism.FourierDecayAlt.M.Ty P → ℂ → Wq →L[ℂ] Wp) (A : Formalism.FourierDecayAlt.Q.Pr ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
        (A' : Formalism.FourierDecayAlt.MA.A P (Formalism.FourierDecayAlt.MA.DQ P)) ↦
      ∀ (Φ : ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')),
        Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR P Bs e
                  ((A.1 : ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') → ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
                    Φ) =
          Formalism.FourierDecayAlt.MA.actA P A' (Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR P Bs e Φ)

theorem UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum :
    ∀ {Wp Wq : Type} [inst : NormedAddCommGroup Wp] [inst_1 : InnerProductSpace ℂ Wp] [inst_2 : NormedAddCommGroup Wq]
      [inst_3 : InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [inst_5 : FiniteDimensional ℂ Wq] {P : Formalism.FourierDecayAlt.M.Par}
      {Bs : Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq} {e : Formalism.FourierDecayAlt.M.Ty P → ℂ → Wq →L[ℂ] Wp},
      (∀ (Φ : ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (ρ : Formalism.FourierDecayAlt.M.Ty P),
          Formalism.FourierDecayAlt.P.CutMP.Gauge.rawR P Bs.μsec e (↑Φ : Formalism.FourierDecayAlt.Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈
            Formalism.FourierDecayAlt.MA.smSub P.r P.TT) →
        ∀ {ι : Type} (s : Finset ι) {A : ι → Formalism.FourierDecayAlt.Q.Pr ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
          {A' : ι → Formalism.FourierDecayAlt.MA.A P (Formalism.FourierDecayAlt.MA.DQ P)},
          (∀ i ∈ s, UpperTheory.Reformulated.B.IntertwinerStructure.Intw P Bs e (A i) (A' i)) → UpperTheory.Reformulated.B.IntertwinerStructure.Intw P Bs e (∑ i ∈ s, A i) (∑ i ∈ s, A' i) := by
  intro Wp Wq _ _ _ _ _ _ P Bs e hs ι s A A' h
  have hv : ∀ Φ ρ q, (Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR P Bs e Φ ρ).1 q =
      Formalism.FourierDecayAlt.P.CutMP.Gauge.rawR P Bs.μsec e Φ.1 ρ q := fun Φ ρ q => by
    simp only [Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR, Formalism.FourierDecayAlt.MA.toSm, dif_pos (hs Φ ρ)]
  have hh : ∀ X Y : Wq →L[ℂ] Wp, Formalism.FourierDecayAlt.B.hsVec (X + Y) = Formalism.FourierDecayAlt.B.hsVec X + Formalism.FourierDecayAlt.B.hsVec Y := fun _ _ => rfl
  let T : _ →+ _ := AddMonoidHom.mk' (Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR P Bs e) fun Φ Ψ => funext fun ρ => Subtype.ext <|
    funext fun q => (hv _ ρ q).trans <| Eq.trans (by simp [Formalism.FourierDecayAlt.P.CutMP.Gauge.rawR, hh, inner_add_right, mul_add])
      (congrArg₂ (· + ·) (hv Φ ρ q) (hv Ψ ρ q)).symm
  refine Finset.sum_induction (p := fun x : _ × _ => UpperTheory.Reformulated.B.IntertwinerStructure.Intw P Bs e x.1 x.2) (fun i => (A i, A' i))
    (fun a b ha hb Φ => (T.map_add _ _).trans ((congrArg₂ (· + ·) (ha Φ) (hb Φ)).trans
      (funext fun ρ => Finset.sum_add_distrib.symm)))
    (fun Φ => T.map_zero.trans (funext fun ρ => Finset.sum_const_zero.symm)) h |> fun H => ?_
  simpa only [Prod.fst_sum, Prod.snd_sum] using H
