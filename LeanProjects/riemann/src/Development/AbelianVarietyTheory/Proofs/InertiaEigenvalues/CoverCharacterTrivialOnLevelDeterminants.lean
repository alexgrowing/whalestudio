import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecEqZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.CoverXiDet

theorem natM_mem_Mb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
  have h : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.subset_span rfl
  rw [← l.prod] at h
  exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h

theorem natM_mem_of_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l l₂ : Level H)
    (I P : Ideal (𝓞 E)) (h : l₂.Mb = l.Mb * I) (hI : I ≤ P) : ((l₂.M : ℕ) : 𝓞 E) ∈ P := by
  have h1 := natM_mem_Mb l₂
  rw [h] at h1
  exact hI (Ideal.mul_le_right (I := l.Mb) (J := I) h1)

end GlobalTheory.CoverXiDet

namespace GlobalTheory.CoverXiDet

set_option maxHeartbeats 4000000 in

theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (t : Tp) (u : GA D (Wc D i)), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ t).l₂.M : ℕ) • w) → M.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC _ i Tp tup M hM t u _ hw
  have hL := hC.lev
  have hN : ∀ PP ∈ R.Q (tup t), (((M.dδ t).l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hPP =>
    natM_mem_of_half _ _ _ _ ((hM.cov t).1).2.2.2.1 ((hM.tuple t).half.2.1 PP hPP)
  obtain ⟨xi', hxi1, hxi2, -, -⟩ := GlobalTheory.TupleCover.exists_xi D (Wc D i) (R.xi (tup t)) (R.xiH (tup t)) (hL.xi (tup t))
    (hL.xi_fin (tup t)).choose (hL.xi_fin (tup t)).choose_spec.1 (hL.xi_fin (tup t)).choose_spec.2 (hL.xi_triv (tup t))
    (hL.xi_tame (tup t))
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D (Wc D i) u
  have e1 := (hM.tuple t).xi u x hx
  have e2 := hxi1 u x hx
  have e3 : xi' (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1 := by
    refine hxi2 _ (M.dδ t).l₂.odd (GlobalTheory.TupleCover.unrAt_of_not_mem R hL (tup t) _ hN) u ?_
    obtain ⟨w, hw1, hw2⟩ := hw
    exact ⟨w, (GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers D).symm ▸ hw1, hw2⟩
  apply Units.ext
  rw [e1, ← e2, e3]

end GlobalTheory.CoverXiDet
