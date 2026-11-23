import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceRead

open GlobalTheory.TwistGood

theorem twistOf_good (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X) (hρ : ρ.Good)
    (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ)
    (e : X.Ok i k →+* ℂ) (hψ : Formalism.MainNotions.IntegralHeckeForms.TwOK i k Q ψ) :
    (twistOf ρ.rc e (ρ.ch i) Q ψ).Good ∧ (ρ.B i j b).admitted (twistOf ρ.rc e (ρ.ch i) Q ψ).Q := by
  classical
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := hψ
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) Q) := GlobalTheory.T.chosenPlaces_admissible_goodSetup D N X ρ hρ i j b Q hsplit hdisj
  let g : (X.Ok i k)ˣ →* Circle := unitPart.comp (Units.map e.toMonoidHom)
  have hkey : charOf ρ.rc e ψ = ρ.rc.pull (g.comp ψ) := by
    rw [Recip.pull_comp _ hopen]
    rfl
  have hz : X.zk i k ^ (X.l i ^ k) = 1 := Units.ext (by simpa using (X.zk_prim i k).pow_eq_one)
  have hpow : ∀ σ, ψ σ ^ (X.l i ^ k) = 1 := by
    intro σ
    obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  refine ⟨?_, hadm⟩
  show (⟨half (ρ.ch i) Q, charOf ρ.rc e ψ, resOf (charOf ρ.rc e ψ)⟩ : Twist D Circle).Good
  rw [hkey]
  refine GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D N X ρ.rc hρ.rc Circle (g.comp ψ) (X.l i) (X.lPrime i).out
    (fun σ => ⟨k, by rw [MonoidHom.comp_apply, ← map_pow, hpow, map_one]⟩) ?_ ?_ _ ?_ ?_ ?_
  · exact Subgroup.isOpen_mono (H₁ := ψ.ker) (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]) hopen
  · intro x x' hx
    show g (ψ x') = (g (ψ x))⁻¹
    rw [hanti x x' hx, map_inv]
  · obtain ⟨P, -, h2, h3⟩ := hadm.1.split
    exact h3.mono (Finset.subset_union_right.trans h2)
  · intro P hP hl
    exact Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 (X.twistExcludedPlaces_contains_residueChar i (show P ∈ placesOver D.host.E (X.l i) from hl))
  · intro v hv hnc B hB σ hσ
    have hvQ : v ∉ Q := by
      intro hvQ
      by_cases hc : v ∈ ρ.ch i
      · exact hv (mem_half.2 ⟨hvQ, hc⟩)
      · obtain ⟨v', hv'⟩ := GlobalTheory.TwistDet.exists_isConjPl v
        have hv'Q : v' ∈ Q := ramExactly_conj X ψ _ hanti hram v hvQ v' hv'
        have hne := ne_of_split (hsplit v hvQ) hv'
        have hv'c : v' ∈ ρ.ch i := by
          by_contra h
          exact hc (((hρ.ch i).pair v v' hv' hne).2 h)
        exact hnc v' (mem_half.2 ⟨hv'Q, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')
    have h1 : ψ σ = 1 := by
      by_contra h
      exact hvQ ((hram v B hB).1 ⟨σ, hσ, h⟩)
    rw [MonoidHom.comp_apply, h1, map_one]

theorem twVia_good : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw), ρ.Good → TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w) → ∀ (j : Fin D.R.m) (ι : KE c w →+* ℂ),
  (twVia ρ ι).Good ∧ (ρ.B (c.twI w) j (c.sd w)).admitted (twVia ρ ι).Q ∧ ∀ τ : ℂ ≃+* ℂ, ConjChar τ (twVia ρ ι) (twVia ρ ((τ : ℂ →+* ℂ).comp ι)) := by
  intro D c w ρ hρ hψ j ι
  obtain ⟨h1, h2⟩ := twistOf_good D D.nd D.ntw ρ hρ (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) (viaOk ι) hψ
  refine ⟨h1, h2, fun τ => ⟨rfl, fun x => ?_⟩⟩
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  have hn : D.ntw.l (c.twI w) ^ (c.k' w) ≠ 0 := pow_ne_zero _ (D.ntw.lPrime (c.twI w)).out.ne_zero
  have hp : chr c w σ ^ (D.ntw.l (c.twI w) ^ (c.k' w)) = 1 := by
    obtain ⟨n, hn⟩ := hψ.2.2.2.2.1 σ
    have hz : D.ntw.zk (c.twI w) (c.k' w) ^ (D.ntw.l (c.twI w) ^ (c.k' w)) = 1 :=
      Units.ext (by simpa using (D.ntw.zk_prim (c.twI w) (c.k' w)).pow_eq_one)
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  change ((charOf ρ.rc (viaOk ((τ : ℂ →+* ℂ).comp ι)) (chr c w) x : Circle) : ℂ) =
    τ ((charOf ρ.rc (viaOk ι) (chr c w) x : Circle) : ℂ)
  rw [charOf_eq ρ.rc _ hψ.2.2.1 hσ hn hp, charOf_eq ρ.rc _ hψ.2.2.1 hσ hn hp]
  rfl

end GlobalTheory.PlaceRead

end
