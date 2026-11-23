import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocHat

open GlobalTheory.StdFrames (cpt cpt_ext toAd_spec)

variable {D : D7} {n : ℕ}

theorem mem_hat_iff_locL {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG) (y : Fin n → EAf D) :
    y ∈ hat Λ ↔ ∀ v : HeightOneSpectrum (𝓞 D.host.F),
      (fun i => Formalism.UG.prV (E := D.host.E) v (y i)) ∈ Formalism.L2.Herm.locL v Λ := by
  haveI : Module.Finite (𝓞 D.host.E) Λ := Module.Finite.iff_fg.mpr h
  rw [mem_hat]
  exact GlobalTheory.LatticeStabLocal.mem_latS_adele_iff Λ y

theorem prV_eq_zero_iff_cpt (v : HeightOneSpectrum (𝓞 D.host.F)) (z : EAf D) :
    Formalism.UG.prV (E := D.host.E) v z = 0 ↔ ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → cpt Q z = 0 := by
  refine (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (toAd_spec D) v z).trans ?_
  exact Iff.rfl

theorem mem_hat_iff_of_supp {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG)
    (v : HeightOneSpectrum (𝓞 D.host.F)) {y : Fin n → EAf D}
    (hy : ∀ w, w ≠ v → ∀ i, Formalism.UG.prV (E := D.host.E) w (y i) = 0) :
    y ∈ hat Λ ↔ (fun i => Formalism.UG.prV (E := D.host.E) v (y i)) ∈ Formalism.L2.Herm.locL v Λ := by
  rw [mem_hat_iff_locL h]
  refine ⟨fun H => H v, fun H w => ?_⟩
  by_cases hwv : w = v
  · subst hwv
    exact H
  · have hz : (fun i => Formalism.UG.prV (E := D.host.E) w (y i)) = 0 := by
      ext i
      exact hy w hwv i
    rw [hz]
    exact Submodule.zero_mem _
set_option maxHeartbeats 800000 in

theorem locL_le {Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG) (h' : Λ'.FG)
    (v : HeightOneSpectrum (𝓞 D.host.F))
    (H : ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → ∀ y : Fin n → EAf D, idem Q • y ∈ hat Λ → idem Q • y ∈ hat Λ') :
    Formalism.L2.Herm.locL v Λ ≤ Formalism.L2.Herm.locL v Λ' := by
  obtain ⟨e, -, -, he1, he0⟩ :=
    GlobalTheory.StdFrames.exists_idem (D := D) {Q : Pl D.host.E | Q.under (𝓞 D.host.F) = v}

  have hpe : Formalism.UG.prV (E := D.host.E) v e = 1 := by
    have h0 : Formalism.UG.prV (E := D.host.E) v (e - 1) = 0 := by
      rw [prV_eq_zero_iff_cpt]
      intro Q hQ
      rw [map_sub, map_one, he1 Q hQ, sub_self]
    rwa [map_sub, map_one, sub_eq_zero] at h0

  have key : ∀ x ∈ Λ, (e • fun i => inc D (x i)) ∈ hat Λ' := by
    intro x hx
    refine mem_hat_of_idem h' fun w => ?_
    rw [smul_smul]
    by_cases hw : w.under (𝓞 D.host.F) = v
    · have hwe : idem w * e = idem w := by
        refine cpt_ext fun Q => ?_
        rw [map_mul]
        by_cases hQ : Q = w
        · subst hQ
          rw [cpt_idem_self, he1 Q hw, one_mul]
        · rw [cpt_idem_ne hQ, zero_mul]
      rw [hwe]
      exact H w hw _ (smul_mem_hat (idem_mem w) (inc_mem_hat hx))
    · have hwe : idem w * e = 0 := by
        refine cpt_ext fun Q => ?_
        rw [map_mul, map_zero]
        by_cases hQ : Q = w
        · subst hQ
          rw [he0 Q hw, mul_zero]
        · rw [cpt_idem_ne hQ, zero_mul]
      rw [hwe, zero_smul]
      exact zero_mem_hat

  unfold Formalism.L2.Herm.locL Formalism.UG.latS
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  have hm := (mem_hat_iff_locL h' _).mp (key x hx) v
  have hxe : (fun i => Formalism.UG.prV (E := D.host.E) v ((e • fun i => inc D (x i)) i)) =
      fun i => Formalism.UG.inclE (F := D.host.F) (v.adicCompletion D.host.F) (x i) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hpe, one_mul]
    rw [Formalism.UG.P.afsplit_prV_inclE]
  rw [hxe] at hm
  exact hm

theorem prV_idem_smul {v : HeightOneSpectrum (𝓞 D.host.F)} {Q : Pl D.host.E} (hQ : Q.under (𝓞 D.host.F) = v)
    (y : Fin n → EAf D) : ∀ w, w ≠ v → ∀ i, Formalism.UG.prV (E := D.host.E) w ((idem Q • y) i) = 0 := by
  intro w hw i
  have hQw : Formalism.UG.prV (E := D.host.E) w (idem Q) = 0 := by
    rw [prV_eq_zero_iff_cpt]
    intro Q' hQ'
    apply cpt_idem_ne
    intro hEq
    subst hEq
    exact hw (hQ'.symm.trans hQ)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, hQw, zero_mul]

theorem locL_eq_iff_idem : ∀ (D : D7) (n : ℕ) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Λ.FG → Λ'.FG → ∀ v : HeightOneSpectrum (𝓞 D.host.F), Formalism.L2.Herm.locL v Λ = Formalism.L2.Herm.locL v Λ' ↔ ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → ∀ y : Fin n → EAf D, idem Q • y ∈ hat Λ ↔ idem Q • y ∈ hat Λ' := by
  intro D n Λ Λ' h h' v
  constructor
  · intro heq Q hQ y
    rw [mem_hat_iff_of_supp h v (prV_idem_smul hQ y), mem_hat_iff_of_supp h' v (prV_idem_smul hQ y), heq]
  · intro H
    exact le_antisymm (locL_le h h' v fun Q hQ y => (H Q hQ y).mp)
      (locL_le h' h v fun Q hQ y => (H Q hQ y).mpr)

end GlobalTheory.LocHat
