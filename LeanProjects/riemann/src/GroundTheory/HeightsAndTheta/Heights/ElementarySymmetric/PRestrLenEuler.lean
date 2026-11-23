import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StRestrLenEuler
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperHyperplane
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotAdd
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechExact
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PIdealTwistFamily
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LengthQuotientEqLengthH0
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace RestrLenEuler

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem length_toNat_eq_finrank (M : Type w) [AddCommGroup M] [Module k M] :
    (Module.length k M).toNat = Module.finrank k M := by
  by_cases h : Module.Finite k M
  · rw [Module.length_eq_finrank]; rfl
  · rw [Module.finrank_of_not_finite h, Module.length_eq_rank]
    have : Cardinal.aleph0 ≤ Module.rank k M := by
      by_contra hlt
      exact h (Module.rank_lt_aleph0_iff.mp (not_le.mp hlt))
    rw [Cardinal.toENat_eq_top.mpr this]
    rfl

theorem vanish_of_fg (F : SubFamily k x Ω) (hF : ∀ I, (F.sub I).FG) :
    ∃ c₀ : ℤ, ∀ i : ℕ, 1 ≤ i → ∀ c : ℤ, c₀ ≤ c → Subsingleton ((F.toSubSystem.twist (twistSys k x c)).H i) := by
  obtain ⟨M, -, hM⟩ := Extension.full k Ω N x Ω F hF
  obtain ⟨c₀, hc₀⟩ := TildeVanish.proof SerreVanish.full k Ω N x Ω M
  have h0 : M.tildeSys 0 = F.toSubSystem := SubSystem.ext_sub fun I => hM I
  refine ⟨c₀, fun i hi c hc => ?_⟩
  rw [← h0, ← SurjectiveClosed.tildeSys_eq_twist]
  exact hc₀ i hi c hc

def incl (F₁ F₂ : SubSystem k x Ω) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I : Chart x) :
    F₂.sub I →ₗ[k] F₁.sub I where
  toFun y := ⟨y, h21 I y.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option maxHeartbeats 1000000 in

theorem quotH_subsingleton (F₁ F₂ : SubSystem k x Ω) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (i : ℕ)
    (h1 : Subsingleton (F₁.H i)) (h2 : Subsingleton (F₂.H (i + 1))) :
    Subsingleton (SubSystem.quotH F₁ F₂ i) := by
  have hdd := CechDSq.full (N + 1) (support x) k (fun I : Chart x => F₁.sub I) F₁.res
    (fun _ _ _ _ _ => LinearMap.ext fun _ => rfl)
  have L := Cech.longExact (R := k) (U := support x)
    (A := fun I : Chart x => F₂.sub I) (B := fun I : Chart x => F₁.sub I)
    (C := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
    (ρA := F₂.res) (ρB := F₁.res) (ρC := SubSystem.quotRes F₁ F₂)
    (dA := fun _ => ⊤) (dB := fun _ => ⊤) (dC := fun _ => ⊤)
    (φ := incl F₁ F₂ h21) (ψ := fun I => (SubSystem.quotSub F₁ F₂ I).mkQ)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => Submodule.mem_top)
    (fun _ _ _ => Submodule.mem_top)
    (fun I a b hab => Subtype.ext (show (a : Ω) = b from congrArg (fun z : F₁.sub I => (z : Ω)) hab))
    (fun I y => (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I)).mpr y.2)
    (fun I m _ hm => ⟨⟨m, (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I)).mp hm⟩, Submodule.mem_top, rfl⟩)
    (fun I z _ => (Submodule.Quotient.mk_surjective _ z).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
    (fun _ _ _ _ _ => Submodule.mem_top) hdd
  obtain ⟨-, hex⟩ := L
  obtain ⟨hg, δ, hgδ, -⟩ := hex i
  have hB : Subsingleton (Cech.Hdeg (fun I : Chart x => F₁.sub I) (fun _ => (⊤ : Submodule k _)) F₁.res i) :=
    haveI : Subsingleton (Cech.H (fun I : Chart x => F₁.sub I) F₁.res i) := h1
    (SnapperQuotientAdditivity.hdegTopEquiv _ _ i).toEquiv.subsingleton
  have hA : Subsingleton (Cech.Hdeg (fun I : Chart x => F₂.sub I) (fun _ => (⊤ : Submodule k _)) F₂.res (i + 1)) :=
    haveI : Subsingleton (Cech.H (fun I : Chart x => F₂.sub I) F₂.res (i + 1)) := h2
    (SnapperQuotientAdditivity.hdegTopEquiv _ _ (i + 1)).toEquiv.subsingleton
  have hC : Subsingleton (Cech.Hdeg (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
      (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₁ F₂) i) := by
    refine ⟨fun a b => ?_⟩
    have hz : ∀ y : Cech.Hdeg (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
        (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₁ F₂) i, y = 0 := by
      intro y
      obtain ⟨b, hb⟩ := (hgδ y).mp (Subsingleton.elim _ _)
      rw [← hb, Subsingleton.elim b 0, map_zero]
    rw [hz a, hz b]
  exact (SnapperQuotientAdditivity.hdegTopEquiv _ _ i).symm.toEquiv.subsingleton

end RestrLenEuler

open RestrLenEuler in

theorem RestrLenEuler.proof : RestrLenEuler.Statement.{u, w} := by
  intro k _ Ω _ _ N x qq hqq _ t L n
  set Ls : Fin t → SubSystem k x Ω := fun j => (L j).toSubSystem with hLs
  let Q : LineBundle k x := twistPowsBundle (twistBundle k x 0) t L n
  have hQ : Q.toSubSystem = (twistSys k x 0).twistPows t Ls n :=
    twistPowsBundle_toSubSystem (twistBundle k x 0) t L n
  obtain ⟨G, hG, hGfg⟩ := IdealTwistFamily.proof k Ω N x Q qq hqq
  obtain ⟨a₁, ha₁⟩ := vanish_of_fg Q.toSubFamily Q.fg
  obtain ⟨a₂, ha₂⟩ := vanish_of_fg G hGfg
  obtain ⟨a₃, ha₃⟩ := SurjectiveClosed.proof Extension.full IdealTwistFamily.proof
    (TildeVanish.proof SerreVanish.full) k Ω N x Q qq hqq
  refine Filter.eventually_atTop.mpr ⟨max a₁ (max a₂ a₃), fun c hc => ?_⟩
  have hc₁ : a₁ ≤ c := le_of_max_le_left hc
  have hc₂ : a₂ ≤ c := le_of_max_le_left (le_of_max_le_right hc)
  have hc₃ : a₃ ≤ c := le_of_max_le_right (le_of_max_le_right hc)
  set F₁ := ((twistSys k x 0).twistPows t Ls n).twist (twistSys k x c) with hF₁
  have hF₁Q : F₁ = Q.toSubSystem.twist (twistSys k x c) := by rw [hQ]
  have hF₂ : (((twistSys k x 0).twist (idealSys x qq)).twistPows t Ls n).twist (twistSys k x c) =
      F₁.twist (idealSys x qq) := by
    rw [twistPows_twist_comm, SurjectiveClosed.twist_twist_comm]
  have hF₂G : F₁.twist (idealSys x qq) = G.toSubSystem.twist (twistSys k x c) := by
    rw [hG, hF₁Q, SurjectiveClosed.twist_twist_comm]
  have h21 : ∀ I, (F₁.twist (idealSys x qq)).sub I ≤ F₁.sub I :=
    SurjectiveClosed.twist_idealSys_le F₁ qq
  have hvan : ∀ i, 1 ≤ i → Subsingleton (SubSystem.quotH F₁ (F₁.twist (idealSys x qq)) i) := by
    intro i hi
    refine quotH_subsingleton F₁ _ h21 i ?_ ?_
    · rw [hF₁Q]; exact ha₁ i hi c hc₁
    · rw [hF₂G]; exact ha₂ (i + 1) (by omega) c hc₂
  have hlift := ha₃ c hc₃
  rw [← hF₁Q] at hlift
  unfold pieceChar restrLen
  rw [hF₂, QuotientH0Length.length_secs_eq _ _ hlift, length_toNat_eq_finrank, eulerCharQuot,
    Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul]; rfl
  · intro i _ hi
    have := hvan i (Nat.one_le_iff_ne_zero.mpr hi)
    rw [Module.finrank_zero_of_subsingleton]
    simp
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) h

end

end GroundTheory.Heights₂.Heights.Kleiman
