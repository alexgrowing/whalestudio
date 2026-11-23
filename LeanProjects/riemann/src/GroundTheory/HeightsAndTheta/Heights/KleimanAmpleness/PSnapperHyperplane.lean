import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PIdealTwistFamily
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperHyperplaneSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperHyperplaneMidSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotAddSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotDevissageSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem twistPows_twist_comm (F Q : SubSystem S x Ω) :
    ∀ (t : ℕ) (L : Fin t → SubSystem S x Ω) (n : Fin t → ℕ),
      (F.twist Q).twistPows t L n = (F.twistPows t L n).twist Q
  | 0, _, _ => rfl
  | t + 1, L, n => by
    simp only [SubSystem.twistPows]
    rw [twistPows_twist_comm F Q t, SubSystem.twist_assoc, SubSystem.twist_comm Q, ← SubSystem.twist_assoc]

def twistPowsBundle (F : LineBundle S x) :
    (t : ℕ) → (Fin t → LineBundle S x) → (Fin t → ℕ) → LineBundle S x
  | 0, _, _ => F
  | t + 1, L, n => (twistPowsBundle F t (fun j => L j.castSucc) (fun j => n j.castSucc)).tensorProd
      ((L (Fin.last t)).powBundle (n (Fin.last t)))

theorem twistPowsBundle_toSubSystem (F : LineBundle S x) :
    ∀ (t : ℕ) (L : Fin t → LineBundle S x) (n : Fin t → ℕ),
      (twistPowsBundle F t L n).toSubSystem = F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n
  | 0, _, _ => rfl
  | t + 1, L, n => by
    change (twistPowsBundle F t (fun j => L j.castSucc) (fun j => n j.castSucc)).toSubSystem.twist
      ((L (Fin.last t)).powBundle (n (Fin.last t))).toSubSystem = _
    rw [twistPowsBundle_toSubSystem F t, LineBundle.powBundle_toSubSystem]
    rfl

theorem idealMod_le_one (J : Ideal (Poly S N)) (I : Chart x) : idealMod J I ≤ 1 := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, s, e, -, hs, hf, hse, rfl⟩
  exact Submodule.mem_one.mpr ⟨⟨_, f, s, e, hs, hf, hse, rfl⟩, rfl⟩

theorem idealMod_le_of_le {J J' : Ideal (Poly S N)} (h : J ≤ J') (I : Chart x) :
    idealMod J I ≤ idealMod J' I :=
  Submodule.span_mono fun _ ⟨f, s, e, hf, hs, hfe, hse, hz⟩ => ⟨f, s, e, h hf, hs, hfe, hse, hz⟩

theorem twist_idealSys_sub_le (Q : SubSystem S x Ω) (J : Ideal (Poly S N)) (I : Chart x) :
    (Q.twist (idealSys x J)).sub I ≤ Q.sub I := by
  rw [SubSystem.twist_sub_eq_mul_of_line]
  exact (Submodule.mul_le.mpr fun a ha b hb => Submodule.mul_mem_mul (idealMod_le_one J I ha) hb).trans (one_mul _).le

theorem twist_idealSys_sub_mono (Q : SubSystem S x Ω) {J J' : Ideal (Poly S N)} (h : J ≤ J') (I : Chart x) :
    (Q.twist (idealSys x J)).sub I ≤ (Q.twist (idealSys x J')).sub I := by
  rw [SubSystem.twist_sub_eq_mul_of_line, SubSystem.twist_sub_eq_mul_of_line]
  exact Submodule.mul_le.mpr fun a ha b hb => Submodule.mul_mem_mul (idealMod_le_of_le h I ha) hb

end Helpers

theorem sup_span_X_homogeneous {R : Type u} [CommRing R] {N : ℕ} (pp : Ideal (Poly R N))
    (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) (i : Fin (N + 1)) :
    ∀ f ∈ pp ⊔ Ideal.span {(X i : Poly R N)}, ∀ d : ℕ,
      homogeneousComponent d f ∈ pp ⊔ Ideal.span {(X i : Poly R N)} := by
  intro f hf d
  obtain ⟨g, hg, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  rw [map_add]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (hh g hg d)) (Ideal.mem_sup_right ?_)
  have hspan := IdealTwistFamily.homogeneousComponent_mul_form r (X i) (isHomogeneous_X R i) d
  refine (Submodule.span_le.mpr ?_ : _ ≤ (Ideal.span {(X i : Poly R N)}).restrictScalars R) hspan
  rintro _ ⟨z, d', -, -, rfl⟩
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem SnapperHyperplane.proof (hA : SnapperQuotAdd.Statement.{u, w, w})
    (hD : SnapperQuotDevissage.Statement.{u, w, w}) (hM : SnapperHyperplaneMid.Statement.{u, w}) :
    SnapperHyperplane.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hp hh hle i hi a
  set J : Ideal (Poly k N) := pp ⊔ Ideal.span {(X i : Poly k N)} with hJdef
  let B := twistBundle k x (a + 1)
  let F₂ : SubFamily k x Ω :=
    { B.twist (idealSys x J) with mem_iff := IdealTwistFamily.twist_mem_iff B J }
  obtain ⟨r, qq, b, hqq, heq⟩ := hD k Ω N x Ω B.toSubFamily F₂ B.fg
    (fun I => twist_idealSys_sub_le B.toSubSystem J I) J (sup_span_X_homogeneous pp hh i)
    (hle.trans le_sup_left) (fun I => le_rfl)
  refine ⟨r, qq, b, fun m => ⟨(hqq m).1, (hqq m).2.1, le_sup_left.trans (hqq m).2.2,
    (hqq m).2.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩, fun t L n c => ?_⟩
  let Q := (twistPowsBundle B t L n).tensorProd (twistBundle k x c)
  have hQ : Q.toSubSystem =
      ((twistSys k x (a + 1)).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c) := by
    change (twistPowsBundle B t L n).toSubSystem.twist (twistSys k x c) = _
    rw [twistPowsBundle_toSubSystem]
    rfl
  have hG : ∀ K : Ideal (Poly k N),
      (((twistSys k x (a + 1)).twist (idealSys x K)).twistPows t (fun j => (L j).toSubSystem) n).twist
        (twistSys k x c) = Q.toSubSystem.twist (idealSys x K) := by
    intro K
    rw [hQ, twistPows_twist_comm (twistSys k x (a + 1)) (idealSys x K), SubSystem.twist_assoc,
      SubSystem.twist_comm (idealSys x K), ← SubSystem.twist_assoc]
  let G₂ : SubFamily k x Ω := { Q.twist (idealSys x J) with mem_iff := IdealTwistFamily.twist_mem_iff Q J }
  let G₃ : SubFamily k x Ω := { Q.twist (idealSys x pp) with mem_iff := IdealTwistFamily.twist_mem_iff Q pp }
  have hadd : eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x pp)) =
      eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) +
        eulerCharQuot k (Q.toSubSystem.twist (idealSys x J)) (Q.toSubSystem.twist (idealSys x pp)) :=
    hA k Ω N x Ω Q.toSubFamily G₂ G₃ Q.fg (fun I => twist_idealSys_sub_le Q.toSubSystem J I)
      (fun I => twist_idealSys_sub_mono Q.toSubSystem le_sup_left I)
  have h1 : pieceChar k pp a L n (c + 1) =
      eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x pp)) := by
    have eA : ((twistSys k x a).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x (c + 1)) =
        Q.toSubSystem := by
      rw [hQ, ← twistSys_twist_eq_add a 1,
        twistPows_twist_comm (twistSys k x a) (twistSys k x 1), SubSystem.twist_assoc,
        twistSys_twist_eq_add, add_comm 1 c]
    have eB : (((twistSys k x a).twist (idealSys x pp)).twistPows t (fun j => (L j).toSubSystem) n).twist
        (twistSys k x (c + 1)) = Q.toSubSystem.twist (idealSys x pp) := by
      rw [← hG pp, ← twistSys_twist_eq_add a 1, SubSystem.twist_assoc (twistSys k x a),
        SubSystem.twist_comm (twistSys k x 1), ← SubSystem.twist_assoc (twistSys k x a),
        twistPows_twist_comm ((twistSys k x a).twist (idealSys x pp)) (twistSys k x 1),
        SubSystem.twist_assoc _ (twistSys k x 1), twistSys_twist_eq_add, add_comm 1 c]
    unfold pieceChar
    rw [eA, eB]
  have h2 : eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) =
      ∑ m, pieceChar k (qq m) (b m) L n c := by
    have := heq t L n c
    change eulerCharQuot k
      (((twistSys k x (a + 1)).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
      ((((twistSys k x (a + 1)).twist (idealSys x J)).twistPows t (fun j => (L j).toSubSystem) n).twist
        (twistSys k x c)) = _ at this
    rwa [hG J, ← hQ] at this
  have h3 := hM k Ω N x pp hp hh hle i hi a t L n c
  rw [← hJdef, hG J, hG pp] at h3
  rw [h1, hadd, h2, h3]
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman
