import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperDevissageSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotDevissageSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w u₁ v₁ w₁

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u₁} [CommRing R]
  {G : Cell U → Type v₁} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {G' : Cell U → Type w₁} [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}

def mapH (φ : ∀ I, G I →ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) (i : ℕ) :
    H G ρ i →ₗ[R] H G' ρ' i :=
  Submodule.mapQ _ _ ((mapC φ i).restrict (p := LinearMap.ker (d G ρ i)) (q := LinearMap.ker (d G' ρ' i))
      (fun s hs => by
        change d G' ρ' i (mapC φ i s) = 0
        rw [← mapC_d φ hφ, show d G ρ i s = 0 from hs, map_zero]))
    (by
      intro s hs
      cases i with
      | zero =>
        change (s : Cochain G 0) ∈ (⊥ : Submodule R _) at hs
        rw [Submodule.mem_bot] at hs
        change (mapC φ 0 s : Cochain G' 0) ∈ (⊥ : Submodule R _)
        rw [hs, map_zero]; exact Submodule.zero_mem _
      | succ i =>
        obtain ⟨t, hts⟩ := hs
        refine ⟨mapC φ i t, ?_⟩
        change d G' ρ' i (mapC φ i t) = mapC φ (i + 1) s
        rw [← mapC_d φ hφ, hts]
        rfl)

def hEquivOfEquiv (φ : ∀ I, G I ≃ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) (i : ℕ) :
    H G ρ i ≃ₗ[R] H G' ρ' i :=
  have hψ : ∀ I J h m, (φ J).symm (ρ' I J h m) = ρ I J h ((φ I).symm m) := fun I J h m => by
    rw [LinearEquiv.symm_apply_eq, hφ, LinearEquiv.apply_symm_apply]
  LinearEquiv.ofLinearMap (mapH (fun I => (φ I).toLinearMap) hφ i)
    (mapH (fun I => (φ I).symm.toLinearMap) hψ i)
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      exact Subtype.ext (funext fun I => (φ I.1).apply_symm_apply _))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      exact Subtype.ext (funext fun I => (φ I.1).symm_apply_apply _))

end Cech

section Zero

variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} (x : Fin (N + 1) → Ω)
  (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]

def zeroFamily : SubFamily k x E where
  sub _ := ⊥
  mono _ _ _ _ hy := hy
  mem_iff I J h y := by
    simp only [Submodule.mem_bot]
    constructor
    · rintro rfl
      exact ⟨1, by simp, by simp⟩
    · rintro ⟨a, ha, hay⟩
      obtain ⟨b, hb⟩ := ha.exists_right_inv
      have hne : (a : Ω) ≠ 0 := by
        intro h0
        have h1 := congrArg (fun z : chartRing k x J => (z : Ω)) hb
        change (a : Ω) * _ = 1 at h1
        rw [h0, zero_mul] at h1
        exact zero_ne_one h1
      exact (smul_eq_zero.mp hay).resolve_left hne

end Zero

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]

omit [Module k E] [IsScalarTower k Ω E] in

theorem twist_sub_eq_bot {F : SubSystem k x E} (hF : ∀ I, F.sub I = ⊥) (Q : SubSystem k x Ω) (I : Chart x) :
    (F.twist Q).sub I = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro _ ⟨q, -, y, hy, rfl⟩
  rw [hF I, Submodule.mem_bot] at hy
  rw [hy, smul_zero]

omit [Module k E] [IsScalarTower k Ω E] in

theorem twistPows_sub_eq_bot {F : SubSystem k x E} (hF : ∀ I, F.sub I = ⊥) :
    ∀ (t : ℕ) (L : Fin t → SubSystem k x Ω) (n : Fin t → ℕ) (I : Chart x), (F.twistPows t L n).sub I = ⊥
  | 0, _, _, I => hF I
  | t + 1, _, _, I => twist_sub_eq_bot (fun I => twistPows_sub_eq_bot hF t _ _ I) _ I

omit [Module k E] [IsScalarTower k Ω E] in

theorem twist_idealSys_primeOf_sub (F : SubSystem k x E) (I : Chart x) :
    (F.twist (idealSys x (primeOf (S := k) x))).sub I = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro _ ⟨q, hq, y, -, rfl⟩
  have hq0 : q = 0 := by
    have h0 : idealMod (primeOf (S := k) x) I = ⊥ := by
      refine Submodule.span_eq_bot.mpr ?_
      rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
      rw [(mem_primeOf_of_isHomogeneous x hfe).mp hf, zero_div]
    have hq' : q ∈ (⊥ : Submodule (chartRing k x I) Ω) := h0 ▸ hq
    exact (Submodule.mem_bot _).mp hq'
  rw [hq0, zero_smul]

theorem eulerCharQuot_of_bot (F₁ F₂ : SubSystem k x E) (h : ∀ I, F₂.sub I = ⊥) :
    eulerCharQuot k F₁ F₂ = eulerChar k F₁ := by
  have hq : ∀ I, SubSystem.quotSub F₁ F₂ I = ⊥ := fun I => by
    refine (Submodule.eq_bot_iff _).mpr fun y hy => Subtype.ext ?_
    have hy' : (y : E) ∈ F₂.sub I := hy
    rw [h I, Submodule.mem_bot] at hy'
    exact hy'
  let φ : ∀ I, F₁.sub I ≃ₗ[k] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) := fun I =>
    (Submodule.quotEquivOfEqBot _ (hq I)).symm
  have hφ : ∀ I J h m, φ J (F₁.res I J h m) = SubSystem.quotRes F₁ F₂ I J h (φ I m) := fun _ _ _ _ => rfl
  unfold eulerCharQuot eulerChar
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact ((Cech.hEquivOfEquiv φ hφ i).finrank_eq).symm

end Lemmas

theorem SnapperDevissage.proof (hQ : SnapperQuotDevissage.Statement.{u, v, w}) :
    SnapperDevissage.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F hF
  obtain ⟨r, pp, a, hpp, heq⟩ := hQ k Ω N x E F (zeroFamily k x E) hF (fun _ => bot_le)
    (primeOf (S := k) x) (fun f hf d => homogeneousComponent_mem_primeOf x hf d) le_rfl
    (fun I => (twist_idealSys_primeOf_sub F.toSubSystem I).le)
  refine ⟨r, pp, a, hpp, fun t L n c => ?_⟩
  rw [← heq t L n c]
  exact (eulerCharQuot_of_bot _ _ fun I =>
    twist_sub_eq_bot (twistPows_sub_eq_bot (fun _ => rfl) t _ n) _ I).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
