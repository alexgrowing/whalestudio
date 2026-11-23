import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder

namespace GlobalTheory.CompanionTheory.Ar.BT.OpsModel

open GlobalTheory.CompanionTheory.Ar.BT

variable {R : Type} [CommRing R] {T H : Type} [CommGroup T] [CommGroup H]

theorem pullFun_apply (ι : H →* T) (f : T → R) (h : H) : pullFun R ι f h = f (ι h) := rfl

theorem mem_quotOrder (π : T →* H) (A : Subalgebra R (T → R)) (f : H → R) :
    f ∈ quotOrder π A ↔ (fun t => f (π t)) ∈ A := Iff.rfl

theorem mem_resOrder (ι : H →* T) (A : Subalgebra R (T → R)) (g : H → R) :
    g ∈ resOrder ι A ↔ ∃ f ∈ A, (fun h => f (ι h)) = g := Iff.rfl

theorem resOrder_id (A : Subalgebra R (T → R)) : resOrder (MonoidHom.id T) A = A := by
  ext g
  rw [mem_resOrder]
  exact ⟨fun ⟨f, hf, e⟩ => e ▸ hf, fun hg => ⟨g, hg, rfl⟩⟩

theorem quotOrder_id (A : Subalgebra R (T → R)) : quotOrder (MonoidHom.id T) A = A := by
  ext g; rfl

theorem resOrder_top (ι : H →* T) (hι : Function.Injective ι) :
    resOrder ι (⊤ : Subalgebra R (T → R)) = ⊤ := by
  refine eq_top_iff.2 fun g _ => ?_
  rw [mem_resOrder]
  exact ⟨Function.extend ι g 0, trivial, funext fun h => hι.extend_apply _ _ _⟩

theorem resOrder_mu_le (ι : H →* T) : resOrder ι (muOrder R T) ≤ muOrder R H := by
  unfold resOrder muOrder
  rw [AlgHom.map_adjoin]
  refine Algebra.adjoin_mono ?_
  rintro _ ⟨_, ⟨χ, rfl⟩, rfl⟩
  exact ⟨χ.comp ι, rfl⟩

theorem char_mem_mu (χ : T →* Rˣ) : (fun t => ((χ t : Rˣ) : R)) ∈ muOrder R T :=
  Algebra.subset_adjoin ⟨χ, rfl⟩

def evChar (t : T) : (T →* Rˣ) →* Rˣ where
  toFun χ := χ t
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ev_mem_dual (A : Subalgebra R (T → R)) (t : T) :
    (fun χ : T →* Rˣ => ((χ t : Rˣ) : R)) ∈ dualOrder A :=
  Algebra.subset_adjoin ⟨(evalAt A t).toLinearMap, fun _ _ => rfl⟩

theorem dual_top_le_mu [Finite T] : dualOrder (⊤ : Subalgebra R (T → R)) ≤ muOrder R (T →* Rˣ) := by
  classical
  cases nonempty_fintype T
  refine Algebra.adjoin_le ?_
  rintro g ⟨l, hl⟩
  have : g = ∑ t : T, l ⟨Pi.single t 1, trivial⟩ • fun χ : T →* Rˣ => ((evChar t χ : Rˣ) : R) := by
    funext χ
    rw [hl χ trivial]
    have e : (⟨fun t => ((χ t : Rˣ) : R), trivial⟩ : (⊤ : Subalgebra R (T → R))) =
        ∑ t : T, ((χ t : Rˣ) : R) • ⟨Pi.single t 1, trivial⟩ := by
      apply Subtype.ext
      funext s
      simp [Finset.sum_apply, Pi.single_apply]
    rw [e, map_sum]
    simp [Finset.sum_apply, evChar, mul_comm]
  rw [this]
  exact Subalgebra.sum_mem _ fun t _ => Subalgebra.smul_mem _ (char_mem_mu (evChar t)) _

theorem mu_eq_span : Subalgebra.toSubmodule (muOrder R T) =
    Submodule.span R (Set.range fun χ : T →* Rˣ => fun t => ((χ t : Rˣ) : R)) := by
  unfold muOrder
  rw [Algebra.adjoin_eq_span]
  congr 1
  apply Set.Subset.antisymm
  · intro f hf
    induction hf using Submonoid.closure_induction with
    | mem x hx => obtain ⟨χ, rfl⟩ := hx; exact ⟨χ, rfl⟩
    | one => exact ⟨1, rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨χ, rfl⟩ := hx
      obtain ⟨ψ, rfl⟩ := hy
      exact ⟨χ * ψ, by funext t; simp⟩
  · rintro _ ⟨χ, rfl⟩
    exact Submonoid.subset_closure ⟨χ, rfl⟩

theorem li_char [IsDomain R] :
    LinearIndependent R (fun χ : T →* Rˣ => fun t => ((χ t : Rˣ) : R)) := by
  have := (linearIndependent_monoidHom T R).comp (fun χ : T →* Rˣ => (Units.coeHom R).comp χ)
    (fun a b h => MonoidHom.ext fun t => Units.ext (DFunLike.congr_fun h t))
  exact this

theorem dual_mu_eq_top [IsDomain R] : dualOrder (muOrder R T) = ⊤ := by
  refine eq_top_iff.2 fun g _ => Algebra.subset_adjoin ?_
  let b := Module.Basis.span (li_char (R := R) (T := T))
  let e : muOrder R T →ₗ[R] Submodule.span R (Set.range fun χ : T →* Rˣ => fun t => ((χ t : Rˣ) : R)) :=
    (LinearEquiv.ofEq _ _ (mu_eq_span (R := R) (T := T))).toLinearMap
  refine ⟨(b.constr R g).comp e, fun χ h => ?_⟩
  have : e ⟨_, h⟩ = b χ := by
    apply Subtype.ext
    simp only [b, Module.Basis.span_apply]
    rfl
  rw [LinearMap.comp_apply, this, Module.Basis.constr_basis]

theorem mu_int_parity (f : T → ℤ) (hf : f ∈ muOrder ℤ T) (s t : T) : f s % 2 = f t % 2 := by
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨χ, rfl⟩ := hx
    rcases Int.units_eq_one_or (χ s) with h | h <;> rcases Int.units_eq_one_or (χ t) with h' | h' <;>
      simp [h, h']
  | algebraMap r => rfl
  | add x y _ _ hx hy => simp only [Pi.add_apply]; omega
  | mul x y _ _ hx hy => simp only [Pi.mul_apply]; rw [Int.mul_emod, hx, hy, ← Int.mul_emod]

theorem mu_int_ne_top [Nontrivial T] : muOrder ℤ T ≠ ⊤ := by
  classical
  intro h
  obtain ⟨s, t, hst⟩ := exists_pair_ne T
  have := mu_int_parity (Pi.single s 1) (h ▸ trivial) s t
  simp [Pi.single_apply, hst.symm] at this

theorem mu_two_ne_bot : muOrder ℤ ℤˣ ≠ ⊥ := by
  intro h
  have h1 := char_mem_mu (R := ℤ) (MonoidHom.id ℤˣ)
  rw [h, Algebra.mem_bot] at h1
  obtain ⟨r, hr⟩ := h1
  have a := congrFun hr 1
  have b := congrFun hr (-1)
  simp at a b
  omega

theorem dual_top_two_ne_top : dualOrder (⊤ : Subalgebra ℤ (ℤˣ → ℤ)) ≠ ⊤ := by
  haveI : Nontrivial (ℤˣ →* ℤˣ) := ⟨1, MonoidHom.id _, fun h => by
    have := DFunLike.congr_fun h (-1); simp at this⟩
  intro h
  exact mu_int_ne_top (eq_top_iff.2 (h ▸ dual_top_le_mu))

theorem dual_bot_eq_top : dualOrder (⊥ : Subalgebra R (T → R)) = ⊤ := by
  refine eq_top_iff.2 fun g _ => Algebra.subset_adjoin ?_
  refine ⟨g 1 • (evalAt ⊥ 1).toLinearMap, fun χ h => ?_⟩
  obtain ⟨r, hr⟩ := Algebra.mem_bot.1 h
  have : χ = 1 := MonoidHom.ext fun t => Units.ext (by
    have a := congrFun hr 1
    have b := congrFun hr t
    simp at a b
    simp [← b, a])
  subst this
  simp [evalAt]

end GlobalTheory.CompanionTheory.Ar.BT.OpsModel
