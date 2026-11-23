import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

noncomputable section

namespace GlobalTheory.RedFun.LatQuot

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k]

def subLattice [IsDomain O] [IsPrincipalIdealRing O] (T : LocLat G Qp LL O) (lam : O)
    (hl : algebraMap O LL lam ≠ 0) (P : Submodule O ↥T.L.T) (hP : ∀ g, ∀ x ∈ P, latRep T.L g x ∈ P)
    (hlam : ∀ x, lam • x ∈ P) : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) T.ρ where
  T := P.map T.L.T.subtype
  stable := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨latRep T.L g x, hP g x hx, rfl⟩
  fg := by
    have := StdAdm.finite_lat T
    exact (IsNoetherian.noetherian _).map _
  free := by
    have := StdAdm.finite_lat T
    have := T.L.free
    have : Module.Free O ↥P := Module.free_of_finite_type_torsion_free'
    exact Module.Free.of_equiv (Submodule.equivMapOfInjective _ T.L.T.injective_subtype _)
  span := by
    rw [eq_top_iff, ← T.L.span, Submodule.span_le]
    intro y hy
    have h1 : lam • y ∈ P.map T.L.T.subtype := ⟨lam • ⟨y, hy⟩, hlam _, rfl⟩
    have h2 := Submodule.smul_mem _ (algebraMap O LL lam)⁻¹ (Submodule.subset_span (R := LL) h1)
    rwa [← algebraMap_smul LL lam y, inv_smul_smul₀ hl] at h2

theorem onto_sub [IsDomain O] [IsPrincipalIdealRing O] (lam : O) (hl : algebraMap O LL lam ≠ 0)
    (hk : algebraMap O k lam = 0) (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hf : IsHom A B f)
    (hi : Function.Injective f) (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)) (hq : Onto T B q) :
    ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q := by
  obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  have hr' : ∀ x, r (f x) = x := fun x => LinearMap.congr_fun hr x
  let P : Submodule O ↥T.L.T := (LinearMap.range (f.restrictScalars O)).comap q
  have hP : ∀ g, ∀ x ∈ P, latRep T.L g x ∈ P := by
    rintro g x ⟨a, ha⟩
    refine ⟨A.ρ g a, ?_⟩
    have ha' : f a = q x := ha
    change f (A.ρ g a) = q _
    rw [hf, ha', hq.2]
  have hlam : ∀ x, lam • x ∈ P := by
    intro x
    refine ⟨0, ?_⟩
    rw [map_zero, map_smul, ← algebraMap_smul k lam, hk, zero_smul]
  let L := subLattice T lam hl P hP hlam
  have hle : L.T ≤ T.L.T := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  refine ⟨withLat T L, (r.restrictScalars O).comp (q.comp (Submodule.inclusion hle)), ?_, ?_⟩
  · intro a
    obtain ⟨x, hx⟩ := hq.1 (f a)
    refine ⟨⟨x.1, x, ⟨a, hx.symm⟩, rfl⟩, ?_⟩
    change r (q x) = a
    rw [hx, hr']
  · rintro g ⟨_, x, ⟨a, ha⟩, rfl⟩
    have ha' : f a = q x := ha
    change r (q (latRep T.L g x)) = A.ρ g (r (q x))
    rw [hq.2, ← ha', ← hf, hr', hr']

theorem onto_quot (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hf : IsHom A B f)
    (hs : Function.Surjective f) (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (hq : Onto T A q) :
    Onto T B ((f.restrictScalars O).comp q) := by
  refine ⟨hs.comp hq.1, fun g x => ?_⟩
  change f (q _) = B.ρ g (f (q x))
  rw [hq.2, hf]

theorem onto_sum (A B C : Ob k G) (i : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) (j : (Fin B.m → k) →ₗ[k] (Fin C.m → k))
    (hi : IsHom A C i) (hj : IsHom B C j) (hs : Function.Surjective (i.coprod j))
    (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (hq : Onto T A q)
    (T' : LocLat G Qp LL O) (q' : ↥T'.L.T →ₗ[O] (Fin B.m → k)) (hq' : Onto T' B q') :
    Onto (StdAdm.prodLat T T') C (((i.coprod j).restrictScalars O).comp
      ((q.prodMap q').comp (StdAdm.prodLatEquiv T T').toLinearMap)) := by
  refine ⟨hs.comp ((hq.1.prodMap hq'.1).comp (StdAdm.prodLatEquiv T T').surjective), fun g x => ?_⟩
  change i (q (latRep T.L g (StdAdm.prodLatEquiv T T' x).1)) + j (q' (latRep T'.L g (StdAdm.prodLatEquiv T T' x).2)) =
    C.ρ g (i (q (StdAdm.prodLatEquiv T T' x).1) + j (q' (StdAdm.prodLatEquiv T T' x).2))
  rw [hq.2, hq'.2, hi, hj, map_add]

theorem onto_one [IsDomain O] (hs : Function.Surjective (algebraMap O k)) (T : LocLat G Qp LL O) (e₀ : ↥T.L.T)
    (hρ : ∀ g x, T.ρ g x = x) (h0 : e₀ ≠ 0) (hsp : Submodule.span O {e₀} = ⊤) :
    ∃ q : ↥T.L.T →ₗ[O] (Fin 1 → k), Onto T (chr 1 : Ob k G) q ∧ q e₀ = fun _ => 1 := by
  have := T.L.free
  have hb : Function.Bijective (LinearMap.toSpanSingleton O ↥T.L.T e₀) := by
    refine ⟨smul_left_injective O h0, ?_⟩
    rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, hsp]
  let e := LinearEquiv.ofBijective _ hb
  have he : e 1 = e₀ := one_smul O e₀
  refine ⟨(LinearMap.pi fun _ => Algebra.linearMap O k).comp e.symm.toLinearMap, ⟨?_, fun g x => ?_⟩, ?_⟩
  · intro y
    obtain ⟨c, hc⟩ := hs (y 0)
    refine ⟨e c, funext fun i => ?_⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    change algebraMap O k (e.symm (e c)) = y 0
    rw [e.symm_apply_apply, hc]
  · have h1 : latRep T.L g x = x := Subtype.ext (hρ g x)
    rw [h1]
    exact (one_smul k _).symm
  · funext i
    change algebraMap O k (e.symm e₀) = 1
    rw [← he, e.symm_apply_apply, map_one]

theorem lattice_quotients : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k] (lam : O), algebraMap O LL lam ≠ 0 → algebraMap O k lam = 0 → Function.Surjective (algebraMap O k) → (∀ x, algebraMap O k x = 0 → lam ∣ x) → (∀ (A B : Ob k G) f, IsHom A B f → Function.Injective f → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) ∧ (∀ (A B : Ob k G) f, IsHom A B f → Function.Surjective f → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) ∧ (∀ (A B C : Ob k G) i j, IsHom A C i → IsHom B C j → Function.Surjective (i.coprod j) → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin C.m → k)), Onto T C q) ∧ ∀ (T : LocLat G Qp LL O) (e₀ : ↥T.L.T), (∀ g x, T.ρ g x = x) → e₀ ≠ 0 → Submodule.span O {e₀} = ⊤ → ∃ q : ↥T.L.T →ₗ[O] (Fin 1 → k), Onto T (chr 1 : Ob k G) q ∧ q e₀ = fun _ => 1 := by
  intro G _ _ Qp LL O _ _ _ _ _ _ _ _ k _ _ lam hl hk hs _
  refine ⟨?_, ?_, ?_, onto_one hs⟩
  · rintro A B f hf hi ⟨T, q, hq⟩
    exact onto_sub lam hl hk A B f hf hi T q hq
  · rintro A B f hf hi ⟨T, q, hq⟩
    exact ⟨T, _, onto_quot A B f hf hi T q hq⟩
  · rintro A B C i j hi hj h ⟨T, q, hq⟩ ⟨T', q', hq'⟩
    exact ⟨_, _, onto_sum A B C i j hi hj h T q hq T' q' hq'⟩

end GlobalTheory.RedFun.LatQuot
