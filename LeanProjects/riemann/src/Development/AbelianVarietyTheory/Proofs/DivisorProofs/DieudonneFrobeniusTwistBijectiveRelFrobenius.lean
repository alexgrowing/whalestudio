import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneBaseChangeBasisStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem wittMap_frobRing_bijective (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] : Function.Bijective (WittVector.map (p := p) (frobRing (p_eq_zero p k))) := by
  have hb : Function.Bijective (frobRing (p_eq_zero p k)) := by
    have e : ⇑(frobRing (p_eq_zero p k)) = ⇑(frobenius k p) :=
      funext fun r => by rw [frobRing_apply, frobenius_def]
    rw [e]
    exact bijective_frobenius k p
  exact ⟨WittVector.map_injective _ hb.1, WittVector.map_surjective _ hb.2⟩

theorem bijective_of_basis {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] (σ : R →+* R') (hσ : Function.Bijective σ) (f : M →+ M')
    (hf : ∀ (a : R) (m : M), f (a • m) = σ a • f m) {ι : Type} [Fintype ι] (b : Module.Basis ι R M)
    (b' : Module.Basis ι R' M') (hb : ∀ i, b' i = f (b i)) : Function.Bijective f := by
  have key : ∀ c : ι → R, f (∑ i, c i • b i) = ∑ i, σ (c i) • b' i := fun c => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hf, hb]
  refine ⟨(injective_iff_map_eq_zero f).2 fun m hm => ?_, fun x => ?_⟩
  · rw [← b.sum_repr m, key] at hm
    have : ∀ i, b.repr m i = 0 := fun i => by
      have := Fintype.linearIndependent_iff.1 b'.linearIndependent _ hm i
      exact hσ.1 (this.trans (map_zero σ).symm)
    rw [← b.sum_repr m]
    simp [this]
  · obtain ⟨c, hc⟩ : ∃ c : ι → R, ∀ i, σ (c i) = b'.repr x i :=
      ⟨fun i => Function.surjInv hσ.2 (b'.repr x i), fun i => Function.surjInv_eq hσ.2 _⟩
    refine ⟨∑ i, c i • b i, ?_⟩
    rw [key]
    simp only [hc]
    exact b'.sum_repr x

end GlobalTheory.Dieu

theorem GlobalTheory.Dieu.frobTwist_module : ∀ (p : ℕ) [Fact p.Prime] (B : Base p fun _ _ _ => True) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), Function.Bijective (B.smap trivial trivial (frobProj (p_eq_zero p k) G)) ∧ (∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G) (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m) ∧ ∀ m n, B.smap trivial trivial (frobProj (p_eq_zero p k) G) n = B.map trivial trivial (verschiebung (p_eq_zero p k) G) m → B.F G trivial n = p • m := by
  intro p _ B k _ _ _ G
  have h2 : ∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G)
      (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m := fun m =>
    (B.smap_comp trivial trivial trivial (frobProj (p_eq_zero p k) G)
      (SemiHom.ofHom (relFrob (p_eq_zero p k) G)) (absFrob (p_eq_zero p k) G)
      (fun n a => by rw [SemiHom.ofHom_app, relFrob_app_frobProj, absFrob_app]) m).symm
  refine ⟨?_, h2, fun m n e => ?_⟩
  · haveI := B.free G trivial
    haveI := B.finite G trivial
    letI := (frobRing (p_eq_zero p k)).toAlgebra
    obtain ⟨b', hb'⟩ := GlobalTheory.T.dieudonne_baseChange_basis p (fun _ _ _ => True) B k k G trivial trivial _
      (Module.Free.chooseBasis (WittVector p k) (B.M G trivial))
    exact bijective_of_basis _ (wittMap_frobRing_bijective p k) _
      (fun a m => B.smap_smul trivial trivial _ a m) _ b' hb'
  · obtain ⟨-, hc, -⟩ := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) B k G
      (frobTwist (p_eq_zero p k) G) G trivial trivial trivial
    obtain ⟨hid, -, -, -, hp, -⟩ := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) B k G G G trivial trivial trivial
    rw [← h2, e, ← LinearMap.comp_apply, ← hc, relFrob_comp_verschiebung, ← pow_one (p : ℤ_[p]), hp,
      pow_one, hid, LinearMap.id_apply]
