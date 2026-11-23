import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLatticeQuotPrimeStatement

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

theorem exists_addEquiv_of_card {Q : Type} [AddCommGroup Q] {p N : ℕ} [hp : Fact p.Prime] [Module (ZMod p) Q]
    (hc : Nat.card Q = p ^ N) : Nonempty (Q ≃+ (Fin N → ZMod p)) := by
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp.out.ne_zero)
  have hr : Module.finrank (ZMod p) Q = N := by
    apply Nat.pow_right_injective hp.out.two_le
    have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Q)
    rw [Nat.card_zmod, hc] at this
    exact this.symm
  exact ⟨(Module.finBasisOfFinrankEq (ZMod p) Q hr).equivFun.toAddEquiv⟩

theorem exists_coords_of_card {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {p N : ℕ} (hp : p.Prime)
    (r : R →+* ZMod p) (hc : Nat.card (M ⧸ (RingHom.ker r • (⊤ : Submodule R M))) = p ^ N) :
    ∃ c : M →ₛₗ[r] (Fin N → ZMod p), Function.Surjective c ∧
      ∀ y, c y = 0 ↔ y ∈ RingHom.ker r • (⊤ : Submodule R M) := by
  have : Fact p.Prime := ⟨hp⟩
  set S : Submodule R M := RingHom.ker r • (⊤ : Submodule R M) with hS
  have hk : ∀ a : R, r a = 0 → ∀ q : M ⧸ S, a • q = 0 := by
    intro a ha q
    obtain ⟨y, rfl⟩ := S.mkQ_surjective q
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  have hpq : ∀ q : M ⧸ S, p • q = 0 := fun q => by
    rw [← Nat.cast_smul_eq_nsmul R]
    exact hk _ (by rw [map_natCast, ZMod.natCast_self]) q
  obtain ⟨e⟩ := @exists_addEquiv_of_card (M ⧸ S) _ p N _ (AddCommGroup.zmodModule hpq) hc
  have hs : ∀ (a : R) (q : M ⧸ S), e (a • q) = r a • e q := by
    intro a q
    have h1 : (a - ((r a).val : R)) • q = 0 := hk _ (by simp) q
    rw [sub_smul, sub_eq_zero] at h1
    rw [h1, Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  refine ⟨{ toFun := fun y => e (S.mkQ y)
            map_add' := fun x y => by rw [map_add, map_add]
            map_smul' := fun a y => by rw [map_smul, hs] },
    e.surjective.comp S.mkQ_surjective, fun y => ?_⟩
  show e (S.mkQ y) = 0 ↔ _
  rw [map_eq_zero_iff _ e.injective, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

theorem plFrame_nonempty : ∀ (I : AutInst) (N p : ℕ) (w : HeightOneSpectrum (𝓞 I.E)), I.n = N → p.Prime → Ideal.absNorm w.asIdeal = p → Nonempty (PlFrame I N p w) ∧ ∀ (fr : PlFrame I N p w) (y : I.Lf), fr.c y = 0 ↔ (y : Fin I.n → (I.E ⊗[I.F] Af I.F)) ∈ extId I w.asIdeal • I.Lf := by
  intro I N p w hN hp hw
  refine ⟨?_, fun fr y => fr.c_ker y⟩
  obtain ⟨r, hr⟩ := Inhab.exists_reduction (F := I.F) p hp w hw
  have hk := Inhab.ker_eq_extId hp.ne_zero r hr
  have hc := GlobalTheory.T.card_lattice_quot_prime I p w hp hw
  subst hN
  rw [← hk] at hc
  obtain ⟨c, h1, h2⟩ := exists_coords_of_card hp r hc
  refine ⟨⟨r, fun a _ => hr a, c, h1, fun y => ?_⟩⟩
  rw [h2, hk]
  exact Submodule.mem_smul_top_iff _ _ y

end GlobalTheory.RowLev
