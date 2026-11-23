import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd

set_option autoImplicit false
noncomputable section
open CategoryTheory WittVector Ideal TensorProduct
namespace GlobalTheory.Published.CycPerfd.Model
open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta
variable {p : ℕ} [Fact p.Prime]

theorem frobenius_mu (S : CycPerfd p) :
    frobenius (Sandwich.mu S.ε) = frobenius (xi S.ε) * Sandwich.mu S.ε := by
  have h : ∀ x : PreTilt S.R p, frobenius (teichmuller p x) = teichmuller p x ^ p := fun x => by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, ← map_pow]; rfl
  have h2 : teichmuller p (root S.ε) ^ p = teichmuller p S.ε := by
    rw [← map_pow]; congr 1
    exact (_root_.frobeniusEquiv (PreTilt S.R p) p).apply_symm_apply S.ε
  simp only [xi, Sandwich.mu, map_sum, map_pow, map_sub, map_one, h, h2]
  rw [geom_sum_mul]

theorem theta_xi (S : CycPerfd p) : fontaineTheta S.R p (xi S.ε) = 0 := by
  rw [← RingHom.mem_ker, S.ker_eq]; exact Ideal.mem_span_singleton_self _

theorem eps_ne_one (S : CycPerfd p) : S.ε ≠ 1 := fun h => by
  have hx : xi S.ε = (p : Ainf p S.R) := by simp [xi, root, h]
  have h0 := theta_xi S
  rw [hx, map_natCast] at h0
  have h1 : (1 : S.R) = 0 := S.reg (by simp [h0])
  exact S.nonunit.out (by rw [h0, ← h1]; exact isUnit_one)

def muSemi (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (X : Type) [AddCommMonoid X] :
    PDiv.SemiBialgHom (algebraMap O O') (AddMonoidAlgebra O X) (AddMonoidAlgebra O' X) where
  toRingHom := AddMonoidAlgebra.mapRingHom X (algebraMap O O')
  smul_map r a := by
    induction a using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | single k c => simp [Algebra.smul_def, -algebraMap_smul]
  counit_map a := by
    induction a using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single k c => simp
  comul_map a := by
    induction a using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single k c => simp

theorem exists_muCompare (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] :
    ∃ j : PDivGroup.mu p O' ⟶ (PDivGroup.mu p O).baseChange O',
      ∀ n, j.app n (1 ⊗ₜ AddMonoidAlgebra.single 1 1) = AddMonoidAlgebra.single 1 1 := by
  have hT : ∀ m : ℕ, muSemi O O' (ZMod m) (PDiv.muT O m) = PDiv.muT O' m := fun m => by
    simp [muSemi, PDiv.muT]
  let s : SemiHom (algebraMap O O') (PDivGroup.mu p O') (PDivGroup.mu p O) :=
    ⟨fun n => muSemi O O' _, fun n a => by
      induction a using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | single k c =>
        have e : (AddMonoidAlgebra.single k c : AddMonoidAlgebra O (ZMod (p ^ (n + 1)))) =
            c • PDiv.muT O _ ^ k.val := by
          rw [PDiv.muT_pow, ZMod.natCast_zmod_val]; simp
        change muRes p O' n (muSemi O O' _ _) = muSemi O O' _ (muRes p O n _)
        rw [e, map_smul (muRes p O n), PDiv.SemiBialgHom.smul_map, PDiv.SemiBialgHom.smul_map, map_smul (muRes p O' n), map_pow, map_pow,
          map_pow, map_pow, muRes_muT, hT, hT, muRes_muT]⟩
  exact ⟨s.lift, fun n => (s.lift_app n 1 _).trans ((one_smul _ _).trans (hT _))⟩

theorem baseChange_clause_inhabited : ∃ (S : CycPerfd p) (α : Ainf p S.R →+* Ainf p S.R), S.Over S α ∧ S.ε ≠ 1 ∧
    ∃ j : PDivGroup.mu p S.R ⟶ (PDivGroup.mu p S.R).baseChange S.R,
      ∀ n, j.app n (1 ⊗ₜ AddMonoidAlgebra.single 1 1) = AddMonoidAlgebra.single 1 1 := by
  obtain ⟨S, -⟩ := CycPerfd.nonempty p
  exact ⟨S, _, S.over_refl, eps_ne_one S, exists_muCompare _ _⟩

theorem xi_mem_fil (h : PrismaticDieudonnePerfd) (S : CycPerfd p) (G : PDivGroup p S.R) :
    ∃ (M : ModuleCat.{0} (Ainf p S.R)) (φ : M →ₛₗ[(frobenius : Ainf p S.R →+* Ainf p S.R)] M)
      (lie : M →ₛₗ[fontaineTheta S.R p] G.dual.Lie), Function.Surjective lie ∧
      (∀ m, lie m = 0 ↔ ∃ n, φ m = frobenius (xi S.ε) • n) ∧ ∀ m, lie (xi S.ε • m) = 0 := by
  obtain ⟨M, map, φ, lie, du, l, e, h1, -⟩ := h p
  refine ⟨M S G, φ S G, lie S G, (h1 S G).2.2.2.2.2.2.1, (h1 S G).2.2.2.2.2.2.2.1, fun m => ?_⟩
  rw [map_smulₛₗ, theta_xi, zero_smul]

end GlobalTheory.Published.CycPerfd.Model
