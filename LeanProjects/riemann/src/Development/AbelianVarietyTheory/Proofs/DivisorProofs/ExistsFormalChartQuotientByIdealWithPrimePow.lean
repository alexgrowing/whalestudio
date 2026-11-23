import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomEvalCompEqEvAMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartPresentsLevelsModIdealStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.ChartRed

def twoRing {R R' A A' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} [CommRing A]
    [Bialgebra R A] [CommRing A'] [Bialgebra R' A'] (f : SemiBialgHom σ A A') :
    A ⊗[R] A →+* A' ⊗[R'] A' where
  toFun := f.two
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [Algebra.TensorProduct.one_def, TensorProduct.map_tmul, SemiBialgHom.lin_apply, map_one,
      Algebra.TensorProduct.one_def]
  map_mul' x y := by
    induction x with
    | zero => simp
    | add a b ha hb => simp only [add_mul, map_add, ha, hb]
    | tmul a b =>
      induction y with
      | zero => simp
      | add u v hu hv => simp only [mul_add, map_add, hu, hv]
      | tmul u v => simp

theorem ev₂_map {p m d : ℕ} {O k : Type} [CommRing O] [CommRing k] {r : O →+* k}
    {G : PDivGroup p O} {G' : PDivGroup p k} (s : SemiHom r G' G) (c : QLog.Chart G d)
    (c' : Katz.Chart G' d) (hc : ∀ n i, c'.x n i = s.app n (c.x n i)) (hp : (p : k) ^ m = 0)
    (n : ℕ) (f : MvPowerSeries (Fin d ⊕ Fin d) O) :
    c'.ev₂ n (map r f) = (s.app n).two (c.ev₂ n f) := by
  have e : (fun i => twoRing (s.app n)
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] 1) (fun i => 1 ⊗ₜ[O] c.x n i) i)) = c'.x₂ n := by
    funext i
    cases i with
    | inl i =>
      change (s.app n) (c.x n i) ⊗ₜ[k] (s.app n) 1 = c'.x n i ⊗ₜ[k] 1
      rw [map_one, hc]
    | inr i =>
      change (s.app n) 1 ⊗ₜ[k] (s.app n) (c.x n i) = 1 ⊗ₜ[k] c'.x n i
      rw [map_one, hc]
  have h := T.map_eval_eq_evA_map_of_isEval_of_pow_eq_zero p m O _ k (G'.A n ⊗[k] G'.A n) _ _ _ (c.isEval₂ n) r (twoRing (s.app n))
    (fun a => by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        ← map_one (twoRing (s.app n))]
      exact map_smulₛₗ (s.app n).two a 1)
    (by rw [← map_natCast (algebraMap k _), ← map_pow, hp, map_zero])
    (fun i => (congrFun e i).symm ▸ c'.nil₂ n i) f
  refine Eq.trans ?_ h.symm
  unfold Katz.Chart.ev₂
  congr 2
  exact e.symm

theorem exists_chart : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (I : Ideal O) (m : ℕ), (p : O) ^ m ∈ I → ∃ c' : Katz.Chart (G.baseChange (O ⧸ I)) d, c'.IsLawOf (fun i => map (Ideal.Quotient.mk I) (c.μ i)) ∧ (∀ n f, c'.ev n (map (Ideal.Quotient.mk I) f) = (G.toBase (O ⧸ I)).app n (c.ev n f)) ∧ ∀ n s, c'.ev₂ n (map (Ideal.Quotient.mk I) s) = ((G.toBase (O ⧸ I)).app n).two (c.ev₂ n s) := by
  intro p _ O _ G d c I m hm
  obtain ⟨hx, h1, h2⟩ := T.formalChart_presents_levels_mod_ideal p O G d c I m hm
  have hp : (p : O ⧸ I) ^ m = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hm
  let c' : Katz.Chart (G.baseChange (O ⧸ I)) d :=
    { x := fun n i => (G.toBase (O ⧸ I)).app n (c.x n i)
      nil := hx
      res := fun n i => ((G.toBase (O ⧸ I)).res_app n _).trans (congrArg _ (c.res n i))
      aug := fun n i => by rw [((G.toBase (O ⧸ I)).app n).counit_map, c.aug, map_zero]
      presents := h2 }
  have h3 := ev₂_map (G.toBase (O ⧸ I)) c c' (fun _ _ => rfl) hp
  refine ⟨c', fun n i => ?_, h1, h3⟩
  exact (h3 n (c.μ i)).trans ((congrArg _ (c.comul n i)).trans
    (((G.toBase (O ⧸ I)).app n).two_comul _))

end GlobalTheory.QLog.ChartRed
