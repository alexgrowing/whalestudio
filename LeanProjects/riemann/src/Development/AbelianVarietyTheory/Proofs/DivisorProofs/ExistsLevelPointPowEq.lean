import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MultTorsion

theorem linComb_eq_prod {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ}
    (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) : linComb y a = ∏ i, y i ^ a i := List.prod_ofFn

theorem linComb_pow {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ}
    (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) (m : ℕ) : linComb y a ^ m = linComb y (fun i => a i * m) := by
  rw [linComb_eq_prod, linComb_eq_prod, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => (pow_mul _ _ _).symm

theorem linComb_mod {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n M : ℕ}
    (y : Fin n → (T ⟶ A)) (hy : ∀ i, y i ^ M = 1) (a : Fin n → ℕ) :
    linComb y a = linComb y (fun i => a i % M) := by
  rw [linComb_eq_prod, linComb_eq_prod]
  exact Finset.prod_congr rfl fun i _ => pow_eq_pow_mod _ (hy i)

theorem linComb_zero {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ}
    (y : Fin n → (T ⟶ A)) : linComb y (fun _ => 0) = 1 := by
  rw [linComb_eq_prod]; simp

end GlobalTheory.MultTorsion

namespace GlobalTheory

open MultTorsion in

theorem exists_levelPoint_pow_eq : ∀ (K : Type) [Field K] [IsAlgClosed K] (Q : PolAV (Sp K)) (m g : ℕ) (hg : Q.g = g) (ze : Γ(Sp K, ⊤)ˣ) (lev : Level Q (m ^ 2) ze) (z : baseOver (Sp K) ⟶ Q.A), 0 < m → z ^ m = 1 → ∃ a : Fin (2 * g) → ZMod (m ^ 2), GlobalTheory.levelPoint lev hg a ^ m = z := by
  intro K _ _ Q m g hg ze lev z hm hz
  subst hg
  have := Q.isAb.comm
  have E : ∀ c : Fin (2 * Q.g) → ℕ,
      linComb (fun i => (Over.homMk (𝟙 _) (by simp) : Over.mk (𝟙 _) ⟶ baseOver _) ≫ lev.pt i) c =
      linComb lev.pt c := fun c => congrArg (linComb · _) (funext fun i => Category.id_comp (lev.pt i))
  have hz2 : z ^ (m ^ 2) = 1 := by rw [sq, pow_mul, hz, one_pow]
  obtain ⟨c, hc⟩ := lev.span K (𝟙 _) z hz2
  replace hc : linComb lev.pt (fun i => (c i : ℕ)) = z := (E _).symm.trans hc
  have hM : 0 < m ^ 2 := pow_pos hm 2
  have h1 : linComb lev.pt (fun i => (c i : ℕ) * m % (m ^ 2)) = linComb lev.pt (fun _ => 0) := by
    rw [← linComb_mod _ lev.torsion, ← linComb_pow, hc, hz, linComb_zero]
  have h2 := lev.indep K (𝟙 _) (fun i => ⟨(c i : ℕ) * m % (m ^ 2), Nat.mod_lt _ hM⟩) (fun _ => ⟨0, hM⟩)
    ((E _).trans (h1.trans (E _).symm))
  have hd : ∀ i, m ∣ (c i : ℕ) := fun i => by
    have h3 := congrArg Fin.val (congrFun h2 i)
    simp only at h3
    have h4 : m * m ∣ (c i : ℕ) * m := by rw [← sq]; exact Nat.dvd_of_mod_eq_zero h3
    exact Nat.dvd_of_mul_dvd_mul_right hm h4
  refine ⟨fun i => (((c i : ℕ) / m : ℕ) : ZMod (m ^ 2)), ?_⟩
  rw [ThetaPtDet.levelPoint_eq, levelBasis_rfl, linComb_pow, ← hc]
  refine congrArg (linComb lev.pt) (funext fun i => ?_)
  have hlt : (c i : ℕ) / m < m ^ 2 := lt_of_le_of_lt (Nat.div_le_self _ _) (c i).isLt
  rw [ZMod.val_natCast_of_lt hlt, Nat.div_mul_cancel (hd i)]

end GlobalTheory
