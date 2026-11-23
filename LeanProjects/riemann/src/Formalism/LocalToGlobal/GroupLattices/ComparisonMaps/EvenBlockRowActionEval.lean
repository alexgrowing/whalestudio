import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CmpCMemMIff
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ProdMemSpan

open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G

noncomputable section

namespace Formalism.L2.G.Cmp

section GlobalTheory

variable {K : Type} [Field K] {k n : ℕ}

theorem eval_rowAct (g : Matrix (Fin k) (Fin k) K) (f : MvPolynomial (Fin k × Fin n) K) (z : Matrix (Fin k) (Fin n) K) :
    eval (fun x => z x.1 x.2) (rowAct K g f) = eval (fun x => (g * z) x.1 x.2) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    simp [rowAct, Matrix.mul_apply]

theorem even_block_row_action_eval (g : Matrix (Fin k) (Fin k) K) (e : ℤ) (f : MvPolynomial (Fin k × Fin k) K)
    (z : Matrix (Fin k) (Fin k) K) :
    z.det ^ e * eval (fun x => z x.1 x.2) (g.det ^ (-e) • rowAct K g⁻¹ f) =
      (g⁻¹ * z).det ^ e * eval (fun x => (g⁻¹ * z) x.1 x.2) f := by
  rw [MvPolynomial.smul_eval, eval_rowAct, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
    mul_zpow, _root_.inv_zpow']
  ring

theorem even_block_weyl_mem {O : Type} [CommRing O] [Algebra O K] (hinj : Function.Injective (algebraMap O K)) (m : ℕ)
    (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (hF : F ∈ Dl0 O m lam (colSpan O g)) :
    ∃ f ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf lam), ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K,
      z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
        (g⁻¹ * z).det ^ lam (Fin.last m) * eval (fun x => (g⁻¹ * z) x.1 x.2) (map (algebraMap O K) f) := by
  rw [dw_eq hinj m lam hlam g hg] at hF
  obtain ⟨F0, hF0, rfl⟩ := Submodule.mem_map.1 hF
  obtain ⟨f, hf, hfeq⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hF0)
  refine ⟨f, hf, fun z => ?_⟩
  have e1 : map (algebraMap O K) f = rowAct K g F0 := hfeq
  have key : eval (fun x => (g⁻¹ * z) x.1 x.2) (map (algebraMap O K) f) = eval (fun x => z x.1 x.2) F0 := by
    rw [e1, eval_rowAct, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]
  simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, MvPolynomial.smul_eval]
  rw [key, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', mul_zpow, _root_.inv_zpow']
  ring

def lamStar {m : ℕ} (lam : Fin (m + 1) → ℤ) : Fin (m + 1) → ℤ := fun i => -lam i.rev

def revCol {m : ℕ} (z : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  z.submatrix id Fin.rev

def OddFact (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) : Prop :=
  ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit g.det →
    (∀ F ∈ Dl0 O m lam (colSpan O g), ∃ F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ),
      ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
        z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
          (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F') ∧
    (∀ F' ∈ Dl0 O m (lamStar lam) (colSpan O (g⁻¹)ᵀ), ∃ F ∈ Dl0 O m lam (colSpan O g),
      ∀ z : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit z.det →
        z.det ^ lam (Fin.last m) * eval (fun x => z x.1 x.2) F =
          (revCol (z⁻¹)ᵀ).det ^ lamStar lam (Fin.last m) * eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F')

end GlobalTheory

section Prod

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ}

theorem evC_prod (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) (F : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℂ)
    (y : Formalism.L2.Forms.Frames G) :
    evC P h pos G M (∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (F v s))) y =
      ∏ v, ∏ s : Fin (P.n' v), ((zAt P h pos M y.1 v s).det ^ (eAt P v s) *
        eval (fun x => zAt P h pos M y.1 v s x.1 x.2) (F v s)) := by
  simp only [evC, LinearMap.coe_mk, AddHom.coe_mk, map_prod, blockEmb, MvPolynomial.eval_rename]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

end Prod

end Formalism.L2.G.Cmp
