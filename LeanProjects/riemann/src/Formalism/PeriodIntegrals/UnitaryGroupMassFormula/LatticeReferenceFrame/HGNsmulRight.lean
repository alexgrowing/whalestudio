import Mathlib
import Formalism.PeriodIntegrals.ScRefExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.HANegRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.HypsNonvacuous

noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.ScRefExists.GlueB

open PI.ScRefExists PI.ScRefExists.GlueA PI.ScRefExists.Sk

section Lemmas

variable (I : Formalism.MainNotions.S.AutInst) (g : ℕ)

theorem zmod_zero : ZMod' I g 0 := ⟨0, zero_mem _, by simp⟩

theorem zmod_of_GE {x : I.E} (h : GE I g x) : ZMod' I g (Formalism.UG.inclE (F := I.F) (Af I.F) x) := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨Formalism.UG.inclE (F := I.F) (Af I.F) (t : I.E), inclE_mem' I t, by rw [map_mul, map_natCast]⟩

theorem zmod_add {x y : I.E ⊗[I.F] Af I.F} (h1 : ZMod' I g x) (h2 : ZMod' I g y) :
    ZMod' I g (x + y) := by
  obtain ⟨a, ha, rfl⟩ := h1
  obtain ⟨b, hb, rfl⟩ := h2
  exact ⟨a + b, add_mem ha hb, (mul_add _ _ _).symm⟩

theorem zmod_mul_int {x y : I.E ⊗[I.F] Af I.F} (h : ZMod' I g x) (hy : y ∈ IntAf I.F I.E) :
    ZMod' I g (x * y) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a * y, mul_mem ha hy, mul_assoc _ _ _⟩

theorem zmod_eps {ε : I.E ⊗[I.F] Af I.F} {θ : I.E}
    (hε : ZMod' I g (ε - Formalism.UG.inclE (F := I.F) (Af I.F) θ)) {x : I.E}
    (hx : x ∈ (algebraMap (𝓞 I.E) I.E).range) (h : GE I g (θ * x)) :
    ZMod' I g (ε * Formalism.UG.inclE (F := I.F) (Af I.F) x) := by
  obtain ⟨s, rfl⟩ := hx
  have h1 := zmod_mul_int I g hε (inclE_mem' I s)
  have h2 := zmod_add I g h1 (zmod_of_GE I g h)
  convert h2 using 1
  rw [map_mul]
  have e : algebraMap (𝓞 I.E) I.E s = (s : I.E) := rfl
  rw [e]
  ring

theorem zmod_sig {ε : I.E ⊗[I.F] Af I.F} {θ : I.E}
    (hε : ZMod' I g (ε - Formalism.UG.inclE (F := I.F) (Af I.F) θ)) :
    ZMod' I g (sigA I ε - Formalism.UG.inclE (F := I.F) (Af I.F) (star θ)) := by
  obtain ⟨t, ht, he⟩ := hε
  have hinc : ∀ a : I.E, sigA I (Formalism.UG.inclE (F := I.F) (Af I.F) a) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
    intro a
    show (Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F))) (a ⊗ₜ[I.F] (1 : Af I.F)) =
      (star a) ⊗ₜ[I.F] (1 : Af I.F)
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hcl : Subring.closure (Set.range (fun x : Formalism.UG.intOE I.E => (x : I.E) ⊗ₜ[I.F] (1 : Af I.F)) ∪
      Set.range (fun y : Formalism.UG.intAd I.F => (1 : I.E) ⊗ₜ[I.F] (y : Af I.F))) ≤
      (IntAf I.F I.E).comap (sigA I) := by
    rw [Subring.closure_le]
    rintro _ (⟨⟨s, hs⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨s', rfl⟩ := hs
      show sigA I (Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E s')) ∈ IntAf I.F I.E
      rw [hinc]
      have hi : IsIntegral ℤ (star (algebraMap (𝓞 I.E) I.E s')) :=
        IsIntegral.map (starRingEnd I.E).toIntAlgHom (NumberField.RingOfIntegers.isIntegral_coe s')
      exact inclE_mem' I ⟨_, hi⟩
    · show (Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F))) ((1 : I.E) ⊗ₜ[I.F] (y : Af I.F)) ∈
        IntAf I.F I.E
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  refine ⟨sigA I t, hcl ht, ?_⟩
  rw [← hinc, ← map_sub, he, map_mul, map_natCast]

theorem hG_nsmul_left (m : ℕ) (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J (m • x) y = (m : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hG_nsmul_right (m : ℕ) (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J x (m • y) = (m : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_mL {x : VA I} (hx : x ∈ I.Lf) : ((g : ℕ) : I.E ⊗[I.F] Af I.F) • x ∈ mL I g :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem incl_osmul (c : 𝓞 I.E) (x : Fin I.n → I.E) :
    incl I (c • x) = (⟨Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E), inclE_mem' I c⟩ : IntAf I.F I.E) •
      incl I x := by
  funext i
  simp only [incl, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Algebra.smul_def, map_mul]
  rfl

theorem mem_L_of (h3 : LocGlob) {x : Fin I.n → I.E} (hx : incl I x ∈ I.Lf) : x ∈ I.L := by
  refine (I.L_dual x).mpr fun y hy => ?_
  let H : VA I → I.E ⊗[I.F] Af I.F := fun v =>
    ∑ i, ∑ j, Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E (y i) * I.J i j) * v j
  have hinc : ∀ z : Fin I.n → I.E, H (incl I z) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J y z) := by
    intro z
    simp only [H, incl, Formalism.UG.hform, map_sum, map_mul]
  have key : ∀ v ∈ I.Lf, H v ∈ IntAf I.F I.E := by
    intro v hv
    change v ∈ Submodule.span _ _ at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨z, rfl⟩ := hv
      change H (incl I (z : Fin I.n → I.E)) ∈ IntAf I.F I.E
      obtain ⟨s, hs⟩ := (I.L_dual z).mp z.2 y hy
      rw [hinc, ← hs]
      exact inclE_mem' I s
    | zero => simp [H]
    | add a b _ _ ha hb =>
      have e : H (a + b) = H a + H b := by
        simp only [H, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [e]
      exact add_mem ha hb
    | smul a v _ hv =>
      have e : H (a • v) = (a : I.E ⊗[I.F] Af I.F) * H v := by
        simp only [H, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e]
      exact mul_mem a.2 hv
  have hm := key _ hx
  rw [hinc x] at hm
  obtain ⟨s, hs⟩ := h3 I _ hm
  exact ⟨s, hs⟩

theorem incl_nsmul' (m : ℕ) (x : Fin I.n → I.E) : incl I (m • x) = m • incl I x := by
  funext i
  simp only [incl, Pi.smul_apply, map_nsmul]

theorem ge_of_nat {x : I.E} (m : ℕ) (h : x = (g : I.E) * (m : I.E)) : GE I g x :=
  ⟨(m : 𝓞 I.E), by rw [h]; exact congrArg _ (map_natCast (algebraMap (𝓞 I.E) I.E) m).symm⟩

end Lemmas

end PI.ScRefExists.GlueB

end
