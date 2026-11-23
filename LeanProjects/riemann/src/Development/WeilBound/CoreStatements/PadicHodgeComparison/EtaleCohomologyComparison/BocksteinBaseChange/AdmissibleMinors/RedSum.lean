import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.RedAbs

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison.Inj

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {G : Model l K → Prop}

theorem red_sum (P : Pre G R) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (hM : G M) (hN : G N) (n : ℕ)
    {a c : ℕ} (b : Module.Basis (Fin a) ℚ_[l] (N.V n)) (e : Module.Basis (Fin c) ℚ_[l] (M.V n)) (z : Fin a → R.B)
    (φ : Module.Dual K (HdR M.q n)) :
    ∑ j, (∑ m, z m * R.q (e.coord j (Model.pullV u hu n (b m)))) * P.c M n (e j) φ =
      ∑ m, z m * P.c N n (b m) (φ ∘ₗ pullR n (Model.genMap u hu) (Model.genMap_q u hu)) := by
  have hexp : ∀ v, P.c M n v φ = ∑ j, R.q (e.coord j v) * P.c M n (e j) φ := by
    intro v
    conv_lhs => rw [← e.sum_repr v]
    rw [map_sum, AddMonoidHom.finsetSum_apply]
    simp only [P.lin, Module.Basis.coord_apply]
  simp_rw [← P.nat M N u hu n hM hN, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hexp (Model.pullV u hu n (b m)), Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem reduce (P : Pre G R) (hR : R.Facts) (hE : EtSide G)
    (hpull : ∀ (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n r : ℕ), ∀ x ∈ FilR N.q n r,
      pullR n (Model.genMap u hu) (Model.genMap_q u hu) x ∈ FilR M.q n r)
    (hconn : ∀ M, G M → ∀ d, M.Conn d → ∀ n, P.Inj M n ∧ P.Strict M n) :
    ∀ M, G M → ∀ n, P.Inj M n ∧ P.Strict M n := by
  intro M hM n
  obtain ⟨r, Q, d, u, hu, hQ, hinj⟩ := hE.comp M hM
  have : ∀ a, FiniteDimensional ℚ_[l] ((Q a).V n) := fun a => hE.fin _ (hQ a).1 n
  let e : ∀ a, Module.Basis (Fin (Module.finrank ℚ_[l] ((Q a).V n))) ℚ_[l] ((Q a).V n) :=
    fun a => Module.finBasis _ _
  let f : (Σ a, Fin (Module.finrank ℚ_[l] ((Q a).V n))) → Module.Dual ℚ_[l] (M.V n) :=
    fun i => (e i.1).coord i.2 ∘ₗ Model.pullV (u i.1) (hu i.1) n
  have hf : ∀ v, (∀ i, f i v = 0) → v = 0 := by
    intro v hv
    refine hinj n v fun a => (e a).ext_elem fun j => ?_
    simpa [f, Module.Basis.coord_apply] using hv ⟨a, j⟩
  refine ⟨fun {c} b z hz => ?_, fun {c} b z hz => ?_⟩
  · funext m
    have hm := red_abs R.q ⊥ (fun x s hs => by rw [AddSubgroup.mem_bot] at hs ⊢; rw [hs, mul_zero]) f hf b z ?_ m
    · simpa using hm
    rintro ⟨a, j⟩
    have hc := (hconn (Q a) (hQ a).1 (d a) (hQ a).2 n).1 (e a) (fun j => ∑ m, z m * R.q (f ⟨a, j⟩ (b m))) (fun φ => by
      have h := hz (φ ∘ₗ pullR n (Model.genMap (u a) (hu a)) (Model.genMap_q (u a) (hu a)))
      rw [← red_sum P (u a) (hu a) (hQ a).1 hM n b (e a) z φ] at h
      exact h)
    rw [AddSubgroup.mem_bot]
    exact congrFun hc j
  · intro m
    refine red_abs R.q R.P.toAddSubgroup (fun x s hs => R.P.mul_mem (hR.q_mem x) hs) f hf b z ?_ m
    rintro ⟨a, j⟩
    refine (hconn (Q a) (hQ a).1 (d a) (hQ a).2 n).2 (e a) (fun j => ∑ m, z m * R.q (f ⟨a, j⟩ (b m)))
      (fun r φ hφ => ?_) j
    have h := hz r (φ ∘ₗ pullR n (Model.genMap (u a) (hu a)) (Model.genMap_q (u a) (hu a)))
      (fun x hx => hφ _ (hpull (Q a) M (u a) (hu a) n (r + 1) x hx))
    rw [← red_sum P (u a) (hu a) (hQ a).1 hM n b (e a) z φ] at h
    exact h

end CrystallineSemistableComparison.Inj
