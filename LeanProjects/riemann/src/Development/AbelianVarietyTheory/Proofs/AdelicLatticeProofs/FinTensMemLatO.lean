import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVac

variable {D : D7}

def hRat (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.E :=
  ∑ a, ∑ b, ∑ c, ∑ d, S.gram⁻¹ a b * star (y c b) * T.gram c d * x d a

def genMap (S T : HSp D) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    Matrix (Fin T.rank) (Fin S.rank) D.host.E :=
  Matrix.of fun i j => a * t i * ∑ k, star (s k) * S.gram k j

def latRat (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) :
    AddSubgroup (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
  AddSubgroup.closure {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ s ∈ LS, ∃ t ∈ LT, w = genMap S T a s t}

def finTens {m n : ℕ} (α : Af D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  M.map fun x => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x

theorem finTens_add {m n : ℕ} (α : Af D.host.F) (M N : Matrix (Fin m) (Fin n) D.host.E) :
    finTens α (M + N) = finTens α M + finTens α N := by
  ext i j; simp [finTens, TensorProduct.tmul_add]

theorem finTens_zero {m n : ℕ} (α : Af D.host.F) :
    finTens α (0 : Matrix (Fin m) (Fin n) D.host.E) = 0 := by
  ext i j; simp [finTens]

theorem finTens_neg {m n : ℕ} (α : Af D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) :
    finTens α (-M) = -finTens α M := by
  ext i j; simp [finTens, TensorProduct.tmul_neg]

theorem smul_mem_latRat {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    (c : 𝓞 D.host.E) {M : Matrix (Fin T.rank) (Fin S.rank) D.host.E} (hM : M ∈ latRat S T LS LT) :
    (c : D.host.E) • M ∈ latRat S T LS LT := by
  induction hM using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨(c : D.host.E) * a, ?_, s, hs, t, ht, ?_⟩
    · exact Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) c ha
    · ext i j; simp [genMap, mul_assoc]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem finTens_mem_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {α : Af D.host.F} (hα : α ∈ intAf D.host.F) {M : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hM : M ∈ latRat S T LS LT) : finTens α M ∈ latO S T LS LT fun _ => True := by
  induction hM using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨α, hα, fun v hv => absurd trivial hv, a, ha, s, hs, t, ht, rfl⟩
  | zero => rw [finTens_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [finTens_add]; exact add_mem hx hy
  | neg x _ hx => rw [finTens_neg]; exact neg_mem hx

theorem latO_induction {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {p : WO S T → Prop} (mem : ∀ α ∈ intAf D.host.F, ∀ M ∈ latRat S T LS LT, p (finTens α M))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) (neg : ∀ x, p x → p (-x))
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) : p u := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    exact mem α hα (genMap S T a s t) (AddSubgroup.subset_closure ⟨a, ha, s, hs, t, ht, rfl⟩)
  | zero => exact zero
  | add x y _ _ hx hy => exact add _ _ hx hy
  | neg x _ hx => exact neg _ hx

theorem gram_star (S : HSp D) (i j : Fin S.rank) : star (S.gram i j) = S.gram j i :=
  S.herm.eq (S.frame i) (S.frame j)

theorem gram_det_isUnit (S : HSp D) : IsUnit S.gram.det := by
  rw [isUnit_iff_ne_zero]
  intro h
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have h1 : ∑ j, v j • S.frame j = 0 := by
    apply S.nondeg.2
    intro x
    have : (S.hT.flip (∑ j, v j • S.frame j)) = 0 := by
      refine S.frame.ext fun i => ?_
      have := congrFun hv0 i
      simpa [Matrix.mulVec, dotProduct, HSpace.gram, map_sum, mul_comm] using this
    exact LinearMap.congr_fun this x
  exact funext (Fintype.linearIndependent_iff.1 S.frame.linearIndependent v h1)

theorem hRat_genMap (S T : HSp D) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (a : D.host.E)
    (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    hRat S T x (genMap S T a s t) = star a * ∑ c, ∑ d, star (t c) * T.gram c d * (x *ᵥ s) d := by
  have key : ∀ e, ∑ b, S.gram⁻¹ e b * star (∑ k, star (s k) * S.gram k b) = s e := by
    intro e
    have : ∀ b, star (∑ k, star (s k) * S.gram k b) = (S.gram *ᵥ s) b := by
      intro b
      simp [star_sum, gram_star, Matrix.mulVec, dotProduct, mul_comm]
    simp_rw [this]
    change (S.gram⁻¹ *ᵥ (S.gram *ᵥ s)) e = _
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (gram_det_isUnit S), Matrix.one_mulVec]
  calc hRat S T x (genMap S T a s t)
      = ∑ e, (∑ b, S.gram⁻¹ e b * star (∑ k, star (s k) * S.gram k b)) *
          ∑ c, ∑ d, star a * star (t c) * T.gram c d * x d e := by
        unfold hRat genMap
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [Finset.mul_sum (s := Finset.univ (α := Fin T.rank)), Matrix.of_apply, star_mul']
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
    _ = _ := by
        simp_rw [key]
        simp only [Finset.mul_sum, Matrix.mulVec, dotProduct]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => by ring

theorem hO_finTens (S T : HSp D) (α β : Af D.host.F) (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hO S T (finTens α M) (finTens β N) = (pairA D.host.F 0 (α * β)) ⊗ₜ[D.host.F] hRat S T M N := by
  have hp : pairA D.host.F 0 (α * β) = pairA D.host.F 0 β * pairA D.host.F 0 α := by
    exact Prod.ext (mul_zero _).symm (mul_comm _ _)
  unfold hO hRat
  simp only [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  have h1 : cA D (finTens β N c b) = (pairA D.host.F 0 β) ⊗ₜ[D.host.F] star (N c b) := rfl
  have h2 : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun x => rfl
  rw [h1, h2, h2, hp]
  simp [finTens, Algebra.TensorProduct.tmul_mul_tmul]

theorem trace_tmul {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem symplO_finTens (S T : HSp D) (α β : Af D.host.F) (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplO S T (finTens α M) (finTens β N) = pairA D.host.F 0 (α * β * algebraMap D.host.F (Af D.host.F)
      (Algebra.trace D.host.F D.host.E (D.host.xi0 * hRat S T M N))) := by
  have h2 : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun x => rfl
  rw [symplO, hO_finTens, h2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_tmul]
  exact Prod.ext (zero_mul _) rfl

theorem hO_add_left (S T : HSp D) (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  simp only [hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  simp only [hO, Matrix.add_apply, RingHom.map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_add_left (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  rw [symplO, hO_add_left, mul_add, map_add]; rfl

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  rw [symplO, hO_add_right, mul_add, map_add]; rfl

def symplHom (S T : HSp D) : WO S T →+ WO S T →+ AF D.host.F :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (symplO S T x) (symplO_add_right S T x))
    fun x x' => AddMonoidHom.ext fun y => symplO_add_left S T x x' y

theorem symplHom_apply (S T : HSp D) (x y : WO S T) : symplHom S T x y = symplO S T x y := rfl

end GlobalTheory.LatVac

end
