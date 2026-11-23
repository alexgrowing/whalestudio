import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.FbExists

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Restr.PphiB

open PositivityTheory.RgUd.TP.Desc.Restr PositivityTheory.RgUd.TP.Desc.Restr.PphiA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p c d : ℕ} [Fact p.Prime] [CharP k p] (B : FB k (p ^ c) d) {n : ℕ}

abbrev ix (r : Fin (n * d)) : Fin n × Fin d := finProdFinEquiv.symm r

def eF (v : Fin n → k) : Fin (n * d) → k := fun r => B.cF (v (ix r).1) (ix r).2

def eI (w : Fin (n * d) → k) : Fin n → k := fun i => ∑ j, w (finProdFinEquiv (i, j)) ^ p ^ c * B.β j

def φM (x : Matrix (Fin n) (Fin n) k) : Matrix (Fin (n * d)) (Fin (n * d)) k :=
  fun r s => B.cF (x (ix r).1 (ix s).1 * B.β (ix s).2) (ix r).2

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem eI_eF (v : Fin n → k) : eI B (eF B v) = v := by
  funext i
  simp only [eI, eF, ix, Equiv.symm_apply_apply]
  exact B.recon (v i)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem eF_eI (w : Fin (n * d) → k) : eF B (eI B w) = w := by
  funext r
  have h := B.uniq (fun j => w (finProdFinEquiv ((ix r).1, j)))
  simp only [eF, eI]
  rw [h]
  exact congrArg w (finProdFinEquiv.apply_symm_apply r)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem eF_add (v v' : Fin n → k) : eF B (v + v') = eF B v + eF B v' := by
  funext r; simp [eF]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem key (x : Matrix (Fin n) (Fin n) k) (v : Fin n → k) : eF B (x *ᵥ v) = φM B x *ᵥ eF B v := by
  funext r
  simp only [eF, φM, mulVec, dotProduct]
  rw [map_sum, Finset.sum_apply]
  rw [← (finProdFinEquiv : Fin n × Fin d ≃ Fin (n * d)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i' _ => ?_
  simp only [ix, Equiv.symm_apply_apply]
  conv_lhs => rw [← B.recon (v i'), Finset.mul_sum, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [show x (finProdFinEquiv.symm r).1 i' * (B.cF (v i') j' ^ p ^ c * B.β j') =
      B.cF (v i') j' ^ p ^ c * (x (finProdFinEquiv.symm r).1 i' * B.β j') by ring, fb_smul]
  ring

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem eF_surj : Function.Surjective (eF B (n := n)) := fun w => ⟨eI B w, eF_eI B w⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem ext_of_eF {M M' : Matrix (Fin (n * d)) (Fin (n * d)) k} (h : ∀ v, M *ᵥ eF B v = M' *ᵥ eF B v) : M = M' := by
  have hw : ∀ w, M *ᵥ w = M' *ᵥ w := by
    intro w
    obtain ⟨v, rfl⟩ := eF_surj B w
    exact h v
  ext i j
  have h1 := congrFun (hw (Pi.single j 1)) i
  simpa [mulVec_single_one] using h1

def φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin (n * d)) (Fin (n * d)) k where
  toFun := φM B
  map_one' := ext_of_eF B fun v => by rw [← key, one_mulVec, one_mulVec]
  map_mul' x y := ext_of_eF B fun v => by rw [← key, ← mulVec_mulVec, ← mulVec_mulVec, ← key, ← key, mulVec_mulVec]
  map_zero' := ext_of_eF B fun v => by
    rw [← key, zero_mulVec, zero_mulVec]; funext r; simp [eF]
  map_add' x y := ext_of_eF B fun v => by rw [← key, add_mulVec, add_mulVec, eF_add, key, key]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem φ_apply_mulVec (x : Matrix (Fin n) (Fin n) k) (v : Fin n → k) : φ B x *ᵥ eF B v = eF B (x *ᵥ v) :=
  (key B x v).symm

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem φ_inj : Function.Injective (φ B (n := n)) := by
  intro x y h
  have hv : ∀ v, x *ᵥ v = y *ᵥ v := by
    intro v
    have h1 := φ_apply_mulVec B x v
    rw [h, φ_apply_mulVec] at h1
    have h2 := congrArg (eI B) h1
    rw [eI_eF, eI_eF] at h2
    exact h2.symm
  ext i j
  have h1 := congrFun (hv (Pi.single j 1)) i
  simpa [mulVec_single_one] using h1

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem φ_scal (a : k) : φ B (algebraMap k (Matrix (Fin n) (Fin n) k) (a ^ p ^ c)) = algebraMap k _ a := by
  apply ext_of_eF B
  intro v
  rw [φ_apply_mulVec]
  funext r
  simp [algebraMap_eq_diagonal, mulVec_diagonal, eF, fb_smul]

def e : (Fin n → k) ≃+ (Fin (n * d) → k) where
  toFun := eF B
  invFun := eI B
  left_inv := eI_eF B
  right_inv := eF_eI B
  map_add' := eF_add B

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem continuous_eF : Continuous (eF B (n := n)) := by
  refine continuous_pi fun r => ?_
  exact (continuous_apply _).comp (B.cont.comp (continuous_apply _))

theorem continuous_eI : Continuous (eI B (n := n)) := by
  unfold eI; fun_prop

theorem continuous_φ : Continuous (φ B (n := n)) := by
  show Continuous (φM B)
  unfold φM
  refine continuous_pi fun r => continuous_pi fun s => ?_
  have hx : Continuous fun a : Matrix (Fin n) (Fin n) k => a (ix r).1 (ix s).1 * B.β (ix s).2 := by
    fun_prop
  exact (continuous_apply _).comp (B.cont.comp hx)

def ψ (M : Matrix (Fin (n * d)) (Fin (n * d)) k) : Matrix (Fin n) (Fin n) k :=
  fun i i' => eI B (M *ᵥ eF B (Pi.single i' 1)) i

theorem ψ_φ (x : Matrix (Fin n) (Fin n) k) : ψ B (φ B x) = x := by
  funext i i'
  simp [ψ, φ_apply_mulVec, eI_eF, mulVec_single_one]

theorem continuous_ψ : Continuous (ψ B (n := n)) := by
  unfold ψ
  refine continuous_pi fun i => continuous_pi fun i' => ?_
  exact (continuous_apply i).comp ((continuous_eI B).comp (continuous_id.matrix_mulVec continuous_const))

theorem φ_emb : Topology.IsClosedEmbedding (φ B (n := n)) :=
  Function.LeftInverse.isClosedEmbedding (ψ_φ B) (continuous_ψ B) (continuous_φ B)

end PositivityTheory.RgUd.TP.Desc.Restr.PphiB
