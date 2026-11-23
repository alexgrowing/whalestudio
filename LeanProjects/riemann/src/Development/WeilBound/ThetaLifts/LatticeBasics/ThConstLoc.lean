import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable

noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Box

variable {A B : Type} [TopologicalSpace A] [TopologicalSpace B]

def boxL : (SB A) ⊗[ℂ] (SB B) →ₗ[ℂ] (A × B → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun a b z => a.1 z.1 * b.1 z.2) (fun _ _ _ => funext fun _ => add_mul _ _ _)
    (fun _ _ _ => funext fun _ => mul_assoc _ _ _) (fun _ _ _ => funext fun _ => mul_add _ _ _)
    fun _ _ _ => funext fun _ => mul_left_comm _ _ _)

theorem boxL_tmul (a : SB A) (b : SB B) : boxL (a ⊗ₜ[ℂ] b) = fun z => a.1 z.1 * b.1 z.2 := rfl

theorem boxL_ker : LinearMap.ker (boxL (A := A) (B := B)) = ⊥ := by
  classical
  refine LinearMap.ker_eq_bot'.2 fun x hx => ?_
  let e := Module.Basis.ofVectorSpace ℂ (SB A)
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left e x
  have h : ∀ i ∈ c.support, c i = 0 := fun i hi => Subtype.ext (funext fun y => by
    refine linearIndependent_iff'.1 e.linearIndependent c.support (fun i => (c i).1 y) (Subtype.ext (funext fun z => ?_)) i hi
    have := congrFun hx (z, y)
    simp only [Finsupp.sum, map_sum, boxL_tmul, Finset.sum_apply] at this
    simpa [mul_comm] using this)
  exact Finset.sum_eq_zero fun i hi => by simp [h i hi]

theorem mem_range_boxL [T2Space A] [T2Space B] {f : A × B → ℂ} (hf : f ∈ SB (A × B)) : f ∈ LinearMap.range boxL := by
  classical
  have hK : IsCompact (tsupport f) := hf.2
  have z : ∀ x y, (x, y) ∉ tsupport f → f (x, y) = 0 := fun x y h => image_eq_zero_of_notMem_tsupport h
  have hl : IsLocallyConstant fun x y => f (x, y) := (IsLocallyConstant.iff_eventually_eq _).2 fun x => by
    have h1 := (hK.image continuous_snd).eventually_forall_of_forall_eventually (x₀ := x)
      (P := fun x' y => f (x', y) = f (x, y)) fun y _ => by
        have a := (IsLocallyConstant.iff_eventually_eq _).1 hf.1 (x, y)
        have b : ∀ᶠ w : A × B in 𝓝 (x, y), f (x, w.2) = f (x, y) :=
          (IsLocallyConstant.iff_eventually_eq _).1 (hf.1.comp_continuous (f := fun w : A × B => (x, w.2)) (by fun_prop)) (x, y)
        filter_upwards [a, b] with w h h' using h.trans h'.symm
    filter_upwards [h1] with x' h
    funext y
    by_cases hy : y ∈ Prod.snd '' tsupport f
    · exact h y hy
    · rw [z _ _ fun h => hy ⟨_, h, rfl⟩, z _ _ fun h => hy ⟨_, h, rfl⟩]
  have hfin : ((fun x y => f (x, y)) '' (Prod.fst '' tsupport f)).Finite := by
    letI : TopologicalSpace (B → ℂ) := ⊥
    haveI : DiscreteTopology (B → ℂ) := ⟨rfl⟩
    exact ((hK.image continuous_fst).image hl.continuous).finite_of_discrete
  have e : f = ∑ g ∈ hfin.toFinset, fun w : A × B =>
      Set.indicator {x | (fun y => f (x, y)) = g} (fun x => if g = 0 then (0 : ℂ) else 1) w.1 * g w.2 := funext fun w => by
    rw [Finset.sum_apply, Finset.sum_eq_single (fun y => f (w.1, y)) (fun g _ hg => by simp [hg.symm])]
    · by_cases h : (fun y => f (w.1, y)) = 0
      · simpa [h] using congrFun h w.2
      · simp [h]
    · intro h
      exact mul_eq_zero_of_right _ (z w.1 w.2 fun h' => h (hfin.mem_toFinset.2 ⟨_, ⟨_, h', rfl⟩, rfl⟩))
  rw [e]
  refine Submodule.sum_mem _ fun g hg => ?_
  obtain ⟨x, -, rfl⟩ := hfin.mem_toFinset.1 hg
  refine ⟨(⟨_, (LocallyConstant.indicator (LocallyConstant.const A _) (hl.isClopen_fiber _)).2,
    HasCompactSupport.intro (hK.image continuous_fst) fun x' hx' => ?_⟩ : SB A) ⊗ₜ
    (⟨_, hf.1.comp_continuous (f := fun y => (x, y)) (by fun_prop),
      HasCompactSupport.intro (hK.image continuous_snd) fun y hy => z _ _ fun h => hy ⟨_, h, rfl⟩⟩ : SB B), rfl⟩
  have : (fun y => f (x', y)) = 0 := funext fun y => z _ _ fun h => hx' ⟨_, h, rfl⟩
  refine Set.indicator_apply_eq_zero.2 fun h => ?_
  exact if_pos (h.symm.trans this)

theorem sb_comp {f : B → ℂ} (hf : f ∈ SB B) (e : A ≃ₜ B) : (fun x => f (e x)) ∈ SB A :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

end Box

section Mat

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n n' d : ℕ}

def lrH (g : GL (Fin n) k) (h : GL (Fin d) k) : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k where
  toFun Y := g.1 * Y * h.1
  invFun Y := (g⁻¹).1 * Y * (h⁻¹).1
  left_inv Y := by simp [Matrix.mul_assoc]
  right_inv Y := by simp [Matrix.mul_assoc]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem sb_right {f : Matrix (Fin n) (Fin d) k → ℂ} (hf : f ∈ SB _) (h : GL (Fin d) k) :
    (fun y : Matrix (Fin n) (Fin d) k => f (y * h.1)) ∈ SB _ := by
  simpa [lrH] using sb_comp hf (lrH 1 h)

theorem sb_left {f : Matrix (Fin n) (Fin d) k → ℂ} (hf : f ∈ SB _) (g : GL (Fin n) k) :
    (fun y : Matrix (Fin n) (Fin d) k => f (g.1 * y)) ∈ SB _ := by
  simpa [lrH] using sb_comp hf (lrH g 1)

def rowsH (e : Fin n ⊕ Fin n' ≃ Fin d) : Matrix (Fin d) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k × Matrix (Fin n') (Fin d) k where
  toFun Y := ((Y.submatrix e id).toRows₁, (Y.submatrix e id).toRows₂)
  invFun Z := (Matrix.fromRows Z.1 Z.2).submatrix e.symm id
  left_inv Y := by simp
  right_inv Z := by simp
  continuous_toFun := by
    refine Continuous.prodMk (continuous_matrix fun i j => ?_) (continuous_matrix fun i j => ?_) <;>
      exact continuous_id.matrix_elem _ _
  continuous_invFun := continuous_matrix fun i j => by
    obtain ⟨i | i, rfl⟩ := e.surjective i <;>
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
    exacts [continuous_fst.matrix_elem _ _, continuous_snd.matrix_elem _ _]

end Mat

theorem locBil (hL : LocDist) {F : Type} [Field F] [NumberField F] (v : Pl F) {n n' d : ℕ} (e : Fin n ⊕ Fin n' ≃ Fin d)
    (ξ : (Fv F v)ˣ →* ℂˣ) (hξ : ∀ t : ℝ, 0 < t → (ξ (unifAt v) : ℂ) ≠ t)
    (β : SB (Matrix (Fin n) (Fin d) (Fv F v)) →ₗ[ℂ] SB (Matrix (Fin n') (Fin d) (Fv F v)) →ₗ[ℂ] ℂ)
    (hβ : ∀ a b (h : GL (Fin d) (Fv F v)), β ⟨_, sb_right a.2 h⟩ ⟨_, sb_right b.2 h⟩ = ξ (Matrix.GeneralLinearGroup.det h) * β a b)
    (a b) (g : GL (Fin n) (Fv F v)) : β ⟨_, sb_left a.2 g⟩ b = ξ (Matrix.GeneralLinearGroup.det g) * β a b := by
  obtain ⟨q, hq⟩ := (boxL (A := Matrix (Fin n) (Fin d) (Fv F v)) (B := Matrix (Fin n') (Fin d) (Fv F v))).exists_leftInverse_of_injective boxL_ker
  let l := TensorProduct.lift β ∘ₗ q ∘ₗ LinearMap.funLeft ℂ ℂ (rowsH (k := Fv F v) e).symm
  have hl : ∀ x, l (fun y => boxL x (rowsH e y)) = TensorProduct.lift β x := fun x => by
    have : LinearMap.funLeft ℂ ℂ (rowsH (k := Fv F v) e).symm (fun y => boxL x (rowsH e y)) = boxL x := funext fun y => by
      simp [LinearMap.funLeft_apply]
    simp only [l, LinearMap.comp_apply, this]
    rw [← LinearMap.comp_apply q, hq, LinearMap.id_apply]
  let G : Matrix (Fin d) (Fin d) (Fv F v) := Matrix.reindex e e (Matrix.fromBlocks g.1 0 0 1)
  have hG : G.det = g.1.det := by simp [G]
  let G' := Matrix.GeneralLinearGroup.mkOfDetNeZero G (hG ▸ g.det_ne_zero)
  have key := (hL F v d d ξ hξ l (fun φ hφ h => ?_)).2 rfl (fun y => boxL (a ⊗ₜ b) (rowsH e y))
    (sb_comp (f := fun z => a.1 z.1 * b.1 z.2) ⟨(a.2.1.comp_continuous continuous_fst).mul (b.2.1.comp_continuous continuous_snd),
      HasCompactSupport.intro (a.2.2.prod b.2.2) fun z hz => ?_⟩ _) G'
  · rw [hl, show Matrix.GeneralLinearGroup.det G' = Matrix.GeneralLinearGroup.det g from Units.ext hG] at key
    rw [← TensorProduct.lift.tmul, ← hl, ← TensorProduct.lift.tmul, ← key]
    congr 1
    funext y
    have : rowsH e (G * y) = (g.1 * (rowsH e y).1, (rowsH e y).2) := by
      ext i j <;> simp [rowsH, G, Matrix.mul_apply, ← e.sum_comp, Matrix.one_apply]
    exact (congrArg (boxL (a ⊗ₜ b)) this).symm
  · obtain ⟨x, hx⟩ := mem_range_boxL (sb_comp hφ (rowsH e).symm)
    obtain rfl : φ = fun y => boxL x (rowsH e y) := funext fun y => by simp [hx]
    clear hx hφ
    induction x using TensorProduct.induction_on with
    | zero => simp [← Pi.zero_def]
    | add x y hx hy =>
      simp only [map_add, Pi.add_apply]
      rw [← Pi.add_def, ← Pi.add_def, map_add, map_add, hx, hy, mul_add]
    | tmul a b =>
      rw [hl, TensorProduct.lift.tmul, ← hβ, ← TensorProduct.lift.tmul, ← hl]
      rfl
  · by_cases h : z.1 ∈ tsupport a.1
    · rw [image_eq_zero_of_notMem_tsupport (f := b.1) fun h' => hz ⟨h, h'⟩, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]

end GlobalTheory.ThK.Dbl.TC

end
