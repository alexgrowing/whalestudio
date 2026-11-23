import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl.CoupStab
open GlobalTheory.StepData GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_mem_box {n : Type} [Fintype n] {M : Matrix n n k} (hM : IntM M) {c : kˣ} {y : n → k}
    (hy : y ∈ box n c) : M *ᵥ y ∈ box n c := by
  rw [mem_box] at hy ⊢
  intro i
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le (hM i j) (hy j)

theorem toBlocks₁₁_mul {n : Type} [Fintype n] (M N : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  ext i j; simp [Matrix.mul_apply, Matrix.toBlocks₁₁, Fintype.sum_sum_type]

theorem toBlocks₁₁_one {n : Type} [Fintype n] [DecidableEq n] :
    (1 : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k).toBlocks₁₁ = 1 := by
  ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]

theorem withCol_mul {n n' : Type} [Fintype n] (κ : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) (x₀ : Matrix n n' k)
    (y : n → k) : κ * withCol x₀ y = withCol (κ.toBlocks₁₁ * x₀) (κ.toBlocks₁₁ *ᵥ y) := by
  ext (r | r) (c | c)
  · simp [withCol, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁]
  · simp [withCol, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.mulVec, dotProduct]
  · exact r.elim0
  · exact r.elim0

theorem box_eq_preimage {n : Type} (c : kˣ) :
    (box n c : Set (n → k)) = (fun y : n → k => ((c⁻¹ : kˣ) : k) • y) ⁻¹' Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
  ext y
  simp only [SetLike.mem_coe, mem_box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Pi.smul_apply,
    smul_eq_mul]
  refine forall_congr' fun i => ?_
  rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  have hc : 0 < valuation k (c : k) := by
    rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 c.ne_zero
  rw [inv_mul_le_iff₀ hc, mul_one]

theorem isOpen_box {n : Type} [Fintype n] (c : kˣ) : IsOpen (box n c : Set (n → k)) := by
  rw [box_eq_preimage]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => (valuation k).isOpen_integer).preimage (continuous_const_smul _)

theorem isCompact_box {n : Type} [Fintype n] (c : kˣ) : IsCompact (box n c : Set (n → k)) := by
  have hK : IsCompact (𝒪[k] : Set k) := isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[k]))
  have e : (box n c : Set (n → k)) = (fun y : n → k => (c : k) • y) '' Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
    rw [box_eq_preimage, Set.image_eq_preimage_of_inverse]
    · intro y; simp [smul_smul]
    · intro y; simp [smul_smul]
  rw [e]
  exact (isCompact_univ_pi fun _ => hK).image (continuous_const_smul _)

theorem finite_image_box {n : Type} [Fintype n] (c₁ c₂ : kˣ) :
    ((Submodule.Quotient.mk (p := box n c₂)) '' (box n c₁ : Set (n → k))).Finite := by
  obtain ⟨t, -, ht⟩ := (isCompact_box (n := n) c₁).elim_nhds_subcover
    (fun y => (fun z => z - y) ⁻¹' (box n c₂ : Set (n → k)))
    (fun y _ => ((isOpen_box c₂).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by show y - y ∈ box n c₂; rw [sub_self]; exact zero_mem _))
  refine (t.finite_toSet.image (Submodule.Quotient.mk (p := box n c₂))).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht hy)
  refine ⟨z, hz, (Submodule.Quotient.eq _).2 ?_⟩
  rw [← neg_sub]; exact neg_mem hyz

theorem om_one_ne {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (h : GL b k) (Φ : Matrix b a k → ℂ) (x : Matrix b a k) (hx : om μ 1 h Φ x ≠ 0) : Φ ((h⁻¹ : GL b k).val * x) ≠ 0 := by
  unfold om at hx
  have := right_ne_zero_of_mul hx
  simpa using this

theorem om_g_ne {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (Φ : Matrix b a k → ℂ) (x x' : Matrix b a k) (hx : om μ g 1 Φ x ≠ 0)
    (h : Φ (x * g.val) ≠ 0 → Φ (x' * g.val) ≠ 0) : om μ g 1 Φ x' ≠ 0 := by
  unfold om at *
  simp only [inv_one, Units.val_one, Matrix.one_mul] at *
  exact mul_ne_zero (left_ne_zero_of_mul hx) (h (right_ne_zero_of_mul hx))

end GlobalTheory.QPl.CoupStab

namespace GlobalTheory.QPl.CoupStab
open GlobalTheory.StepData GlobalTheory.SplitWeil

theorem psi_ne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
    (T : Chain k s X Z) (hL : T.Laws) {κ : GL (X (s + 1) ⊕ Fin 0) k} (hκ : κ ∈ (T.lev (s + 1) 0 rfl).J)
    (g : GL (X s ⊕ Fin (0 + 1)) k) (x₀ : Matrix (X (s + 1)) (X s) k) (y : X (s + 1) → k) (h : T.Psi g x₀ y ≠ 0) :
    T.Psi g (κ.val.toBlocks₁₁ * x₀) (κ.val.toBlocks₁₁ *ᵥ y) ≠ 0 := by
  have hPhi : ∀ x, T.Phi s 0 rfl x ≠ 0 → T.Phi s 0 rfl (κ.val * x) ≠ 0 := by
    intro x hx
    have e := congrFun ((hL.1 s 0 rfl).2 ⟨κ⁻¹, inv_mem hκ⟩) x
    have hr : om (T.mu (s + 1)) 1 (κ⁻¹ : GL (X (s + 1) ⊕ Fin 0) k) (T.Phi s 0 rfl) x ≠ 0 := by
      rw [e, Pi.smul_apply, smul_eq_mul]; exact mul_ne_zero (Units.ne_zero _) hx
    simpa using om_one_ne _ _ _ _ hr
  unfold Chain.Psi at *
  refine om_g_ne _ _ _ _ _ h fun h' => ?_
  rw [← withCol_mul, Matrix.mul_assoc]
  exact hPhi _ h'

theorem coupIdx_stab : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), (Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)).Finite ∧ (∀ yb, SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb) ∧ (∀ yb yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb) ∧ (∀ yb yb' yb'', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb'' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb'') ∧ ∀ yb ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂), ∀ yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → yb' ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) := by
  intro D c v χ Q
  have hB : ∀ {g : GL (Q.X (Q.s + 1) ⊕ Fin 0) Q.k}, g ∈ (Q.T.lev (Q.s + 1) 0 rfl).J → IntM g.val.toBlocks₁₁ :=
    fun hg i j => intM_of_mem_KO (Q.le _ _ _ hg) (.inl i) (.inl j)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (finite_image_box Q.c₁ Q.c₂).subset (by rintro _ ⟨y, hy, rfl, -⟩; exact ⟨y, hy, rfl⟩)
  · intro yb
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ yb
    refine ⟨1, one_mem _, y, rfl, ?_⟩
    rw [Units.val_one, toBlocks₁₁_one, Matrix.one_mulVec]
  · rintro _ _ ⟨g, hg, y, rfl, rfl⟩
    refine ⟨g⁻¹, inv_mem hg, _, rfl, ?_⟩
    rw [Matrix.mulVec_mulVec, ← toBlocks₁₁_mul, Units.inv_mul, toBlocks₁₁_one, Matrix.one_mulVec]
  · rintro _ _ _ ⟨g, hg, y, rfl, h1⟩ ⟨g', hg', y', h2, h3⟩
    refine ⟨g' * g, mul_mem hg' hg, y, rfl, ?_⟩
    rw [← h3, Units.val_mul, toBlocks₁₁_mul, ← Matrix.mulVec_mulVec]
    refine (Submodule.Quotient.eq _).2 ?_
    rw [← Matrix.mulVec_sub]
    exact mulVec_mem_box (hB hg') ((Submodule.Quotient.eq _).1 (h1.trans h2.symm))
  · rintro _ ⟨y₁, -, rfl, g, hg, x₀, hΨ⟩ _ ⟨κ, hκ, y, hy, rfl⟩
    have hd : y - y₁ ∈ box _ Q.c₂ := (Submodule.Quotient.eq _).1 hy
    have hΨy : Q.T.Psi g x₀ y ≠ 0 := by
      rw [show y = y₁ + (y - y₁) by abel, (Q.adapt g hg x₀ y₁).2 _ hd]; exact hΨ
    exact ⟨_, mulVec_mem_box (hB hκ) ((Q.adapt g hg x₀ y).1 hΨy), rfl, g, hg, _,
      psi_ne Q.T Q.laws hκ g x₀ y hΨy⟩

end GlobalTheory.QPl.CoupStab
