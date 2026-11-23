import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.KirFin

theorem mem_of_separates {X : Type} [TopologicalSpace X] [CompactSpace X] (A : Subalgebra ℂ (X → ℂ))
    (hA : ∀ a ∈ A, IsLocallyConstant a) (hs : ∀ x y, x ≠ y → ∃ a ∈ A, a x ≠ a y) {f : X → ℂ}
    (hf : IsLocallyConstant f) : f ∈ A := by
  classical
  have hind : ∀ a ∈ A, ∀ c : ℂ, (fun x => if a x = c then (1 : ℂ) else 0) ∈ A := by
    intro a ha c
    have hfin := (hA a ha).range_finite
    have e : (fun x => if a x = c then (1 : ℂ) else 0) =
        ∏ d ∈ hfin.toFinset.erase c, (c - d)⁻¹ • (a - algebraMap ℂ (X → ℂ) d) := by
      funext x
      simp only [Finset.prod_apply, Pi.smul_apply, Pi.sub_apply, Pi.algebraMap_apply, smul_eq_mul,
        Algebra.algebraMap_self, RingHom.id_apply]
      split_ifs with h
      · refine (Finset.prod_eq_one fun d hd => ?_).symm
        rw [h]
        exact inv_mul_cancel₀ (sub_ne_zero.2 (Finset.ne_of_mem_erase hd).symm)
      · exact (Finset.prod_eq_zero (i := a x) (by simp [h]) (by simp)).symm
    rw [e]
    exact A.prod_mem fun d _ => A.smul_mem (A.sub_mem ha (A.algebraMap_mem d)) _
  have hcl : ∀ a : X → ℂ, IsLocallyConstant a → IsClopen {p : X × X | a p.1 ≠ a p.2} := fun a ha => by
    have h1 : IsLocallyConstant fun p : X × X => a p.1 - a p.2 :=
      (ha.comp_continuous continuous_fst).sub (ha.comp_continuous continuous_snd)
    convert (h1.isClopen_fiber 0).compl using 1
    ext p
    simp [sub_eq_zero]
  obtain ⟨t, ht⟩ := (hcl f hf).isClosed.isCompact.elim_finite_subcover
    (fun a : A => {p : X × X | a.1 p.1 ≠ a.1 p.2}) (fun a => (hcl _ (hA _ a.2)).isOpen) (by
      intro p hp
      obtain ⟨a, ha, h⟩ := hs p.1 p.2 fun h => hp (by rw [h])
      exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, h⟩)
  let T : X → (t → ℂ) := fun x a => a.1.1 x
  have hT : ∀ x y, T x = T y → f x = f y := fun x y h => by
    by_contra hne
    obtain ⟨a, ha, h'⟩ := Set.mem_iUnion₂.1 (ht (show (x, y) ∈ _ from hne))
    exact h' (congrFun h ⟨a, ha⟩)
  have hfin : (Set.range T).Finite :=
    (Set.Finite.pi' fun a : t => (hA _ a.1.2).range_finite).subset (by rintro _ ⟨x, rfl⟩ a; exact ⟨x, rfl⟩)
  let v : (t → ℂ) → ℂ := fun c => if h : c ∈ Set.range T then f h.choose else 0
  have e : f = ∑ c ∈ hfin.toFinset, v c • ∏ a : t, fun x => if a.1.1 x = c a then (1 : ℂ) else 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Finset.prod_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (T x)]
    · have hx : T x ∈ Set.range T := ⟨x, rfl⟩
      simp only [v, dif_pos hx, T, if_true, Finset.prod_const_one, mul_one]
      exact (hT _ _ hx.choose_spec).symm
    · intro c _ hc
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hc
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (if_neg (Ne.symm ha)), mul_zero]
    · simp
  rw [e]
  exact A.sum_mem fun c _ => A.smul_mem (A.prod_mem fun a _ => hind _ a.1.2 _) _

variable {F : Type} [NormedField F]

theorem mul_mem_of_char [ProperSpace F] {ψ : AddChar F ℂ} (hψ : IsLocallyConstant ψ) (hψ1 : ψ ≠ 1) {X ι : Type}
    [Fintype ι] (r : X → ι → F) (𝒱 : Submodule ℂ (X → ℂ))
    (h𝒱 : ∀ V ∈ 𝒱, ∀ x : ι → F, (fun h => ψ (r h ⬝ᵥ x) * V h) ∈ 𝒱) {V : X → ℂ} (hV : V ∈ 𝒱)
    (hL : ∀ᶠ x in 𝓝 (0 : ι → F), ∀ h, ψ (r h ⬝ᵥ x) * V h = V h) {φ : (ι → F) → ℂ} (hφ : IsLocallyConstant φ) :
    (fun h => φ (r h) * V h) ∈ 𝒱 := by
  classical
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ1 (AddChar.ext _ _ h)
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.1 hL
  let K : Set (ι → F) := Metric.closedBall 0 (‖t‖ / ε)
  have hK : ∀ h, V h ≠ 0 → r h ∈ K := by
    intro h hh
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    by_contra hi
    push_neg at hi
    have h0 : 0 < ‖r h i‖ := lt_of_le_of_lt (by positivity) hi
    have h1 := hb (Pi.single i (t / r h i)) (by
      rw [mem_ball_zero_iff, Pi.norm_single, norm_div, div_lt_iff₀ h0]
      rwa [div_lt_iff₀ hε, mul_comm] at hi) h
    rw [dotProduct_single, mul_div_cancel₀ _ (norm_pos_iff.1 h0)] at h1
    exact ht ((mul_eq_right₀ hh).1 h1)
  let A : Subalgebra ℂ ((ι → F) → ℂ) :=
    { carrier := {a | IsLocallyConstant a ∧ ∀ V' ∈ 𝒱, (fun h => a (r h) * V' h) ∈ 𝒱}
      mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, fun V' hV' => by
        simpa only [Pi.mul_apply, mul_assoc] using ha.2 _ (hb.2 V' hV')⟩
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun V' hV' => by
        simp only [Pi.add_apply, add_mul]; exact 𝒱.add_mem (ha.2 V' hV') (hb.2 V' hV')⟩
      algebraMap_mem' := fun c => ⟨IsLocallyConstant.const _, fun V' hV' => 𝒱.smul_mem c hV'⟩ }
  let ρ : ((ι → F) → ℂ) →ₐ[ℂ] (K → ℂ) :=
    { toFun := fun a x => a x.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  obtain ⟨a, ha, e⟩ := mem_of_separates (A.map ρ)
    (by rintro _ ⟨a, ha, rfl⟩; exact ha.1.comp_continuous continuous_subtype_val)
    (by
      intro x y hxy
      obtain ⟨i, hi⟩ := Function.ne_iff.1 (Subtype.coe_ne_coe.2 hxy)
      refine ⟨ρ fun z => ψ (z ⬝ᵥ Pi.single i (t / (x.1 i - y.1 i))), ⟨_, ⟨hψ.comp_continuous
        (continuous_id.dotProduct continuous_const), fun V' hV' => h𝒱 V' hV' _⟩, rfl⟩, fun h => ht ?_⟩
      change ψ (x.1 ⬝ᵥ _) = ψ (y.1 ⬝ᵥ _) at h
      rw [dotProduct_single, dotProduct_single] at h
      have h2 : x.1 i * (t / (x.1 i - y.1 i)) = t + y.1 i * (t / (x.1 i - y.1 i)) := by
        have := sub_ne_zero.2 hi
        field_simp
        ring
      rw [h2, AddChar.map_add_eq_mul] at h
      exact (mul_eq_right₀ (ψ.val_isUnit _).ne_zero).1 h)
    (hφ.comp_continuous continuous_subtype_val)
  convert ha.2 V hV using 2 with h
  by_cases hh : V h = 0
  · simp [hh]
  · exact congrArg (· * V h) (congrFun e ⟨r h, hK h hh⟩).symm

theorem isEmbedding_coe {n : Type} [Fintype n] [DecidableEq n] : IsEmbedding (fun g : GL n F => g.val) := by
  refine Units.isEmbedding_val_mk' (f := fun A : Matrix n n F => A⁻¹) (fun A hA => ?_) fun u => by simp
  refine (continuousAt_matrix_inv A ?_).continuousWithinAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero

variable {m : ℕ}

def lr (g : GL (Fin (m + 1)) F) : Fin (m + 1) → F := g.val (Fin.last m)

theorem lr_mul (g h : GL (Fin (m + 1)) F) : lr (g * h) = lr g ᵥ* h.val := rfl

theorem lr_mul_congr {a b : GL (Fin (m + 1)) F} (h : lr a = lr b) (c : GL (Fin (m + 1)) F) :
    lr (a * c) = lr (b * c) := by rw [lr_mul, lr_mul, h]

theorem continuous_lr : Continuous (lr : GL (Fin (m + 1)) F → _) :=
  continuous_pi fun j => Units.continuous_val.matrix_elem (Fin.last m) j

theorem lr_eq_iff {g : GL (Fin (m + 1)) F} :
    lr g = lr 1 ↔ ∀ j, g.val (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
  simp [lr, funext_iff, Matrix.one_apply, eq_comm]

theorem lr_of_mem {u : GL (Fin (m + 1)) F} (hu : u ∈ unipB F (Fin (m + 1))) : lr u = lr 1 := by
  rw [mem_unipB] at hu
  refine lr_eq_iff.2 fun j => ?_
  split_ifs with h
  · rw [h]; exact hu.2 _
  · exact hu.1 _ _ (Fin.lt_last_iff_ne_last.2 h)

theorem eventually_mem_orbit (g : GL (Fin (m + 1)) F) (U : Set (GL (Fin (m + 1)) F)) (hU : IsOpen U) (h1 : 1 ∈ U) :
    ∀ᶠ y in 𝓝 (lr g), ∀ h, lr h = y → ∃ p, lr p = lr 1 ∧ ∃ u ∈ U, h = p * g * u := by
  obtain ⟨O, hO, rfl⟩ := isEmbedding_coe.isInducing.isOpen_iff.1 hU
  let c : Fin (m + 1) → F := fun i => (g⁻¹).val i (Fin.last m)
  have hc : lr g ⬝ᵥ c = 1 := by
    have : (g * g⁻¹).val (Fin.last m) (Fin.last m) = 1 := by simp
    exact this
  let s : (Fin (m + 1) → F) → Matrix (Fin (m + 1)) (Fin (m + 1)) F := fun y => 1 + vecMulVec c (y - lr g)
  have hs : Continuous s := continuous_const.add (continuous_const.matrix_vecMulVec (continuous_id.sub continuous_const))
  have hs1 : s (lr g) = 1 := by simp [s]
  have e1 : ∀ᶠ y in 𝓝 (lr g), s y ∈ O := hs.continuousAt.eventually_mem (hO.mem_nhds (by rw [hs1]; exact h1))
  have e2 : ∀ᶠ y in 𝓝 (lr g), (s y).det ≠ 0 := hs.matrix_det.continuousAt.eventually_ne (by simp [hs1])
  filter_upwards [e1, e2] with y hy1 hy2 h hh
  let u : GL (Fin (m + 1)) F := GeneralLinearGroup.mkOfDetNeZero _ hy2
  have e : lr h = lr (g * u) := by
    rw [lr_mul, hh]
    change y = lr g ᵥ* (1 + vecMulVec c (y - lr g))
    rw [vecMul_add, vecMul_one, vecMul_vecMulVec, hc]
    simp
  refine ⟨h * (g * u)⁻¹, by rw [lr_mul_congr e, mul_inv_cancel], u, hy1, by group⟩

def mirM (A : Matrix (Fin m) (Fin m) F) (x : Fin m → F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j) (fun i => Fin.lastCases (x i) (fun j => A i j) j) i

section
variable (A : Matrix (Fin m) (Fin m) F) (x : Fin m → F)
@[simp] theorem mirM_cc (i j : Fin m) : mirM A x i.castSucc j.castSucc = A i j := by simp [mirM]
@[simp] theorem mirM_cl (i : Fin m) : mirM A x i.castSucc (Fin.last m) = x i := by simp [mirM]
@[simp] theorem mirM_lc (j : Fin m) : mirM A x (Fin.last m) j.castSucc = 0 := by simp [mirM]
@[simp] theorem mirM_ll : mirM A x (Fin.last m) (Fin.last m) = 1 := by simp [mirM]
end

theorem mirM_mul (A B : Matrix (Fin m) (Fin m) F) (x y : Fin m → F) :
    mirM A x * mirM B y = mirM (A * B) (A *ᵥ y + x) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, mulVec, dotProduct]

theorem mirM_one : mirM (1 : Matrix (Fin m) (Fin m) F) 0 = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem continuous_mirM {Y : Type} [TopologicalSpace Y] {A : Y → Matrix (Fin m) (Fin m) F} {x : Y → Fin m → F}
    (hA : Continuous A) (hx : Continuous x) : Continuous fun y => mirM (A y) (x y) := by
  refine continuous_matrix fun i j => ?_
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp only [mirM_cc, mirM_cl, mirM_lc, mirM_ll]
  exacts [continuous_const, continuous_const, (continuous_apply _).comp hx, hA.matrix_elem _ _]

def mir (h : GL (Fin m) F) (x : Fin m → F) : GL (Fin (m + 1)) F :=
  ⟨mirM h.val x, mirM (h⁻¹).val (-((h⁻¹).val *ᵥ x)), by
    rw [mirM_mul, mulVec_neg, mulVec_mulVec, Units.mul_inv, one_mulVec, neg_add_cancel, mirM_one], by
    rw [mirM_mul, Units.inv_mul, add_neg_cancel, mirM_one]⟩

@[simp] theorem mir_val (h : GL (Fin m) F) (x : Fin m → F) : (mir h x).val = mirM h.val x := rfl

theorem mir_mul (g h : GL (Fin m) F) (x y : Fin m → F) : mir g x * mir h y = mir (g * h) (g.val *ᵥ y + x) :=
  Units.ext (mirM_mul _ _ _ _)

theorem mir_one : mir (1 : GL (Fin m) F) 0 = 1 := Units.ext mirM_one

theorem mir_eq (h : GL (Fin m) F) (x : Fin m → F) : mir h x = mir 1 x * mir h 0 := by simp [mir_mul]

def cor : GL (Fin m) F →* GL (Fin (m + 1)) F where
  toFun h := mir h 0
  map_one' := mir_one
  map_mul' g h := by simp [mir_mul]

theorem continuous_cor : Continuous (cor : GL (Fin m) F → _) :=
  isEmbedding_coe.continuous_iff.2 (continuous_mirM Units.continuous_val continuous_const)

theorem continuous_col : Continuous fun x : Fin m → F => mir 1 x :=
  isEmbedding_coe.continuous_iff.2 (continuous_mirM continuous_const continuous_id)

theorem lr_mir (h : GL (Fin m) F) (x : Fin m → F) : lr (mir h x) = lr 1 := by
  funext j
  induction j using Fin.lastCases <;> simp [lr, Matrix.one_apply, (Fin.castSucc_ne_last _).symm]

theorem eq_mirabolicMatrix_of_lastRow_eq {p : GL (Fin (m + 1)) F} (hp : lr p = lr 1) :
    p.val = mirM (p.val.submatrix Fin.castSucc Fin.castSucc) fun i => p.val i.castSucc (Fin.last m) := by
  rw [lr_eq_iff] at hp
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [hp, Fin.castSucc_ne_last]

theorem exists_mir {p : GL (Fin (m + 1)) F} (hp : lr p = lr 1) : ∃ h x, p = mir h x := by
  have hq : lr p⁻¹ = lr 1 := by
    have := lr_mul_congr hp p⁻¹
    rw [mul_inv_cancel, one_mul] at this
    exact this.symm
  have h1 : p.val.submatrix Fin.castSucc Fin.castSucc * (p⁻¹).val.submatrix Fin.castSucc Fin.castSucc = 1 := by
    have h2 := p.mul_inv
    rw [eq_mirabolicMatrix_of_lastRow_eq hp, eq_mirabolicMatrix_of_lastRow_eq hq, mirM_mul] at h2
    ext i j
    have := congrFun (congrFun h2 i.castSucc) j.castSucc
    rw [mirM_cc] at this
    rw [this]
    simp [Matrix.one_apply]
  exact ⟨⟨_, _, h1, mul_eq_one_comm.1 h1⟩, _, Units.ext (eq_mirabolicMatrix_of_lastRow_eq hp)⟩

theorem mir_mem_iff {u : GL (Fin m) F} {x : Fin m → F} : mir u x ∈ unipB F (Fin (m + 1)) ↔ u ∈ unipB F (Fin m) := by
  rw [mem_unipB, mem_unipB]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j h => by simpa using h1 i.castSucc j.castSucc (by simpa using h), fun i => by simpa using h2 i.castSucc⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · exact absurd hij (lt_irrefl _)
      · simp
      · exact absurd hij (not_lt.2 (Fin.le_last _))
      · simpa using h1 _ _ (by simpa using hij)
    · induction i using Fin.lastCases <;> simp [h2]

theorem superDiag_mir (u : GL (Fin (m + 1)) F) (x : Fin (m + 1) → F) :
    superDiag (mir u x) = superDiag u + x (Fin.last m) := by
  unfold superDiag
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.sum_univ_castSucc (n := m + 1), mir_val, mirM_cc, mirM_cl, mirM_lc, mirM_ll, Fin.val_castSucc,
    Fin.val_last, Finset.sum_add_distrib]
  have : ∀ i : Fin (m + 1), (m = i.val) ↔ i = Fin.last m := fun i => by simp [Fin.ext_iff, eq_comm]
  simp [this]

theorem superDiag_one' : superDiag (1 : GL (Fin m) F) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_filter] at hj
  exact Matrix.one_apply_ne fun h => by simp [h] at hj

theorem isCompact_blocks {C : Set (GL (Fin (m + 1)) F)} (hC : IsCompact C) :
    IsCompact {h : GL (Fin m) F | ∃ x, mir h x ∈ C} := by
  rw [isEmbedding_coe.isInducing.isCompact_iff]
  have h1 : IsCompact (C ∩ {p | lr p = lr 1}) := hC.inter_right (isClosed_eq continuous_lr continuous_const)
  convert h1.image (f := fun p : GL (Fin (m + 1)) F => p.val.submatrix Fin.castSucc Fin.castSucc)
    (Units.continuous_val.matrix_submatrix _ _) using 1
  ext A
  constructor
  · rintro ⟨h, ⟨x, hx⟩, rfl⟩
    exact ⟨mir h x, ⟨hx, lr_mir h x⟩, by ext i j; simp⟩
  · rintro ⟨p, ⟨hp, hp'⟩, rfl⟩
    obtain ⟨h, x, rfl⟩ := exists_mir hp'
    exact ⟨h, ⟨x, hp⟩, by ext i j; simp⟩

def Eqv (ψ : AddChar F ℂ) {n : ℕ} (W : GL (Fin n) F → ℂ) : Prop :=
  ∀ u ∈ unipB F (Fin n), ∀ g, W (u * g) = ψ (superDiag u) * W g

def Smo {n : ℕ} (W : GL (Fin n) F → ℂ) : Prop :=
  ∃ U : Subgroup (GL (Fin n) F), IsOpen (U : Set (GL (Fin n) F)) ∧ ∀ u ∈ U, ∀ g, W (g * u) = W g

theorem Smo.translate {n : ℕ} {W : GL (Fin n) F → ℂ} (h : Smo W) (g : GL (Fin n) F) : Smo fun x => W (x * g) := by
  obtain ⟨U, hU, hW⟩ := h
  refine ⟨U.comap (MulAut.conj g⁻¹).toMonoidHom, hU.preimage (f := fun u => g⁻¹ * u * g⁻¹⁻¹) (by fun_prop),
    fun u hu x => ?_⟩
  have := hW _ hu (x * g)
  simpa [mul_assoc] using this

theorem Smo.res {W : GL (Fin (m + 1)) F → ℂ} (h : Smo W) : Smo fun x : GL (Fin m) F => W (cor x) := by
  obtain ⟨U, hU, hW⟩ := h
  exact ⟨U.comap cor, hU.preimage continuous_cor, fun u hu x => by simp only [map_mul]; exact hW _ hu _⟩

theorem Eqv.apply_mir {ψ : AddChar F ℂ} {W : GL (Fin (m + 2)) F → ℂ} (h : Eqv ψ W) (g : GL (Fin (m + 1)) F)
    (x : Fin (m + 1) → F) : W (mir g x) = ψ (x (Fin.last m)) * W (cor g) := by
  rw [mir_eq, h _ (mir_mem_iff.2 (one_mem _)), superDiag_mir, superDiag_one', zero_add]
  rfl

theorem Eqv.res {ψ : AddChar F ℂ} {W : GL (Fin (m + 2)) F → ℂ} (h : Eqv ψ W) :
    Eqv ψ fun x : GL (Fin (m + 1)) F => W (cor x) := fun u hu g => by
  simp only [map_mul]
  rw [h (cor u) (mir_mem_iff.2 hu)]
  change ψ (superDiag (mir u 0)) * _ = _
  rw [superDiag_mir, Pi.zero_apply, add_zero]

def Kir (ψ : AddChar F ℂ) (m : ℕ) : Prop :=
  ∀ 𝒲 : Submodule ℂ (GL (Fin (m + 1)) F → ℂ), (∀ W ∈ 𝒲, Eqv ψ W) → (∀ W ∈ 𝒲, Smo W) →
    (∀ W ∈ 𝒲, ∀ p, lr p = lr 1 → (fun g => W (g * p)) ∈ 𝒲) → (∃ W ∈ 𝒲, ∃ p, lr p = lr 1 ∧ W p ≠ 0) →
    ∀ b : GL (Fin (m + 1)) F → ℂ, Eqv ψ b → Smo b →
      (∃ C, IsCompact C ∧ ∀ p, lr p = lr 1 → b p ≠ 0 → ∃ u ∈ unipB F (Fin (m + 1)), u⁻¹ * p ∈ C) →
      ∃ W ∈ 𝒲, ∀ p, lr p = lr 1 → W p = b p

theorem Kir.mem [ProperSpace F] [IsUltrametricDist F] {ψ : AddChar F ℂ} (H : Kir ψ m)
    (𝒱 : Submodule ℂ (GL (Fin (m + 1)) F → ℂ)) (he : ∀ W ∈ 𝒱, Eqv ψ W) (hs : ∀ W ∈ 𝒱, Smo W)
    (ht : ∀ W ∈ 𝒱, ∀ p, (fun g => W (g * p)) ∈ 𝒱)
    (hm : ∀ W ∈ 𝒱, ∀ φ : (Fin (m + 1) → F) → ℂ, IsLocallyConstant φ → (fun h => φ (lr h) * W h) ∈ 𝒱)
    (h0 : ∃ W ∈ 𝒱, ∃ p, W p ≠ 0) {b : GL (Fin (m + 1)) F → ℂ} (hbe : Eqv ψ b) (hbs : Smo b)
    {C : Set (GL (Fin (m + 1)) F)} (hC : IsCompact C)
    (hb : ∀ p, b p ≠ 0 → ∃ u ∈ unipB F (Fin (m + 1)), u⁻¹ * p ∈ C) : b ∈ 𝒱 := by
  classical
  have key : ∃ B : Set (Fin (m + 1) → F), IsClopen B ∧ lr '' C ⊆ B ∧ (fun h => B.indicator 1 (lr h) * b h) ∈ 𝒱 := by
    refine (hC.image continuous_lr).induction_on
      (p := fun S => ∃ B : Set (Fin (m + 1) → F), IsClopen B ∧ S ⊆ B ∧ (fun h => B.indicator 1 (lr h) * b h) ∈ 𝒱)
      ⟨∅, isClopen_empty, le_rfl, by convert 𝒱.zero_mem using 1; funext h; simp⟩
      (fun s t hst ⟨B, h1, h2, h3⟩ => ⟨B, h1, hst.trans h2, h3⟩) ?_ ?_
    · rintro s t ⟨B, h1, h2, h3⟩ ⟨B', h1', h2', h3'⟩
      refine ⟨B ∪ B', h1.union h1', Set.union_subset_union h2 h2', ?_⟩
      convert 𝒱.add_mem h3 (hm _ h3' _ ((LocallyConstant.charFn ℂ h1.compl).isLocallyConstant)) using 1
      funext h
      by_cases hB : lr h ∈ B <;> by_cases hB' : lr h ∈ B' <;> simp [hB, hB', LocallyConstant.coe_charFn]
    · rintro _ ⟨g, -, rfl⟩
      obtain ⟨W₀, hW₀, p₀, hp₀⟩ := h0
      obtain ⟨W, hW, hWb⟩ := H 𝒱 he hs (fun W hW p _ => ht W hW p) ⟨_, ht W₀ hW₀ p₀, 1, rfl, by simpa using hp₀⟩
        (fun x => b (x * g)) (fun u hu x => by simp only [mul_assoc]; exact hbe u hu _) (hbs.translate g)
        ⟨(· * g⁻¹) '' C, hC.image (by fun_prop), fun p _ hp => by
          obtain ⟨u, hu, h⟩ := hb _ hp
          exact ⟨u, hu, _, h, by simp [mul_assoc]⟩⟩
      have hW' := ht W hW g⁻¹
      obtain ⟨U, hU, hWU⟩ := hs _ hW'
      obtain ⟨U', hU', hbU⟩ := hbs
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
        (eventually_mem_orbit g (U ∩ U') (hU.inter hU') ⟨U.one_mem, U'.one_mem⟩)
      have hcl : IsClopen (Metric.ball (lr g) ε) := IsUltrametricDist.isClopen_ball _ _
      refine ⟨Metric.ball (lr g) ε, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hε), _, hcl, le_rfl, ?_⟩
      convert hm _ hW' _ ((LocallyConstant.charFn ℂ hcl).isLocallyConstant) using 2 with h
      change _ = (Metric.ball (lr g) ε).indicator 1 (lr h) * _
      by_cases hh : lr h ∈ Metric.ball (lr g) ε
      · obtain ⟨p, hp, u, hu, rfl⟩ := hball _ hh h rfl
        have h3 : W (p * g * u * g⁻¹) = W (p * g * g⁻¹) := hWU u hu.1 _
        rw [hbU u hu.2, h3, mul_inv_cancel_right, hWb p hp]
      · simp [hh]
  obtain ⟨B, -, hB, hb'⟩ := key
  convert hb' using 2 with h
  by_cases hh : b h = 0
  · simp [hh]
  · obtain ⟨u, hu, hC'⟩ := hb h hh
    have : lr h ∈ B := hB ⟨_, hC', by rw [lr_mul_congr (lr_of_mem (inv_mem hu)), one_mul]⟩
    simp [this]

theorem Kir.succ [ProperSpace F] [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsLocallyConstant ψ) (hψ1 : ψ ≠ 1)
    (H : Kir ψ m) : Kir ψ (m + 1) := by
  rintro 𝒲 he hs ht ⟨W₀, hW₀, p₀, hp₀, h0⟩ b hbe hbs ⟨C, hC, hb⟩
  let res : (GL (Fin (m + 2)) F → ℂ) →ₗ[ℂ] (GL (Fin (m + 1)) F → ℂ) := LinearMap.funLeft ℂ ℂ cor
  have hcol : ∀ W ∈ 𝒲, ∀ x h, W (cor h * mir 1 x) = ψ (lr h ⬝ᵥ x) * W (cor h) := fun W hW x h => by
    change W (mir h 0 * mir 1 x) = _
    rw [mir_mul, (he W hW).apply_mir, mul_one, add_zero]
    rfl
  have hchar : ∀ V ∈ 𝒲.map res, ∀ x, (fun h => ψ (lr h ⬝ᵥ x) * V h) ∈ 𝒲.map res := by
    rintro _ ⟨W, hW, rfl⟩ x
    exact ⟨_, ht W hW _ (lr_mir 1 x), funext fun h => hcol W hW x h⟩
  obtain ⟨W, hW, e⟩ := H.mem (𝒲.map res) (by rintro _ ⟨W, hW, rfl⟩; exact (he W hW).res)
    (by rintro _ ⟨W, hW, rfl⟩; exact (hs W hW).res)
    (by
      rintro _ ⟨W, hW, rfl⟩ p
      exact ⟨_, ht W hW (cor p) (lr_mir p 0), funext fun h => congrArg W (map_mul cor h p).symm⟩)
    (by
      rintro _ ⟨W, hW, rfl⟩ φ hφ
      refine mul_mem_of_char hψ hψ1 lr _ hchar ⟨W, hW, rfl⟩ ?_ hφ
      obtain ⟨U, hU, hWU⟩ := hs W hW
      have : ∀ᶠ x in 𝓝 (0 : Fin (m + 1) → F), mir 1 x ∈ U :=
        continuous_col.continuousAt.eventually_mem (hU.mem_nhds (by simp only [mir_one]; exact U.one_mem))
      filter_upwards [this] with x hx h
      exact (hcol W hW x h).symm.trans (hWU _ hx _))
    (by
      obtain ⟨h, x, rfl⟩ := exists_mir hp₀
      rw [(he W₀ hW₀).apply_mir] at h0
      exact ⟨_, ⟨W₀, hW₀, rfl⟩, h, right_ne_zero_of_mul h0⟩)
    hbe.res hbs.res (isCompact_blocks hC)
    (by
      intro h hh
      obtain ⟨u, hu, hu'⟩ := hb _ (lr_mir h 0) hh
      obtain ⟨v, x, e⟩ := exists_mir (lr_of_mem (inv_mem hu))
      have hv : v ∈ unipB F (Fin (m + 1)) := mir_mem_iff.1 (e ▸ inv_mem hu)
      rw [e, mir_mul] at hu'
      exact ⟨v⁻¹, inv_mem hv, _, by rw [inv_inv]; exact hu'⟩)
  refine ⟨W, hW, fun p hp => ?_⟩
  obtain ⟨h, x, rfl⟩ := exists_mir hp
  rw [(he W hW).apply_mir, hbe.apply_mir]
  exact congrArg (_ * ·) (congrFun e h)

end GlobalTheory.JSW.KirFin
