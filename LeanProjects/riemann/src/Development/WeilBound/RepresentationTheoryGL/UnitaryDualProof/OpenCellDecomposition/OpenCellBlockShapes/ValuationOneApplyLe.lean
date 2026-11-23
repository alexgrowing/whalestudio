import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellBlockShapes.VolRelIndex
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellBlockShapes.IsBlockShapeOneAdd
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.BlockIndexOfWeylShuffle

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier ValuativeRel GroundTheory.Automorphic.GLnLocal
open GlobalTheory.SplitWeil PositivityTheory.RgUd.CellA

noncomputable section

namespace PositivityTheory.RgUd.CellB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem valuation_blockE_le {r m : ℕ} {γ : ValueGroupWithZero k} {Y : Fin m × Fin r → k}
    (hY : Y ∈ box (Fin m × Fin r) γ) (i j : Fin (r + m)) : valuation k (blockE r Y i j) ≤ γ := by
  unfold blockE
  split_ifs
  · exact hY _
  · simp

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem valuation_one_apply_le {N : ℕ} (i j : Fin N) : valuation k ((1 : Matrix (Fin N) (Fin N) k) i j) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem mem_congr_iff_box {r m : ℕ} (n : ℕ) {u : GL (Fin (r + m)) k}
    (hu : IsBlockShape (u : Matrix (Fin (r + m)) (Fin (r + m)) k)) :
    u ∈ congruenceSubgroup k (r + m) n ↔
      blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k) ∈
        box (Fin m × Fin r) (valuation k (uniformizer k : k) ^ n) := by
  have hE := eq_one_add_blockE hu
  have hγ : valuation k (uniformizer k : k) ^ n ≤ 1 :=
    pow_le_one₀ zero_le' (GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_lt_one k).le
  rw [GroundTheory.Automorphic.GLnLocal.mem_congruenceSubgroup_iff, mem_box]
  constructor
  · rintro ⟨-, h⟩ ⟨i, j⟩
    simpa only [blockY, one_rowI_colI, sub_zero] using h (rowI i) (colI j)
  · intro hY
    have hY' : blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k) ∈
        box (Fin m × Fin r) (valuation k (uniformizer k : k) ^ n) := mem_box.2 hY
    have hent : ∀ i j, valuation k ((u : Matrix (Fin (r + m)) (Fin (r + m)) k) i j -
        (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) i j) ≤ valuation k (uniformizer k : k) ^ n := by
      intro i j
      rw [hE, Matrix.add_apply, add_sub_cancel_left]
      exact valuation_blockE_le hY' i j
    refine ⟨(GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff k _).2 ⟨fun i j => ?_, fun i j => ?_⟩, hent⟩
    · show valuation k _ ≤ 1
      have e : (u : Matrix (Fin (r + m)) (Fin (r + m)) k) i j = (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) i j +
          ((u : Matrix (Fin (r + m)) (Fin (r + m)) k) i j - (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) i j) := by
        ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le (valuation_one_apply_le i j) ((hent i j).trans hγ))
    · have hinv : ((u⁻¹ : GL (Fin (r + m)) k) : Matrix (Fin (r + m)) (Fin (r + m)) k) =
          1 - blockE r (blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k)) := by
        apply Units.inv_eq_of_mul_eq_one_right
        calc (u : Matrix (Fin (r + m)) (Fin (r + m)) k) *
              (1 - blockE r (blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k)))
            = (1 + blockE r (blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k))) *
              (1 - blockE r (blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k))) := by rw [← hE]
          _ = 1 := by
            simp only [add_mul, mul_sub, one_mul, mul_one, blockE_mul]
            abel
      show valuation k _ ≤ 1
      rw [hinv, Matrix.sub_apply]
      exact (Valuation.map_sub _ _ _).trans
        (max_le (valuation_one_apply_le i j) ((valuation_blockE_le hY' i j).trans hγ))

abbrev congrL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r m n : ℕ) :
    Subgroup (GL (Fin (r + m)) k) :=
  unipU k (dd r m) (hdd r m) ⊓ (congruenceSubgroup k (r + m) n).comap (MulAut.conj (pm k (wOpen (dd r m) (hdd r m)))).toMonoidHom

theorem mem_congrL {r m n : ℕ} {u : GL (Fin (r + m)) k} :
    u ∈ congrL k r m n ↔ u ∈ unipU k (dd r m) (hdd r m) ∧ u ∈ congruenceSubgroup k (r + m) n := by
  rw [congrL, Subgroup.mem_inf, Subgroup.mem_comap]
  refine and_congr_right fun _ => ?_
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, pm]
  constructor
  · intro h
    have := GroundTheory.Automorphic.Parabolic.permGL_conj_mem_congruenceSubgroup
      (w := (wOpen (dd r m) (hdd r m))⁻¹) h
    simpa [map_inv, mul_assoc] using this
  · exact GroundTheory.Automorphic.Parabolic.permGL_conj_mem_congruenceSubgroup

set_option maxHeartbeats 1000000 in

theorem vol_conj_aDiag (ψ : AddChar k Circle) {r m : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (dd r m a)) W) (J : openFns (dd r m) (hdd r m) ρ →ₗ[ℂ] W)
    (vol : Subgroup (GL (Fin (r + m)) k) → ℝ)
    (hU : ∀ (u : GL (Fin (r + m)) k) (hu : u ∈ unipU k (dd r m) (hdd r m)) (hb : u ∈ unipB k (Fin (r + m)))
      (f f' : openFns (dd r m) (hdd r m) ρ), (f' : IndSp (stdBlocks (dd r m) (hdd r m)) ρ) = parInd (stdBlocks (dd r m) (hdd r m)) ρ u f →
        J f' = (whitChar ψ (r + m) ⟨u, hb⟩ : ℂ) • J f)
    (hV : ∀ L₀ : Subgroup (GL (Fin (r + m)) k), L₀ ≤ unipU k (dd r m) (hdd r m) → IsCompact (L₀ : Set (GL (Fin (r + m)) k)) →
      (∃ O : Set (GL (Fin (r + m)) k), IsOpen O ∧ O ∩ (unipU k (dd r m) (hdd r m) : Set (GL (Fin (r + m)) k)) = L₀) →
      0 < vol L₀ ∧ ∀ (f : openFns (dd r m) (hdd r m) ρ) (v : W),
        (∀ (u : GL (Fin (r + m)) k) (hb : u ∈ unipB k (Fin (r + m))), u ∈ L₀ →
          f.1.1.1 (pm k (wOpen (dd r m) (hdd r m)) * u) = (whitChar ψ (r + m) ⟨u, hb⟩ : ℂ) • v) →
        (∀ u ∈ unipU k (dd r m) (hdd r m), u ∉ L₀ → f.1.1.1 (pm k (wOpen (dd r m) (hdd r m)) * u) = 0) → J f = (vol L₀ : ℂ) • v)
    (hU2 : ∀ u : GL (Fin (r + m)) k, u ∈ unipU k (dd r m) (hdd r m) ↔
      u ∈ unipB k (Fin (r + m)) ∧ IsBlockShape (u : Matrix (Fin (r + m)) (Fin (r + m)) k))
    (n : ℕ) (z : kˣ) (hz : valuation k (z : k) ≤ 1)
    (hθ : ∀ (u : GL (Fin (r + m)) k) (hb : u ∈ unipB k (Fin (r + m))), u ∈ congrL k r m n →
      whitChar ψ (r + m) ⟨u, hb⟩ = 1)
    (g : openFns (dd r m) (hdd r m) ρ) (v : W) (hv : v ≠ 0)
    (hg1 : ∀ u ∈ (congrL k r m n).map (MulAut.conj (aDiag k (r + m) m z)).toMonoidHom,
      g.1.1.1 (pm k (wOpen (dd r m) (hdd r m)) * u) = v)
    (hg0 : ∀ u ∈ unipU k (dd r m) (hdd r m), u ∉ (congrL k r m n).map (MulAut.conj (aDiag k (r + m) m z)).toMonoidHom →
      g.1.1.1 (pm k (wOpen (dd r m) (hdd r m)) * u) = 0) :
    vol ((congrL k r m n).map (MulAut.conj (aDiag k (r + m) m z)).toMonoidHom) =
      nabs k z ^ (m * r) * vol (congrL k r m n) := by
  set U := unipU k (dd r m) (hdd r m) with hUdef
  set a := aDiag k (r + m) m z with hadef
  set L₀ := congrL k r m n with hL₀def
  set C := congruenceSubgroup k (r + m) n with hCdef
  have hL₀U : L₀ ≤ U := inf_le_left
  have hmemL₀ : ∀ u, u ∈ L₀ ↔ u ∈ U ∧ u ∈ C := fun u => mem_congrL
  have haU : ∀ u ∈ U, a * u * a⁻¹ ∈ U := fun u hu => aDiag_conj_mem_unipU k z hu
  have haU' : ∀ u ∈ U, a⁻¹ * u * a ∈ U := by
    intro u hu
    have := aDiag_conj_mem_unipU k z⁻¹ hu
    rwa [← aDiag_inv, inv_inv] at this
  have hφ : ∀ (u : GL (Fin (r + m)) k) (hu : u ∈ U),
      Multiplicative.toAdd (blockEquiv U hU2 ⟨u, hu⟩) = blockY (u : Matrix (Fin (r + m)) (Fin (r + m)) k) := by
    intro u hu
    funext p
    exact blockEquiv_apply U hU2 ⟨u, hu⟩ p.1 p.2
  have hc0 : (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) ≠ 0 :=
    GroundTheory.Automorphic.GLnLocal.uniformizer_ne_zero k
  set c : kˣ := (Units.mk0 _ hc0) ^ n with hcdef
  have hvc : valuation k (c : k) = valuation k (uniformizer k : k) ^ n := by
    simp [c, map_pow]
  have hUclosed : IsClosed (U : Set (GL (Fin (r + m)) k)) := by
    have e : (U : Set (GL (Fin (r + m)) k)) = {u : GL (Fin (r + m)) k | ∀ i j : Fin (r + m),
        ¬ ((i : ℕ) < m ∧ m ≤ (j : ℕ)) →
        (u : Matrix (Fin (r + m)) (Fin (r + m)) k) i j = (1 : Matrix (Fin (r + m)) (Fin (r + m)) k) i j} := by
      ext u
      simp only [SetLike.mem_coe, Set.mem_setOf_eq]
      rw [hU2]
      constructor
      · rintro ⟨-, hs⟩ i j hij
        by_contra hne
        exact hij (hs i j hne)
      · intro H
        refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, fun i j hne => ?_⟩
        · rw [H i j (fun h => absurd (lt_of_lt_of_le h.1 h.2) (not_lt.mpr (Fin.le_def.mp hji.le)))]
          exact Matrix.one_apply_ne hji.ne'
        · rw [H i i (fun h => absurd (lt_of_lt_of_le h.1 h.2) (lt_irrefl _))]
          exact Matrix.one_apply_eq i
        · by_contra hc
          exact hne (H i j hc)
    rw [e]
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
  have hL₀set : (L₀ : Set (GL (Fin (r + m)) k)) = (C : Set (GL (Fin (r + m)) k)) ∩ U := by
    ext u
    simp only [SetLike.mem_coe, Set.mem_inter_iff, hmemL₀]
    tauto
  have hcomp₀ : IsCompact (L₀ : Set (GL (Fin (r + m)) k)) := by
    rw [hL₀set]
    exact (GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k (r + m) n).inter_right hUclosed
  have hopen₀ : ∃ O : Set (GL (Fin (r + m)) k), IsOpen O ∧ O ∩ (U : Set (GL (Fin (r + m)) k)) = L₀ :=
    ⟨C, GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k (r + m) n, hL₀set.symm⟩
  have hcont : Continuous fun u : GL (Fin (r + m)) k => a * u * a⁻¹ := by fun_prop
  have hcomp : IsCompact ((L₀.map (MulAut.conj a).toMonoidHom : Subgroup _) : Set (GL (Fin (r + m)) k)) := by
    rw [Subgroup.coe_map]
    exact hcomp₀.image hcont
  have hopen : ∃ O : Set (GL (Fin (r + m)) k), IsOpen O ∧
      O ∩ (U : Set (GL (Fin (r + m)) k)) = (L₀.map (MulAut.conj a).toMonoidHom : Subgroup _) := by
    refine ⟨(fun u => a⁻¹ * u * a) ⁻¹' (C : Set (GL (Fin (r + m)) k)),
      (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k (r + m) n).preimage (by fun_prop), ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_map_equiv,
      MulAut.conj_symm_apply, hmemL₀]
    constructor
    · rintro ⟨hC, hU⟩
      exact ⟨haU' x hU, hC⟩
    · rintro ⟨hU, hC⟩
      refine ⟨hC, ?_⟩
      have := haU _ hU
      simpa [mul_assoc] using this
  have hS : ∀ (u : GL (Fin (r + m)) k) (hu : u ∈ U),
      u ∈ L₀ ↔ Multiplicative.toAdd (blockEquiv U hU2 ⟨u, hu⟩) ∈ box (Fin m × Fin r) (valuation k (c : k)) := by
    intro u hu
    rw [hφ, hvc, hmemL₀, ← mem_congr_iff_box n ((hU2 u).1 hu).2]
    simp [hu, C]
  have hscale : ∀ (u : GL (Fin (r + m)) k) (hu : u ∈ U),
      Multiplicative.toAdd (blockEquiv U hU2 ⟨a * u * a⁻¹, haU u hu⟩) =
        z • Multiplicative.toAdd (blockEquiv U hU2 ⟨u, hu⟩) := by
    intro u hu
    rw [hφ, hφ]
    funext p
    simp only [blockY, Pi.smul_apply, Units.smul_def, smul_eq_mul, a, aDiag_conj_apply]
    have h1 : ((rowI (r := r) p.1 : Fin (r + m)) : ℕ) < m := p.1.2
    have h2 : ¬ ((colI (m := m) p.2 : Fin (r + m)) : ℕ) < m := by simp [colI]
    rw [if_pos h1, if_neg h2, mul_one]
  obtain ⟨hLL₀, hidx⟩ := relIndex_conj (Fin m × Fin r) U (blockEquiv U hU2) a z haU hscale L₀ hL₀U
    (box (Fin m × Fin r) (valuation k (c : k))) hS (isCompact_box _ c) (isOpen_box _ c)
    (fun x hx => smul_mem_box z hz hx)
  have hvol := vol_relIndex ψ (dd r m) (hdd r m) ρ J vol (fun u hu hb f f' h => hU u hu hb f f' h) hV hLL₀ hL₀U
    hcomp₀ hopen₀ hcomp hopen hθ g v hv hg1 hg0
  rw [hidx] at hvol
  have hpos := GlobalTheory.SplitWeil.nabs_pos k z
  have hcard : Fintype.card (Fin m × Fin r) = m * r := by simp
  rw [hcard] at hvol
  rw [hvol, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hpos.ne', one_pow, one_mul]

end PositivityTheory.RgUd.CellB
