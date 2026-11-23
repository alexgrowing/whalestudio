import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.Pst

theorem semilinear_coord_fixed {F D ι : Type*} [Field F] [AddCommGroup D] [Module F D] [Fintype ι]
    {b : ι → D} (hb : LinearIndependent F b) (σ : F → F) (T : D →+ D)
    (hT : ∀ c x, T (c • x) = σ c • T x) (hTb : ∀ i, T (b i) = b i) (c : ι → F)
    (h : T (∑ i, c i • b i) = ∑ i, c i • b i) (i : ι) : σ (c i) = c i := by
  rw [map_sum] at h
  simp only [hT, hTb] at h
  exact Fintype.linearIndependent_iffₛ.mp hb _ _ h i

variable {l : ℕ} [Fact l.Prime]

theorem galois_mem_Kur (g : GQ l) (c : ↥(MaximalUnramifiedExtension l)) : g (c : Om l) ∈ MaximalUnramifiedExtension l := by
  obtain ⟨c, hc⟩ := c
  change g c ∈ MaximalUnramifiedExtension l
  induction hc using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, h0, hm, hx⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨m, h0, hm, by rw [← map_pow, hx, map_one]⟩
  | algebraMap x => rw [g.commutes]; exact (MaximalUnramifiedExtension l).algebraMap_mem x
  | add x y _ _ hx hy => rw [map_add]; exact (MaximalUnramifiedExtension l).add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact (MaximalUnramifiedExtension l).inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact (MaximalUnramifiedExtension l).mul_mem hx hy

theorem mem_of_GK_fixed {K : FinExt l} {x : Om l} (hx : ∀ g : ↥(GK K), (g : GQ l) x = x) : x ∈ K.1 := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
  exact fun g hg => hx ⟨g, hg⟩

theorem mulV_padic_smul (P : LocPrime l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (q : ℚ_[l]) (c : ↥(MaximalUnramifiedExtension l)) (x : V ⊗[ℚ_[l]] Bst P) :
    mulV P LL V (q • c) x = q • mulV P LL V c x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [mulV_tmul, mulV_tmul, ← tmul_smul, Algebra.smul_def q c, map_mul,
      ← IsScalarTower.algebraMap_apply, mul_assoc, ← Algebra.smul_def]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

theorem mem_closure_mulV_of_finrank_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsPst P ρ → ∀ S : Submodule ↥LL.1 (V ⊗[ℚ_[l]] Bst P), S ≤ Dst P ρ → (∀ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 → ∀ x ∈ S, mulV P ↥LL.1 V c x ∈ S) → finrank ↥LL.1 ↥S = finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V → ∀ x ∈ Dpst P ρ, x ∈ AddSubgroup.closure {y | ∃ (c : ↥(MaximalUnramifiedExtension l)) (s : V ⊗[ℚ_[l]] Bst P), s ∈ S ∧ y = mulV P ↥LL.1 V c s} := by
  intro l _ P K LL V _ _ _ _ _ ρ hV S hS _ hrk x hx
  haveI := LL.2
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  obtain ⟨hfin, hd⟩ := (isPst_iff P ρ).mp hV
  let val : DpstUr P ρ →+ V ⊗[ℚ_[l]] Bst P :=
    (Dpst P ρ).subtype.toAddMonoidHom.comp (toUr P ρ).symm.toAddMonoidHom
  have hSD : S ≤ Dpst P ρ := fun s hs => (mem_Dpst P ρ).mpr ⟨K, fun g _ => (mem_Dst P ρ).mp (hS hs) g⟩
  obtain ⟨b, hbS, hsp, hli⟩ := exists_linearIndependent ↥(MaximalUnramifiedExtension l) {y : DpstUr P ρ | val y ∈ S}
  haveI : Finite ↥b := hli.finite
  letI : Fintype ↥b := Fintype.ofFinite _
  have hspan : ∀ y : DpstUr P ρ, y ∈ Submodule.span ↥(MaximalUnramifiedExtension l) b → ∃ c : ↥b → ↥(MaximalUnramifiedExtension l),
      ∑ i, c i • (i : DpstUr P ρ) = y := fun y hy => by
    rw [← Submodule.mem_span_range_iff_exists_fun, Subtype.range_coe]; exact hy
  let inc : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) := IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)
  let f : (↥b → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P :=
    { toFun := fun c => ∑ i, mulV P ↥LL.1 V (inc (c i)) (val i)
      map_add' := fun c c' => by simp [Finset.sum_add_distrib]
      map_smul' := fun q c => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => mulV_padic_smul P _ V q (inc (c i)) (val i) }
  have hle : S.restrictScalars ℚ_[l] ≤ LinearMap.range f := by
    intro s hs
    obtain ⟨c, hc⟩ := hspan (toUr P ρ ⟨s, hSD hs⟩) (hsp ▸ Submodule.subset_span hs)
    have hfix : ∀ i, (c i : Om l) ∈ K.1 := fun i => mem_of_GK_fixed fun g => by
      have := semilinear_coord_fixed hli (fun a => ⟨_, galois_mem_Kur g a⟩)
        (actD P ρ g).toAddMonoidHom
        (fun a y => LinearMap.congr_fun (actD_mulD P ρ g a _ rfl) y)
        (fun j => Subtype.ext ((mem_Dst P ρ).mp (hS (hbS j.2)) g)) c
        (by rw [hc]; exact Subtype.ext ((mem_Dst P ρ).mp (hS hs) g)) i
      exact congrArg Subtype.val this
    refine ⟨fun i => ⟨c i, hfix i, (c i).2⟩, ?_⟩
    have := congrArg val hc
    rw [map_sum] at this
    exact this
  have h1 : finrank ℚ_[l] ↥(S.restrictScalars ℚ_[l]) ≤ Fintype.card ↥b * finrank ℚ_[l] ↥(K0 K) := by
    refine (Submodule.finrank_mono hle).trans ((LinearMap.finrank_range_le f).trans ?_)
    simp [Module.finrank_pi_fintype]
  have h2 : finrank ℚ_[l] ↥(S.restrictScalars ℚ_[l]) = finrank ℚ_[l] V * finrank ℚ_[l] ↥(K0 K) := by
    change finrank ℚ_[l] ↥S = _
    rw [← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 ↥S, hrk, ← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 V]
    ring
  have h3 : finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ Fintype.card ↥b := by
    rw [hd]
    exact Nat.le_of_mul_le_mul_right (h2 ▸ h1) Module.finrank_pos
  have htop := hli.span_eq_top_of_card_eq_finrank' (le_antisymm hli.fintype_card_le_finrank h3)
  rw [Subtype.range_coe] at htop
  obtain ⟨c, hc⟩ := hspan (toUr P ρ ⟨x, hx⟩) (htop ▸ Submodule.mem_top)
  have h4 := congrArg val hc
  rw [map_sum] at h4
  rw [← show _ = x from h4]
  exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨c i, val i, hbS i.2, rfl⟩

end GlobalTheory.Pst
