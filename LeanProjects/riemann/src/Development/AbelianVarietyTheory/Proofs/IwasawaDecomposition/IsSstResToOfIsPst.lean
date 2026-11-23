import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.PstSst

variable {l : ℕ} [Fact l.Prime]

theorem apply_mem_kur (g : GQ l) (c : ↥(MaximalUnramifiedExtension l)) : g (c : Om l) ∈ MaximalUnramifiedExtension l := by
  have h : (MaximalUnramifiedExtension l).map (g : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    conv_lhs => rw [MaximalUnramifiedExtension, IntermediateField.adjoin_map]
    refine IntermediateField.adjoin.mono _ _ _ ?_
    rintro _ ⟨x, ⟨m, h0, hm, hx⟩, rfl⟩
    exact ⟨m, h0, hm, by rw [← map_pow, hx, map_one]⟩
  exact h ⟨c, c.2, rfl⟩

theorem mem_of_fixed (K : FinExt l) (x : Om l) (hx : ∀ g ∈ GK K, g x = x) : x ∈ K.1 := by
  have : IsGalois ℚ_[l] (Om l) := {}
  rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
  exact hx

def incl (K : FinExt l) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) :=
  IntermediateField.inclusion (inf_le_right : K.1 ⊓ MaximalUnramifiedExtension l ≤ MaximalUnramifiedExtension l)

section

variable (P : LocPrime l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
  (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem mulV_smul (q : ℚ_[l]) (c : ↥(MaximalUnramifiedExtension l)) (x : V ⊗[ℚ_[l]] Bst P) :
    mulV P LL V (q • c) x = q • mulV P LL V c x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [mulV_tmul, mulV_tmul, ← tmul_smul, ← smul_mul_assoc]
    congr 2
    rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, smul_C]
    congr 1
    exact map_smul (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B) q c
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

def comb (K' : FinExt l) {n : ℕ} (b : Fin n → V ⊗[ℚ_[l]] Bst P) :
    (Fin n → ↥(K0 K')) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P where
  toFun c := ∑ i, mulV P LL V (incl K' (c i)) (b i)
  map_add' c d := by simp [Finset.sum_add_distrib]
  map_smul' q c := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mulV_smul]
    exact congrArg (fun a => mulV P LL V a (b i)) (map_smul (incl K').toLinearMap q (c i))

variable {LL V} {K : FinExt l} (ρ : Representation LL ↥(GK K) V)

theorem coe_sum {n : ℕ} (b : Fin n → DpstUr P ρ) (c : Fin n → ↥(MaximalUnramifiedExtension l)) :
    (((toUr P ρ).symm (∑ i, c i • b i) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
      ∑ i, mulV P LL V (c i) (((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) := by
  rw [map_sum, Submodule.coe_sum]
  rfl

theorem finrank_dst {n : ℕ} (b : Basis (Fin n) ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)) (K' : FinExt l) (h : K.1 ≤ K'.1)
    (hb : ∀ i (g : ↥(GK K)), (g : GQ l) ∈ GK K' →
      stRep P ρ g ((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) = ((toUr P ρ).symm (b i) : ↥(Dpst P ρ))) :
    finrank ℚ_[l] ↥(Dst P (resTo ρ h)) = n * finrank ℚ_[l] ↥(K0 K') := by
  have := K'.2
  have hle : K0 K' ≤ K'.1 := inf_le_left
  have : FiniteDimensional ℚ_[l] ↥(K0 K') :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  set β : Fin n → V ⊗[ℚ_[l]] Bst P := fun i => ((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) with hβ
  have huniq : ∀ c d : Fin n → ↥(MaximalUnramifiedExtension l),
      ∑ i, mulV P LL V (c i) (β i) = ∑ i, mulV P LL V (d i) (β i) → c = d := by
    intro c d hcd
    rw [← coe_sum, ← coe_sum] at hcd
    have h1 := (toUr P ρ).symm.injective (Subtype.ext hcd)
    rw [← b.equivFun_symm_apply, ← b.equivFun_symm_apply] at h1
    exact b.equivFun.symm.injective h1
  have hact : ∀ (g : ↥(GK K)), (g : GQ l) ∈ GK K' → ∀ c : Fin n → ↥(MaximalUnramifiedExtension l),
      stRep P ρ g (∑ i, mulV P LL V (c i) (β i)) =
        ∑ i, mulV P LL V ⟨_, apply_mem_kur (g : GQ l) (c i)⟩ (β i) := by
    intro g hg c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← End.mul_apply, stRep_mulV P ρ g (c i) ⟨_, apply_mem_kur (g : GQ l) (c i)⟩ rfl, End.mul_apply,
      hb i g hg]
  have hinj : Function.Injective (comb P LL V K' β) := fun c d hcd =>
    funext fun i => (incl K').injective (congrFun (huniq _ _ hcd) i)
  have hrange : LinearMap.range (comb P LL V K' β) = (Dst P (resTo ρ h)).restrictScalars ℚ_[l] := by
    ext x
    rw [Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨c, rfl⟩
      refine (mem_Dst_resTo P ρ h).mpr fun g hg => ?_
      refine (hact g hg fun i => incl K' (c i)).trans (Finset.sum_congr rfl fun i _ => ?_)
      congr 2
      exact Subtype.ext (mem_GK.mp hg _ (c i).2.1)
    · intro hx
      let c : Fin n → ↥(MaximalUnramifiedExtension l) := b.repr (toUr P ρ ⟨x, Dst_resTo_le P ρ h hx⟩)
      have hc : ∑ i, mulV P LL V (c i) (β i) = x := by
        rw [← coe_sum, b.sum_repr, AddEquiv.symm_apply_apply]
      have hK : ∀ i, (c i : Om l) ∈ K'.1 := fun i => mem_of_fixed K' _ fun g hg => by
        have h1 := hact ⟨g, GK_le h hg⟩ hg c
        rw [hc, (mem_Dst_resTo P ρ h).mp hx ⟨g, GK_le h hg⟩ hg, ← hc] at h1
        exact (congrArg Subtype.val (congrFun (huniq _ _ h1) i)).symm
      exact ⟨fun i => ⟨c i, hK i, (c i).2⟩, hc⟩
  have h1 := LinearMap.finrank_range_of_inj hinj
  rw [hrange, finrank_pi_fintype] at h1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  exact h1

end

theorem isSst_resTo_of_isPst (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : Type)
    [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (hV : IsPst P ρ) :
    ∃ (K₁ : FinExt l), K.1 ≤ K₁.1 ∧
      ∀ (K' : FinExt l) (h : K.1 ≤ K'.1), K₁.1 ≤ K'.1 → IsSst P (resTo ρ h) := by
  have := LL.2
  have : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  obtain ⟨_, hdim⟩ := (isPst_iff P ρ).mp hV
  let b := finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)
  choose F hF using fun i => (mem_Dpst P ρ).mp ((toUr P ρ).symm (b i)).2
  have := fun i => (F i).2
  refine ⟨supExt K ⟨⨆ i, (F i).1, inferInstance⟩, le_sup_left, fun K' h h₁ => ?_⟩
  have h1 := finrank_dst P ρ b K' h fun i g hg =>
    hF i g (GK_le (K := F i) (((le_iSup (fun i => (F i).1) i).trans le_sup_right).trans h₁) hg)
  rw [hdim, ← finrank_mul_finrank ℚ_[l] ↥LL.1 V, ← finrank_mul_finrank ℚ_[l] ↥LL.1, mul_assoc] at h1
  rw [IsSst, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left finrank_pos h1

end GlobalTheory.PstSst
