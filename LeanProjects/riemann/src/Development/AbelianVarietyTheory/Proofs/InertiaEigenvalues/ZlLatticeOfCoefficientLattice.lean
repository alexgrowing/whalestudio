import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section
namespace GlobalTheory

theorem latticeZl_of_latticeO : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (ρ : Representation LL ↥(GK K) V) (L : Lattice (O := O) ρ),
    ∃ LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ), ∀ v, v ∈ LZ.T ↔ v ∈ L.T := by
  intro l _ K LL _ _ O _ _ V _ _ _ _ _ _ _ _ lam n e f h1 h2 h3 ρ L

  have hz : ∀ (z : ℤ_[l]) (v : V), z • v = ((z : ℚ_[l]) : ℚ_[l]) • v := fun z v => by
    rw [← algebraMap_smul ℚ_[l] z v]; rfl

  have hdec : ∀ (a : LL) (t : V), a • t = ∑ i, lam (algebraMap O LL (f i) * a) • (e i • t) := by
    intro a t
    conv_lhs => rw [h3 a]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_assoc, algebraMap_smul]
  let TZ : Submodule ℤ_[l] V :=
    { carrier := (L.T : Set V)
      add_mem' := fun ha hb => L.T.add_mem ha hb
      zero_mem' := L.T.zero_mem
      smul_mem' := by
        intro z v hv
        obtain ⟨o, ho⟩ := h1 z
        show z • v ∈ L.T
        rw [hz, ← algebraMap_smul LL (z : ℚ_[l]) v, ← ho, algebraMap_smul]
        exact L.T.smul_mem o hv }
  have hmem : ∀ v, v ∈ TZ ↔ v ∈ L.T := fun v => Iff.rfl

  have hfg : TZ.FG := by
    obtain ⟨S, hS⟩ := L.fg
    classical
    refine ⟨Finset.image (fun p : Fin n × V => e p.1 • p.2) (Finset.univ ×ˢ S), ?_⟩
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.coe_product, Set.mem_prod, Finset.coe_univ,
        Set.mem_univ, true_and, Finset.mem_coe] at hx
      obtain ⟨⟨i, t⟩, ht, rfl⟩ := hx
      have : t ∈ L.T := hS ▸ Submodule.subset_span ht
      exact L.T.smul_mem (e i) this
    · intro x hx
      have hx' : x ∈ Submodule.span O (S : Set V) := by rw [hS]; exact hx
      obtain ⟨c, -, rfl⟩ := (Submodule.mem_span_finset).1 hx'
      refine Submodule.sum_mem _ fun t ht => ?_
      rw [← algebraMap_smul LL (c t) t, hdec]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨z, hz'⟩ := h2 (f i * c t)
      rw [← map_mul, hz', ← hz]
      refine Submodule.smul_mem _ z (Submodule.subset_span ?_)
      simp only [Finset.coe_image, Set.mem_image, Finset.coe_product, Set.mem_prod, Finset.coe_univ,
        Set.mem_univ, true_and, Finset.mem_coe]
      exact ⟨(i, t), ht, rfl⟩
  have hfin : Module.Finite ℤ_[l] TZ := Module.Finite.iff_fg.mpr hfg
  have htf : Module.IsTorsionFree ℤ_[l] TZ := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro z x h
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    right
    have h' : ((z : ℚ_[l]) : ℚ_[l]) • (x : V) = 0 := by
      rw [← hz]; exact congrArg Subtype.val h
    have hq : (z : ℚ_[l]) ≠ 0 := fun h0 => hz0 (PadicInt.coe_eq_zero.1 h0)
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left hq)
  refine ⟨{ T := TZ, stable := ?_, fg := hfg, free := ?_, span := ?_ }, hmem⟩
  · intro g x hx
    exact L.stable g x hx
  · exact Module.free_of_finite_type_torsion_free'
  · let W : Submodule LL V :=
      { carrier := (Submodule.span ℚ_[l] (TZ : Set V) : Set V)
        add_mem' := fun ha hb => Submodule.add_mem _ ha hb
        zero_mem' := Submodule.zero_mem _
        smul_mem' := by
          intro a x hx
          induction hx using Submodule.span_induction with
          | mem t ht =>
            show a • t ∈ Submodule.span ℚ_[l] (TZ : Set V)
            rw [hdec]
            refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
            exact L.T.smul_mem (e i) ht
          | zero => simp
          | add x y _ _ hx hy =>
            show a • (x + y) ∈ Submodule.span ℚ_[l] (TZ : Set V)
            rw [smul_add]; exact Submodule.add_mem _ hx hy
          | smul q x _ hx =>
            show a • (q • x) ∈ Submodule.span ℚ_[l] (TZ : Set V)
            rw [← algebraMap_smul LL q x, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
            exact Submodule.smul_mem _ q hx }
    have hW : W = ⊤ := by
      rw [eq_top_iff, ← L.span, Submodule.span_le]
      intro t ht
      exact Submodule.subset_span ht
    rw [eq_top_iff]
    intro v _
    have : v ∈ W := hW ▸ Submodule.mem_top
    exact this
end GlobalTheory
