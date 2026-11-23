import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroMemBoxF
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet

theorem exists_nsmul_sub_mem {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (S : AddSubgroup G) (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ S, x - γ ∈ K)
    (V : Set G) (hV : V ∈ nhds (0 : G)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ b : G, ∃ q : ℕ, 1 ≤ q ∧ q ≤ N ∧ ∃ γ ∈ S, q • b - γ ∈ V := by
  obtain ⟨W, hWo, hW0, hWV⟩ := exists_open_nhds_zero_half hV
  set U : Set G := W ∩ -W with hUdef
  have hUo : IsOpen U := hWo.inter hWo.neg
  have hU0 : (0 : G) ∈ U := ⟨hW0, by simpa using hW0⟩
  have hUV : ∀ v ∈ U, ∀ w ∈ U, v - w ∈ V := by
    intro v hv w hw
    rw [sub_eq_add_neg]
    exact hWV v hv.1 (-w) (by simpa using hw.2)
  obtain ⟨t, ht⟩ := compact_covered_by_add_left_translates (V := U) hK
    (by rw [hUo.interior_eq]; exact ⟨0, hU0⟩)
  refine ⟨t.card + 1, le_add_self, fun b => ?_⟩
  have hx : ∀ m : Fin (t.card + 2), ∃ γ ∈ S, ∃ g ∈ t, g + (((m : ℕ) + 1) • b - γ) ∈ U := by
    intro m
    obtain ⟨γ, hγ, hγK⟩ := hcov (((m : ℕ) + 1) • b)
    have := ht hγK
    simp only [Set.mem_iUnion, Set.mem_preimage] at this
    obtain ⟨g, hg, hgU⟩ := this
    exact ⟨γ, hγ, g, hg, hgU⟩
  choose γ hγ g hg hgU using hx
  obtain ⟨i, j, hij, hg_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun m : Fin (t.card + 2) => (⟨g m, hg m⟩ : t)) (by simp)
  simp only [Subtype.mk.injEq] at hg_eq
  have key : ∀ i j : Fin (t.card + 2), (i : ℕ) < j → g i = g j →
      ∃ q : ℕ, 1 ≤ q ∧ q ≤ t.card + 1 ∧ ∃ γ' ∈ S, q • b - γ' ∈ V := by
    intro i j hlt hgij
    refine ⟨(j : ℕ) - i, by omega, by omega, γ j - γ i, S.sub_mem (hγ j) (hγ i), ?_⟩
    have h := hUV _ (hgU j) _ (hgU i)
    have e : (j : ℕ) + 1 = ((j : ℕ) - i) + ((i : ℕ) + 1) := by omega
    rw [e, add_nsmul, hgij] at h
    convert h using 1
    abel
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact key i j h hg_eq
  · exact key j i h hg_eq.symm

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem boxF_mem_nhds {ε : ℝ} (hε : 0 < ε) : boxF F ε ∈ nhds (0 : AF F) := by
  have hopen : IsOpen ({a : AF F | (∀ w : InfinitePlace F, ‖a.1 w‖ < ε)} ∩
      {a : AF F | a.2 ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F}) := by
    refine IsOpen.inter ?_ ?_
    · simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun w =>
        isOpen_lt (continuous_norm.comp ((continuous_apply w).comp continuous_fst)) continuous_const
    · exact GroundTheory.Global.isOpen_integralFiniteAdeles.preimage continuous_snd
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨fun w => ?_, (zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F) : _)⟩) ?_
  · show ‖(0 : AF F).1 w‖ < ε
    rw [show (0 : AF F).1 w = 0 from rfl, norm_zero]; exact hε
  · rintro a ⟨h1, h2⟩
    exact ⟨fun w => (h1 w).le, h2⟩

theorem repr_inclR (c : E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr (inclR (F := F) (AF F) c) k =
      algebraMap F (AF F) ((Module.finBasis F E).repr c k) := by
  have : inclR (F := F) (AF F) c = (1 : AF F) ⊗ₜ[F] c := rfl
  rw [this, Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem exists_compact_pi (d : ℕ) :
    ∃ K : Set (Fin d → AF F), IsCompact K ∧ ∀ x : Fin d → AF F, ∃ f : Fin d → F,
      (x - fun k => algebraMap F (AF F) (f k)) ∈ K := by
  obtain ⟨C, hC, hx⟩ := GroundTheory.Global.exists_isCompact_forall_exists_sub_mem F
  refine ⟨Set.univ.pi fun _ => C ×ˢ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set _),
    isCompact_univ_pi fun _ => hC.prod (GroundTheory.Global.isCompact_integralFiniteAdeles F), fun x => ?_⟩
  choose f hf using fun k => hx (x k)
  exact ⟨f, fun k _ => hf k⟩

theorem dirichlet (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, 1 ≤ N ∧ ∀ b : AF F ⊗[F] E, ∃ q : ℕ, 1 ≤ q ∧ q ≤ N ∧
    ∃ c : E, (q : AF F ⊗[F] E) * b - inclR (F := F) (AF F) c ∈ boxE F E ε := by
  set d := Module.finrank F E
  let S : AddSubgroup (Fin d → AF F) :=
    (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom (Fin d)).range
  obtain ⟨K, hK, hcov⟩ := exists_compact_pi F d
  have hV : (Set.univ.pi fun _ : Fin d => boxF F ε) ∈ nhds (0 : Fin d → AF F) :=
    set_pi_mem_nhds Set.finite_univ fun _ _ => boxF_mem_nhds F hε
  obtain ⟨N, hN, hb⟩ := exists_nsmul_sub_mem S K hK
    (fun x => by
      obtain ⟨f, hf⟩ := hcov x
      exact ⟨_, ⟨f, rfl⟩, hf⟩) _ hV
  refine ⟨N, hN, fun b => ?_⟩
  set B := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  obtain ⟨q, hq1, hqN, γ, ⟨f, rfl⟩, hmem⟩ := hb (fun k => B.repr b k)
  refine ⟨q, hq1, hqN, (Module.finBasis F E).equivFun.symm f, fun k => ?_⟩
  have hk := hmem k (Set.mem_univ _)
  rw [← nsmul_eq_mul, map_sub, map_nsmul, Finsupp.sub_apply, Finsupp.smul_apply, repr_inclR]
  have hc : (Module.finBasis F E).repr ((Module.finBasis F E).equivFun.symm f) k = f k := by
    have := congrFun ((Module.finBasis F E).equivFun.apply_symm_apply f) k
    rwa [Module.Basis.equivFun_apply] at this
  rw [hc]
  simpa using hk

end GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet

end
