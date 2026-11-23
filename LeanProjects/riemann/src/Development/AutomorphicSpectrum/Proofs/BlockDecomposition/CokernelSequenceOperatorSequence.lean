import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerOpsComm
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CokernelCoherent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.UV

theorem π_cokOps {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)}
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i : Fin k) (e : ℕ) :
    cokernel.π (T (Fin.last k) e) ≫ cokOps hc i e =
      T i.castSucc (e + 1) ≫ cokernel.π (T (Fin.last k) (e + 1)) := by
  exact cokernel.π_desc _ _ _

theorem app_comp_apply {X : Scheme.{0}} {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C) (U : X.Opens)
    (x : Γ(A, U)) : g.app U (f.app U x) = (f ≫ g).app U x := by
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]

theorem app_apply_eq_of_comp_eq {X : Scheme.{0}} {A B B' C : X.Modules} (f : A ⟶ B) (g : B ⟶ C)
    (f' : A ⟶ B') (g' : B' ⟶ C) (h : f ≫ g = f' ≫ g') (U : X.Opens) (x : Γ(A, U)) :
    g.app U (f.app U x) = g'.app U (f'.app U x) := by
  rw [app_comp_apply, app_comp_apply, h]

theorem cokOpSeq {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (hM : OpSeq (k + 1) M T d) :
    OpSeq k (cokSeq M T) (cokOps hM.comm) d where
  coherent e := by
    haveI := (hM.coherent e).1
    exact isCoherent_cokernel (T (Fin.last k) e) (hM.coherent (e + 1))
  comm := cokOps_comm hM.comm
  gen e he U := by
    haveI := (hM.coherent (e + 1)).1
    haveI := (hM.coherent (e + 1 + 1)).1
    rw [eq_top_iff]
    rintro y -
    obtain ⟨z, rfl⟩ := surjective_cokernel_π_app (T (Fin.last k) (e + 1)) U.2 y
    have hz : z ∈ Submodule.span Γ(X, U) (⋃ i, Set.range ((T i (e + 1)).app U)) := by
      rw [hM.gen (e + 1) (by omega) U]; trivial
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.1 hz
      induction i using Fin.lastCases with
      | last =>
        have h0 : T (Fin.last k) (e + 1) ≫ cokernel.π (T (Fin.last k) (e + 1)) = 0 :=
          cokernel.condition _
        rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, h0,
          Scheme.Modules.Hom.zero_app]
        exact Submodule.zero_mem _
      | cast i =>
        refine Submodule.subset_span (Set.mem_iUnion.2 ⟨i, (cokernel.π (T (Fin.last k) e)).app U x, ?_⟩)
        exact app_apply_eq_of_comp_eq (B := cokSeq M T e) (C := cokSeq M T (e + 1))
          (cokernel.π (T (Fin.last k) e)) (cokOps hM.comm i e) (T i.castSucc (e + 1))
          (cokernel.π (T (Fin.last k) (e + 1))) (π_cokOps hM.comm i e) U.1 x
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
      rw [Scheme.Modules.Hom.app_smul]
      exact Submodule.smul_mem _ _ ha

end GlobalTheory.CompanionTheory.GE.UV
