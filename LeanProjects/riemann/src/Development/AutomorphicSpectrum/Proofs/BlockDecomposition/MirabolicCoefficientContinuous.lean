import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem continuous_coef : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), IsSmooth T → ∀ (v : V) (v' : V'), Continuous (coef T B v v') := by
  intro k _ _ _ _ n V V' _ _ _ _ T B hT v v'
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hcont : Continuous fun y : Fin n → k =>
      GlobalTheory.CompanionTheory.MirFourier.unipIn k n (Multiplicative.ofAdd (y - x)) :=
    (GlobalTheory.CompanionTheory.MirFourier.continuous_unipIn n).comp
      (continuous_ofAdd.comp (continuous_id.sub continuous_const))
  have hopen : IsOpen {y : Fin n → k |
      T (GlobalTheory.CompanionTheory.MirFourier.unipIn k n (Multiplicative.ofAdd (y - x))) v = v} :=
    (hT v).preimage hcont
  have hx : x ∈ {y : Fin n → k |
      T (GlobalTheory.CompanionTheory.MirFourier.unipIn k n (Multiplicative.ofAdd (y - x))) v = v} := by
    simp
  filter_upwards [hopen.mem_nhds hx] with y hy
  have hy' : T (GlobalTheory.CompanionTheory.MirFourier.unipIn k n (Multiplicative.ofAdd (y - x))) v = v := hy
  have hsplit : GlobalTheory.CompanionTheory.MirPair.uM n y =
      GlobalTheory.CompanionTheory.MirPair.uM n x * GlobalTheory.CompanionTheory.MirFourier.unipIn k n (Multiplicative.ofAdd (y - x)) := by
    unfold GlobalTheory.CompanionTheory.MirPair.uM
    rw [← map_mul, ← ofAdd_add, add_sub_cancel]
  unfold GlobalTheory.CompanionTheory.MirPair.coef
  rw [hsplit, map_mul, Module.End.mul_apply, hy']

end GlobalTheory.CompanionTheory.MirPair
