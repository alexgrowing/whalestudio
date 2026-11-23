import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalPullSemilinearOfIsTwInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.SemilinearPullbackEval

open GlobalTheory.PolFan.OrbMark

theorem eval_pull_semilinear_of_isTwG : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (w0 : O), CMOrd O bar → ∀ (φ : InvFun O), IsTwG w0 φ →
    ∀ {X Y : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup Y] [Module O Y] [Module.Finite O Y]
      (τ : O ≃+* O), τ w0 = w0 → ∀ (f : X →+ Y), Function.Surjective f → (∀ (a : O) (x : X), f (a • x) = τ a • f x) →
      ∀ B : Y → Y → ℝ, φ.eval X (fun x y => B (f x) (f y)) = φ.eval Y B := by
  intro O _ _ _ _ bar w0 _ φ hφ X Y _ _ _ _ _ _ τ hτ f hf hsl B
  obtain ⟨n, πX, hπX⟩ := Module.Finite.exists_fin' O X
  let g : (Fin n → O) →ₗ[O] Y :=
    { toFun := fun a => f (πX (twv τ.symm a))
      map_add' := fun a b => by
        show f (πX (twv τ.symm (a + b))) = f (πX (twv τ.symm a)) + f (πX (twv τ.symm b))
        have hadd : twv τ.symm (a + b) = twv τ.symm a + twv τ.symm b := by
          funext i
          simp [twv_apply]
        rw [hadd, map_add, map_add]
      map_smul' := fun c a => by
        show f (πX (twv τ.symm (c • a))) = c • f (πX (twv τ.symm a))
        rw [twv_smul, map_smul, hsl, RingEquiv.apply_symm_apply] }
  have hg_apply : ∀ a, g a = f (πX (twv τ.symm a)) := fun _ => rfl
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨a, rfl⟩ := hπX x
    exact ⟨twv τ a, by rw [hg_apply, twv_symm_twv]⟩
  have key : ∀ a : Fin n → O, g (fun i => τ (a i)) = f (πX a) := by
    intro a
    rw [hg_apply]
    congr 2
    funext i
    simp [twv_apply]
  rw [φ.eval_eq hπX, φ.eval_eq hg, ← hφ τ hτ n (fun a b => B (g a) (g b))]
  congr 1
  funext a b
  show B (f (πX a)) (f (πX b)) = B (g (fun i => τ (a i))) (g (fun i => τ (b i)))
  rw [key a, key b]

end GlobalTheory.CompanionTheory.Ar.Fan.SemilinearPullbackEval
