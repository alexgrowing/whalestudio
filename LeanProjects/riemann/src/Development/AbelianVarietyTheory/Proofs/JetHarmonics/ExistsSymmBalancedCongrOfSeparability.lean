import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeIntCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeIntCut
open ReciprocityTheory.ChartRestriction.G.TB (dAct bilinPart)

namespace GlobalTheory

theorem exists_addHom_tensor_int_of_biadditive {M N P : Type} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] (f : M → N → P) (h1 : ∀ m m' n, f (m + m') n = f m n + f m' n)
    (h2 : ∀ m n n', f m (n + n') = f m n + f m n') :
    ∃ g : M ⊗[ℤ] N →+ P, ∀ m n, g (m ⊗ₜ[ℤ] n) = f m n := by
  let F : M →+ N →+ P := AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (f m) (h2 m))
    (fun m m' => by ext n; exact h1 m m' n)
  refine ⟨TensorProduct.liftAddHom F (fun r m n => ?_), fun m n => ?_⟩
  · rw [map_zsmul, map_zsmul]; rfl
  · rw [TensorProduct.liftAddHom_tmul]; rfl

end GlobalTheory
