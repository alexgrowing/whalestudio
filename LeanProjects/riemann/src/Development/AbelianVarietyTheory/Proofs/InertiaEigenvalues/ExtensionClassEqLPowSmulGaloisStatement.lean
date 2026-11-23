import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionClassEqLPowSmulGalois
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extensionClass_eq_lPow_smul_galois : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (T Tp : QLat LL) (f : LatHom T.L Tp.L) (g : LatHom Tp.L (unitLat (Gl l) : QLat LL).L), IsSESLat (Qp := ℚ_[l]) f g → ∀ (Pk : Pack a ϖ η H T) (Pp : Pack a ϖ η H Tp) (Pu : Pack a ϖ η H (unitLat (Gl l) : QLat LL)) (F : BKHom Pk.D Pp.D) (G : BKHom Pp.D Pu.D), IsMapOf Pk.R.I Pp.R.I f F.toHom → IsMapOf Pp.R.I Pu.R.I g G.toHom → IsExactTriple F.toHom G.toHom → Function.Injective F.app → ∀ (u : ME Pu.D.toPhiMod) (x : ↥(unitLat (Gl l) : QLat LL).L.T), x.1 = (1 : ↥LL.1) → u.1 ∈ Pu.D.Minv → Pu.D.phi u.1 = u.1 → toW (thetaW a LL) ϖ Pu.D.toPhiMod u = Pu.R.I.ofT x → ∀ (n : ℕ) (x₂ : Vec ↥LL.1 a (Fin Pp.n)), x₂ ∈ Pp.D.Minv → G.app x₂ = (l ^ n) • u.1 → ∀ (v : Tp.V) (c : Gl l → T.V), v ∈ Tp.L.T → g.f v = (1 : ↥LL.1) → (∀ h, Tp.ρ h v - v = f.f (c h)) → ∀ σ ∈ Pk.D.MMl, σ ∈ Pk.D.desc.inv → F.app σ = Pp.D.phi x₂ - Pp.D.xi (red (Pp.D.phi x₂)) → ∀ y ∈ Pk.D.Y, F.app y = Pp.D.phi x₂ - x₂ → Pk.R.ClassOf y ((l : ↥LL.1) ^ n • c) := by
  first | exact @GlobalTheory.ExtClass.main | exact GlobalTheory.ExtClass.main | (intros; apply GlobalTheory.ExtClass.main <;> assumption)
