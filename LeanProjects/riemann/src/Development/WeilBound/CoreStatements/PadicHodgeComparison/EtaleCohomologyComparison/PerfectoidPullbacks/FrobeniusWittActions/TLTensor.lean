import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingSmulLeftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingSmulDualStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingGaloisEquivariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingFrobeniusCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingLTensorNaturalityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TracePairingBasisEvalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEvalFixedOfFixedStatement

set_option backward.isDefEq.respectTransparency false

noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.Pb.Psi

variable {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A]
  {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L]
  (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w))

theorem T_smul (f : Module.Dual K₀ (K₀ ⊗[W] L)) (a : A) (z : A ⊗[W] L) : T c k hk f (a • z) = c a * T c k hk f z := GlobalTheory.T.trace_pairing_smul_left c k hk f a z

theorem T_ksmul (x : K₀) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L) : T c k hk (x • f) z = k x * T c k hk f z := GlobalTheory.T.trace_pairing_smul_dual c k hk x f z

theorem T_gal (σA : A →+* A) (σC : C₀ →+* C₀) (gT : A ⊗[W] L →+ A ⊗[W] L) (hg : ∀ a y, gT (a ⊗ₜ y) = σA a ⊗ₜ y)
    (hσ : ∀ a, σC (c a) = c (σA a)) (hσk : ∀ x, σC (k x) = k x) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L) :
    T c k hk f (gT z) = σC (T c k hk f z) := GlobalTheory.T.trace_pairing_galois_equivariant c k hk σA σC gT hg hσ hσk f z

theorem T_phi {F : W →+* W} (φA : A →+* A) (φC : C₀ →+* C₀) (φL : L →ₛₗ[F] L) (fr : K₀ →+* K₀)
    (φD : K₀ ⊗[W] L →+ K₀ ⊗[W] L) (hD : ∀ x y, φD (x ⊗ₜ y) = fr x ⊗ₜ φL y)
    (pT : A ⊗[W] L →+ A ⊗[W] L) (hp : ∀ a y, pT (a ⊗ₜ y) = φA a ⊗ₜ φL y)
    (hφ : ∀ a, φC (c a) = c (φA a)) (hφk : ∀ x, φC (k x) = k (fr x))
    {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)) (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L) :
    T c k hk f (pT z) = ∑ s, φC (T c k hk (b.coord s) z) * k (f (φD (b s))) :=
  GlobalTheory.T.trace_pairing_frobenius_compat c k hk φA φC φL fr φD hD pT hp hφ hφk b f z

theorem T_lTensor {L' : Type 1} [AddCommGroup L'] [Module W L'] (g : L' →ₗ[W] L) (f : Module.Dual K₀ (K₀ ⊗[W] L))
    (z : A ⊗[W] L') : T c k hk f (LinearMap.lTensor A g z) = T c k hk (f ∘ₗ g.baseChange K₀) z :=
  GlobalTheory.T.trace_pairing_lTensor_naturality c k hk g f z

theorem T_fac {B : Type} [Field B] (ι : C₀ →+* B) (i : A →+* B) (hι : ∀ a, ι (c a) = i a) (h : L →+ B)
    (hh : ∀ (w : W) y, h (w • y) = i (algebraMap W A w) * h y) {m : ℕ} (b : Module.Basis (Fin m) K₀ (K₀ ⊗[W] L)) :
    ∃ E : K₀ ⊗[W] L →+ B, (∀ x y, E (x ⊗ₜ y) = ι (k x) * h y) ∧
      ∀ G : A ⊗[W] L →+ B, (∀ a y, G (a ⊗ₜ y) = i a * h y) → ∀ z, G z = ∑ s, ι (T c k hk (b.coord s) z) * E (b s) :=
  GlobalTheory.T.trace_pairing_basis_eval c k hk ι i hι h hh b

theorem E_fix {B : Type} [Field B] [IsFractionRing W K₀] (ι : C₀ →+* B) (σB : B →+* B) (h : L →+ B)
    (E : K₀ ⊗[W] L →+ B) (hE : ∀ x y, E (x ⊗ₜ y) = ι (k x) * h y)
    (hσ : ∀ w, σB (ι (k (algebraMap W K₀ w))) = ι (k (algebraMap W K₀ w))) (hy : ∀ y, σB (h y) = h y) (v : K₀ ⊗[W] L) :
    σB (E v) = E v := GlobalTheory.T.tensor_eval_fixed_of_fixed k ι σB h E hE hσ hy v

end CrystallineSemistableComparison.Pb.Psi
