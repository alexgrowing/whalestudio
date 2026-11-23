import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.CycGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def DecOn (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (T : Finset (Pl F))
    (Ψ : (Fin n × Fin d → AF F) → ℂ) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
    (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  (∀ j, f j ∈ M.Pol B.ψ B.emb ∧ (∀ v, φ j v ∈ SB _) ∧ ∀ v ∉ T, φ j v = M.vac v) ∧ Ψ = ∑ j, pure (f j) (φ j)

def imgOn {a a' : ℕ} (R : RealMaps F a a') (Rf : FinMaps F a a') (T : Finset (Pl F)) (m : ℕ)
    (f : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ) :
    R.Pi ⊗[ℂ] (⨂[ℂ] v : T, Rf.Pi v) :=
  ∑ j, R.p' (f j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ j v))

def ImgSet {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (R : RealMaps F a a') (Rf : FinMaps F a a') (T : Finset (Pl F))
    (S : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ)) : Set (R.Pi ⊗[ℂ] (⨂[ℂ] v : T, Rf.Pi v)) :=
  {x | ∃ Ψ ∈ S, ∃ (m : ℕ) (f : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ),
    DecOn B G.M' T Ψ m f φ ∧ imgOn R Rf T m f φ = x}

end GlobalTheory.ThK.CycGen
