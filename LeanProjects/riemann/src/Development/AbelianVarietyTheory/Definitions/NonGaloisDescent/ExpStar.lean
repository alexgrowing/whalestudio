import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis

noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

def IsTheta {P : LocPrime l} (AI : LocAinf l P) (θ : Ainf l →+* OC l) : Prop :=
  (∀ (x : OCb l) (y : OC l),
    PreTilt.coeff 0 x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y →
      θ (WittVector.teichmuller l x) - y ∈ Ideal.span {((l : ℕ) : OC l)}) ∧
  Function.Surjective θ ∧
  (∀ (g : GQ l) (a : Ainf l), ((θ (AI.actW g a) : OC l) : PadicComplex l) =
    AI.actC g ((θ a : OC l) : PadicComplex l)) ∧
  (∀ a : Ainf l, θ a = 0 ↔ AI.ξ ∣ a) ∧
  ∀ j : ℕ, θ (WittVector.teichmuller l (AI.εroot j)) = AI.ζ j

def zC (x : ℤ_[l]) : PadicComplex l := algebraMap ℚ_[l] (PadicComplex l) (x : ℚ_[l])

def IsMat (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) : Prop :=
  letI := zlMod LL T
  ∃ b : Module.Basis (Fin d) ℤ_[l] ↥T.L.T,
    (∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = zC (b.repr (actTZ LL T g (b j)) i)) ∧
    ∀ (a : ↥(OL LL)) (i j : Fin d), A a i j = zC (b.repr (⟨_, T.L.T.smul_mem a (b j).2⟩ : ↥T.L.T) i)

def IsDec (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l)
    (m : ℕ) {d : ℕ} (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (D : Matrix (Fin d) (Fin d) (PadicComplex l))
    (U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) : Prop :=
  IsUnit D.det ∧ (∀ a b, ‖D a b‖ ≤ 1) ∧ (∀ a b, ‖(l : PadicComplex l) * D⁻¹ a b‖ ≤ 1) ∧
    Frame χ K m U g ∧ ∀ σ ∈ Gj K m, D * U σ = M σ * D.map (act σ)

def ExpStar (LT : LocTheory) (G : Subgroup (GQ l)) (e : ℕ) (z : GQ l → ℚ_[l]) (α : Om l) : Prop :=
  CocOn G (fun σ y => (((LT l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z ∧
  ∃ b ∈ ((LT l).PD (botExt l)).Fil 0, ∀ σ ∈ G,
    algebraMap ℚ_[l] (LT l).R.BdR (z σ) -
      algebraMap ℚ_[l] (LT l).R.BdR ((logChi LT σ : ℤ_[l]) : ℚ_[l]) *
        (algebraMap (Om l) (LT l).R.BdR α * (LT l).ιB (LT l).tB ^ e) -
      (algebraMap ℚ_[l] (LT l).R.BdR (((LT l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) *
        (LT l).actQdR σ b - b) ∈ ((LT l).PD (botExt l)).Fil ((e : ℤ) + 1)

def betaE (l s e : ℕ) : ℤ :=
  if e = 0 then -1 else (s : ℤ) - 1 - e - padicValNat l (e - 1).factorial

def repQ {P : LocPrime l} (AI : LocAinf l P) (G : Subgroup (GQ l)) {T : Type} [AddCommGroup T]
    [Module ℤ_[l] T] (ρ : ↥G →* (T →ₗ[ℤ_[l]] T)) (a b : ℤ) :
    Representation ℤ_[l] ↥G (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b)) :=
  repX (act := AI.actWCbHom.comp G.subtype) ρ
    ⟨fun g x hx => (xiOK AI).1 (g : GQ l) x hx, (xiOK AI).2.1, fun g => (xiOK AI).2.2 (g : GQ l)⟩ a b

end GlobalTheory.Cyc
