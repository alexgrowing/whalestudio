import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open scoped TensorProduct

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PairEx : Prop := ∀ (D : D7) (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ),
  (∀ τ, GlobalTheory.PairLift.PairPar (S τ) (S' τ) (aS τ) (aT τ)) → ∀ (V W : HSp D) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M,
      ∀ ω : GlobalTheory.Grid.WRep V W, GlobalTheory.PairLift.IsWeilExp ψ V W aS aT ω → ∀ f, GlobalTheory.Chain.IsVacVec ψ θ M M' f →
        IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It

def parRow (D : D7) (C : ℝ) (i : ℕ) : D.what₂.Tau → SPar := fun τ => dualPar (Node.par D C (.grid i 0) τ)

def RowModels : Prop := Gap fun {D} _ _ {sc} {G} W _ => ∀ i, i ≤ D.R.m →
  ∃ MV : DSModel (G.V (.grid i 0)) (parRow D sc.cGap i), cart MV = W.cart (.grid i 0)

def RowStep : Prop := Gap fun {D} {T} _ {sc} {G} W M => ∀ i, i < D.R.m → ∀ (S S' : D.what₂.Tau → SPar)
  (MA : DSModel (G.V (.grid i 0)) S) (MB : DSModel (G.V (.grid (i + 1) 0)) S'), S = parRow D sc.cGap i → S' = parRow D sc.cGap (i + 1) →
    cart MA = W.cart (.grid i 0) → cart MB = W.cart (.grid (i + 1) 0) →
    ∃ It : PolF D (G.V (.grid i 0)).rank (G.V (.grid (i + 1) 0)).rank → SmT MA → SmT MB, ∀ F ∈ MultT W.θ MA ∅ 1, ∀ κ : G.CosAt i,
      ∃ F' ∈ MultT W.θ MB ∅ 1, ∀ P v,
        LiftConv W M (.right i 0 : Arrow T) (W.fock (.chi i 0) (W.cosVec i κ) P) (F v) ∧
          liftA W M (.right i 0 : Arrow T) (W.fock (.chi i 0) (W.cosVec i κ) P) (F v) = F' (It P v)

def RowTower : Prop := Gap fun {D} {T} _ {sc} {G} W M => ∀ M₀ : DSModel (Yc D 0) (parB (Ptw D) 0), cart M₀ = W.cart (.grid 0 0) →
  ∀ (n : ℕ) (h : n ≤ D.R.m), ∃ (S : D.what₂.Tau → SPar) (MB : DSModel (G.V (.grid n 0)) S), S = parRow D sc.cGap n ∧
    cart MB = W.cart (.grid n 0) ∧ ∃ vec : G.RealVec → SmT M₀ → SmT MB, ∀ t ∈ MultT W.θ M₀ ∅ 1, ∀ Φ : G.Datum,
      ∃ F' ∈ MultT W.θ MB ∅ 1, ∀ ρ w,
        PathConv W M (rowPath T 0 n) (rowFam 0 n fun i => W.datum ρ Φ (Fin.castLE h i)) (t w) ∧ part W M ρ Φ (t w) n h = F' (vec ρ w)

def CoefTensor : Prop := ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is →
  ∃ (Wt : D.what₂.Tau → Type) (_ : ∀ τ, AddCommGroup (Wt τ)) (_ : ∀ τ, Module ℂ (Wt τ)) (_ : ∀ τ, FiniteDimensional ℂ (Wt τ))
    (π : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (Wt τ)) (e : (⨂[ℂ] τ, Wt τ) ≃ₗ[ℂ] Module.Dual ℂ c.W),
    (∀ τ, GlobalTheory.RealBessel.IsContIrred (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (π τ)) ∧
      ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ x y : ∀ τ, Wt τ, y τ = π τ g (x τ) → (∀ τ', τ' ≠ τ → y τ' = x τ') →
        e (PiTensorProduct.tprod ℂ y) = e (PiTensorProduct.tprod ℂ x) ∘ₗ c.ρ (atTau θ V τ g)⁻¹

section Sep

variable {D : D7} {V A : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {r : ℕ}
  (F : D.what₂.Tau → Matrix (Fin V.rank) (Fin A.rank) ℂ) (e : D.what₂.Tau → Matrix (Fin V.rank) (Fin r) ℂ)
  (χ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ) {Wt : D.what₂.Tau → Type} [∀ τ, AddCommGroup (Wt τ)] [∀ τ, Module ℂ (Wt τ)]
  (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → Module.End ℂ (Wt τ))

open Classical in

def SepBes (β : (∀ τ, Wt τ) → M.Vec → ℂ) : Prop :=
  ∀ τ x v, ∃ b ∈ GlobalTheory.RealBessel.besselForms (gramAt D V τ) (gramAt D A τ) (F τ) (e τ) (χ τ) (M.rep τ) (π τ) (M.sm τ),
    ∀ y u, β (Function.update x τ y) (Function.update v τ u) = b y u

end Sep

def SepLine : Prop := ∀ (D : D7) (V A : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (r : ℕ)
  (F : D.what₂.Tau → Matrix (Fin V.rank) (Fin A.rank) ℂ) (e : D.what₂.Tau → Matrix (Fin V.rank) (Fin r) ℂ) (z : D.what₂.Tau → Fin V.rank → ℂ)
  (χ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ) (Wt : D.what₂.Tau → Type) [∀ τ, AddCommGroup (Wt τ)] [∀ τ, Module ℂ (Wt τ)]
  [∀ τ, FiniteDimensional ℂ (Wt τ)] (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → Module.End ℂ (Wt τ)),
  (∀ τ, GlobalTheory.RealBessel.IsFrame (gramAt D V τ) (gramAt D A τ) (F τ) (e τ) (z τ) ∧ GlobalTheory.RealBessel.IsGeneric (gramAt D V τ) (e τ) (z τ) (χ τ) ∧
    GlobalTheory.RealBessel.IsContIrred (Formalism.QuantumDeterminants.UH (gramAt D A τ)) (π τ)) →
  ∃ ℓ : (∀ τ, Wt τ) → M.Vec → ℂ, ∀ β, SepBes M F e χ π β → ∃ l : ℂ, ∀ x v, β x v = ℓ x v * l

def TopFrame : Prop := All fun {D} _ _ _ {G} W _ => ∃ z : D.what₂.Tau → Fin (G.V (.grid D.R.m 0)).rank → ℂ, ∀ τ,
  GlobalTheory.RealBessel.IsFrame (gramAt D (G.V (.grid D.R.m 0)) τ) (gramAt D (G.V (.top 0)) τ)
               ((frameMat _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι).map (tauE D τ)) (G.besTop.e.map (tauE D τ)) (z τ) ∧
    GlobalTheory.RealBessel.IsGeneric (gramAt D (G.V (.grid D.R.m 0)) τ) (G.besTop.e.map (tauE D τ)) (z τ)
      fun u => besChar W.ψ G.besTop (atTau W.θ _ τ u)

def TopSep : Prop := All fun {D} _ _ _ {G} W M => ∀ (S : D.what₂.Tau → SPar) (MB : DSModel (G.V (.grid D.R.m 0)) S),
  ∀ F' ∈ MultT W.θ MB ∅ 1, ∀ Ψ ∈ Cols G W.θ,
    (∃ b : Module.Dual ℂ (coefPlus G W.θ).W →ₗ[ℂ] SmT MB →ₗ[ℂ] ℂ, ∀ ξ v, Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) (F' v) = b ξ v) ∧
    ∀ (Wt : D.what₂.Tau → Type) [∀ τ, AddCommGroup (Wt τ)] [∀ τ, Module ℂ (Wt τ)]
      (π : ∀ τ, Matrix (Fin (G.V (.top 0)).rank) (Fin (G.V (.top 0)).rank) ℂ → Module.End ℂ (Wt τ))
      (e : (⨂[ℂ] τ, Wt τ) ≃ₗ[ℂ] Module.Dual ℂ (coefPlus G W.θ).W),
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V (.top 0)) τ), ∀ x y : ∀ τ, Wt τ, y τ = π τ g (x τ) → (∀ τ', τ' ≠ τ → y τ' = x τ') →
        e (PiTensorProduct.tprod ℂ y) = e (PiTensorProduct.tprod ℂ x) ∘ₗ (coefPlus G W.θ).ρ (atTau W.θ _ τ g)⁻¹) →
      SepBes MB (fun τ => (frameMat _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι).map (tauE D τ))
        (fun τ => G.besTop.e.map (tauE D τ)) (fun τ u => besChar W.ψ G.besTop (atTau W.θ _ τ u)) π
        fun x v => Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ x)) Ψ) (F' (PiTensorProduct.tprod ℂ v))

def TopLine : Prop := All fun {D} _ _ _ {G} W M => ∀ (S : D.what₂.Tau → SPar) (MB : DSModel (G.V (.grid D.R.m 0)) S),
  ∃ ℓ : Module.Dual ℂ (coefPlus G W.θ).W → SmT MB → ℂ, ∀ F' ∈ MultT W.θ MB ∅ 1, ∀ Ψ ∈ Cols G W.θ, ∃ l : ℂ,
    ∀ ξ v, Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) (F' v) = ℓ ξ v * l

def RowConv : Prop := Gap fun {D} _ {L} _ {G} W M => ∀ M₀ : DSModel (Yc D 0) (parB (Ptw D) 0), cart M₀ = W.cart (.grid 0 0) →
  ∀ t ∈ Rows L W.θ M₀, ∀ w ρ ξ, ∀ Ψ ∈ Cols G W.θ, ∀ Φ, FConv W M ρ ξ Ψ Φ (t w)

def GoodRows : Prop := ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ t ∈ R.EEat R.triv,
    PiTensorProduct.lift t ∈ Rows R.toLevCh R.θ (R.MY 0)

theorem parRow_zero (D : D7) (C : ℝ) : parRow D C 0 = parB (Ptw D) 0 :=
  funext fun τ => congrArg dualPar (parV_zero D C (Nat.zero_le _) τ)

end GlobalTheory.SepRows

end
