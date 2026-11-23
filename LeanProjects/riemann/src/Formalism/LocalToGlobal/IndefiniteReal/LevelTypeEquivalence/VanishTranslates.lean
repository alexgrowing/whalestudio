import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThFEquivOf
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IoUniq
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.VanishKfLow

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.KerDiag

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Gen

variable {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)

def KfLow (τ : D.what₂.Tau) : Submodule ℂ (M.sm τ) :=
  Submodule.span ℂ {w | ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃ w0 : lowT M τ,
    (w : M.H τ) = M.rep τ g ((w0 : M.sm τ) : M.H τ)}

open Classical in

theorem mult_equiv {T : MMap M} (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ) (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => rfl
  | add T T' _ _ h1 h2 =>
    simp only [_root_.add_apply, h1, h2]
    rfl
  | smul c T _ h =>
    simp only [_root_.smul_apply, h]
    rfl

open Classical in

theorem vanish_KfLow {T : MMap M} (hT : T ∈ Mult θ M J χ)
    (hlow : ∀ v : ∀ ρ, lowT M ρ, T (fun ρ => v ρ) = 0) :
    ∀ (s : Finset D.what₂.Tau) (v : M.Vec), (∀ τ ∈ s, v τ ∈ KfLow M τ) →
      (∀ τ ∉ s, ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃ w0 : lowT M τ,
        (v τ : M.H τ) = M.rep τ g ((w0 : M.sm τ) : M.H τ)) → T v = 0 :=
  by apply _root_.UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.vanish_KfLow <;> assumption

end Gen

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def DensLow : Prop :=
  ∀ i τ (ℓ : (R.MW i (sg0 D A)).H τ →ₗ[ℂ] ℂ),
    Sobolev₂ (lieAt (Wc D i) τ) ((R.MW i (sg0 D A)).rep τ) ℓ →
      (∀ w ∈ KfLow (R.MW i (sg0 D A)) τ, ℓ (w : (R.MW i (sg0 D A)).H τ) = 0) →
        ∀ w : (R.MW i (sg0 D A)).sm τ, ℓ (w : (R.MW i (sg0 D A)).H τ) = 0

open Classical in
theorem spanP_of (h : DensLow R) : Formalism.IndefR.Eqv.Act.SpanP R := by
  intro i F hS hlow
  let M := R.MW i (sg0 D A)
  let Kf : ∀ τ, Submodule ℂ (M.sm τ) := fun τ => KfLow M τ
  let Tm : ℂ →ₗ[ℂ] (⨂[ℂ] τ, Kf τ) →ₗ[ℂ] (⨂[ℂ] τ, M.sm τ) :=
    LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (PiTensorProduct.map fun τ => (Kf τ).subtype)
  have hS' : F ∈ Mult R.θ M (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) := hS
  have hu : PiTensorProduct.lift F ∈ MultT R.θ M (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) := by
    rw [mem_multT, LinearEquiv.symm_apply_apply]; exact hS'
  have hvan0 : ∀ v : ∀ τ, Kf τ, F (fun τ => (v τ : M.sm τ)) = 0 := fun v =>
    vanish_KfLow R.θ M _ _ hS' hlow Finset.univ _ (fun τ _ => (v τ).2) (fun τ h => absurd (Finset.mem_univ τ) h)
  have hvan : ∀ (φ : ℂ) (w : ⨂[ℂ] τ, Kf τ), PiTensorProduct.lift F (Tm φ w) = 0 := by
    intro φ w
    simp only [Tm, LinearMap.smulRight_apply, LinearMap.id_apply, LinearMap.smul_apply, map_smul]
    rw [smul_eq_zero]
    right
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, PiTensorProduct.map_tprod, map_smul, PiTensorProduct.lift.tprod]
      simp only [Submodule.subtype_apply]
      rw [hvan0 v, smul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  have hspan : ∀ v : ∀ τ, M.sm τ, (∀ τ, v τ ∈ Kf τ) →
      PiTensorProduct.tprod ℂ v ∈ Submodule.span ℂ {x | ∃ φ w, Tm φ w = x} := by
    intro v hv
    refine Submodule.subset_span ⟨1, PiTensorProduct.tprod ℂ (fun τ => (⟨v τ, hv τ⟩ : Kf τ)), ?_⟩
    simp only [Tm, LinearMap.smulRight_apply, LinearMap.id_apply, LinearMap.smul_apply, one_smul,
      PiTensorProduct.map_tprod]
    rfl
  have h0 := Formalism.IndefR.Eqv.ioUniqueAt_holds D _ _ M R.θ _ _ Kf ℂ (⨂[ℂ] τ, Kf τ) Tm (fun τ ℓ hℓ hK => h i τ ℓ hℓ hK)
    hspan _ hu hvan
  have : F = PiTensorProduct.lift.symm (PiTensorProduct.lift F) := by simp
  rw [this, h0, map_zero]

end Formalism.IndefR.Eqv.KerDiag

end
