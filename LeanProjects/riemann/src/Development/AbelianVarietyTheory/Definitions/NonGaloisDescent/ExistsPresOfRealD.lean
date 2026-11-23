import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsResCharP

noncomputable section
namespace GlobalTheory.Present
open scoped LaurentSeries PowerSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}
    (W : LocWach PD LL O v n₀) {k : Type} [Field k] [Algebra O k]

theorem φ_mem (T : LocLat G Qp LL O) (x : ↥(DΔ W T)) : W.φD T x ∈ DΔ W T :=
  fun δ hδ => by rw [← W.φγ_comm, x.2 δ hδ]

theorem γ_mem (T : LocLat G Qp LL O) (g : W.Gam) (x : ↥(DΔ W T)) : W.γD T g x ∈ DΔ W T :=
  fun δ hδ => by rw [← W.γD_mul, mul_comm, W.γD_mul, x.2 δ hδ]

variable {W} {l n : ℕ} {R : RingPG k l} {F : DFun R n G} {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {τ : ZMod n → ZMod n₀} {γ : W.Gam}

theorem Pres.j_φ' (p : Pres W F ι τ γ) {T A q} (h : Onto T A q) (i : ZMod n) (x : ↥(DΔ W T)) :
    p.j T A q i ⟨W.φD T x, φ_mem W T x⟩ = (F.D A).φ i (p.j T A q (i - 1) x) :=
  p.j_φ T A q h i x _ rfl

theorem Pres.j_γ' (p : Pres W F ι τ γ) {T A q} (h : Onto T A q) (i : ZMod n) (x : ↥(DΔ W T)) :
    p.j T A q i ⟨W.γD T γ x, γ_mem W T γ x⟩ = (F.D A).γ i (p.j T A q i x) :=
  p.j_γ T A q h i x _ rfl

end GlobalTheory.Present

namespace GlobalTheory.TopSteps.TopSit
open scoped LaurentSeries PowerSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.PhiGam GlobalTheory.Models GlobalTheory.Present
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

end GlobalTheory.TopSteps.TopSit
