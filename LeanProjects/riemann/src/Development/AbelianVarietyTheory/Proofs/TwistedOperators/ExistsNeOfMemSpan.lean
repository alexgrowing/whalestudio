import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InclTprodUpdate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerSpanKFiniteTensorsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Formalism.L2.DIV Formalism.L2.Indef NumberField GlobalTheory.Chain GlobalTheory.Chain.IoLift
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowTest.WVec

variable {D : D7}

theorem tprod_ne_zero {κ : Type} [Fintype κ] {E : κ → Type} [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)]
    {v : ∀ j, E j} (hv : ∀ j, v j ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  choose l hl using fun j => Module.Projective.exists_dual_eq_one ℂ (hv j)
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap l)) h
  simp [hl] at this

theorem exists_inclK_ne {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} (h : KSm M) :
    ∃ y : KT M, inclK h y ≠ 0 := by
  have hu : ∀ τ, ∃ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, u ≠ 0 := fun τ => by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin_ne_bot M τ)
    exact ⟨⟨x, hx⟩, fun e => hx0 (congrArg Subtype.val e)⟩
  choose u hu using hu
  refine ⟨PiTensorProduct.tprod ℂ u, fun e => tprod_ne_zero hu ?_⟩
  exact GlobalTheory.Chain.IoLift.FinTensor.inclK_injective h (e.trans (map_zero _).symm)

theorem exists_ne_of_mem_span {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (L : E →ₗ[ℂ] F) {s : Set E} {x : E} (hx : x ∈ Submodule.span ℂ s) (h : L x ≠ 0) : ∃ z ∈ s, L z ≠ 0 := by
  by_contra hn
  push_neg at hn
  exact h ((Submodule.span_le (p := LinearMap.ker L)).2 (fun z hz => hn z hz) hx)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem dnVec_congr (d d' : ChainVec R) : ∀ n, (∀ k < n, d.polY k = d'.polY k) → d.dnVec n = d'.dnVec n
  | 0, _ => rfl
  | n + 1, h => by
    show d.dnVec n ∘ₗ R.ItY n (d.polY n) = d'.dnVec n ∘ₗ R.ItY n (d'.polY n)
    rw [dnVec_congr d d' n fun k hk => h k (by omega), h n (by omega)]

def ofPol (p : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank) : ChainVec R := ⟨p, 0, 0⟩

theorem exists_w_ne (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules)
    (hC : ∀ k, ChainPar D k) (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hch : R.IsChain) (hθ : R.models_inf) :
    ∃ cv : ChainVec R, cv.w ≠ 0 := by
  have hm := D.R.two_le_m
  have hS := GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hθ hch.ωY hch.ωX hch.vY hch.vX
  have stepY : ∀ k, k + 1 < D.R.m → ∃ (h : KSm (R.MY k)) (h' : KSm (R.MY (k + 1))),
      LinearMap.range (inclK h) ≤ Submodule.span ℂ {x | ∃ φ y, R.ItY k φ (inclK h' y) = x} := fun k hk => by
    obtain ⟨hW, hV⟩ := hS.1 A.μ0 ⟨k, by omega⟩ hk
    exact GlobalTheory.T.realThetaIntertwiner_span_kFiniteTensors hD hH D ⟨k, by omega⟩ (min k D.R.m) (min (k + 1) D.R.m) (min_eq_left (by omega))
      (min_eq_left (by omega)) _ _ (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ (hC _) (R.ωY A.μ0 k) (R.vY A.μ0 k) hW hV (R.ItY k)
      (hch.ItY A.μ0 k hk)
  have stepX : ∃ (h : KSm (R.MY (D.R.m - 1))) (h' : KSm R.MX),
      LinearMap.range (inclK h) ≤ Submodule.span ℂ {x | ∃ φ y, R.ItX φ (inclK h' y) = x} := by
    obtain ⟨hW, hV⟩ := hS.2 A.μ0 ⟨D.R.m - 1, by omega⟩ rfl
    exact GlobalTheory.T.realThetaIntertwiner_span_kFiniteTensors hD hH D ⟨D.R.m - 1, by omega⟩ (min (D.R.m - 1) D.R.m) D.R.m (min_eq_left (Nat.sub_le _ _))
      (by show D.R.m = D.R.m - 1 + 1; omega) _ _ (R.MY (D.R.m - 1)) R.MX R.θ R.ψ hθ (hC _) (R.ωX A.μ0) (R.vX A.μ0) hW hV
      R.ItX (hch.ItX A.μ0)
  have key : ∀ n, n + 1 ≤ D.R.m → ∃ (p : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank) (h : KSm (R.MY n))
      (y : KT (R.MY n)), (ofPol (R := R) p).dnVec n (inclK h y) ≠ 0 := by
    intro n
    induction n with
    | zero =>
      intro _
      obtain ⟨h, -, -⟩ := stepY 0 (by omega)
      obtain ⟨y, hy⟩ := exists_inclK_ne h
      exact ⟨fun _ => 0, h, y, hy⟩
    | succ n ih =>
      intro hn
      obtain ⟨p, h, y, hy⟩ := ih (by omega)
      obtain ⟨h1, h2, hsp⟩ := stepY n (by omega)
      obtain ⟨z, ⟨φ, y', rfl⟩, hz⟩ := exists_ne_of_mem_span _ (hsp ⟨y, rfl⟩) hy
      refine ⟨Function.update p n φ, h2, y', ?_⟩
      show (ofPol (R := R) (Function.update p n φ)).dnVec n
        (R.ItY n ((Function.update p n φ) n) (inclK h2 y')) ≠ 0
      rw [Function.update_self, dnVec_congr (ofPol (Function.update p n φ)) (ofPol p) n
        fun k hk => Function.update_of_ne (by omega) _ _]
      exact hz
  obtain ⟨p, h, y, hy⟩ := key (D.R.m - 1) (by omega)
  obtain ⟨h1, h2, hsp⟩ := stepX
  obtain ⟨z, ⟨φ, y', rfl⟩, hz⟩ := exists_ne_of_mem_span _ (hsp ⟨y, rfl⟩) hy
  refine ⟨⟨p, φ, inclK h2 y'⟩, ?_⟩
  show ChainVec.dnVec ⟨p, φ, inclK h2 y'⟩ (D.R.m - 1) (R.ItX φ (inclK h2 y')) ≠ 0
  rwa [dnVec_congr ⟨p, φ, inclK h2 y'⟩ (ofPol p) (D.R.m - 1) fun k _ => rfl]

end GlobalTheory.RowTest.WVec

end
