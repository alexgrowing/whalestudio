import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroTraceElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomIntegersInjectiveOfCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
namespace GlobalTheory.FlatModel.EigSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] {P : PtP E p} {V : Type} [CommRing V]

noncomputable def phi (β : V →+* 𝓞_ℂ_[p]) (tι : Dw.La →+ P.T) : V ⊗[ℤ] Dw.La →ₗ[ℤ] P.V :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun (v : V) (b : Dw.La) => ((β v : 𝓞_ℂ_[p]) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι b)
    (fun v v' b => by simp [TensorProduct.add_tmul])
    (fun n v b => by simp [TensorProduct.smul_tmul'])
    (fun v b b' => by simp [TensorProduct.tmul_add])
    (fun n v b => by simp [TensorProduct.tmul_smul]))

theorem phi_tmul (β : V →+* 𝓞_ℂ_[p]) (tι : Dw.La →+ P.T) (v : V) (b : Dw.La) :
    phi β tι (v ⊗ₜ b) = ((β v : 𝓞_ℂ_[p]) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι b := by
  unfold phi
  erw [TensorProduct.lift.tmul]; rfl

theorem phi_smul (β : V →+* 𝓞_ℂ_[p]) (tι : Dw.La →+ P.T) (v : V) (y : V ⊗[ℤ] Dw.La) :
    phi β tι (v • y) = ((β v : 𝓞_ℂ_[p]) : ℂ_[p]) • phi β tι y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b =>
    rw [TensorProduct.smul_tmul', phi_tmul, phi_tmul, TensorProduct.smul_tmul']
    simp
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem le_span_of_casimir (β : V →+* 𝓞_ℂ_[p]) (σ : 𝓞 E →+* V) {J : Type} [DecidableEq J] {N : ℕ}
    (a : Fin N → Dw.La) (T S : J → Fin N → V) (tι : Dw.La →+ P.T) (hL : LatData Dw σ a T S)
    (hι : ∀ (o : 𝓞 E) b, tι (o • b) = P.actT o (tι b))
    (hsp : Submodule.span ℤ_[p] (Set.range tι) = ⊤)
    {d : ℕ} (c θ : Fin d → 𝓞 E) (hc : ∀ o : 𝓞 E, ∑ j, c j ⊗ₜ[ℤ] (o * θ j) = ∑ j, (o * c j) ⊗ₜ[ℤ] θ j)
    (hne : ((β (σ (∑ j, c j * θ j)) : 𝓞_ℂ_[p]) : ℂ_[p]) ≠ 0) :
    P.eigV (β.comp σ) ≤
      Submodule.span ℂ_[p] (Set.range fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι (a m)) := by
  set Sp := Submodule.span ℂ_[p] (Set.range fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι (a m)) with hSp
  let χ : 𝓞 E → ℂ_[p] := fun o => ((β (σ o) : 𝓞_ℂ_[p]) : ℂ_[p])
  let Q : P.V →ₗ[ℂ_[p]] P.V := ∑ j, χ (c j) • P.actV (θ j)
  have hΦ : ∀ y ∈ Submodule.span V (Set.range fun i => ∑ m, T i m ⊗ₜ[ℤ] a m), phi β tι y ∈ Sp := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [map_sum]
      simp only [phi_tmul]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Sp.add_mem hx hy
    | smul v x _ hx => rw [phi_smul]; exact Sp.smul_mem _ hx
  have hb : ∀ b : Dw.La, Q (1 ⊗ₜ tι b) ∈ Sp := by
    intro b
    let g : 𝓞 E →ₗ[ℤ] Dw.La := (LinearMap.toSpanSingleton (𝓞 E) Dw.La b).restrictScalars ℤ
    have hx : (∑ j, σ (c j) ⊗ₜ[ℤ] (θ j • b)) ∈
        Submodule.span V (Set.range fun i => ∑ m, T i m ⊗ₜ[ℤ] a m) := by
      apply hL.2.2
      intro o
      have h1 := congrArg (TensorProduct.map σ.toIntAlgHom.toLinearMap g) (hc o)
      simp only [map_sum, TensorProduct.map_tmul] at h1
      simp only [map_sum, LinearMap.baseChange_tmul, Finset.smul_sum, TensorProduct.smul_tmul']
      simp only [g, LinearMap.restrictScalars_apply, LinearMap.toSpanSingleton_apply, mul_smul, map_mul,
        AlgHom.toLinearMap_apply] at h1
      exact h1
    have h2 := hΦ _ hx
    convert h2 using 1
    simp [Q, LinearMap.sum_apply, Point.actV, GlobalTheory.EigenSplit.baseChangeAction_apply,
      LinearMap.baseChange_tmul, hι, TensorProduct.smul_tmul', phi_tmul, χ]
  have hall : ∀ w, Q w ∈ Sp := by
    have hsm : ∀ (r : ℤ_[p]) (t : P.T), (1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] (r • t) =
        (algebraMap ℤ_[p] ℂ_[p] r) • ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] t) := by
      intro r t
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one, smul_eq_mul, _root_.mul_one]
    let M : Submodule ℤ_[p] P.T :=
      { carrier := {t | Q ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] t) ∈ Sp}
        add_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq, TensorProduct.tmul_add, map_add] at hx hy ⊢
          exact Sp.add_mem hx hy
        zero_mem' := by simp
        smul_mem' := fun r t ht => by
          simp only [Set.mem_setOf_eq, hsm, map_smul] at ht ⊢
          exact Sp.smul_mem _ ht }
    have hM : M = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      exact hb b
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul z t =>
      have ht : t ∈ M := hM ▸ Submodule.mem_top
      have he : z ⊗ₜ[ℤ_[p]] t = z • ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] t) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [he, map_smul]
      exact Sp.smul_mem _ ht
    | add x y hx hy => rw [map_add]; exact Sp.add_mem hx hy
  intro w hw
  have hw' := GlobalTheory.EigenSplit.mem_eigenSub.1 hw
  have hQ : Q w = χ (∑ j, c j * θ j) • w := by
    simp only [Q, LinearMap.sum_apply, LinearMap.smul_apply, hw', smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    simp [χ, map_sum, map_mul]
  have : w = (χ (∑ j, c j * θ j))⁻¹ • Q w := by
    rw [hQ, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [this]
  exact Sp.smul_mem _ (hall w)

theorem eigV_le_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (V : Type) [CommRing V]
    (β : V →+* 𝓞_ℂ_[p]) (σ : 𝓞 E →+* V) (J : Type) [DecidableEq J] (N : ℕ) (a : Fin N → Dw.La)
    (T S : J → Fin N → V) (tι : Dw.La →+ P.T), LatData Dw σ a T S → (∀ (o : 𝓞 E) b, tι (o • b) = P.actT o (tι b)) →
    Submodule.span ℤ_[p] (Set.range tι) = ⊤ →
    P.eigV (β.comp σ) ≤ Submodule.span ℂ_[p] (Set.range fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι (a m)) := by
  intro E _ _ _ H Dw p _ _ P V _ β σ J _ N a T S tι hL hι hsp
  obtain ⟨d, c, θ, hc, hne⟩ := GlobalTheory.T.exists_nonzero_trace_element E
  refine le_span_of_casimir β σ a T S tι hL hι hsp c θ hc ?_
  have hinj := GlobalTheory.ringHom_integers_injective_of_charZero E ℂ_[p] ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (β.comp σ))
  intro h
  apply hne
  apply hinj
  simpa using h

end GlobalTheory.FlatModel.EigSpan
