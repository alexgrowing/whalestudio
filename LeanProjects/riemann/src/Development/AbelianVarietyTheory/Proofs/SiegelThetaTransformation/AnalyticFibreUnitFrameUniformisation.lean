import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkingsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem exists_ex_transport {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {s : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo s ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
    (x0 : Sp ℂ ⟶ Xo.X) (h : x0 = F.u i P) :
    ∃ ex : (Fin g → ℂ) → (ptO Xo x0 ⟶ Xo.univ.t.G),
      (∀ z, (ex z).left = (F.ex i P z).left) ∧ (∀ z w, ex (z + w) = ex z * ex w) ∧ Function.Surjective ex ∧
      (∀ z, ex z = 1 ↔ z ∈ P.range) ∧
      (∀ (a : 𝓞 E) z, ex (fun j => ty j (a : E) * z j) = ex z ≫ Xo.univ.t.act.act a) ∧
      ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo x0 a = ex ((l.M : ℂ)⁻¹ • P (F.t i a)) := by
  subst h
  refine ⟨F.ex i P, fun _ => rfl, F.ex_add i P hP, F.ex_onto i P hP, F.ex_ker i P hP, F.ex_lin i P hP, ?_⟩
  intro a ha
  exact F.ex_eta i P hP a ha

set_option maxHeartbeats 1000000 in

theorem uw_anFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (W : UW U) (k : U.Comp) (bas : (Fin W.g ⊕ Fin W.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin W.g ≃ (U.X k).Ψ × Fin r), IsSympl (U.X k) bas → (∀ x v j, pv (U.X k) idx x v j = perFr (U.X k) x v (relab c σ (W.e j).1) (W.e j).2) → (∀ j, rowType (U.X k) (idx j) = relab c σ (W.e j).1) → ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ A : AnFib (U.X k) bas idx W.e x.1 (U.X k).Λ (unC U k x), A.Marked (W.mark k) ∧ ∃ θ, A.Reads 1 (unC U k x).s θ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ θ := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hr W k bas idx hS hpv hrow x hxu
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨Pm, hPm, hPer, hux, hder, hfr⟩ := W.pt k x
  obtain ⟨Hm, χl, fr, θ, Fd, hHm, -, hIm, hfrhol, hfrne, hfrg, hfr0, hfrper, hread, hFd, hmean⟩ := hfr hxu
  obtain ⟨ex, hexl, hadd, honto, hker, hlin, hmark⟩ :=
    exists_ex_transport W.F (W.ik k) Pm hPer (U.un k x).x hux

  have hPv : ∀ a, Pm a = pv (U.X k) idx x.1 (W.φ k a : Fin r → E) := fun a => funext fun j => by
    rw [hPm, hpv]
  have hφs : ∀ u ∈ (U.X k).Λ, ∃ a, (W.φ k a : Fin r → E) = u := fun u hu =>
    ⟨(W.φ k).symm ⟨u, hu⟩, by simp⟩
  have hembφ : ∀ a, W.emb k a = (W.φ k a : Fin r → E) := fun a => rfl
  have hrange : ∀ z, z ∈ Pm.range ↔ ∃ v ∈ (U.X k).Λ, z = pv (U.X k) idx x.1 v := by
    intro z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, SetLike.coe_mem _, hPv a⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := hφs v hv
      exact ⟨a, hPv a⟩
  obtain ⟨-, -, -, -, -, hspan, hEF⟩ := GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hσ hU hr W k
  have hrng : Set.range (W.emb k) = ((U.X k).Λ : Set (Fin r → E)) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      rw [hembφ]
      exact SetLike.coe_mem _
    · intro hv
      obtain ⟨a, rfl⟩ := hφs v hv
      exact ⟨a, hembφ a⟩
  obtain ⟨-, -, -, -, hsm, -, hL, -⟩ := hx_laws E r (U.X k) W.g bas idx 0 hS ⟨0, rfl⟩ x.1 x.2

  have him : ∀ u ∈ (U.X k).Λ, ∀ v ∈ (U.X k).Λ,
      (hermForm Hm (pv (U.X k) idx x.1 u) (pv (U.X k) idx x.1 v)).im = (EF (U.X k) u v : ℝ) := by
    intro u hu v hv
    obtain ⟨a, rfl⟩ := hφs u hu
    obtain ⟨b, rfl⟩ := hφs v hv
    rw [← hPv, ← hPv, hIm, ← hembφ, ← hembφ, ← hEF a b]
    norm_cast
  have hH : ∀ z w, hermForm Hm z w = hx (U.X k) bas idx x.1 z w :=
    (hL (U.X k).Λ (hrng ▸ hspan)).2 Hm hHm him
  have hfun : (fun z => (ex z).left) = fun z => (W.F.ex (W.ik k) Pm z).left := funext hexl
  refine ⟨{ ex := ex
            ex_add := hadd
            ex_onto := honto
            ex_ker := fun z => (hker z).trans (hrange z)
            ex_lin := fun a z => by
              have e : (fun j => rowType (U.X k) (idx j) (a : E) * z j) =
                  fun j => relab c σ (W.e j).1 (a : E) * z j := funext fun j => by rw [hrow]
              rw [e]
              exact hlin a z
            hol := by
              intro V f
              simp only [Set.sep_univ, hexl]
              exact ReciprocityTheory.ChartRestriction.G.TB.ValAt.famHol W.F (W.ik k) Pm hPer V f
            der := fun ℓ => by
              rw [hfun]
              exact hder ℓ.1 ℓ.2
            fr := fr
            fr_hol := fun j => by simp only [hexl]; exact hfrhol j
            fr_ne := fun j z => by simp only [hexl]; exact hfrne j z
            fr_g := fun j j' z => by simp only [hexl]; exact hfrg j j' z
            fr_0 := fun j => by simp only [hexl]; exact hfr0 j
            χ := fun v => if ‖χl (pv (U.X k) idx x.1 v)‖ = 1 then χl (pv (U.X k) idx x.1 v) else 1
            χ_norm := fun v _ => by
              try dsimp only
              split_ifs with h
              · exact h
              · simp
            fr_per := fun v hv j z hz => by
              obtain ⟨a, rfl⟩ := hφs v hv
              obtain ⟨hn, hp⟩ := hfrper a j z
              try dsimp only
              rw [← hPv, if_pos hn, ← hH, ← hH]
              exact hp (by simpa only [hexl] using hz) }, ?_, θ, ?_, ?_⟩
  · intro a ha
    have hM : pv (U.X k) idx x.1 (((l.M : E)⁻¹) • W.mark k a) = (l.M : ℂ)⁻¹ • Pm (W.F.t (W.ik k) a) := by
      funext j
      simp only [hsm, hrow, hPv, Pi.smul_apply, smul_eq_mul, map_inv₀, map_natCast]
      rfl
    exact (hmark a ha).trans (congrArg ex hM.symm)
  · intro j z pt h1 h2 h3
    rw [zpow_one]
    exact hread j z pt (h1.trans (hexl z)) h2 (by simpa only [hexl] using h3)
  · refine ⟨Pm.range, Fd, hrange, hFd, ?_⟩
    simpa only [hH] using hmean

end GlobalTheory.Dict
