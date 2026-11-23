import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermSmulAddDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCoeffsTendstoZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGaugeFiniteExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.ThetaTermAdic

theorem decomp (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : ℕ) (hm : 0 < m) :
    ∃ (mu rh : X → X), (Set.range rh).Finite ∧ ∀ χ, χ = m • mu χ + rh χ := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  refine ⟨fun χ => ∑ i, (b.repr χ i / (m : ℤ)) • b i, fun χ => ∑ i, (b.repr χ i % (m : ℤ)) • b i, ?_, fun χ => ?_⟩
  · have hS : (Set.pi Set.univ fun _ : Module.Free.ChooseBasisIndex ℤ X => Set.Ico (0 : ℤ) m).Finite :=
      Set.Finite.pi fun _ => Set.finite_Ico _ _
    refine (hS.image fun f => ∑ i, f i • b i).subset ?_
    rintro _ ⟨χ, rfl⟩
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    exact ⟨fun i => b.repr χ i % m, fun i _ => ⟨Int.emod_nonneg _ hm'.ne', Int.emod_lt_of_pos _ hm'⟩, rfl⟩
  · conv_lhs => rw [← b.sum_repr χ]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ, smul_smul, ← add_smul, Int.mul_ediv_add_emod]

theorem mul_mem_smul_top {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) (a s : S)
    (hs : s ∈ (I • ⊤ : Submodule R S)) : a * s ∈ (I • ⊤ : Submodule R S) := by
  rw [Ideal.smul_top_eq_map] at hs ⊢
  exact Ideal.mul_mem_left _ a hs

theorem core {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (N : GlobalTheory.Ex.NumD (Kb R))
    (S : Subalgebra R (Kb R)) [Module.Finite R S] (m : ℕ) (hm : 0 < m) (q : N.QT (m ^ 2))
    (hθ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}), ∀ x' ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}),
      ∀ x'' ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}),
      (N.θ x x' x'' : Kb R) ∈ S ∧ (((N.θ x x' x'')⁻¹ : (Kb R)ˣ) : Kb R) ∈ S)
    (hσ : ∀ x ∈ Subgroup.closure (Set.range N.c ∪ {(q.1.2 ^ m).b}), (N.σ x : Kb R) ∈ S ∧ (((N.σ x)⁻¹ : (Kb R)ˣ) : Kb R) ∈ S)
    (hthS : ∀ χ, N.th (N.c χ * (q.1.2 ^ m).b) ∈ S) (hψS : ∀ χ, (N.ψ χ : Kb R) ∈ S)
    (hψn : ∀ n : ℕ, {χ | ¬ ∃ s ∈ (maximalIdeal R ^ n • ⊤ : Submodule R S), (s : Kb R) = N.ψ χ}.Finite) :
    ∃ (Jx : Type) (_ : Fintype Jx) (g : Jx → Kb R) (c : N.X → Jx → R),
      (∀ χ, N.txT m q χ = ∑ k, algebraMap (FractionRing R) (Kb R) (algebraMap R _ (c χ k)) * g k) ∧
      ∀ n : ℕ, {χ | ¬ ∀ k, c χ k ∈ maximalIdeal R ^ n}.Finite := by
  classical
  set h := q.1.2 ^ m with hdef
  set y := q.1.1.toAdd with hy
  have hh : h ^ m = N.io y := by rw [hdef, ← pow_mul, ← sq]; exact N.mem_QT.1 q.2
  obtain ⟨mu, rh, hrf, hχ⟩ := decomp N.X m hm
  choose w hwS hw using GlobalTheory.T.thetaSeriesTerm_smul_add_decomposition (Kb R) N S.toSubring m h y hh hθ hσ
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := S)
  obtain ⟨e, he⟩ : ∃ e, m ^ 2 = e + 1 := ⟨m ^ 2 - 1, by have := pow_pos hm 2; omega⟩
  let K : N.X → Kb R := fun b => ((N.wQ q / mulq N.θ N.σ m q.1.2.b : (Kb R)ˣ) : Kb R) *
    ((N.ψ b * h.s b * (N.ψ (m • b + y))⁻¹ : (Kb R)ˣ) : Kb R)
  let z0 : N.X → Kb R := fun χ => (w (mu χ) (rh χ) : Kb R) * (N.ψ (mu χ) : Kb R) ^ e * N.th (N.c χ * h.b) *
    N.ψ (mu χ + (m • rh χ + y))
  have key : ∀ χ, N.txT m q χ = K (rh χ) * z0 χ := fun χ => by
    have a := hw (mu χ) (rh χ)
    rw [← hχ χ, he, NumD.τ] at a
    simp only [NumD.txT, NumD.vt, K, z0]
    rw [← hdef, a]
    push_cast
    field_simp
    ring
  have hz0 : ∀ χ, z0 χ ∈ S := fun χ =>
    S.mul_mem (S.mul_mem (S.mul_mem (Subalgebra.mem_toSubring.1 (hwS _ _)) (S.pow_mem (hψS _) _)) (hthS χ)) (hψS _)
  let zS : N.X → S := fun χ => ⟨z0 χ, hz0 χ⟩
  have hzn : ∀ n : ℕ, {χ | zS χ ∉ (maximalIdeal R ^ n • ⊤ : Submodule R S)}.Finite := fun n => by
    refine (hrf.biUnion fun b _ => (hψn n).image fun χ' => m • (χ' - (m • b + y)) + b).subset ?_
    intro χ hχn
    refine Set.mem_biUnion (Set.mem_range_self χ) ⟨mu χ + (m • rh χ + y), ?_, ?_⟩
    · rintro ⟨s', hs', he'⟩
      refine hχn ?_
      have e1 : zS χ = (⟨(w (mu χ) (rh χ) : Kb R) * (N.ψ (mu χ) : Kb R) ^ e * N.th (N.c χ * h.b),
          S.mul_mem (S.mul_mem (Subalgebra.mem_toSubring.1 (hwS _ _)) (S.pow_mem (hψS _) _)) (hthS χ)⟩ : S) * s' :=
        Subtype.ext (by simp only [zS, z0, Subalgebra.coe_mul, he'])
      rw [e1]
      exact mul_mem_smul_top _ _ _ hs'
    · change m • (mu χ + (m • rh χ + y) - (m • rh χ + y)) + rh χ = χ
      rw [add_sub_cancel_right]; exact (hχ χ).symm
  obtain ⟨c, hc, hcn⟩ := GlobalTheory.T.exists_coeffs_adic_finite_of_span_eq_univ R S r s hs N.X zS hzn
  haveI : Fintype (Set.range rh) := hrf.fintype
  refine ⟨Fin r × Set.range rh, inferInstance, fun k => K k.2 * (s k.1 : Kb R),
    fun χ k => if (⟨rh χ, Set.mem_range_self χ⟩ : Set.range rh) = k.2 then c χ k.1 else 0, fun χ => ?_, fun n => ?_⟩
  · rw [key, Fintype.sum_prod_type]
    have hz : z0 χ = ∑ j, algebraMap R (Kb R) (c χ j) * (s j : Kb R) := by
      have := congrArg Subtype.val (hc χ)
      simpa [zS, Algebra.smul_def] using this
    rw [hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← IsScalarTower.algebraMap_apply]
    ring
  · refine (hcn n).subset fun χ hχ hall => hχ fun k => ?_
    dsimp only
    split_ifs
    · exact hall _
    · exact zero_mem _

theorem terms : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (N : GlobalTheory.Ex.NumD (Kb R)) (ν : GlobalTheory.Ex.NumOf D.toPre (Kb R) N) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (p : QkPt D.toPre (Kb R) (m ^ 2)) (q : N.QT (m ^ 2)), ν.QPt p q → ∃ (Jx : Type) (_ : Fintype Jx) (g : Jx → Kb R) (c : N.X → Jx → R), (∀ χ, N.txT m q χ = ∑ k, algebraMap (FractionRing R) (Kb R) (algebraMap R _ (c χ k)) * g k) ∧ ∀ n : ℕ, {χ | ¬ ∀ k, c χ k ∈ maximalIdeal R ^ n}.Finite := by
  intro R _ _ _ hB D N ν m hm hmu p q hq
  haveI : IsNoetherianRing R := hB.1.1
  obtain ⟨N', ν', q', S, hth, hq', hfin, hθ, hσ, hthS, hψS, hψn⟩ := GlobalTheory.T.exists_integral_gauge_finite_extension R hB D N ν m hm hmu p
  haveI := hfin
  obtain ⟨I, hl, -, hI⟩ := GlobalTheory.GaugeHom.exists_hom R D.toPre (Kb R) (Kb R) (RingHom.id _) (RingHom.id_comp _) N N' ν ν' hth
  obtain ⟨e1, e2⟩ := hI (m ^ 2) p p q q' (GlobalTheory.SeriesCompare.qkExt_id p) hq hq'
  have htx : ∀ χ, N.txT m q χ = N'.txT m q' (I.e χ) := fun χ => by
    rw [I.txT_eq hm q q' e1 e2 χ, hl, Units.val_one, _root_.one_mul, RingHom.id_apply]
  obtain ⟨Jx, fJ, g, c, hc, hcn⟩ := core N' S m hm.pos q' hθ hσ hthS hψS hψn
  exact ⟨Jx, fJ, g, fun χ => c (I.e χ), fun χ => by rw [htx, hc], fun n => (hcn n).preimage I.e.injective.injOn⟩

end GlobalTheory.ThetaTermAdic
