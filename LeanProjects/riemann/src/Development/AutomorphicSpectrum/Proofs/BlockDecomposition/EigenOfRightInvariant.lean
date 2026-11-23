import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetUpperTriangularBlock

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.B3

variable {D : D7} {n : ℕ} {v : Pl D}

theorem term_eq {χ : (AE D)ˣ →* Circle} {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v} (hχ : GoodChi D χ v τ) {z : ℂ}
    {f : G D n → ℂ} (hf : IsLaw χ z f) (hK : ∀ k ∈ KAt D n v, ∀ g, f (g * k) = f g) {nb : hermA D n → G D n}
    (hnb : IsNMap nb) (C : Cut D n v) (g : G D n) (p₀ : PV D n v) {k₀ : GLoc D.sp.cm.sig (Jst D n) v}
    (hk₀ : k₀ ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) (e₀ : proj D.sp.cm.sig (Jst D n) v g = p₀ * k₀)
    {k : G D n} (hk : k ∈ KAt D n v) {x : hermA D n} (hx : x ∈ C.s) :
    f (g * (k * nb x)) = sphV D n v z (k₀ * proj D.sp.cm.sig (Jst D n) v (k * nb x)) * f g := by
  obtain ⟨p₁, k₁, hk₁, e₁⟩ := GlobalTheory.LocIntw.exists_mul_fin (GlobalTheory.LocIntw.exists_mul_adele D n) v
    (k₀ * proj D.sp.cm.sig (Jst D n) v (k * nb x))
  have hu : k * nb x ∈ atPts D.sp.cm.sig (Jst D n) {v} := mul_mem hk.2 (nb_mem_atPts hnb C hx)
  rw [shift hf hK g p₀ p₁ hk₀ hk₁ e₀ hu e₁, lawV, chi_one hχ hnb hk₀ hk₁ hk x p₁ e₁, e₁, Circle.coe_one, one_mul]
  congr 1
  exact (congrArg (fun r => npow r (z + (n : ℂ) / 2))
    (GlobalTheory.LocIntw.hgtUp_mul (GlobalTheory.LocIntw.isIwasawaUp_fin D n v) p₁ hk₁)).symm

theorem eigen_of_rightInvariant : SectionEigenfunctionMaximalCompact := by
  intro D n χ nb hnb v τ hχ C νv hν z c hc f hf hK g
  obtain ⟨p₀, k₀, hk₀, e₀⟩ := GlobalTheory.LocIntw.exists_mul_fin (GlobalTheory.LocIntw.exists_mul_adele D n) v
    (proj D.sp.cm.sig (Jst D n) v g)
  have hκ : emb D.sp.cm.sig (Jst D n) v k₀ ∈ KAt D n v :=
    ⟨GlobalTheory.LocIntw.emb_mem_KUpAd hk₀, by rw [← range_emb]; exact ⟨_, rfl⟩⟩
  have key : ∀ k : KAt D n v, cutR nb C f (g * k) =
      f g * (fun k : KAt D n v => ∑ x ∈ C.s, C.co x * sphV D n v z (proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x)))
        (⟨_, hκ⟩ * k) := by
    intro k
    simp only [PositivityTheory.Rg.Rsw.L.cutR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mul_assoc g, term_eq hχ hf hK hnb C g p₀ hk₀ e₀ k.2 hx]
    have e : proj D.sp.cm.sig (Jst D n) v ((((⟨_, hκ⟩ : KAt D n v) * k : KAt D n v) : G D n) * nb x) =
        k₀ * proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x) := by
      rw [Subgroup.coe_mul, mul_assoc, map_mul, proj_emb_self]
    rw [e]
    ring
  simp only [key]
  rw [integral_const_mul, integral_mul_left_eq_self
    (fun k : KAt D n v => ∑ x ∈ C.s, C.co x * sphV D n v z (proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x))) ⟨_, hκ⟩,
    hc, mul_comm]

end GlobalTheory.CompanionTheory.Jp.B3

end
