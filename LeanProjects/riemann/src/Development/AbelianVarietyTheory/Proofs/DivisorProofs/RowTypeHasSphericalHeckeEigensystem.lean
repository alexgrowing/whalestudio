import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypeExistsBaseLevelVectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.RowEig

open Formalism.IndefR.principalLevelFrame

variable {D : D7}

def rtV (V : HSp D) : GA D V →* Module.End ℂ (GA D V → ℂ) where
  toFun g := { toFun := fun f h => f (h * g), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  map_one' := by ext f h; simp
  map_mul' g g' := by ext f h; simp [mul_assoc]

theorem rtV_apply (V : HSp D) (g : GA D V) (f : GA D V → ℂ) (h : GA D V) : rtV V g f h = f (h * g) := rfl

variable {V : HSp D} {n : ℕ}

theorem pre_psi (Q : RowPsi V n) (z : Formalism.AUTREP.GAf D.host.E n) : pre Q (Q.ψ z) = z := by
  have h : ∃ x, Q.ψ x = Q.ψ z := ⟨z, rfl⟩
  unfold pre
  rw [dif_pos h]
  exact Q.inj h.choose_spec

theorem psi_pre (Q : RowPsi V n) {γ : GA D V} (hγ : γ ∈ GfC V) : Q.ψ (pre Q γ) = γ := by
  obtain ⟨h, hh⟩ := Q.onto γ hγ
  have h' : ∃ x, Q.ψ x = γ := ⟨h, hh⟩
  unfold pre
  rw [dif_pos h']
  exact h'.choose_spec

open Classical in

def lift (Q : RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) : GA D V → ℂ :=
  fun g => if g ∈ GfC V then x (pre Q g) else 0

theorem rtV_lift_psi (Q : RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) {γ : GA D V} (hγ : γ ∈ GfC V)
    (y : Formalism.AUTREP.GAf D.host.E n) : rtV V γ (lift Q x) (Q.ψ y) = x (y * pre Q γ) := by
  rw [rtV_apply]
  have hmem : Q.ψ y * γ ∈ GfC V := (GfC V).mul_mem (Q.into y) hγ
  have heq : Q.ψ y * γ = Q.ψ (y * pre Q γ) := by rw [map_mul, psi_pre Q hγ]
  unfold lift
  rw [if_pos hmem, heq, pre_psi]

theorem lift_fixed (Q : RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) (K : Set (GA D V)) (hK : K ⊆ GfC V)
    (hx : ∀ κ, Q.ψ κ ∈ K → Formalism.L2.NG.rt D.host.E n κ x = x) : ∀ k ∈ K, rtV V k (lift Q x) = lift Q x := by
  intro k hk
  have hkG : k ∈ GfC V := hK hk
  funext g
  rw [rtV_apply]
  by_cases hg : g ∈ GfC V
  · have hgk : g * k ∈ GfC V := (GfC V).mul_mem hg hkG
    have heq : g * k = Q.ψ (pre Q g * pre Q k) := by rw [map_mul, psi_pre Q hg, psi_pre Q hkG]
    have hfix := congrFun (hx (pre Q k) (by rw [psi_pre Q hkG]; exact hk)) (pre Q g)
    unfold lift
    rw [if_pos hgk, if_pos hg, heq, pre_psi]
    exact hfix
  · have hgk : g * k ∉ GfC V := fun h => hg (by simpa using (GfC V).mul_mem h ((GfC V).inv_mem hkG))
    unfold lift
    rw [if_neg hgk, if_neg hg]

theorem heckeOperator_apply' (Q : RowPsi V n) (B : Finset (GA D V)) (x : Formalism.AUTREP.GAf D.host.E n → ℂ) (y : Formalism.AUTREP.GAf D.host.E n) :
    Hecke₃ Q B x y = ∑ γ ∈ B, x (y * pre Q γ) := by
  simp [Hecke₃, heckeG, LinearMap.sum_apply, Finset.sum_apply, Formalism.L2.NG.rt]

theorem sph_mem_GfC {P : Pl D.host.E} {d : List ℤ} {B : Finset (GA D V)} (hB : SphOp V P d B) : ∀ γ ∈ B, γ ∈ GfC V := by
  obtain ⟨e, f, ϖ, α, -, -, -, -, -, -, -, -, -, -, hR⟩ := hB
  exact fun γ hγ => (hR.1 γ hγ).1

theorem hyp_sub (P : Pl D.host.E) : hyp V P ⊆ GfC V := fun k hk => hk.1.1

theorem heckeOperator_eq_of_spherical (Q : RowPsi V n) (P : Pl D.host.E) (d : List ℤ) (B B' : Finset (GA D V)) (hB : SphOp V P d B)
    (hB' : SphOp V P d B') (x : Formalism.AUTREP.GAf D.host.E n → ℂ) (hx : ∀ κ, Q.ψ κ ∈ hyp V P → Formalism.L2.NG.rt D.host.E n κ x = x) :
    Hecke₃ Q B x = Hecke₃ Q B' x := by
  have hu := lift_fixed Q x (hyp V P) (hyp_sub P) hx
  have e1 := ((GlobalTheory.SphLabelOps.label_operators V P).1 d B hB).2 (GA D V → ℂ) (rtV V) (lift Q x) hu
  have e2 := ((GlobalTheory.SphLabelOps.label_operators V P).1 d B' hB').2 (GA D V → ℂ) (rtV V) (lift Q x) hu
  have e := e1.trans e2.symm
  funext y
  have ey := congrFun e (Q.ψ y)
  rw [Finset.sum_apply, Finset.sum_apply] at ey
  rw [heckeOperator_apply', heckeOperator_apply']
  rw [Finset.sum_congr rfl (fun γ hγ => rtV_lift_psi Q x (sph_mem_GfC hB γ hγ) y),
    Finset.sum_congr rfl (fun γ hγ => rtV_lift_psi Q x (sph_mem_GfC hB' γ hγ) y)] at ey
  exact ey

theorem sph_of_full {J : Set (GA D V)} {χ : GA D V → ℂ} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : Pl D.host.E}
    {d : List ℤ} {B : Finset (GA D V)} (h : Hecke₂ V J χ S P d B) : SphOp V P d B := by
  obtain ⟨e, f, ϖ, α, -, hPI, h1, h2, hd, hJ, -, hα, hdiv, hR, hcos⟩ := h
  have hset : {k | k ∈ J ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := by
    ext k
    exact ⟨fun ⟨a, b⟩ => ⟨(hJ k b).1 a, b⟩, fun ⟨a, b⟩ => ⟨(hJ k b).2 a, b⟩⟩
  rw [hset] at hcos
  exact ⟨e, f, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), hPI, h1, h2, hd, fun _ _ => Iff.rfl,
    fun _ _ _ => rfl, hα, hdiv, hR, hcos⟩

end GlobalTheory.RowEig

namespace GlobalTheory.RowEig

open Formalism.IndefR.principalLevelFrame

set_option maxHeartbeats 1000000 in

theorem row_type_eig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∀ i0, ∃ c, principalLevelFrame.IsEigOf (PW i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF π c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hCore hX SF hSF n hF PY PW hPY hPW π hπ i0
  classical
  have hsc : ∀ Pr d B, SphOp (Wc D i0) Pr d B → ∃ a : ℂ, ∀ x ∈ π.S,
      (∀ κ, (PW i0).ψ κ ∈ hyp (Wc D i0) Pr → Formalism.L2.NG.rt D.host.E n κ x = x) → Hecke₃ (PW i0) B x = a • x :=
    fun Pr d B h => GlobalTheory.T.sphericalHecke_scalar_on_spherical_vectors hF (PW i0) (hPW i0) π Pr d B h

  obtain ⟨c0, hBase⟩ := hCore.lev.βW i0
  rw [one_pow] at hBase

  have hfix : ∀ Pr d B, Hecke₂ (Wc D i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A))))
      (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF Pr d B → ∀ x,
      IsTypeVec ((PW i0).ψ ⁻¹' levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A))))
        (fun κ => levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A))) ((PW i0).ψ κ)) x →
      ∀ κ, (PW i0).ψ κ ∈ hyp (Wc D i0) Pr → Formalism.L2.NG.rt D.host.E n κ x = x := by
    intro Pr d B hB x hx κ hκ
    have hOff : OffS D SF Pr := by
      obtain ⟨e, f, ϖ, α, h, -⟩ := hB
      exact h
    have hGood : Good R A.μ0 Pr := ((GlobalTheory.GoodPrimes.good_primes R F hCore.lev).2.2.1 SF hSF Pr).mp hOff
    have hN : ((1 : ℕ) : 𝓞 D.host.E) ∉ Pr.asIdeal := by
      rw [Nat.cast_one]
      exact (Ideal.ne_top_iff_one _).mp Pr.isPrime.ne_top
    have hL := (GlobalTheory.LevOp.level_operators (Wc D i0) (R.βW i0) (R.ΛW i0) 1 (R.datWp i0 (R.levL F false (sg0 D A))) hBase Pr hN
      (fun PP hPP => by
        rcases hPP with h | h
        · exact hGood PP (Or.inl h)
        · exact absurd h (Finset.notMem_empty PP))).1 _ hκ
    have := hx κ hL.1
    rw [this]
    dsimp only
    rw [hL.2, one_smul]
  refine ⟨fun Pr d => if h : ∃ B, Hecke₂ (Wc D i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A))))
      (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF Pr d B then
      (hsc Pr d h.choose (sph_of_full h.choose_spec)).choose else 0, ?_, ?_, ?_⟩
  · exact GlobalTheory.T.rowType_exists_baseLevel_vector R F hOk hCore hX hF PY PW hPY hPW π hπ i0
  · intro Pr d B hB x hxS hx
    have hex : ∃ B, Hecke₂ (Wc D i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A))))
      (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF Pr d B := ⟨B, hB⟩
    have hxf := hfix Pr d B hB x hx
    dsimp only
    rw [dif_pos hex, heckeOperator_eq_of_spherical (PW i0) Pr d B hex.choose (sph_of_full hB) (sph_of_full hex.choose_spec) x hxf]
    exact (hsc Pr d hex.choose (sph_of_full hex.choose_spec)).choose_spec x hxS hxf
  · intro Pr d hne
    exact dif_neg hne

end GlobalTheory.RowEig
