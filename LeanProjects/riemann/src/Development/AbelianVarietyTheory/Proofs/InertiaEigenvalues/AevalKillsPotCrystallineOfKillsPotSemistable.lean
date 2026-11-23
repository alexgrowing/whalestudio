import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContMapRepIotaOQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepDecompositionInduced
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

open TensorProduct GlobalTheory.Pst GlobalTheory.PstLine

namespace GlobalTheory.PcrisPst

theorem fixed_of_mem_Dpcris {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K K' L : FinExt l) (h : K.1 ≤ K'.1)
    (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c')
    {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    (ρ : Representation ↥L.1 ↥(GK K) V) {d : V ⊗[ℚ_[l]] P.R.B} (hd : d ∈ (pc P h hN hF hS).Dpcris ρ)
    (x : ↥(GKin h)) : actVB (P.PD K) ρ (x : ↥(GK K)) d = d := by
  simp only [Formalism.WeaklyAdmissibleFiltrations.PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hd
  have := hd x
  have e : actVB (pc P h hN hF hS).PD' ((pc P h hN hF hS).resH ρ) x = actVB (P.PD K) ρ (x : ↥(GK K)) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro v b
    have := (pc P h hN hF hS).actB_eq x b
    simp [actVB, Formalism.WeaklyAdmissibleFiltrations.PotCrysData.resH] at this ⊢
    rw [this]
    rfl
  rw [← e]; exact this

section Map

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {f : V →ₗ[ℚ_[l]] V'} {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}

theorem stMap_crisIncl_pow (he : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : ↥(GK K)) (n : ℕ)
    (x : V ⊗[ℚ_[l]] P.R.B) :
    stMap P f (crisIncl P ↥L.1 V ((actVB (P.PD K) ρ g ^ n) x)) =
      (stRep P ρ' g ^ n) (stMap P f (crisIncl P ↥L.1 V x)) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← stRep_crisIncl,
      stMap_stRep P he, ih]

theorem stMap_crisIncl_aeval {hL : L.1 ≤ L'.1} (hm : IsMor hL f ρ ρ') (g : ↥(GK K)) (q : (↥L.1)[X])
    (x : V ⊗[ℚ_[l]] P.R.B) :
    stMap P f (crisIncl P ↥L.1 V (Polynomial.aeval (actVB (P.PD K) ρ g) q x)) =
      Polynomial.aeval (stRep P ρ' g) (q.map (IntermediateField.inclusion hL).toRingHom)
        (stMap P f (crisIncl P ↥L.1 V x)) := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hr]
  | monomial n a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, stMap_smul P f (hm.smul a),
      stMap_crisIncl_pow P hm.equiv]
    rfl

end Map

theorem aeval_eq_zero_of_kills_Dpst : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K K' L L' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (hL : L.1 ≤ L'.1) {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V'] (ρ : Representation ↥L.1 ↥(GK K) V) (ρ' : Representation ↥L'.1 ↥(GK K) V') (f : V →ₗ[ℚ_[l]] V'), Function.Injective f → GlobalTheory.PstLine.IsMor hL f ρ ρ' → ∀ (g : ↥(GK K)) (q : (↥L.1)[X]), (∀ y ∈ GlobalTheory.Pst.Dpst P ρ', Polynomial.aeval (GlobalTheory.Pst.stRep P ρ' g) (q.map (IntermediateField.inclusion hL).toRingHom) y = 0) → ∀ d ∈ (pc P h hN hF hS).Dpcris ρ, Polynomial.aeval (actVB (P.PD K) ρ g) q d = 0 := by
  intro l _ P K K' L L' h hN hF hS hL V V' _ _ _ _ _ _ _ _ ρ ρ' f hf hm g q hq d hd
  have hmem : crisIncl P ↥L.1 V d ∈ Dpst P ρ :=
    (mem_Dpst P ρ).2 ⟨K', fun g' hg' => by
      rw [stRep_crisIncl, fixed_of_mem_Dpcris P K K' L h hN hF hS ρ hd ⟨g', hg'⟩]⟩
  have hinj : Function.Injective (stMap P f) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  apply crisIncl_injective P (LL := ↥L.1) (V := V)
  apply hinj
  rw [stMap_crisIncl_aeval P hm g q d, map_zero, map_zero]
  exact hq _ (stMap_mem_Dpst P hm.equiv hmem)

end GlobalTheory.PcrisPst
