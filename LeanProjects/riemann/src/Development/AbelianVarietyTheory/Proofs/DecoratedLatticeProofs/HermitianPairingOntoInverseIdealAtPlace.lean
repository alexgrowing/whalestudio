import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLatticeDualZIdealMul
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorDisjointSupportSmulAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotLineLatAtZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSmulIntegralMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdeleSupportedAtPlaceNotIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeeSaw.HzOnto

open GlobalTheory.IwaPlace

variable {D : D7}

def pz (S : HSp D) (z x : Fin S.rank → D.host.E) : D.host.E := ∑ i, ∑ j, star (x i) * S.gram i j * z j

theorem pz_add (S : HSp D) (z x y : Fin S.rank → D.host.E) : pz S z (x + y) = pz S z x + pz S z y := by
  simp only [pz, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem pz_smul (S : HSp D) (z x : Fin S.rank → D.host.E) (c : D.host.E) :
    pz S z (c • x) = star c * pz S z x := by
  simp only [pz, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def valSub (S : HSp D) (M : Lat S) (z : Fin S.rank → D.host.E) : Submodule (𝓞 D.host.E) D.host.E where
  carrier := {a | ∃ x ∈ M, pz S z x = a}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, M.add_mem hx hy, pz_add S z x y⟩
  zero_mem' := ⟨0, M.zero_mem, by simp [pz]⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    obtain ⟨c', hc'⟩ := GlobalTheory.FinPl.LatMem.star_int c
    refine ⟨c' • x, M.smul_mem c' hx, ?_⟩
    have e : (c' • x : Fin S.rank → D.host.E) = (c' : D.host.E) • x := by
      funext i; exact (algebraMap_smul D.host.E c' (x i)).symm
    rw [e, pz_smul, hc', star_star, Algebra.smul_def]

theorem valSub_isFractional (S : HSp D) (M : Lat S) (hM : IsSelfDualC S M) (z : Fin S.rank → D.host.E) :
    IsFractional (𝓞 D.host.E)⁰ (valSub S M z) := by
  have hsp : Submodule.span D.host.E (M : Set (Fin S.rank → D.host.E)) = ⊤ := hM.1.span_eq_top
  have hz : z ∈ Submodule.span D.host.E (M : Set (Fin S.rank → D.host.E)) := by rw [hsp]; trivial
  obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (𝓞 D.host.E)⁰ D.host.E (M : Set _) z hz
  rw [Submodule.span_eq] at hd
  refine ⟨d, d.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨b, hb⟩ := (hM.2 _).1 hd x hx
  refine ⟨b, ?_⟩
  change (b : D.host.E) = (d : 𝓞 D.host.E) • pz S z x
  rw [hb, Algebra.smul_def]
  simp only [pz, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e : (d • z) j = algebraMap (𝓞 D.host.E) D.host.E d * z j := by
    change ((d : 𝓞 D.host.E) • z) j = _
    rw [Pi.smul_apply, Algebra.smul_def]
  rw [e]
  ring

def valIdl (S : HSp D) (M : Lat S) (hM : IsSelfDualC S M) (z : Fin S.rank → D.host.E) : FI D :=
  ⟨valSub S M z, valSub_isFractional S M hM z⟩

theorem mem_valIdl {S : HSp D} {M : Lat S} {hM : IsSelfDualC S M} {z : Fin S.rank → D.host.E} {a : D.host.E} :
    a ∈ valIdl S M hM z ↔ ∃ x ∈ M, pz S z x = a := Iff.rfl

theorem hermAt_gen (S : HSp D) (z x : Fin S.rank → D.host.E) (α : Af D.host.F) :
    hermAt S (ratV z) (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) =
      pairA D.host.F 0 α ⊗ₜ[D.host.F] pz S z x := by
  simp only [hermAt, pz, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change (pairA D.host.F 0 α ⊗ₜ[D.host.F] star (1 * x i)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram i j) *
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] z j) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul]

theorem hermAt_add (S : HSp D) (w x y : Fin S.rank → AE D) : hermAt S w (x + y) = hermAt S w x + hermAt S w y := by
  simp only [hermAt, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hermAt_zero (S : HSp D) (w : Fin S.rank → AE D) : hermAt S w 0 = 0 := by
  simp [hermAt]

theorem hermAt_neg (S : HSp D) (w x : Fin S.rank → AE D) : hermAt S w (-x) = -hermAt S w x := by
  simp [hermAt, Finset.sum_neg_distrib]

theorem cA_sum_eq (S : HSp D) (Z y : Fin S.rank → AE D) :
    cA D (∑ l, (∑ m, cA D (Z m) * gA S m l) * y l) = hermAt S Z y := by
  have hg : ∀ m l, cA D (gA S m l) = gA S l m := fun m l => congrFun (congrFun (adj_gA S) l) m
  simp only [map_sum, map_mul, cA_cA, hermAt, Finset.sum_mul, hg]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_not_intAt (v : Pl D) : ∃ u ∈ idAt D (· = v), u ∉ intAt D (· = v) := GlobalTheory.T.exists_adele_supportedAt_place_not_integral D v

theorem exists_not_mem_idV (v : Pl D) {𝔠 : FI D} (h : 𝔠 ≠ 0) : ∃ t ∈ idAt D (· = v), t ∉ idV 𝔠 v := by
  obtain ⟨x, hx, hg⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔠 h
  obtain ⟨u, hu, hnu⟩ := exists_not_intAt (D := D) v
  have ht : incA D x * u ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hu
  refine ⟨incA D x * u, ht, fun hm => hnu ?_⟩
  have := ((hg _).1 hm).1
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul] at this

theorem hz_onto : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L : HSp D) (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D), IsSelfDualC S M → LineId o ζ M 𝔠 v → 𝔠 ≠ 0 →
      ∀ g ∈ idV 𝔠⁻¹ v, ∃ y ∈ latV S M (· = v), cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) = g := by
  intro D ψ hψ S A L o ζ M 𝔠 v hM hL h𝔠 g hg
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hSD := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S M v hM
  set z := vecB o ζ with hzdef
  set 𝔦 : FI D := valIdl S M hM z with h𝔦def
  have hval : ∀ x ∈ latV S M (· = v), hermAt S (ratV z) x ∈ idV 𝔦 v := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, hα, a, ha, m, hm, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      rw [hermAt_gen]
      exact AddSubgroup.subset_closure ⟨α, hαi, hα, _, mem_valIdl.2 ⟨m, hm, rfl⟩, rfl⟩
    | zero => rw [hermAt_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [hermAt_add]; exact add_mem hx hy
    | neg x _ hx => rw [hermAt_neg]; exact neg_mem hx
  have hkey : ∀ t ∈ idAt D (· = v),
      t ∈ idV 𝔠 v ↔ ∀ x ∈ latV S M (· = v), t * hermAt S (ratV z) x ∈ intAt D (· = v) := by
    intro t ht
    rw [← hL t ht, hSD.2.2 (t • ratV z) (fun i => Ideal.mul_mem_right _ _ ht)]
    simp only [GlobalTheory.IwaPlace.SDStable.hermAt_smul_left]
  have h𝔦 : 𝔦 ≠ 0 := by
    intro h0
    obtain ⟨t, ht, htn⟩ := exists_not_mem_idV v h𝔠
    refine htn ((hkey t ht).2 fun x hx => ?_)
    have := hval x hx
    rw [h0, idV_zero, AddSubgroup.mem_bot] at this
    rw [this, mul_zero]
    exact ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  have hsub : ∀ a ∈ idV 𝔦⁻¹ v, a ∈ idV 𝔠 v := by
    intro a ha
    have haA := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ a ha
    refine (hkey a haA).2 fun x hx => ?_
    have e := (h2 𝔦 1 h𝔦 one_ne_zero a haA).2 (by rwa [one_mul])
    exact (h1 _).1 (e _ (hval x hx))
  have hgA := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ g hg
  have hg' : g ∈ idV 𝔦 v := by
    have e := (h2 𝔦⁻¹ 1 (inv_ne_zero h𝔦) one_ne_zero g hgA).1 fun a ha =>
      (h2 𝔠 1 h𝔠 one_ne_zero g hgA).2 (by rwa [one_mul]) a (hsub a ha)
    rwa [one_mul, inv_inv] at e
  have honto : ∀ b ∈ idV 𝔦 v, ∃ y ∈ latV S M (· = v), hermAt S (ratV z) y = b := by
    intro b hb
    induction hb using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hαi, hα, a, ha, rfl⟩ := hw
      obtain ⟨m, hm, rfl⟩ := mem_valIdl.1 ha
      exact ⟨_, AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, m, hm, rfl⟩, hermAt_gen S z m α⟩
    | zero => exact ⟨0, zero_mem _, hermAt_zero S _⟩
    | add b b' _ _ hb hb' =>
      obtain ⟨y, hy, e⟩ := hb
      obtain ⟨y', hy', e'⟩ := hb'
      exact ⟨y + y', add_mem hy hy', by rw [hermAt_add, e, e']⟩
    | neg b _ hb =>
      obtain ⟨y, hy, e⟩ := hb
      exact ⟨-y, neg_mem hy, by rw [hermAt_neg, e]⟩
  obtain ⟨y, hy, e⟩ := honto g hg'
  exact ⟨y, hy, by rw [cA_sum_eq, e]⟩

end GlobalTheory.SeeSaw.HzOnto

end
