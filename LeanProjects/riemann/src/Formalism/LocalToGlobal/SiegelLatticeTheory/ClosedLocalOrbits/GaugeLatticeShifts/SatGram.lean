import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountIdx
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ColPhaseCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCoreGamProdSum
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCorePsiNatEquiv
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLoc

noncomputable section

open scoped Classical TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.UG Formalism.UG.P Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf.SatGram

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Red

variable {D : D7} (X : HidaSetting D)

def gPl : Type := {v : HeightOneSpectrum (𝓞 X.B.I.F) // ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal}

theorem g_ne_zero : X.B.g ≠ 0 := by
  rw [X.g_eq]
  exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

instance : Fintype (gPl X) :=
  (Formalism.L2.SG.TypedSets.finite_over X.B.I.F X.B.g (g_ne_zero X)).fintype

def IsRedAt (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (r : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F →+* v.adicCompletion X.B.I.F) : Prop :=
  r (prV v X.ew) = 1 ∧ (∀ c : v.adicCompletion X.B.I.F, r ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] c) = c) ∧
    (∀ x ∈ intV X.B.I.E v, r x ∈ v.adicCompletionIntegers X.B.I.F) ∧
    ∀ x, prV v X.ew * x = x → x = ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] r x) * prV v X.ew

def RedExists : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal → ∃ r, IsRedAt X v r

def GUnif : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
    Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) = WithZero.exp (-1 : ℤ)

def GResCard : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 X.B.I.F)) (i : Fin 2), ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
    Nat.card (𝓞 X.B.I.F ⧸ v.asIdeal) = D.host.g i

def PsiCond : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
    ∃ o ∈ v.adicCompletionIntegers X.B.I.F,
      X.psiEf (divN X.B.I X.B.g (X.ew * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] afsplitI v o))) ≠ 1

variable {X}

def rV (hR : RedExists X) (v : gPl X) :
    X.B.I.E ⊗[X.B.I.F] v.1.adicCompletion X.B.I.F →+* v.1.adicCompletion X.B.I.F :=
  (hR v.1 v.2).choose

theorem rV_spec (hR : RedExists X) (v : gPl X) : IsRedAt X v.1 (rV hR v) := (hR v.1 v.2).choose_spec

def rO (hR : RedExists X) (v : gPl X) :
    ↥(IntAf X.B.I.F X.B.I.E) →+* ↥(v.1.adicCompletionIntegers X.B.I.F) :=
  ((rV hR v).comp ((prV (E := X.B.I.E) v.1).comp (IntAf X.B.I.F X.B.I.E).subtype)).codRestrict
    (v.1.adicCompletionIntegers X.B.I.F)
    (fun x => (rV_spec hR v).2.2.1 _ (afsplit_prV_int v.1 x.1 x.2))

theorem rO_coe (hR : RedExists X) (v : gPl X) (x : ↥(IntAf X.B.I.F X.B.I.E)) :
    ((rO hR v x : ↥(v.1.adicCompletionIntegers X.B.I.F)) : v.1.adicCompletion X.B.I.F) =
      rV hR v (prV (E := X.B.I.E) v.1 (x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) := rfl

def resV (hR : RedExists X) (v : gPl X) :
    ↥(IntAf X.B.I.F X.B.I.E) →+* IsLocalRing.ResidueField ↥(v.1.adicCompletionIntegers X.B.I.F) :=
  (IsLocalRing.residue _).comp (rO hR v)

end Red

section Red2

variable {D : D7} {X : HidaSetting D}

theorem prV_algebraMap (v : HeightOneSpectrum (𝓞 X.B.I.F)) (c : X.B.I.F) :
    prV (E := X.B.I.E) v (algebraMap X.B.I.F (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) c) =
      (1 : X.B.I.E) ⊗ₜ[X.B.I.F] algebraMap X.B.I.F (v.adicCompletion X.B.I.F) c := by
  first
  | (rw [← Algebra.TensorProduct.algebraMap_apply']
     exact (Algebra.TensorProduct.map (AlgHom.id X.B.I.F X.B.I.E) (evalV X.B.I.F v)).commutes c)
  | (simp only [Formalism.UG.prV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
     rw [← mul_one (algebraMap X.B.I.F X.B.I.E c), ← Algebra.smul_def, TensorProduct.smul_tmul,
       Algebra.smul_def, mul_one])

theorem le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  · obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = WithZero.exp n := ⟨WithZero.log x, (WithZero.exp_log hx).symm⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem tens_one_mem_intV (v : HeightOneSpectrum (𝓞 X.B.I.F)) (c : v.adicCompletion X.B.I.F)
    (hc : c ∈ v.adicCompletionIntegers X.B.I.F) : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] c ∈ intV X.B.I.E v :=
  Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)

theorem one_tens_mem_IntAf (a : Af X.B.I.F) (ha : a ∈ intAd X.B.I.F) :
    (1 : X.B.I.E) ⊗ₜ[X.B.I.F] a ∈ IntAf X.B.I.F X.B.I.E :=
  Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

theorem ew_ew : X.ew * X.ew = X.ew := X.ew_idem

variable (hR : RedExists X) (hU : GUnif X)

theorem resV_ew (v : gPl X) (x : ↥(IntAf X.B.I.F X.B.I.E)) :
    resV hR v ⟨X.ew * x, mul_mem X.ew_int x.2⟩ = resV hR v x := by
  unfold resV
  simp only [RingHom.comp_apply]
  congr 1
  apply Subtype.ext
  simp only [rO_coe, map_mul, (rV_spec hR v).1, one_mul]

include hU in
theorem g_mem_max (v : gPl X) :
    ((X.B.g : ℕ) : ↥(v.1.adicCompletionIntegers X.B.I.F)) ∈
      IsLocalRing.maximalIdeal ↥(v.1.adicCompletionIntegers X.B.I.F) := by
  rw [Formalism.BasicNotions.Examples₂.adicInt_mem_max_iff]
  have : (((X.B.g : ℕ) : ↥(v.1.adicCompletionIntegers X.B.I.F)) : v.1.adicCompletion X.B.I.F) =
      ((X.B.g : ℕ) : v.1.adicCompletion X.B.I.F) := by push_cast; rfl
  rw [this, hU v.1 v.2, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

include hU in
theorem resV_ker_of (x : ↥(IntAf X.B.I.F X.B.I.E)) (hx : ZMod' X.B.I X.B.g (X.ew * x)) (v : gPl X) :
    resV hR v x = 0 := by
  obtain ⟨t, ht, he⟩ := hx
  rw [← resV_ew hR v x]
  have e : (⟨X.ew * x, mul_mem X.ew_int x.2⟩ : ↥(IntAf X.B.I.F X.B.I.E)) =
      ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) * ⟨t, ht⟩ := Subtype.ext (by push_cast; exact he)
  rw [e, map_mul, map_natCast]
  have h0 : ((X.B.g : ℕ) : IsLocalRing.ResidueField ↥(v.1.adicCompletionIntegers X.B.I.F)) = 0 := by
    rw [← map_natCast (IsLocalRing.residue ↥(v.1.adicCompletionIntegers X.B.I.F)),
      IsLocalRing.residue_eq_zero_iff]
    exact g_mem_max hU v
  rw [h0, zero_mul]

include hU in
theorem ker_resV (x : ↥(IntAf X.B.I.F X.B.I.E)) (hx : ∀ v, resV hR v x = 0) :
    ZMod' X.B.I X.B.g (X.ew * x) := by
  have hg := g_ne_zero X
  set y := X.ew * (x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) with hy
  have hyI : y ∈ IntAf X.B.I.F X.B.I.E := mul_mem X.ew_int x.2
  refine ⟨divN X.B.I X.B.g y, ?_, (Formalism.L2.SG.Pf.unitaryCongruence.gmul_divN X.B.I X.B.g hg y).symm⟩
  apply Formalism.MainNotions.Gaps.CC.Idx.mem_S_of_loc
  intro w
  have hpr : prV (E := X.B.I.E) w (divN X.B.I X.B.g y) =
      ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] ((X.B.g : ℕ) : w.adicCompletion X.B.I.F)⁻¹) * prV (E := X.B.I.E) w y := by
    unfold divN
    rw [map_mul, prV_algebraMap, map_inv₀, map_natCast]
  rw [hpr]
  by_cases hw : ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ w.asIdeal
  · let v : gPl X := ⟨w, hw⟩
    have hs := rV_spec hR v
    set e := prV (E := X.B.I.E) w X.ew with he
    have hey : e * prV (E := X.B.I.E) w y = prV (E := X.B.I.E) w y := by
      rw [he, hy, ← map_mul, ← mul_assoc, ew_ew]
    have hdec := hs.2.2.2 _ hey
    have hr : rV hR v (prV (E := X.B.I.E) w y) = ((rO hR v x : ↥(w.adicCompletionIntegers X.B.I.F)) : w.adicCompletion X.B.I.F) := by
      rw [rO_coe, hy, map_mul, map_mul, hs.1, one_mul]
    set c := rV hR v (prV (E := X.B.I.E) w y) with hc
    have hcmax : (rO hR v x) ∈ IsLocalRing.maximalIdeal ↥(w.adicCompletionIntegers X.B.I.F) := by
      rw [← IsLocalRing.residue_eq_zero_iff]; exact hx v
    have hcv : Valued.v c ≤ WithZero.exp (-1 : ℤ) := by
      rw [hr]; exact le_exp_neg_one ((Formalism.BasicNotions.Examples₂.adicInt_mem_max_iff w _).1 hcmax)
    have hgv := hU w hw
    have hint : ((X.B.g : ℕ) : w.adicCompletion X.B.I.F)⁻¹ * c ∈ w.adicCompletionIntegers X.B.I.F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hgv]
      calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v c ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1 : ℤ) :=
            by gcongr
        _ = 1 := inv_mul_cancel₀ (WithZero.exp_ne_zero)
    rw [hdec, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact mul_mem (tens_one_mem_intV w _ hint) (afsplit_prV_int w X.ew X.ew_int)
  · have h1 : Valued.v ((X.B.g : ℕ) : w.adicCompletion X.B.I.F) = 1 := by
      have := Formalism.MainNotions.Gaps.LG.sc_val_one w ((X.B.g : ℕ) : 𝓞 X.B.I.F) hw
      simpa using this
    have hint : ((X.B.g : ℕ) : w.adicCompletion X.B.I.F)⁻¹ ∈ w.adicCompletionIntegers X.B.I.F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]
    exact mul_mem (tens_one_mem_intV w _ hint) (afsplit_prV_int w y hyI)

theorem resV_joint : Function.Surjective
    (fun (x : ↥(IntAf X.B.I.F X.B.I.E)) (v : gPl X) => resV hR v x) := by
  intro b
  choose o ho using fun v : gPl X => IsLocalRing.residue_surjective (b v)
  refine ⟨⟨∑ v : gPl X, (1 : X.B.I.E) ⊗ₜ[X.B.I.F] afsplitI v.1 (o v : v.1.adicCompletion X.B.I.F),
    Subring.sum_mem _ fun v _ => one_tens_mem_IntAf _ (afsplitI_mem_intAd v.1 _ (o v).2)⟩, ?_⟩
  funext w
  show (IsLocalRing.residue _) (rO hR w _) = b w
  rw [← ho w]
  congr 1
  apply Subtype.ext
  rw [rO_coe]
  show rV hR w (prV (E := X.B.I.E) w.1 (∑ v : gPl X, (1 : X.B.I.E) ⊗ₜ[X.B.I.F] afsplitI v.1 (o v : v.1.adicCompletion X.B.I.F))) = _
  rw [map_sum, Finset.sum_eq_single w]
  · rw [afsplit_prV_tmul, afsplitI_self]; exact (rV_spec hR w).2.1 _
  · intro v _ hvw
    rw [afsplit_prV_tmul, afsplitI_ne v.1 w.1 (fun h => hvw (Subtype.ext h.symm)), TensorProduct.tmul_zero]
  · intro h; exact absurd (Finset.mem_univ w) h

end Red2

section Psi

variable {D : D7} (X : HidaSetting D)

def psiLoc (v : HeightOneSpectrum (𝓞 X.B.I.F)) (o : v.adicCompletion X.B.I.F) : ℂ :=
  X.psiEf (divN X.B.I X.B.g (X.ew * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] afsplitI v o)))

variable {X}

theorem psiEf_zero : X.psiEf 0 = 1 := X.psiEf_int 0 (zero_mem _)

theorem psiLoc_add (v : HeightOneSpectrum (𝓞 X.B.I.F)) (a b : v.adicCompletion X.B.I.F) :
    psiLoc X v (a + b) = psiLoc X v a * psiLoc X v b := by
  simp only [psiLoc, map_add, TensorProduct.tmul_add, mul_add, Formalism.L2.SG.HidaSetting.divN, X.psiEf_add]

theorem psiLoc_zero (v : HeightOneSpectrum (𝓞 X.B.I.F)) : psiLoc X v 0 = 1 := by
  simp only [psiLoc, map_zero, TensorProduct.tmul_zero, mul_zero, Formalism.L2.SG.HidaSetting.divN, psiEf_zero]

theorem psiLoc_g (v : HeightOneSpectrum (𝓞 X.B.I.F)) (t : v.adicCompletion X.B.I.F)
    (ht : t ∈ v.adicCompletionIntegers X.B.I.F) :
    psiLoc X v (((X.B.g : ℕ) : v.adicCompletion X.B.I.F) * t) = 1 := by
  unfold psiLoc
  have e1 : ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) * t = ((X.B.g : ℕ) : X.B.I.F) • t := by
    rw [Algebra.smul_def, map_natCast]
  rw [e1, map_smul, TensorProduct.tmul_smul, Algebra.smul_def, map_natCast, mul_left_comm]
  refine Formalism.L2.SG.Pf.unitaryCongruence.psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (g_ne_zero X) ?_
  exact ⟨_, mul_mem X.ew_int (one_tens_mem_IntAf _ (afsplitI_mem_intAd v _ ht)), rfl⟩

variable (hR : RedExists X) (hU : GUnif X)

include hU in
theorem psiLoc_wd (v : gPl X) (a b : ↥(v.1.adicCompletionIntegers X.B.I.F))
    (h : IsLocalRing.residue _ a = IsLocalRing.residue _ b) :
    psiLoc X v.1 (a : v.1.adicCompletion X.B.I.F) = psiLoc X v.1 b := by
  have hm : a - b ∈ IsLocalRing.maximalIdeal ↥(v.1.adicCompletionIntegers X.B.I.F) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
  have hv : Valued.v (((a - b : ↥(v.1.adicCompletionIntegers X.B.I.F))) : v.1.adicCompletion X.B.I.F) ≤
      WithZero.exp (-1 : ℤ) := le_exp_neg_one ((Formalism.BasicNotions.Examples₂.adicInt_mem_max_iff v.1 _).1 hm)
  set t := ((X.B.g : ℕ) : v.1.adicCompletion X.B.I.F)⁻¹ *
    (((a - b : ↥(v.1.adicCompletionIntegers X.B.I.F))) : v.1.adicCompletion X.B.I.F) with htd
  have hgv := hU v.1 v.2
  have hg0 : ((X.B.g : ℕ) : v.1.adicCompletion X.B.I.F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hgv; exact WithZero.exp_ne_zero hgv.symm
  have ht : t ∈ v.1.adicCompletionIntegers X.B.I.F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, htd, map_mul, map_inv₀, hgv]
    calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v _ ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1 : ℤ) := by gcongr
      _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
  have e : (a : v.1.adicCompletion X.B.I.F) = b + ((X.B.g : ℕ) : v.1.adicCompletion X.B.I.F) * t := by
    rw [htd, ← mul_assoc, mul_inv_cancel₀ hg0, one_mul]; push_cast; ring
  rw [e, psiLoc_add, psiLoc_g v.1 t ht, mul_one]

def liftR (v : gPl X) (z : IsLocalRing.ResidueField ↥(v.1.adicCompletionIntegers X.B.I.F)) :
    ↥(v.1.adicCompletionIntegers X.B.I.F) :=
  (IsLocalRing.residue_surjective z).choose

theorem liftR_spec (v : gPl X) (z : IsLocalRing.ResidueField ↥(v.1.adicCompletionIntegers X.B.I.F)) :
    IsLocalRing.residue _ (liftR v z) = z := (IsLocalRing.residue_surjective z).choose_spec

def psiV (v : gPl X) : AddChar (IsLocalRing.ResidueField ↥(v.1.adicCompletionIntegers X.B.I.F)) ℂ where
  toFun z := psiLoc X v.1 (liftR v z : v.1.adicCompletion X.B.I.F)
  map_zero_eq_one' := by
    have := psiLoc_wd hU v (liftR v 0) 0 (by rw [liftR_spec, map_zero])
    rw [this]; push_cast; exact psiLoc_zero v.1
  map_add_eq_mul' a b := by
    have := psiLoc_wd hU v (liftR v (a + b)) (liftR v a + liftR v b)
      (by rw [liftR_spec, map_add, liftR_spec, liftR_spec])
    rw [this]; push_cast; exact psiLoc_add v.1 _ _

theorem psiV_apply (v : gPl X) (o : ↥(v.1.adicCompletionIntegers X.B.I.F)) :
    psiV hU v (IsLocalRing.residue _ o) = psiLoc X v.1 o :=
  psiLoc_wd hU v _ _ (liftR_spec v _)

theorem gi_mem (v : gPl X) : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.1.asIdeal := by
  have h : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ v.1.asIdeal := by
    rw [← Nat.cast_mul, ← X.g_eq]
    exact v.2
  rcases v.1.isPrime.mem_or_mem h with h0 | h1
  · exact ⟨0, h0⟩
  · exact ⟨1, h1⟩

theorem finite_res (hC : GResCard X) (v : gPl X) :
    Finite (IsLocalRing.ResidueField ↥(v.1.adicCompletionIntegers X.B.I.F)) := by
  obtain ⟨i, hi⟩ := gi_mem v
  apply Nat.finite_of_card_ne_zero
  rw [Formalism.MainNotions.Gaps.LG.fm_card_residue, hC v.1 i hi]
  exact (D.host.g_prime i).ne_zero

def sumS (o : ∀ v : gPl X, v.1.adicCompletion X.B.I.F) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
  ∑ v : gPl X, X.ew * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] afsplitI v.1 (o v))

theorem prV_sumS (o : ∀ v : gPl X, v.1.adicCompletion X.B.I.F) (w : gPl X) :
    prV (E := X.B.I.E) w.1 (sumS o) = prV (E := X.B.I.E) w.1 X.ew * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] o w) := by
  unfold sumS
  rw [map_sum, Finset.sum_eq_single w]
  · rw [map_mul, afsplit_prV_tmul, afsplitI_self]
  · intro v _ hvw
    rw [map_mul, afsplit_prV_tmul, afsplitI_ne v.1 w.1 (fun h => hvw (Subtype.ext h.symm)),
      TensorProduct.tmul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ w) h

theorem sumS_mem (o : ∀ v : gPl X, v.1.adicCompletion X.B.I.F)
    (ho : ∀ v, o v ∈ v.1.adicCompletionIntegers X.B.I.F) : sumS o ∈ IntAf X.B.I.F X.B.I.E :=
  Subring.sum_mem _ fun v _ => mul_mem X.ew_int (one_tens_mem_IntAf _ (afsplitI_mem_intAd v.1 _ (ho v)))

theorem psiEf_sum {ι : Type*} (s : Finset ι) (f : ι → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    X.psiEf (∑ i ∈ s, f i) = ∏ i ∈ s, X.psiEf (f i) := by
  classical
  refine Finset.induction_on s (by simp [psiEf_zero]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.prod_insert ha, X.psiEf_add, ih]

include hU in
theorem prod_local_char_eq_global (x : ↥(IntAf X.B.I.F X.B.I.E)) (hx : (x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = X.ew * x) :
    ∏ v : gPl X, psiV hU v (resV hR v x) = X.psiEf (divN X.B.I X.B.g x) := by
  set o : ∀ v : gPl X, ↥(v.1.adicCompletionIntegers X.B.I.F) := fun v => rO hR v x with ho
  have hlhs : ∀ v, psiV hU v (resV hR v x) = psiLoc X v.1 (o v) := fun v => psiV_apply hU v _
  simp_rw [hlhs]
  have hsum : X.psiEf (divN X.B.I X.B.g (sumS (fun v => (o v : v.1.adicCompletion X.B.I.F)))) =
      ∏ v : gPl X, psiLoc X v.1 (o v) := by
    unfold sumS divN; rw [Finset.mul_sum, psiEf_sum]; rfl
  rw [← hsum]
  set S := sumS (fun v => (o v : v.1.adicCompletion X.B.I.F)) with hS
  have hSI : S ∈ IntAf X.B.I.F X.B.I.E := sumS_mem _ (fun v => (o v).2)
  have hdI : (x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) - S ∈ IntAf X.B.I.F X.B.I.E := sub_mem x.2 hSI
  have hZ : ZMod' X.B.I X.B.g (X.ew * (((⟨_, hdI⟩ : ↥(IntAf X.B.I.F X.B.I.E))) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) := by
    apply ker_resV hR hU
    intro w
    have h1 : (⟨_, hdI⟩ : ↥(IntAf X.B.I.F X.B.I.E)) = x - ⟨S, hSI⟩ := rfl
    rw [h1, map_sub, sub_eq_zero]
    show IsLocalRing.residue _ (rO hR w x) = IsLocalRing.residue _ (rO hR w ⟨S, hSI⟩)
    congr 1
    apply Subtype.ext
    rw [rO_coe, rO_coe]
    show _ = rV hR w (prV (E := X.B.I.E) w.1 S)
    rw [hS, prV_sumS, map_mul, (rV_spec hR w).1, one_mul, (rV_spec hR w).2.1]
    rfl
  have hed : X.ew * ((x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) - S) = (x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) - S := by
    have hS2 : X.ew * S = S := by
      rw [hS]; unfold sumS; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← mul_assoc, ew_ew]
    rw [mul_sub, hS2, ← hx]
  change ZMod' X.B.I X.B.g (X.ew * ((x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) - S)) at hZ
  rw [hed] at hZ
  have e : (x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = S + ((x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) - S) := by ring
  rw [e, Formalism.L2.SG.Pf.unitaryCongruence.divN_add, X.psiEf_add,
    Formalism.L2.SG.Pf.unitaryCongruence.psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (g_ne_zero X) hZ, mul_one]

end Psi

section reductionTypedPlaces

variable {D : D7} {X : HidaSetting D} (hR : RedExists X) (hU : GUnif X) (hC : GResCard X)

def reductionTypedPlaces : TypedRed X where
  Pl := gPl X
  fPl := inferInstance
  Fq v := IsLocalRing.ResidueField ↥(v.1.adicCompletionIntegers X.B.I.F)
  fld v := inferInstance
  fin v := @Fintype.ofFinite _ (finite_res hC v)
  res v := resV hR v
  res_surj v b := by
    obtain ⟨x, hx⟩ := resV_joint hR (Function.update (fun w => (0 : IsLocalRing.ResidueField
      ↥(w.1.adicCompletionIntegers X.B.I.F))) v b)
    exact ⟨x, by have := congrFun hx v; rw [Function.update_self] at this; exact this⟩
  res_joint := resV_joint hR
  res_ker x := ⟨fun h => ker_resV hR hU x h, fun h v => resV_ker_of hR hU x h v⟩
  res_ew v x := resV_ew hR v x
  card_q v := by
    obtain ⟨i, hi⟩ := gi_mem v
    rw [Fintype.card_eq_nat_card, Formalism.MainNotions.Gaps.LG.fm_card_residue, hC v.1 i hi]
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  psi0 v := psiV hU v
  psi_eq x hx := prod_local_char_eq_global hR hU x hx

theorem reduction_additive_char_ne_one (hP : PsiCond X) (v : (reductionTypedPlaces hR hU hC).Pl) : (reductionTypedPlaces hR hU hC).psi0 v ≠ 1 := by
  change gPl X at v
  intro h
  obtain ⟨o, ho, hne⟩ := hP v.1 v.2
  have h2 : psiV hU v (IsLocalRing.residue _ ⟨o, ho⟩) = 1 := by
    rw [show psiV hU v = 1 from h, AddChar.one_apply]
  rw [psiV_apply] at h2
  exact hne h2

include hR hU hC in

theorem typedRed_exists (hP : PsiCond X) : ∃ TR : TypedRed X, ∀ v, TR.psi0 v ≠ 1 :=
  ⟨reductionTypedPlaces hR hU hC, reduction_additive_char_ne_one hR hU hC hP⟩

end reductionTypedPlaces

section Corank

open Formalism.L2.SG.Full Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

variable {D : D7} {X : HidaSetting D} (Y : Full X)

theorem gt_mk {u' : D.what₂.Word}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {F0 : LFlag (VS D) D.R.rS T}
    {P : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) → Prop} (hG : GFun Λ F0 P) (x : Carrier P) :
    TermDef.Gt Λ F0 P (TermDef.mk Λ F0 P x) = Gval F0 x.1 := by
  unfold TermDef.Gt TermDef.mk
  have h : Quot.mk (Rel Λ F0 P) (Quot.out (Quot.mk (Rel Λ F0 P) x)) = Quot.mk (Rel Λ F0 P) x := Quot.out_eq _
  have key : ∀ a b : Carrier P, Relation.EqvGen (Rel Λ F0 P) a b → Gval F0 a.1 = Gval F0 b.1 := by
    intro a b he
    induction he with
    | rel a b hab => exact hG a b hab
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  exact key _ _ (Quot.eqvGen_exact h)

theorem gterm_G {u u' : D.what₂.Word}
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    t.G = Gval (lf D (X.Fu u)) t.frame := by
  have hΛ := (Y.rowsOK u).1 t.lam t.mem
  exact gt_mk ((Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hΛ).1) _

theorem corankPos_tO (u u' : D.what₂.Word) : (Y.tO u u').CorankPos := by
  intro t t' hr hG _
  have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  show 1 ≤ s0T t t'
  unfold s0T
  rw [if_pos ⟨hlam, hlam'⟩]
  have hΛ := (Y.rowsOK u).1 t.lam t.mem
  have hGv : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    rw [← gterm_G Y t]
    intro h; apply hG; show TermOp.Gt t = 0; unfold TermOp.Gt; rw [if_pos h]
  exact Formalism.L2.SG.Closed.CorankPosG_holds D.host.E (VS D) D.R.rS D.R.k (Formalism.L2.SG.Corank.finrank_VS D) t.lam
    hΛ.2.1.1 _ _ (lf D (X.Fu u)) t.frame t'.frame (t'.lin * t.lin⁻¹) hΛ.2.1.2.2.1 t.rep.2.2.2.2.1 hGv

theorem idDegenerate_tO (u u' : D.what₂.Word) : (Y.tO u u').IdDegenerate := by
  intro t ht
  have hΛ := (Y.rowsOK u).1 t.lam t.mem
  have hG : t.toTerm.G = 0 := Formalism.L2.SG.FourParts.G_eq_zero_of_termInS
    ((Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hΛ).1)
    (Formalism.L2.SG.FourParts.termInS_of_termIsId ht)
  have hG' : t.G = 0 := hG
  show TermOp.Gt t = 0
  unfold TermOp.Gt
  rw [if_pos hG']

end Corank

section GramInv

variable {τ I K Q : Type*} [Group I] [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem zs_map (S : Set τ) (intersection_update_fsHerm_neg_one : τ → Q) (ιt : τ → I) (a : τ → K) (q : Q) (φ : τ ≃ τ) (U : K ≃ₗᵢ[ℂ] K)
    (f : I → I) (hf : Function.Injective f)
    (hS : ∀ t, (t ∈ S ∧ intersection_update_fsHerm_neg_one t = q) ↔ (φ t ∈ S ∧ intersection_update_fsHerm_neg_one (φ t) = q))
    (hι : ∀ t, t ∈ S → intersection_update_fsHerm_neg_one t = q → ιt (φ t) = f (ιt t))
    (ha : ∀ t, t ∈ S → intersection_update_fsHerm_neg_one t = q → a (φ t) = U (a t)) (i : I) :
    Formalism.L2.SG.NormCut.Zs S intersection_update_fsHerm_neg_one ιt a q (f i) = U (Formalism.L2.SG.NormCut.Zs S intersection_update_fsHerm_neg_one ιt a q i) := by
  unfold Formalism.L2.SG.NormCut.Zs
  rw [← φ.tsum_eq]
  have hpt : ∀ t, (if φ t ∈ S ∧ intersection_update_fsHerm_neg_one (φ t) = q ∧ ιt (φ t) = f i then a (φ t) else 0) =
      U (if t ∈ S ∧ intersection_update_fsHerm_neg_one t = q ∧ ιt t = i then a t else 0) := by
    intro t
    by_cases h : t ∈ S ∧ intersection_update_fsHerm_neg_one t = q
    · have h' := (hS t).1 h
      rw [hι t h.1 h.2, ha t h.1 h.2, hf.eq_iff]
      by_cases hi : ιt t = i
      · simp [h, h', hi]
      · simp [h.1, h.2, h'.1, h'.2, hi]
    · have h' : ¬ (φ t ∈ S ∧ intersection_update_fsHerm_neg_one (φ t) = q) := fun h'' => h ((hS t).2 h'')
      have e1 : ¬ (φ t ∈ S ∧ intersection_update_fsHerm_neg_one (φ t) = q ∧ ιt (φ t) = f i) := fun h3 => h' ⟨h3.1, h3.2.1⟩
      have e2 : ¬ (t ∈ S ∧ intersection_update_fsHerm_neg_one t = q ∧ ιt t = i) := fun h3 => h ⟨h3.1, h3.2.1⟩
      rw [if_neg e1, if_neg e2, map_zero]
  simp_rw [hpt]
  exact (U.toContinuousLinearEquiv.map_tsum).symm

theorem zs_gram (S : Set τ) (intersection_update_fsHerm_neg_one : τ → Q) (ιt : τ → I) (a : τ → K) (q : Q) (φ : τ ≃ τ) (U : K ≃ₗᵢ[ℂ] K)
    (f : I → I) (hf : Function.Injective f)
    (hS : ∀ t, (t ∈ S ∧ intersection_update_fsHerm_neg_one t = q) ↔ (φ t ∈ S ∧ intersection_update_fsHerm_neg_one (φ t) = q))
    (hι : ∀ t, t ∈ S → intersection_update_fsHerm_neg_one t = q → ιt (φ t) = f (ιt t))
    (ha : ∀ t, t ∈ S → intersection_update_fsHerm_neg_one t = q → a (φ t) = U (a t)) (i j : I) :
    inner ℂ (Formalism.L2.SG.NormCut.Zs S intersection_update_fsHerm_neg_one ιt a q (f i)) (Formalism.L2.SG.NormCut.Zs S intersection_update_fsHerm_neg_one ιt a q (f j)) =
      inner ℂ (Formalism.L2.SG.NormCut.Zs S intersection_update_fsHerm_neg_one ιt a q i) (Formalism.L2.SG.NormCut.Zs S intersection_update_fsHerm_neg_one ιt a q j) := by
  rw [zs_map S intersection_update_fsHerm_neg_one ιt a q φ U f hf hS hι ha i, zs_map S intersection_update_fsHerm_neg_one ιt a q φ U f hf hS hι ha j,
    LinearIsometryEquiv.inner_map_map]

end GramInv

section Sat

open Formalism.L2.SG.NormCut Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (TR : TypedRed X) (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)

variable (F0 F0') in

def LeftAct (S : Set (GTerm X u u' F0 F0' what₂ rows')) (A : {Λ // Λ ∈ what₂} → Set (Iof TR)) : Prop :=
  ∀ (q : {Λ // Λ ∈ what₂} × {Λ' // Λ' ∈ rows'}), ∀ b ∈ A q.1,
    ∃ (φ : GTerm X u u' F0 F0' what₂ rows' ≃ GTerm X u u' F0 F0' what₂ rows')
      (U : Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) ≃ₗᵢ[ℂ] Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u)),
      (∀ t, (t ∈ S ∧ positionT t = q) ↔ (φ t ∈ S ∧ positionT (φ t) = q)) ∧
      (∀ t, t ∈ S → positionT t = q → iotaOf TR cs cs' (φ t) = b * iotaOf TR cs cs' t) ∧
      (∀ t, t ∈ S → positionT t = q → aT cs cs' FdN FdN' (φ t) = U (aT cs cs' FdN FdN' t))

variable (F0 F0') in

def RightAct (S : Set (GTerm X u u' F0 F0' what₂ rows')) (A' : {Λ' // Λ' ∈ rows'} → Set (Iof TR)) : Prop :=
  ∀ (q : {Λ // Λ ∈ what₂} × {Λ' // Λ' ∈ rows'}), ∀ b ∈ A' q.2,
    ∃ (φ : GTerm X u u' F0 F0' what₂ rows' ≃ GTerm X u u' F0 F0' what₂ rows')
      (U : Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u) ≃ₗᵢ[ℂ] Formalism.L2.SG.PackageTie.HS (X.Vpi u') (X.Vpi u)),
      (∀ t, (t ∈ S ∧ positionT t = q) ↔ (φ t ∈ S ∧ positionT (φ t) = q)) ∧
      (∀ t, t ∈ S → positionT t = q → iotaOf TR cs cs' (φ t) = iotaOf TR cs cs' t * b⁻¹) ∧
      (∀ t, t ∈ S → positionT t = q → aT cs cs' FdN FdN' (φ t) = U (aT cs cs' FdN FdN' t))

theorem satGram_of (S : Set (GTerm X u u' F0 F0' what₂ rows')) (A : {Λ // Λ ∈ what₂} → Set (Iof TR))
    (A' : {Λ' // Λ' ∈ rows'} → Set (Iof TR)) (hL : LeftAct F0 F0' TR cs cs' FdN FdN' S A)
    (hR : RightAct F0 F0' TR cs cs' FdN FdN' S A') :
    SatGram F0 F0' TR cs cs' FdN FdN' S A A' := by
  intro q
  constructor
  · intro b hb i j
    obtain ⟨φ, U, h1, h2, h3⟩ := hL q b hb
    exact zs_gram S positionT (iotaOf TR cs cs') (aT cs cs' FdN FdN') q φ U (fun i => b * i)
      (mul_right_injective b) h1 h2 h3 i j
  · intro b hb i j
    obtain ⟨φ, U, h1, h2, h3⟩ := hR q b hb
    exact zs_gram S positionT (iotaOf TR cs cs') (aT cs cs' FdN FdN') q φ U (fun i => i * b⁻¹)
      (mul_left_injective b⁻¹) h1 h2 h3 i j

end Sat

section Count

variable {D : D7} (X : HidaSetting D)

def GCount : Prop :=
  ∀ i : Fin 2, {v : HeightOneSpectrum (𝓞 X.B.I.F) | ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal}.ncard =
    Module.finrank ℚ X.B.I.F

variable {X}

def jointR (TR : TypedRed X) : ↥(IntAf X.B.I.F X.B.I.E) →+* (∀ v, TR.Fq v) := RingHom.pi TR.res

theorem jointR_surj (TR : TypedRed X) : Function.Surjective (jointR TR) := TR.res_joint

theorem mem_ker_jointR (TR : TypedRed X) (x : ↥(IntAf X.B.I.F X.B.I.E)) :
    x ∈ RingHom.ker (jointR TR) ↔ ZMod' X.B.I X.B.g (X.ew * x) := by
  rw [RingHom.mem_ker, ← TR.res_ker]
  constructor
  · intro h v
    exact congrFun h v
  · intro h
    funext v
    exact h v

theorem card_pi_eq (TR TR' : TypedRed X) : Nat.card (∀ v, TR.Fq v) = Nat.card (∀ v, TR'.Fq v) := by
  have hk : RingHom.ker (jointR TR) = RingHom.ker (jointR TR') := by
    ext x
    rw [mem_ker_jointR, mem_ker_jointR]
  have e1 := RingHom.quotientKerEquivOfSurjective (jointR_surj TR)
  have e2 := RingHom.quotientKerEquivOfSurjective (jointR_surj TR')
  exact Nat.card_congr ((e1.symm.trans (Ideal.quotEquivOfEq hk)).trans e2).toEquiv

theorem prod_two {P M : Type*} [Fintype P] [CommMonoid M] (q : P → ℕ) (a b : ℕ) (hab : a ≠ b)
    (hq : ∀ p, q p = a ∨ q p = b) (h : ℕ → M) :
    ∏ p, h (q p) = h a ^ Fintype.card {p // q p = a} * h b ^ Fintype.card {p // q p = b} := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun p => q p = a)]
  have e1 : ∀ p ∈ Finset.univ.filter (fun p => q p = a), h (q p) = h a := by
    intro p hp
    rw [(Finset.mem_filter.1 hp).2]
  have e2 : ∀ p ∈ Finset.univ.filter (fun p => ¬ q p = a), h (q p) = h b := by
    intro p hp
    rcases hq p with h1 | h1
    · exact absurd h1 (Finset.mem_filter.1 hp).2
    · rw [h1]
  have e3 : Finset.univ.filter (fun p => ¬ q p = a) = Finset.univ.filter (fun p => q p = b) := by
    apply Finset.filter_congr
    intro p _
    rcases hq p with h1 | h1
    · simp [h1, hab]
    · simp [h1, Ne.symm hab]
  rw [Finset.prod_congr rfl e1, Finset.prod_congr rfl e2, Finset.prod_const, Finset.prod_const,
    e3, Fintype.card_subtype, Fintype.card_subtype]

theorem pow_pow_inj {a b m n m' n' : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (h : a ^ m * b ^ n = a ^ m' * b ^ n') : m = m' ∧ n = n' := by
  have hfa := congrArg (fun t => t.factorization a) h
  have hfb := congrArg (fun t => t.factorization b) h
  simp only [Nat.factorization_mul (pow_ne_zero _ ha.ne_zero) (pow_ne_zero _ hb.ne_zero),
    Nat.factorization_pow, ha.factorization, hb.factorization, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul] at hfa hfb
  simp [hab, Ne.symm hab] at hfa hfb
  exact ⟨hfa, hfb⟩

theorem g_coprime_mem (v : HeightOneSpectrum (𝓞 X.B.I.F)) (h0 : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal)
    (h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) : False := by
  have hcop : Nat.Coprime (D.host.g 0) (D.host.g 1) :=
    (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
  have hb := Nat.gcd_eq_gcd_ab (D.host.g 0) (D.host.g 1)
  rw [hcop.gcd_eq_one] at hb
  have h1' : (1 : 𝓞 X.B.I.F) = ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) *
      (Nat.gcdA (D.host.g 0) (D.host.g 1) : 𝓞 X.B.I.F) +
      ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) * (Nat.gcdB (D.host.g 0) (D.host.g 1) : 𝓞 X.B.I.F) := by
    have := congrArg (Int.cast : ℤ → 𝓞 X.B.I.F) hb
    push_cast at this
    exact this
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, h1']
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h0) (Ideal.mul_mem_right _ _ h1)

variable (hR : RedExists X) (hU : GUnif X) (hC : GResCard X)

theorem card_gPl_sub (hN : GCount X) (i : Fin 2) :
    Fintype.card {v : gPl X // ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.1.asIdeal} = Module.finrank ℚ X.B.I.F := by
  have hmem : ∀ w : HeightOneSpectrum (𝓞 X.B.I.F), ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ w.asIdeal →
      ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ w.asIdeal := by
    intro w hw
    rw [X.g_eq, Nat.cast_mul]
    fin_cases i
    · exact w.asIdeal.mul_mem_right _ hw
    · exact w.asIdeal.mul_mem_left _ hw
  rw [Fintype.card_eq_nat_card, ← hN i]
  first
  | rw [← Set.Nat.card_coe_set_eq]
  | rw [← Nat.card_coe_set_eq]
  | rw [Set.ncard_def]
  exact Nat.card_congr
    { toFun := fun v => ⟨v.1.1, v.2⟩
      invFun := fun v => ⟨⟨v.1, hmem v.1 v.2⟩, v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

include hR hU hC in

theorem card_prod (hN : GCount X) (TR : TypedRed X) :
    ∏ v, Fintype.card (TR.Fq v) =
      D.host.g 0 ^ Module.finrank ℚ X.B.I.F * D.host.g 1 ^ Module.finrank ℚ X.B.I.F := by
  classical
  have hpi : ∀ T : TypedRed X, ∏ v, Fintype.card (T.Fq v) = Nat.card (∀ v, T.Fq v) := by
    intro T
    rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  have hinj : ∀ a b : Fin 2, D.host.g a = D.host.g b → a = b := by
    intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd h D.host.g_ne
    · exact absurd h.symm D.host.g_ne
    · rfl
  have hq : ∀ (v : (reductionTypedPlaces hR hU hC).Pl) (i : Fin 2), Fintype.card ((reductionTypedPlaces hR hU hC).Fq v) = D.host.g i ↔
      ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ (show gPl X from v).1.asIdeal := by
    intro v i
    obtain ⟨j, hj⟩ := gi_mem (show gPl X from v)
    have hcard : Fintype.card ((reductionTypedPlaces hR hU hC).Fq v) = D.host.g j := by
      rw [Fintype.card_eq_nat_card]
      show Nat.card (IsLocalRing.ResidueField
        ↥((show gPl X from v).1.adicCompletionIntegers X.B.I.F)) = _
      rw [Formalism.MainNotions.Gaps.LG.fm_card_residue, hC _ j hj]
    rw [hcard]
    constructor
    · intro h
      rw [← hinj j i h]
      exact hj
    · intro hi
      have hij : i = j := by
        by_contra hne
        fin_cases i <;> fin_cases j
        · exact hne rfl
        · exact g_coprime_mem (show gPl X from v).1 hi hj
        · exact g_coprime_mem (show gPl X from v).1 hj hi
        · exact hne rfl
      rw [hij]
  have hcnt : ∀ i : Fin 2, Fintype.card {v : (reductionTypedPlaces hR hU hC).Pl //
      Fintype.card ((reductionTypedPlaces hR hU hC).Fq v) = D.host.g i} = Module.finrank ℚ X.B.I.F := by
    intro i
    rw [← card_gPl_sub hN i]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun v => hq v i))
  have hp2 := prod_two (fun v : (reductionTypedPlaces hR hU hC).Pl => Fintype.card ((reductionTypedPlaces hR hU hC).Fq v))
    (D.host.g 0) (D.host.g 1) D.host.g_ne (reductionTypedPlaces hR hU hC).card_q id
  simp only [id] at hp2
  rw [hpi, card_pi_eq TR (reductionTypedPlaces hR hU hC), ← hpi, hp2, hcnt 0, hcnt 1]

include hR hU hC in

theorem typed_count (hN : GCount X) (TR : TypedRed X) (i : Fin 2) :
    Fintype.card {v : TR.Pl // Fintype.card (TR.Fq v) = D.host.g i} = Module.finrank ℚ X.B.I.F := by
  classical
  have hpq := prod_two (fun v : TR.Pl => Fintype.card (TR.Fq v)) (D.host.g 0) (D.host.g 1)
    D.host.g_ne TR.card_q id
  simp only [id] at hpq
  rw [card_prod hR hU hC hN TR] at hpq
  obtain ⟨h0, h1⟩ := pow_pow_inj (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hpq
  fin_cases i
  · exact h0.symm
  · exact h1.symm

include hR hU hC in

theorem tt_eq (hN : GCount X) (TR : TypedRed X) :
    ∏ v, (1 + 3 / (Fintype.card (TR.Fq v) : ℝ)) =
      (1 + 3 / (D.host.g 0 : ℝ)) ^ Module.finrank ℚ X.B.I.F * (1 + 3 / (D.host.g 1 : ℝ)) ^ Module.finrank ℚ X.B.I.F := by
  classical
  have hpq := prod_two (fun v : TR.Pl => Fintype.card (TR.Fq v)) (D.host.g 0) (D.host.g 1)
    D.host.g_ne TR.card_q (fun n : ℕ => (1 + 3 / (n : ℝ)))
  rw [hpq, typed_count hR hU hC hN TR 0, typed_count hR hU hC hN TR 1]

end Count

section Gam

variable {D : D7} {X : HidaSetting D}

def eqZ (F : Type) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] (h : Fintype.card F = p) : F ≃+* ZMod p :=
  FiniteField.ringEquivOfCardEq (by rw [h, ZMod.card])

theorem card_GL_eq (F : Type) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] (h : Fintype.card F = p) (k : ℕ) :
    Fintype.card (GL (Fin k) F) = Formalism.L2.SG.TypedSets.glkC k p := by
  unfold Formalism.L2.SG.TypedSets.glkC
  rw [Fintype.card_eq_nat_card]
  exact Nat.card_congr (Units.mapEquiv (eqZ F p h).mapMatrix.toMulEquiv).toEquiv

theorem cardU_eq (F : Type) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] (h : Fintype.card F = p) (k : ℕ) :
    Formalism.L2.SG.GGMirabolic.cardU F k = Formalism.L2.SG.TypedSets.ukC k p := by
  unfold Formalism.L2.SG.GGMirabolic.cardU Formalism.L2.SG.TypedSets.ukC
  let e := Units.mapEquiv ((eqZ F p h).mapMatrix (m := Fin k)).toMulEquiv
  apply Nat.card_congr
  refine e.toEquiv.subtypeEquiv ?_
  intro x
  show Formalism.L2.SG.GGMirabolic.IsUni k x ↔
    Formalism.DoubleCosetMeasures.IsUpUni ((e x : GL (Fin k) (ZMod p)) : Matrix (Fin k) (Fin k) (ZMod p))
  have he : ∀ i j, ((e x : GL (Fin k) (ZMod p)) : Matrix (Fin k) (Fin k) (ZMod p)) i j =
      eqZ F p h ((x : Matrix (Fin k) (Fin k) F) i j) := fun i j => rfl
  simp only [Formalism.L2.SG.GGMirabolic.IsUni, Formalism.DoubleCosetMeasures.IsUpUni, Matrix.IsUpperTriangular,
    Matrix.BlockTriangular, id, he, map_eq_one_iff _ (eqZ F p h).injective,
    map_eq_zero_iff _ (eqZ F p h).injective]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    intro i j hij
    exact h2 i j hij
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun i j hij => h1 i j hij⟩

theorem gamma_one_eq_prod_card_ratio (TR : TypedRed X) :
    Gam1 TR = ∏ v, ((Fintype.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ) /
      (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ)) := by
  have hg : ∀ v, Formalism.L2.SG.GGMirabolic.gam (TR.psi0 v) (1 : GL (Fin D.R.k) (TR.Fq v)) =
      (((Fintype.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ) /
        (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ) : ℝ) : ℂ) := by
    intro v
    have hU1 : Formalism.L2.SG.GGMirabolic.psiNat (TR.psi0 v) (1 : GL (Fin D.R.k) (TR.Fq v)) = 1 := by
      unfold Formalism.L2.SG.GGMirabolic.psiNat
      rw [if_pos]
      · have h0 : (∑ i : Fin D.R.k, ∑ j : Fin D.R.k, if (j : ℕ) = (i : ℕ) + 1 then
            (1 : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          apply Finset.sum_eq_zero
          intro j _
          split_ifs with hj
          · apply Matrix.one_apply_ne
            intro hij
            rw [hij] at hj
            omega
          · rfl
        simp only [Formalism.L2.SG.GGMirabolic.psiU, Formalism.L2.SG.GGMirabolic.superdiag, Units.val_one]
        rw [h0, AddChar.map_zero_eq_one]
      · exact ⟨fun i => by simp, fun i j hij => by simp [Matrix.one_apply_ne hij.ne']⟩
    rw [Formalism.L2.SG.GGMirabolic.gam]
    simp only [mul_one, mul_inv_cancel, hU1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    push_cast
    ring
  unfold Formalism.L2.SG.TermOp.Gam1 Formalism.L2.SG.GGMirabolic.gamProd
  simp only [Pi.one_apply, hg]
  rw [← Complex.ofReal_prod, Complex.ofReal_re]

def gaZ (k q : ℕ) : ℝ := (Formalism.L2.SG.TypedSets.glkC k q : ℝ) / (Formalism.L2.SG.TypedSets.ukC k q : ℝ)

theorem factor_eq (TR : TypedRed X) (v : TR.Pl) :
    ((Fintype.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ) / (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ)) =
      gaZ D.R.k (Fintype.card (TR.Fq v)) := by
  haveI : Fact (Fintype.card (TR.Fq v)).Prime := ⟨by
    rcases TR.card_q v with h | h <;> rw [h] <;> exact D.host.g_prime _⟩
  rw [card_GL_eq (TR.Fq v) _ rfl D.R.k, cardU_eq (TR.Fq v) _ rfl D.R.k]
  rfl

variable (hR : RedExists X) (hU : GUnif X) (hC : GResCard X)

include hR hU hC in

theorem gamma_one_eq_pow_degree (hN : GCount X) (TR : TypedRed X) :
    Gam1 TR = gaZ D.R.k (D.host.g 0) ^ Module.finrank ℚ X.B.I.F * gaZ D.R.k (D.host.g 1) ^ Module.finrank ℚ X.B.I.F := by
  classical
  rw [gamma_one_eq_prod_card_ratio]
  simp only [factor_eq]
  have hpq := prod_two (fun v : TR.Pl => Fintype.card (TR.Fq v)) (D.host.g 0) (D.host.g 1)
    D.host.g_ne TR.card_q (gaZ D.R.k)
  rw [hpq, typed_count hR hU hC hN TR 0, typed_count hR hU hC hN TR 1]

theorem card_typ (hN : GCount X) (i : Fin 2) :
    Fintype.card {p : Formalism.L2.SG.TypedSets.TypP X.B.I.F (D.host.g 0) (D.host.g 1) //
      Formalism.L2.SG.TypedSets.gOf p = D.host.g i} = Module.finrank ℚ X.B.I.F := by
  classical
  have hfin0 := Formalism.L2.SG.TypedSets.finite_over X.B.I.F (D.host.g 0) (D.host.g_prime 0).ne_zero
  have hfin1 := Formalism.L2.SG.TypedSets.finite_over X.B.I.F (D.host.g 1) (D.host.g_prime 1).ne_zero
  have hfin : {v : HeightOneSpectrum (𝓞 X.B.I.F) |
      Formalism.L2.SG.TypedSets.IsTyped X.B.I.F (D.host.g 0) (D.host.g 1) v}.Finite :=
    (hfin0.union hfin1).subset (fun v hv => hv)
  have hmem : ∀ v, v ∈ Formalism.L2.SG.TypedSets.typSet X.B.I.F (D.host.g 0) (D.host.g 1) ↔
      Formalism.L2.SG.TypedSets.IsTyped X.B.I.F (D.host.g 0) (D.host.g 1) v := by
    intro v
    unfold Formalism.L2.SG.TypedSets.typSet
    rw [dif_pos hfin, Set.Finite.mem_toFinset]
    rfl
  have hinj : ∀ a b : Fin 2, D.host.g a = D.host.g b → a = b := by
    intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd h D.host.g_ne
    · exact absurd h.symm D.host.g_ne
    · rfl
  have hq : ∀ p : Formalism.L2.SG.TypedSets.TypP X.B.I.F (D.host.g 0) (D.host.g 1),
      Formalism.L2.SG.TypedSets.gOf p = D.host.g i ↔ ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
    intro p
    have hp := (hmem p.1).1 p.2
    unfold Formalism.L2.SG.TypedSets.gOf
    split_ifs with h0
    · constructor
      · intro h
        rw [← hinj 0 i h]
        exact h0
      · intro hi
        by_contra hne
        fin_cases i
        · exact hne rfl
        · exact g_coprime_mem p.1 h0 hi
    · have h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := hp.resolve_left h0
      constructor
      · intro h
        rw [← hinj 1 i h]
        exact h1
      · intro hi
        fin_cases i
        · exact absurd hi h0
        · rfl
  have hT : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      Formalism.L2.SG.TypedSets.IsTyped X.B.I.F (D.host.g 0) (D.host.g 1) v := by
    intro v hv
    fin_cases i
    · exact Or.inl hv
    · exact Or.inr hv
  rw [Fintype.card_eq_nat_card, ← hN i]
  first
  | rw [← Set.Nat.card_coe_set_eq]
  | rw [← Nat.card_coe_set_eq]
  | rw [Set.ncard_def]
  exact Nat.card_congr
    { toFun := fun p => ⟨p.1.1, (hq p.1).1 p.2⟩
      invFun := fun v => ⟨⟨v.1, (hmem v.1).2 (hT v.1 v.2)⟩, (hq _).2 v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

include hR hU hC in

theorem gamma_one_eq_prod_typed_places (hN : GCount X) (TR : TypedRed X) :
    Gam1 TR = ∏ p : Formalism.L2.SG.TypedSets.TypP X.B.I.F (D.host.g 0) (D.host.g 1),
      (Formalism.L2.SG.TypedSets.glkC D.R.k (Formalism.L2.SG.TypedSets.gOf p) : ℝ) /
        (Formalism.L2.SG.TypedSets.ukC D.R.k (Formalism.L2.SG.TypedSets.gOf p) : ℝ) := by
  classical
  rw [gamma_one_eq_pow_degree hR hU hC hN TR]
  have hq' : ∀ p : Formalism.L2.SG.TypedSets.TypP X.B.I.F (D.host.g 0) (D.host.g 1),
      Formalism.L2.SG.TypedSets.gOf p = D.host.g 0 ∨ Formalism.L2.SG.TypedSets.gOf p = D.host.g 1 := by
    intro p
    unfold Formalism.L2.SG.TypedSets.gOf
    split_ifs <;> simp
  have hpq := prod_two (fun p : Formalism.L2.SG.TypedSets.TypP X.B.I.F (D.host.g 0) (D.host.g 1) =>
    Formalism.L2.SG.TypedSets.gOf p) (D.host.g 0) (D.host.g 1) D.host.g_ne hq' (gaZ D.R.k)
  change _ = ∏ p : Formalism.L2.SG.TypedSets.TypP X.B.I.F (D.host.g 0) (D.host.g 1),
    gaZ D.R.k (Formalism.L2.SG.TypedSets.gOf p)
  rw [hpq, card_typ hN 0, card_typ hN 1]

end Gam

section Derive

open Formalism.L2.SG.Pf.SatGramLoc

theorem ncard_places_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L) (p : ℕ) :
    {w : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ w.asIdeal}.ncard =
      {w : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ w.asIdeal}.ncard := by
  set f := RingOfIntegers.mapRingEquiv e
  have hne : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (f.symm : 𝓞 L →+* 𝓞 K) ≠ ⊥ := by
    intro w h
    apply w.ne_bot
    rw [← Ideal.map_comap_of_surjective (f.symm : 𝓞 L →+* 𝓞 K) f.symm.surjective w.asIdeal, h, Ideal.map_bot]
  refine Set.ncard_congr (fun w _ => (⟨w.asIdeal.comap (f.symm : 𝓞 L →+* 𝓞 K), Ideal.comap_isPrime _ _, hne w⟩ :
    HeightOneSpectrum (𝓞 L))) ?_ ?_ ?_
  · intro w hw
    show ((p : ℕ) : 𝓞 L) ∈ w.asIdeal.comap (f.symm : 𝓞 L →+* 𝓞 K)
    rw [Ideal.mem_comap, map_natCast]; exact hw
  · intro a b _ _ hab
    have h := congrArg HeightOneSpectrum.asIdeal hab
    simp only at h
    exact HeightOneSpectrum.ext (Ideal.comap_injective_of_surjective _ f.symm.surjective h)
  · intro w hw
    refine ⟨⟨w.asIdeal.comap (f : 𝓞 K →+* 𝓞 L), Ideal.comap_isPrime _ _, ?_⟩, ?_, ?_⟩
    · intro h
      apply w.ne_bot
      rw [← Ideal.map_comap_of_surjective (f : 𝓞 K →+* 𝓞 L) f.surjective w.asIdeal, h, Ideal.map_bot]
    · show ((p : ℕ) : 𝓞 K) ∈ w.asIdeal.comap (f : 𝓞 K →+* 𝓞 L)
      rw [Ideal.mem_comap, map_natCast]; exact hw
    · apply HeightOneSpectrum.ext
      show (w.asIdeal.comap (f : 𝓞 K →+* 𝓞 L)).comap (f.symm : 𝓞 L →+* 𝓞 K) = w.asIdeal
      rw [Ideal.comap_comap]
      have : (f : 𝓞 K →+* 𝓞 L).comp (f.symm : 𝓞 L →+* 𝓞 K) = RingHom.id _ := by
        ext x; simp
      rw [this, Ideal.comap_id]

variable {D : D7} (X : HidaSetting D)

theorem gsplit_X (i : Fin 2) :
    {w : HeightOneSpectrum (𝓞 X.B.I.E) | ((D.host.g i : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard =
      Module.finrank ℚ X.B.I.E := by
  rw [ncard_places_eq X.ιE, LinearEquiv.finrank_eq X.ιE.toRatAlgEquiv.toLinearEquiv]
  exact D.nd.g_split i

variable {X}

theorem gResCard_of (hS : SplitPrimeLoc) : GResCard X := fun v i hi =>
  ((hS X.B.I.F X.B.I.E (D.host.g i) (D.host.g_prime i) (gsplit_X X i)).1 v hi).1

theorem gCount_of (hS : SplitPrimeLoc) : GCount X := fun i =>
  (hS X.B.I.F X.B.I.E (D.host.g i) (D.host.g_prime i) (gsplit_X X i)).2

theorem gUnif_of (hS : SplitPrimeLoc) : GUnif X := by
  intro v hv
  obtain ⟨i, hi⟩ := gi_mem (X := X) ⟨v, hv⟩
  have hval := fun j (hj : ((D.host.g j : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) =>
    ((hS X.B.I.F X.B.I.E (D.host.g j) (D.host.g_prime j) (gsplit_X X j)).1 v hj).2
  have hone : ∀ j, ((D.host.g j : ℕ) : 𝓞 X.B.I.F) ∉ v.asIdeal →
      Valued.v ((D.host.g j : ℕ) : v.adicCompletion X.B.I.F) = 1 := by
    intro j hj
    have := Formalism.MainNotions.Gaps.LG.sc_val_one v ((D.host.g j : ℕ) : 𝓞 X.B.I.F) hj
    simpa using this
  have e : ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) =
      ((D.host.g 0 : ℕ) : v.adicCompletion X.B.I.F) * ((D.host.g 1 : ℕ) : v.adicCompletion X.B.I.F) := by
    rw [X.g_eq]; push_cast; ring
  rw [e, map_mul]
  fin_cases i
  · rw [hval 0 hi, hone 1 (fun h1 => g_coprime_mem v hi h1), mul_one]
  · rw [hval 1 hi, hone 0 (fun h0 => g_coprime_mem v h0 hi), one_mul]

variable (X) in

theorem one_sub_ew : ZMod' X.B.I X.B.g (1 - X.ew - sigA X.B.I X.ew) := by
  set c := 1 - X.ew - sigA X.B.I X.ew with hc
  have hcI : c ∈ IntAf X.B.I.F X.B.I.E :=
    sub_mem (sub_mem (one_mem _) X.ew_int) (Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem X.B.I X.ew_int)
  have hz : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  have hm := Formalism.L2.SG.Pf.unitaryCongruence.mL_Qs X.B.I X.B.g hz (X.ew_full X.z0 hz)
  have h1 : ZMod' X.B.I X.B.g (c * hA X.B.I X.z0 X.z0) := by
    have := hm
    change ZMod' X.B.I X.B.g (hA X.B.I X.z0 (c • X.z0)) at this
    rwa [Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_right] at this
  have h2 : ZMod' X.B.I X.B.g (c * (hA X.B.I X.z0 X.z0 + 1)) :=
    Formalism.L2.SG.Pf.unitaryCongruence.Z_smul X.B.I X.B.g hcI X.formsAtZero.1
  have e : c = c * (hA X.B.I X.z0 X.z0 + 1) - c * hA X.B.I X.z0 X.z0 := by ring
  rw [e]; exact Formalism.L2.SG.Pf.unitaryCongruence.Z_sub X.B.I X.B.g h2 h1

theorem redExists_of (hC : RedCore) (hU : GUnif X) : RedExists X := by
  intro v hv
  obtain ⟨t, ht, he⟩ := one_sub_ew X
  have hsig : ∀ y, Formalism.UG.sigR X.B.I.cm.sig (v.adicCompletion X.B.I.F) (prV (E := X.B.I.E) v y) =
      prV (E := X.B.I.E) v (sigA X.B.I y) := fun y =>
    (congrArg (fun φ : _ →+* _ => φ y) (afsplit_prV_comp_sigR X.B.I.cm.sig v)).symm
  obtain ⟨r, h1, h2, h3, h4⟩ := hC X.B.I.F X.B.I.E X.B.I.cm.sig (fun x => star_star x) X.B.I.cm.deg2 v
    (prV (E := X.B.I.E) v X.ew) (afsplit_prV_int v _ X.ew_int) (by rw [← map_mul, X.ew_idem])
    (by rw [hsig, ← map_mul, X.ew_orth, map_zero])
    ⟨((X.B.g : ℕ) : v.adicCompletion X.B.I.F), by rw [hU v hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega,
      prV (E := X.B.I.E) v t, afsplit_prV_int v t ht, by
        rw [hsig, ← map_one (prV (E := X.B.I.E) v), ← map_sub, ← map_sub, he, map_mul, map_natCast]
        congr 1
        rw [← map_natCast (Algebra.TensorProduct.includeRight (R := X.B.I.F) (A := X.B.I.E)
          (B := v.adicCompletion X.B.I.F))]
        rfl⟩
  exact ⟨r, h1, h2, h3, h4⟩

theorem typedRed_exists' (hS : SplitPrimeLoc) (hC : RedCore) (hP : PsiCond X) :
    ∃ TR : TypedRed X, ∀ v, TR.psi0 v ≠ 1 :=
  typedRed_exists (redExists_of hC (gUnif_of hS)) (gUnif_of hS) (gResCard_of hS) hP

end Derive

section Closed

open Formalism.L2.SG.Pf.SatGramLoc Formalism.L2.SG.NormCut Formalism.L2.SG.Full

variable {D : D7} {X : HidaSetting D}

theorem typed_count' (hS : SplitPrimeLoc) (hRC : RedCore) (TR : TypedRed X) (i : Fin 2) :
    Fintype.card {v : TR.Pl // Fintype.card (TR.Fq v) = D.host.g i} = Module.finrank ℚ X.B.I.F :=
  typed_count (redExists_of hRC (gUnif_of hS)) (gUnif_of hS) (gResCard_of hS) (gCount_of hS) TR i

theorem tt_eq' (hS : SplitPrimeLoc) (hRC : RedCore) (TR : TypedRed X) :
    ∏ v, (1 + 3 / (Fintype.card (TR.Fq v) : ℝ)) =
      (1 + 3 / (D.host.g 0 : ℝ)) ^ Module.finrank ℚ X.B.I.F * (1 + 3 / (D.host.g 1 : ℝ)) ^ Module.finrank ℚ X.B.I.F :=
  tt_eq (redExists_of hRC (gUnif_of hS)) (gUnif_of hS) (gResCard_of hS) (gCount_of hS) TR

theorem gamma_one_typed_places_of_local (hS : SplitPrimeLoc) (hRC : RedCore) (TR : TypedRed X) :
    Gam1 TR = ∏ p : Formalism.L2.SG.TypedSets.TypP X.B.I.F (D.host.g 0) (D.host.g 1),
      (Formalism.L2.SG.TypedSets.glkC D.R.k (Formalism.L2.SG.TypedSets.gOf p) : ℝ) /
        (Formalism.L2.SG.TypedSets.ukC D.R.k (Formalism.L2.SG.TypedSets.gOf p) : ℝ) :=
  gamma_one_eq_prod_typed_places (redExists_of hRC (gUnif_of hS)) (gUnif_of hS) (gResCard_of hS) (gCount_of hS) TR

def LeftActC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ S ∈ ({(Y.tO u u').genSet, (Y.tO u u').ngSet, (Y.tO u u').degSet} :
      Set (Set (GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')))),
    LeftAct (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') S (Aset Y.TR (Y.cs u))

def RightActC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ S ∈ ({(Y.tO u u').genSet, (Y.tO u u').ngSet, (Y.tO u u').degSet} :
      Set (Set (GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')))),
    RightAct (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') S (Aset Y.TR (Y.cs u'))

theorem satGramC_of (hL : LeftActC) (hR : RightActC) (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) :
    SatGram (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (Y.tO u u').genSet
        (Aset Y.TR (Y.cs u)) (Aset Y.TR (Y.cs u')) ∧
      SatGram (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (Y.tO u u').ngSet
        (Aset Y.TR (Y.cs u)) (Aset Y.TR (Y.cs u')) ∧
      SatGram (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (Y.tO u u').degSet
        (Aset Y.TR (Y.cs u)) (Aset Y.TR (Y.cs u')) :=
  ⟨satGram_of Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') _ _ _ (hL D X Y u u' _ (by simp))
      (hR D X Y u u' _ (by simp)),
    satGram_of Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') _ _ _ (hL D X Y u u' _ (by simp))
      (hR D X Y u u' _ (by simp)),
    satGram_of Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') _ _ _ (hL D X Y u u' _ (by simp))
      (hR D X Y u u' _ (by simp))⟩

end Closed

section Closed2

open Formalism.L2.SG.Full

def LiftOntoC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    LiftOnto X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')

def PsiCondC : Prop := ∀ (D : D7) (X : HidaSetting D), PsiCond X

end Closed2

end Formalism.L2.SG.Pf.SatGram

namespace Formalism.L2.SG.Pf

alias typedRed_exists := SatGram.typedRed_exists
alias typedRed_exists' := SatGram.typedRed_exists'
alias corankPos_tO := SatGram.corankPos_tO
alias idDegenerate_tO := SatGram.idDegenerate_tO
alias satGram_of := SatGram.satGram_of
alias satGramC_of := SatGram.satGramC_of
alias typed_count := SatGram.typed_count
alias typed_count' := SatGram.typed_count'
alias tt_eq := SatGram.tt_eq
alias tt_eq' := SatGram.tt_eq'
alias gamma_one_eq_prod_typed_places := SatGram.gamma_one_eq_prod_typed_places
alias gamma_one_typed_places_of_local := SatGram.gamma_one_typed_places_of_local
alias gsplit_X := SatGram.gsplit_X
alias one_sub_ew := SatGram.one_sub_ew

end Formalism.L2.SG.Pf
