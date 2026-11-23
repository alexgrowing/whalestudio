import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabelThetaLiftSpaceIffDualStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsRowsRationalSelfAdjointLabelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
noncomputable section

namespace GlobalTheory.InertValLab

theorem eig_eq_of_mem_span {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (op : Module.End K V) (U : Module.End ℂ W) (μ : K) (S : Submodule K V)
    (hU : ∀ x, U (j x) = j (op x)) (hS : S ≤ op.maxGenEigenspace μ) (v : W)
    (hv : v ∈ Submodule.span ℂ (j '' (S : Set V))) (l : ℂ) (hl : U v = l • v) (hv0 : v ≠ 0) : l = σ μ := by
  have hpow : ∀ (k : ℕ) x, ((U - σ μ • (1 : Module.End ℂ W)) ^ k) (j x) = j (((op - μ • (1 : Module.End K V)) ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply]
      have : (U - σ μ • (1 : Module.End ℂ W)) (j x) = j ((op - μ • (1 : Module.End K V)) x) := by
        simp [hU, LinearMap.map_smulₛₗ]
      rw [this, ih]
  have hle : Submodule.span ℂ (j '' (S : Set V)) ≤ U.maxGenEigenspace (σ μ) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (hS hx)
    exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, by rw [hpow, hk, map_zero]⟩
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (hle hv)
  have hpv : ∀ k : ℕ, ((U - σ μ • (1 : Module.End ℂ W)) ^ k) v = (l - σ μ) ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, pow_succ]
      have : (U - σ μ • (1 : Module.End ℂ W)) v = (l - σ μ) • v := by simp [hl, sub_smul]
      rw [this, LinearMap.map_smul, ih, smul_smul, mul_comm]
  rw [hpv] at hk
  have := (smul_eq_zero.1 hk).resolve_right hv0
  exact sub_eq_zero.1 (pow_eq_zero_iff'.1 this).1

theorem eq_of_le_maxGen {K V : Type} [Field K] [AddCommGroup V] [Module K V] (f : Module.End K V) (a b : K)
    (S : Submodule K V) (hS : S ≠ ⊥) (ha : S ≤ f.maxGenEigenspace a) (hb : S ≤ f.maxGenEigenspace b) : a = b := by
  by_contra h
  have hd := Module.End.disjoint_genEigenspace f h ⊤ ⊤
  exact hS (eq_bot_iff.2 fun x hx => by
    have := hd.le_bot ⟨ha hx, hb hx⟩
    simpa using this)

theorem inertPartition_le_partF {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty : Type}
    {B : BlockDat K G Pl0} (Dd : InertDat3 B I0 Ty) (p : Typ3 K Pl0 I0 Ty) (k : Dd.PlI × Ty) :
    Dd.inertTypeEigenspaceSum p ≤ (Dd.opI k).maxGenEigenspace (p.2 (Dd.plI k.1, k.2)) := by
  unfold InertDat3.inertTypeEigenspaceSum Formalism.L2.Col.eigSum
  refine iSup₂_le fun x hx => ?_
  have := Formalism.L2.Col.eigAt_le Dd.opAll x (Sum.inr k)
  rw [hx.2 k] at this
  exact this

theorem hkF_single_of_not {D : D7} (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (d : List ℤ)
    (hd : ¬ IsLab V P d) (F : Bridge.Gf V → W) : GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F = 0 := by
  funext h
  simp [GlobalTheory.Hk3.hkF, GlobalTheory.Hk3.rep, hd]

theorem hkF_eq_sum {D : D7} (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (c : List ℤ →₀ ℂ)
    (F : Bridge.Gf V → W) : GlobalTheory.Hk3.hkF V P c F = c.sum fun d z => z • GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F := by
  funext h
  conv_rhs => rw [Finsupp.sum, Finset.sum_apply]
  simp only [GlobalTheory.Hk3.hkF, Pi.smul_apply, zero_smul, Finsupp.sum_single_index, one_smul]
  rfl

theorem labIn_pw {n : ℕ} {y : List ℕ} (hy : Formalism.L2.Col.InertTypeOk n y) : (labIn n y).Pairwise (fun a b => b ≤ a) :=
  ((GlobalTheory.Hk3.labIn_selfDual_iff n (labIn n y)).2 ⟨y, hy.2.2, hy.1, hy.2.1, rfl⟩).2.1

theorem labs {D : D7} (V : HSp D) (P : Pl D.host.E) (d : List ℤ) (hd : IsLab V P d) (hc : conjPl P = P) :
    ∃ y, Formalism.L2.Col.InertTypeOk V.rank y ∧ d = labIn V.rank y := by
  obtain ⟨hl, hpw, hdu⟩ := (GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing V P d).1 hd
  obtain ⟨y, h1, h2, h3, h4⟩ := (GlobalTheory.Hk3.labIn_selfDual_iff _ d).1 ⟨hl, hpw, hdu hc⟩
  exact ⟨y, ⟨h2, h3, h1⟩, h4⟩

theorem key_generic {H : Type} [AddCommGroup H] [Module ℂ H] (hXP : (List ℤ →₀ ℂ) → Module.End ℂ H)
    (lin : ∀ cX x, hXP cX x = cX.sum fun d z => z • hXP (Finsupp.single d 1) x) (μ : List ℤ → ℂ) (v : H) (hv0 : v ≠ 0)
    (h2 : ∀ d, hXP (Finsupp.single d 1) v = μ d • v) (cX : List ℤ →₀ ℂ) (a : ℂ) (h1 : hXP cX v = a • v) :
    a = cX.sum fun d z => z * μ d := by
  rw [lin, Finsupp.sum] at h1
  simp only [h2, smul_smul] at h1
  rw [← Finset.sum_smul] at h1
  exact (smul_left_injective ℂ hv0 h1).symm

theorem conjIdeal_eq_conjPl {D : D7} (P : Pl D.host.E) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = (conjPl P).asIdeal := by
  unfold Formalism.HermitianLatticesTheory.conjIdeal
  have hs : {r : 𝓞 D.host.E | ∃ s ∈ P.asIdeal, algebraMap (𝓞 D.host.E) D.host.E r =
      star (algebraMap (𝓞 D.host.E) D.host.E s)} = ((conjPl P).asIdeal : Set (𝓞 D.host.E)) := by
    ext r
    rw [SetLike.mem_coe]
    show _ ↔ r ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E)
    rw [Ideal.mem_map_of_equiv]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨s, hs, hr⟩
      exact ⟨s, hs, RingOfIntegers.ext hr.symm⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
  rw [hs, Ideal.span_eq]

theorem eq_of_isConj {D : D7} {P PP : Pl D.host.E} (hc : conjPl P = P) (h : Formalism.IndefR.Lev.IsConjPl PP P) : PP = P := by
  have hle : PP.asIdeal ≤ P.asIdeal := by
    intro a ha
    obtain ⟨c', hc', he⟩ := h a ha
    have h2 : a ∈ (conjPl P).asIdeal := by
      show a ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E)
      rw [Ideal.mem_map_of_equiv]
      refine ⟨c', hc', RingOfIntegers.ext ?_⟩
      show star (c' : D.host.E) = (a : D.host.E)
      rw [he, star_star]
    rwa [hc] at h2
  exact HeightOneSpectrum.ext (PP.isMaximal.eq_of_le P.isPrime.ne_top hle)

section Ctx

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem tie1 (R : RealDat3 D A3 Ks) (hIn : R.IsInert) (hAll : R.AllPlaces) (P : Pl D.host.E)
    (hP : Good R.toRealDat A3.A.μ0 P) (hc : conjPl P = P) : ∃ Q : A3.okI A3.A.μ0, R.plI Q.1 = P := by
  have hPg : P ∉ R.Pg := fun h => (hP P (Or.inl h)).1 rfl
  have hPQ : P ∉ R.Q A3.A.μ0 := fun h => (hP P (Or.inr h)).1 rfl
  have hcj : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal := by rw [conjIdeal_eq_conjPl, hc]
  have hSb : P ∉ (R.Sb : Set (Pl D.host.E)) := by
    rw [Finset.mem_coe, show R.Sb = R.Pg from hAll]; exact hPg
  obtain ⟨Q0, hQ0⟩ := hIn.onto P ⟨hcj, hSb⟩
  refine ⟨⟨Q0, (hIn.tie.okI A3.A.μ0 Q0).2 ?_⟩, hQ0⟩
  rw [hQ0]
  refine ⟨hcj, ?_⟩
  rintro (h | h)
  · exact hSb h
  · exact hPQ h

theorem tie2 (R : RealDat3 D A3 Ks) (hIn : R.IsInert) (hAll : R.AllPlaces) (Q : A3.okI A3.A.μ0) :
    Good R.toRealDat A3.A.μ0 (R.plI Q.1) ∧ conjPl (R.plI Q.1) = R.plI Q.1 := by
  obtain ⟨hcj, hn⟩ := (hIn.tie.okI A3.A.μ0 Q.1).1 Q.2
  have hc : conjPl (R.plI Q.1) = R.plI Q.1 :=
    HeightOneSpectrum.ext (by rw [← conjIdeal_eq_conjPl, hcj])
  refine ⟨fun PP hPP => ?_, hc⟩
  have hmem : PP ∈ ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q A3.A.μ0 : Set (Pl D.host.E))) := by
    rcases hPP with h | h
    · left; rw [Finset.mem_coe, show R.Sb = R.Pg from hAll]; exact h
    · right; exact h
  have hne : PP ≠ R.plI Q.1 := fun h => hn (h ▸ hmem)
  exact ⟨hne, fun h => hne (eq_of_isConj hc h)⟩

end Ctx

section Ctx2

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 4000000 in
theorem ev_lemma (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hCore : Core R.toRealDat F.lv2) (hSchur : SchurAll R.toRealDat)
    (hSF : IsSF R.toRealDat R.SF) (hEEc : ∀ c, R.EEc c = EEc R.toRealDat R.SF c)
    (hInj : ∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0)
    (hX : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HX A3.A.μ0).H) (hXops : GlobalTheory.Hk3.IsOpsX R.toRealDat A3.A.μ0 hX)
    (q : A3.fam3.base3.Ix) (e : Pl D.host.E → List ℤ → ℂ) (he : R.Carries q e) : ∃ v, v ≠ 0 ∧
      v ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) ∧
      ∀ P, Good R.toRealDat A3.A.μ0 P → ∀ cX c0, GlobalTheory.Hk3.MatchE R.toRealDat A3.A.μ0 P cX c0 →
        hX P cX v = GlobalTheory.Hk3.evC (Yc D 0) P (fun d => e P (dualLab d)) c0 • v := by
  have he1 : R.EEc e ≠ ⊥ := he.1
  have he2 : (R.EEc e).map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
      Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)) := he.2
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot he1
  refine ⟨LinearMap.adjoint (R.Th A3.A.μ0) w, ?_, he2 (Submodule.mem_map_of_mem hw), ?_⟩
  · intro h0
    have hle : R.EEc e ≤ R.EEp3 q := le_iSup₂_of_le (f := fun c (_ : R.Carries q c) => R.EEc c) e he le_rfl
    exact hw0 (hInj q w (hle hw) h0)
  · intro P hP cX c0 hM
    exact (GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 hCore hSchur R.SF hSF A3.A.μ0 P hP cX c0 hM hX hXops).2 e w
      (by rw [← hEEc]; exact hw)

set_option maxHeartbeats 4000000 in
theorem lin_lemma (R : RealDat3 D A3 Ks) (hX : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HX A3.A.μ0).H)
    (hXops : GlobalTheory.Hk3.IsOpsX R.toRealDat A3.A.μ0 hX) (heInj : Function.Injective (R.HX A3.A.μ0).e)
    (P : Pl D.host.E) (hP : Good R.toRealDat A3.A.μ0 P) (cX : List ℤ →₀ ℂ) (x : (R.HX A3.A.μ0).H) :
    hX P cX x = cX.sum fun d z => z • hX P (Finsupp.single d 1) x := by
  apply heInj
  rw [hXops P hP, map_finsuppSum]
  simp only [map_smul, hXops P hP]
  exact hkF_eq_sum _ _ _ _

set_option maxHeartbeats 4000000 in
theorem zer_lemma (R : RealDat3 D A3 Ks) (hX : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HX A3.A.μ0).H)
    (hXops : GlobalTheory.Hk3.IsOpsX R.toRealDat A3.A.μ0 hX) (heInj : Function.Injective (R.HX A3.A.μ0).e)
    (P : Pl D.host.E) (hP : Good R.toRealDat A3.A.μ0 P) (d : List ℤ) (hd : ¬ IsLab D.sp.X' P d) (x : (R.HX A3.A.μ0).H) :
    hX P (Finsupp.single d 1) x = 0 := by
  apply heInj
  rw [hXops P hP, map_zero, hkF_single_of_not _ _ _ hd]

set_option maxHeartbeats 4000000 in
theorem opv_lemma (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hCore : Core R.toRealDat F.lv2) (hIn : R.IsInert)
    (hAll : R.AllPlaces) (hX : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HX A3.A.μ0).H)
    (hXops : GlobalTheory.Hk3.IsOpsX R.toRealDat A3.A.μ0 hX)
    (q : A3.fam3.base3.Ix) (Q : A3.okI A3.A.μ0) (y : List ℕ) (hy : Formalism.L2.Col.InertTypeOk D.sp.X'.rank y)
    (v : (R.HX A3.A.μ0).H)
    (hv : v ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)))
    (l : ℂ) (hl : hX (R.plI Q.1) (Finsupp.single (labIn D.sp.X'.rank y) 1) v = l • v) (hv0 : v ≠ 0) :
    l = D.what₂.embLL (q.1.2 (Q.1, y)) := by
  have hT := GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels R.toRealDat F.lv2 hCore.lev hCore.fam hCore.models A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
    (fun k => R.plI k.1) (fun k => labIn D.sp.X'.rank k.2) (A3.heckeRI A3.A.μ0)
    (fun k => Formalism.L2.Col.InertTypeOk D.sp.X'.rank k.2)
    (fun k hk => ⟨(tie2 R hIn hAll k.1).1, (tie2 R hIn hAll k.1).2, labIn_pw hk⟩)
    (hIn.hR A3.A.μ0).some (Q, y) hy
  exact eig_eq_of_mem_span D.what₂.embLL (R.jX A3.A.μ0) (A3.heckeRI A3.A.μ0 (Q, y)) _ (q.1.2 (Q.1, y)) _
    (fun f => (hT.2.2.2 hX hXops f).symm) (inertPartition_le_partF (A3.rowI A3.A.μ0) q.1 (Q, y)) v hv l hl hv0

end Ctx2

section Ctx3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in

def muQ (Q : A3.okI A3.A.μ0) (q : A3.fam3.base3.Ix) (d : List ℤ) : ℂ :=
  if h : ∃ y, Formalism.L2.Col.InertTypeOk D.sp.X'.rank y ∧ d = labIn D.sp.X'.rank y then
    D.what₂.embLL (q.1.2 (Q.1, h.choose)) else 0

set_option maxHeartbeats 4000000 in
theorem mu_lemma (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hCore : Core R.toRealDat F.lv2) (hIn : R.IsInert)
    (hAll : R.AllPlaces) (hX : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HX A3.A.μ0).H)
    (hXops : GlobalTheory.Hk3.IsOpsX R.toRealDat A3.A.μ0 hX) (heInj : Function.Injective (R.HX A3.A.μ0).e)
    (Q : A3.okI A3.A.μ0) (hTS : TwoSided R.toRealDat A3.A.μ0 (R.plI Q.1))
    (q : A3.fam3.base3.Ix) (e : Pl D.host.E → List ℤ → ℂ) (v : (R.HX A3.A.μ0).H) (hv0 : v ≠ 0)
    (hvs : v ∈ Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms)))
    (hvE : ∀ cX c0, GlobalTheory.Hk3.MatchE R.toRealDat A3.A.μ0 (R.plI Q.1) cX c0 →
        hX (R.plI Q.1) cX v = GlobalTheory.Hk3.evC (Yc D 0) (R.plI Q.1) (fun d => e (R.plI Q.1) (dualLab d)) c0 • v)
    (d' : List ℤ) : hX (R.plI Q.1) (Finsupp.single d' 1) v = muQ Q q d' • v := by
  unfold muQ
  split_ifs with h
  · obtain ⟨c0', hM'⟩ := hTS.1.1 (Finsupp.single d' 1)
    have h3 := hvE _ _ hM'
    rw [h3]
    congr 1
    refine opv_lemma R F hCore hIn hAll hX hXops q Q h.choose h.choose_spec.1 v hvs _ ?_ hv0
    rw [← h.choose_spec.2]; exact h3
  · rw [zero_smul]
    exact zer_lemma R hX hXops heInj _ (tie2 R hIn hAll Q).1 d'
      (fun hl => h (labs _ _ _ hl (tie2 R hIn hAll Q).2)) v

set_option maxHeartbeats 4000000 in
theorem dir1 (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hCore : Core R.toRealDat F.lv2)
    (hSchur : SchurAll R.toRealDat) (hSF : IsSF R.toRealDat R.SF) (hEEc : ∀ c, R.EEc c = EEc R.toRealDat R.SF c)
    (hInj : ∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) (hIn : R.IsInert) (hAll : R.AllPlaces)
    (hX : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HX A3.A.μ0).H)
    (hXops : GlobalTheory.Hk3.IsOpsX R.toRealDat A3.A.μ0 hX) (heInj : Function.Injective (R.HX A3.A.μ0).e)
    (hTS : ∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P)
    (i : Fin D.R.m) (p p' : A3.fam3.base3.Ix) (c c' : Pl D.host.E → List ℤ → ℂ) (hc : R.Carries p c) (hc' : R.Carries p' c')
    (hp : ∀ k : A3.okI A3.A.μ0 × List ℕ, p.1.2 (k.1.1, k.2) = p'.1.2 (k.1.1, k.2))
    (P : Pl D.host.E) (d : List ℤ) (hP : Good R.toRealDat A3.A.μ0 P) (hconj : conjPl P = P) (hd : IsLab (Wc D i) P d) :
    c P d = c' P d := by
  obtain ⟨Q, hQ⟩ := tie1 R hIn hAll P hP hconj
  subst hQ
  have hdY : IsLab (Yc D 0) (R.plI Q.1) d := ((GlobalTheory.T.isLabel_thetaLiftSpace_iff_dual R.toRealDat F.lv2 (s := s) hCore i _ d hP).2).1 hd
  have hdd : dualLab d = d := ((GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Yc D 0) _ d).1 hdY).2.2 hconj
  obtain ⟨cX, hM⟩ := (hTS _ hP hconj).1.2 (Finsupp.single d 1)
  have hev : ∀ a : Pl D.host.E → List ℤ → ℂ,
      GlobalTheory.Hk3.evC (Yc D 0) (R.plI Q.1) (fun e => a (R.plI Q.1) (dualLab e)) (Finsupp.single d 1) = a (R.plI Q.1) d := by
    intro a
    simp [GlobalTheory.Hk3.evC, hdY, hdd]
  have key : ∀ (q : A3.fam3.base3.Ix) (e : Pl D.host.E → List ℤ → ℂ), R.Carries q e →
      e (R.plI Q.1) d = cX.sum fun d' z => z * muQ Q q d' := by
    intro q e he
    obtain ⟨v, hv0, hvs, hvE⟩ := ev_lemma R F hCore hSchur hSF hEEc hInj hX hXops q e he
    have h1 := hvE _ hP cX _ hM
    rw [hev] at h1
    exact key_generic (hX (R.plI Q.1)) (lin_lemma R hX hXops heInj _ hP) (muQ Q q) v hv0
      (mu_lemma R F hCore hIn hAll hX hXops heInj Q (hTS _ hP hconj) q e v hv0 hvs (hvE _ hP)) cX _ h1
  rw [key p c hc, key p' c' hc']
  refine Finsupp.sum_congr fun d' _ => ?_
  congr 1
  unfold muQ
  split_ifs with h
  · exact congrArg D.what₂.embLL (hp (Q, h.choose))
  · rfl

set_option maxHeartbeats 4000000 in
theorem dir2 (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hCore : Core R.toRealDat F.lv2)
    (hSchur : SchurAll R.toRealDat) (hSF : IsSF R.toRealDat R.SF) (hEEc : ∀ c, R.EEc c = EEc R.toRealDat R.SF c)
    (hInj : ∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) (hIn : R.IsInert) (hAll : R.AllPlaces)
    (hX : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HX A3.A.μ0).H)
    (hXops : GlobalTheory.Hk3.IsOpsX R.toRealDat A3.A.μ0 hX)
    (hTS : ∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P)
    (hJunk : ∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧
      A3.heckeRI t k = A3.heckeRI t (k.1, y))
    (i : Fin D.R.m) (p p' : A3.fam3.base3.Ix) (c c' : Pl D.host.E → List ℤ → ℂ) (hc : R.Carries p c) (hc' : R.Carries p' c')
    (hcc : ∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D i) P d → c P d = c' P d)
    (k : A3.okI A3.A.μ0 × List ℕ) : p.1.2 (k.1.1, k.2) = p'.1.2 (k.1.1, k.2) := by
  obtain ⟨Q, y⟩ := k
  obtain ⟨hPg, hPc⟩ := tie2 R hIn hAll Q
  have eqv : ∀ (q : A3.fam3.base3.Ix) (e : Pl D.host.E → List ℤ → ℂ), R.Carries q e → ∀ y',
      Formalism.L2.Col.InertTypeOk D.sp.X'.rank y' → ∀ c0, GlobalTheory.Hk3.MatchE R.toRealDat A3.A.μ0 (R.plI Q.1)
        (Finsupp.single (labIn D.sp.X'.rank y') 1) c0 →
      D.what₂.embLL (q.1.2 (Q.1, y')) = GlobalTheory.Hk3.evC (Yc D 0) (R.plI Q.1) (fun d => e (R.plI Q.1) (dualLab d)) c0 := by
    intro q e he y' hy' c0 hM
    obtain ⟨v, hv0, hvs, hvE⟩ := ev_lemma R F hCore hSchur hSF hEEc hInj hX hXops q e he
    exact (opv_lemma R F hCore hIn hAll hX hXops q Q y' hy' v hvs _ (hvE _ hPg _ _ hM) hv0).symm
  have nb : ∀ (q : A3.fam3.base3.Ix) (e : Pl D.host.E → List ℤ → ℂ), R.Carries q e →
      (A3.rowI A3.A.μ0).inertTypeEigenspaceSum q.1 ≠ ⊥ := by
    intro q e he hb
    obtain ⟨v, hv0, hvs, -⟩ := ev_lemma R F hCore hSchur hSF hEEc hInj hX hXops q e he
    rw [hb] at hvs
    simp at hvs
    exact hv0 hvs
  have evEq : ∀ c0, GlobalTheory.Hk3.evC (Yc D 0) (R.plI Q.1) (fun d => c (R.plI Q.1) (dualLab d)) c0 =
      GlobalTheory.Hk3.evC (Yc D 0) (R.plI Q.1) (fun d => c' (R.plI Q.1) (dualLab d)) c0 := by
    intro c0
    unfold GlobalTheory.Hk3.evC
    refine Finsupp.sum_congr fun d _ => ?_
    split_ifs with hd
    · have hdd : dualLab d = d := ((GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Yc D 0) _ d).1 hd).2.2 hPc
      show c0 d * c (R.plI Q.1) (dualLab d) = c0 d * c' (R.plI Q.1) (dualLab d)
      rw [hdd, hcc _ d hPg hPc (((GlobalTheory.T.isLabel_thetaLiftSpace_iff_dual R.toRealDat F.lv2 (s := s) hCore i _ d hPg).2).2 hd)]
    · rfl
  have valid : ∀ y', Formalism.L2.Col.InertTypeOk D.sp.X'.rank y' → p.1.2 (Q.1, y') = p'.1.2 (Q.1, y') := by
    intro y' hy'
    obtain ⟨c0, hM⟩ := (hTS _ hPg hPc).1.1 (Finsupp.single (labIn D.sp.X'.rank y') 1)
    apply D.what₂.embLL.injective
    rw [eqv p c hc y' hy' c0 hM, eqv p' c' hc' y' hy' c0 hM, evEq]
  have hrank : (A3.A.fam.R A3.A.μ0).n = D.sp.X'.rank := R.B.rankR.symm
  rcases hJunk A3.A.μ0 (Q, y) with h0 | ⟨y', hy', hop⟩
  · have z : ∀ (q : A3.fam3.base3.Ix) (e : Pl D.host.E → List ℤ → ℂ), R.Carries q e → q.1.2 (Q.1, y) = 0 := by
      intro q e he
      refine eq_of_le_maxGen (A3.heckeRI A3.A.μ0 (Q, y)) _ _ _ (nb q e he) (inertPartition_le_partF (A3.rowI A3.A.μ0) q.1 (Q, y)) ?_
      rw [h0]
      intro x _
      exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by simp⟩
    show p.1.2 (Q.1, y) = p'.1.2 (Q.1, y)
    rw [z p c hc, z p' c' hc']
  · have w : ∀ (q : A3.fam3.base3.Ix) (e : Pl D.host.E → List ℤ → ℂ), R.Carries q e →
        q.1.2 (Q.1, y) = q.1.2 (Q.1, y') := by
      intro q e he
      refine eq_of_le_maxGen (A3.heckeRI A3.A.μ0 (Q, y)) _ _ _ (nb q e he) (inertPartition_le_partF (A3.rowI A3.A.μ0) q.1 (Q, y)) ?_
      rw [hop]
      exact inertPartition_le_partF (A3.rowI A3.A.μ0) q.1 (Q, y')
    show p.1.2 (Q.1, y) = p'.1.2 (Q.1, y)
    rw [w p c hc, w p' c' hc']
    exact valid y' (hrank ▸ hy')

end Ctx3

set_option maxHeartbeats 4000000 in

theorem inert_vals_iff_labels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∀ (i : Fin D.R.m) (p p' : A3.fam3.base3.Ix) c c', R.Carries p c → R.Carries p' c' → ((∀ k : A3.okI A3.A.μ0 × List ℕ, p.1.2 (k.1.1, k.2) = p'.1.2 (k.1.1, k.2)) ↔ (∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D i) P d → c P d = c' P d)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hCW hEx hSchur hTS hJunk hInj i p p' c c' hc hc'
  obtain ⟨hCore, hSF, hEEc, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hCW hEx
  obtain ⟨hX, hXops, -⟩ := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hCore.lev hCore.fam hCore.models).1 A3.A.μ0
  have heInj : Function.Injective (R.HX A3.A.μ0).e := (hCore.models.HX A3.A.μ0).1
  exact ⟨fun hp P d hP hconj hd => dir1 R F (s := s) hCore hSchur hSF hEEc hInj hCW.inert hCW.allPl hX hXops heInj hTS i
      p p' c c' hc hc' hp P d hP hconj hd,
    fun hcc k => dir2 R F (s := s) hCore hSchur hSF hEEc hInj hCW.inert hCW.allPl hX hXops hTS hJunk.1 i p p' c c' hc hc'
      hcc k⟩

end GlobalTheory.InertValLab
