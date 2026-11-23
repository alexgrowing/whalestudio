import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorBaseChangeForms
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ComplexHeckeAdjoint

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

theorem levChi_one {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    ∀ k ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv), levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1 := by
  intro k _
  have h1 : ext1 (R.datWp i R.triv).P.H (R.datWp i R.triv).P.chi (rTup (R.βW i) (R.datWp i R.triv) (Lev.finE (Wc D i) k)) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h1]
  simp [LevCh.datWp, datY]

theorem conj_eq {D : D7} {P P' : PlE D.host} (h : Formalism.BasicNotions.IsConjPl D.host P P') : P' = Formalism.DivisionValues.conjPl P := by
  have hc : ∀ y : 𝓞 D.host.E, Formalism.HermitianLattices.Ext.L3.conjO D.host.E y = Formalism.DivisionValues.cO D.host.E y := fun y =>
    RingOfIntegers.ext (by simp [Formalism.DivisionValues.cO, Formalism.HermitianLattices.Ext.L3.conjO_coe])
  have hcc : ∀ y : 𝓞 D.host.E, Formalism.DivisionValues.cO D.host.E (Formalism.DivisionValues.cO D.host.E y) = y := fun y =>
    RingOfIntegers.ext (by simp [Formalism.DivisionValues.cO])
  rw [GlobalTheory.ConjPlaceOff.isConjPl_iff] at h
  ext x
  show x ∈ P'.asIdeal ↔ x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E)
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro hx
    refine ⟨Formalism.DivisionValues.cO D.host.E x, (h _).2 ?_, hcc x⟩
    rwa [hc, hcc]
  · rintro ⟨y, hy, rfl⟩
    rw [← hc]
    exact (h y).1 hy

open GlobalTheory.HeckeParts in

theorem keep_adj {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    {L : LevDat D.host.E ℂ V.rank} (hβ : IsBaseFrame V β Λ N) {P : Pl D.host.E} (hP : OffLevel L N P)
    (hχ : ∀ k ∈ levG V β L, levChi V β L k = 1) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {HM : HMod (MMap M)} {U : Submodule ℂ (MMap M)}
    (hU : U = Mult θ M (levS V β L) (levChi V β L)) {ip : MMap M → MMap M → ℂ} {c : ℂ}
    (hip : ∀ T T', ip T T' = c * ipM M μ 𝓕 T T') (h : HM.Is U ip) {x : GA D V} {A A' : Finset (GA D V)}
    (hA : LocRep (levG V β L) P x A) (hA' : LocRep (levG V β L) P x⁻¹ A') :
    (∀ y, ∃ y', HM.e y' = heckeOn M A (HM.e y)) ∧ (∀ y, ∃ y', HM.e y' = heckeOn M A' (HM.e y)) ∧
      ∀ y z y' z', HM.e y' = heckeOn M A (HM.e y) → HM.e z' = heckeOn M A' (HM.e z) → inner ℂ y' z = inner ℂ y z' := by
  subst hU
  have h' : HM.Is (Mult θ M (levS V β L) (levChi V β L)) fun T T' => c * ipM M μ 𝓕 T T' :=
    ⟨h.1, h.2.1, fun y z => (h.2.2 y z).trans (hip _ _)⟩
  have hmem : ∀ y, HM.e y ∈ Mult θ M (levS V β L) (levChi V β L) := fun y => h.2.1 ▸ LinearMap.mem_range_self _ y
  have keep : ∀ {w : GA D V} {C : Finset (GA D V)}, LocRep (levG V β L) P w C → ∀ y,
      heckeOn M C (HM.e y) ∈ LinearMap.range HM.e := by
    intro w C hC y
    rw [h.2.1]
    exact hC.mult hβ hP (fun k hk => levG_le_flag hk) (hmem y) (fun v => rInv_of_mem hχ (hmem y) v)
  have lift : ∀ {w : GA D V} {C : Finset (GA D V)}, LocRep (levG V β L) P w C →
      ∃ t : Module.End ℂ HM.H, ∀ y, HM.e (t y) = heckeOn M C (HM.e y) := by
    intro w C hC
    refine ⟨(LinearEquiv.ofInjective _ h.1).symm.toLinearMap ∘ₗ ((heckeOn M C ∘ₗ HM.e).codRestrict _ (keep hC)),
      fun y => ?_⟩
    exact congrArg Subtype.val ((LinearEquiv.ofInjective _ h.1).apply_symm_apply _)
  obtain ⟨t, ht⟩ := lift hA
  obtain ⟨t', ht'⟩ := lift hA'
  refine ⟨fun y => keep hA y, fun y => keep hA' y, fun y z y' z' hy hz => ?_⟩
  obtain rfl : y' = t y := h.1 (hy.trans (ht y).symm)
  obtain rfl : z' = t' z := h.1 (hz.trans (ht' z).symm)
  exact inner_hecke hχ hμ h𝓕 h' le_rfl hA.2 hA'.2 (hA.card hβ hP hA') ht ht' y z

end GlobalTheory.ComplexHeckeAdjoint

namespace GlobalTheory.CxHeckeAdj

set_option maxHeartbeats 1600000 in

theorem hecke_adjoint : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3),
    Rl.Char3 F → ∀ (i : Fin D.R.m) (k : ℕ) (P P' : PlE D.host), IsSplitPl D.host P → IsConjPl D.host P P' →
    Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
    Formalism.IndefR.Bridge.SplitOff P' (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
    ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal → 1 ≤ k → k ≤ D.R.r →
    ∃ (α α' : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Wc D i)) (R R' : Finset (Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Wc D i))),
      Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) P k α ∧
      Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α R ∧
      Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) P' k α' ∧
      Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α' R' ∧
      (∀ x, ∃ x', (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x' =
        Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x)) ∧
      (∀ y, ∃ y', (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y' =
        Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R' ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y)) ∧
      ∀ x y x' y' : (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).H,
        (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x' =
          Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x) →
        (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y' =
          Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R' ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y) →
        ⟪x', y⟫_ℂ = ⟪x, y'⟫_ℂ := by

  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ Rl F hc i k P P' _hsp hcj hso hso' _h2 _h2' _hk1 hk
  classical
  obtain ⟨c, hβ⟩ := hc.lev.βW i
  have hrk : k ≤ (Formalism.IndefR.Links.Wc D i).rank := by
    rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2]; exact hk
  have hoff : ∀ Q : Formalism.L2.DIV.Pl D.host.E, Formalism.IndefR.Bridge.SplitOff Q (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
      GlobalTheory.HeckeParts.OffLevel (Rl.datWp i Rl.triv) (1 ^ c) Q := by
    intro Q hQ
    refine ⟨hQ.1, ?_, ?_⟩
    · rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 Q.isPrime.ne_top
    · intro PP hPP
      have hPP' : PP ∈ Rl.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
      have hS : PP ∈ (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hc.fam.Sb hPP'
      refine ⟨fun h => hQ.2.1 (h ▸ hS), fun h => hQ.2.2 PP hS ?_⟩
      rw [Formalism.L2.Col.conjIdeal_asIdeal]
      refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ Q).isPrime.ne_top fun a ha => ?_
      obtain ⟨a', ha', e⟩ := h a ha
      rw [Formalism.L2.Col.mem_conjP]
      have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
      rwa [this]
  obtain ⟨α, A, A', hα, hA, hA'⟩ := GlobalTheory.HeckeParts.exists_hecke hβ (hoff P hso) hrk
  obtain ⟨α₂, B, B', hα₂, -, -⟩ := GlobalTheory.HeckeParts.exists_hecke hβ (hoff P' hso') hrk
  have hα₂' : Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) (Formalism.DivisionValues.conjPl P) k α₂ :=
    GlobalTheory.ComplexHeckeAdjoint.conj_eq hcj ▸ hα₂
  obtain ⟨e, ϖ, he, -, -, -⟩ := id hα
  obtain ⟨a, ha, b, hb, hab⟩ := GlobalTheory.SplitHeckeAdj.hecke_conj (Formalism.IndefR.Links.Wc D i) he hα hα₂'
  obtain ⟨Lp, -, -, -, hK⟩ := GlobalTheory.HeckeParts.loc_package hβ (hoff P hso) he
  have hA₂ : Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α₂ A :=
    GlobalTheory.SplitHeckeAdj.isDC_of_mem (Subgroup.inv_mem _ ((hK a).1 ha).1) (Subgroup.inv_mem _ ((hK b).1 hb).1)
      (by rw [hab]; group) hA.2

  obtain ⟨hk1, hk2, hadj⟩ := GlobalTheory.ComplexHeckeAdjoint.keep_adj hβ (hoff P hso) (GlobalTheory.ComplexHeckeAdjoint.levChi_one Rl.toRealDat i)
    (hc.models.νW i).1.1 (hc.models.νW i).2 rfl
    (fun _ _ => rfl) (hc.models.HW i (Formalism.IndefR.Links.sg0 D A3.A)) hA' hA
  exact ⟨α, α₂, A', A, hα, hA'.2, hα₂, hA₂, hk1, hk2, hadj⟩

end GlobalTheory.CxHeckeAdj
