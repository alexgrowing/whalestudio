import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite.TypeSpan

variable {D : D7} {V W : HSp D}

theorem levChi_mul' {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {k k' : GA D V}
    (hk : k ∈ levG V β L) (hk' : k' ∈ levG V β L) :
    levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  have e := (Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩
  have e' : Formalism.L2.DIV.levFn β L (finE V k * finE V k') =
      Formalism.L2.DIV.levFn β L (finE V k) * Formalism.L2.DIV.levFn β L (finE V k') := e
  unfold levChi
  rw [map_mul, e', Units.val_mul]

theorem levChi_ne_zero (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (k : GA D V) :
    levChi V β L k ≠ 0 := by
  unfold levChi
  exact Units.ne_zero _

theorem eventually_levChi_one (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    ∀ᶠ κ in nhds (1 : GA D V), levChi V β L κ = 1 := by
  classical
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨-, -, h3⟩ := hh
  unfold levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one β L _ fun PP hP => h3 PP (by rcases hP with h | h <;> simp [h]), Units.val_one]

end GlobalTheory.DownLift.GenFinite.TypeSpan

namespace GlobalTheory.DownLift.GenFinite

open GlobalTheory.DownLift.GenFinite.TypeSpan

theorem typeSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → f ∈ Submodule.span ℂ ({φ | GlobalTheory.DownLift.GenFinite.TypeVec R i t φ} ∪ GlobalTheory.DownLift.GenFinite.TypeDiff R i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ hP i t f hf
  classical
  have hW := (hP i t).datum
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (Vc D i).gram
  obtain ⟨U, U', hUo, -, hfix⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D R.ψ hW.std (Vc D i) (Wc D i) (R.ωP i t)
    (GlobalTheory.Ker.isWeak_of_datum hW) hW.om_cont f hf
  set J := levG (Vc D i) (R.βV i) (R.datVt i t) with hJ
  set lam := levChi (Vc D i) (R.βV i) (R.datVt i t) with hlam
  set om := R.ωP i t with hom
  have hmul : ∀ a b : GA D (Vc D i), om (a * b, 1) = om (a, 1) * om (b, 1) := fun a b => by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hone : om (1, 1) = 1 := by rw [← Prod.one_eq_mk, map_one]
  have hlm : ∀ {a b : GA D (Vc D i)}, a ∈ J → b ∈ J → lam (a * b) = lam a * lam b := fun ha hb => levChi_mul' ha hb
  have hlne : ∀ a : GA D (Vc D i), lam a ≠ 0 := fun a => levChi_ne_zero _ _ a
  have hlam1 : lam 1 = 1 := by
    have e := hlm (one_mem J) (one_mem J)
    rw [mul_one] at e
    have h0 := hlne 1
    have e' : lam 1 * 1 = lam 1 * lam 1 := by rw [mul_one]; exact e
    exact (mul_left_cancel₀ h0 e').symm

  let N : Subgroup J :=
    { carrier := {κ | om ((κ : GA D (Vc D i)), 1) f = f ∧ lam κ = 1}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨?_, ?_⟩
        · show om ((a : GA D (Vc D i)) * b, 1) f = f
          rw [hmul, Module.End.mul_apply, hb1, ha1]
        · show lam ((a : GA D (Vc D i)) * b) = 1
          rw [hlm a.2 b.2, ha2, hb2, one_mul]
      one_mem' := by
        refine ⟨?_, ?_⟩
        · show om (1, 1) f = f
          rw [hone]; rfl
        · exact hlam1
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨?_, ?_⟩
        · show om ((a : GA D (Vc D i))⁻¹, 1) f = f
          conv_lhs => rw [← ha1]
          rw [← Module.End.mul_apply, ← hmul, inv_mul_cancel, hone]; rfl
        · show lam ((a : GA D (Vc D i))⁻¹) = 1
          have e := hlm (inv_mem a.2) a.2
          rw [inv_mul_cancel, hlam1, ha2, mul_one] at e
          exact e.symm }
  have hNo : IsOpen (N : Set J) := by
    refine Subgroup.isOpen_of_mem_nhds N (g := 1) ?_
    have h1 : {x : GA D (Vc D i) | x ∈ U ∧ lam x = 1} ∈ nhds (1 : GA D (Vc D i)) :=
      Filter.inter_mem (hUo.mem_nhds U.one_mem) (eventually_levChi_one _ _)
    have h2 := (continuous_subtype_val (p := fun x => x ∈ J)).continuousAt (x := (1 : J)).preimage_mem_nhds h1
    exact Filter.mem_of_superset h2 fun κ hκ => ⟨hfix _ hκ.1 κ.2.1 1 U'.one_mem (one_mem _), hκ.2⟩
  haveI : CompactSpace J := isCompact_iff_compactSpace.mp (GlobalTheory.ParahoricCompact.isCompact_levG _ _ _)
  haveI : Finite (J ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  letI : Fintype (J ⧸ N) := Fintype.ofFinite _

  let Fv : J → (WO (Vc D i) (Wc D i) → ℂ) := fun κ => lam κ • om ((κ : GA D (Vc D i)), 1) f
  have hFvN : ∀ (a n : J), n ∈ N → Fv (a * n) = Fv a := by
    rintro a n ⟨hn1, hn2⟩
    show lam ((a : GA D (Vc D i)) * n) • om ((a : GA D (Vc D i)) * n, 1) f = lam a • om ((a : GA D (Vc D i)), 1) f
    rw [hlm a.2 n.2, hn2, mul_one, hmul, Module.End.mul_apply, hn1]
  let Fb : J ⧸ N → (WO (Vc D i) (Wc D i) → ℂ) := fun q => Fv q.out
  have hFb : ∀ κ : J, Fb (κ : J ⧸ N) = Fv κ := by
    intro κ
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N κ
    show Fv (κ : J ⧸ N).out = Fv κ
    rw [hn]
    exact hFvN κ n n.2
  have hFbTh : ∀ q, IsThetaFunO R.ψ (Vc D i) (Wc D i) (Fb q) := fun q =>
    theta_smul _ (hW.om_pres _ _ hf)

  have hact : ∀ (κ' : J) (q : J ⧸ N), om ((κ' : GA D (Vc D i)), 1) (Fb q) = (lam κ')⁻¹ • Fb (κ' • q) := by
    intro κ' q
    induction q using QuotientGroup.induction_on with
    | H κ =>
      rw [MulAction.Quotient.smul_mk, hFb, hFb]
      show om ((κ' : GA D (Vc D i)), 1) (lam κ • om ((κ : GA D (Vc D i)), 1) f) =
        (lam κ')⁻¹ • (lam ((κ' : GA D (Vc D i)) * κ) • om ((κ' : GA D (Vc D i)) * κ, 1) f)
      rw [map_smul, hmul, Module.End.mul_apply, hlm κ'.2 κ.2, smul_smul, ← mul_assoc,
        inv_mul_cancel₀ (hlne _), one_mul]
  set c : ℂ := ((Fintype.card (J ⧸ N) : ℕ) : ℂ)⁻¹ with hc
  set fJ := c • ∑ q, Fb q with hfJ
  have hfJv : TypeVec R i t fJ := by
    refine ⟨theta_smul _ (theta_sum Finset.univ Fb f hf fun q _ => hFbTh q), fun κ hκ => ?_⟩
    show om (κ, 1) fJ = (lam κ)⁻¹ • fJ
    have e : om (κ, 1) (∑ q, Fb q) = (lam κ)⁻¹ • ∑ q, Fb q := by
      rw [map_sum]
      have := fun q => hact ⟨κ, hκ⟩ q
      simp only [] at this
      rw [Finset.sum_congr rfl fun q _ => this q, ← Finset.smul_sum]
      congr 1
      exact Equiv.sum_comp (MulAction.toPerm (⟨κ, hκ⟩ : J)) Fb
    rw [hfJ, map_smul, e, smul_comm]
  have hdiff : ∀ q, f - Fb q ∈ Submodule.span ℂ ({φ | TypeVec R i t φ} ∪ TypeDiff R i t) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H κ =>
      rw [hFb]
      have e : f - Fv κ = (-lam κ) • (om ((κ : GA D (Vc D i)), 1) f - (lam κ)⁻¹ • f) := by
        show f - lam κ • om ((κ : GA D (Vc D i)), 1) f = _
        rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ (hlne _)]
        simp only [neg_smul, one_smul]
        abel
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨κ, κ.2, f, hf, rfl⟩))
  have hcard : ((Fintype.card (J ⧸ N) : ℕ) : ℂ) ≠ 0 := by
    have : 0 < Fintype.card (J ⧸ N) := Fintype.card_pos
    exact_mod_cast this.ne'
  have hsplit : f = fJ + c • ∑ q, (f - Fb q) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      hc, inv_mul_cancel₀ hcard, one_smul, hfJ]
    abel
  rw [hsplit]
  exact Submodule.add_mem _ (Submodule.subset_span (Or.inl hfJv))
    (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => hdiff q))

end GlobalTheory.DownLift.GenFinite

end
