import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DtTiedTrue
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.ChiDVal

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

section Gen

variable {L : Type} [Field L] [NumberField L]

theorem ideles_snd_mul (a b : Ideles L) (v : HeightOneSpectrum (𝓞 L)) :
    ((a * b : Ideles L) : AdeleRing (𝓞 L) L).2 v = (a : AdeleRing (𝓞 L) L).2 v * (b : AdeleRing (𝓞 L) L).2 v := rfl

theorem ideles_snd_inv_mul (a : Ideles L) (v : HeightOneSpectrum (𝓞 L)) :
    ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v * (a : AdeleRing (𝓞 L) L).2 v = 1 := by
  rw [← ideles_snd_mul, inv_mul_cancel]
  rfl

theorem ideles_finite (a : Ideles L) : {v : HeightOneSpectrum (𝓞 L) | ¬ Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1}.Finite := by
  have h1 := (a : AdeleRing (𝓞 L) L).2.2
  have h2 := ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2.2
  refine Filter.eventually_cofinite.1 ((h1.and h2).mono fun v hv => ?_)
  have e1 : Valued.v ((a : AdeleRing (𝓞 L) L).2 v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv.1
  have e2 : Valued.v (((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv.2
  have e3 := congrArg Valued.v (ideles_snd_inv_mul a v)
  rw [map_mul, map_one] at e3
  refine le_antisymm e1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) * Valued.v ((a : AdeleRing (𝓞 L) L).2 v) := e3.symm
    _ ≤ 1 * Valued.v ((a : AdeleRing (𝓞 L) L).2 v) := mul_le_mul_left e2 _
    _ = _ := one_mul _

theorem exists_unif_zpow (v : HeightOneSpectrum (𝓞 L)) (y : v.adicCompletion L) (hy : y ≠ 0) :
    ∃ n : ℤ, Valued.v (((atFin v (unif v)) ^ n : (v.adicCompletion L)ˣ) : v.adicCompletion L) = Valued.v y := by
  have h0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  refine ⟨-WithZero.log (Valued.v y), ?_⟩
  have hu : Valued.v ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec v
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hu, ← WithZero.exp_zsmul]
  simp [WithZero.exp_log h0]

theorem ideles_values {Gp : Type} [CommGroup Gp] (f : Ideles L →* Gp)
    (hU : ∀ a : Ideles L, (∀ v, Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1) → f a = 1) (S : Subgroup Gp)
    (hS : ∀ v, f (localIdele L v (atFin v (unif v))) ∈ S) (a : Ideles L) : f a ∈ S := by
  classical
  have key : ∀ (T : Finset (HeightOneSpectrum (𝓞 L))) (a : Ideles L),
      (∀ v, v ∉ T → Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1) → f a ∈ S := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro a ha
      rw [hU a fun v => ha v (Finset.notMem_empty v)]
      exact S.one_mem
    | insert v0 T _ ih =>
      intro a ha
      have hy : (a : AdeleRing (𝓞 L) L).2 v0 ≠ 0 := by
        intro h0
        have := ideles_snd_inv_mul a v0
        rw [h0, mul_zero] at this
        exact zero_ne_one this
      obtain ⟨n, hn⟩ := exists_unif_zpow v0 _ hy
      have h1 : f (a * (localIdele L v0 ((atFin v0 (unif v0)) ^ n))⁻¹) ∈ S := by
        refine ih _ fun v hv => ?_
        rw [← map_inv, ideles_snd_mul]
        by_cases hvv : v = v0
        · subst hvv
          rw [localIdele_snd_self, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hn]
          exact mul_inv_cancel₀ ((Valuation.ne_zero_iff _).2 hy)
        · rw [(localIdele_isSupportedAt L v0 _).2 v hvv, mul_one]
          exact ha v fun h => (Finset.mem_insert.1 h).elim hvv hv
      have h2 : f a = f (a * (localIdele L v0 ((atFin v0 (unif v0)) ^ n))⁻¹) * f (localIdele L v0 (atFin v0 (unif v0))) ^ n := by
        rw [map_mul, map_inv, map_zpow (localIdele L v0), map_zpow f, inv_mul_cancel_right]
      rw [h2]
      exact S.mul_mem h1 (S.zpow_mem (hS v0) n)
  exact key (ideles_finite a).toFinset a fun v hv => by
    by_contra h
    exact hv ((ideles_finite a).mem_toFinset.2 h)

end Gen

def coeffUnits (D : D7) : Subgroup ℂˣ where
  carrier := {z | ∃ r : D.what₂.LL, D.what₂.embLL r = (z : ℂ)}
  one_mem' := ⟨1, map_one _⟩
  mul_mem' := by
    rintro a b ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r * s, by rw [map_mul, hr, hs, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨r, hr⟩
    exact ⟨r⁻¹, by rw [map_inv₀, hr, Units.val_inv_eq_inv_val]⟩

theorem chiD_mem_of {D : D7} {C : CharFrame D} (T : DtTied D C) (hV : C.chiPsi.ValuesIn 0 D.what₂.embLL) :
    ∀ z : D.Dt, ∃ r : D.what₂.LL, D.what₂.embLL r = ((D.chiD z : ℂˣ) : ℂ) := by
  intro z
  obtain ⟨a, rfl⟩ := T.surj z
  refine ideles_values (D.chiD.comp T.eDt) (fun a ha => D.chiD_UO _ ((T.UO_eq _).2 ⟨a, ha, rfl⟩)) (coeffUnits D) (fun v => ?_) a
  obtain ⟨y, hy⟩ := hV v (C.isChi.unr v)
  refine ⟨y, ?_⟩
  rw [hy]
  show _ = ((D.chiD (T.eDt (localIdele D.host.E v (atFin v (unif v)))) : ℂˣ) : ℂ)
  rw [T.chiD_eq _ (fun w => (localIdele_isSupportedAt D.host.E v _).1 w)]
  unfold HChar.valTw
  rw [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one]
  rfl

theorem chiD_values_and_cc_top : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt), (∀ z : (w.D Z).Dt, ∃ r : (w.D Z).what₂.LL, (w.D Z).what₂.embLL r = (((w.D Z).chiD z : ℂˣ) : ℂ)) ∧ ∀ (L : SizeData₂ (w.D Z)) (hT : GatTies (w.D Z)) (Gi : G.Inst (w.D Z) L) (Gl : G.LatInst (w.D Z)) (K : G.Consts) (Y : DivX (w.D Z)) (cX : ExtraC) (ex : Extra (w.D Z) L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.cc = ⊤ := by
  intro B f T w Z
  refine ⟨?_, fun L hT Gi Gl K Y cX ex t => t.cc_rec.trans B.toPre.ccK_top⟩
  obtain ⟨dt, -⟩ := TC.dtTied_true w.I w.ok w.pins w.l Z
  have hv : Formalism.L2.Host.ValLL0 (w.D Z) (TC.cf w.I w.l Z) := by
    rcases w with ⟨px, I, ok, C_eq, S_eq, xi_range, pins, l, l0, δ, exact, fld, val⟩
    subst C_eq
    exact val _ _ _ _ _ _
  exact chiD_mem_of dt hv.toLL.chiPsi

end GlobalTheory.Mem.ChiDVal
