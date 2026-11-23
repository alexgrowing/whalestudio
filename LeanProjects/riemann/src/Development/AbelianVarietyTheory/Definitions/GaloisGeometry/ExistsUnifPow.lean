import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemberChainFormsLevelPrimeEqMember
import Formalism.LocalToGlobal.UnitaryNorms.CharRat
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypTwA
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypChi

noncomputable section

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.KAat Formalism.MainNotions.G.ChartsLv Formalism.MainNotions.G.CmpJ.AgreeLv
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ChiDRat (D : D7) : Prop := ∀ z : D.Dt, ∃ r : D.what₂.LL, D.what₂.embLL r = ((D.chiD z : ℂˣ) : ℂ)

set_option maxHeartbeats 2000000 in
theorem chRat_ofChiD (h : ChiDRat D) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    {S : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad} (Y : DetTie S) (c : ℤ)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((DetTw.ofChiD Y c).ch x : ℂˣ) : ℂ) := by
  obtain ⟨r, hr⟩ := h (Y.dt x)
  refine ⟨r ^ c, ?_⟩
  rw [map_zpow₀, hr]
  show _ = (((D.chiD (Y.dt x)) ^ c : ℂˣ) : ℂ)
  rw [Units.val_zpow_eq_zpow_val]

set_option maxHeartbeats 2000000 in
theorem chRat_mem (h : ChiDRat D) {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)
    (dt : MemDt F) (i : ℕ) (hi : i + 1 ≤ D.R.m) :
    ∀ β cl, ∃ r : D.what₂.LL, D.what₂.embLL r = (((formsInMem F dt i hi).tw β).ch (((formsInMem F dt i hi).K β).y cl) : ℂ) := by
  by_cases h' : i + 1 = D.R.m
  · rw [formsInMem_top F dt i hi h']
    intro β cl
    exact chRat_ofChiD h _ _ _
  · rw [formsInMem_mid F dt i hi (by omega)]
    intro β cl
    exact chRat_ofChiD h _ _ _

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

theorem fillRec (ex : Extra D L hT Gi Gl Kc Dx cX) : ∀ u w hg, FillTie hT u w hg (Gl.Fl u w hg) := by
  intro u w hg v s b hb
  have h1 := ex.fills_all u w hg v s (b + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have h2 : wj D (b + 1) (hT.gat_pos u w hg ⟨v, s⟩) = (((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dif_pos (show b + 1 - 1 < D.R.m by simpa using hb), D.hcW_e]
    rfl
  rw [h2] at h1
  have e : ((((Gl.Fl u w hg).w v (b + 1) s : ℤ) : ℚ) : ℝ) =
      ((wG D.R ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩) (b + 1) : ℚ) : ℝ) := by
    rw [Rat.cast_intCast, h1]
    unfold wG G.kaJ
    push_cast
    ring
  exact Rat.cast_injective e

end GlobalTheory.Port

end

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

section Gen

variable {L : Type} [Field L] [NumberField L]

theorem ide_snd_mul (a b : Ideles L) (v : HeightOneSpectrum (𝓞 L)) :
    ((a * b : Ideles L) : AdeleRing (𝓞 L) L).2 v = (a : AdeleRing (𝓞 L) L).2 v * (b : AdeleRing (𝓞 L) L).2 v := rfl

theorem ide_snd_inv_mul (a : Ideles L) (v : HeightOneSpectrum (𝓞 L)) :
    ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v * (a : AdeleRing (𝓞 L) L).2 v = 1 := by
  rw [← ide_snd_mul, inv_mul_cancel]
  rfl

theorem ide_finite (a : Ideles L) : {v : HeightOneSpectrum (𝓞 L) | ¬ Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1}.Finite := by
  have h1 := (a : AdeleRing (𝓞 L) L).2.2
  have h2 := ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2.2
  refine Filter.eventually_cofinite.1 ((h1.and h2).mono fun v hv => ?_)
  have e1 : Valued.v ((a : AdeleRing (𝓞 L) L).2 v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv.1
  have e2 : Valued.v (((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv.2
  have e3 := congrArg Valued.v (ide_snd_inv_mul a v)
  rw [map_mul, map_one] at e3
  refine le_antisymm e1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) * Valued.v ((a : AdeleRing (𝓞 L) L).2 v) := e3.symm
    _ ≤ 1 * Valued.v ((a : AdeleRing (𝓞 L) L).2 v) := mul_le_mul_left e2 _
    _ = _ := one_mul _

theorem exists_unif_pow (v : HeightOneSpectrum (𝓞 L)) (y : v.adicCompletion L) (hy : y ≠ 0) :
    ∃ n : ℤ, Valued.v (((atFin v (unif v)) ^ n : (v.adicCompletion L)ˣ) : v.adicCompletion L) = Valued.v y := by
  have h0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  refine ⟨-WithZero.log (Valued.v y), ?_⟩
  have hu : Valued.v ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec v
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hu, ← WithZero.exp_zsmul]
  simp [WithZero.exp_log h0]

theorem ide_values {Gp : Type} [CommGroup Gp] (f : Ideles L →* Gp)
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
        have := ide_snd_inv_mul a v0
        rw [h0, mul_zero] at this
        exact zero_ne_one this
      obtain ⟨n, hn⟩ := exists_unif_pow v0 _ hy
      have h1 : f (a * (localIdele L v0 ((atFin v0 (unif v0)) ^ n))⁻¹) ∈ S := by
        refine ih _ fun v hv => ?_
        rw [← map_inv, ide_snd_mul]
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
  exact key (ide_finite a).toFinset a fun v hv => by
    by_contra h
    exact hv ((ide_finite a).mem_toFinset.2 h)

end Gen

variable {D : D7}

def ratSub (D : D7) : Subgroup ℂˣ where
  carrier := {z | ∃ r : D.what₂.LL, D.what₂.embLL r = (z : ℂ)}
  one_mem' := ⟨1, map_one _⟩
  mul_mem' := by
    rintro a b ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r * s, by rw [map_mul, hr, hs, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨r, hr⟩
    exact ⟨r⁻¹, by rw [map_inv₀, hr, Units.val_inv_eq_inv_val]⟩

theorem chiDRat_of {C : CharFrame D} (T : DtTied D C) (hV : C.chiPsi.ValuesIn 0 D.what₂.embLL) : ChiDRat D := by
  intro z
  obtain ⟨a, rfl⟩ := T.surj z
  refine ide_values (D.chiD.comp T.eDt) (fun a ha => D.chiD_UO _ ((T.UO_eq _).2 ⟨a, ha, rfl⟩)) (ratSub D) (fun v => ?_) a
  obtain ⟨y, hy⟩ := hV v (C.isChi.unr v)
  refine ⟨y, ?_⟩
  rw [hy]
  show _ = ((D.chiD (T.eDt (localIdele D.host.E v (atFin v (unif v)))) : ℂˣ) : ℂ)
  rw [T.chiD_eq _ (fun w => (localIdele_isSupportedAt D.host.E v _).1 w)]
  unfold HChar.valTw
  rw [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one]
  rfl

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

end GlobalTheory.Port

end

end
