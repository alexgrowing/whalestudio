import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.PinModel

variable {D : D7} {u : D.what₂.Word}

theorem exists_finM (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (V.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ a ∈ GfC V, GlobalTheory.AdForm.finM V hn a = y.1.1 := by
  subst hn
  obtain ⟨a, ha, e⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V ⟨y.1, y.2⟩
  refine ⟨a, ha, ?_⟩
  have e2 : (finE V a : GL _ _) = y.1 := congrArg Subtype.val e
  rw [← e2]
  rfl

theorem exists_transport_adelic_correction {X : HidaSetting D} {F : Formalism.L2.Forms.Forms0 D u} (tr : Formalism.L2.SG.ColDict.Transport X u F) :
    ∃ a, IsTransportAdelicCorrection tr a := by
  obtain ⟨a, ha, e⟩ := exists_finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) tr.h0
  exact ⟨a, ha, e⟩

theorem exists_symOrd' {r : ℕ} (ρ k : ℕ) (h : ρ + k ≤ r) : ∃ π : Equiv.Perm (Fin r), IsSymOrd ρ k π := by
  refine ⟨⟨fun a => ⟨if (a : ℕ) < ρ then k + a else if (a : ℕ) < ρ + k then a - ρ else a, ?_⟩,
    fun b => ⟨if (b : ℕ) < k then b + ρ else if (b : ℕ) < ρ + k then b - k else b, ?_⟩, fun a => Fin.ext ?_, fun b => Fin.ext ?_⟩,
    fun _ => rfl⟩
  · have := a.2
    split_ifs <;> omega
  · have := b.2
    split_ifs <;> omega
  · dsimp only
    split_ifs <;> omega
  · dsimp only
    split_ifs <;> omega

def reordHom {Pg : Finset (Pl D.host.E)} {r : ℕ} (π : Equiv.Perm (Fin r)) : G0 Pg r →* G0 Pg r where
  toFun := reord π
  map_one' := by funext PP; simp [reord]
  map_mul' a b := by funext PP; simp [reord]

theorem exists_isSymLev (Pg : Finset (Pl D.host.E)) : ∃ P : LevelP Pg D.R.r ℂ, IsSymLev P := by
  have key : ∀ PP : Pl D.host.E, ∃ ψ : AddChar (kP PP) ℂ, ψ ≠ 1 := fun PP => by
    have : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
    have : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
    obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := kP PP) (a := 1)).2 one_ne_zero
    exact ⟨ψ, fun h => hψ (by rw [h]; rfl)⟩
  choose ψ0 hψ using key
  have hr : D.R.rS + D.R.k ≤ D.R.r := by
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rS Formalism.BasicNotions.Ranks.r
    omega
  obtain ⟨π, hπ⟩ := exists_symOrd' D.R.rS D.R.k hr
  let Q := PsharpSym Pg D.R.r D.R.rS D.R.k ψ0
  refine ⟨⟨Q.H.comap (reordHom π), Q.chi.comp ((reordHom π).subgroupComap Q.H)⟩, ψ0, fun PP _ => hψ PP, π, hπ,
    fun g => Iff.rfl, fun g hg hg' => rfl⟩

theorem exists_isTypePlaces : ∃ Pg : Finset (Pl D.host.E), GlobalTheory.Core.Mi.IsTypePlaces Pg := by
  have key : ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ PP : Pl D.host.E, PP.under (𝓞 D.host.F) = v := fun v => by
    have := v.isMaximal
    obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    refine ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, ?_⟩
    exact HeightOneSpectrum.ext hQ'.over.symm
  choose s hs using key
  have hne : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have hfin : {v : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)})
      (by rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hne)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  refine ⟨hfin.toFinset.image s, ?_, ?_⟩
  · intro PP hPP
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPP
    have hv' : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := hfin.mem_toFinset.1 hv
    rw [← hs v] at hv'
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (s v).asIdeal := hv'
    rwa [map_natCast] at h2
  · intro v hv
    refine ⟨s v, ⟨Finset.mem_image.2 ⟨v, hfin.mem_toFinset.2 hv, rfl⟩, hs v⟩, ?_⟩
    rintro PP ⟨hPP, e⟩
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hPP
    rw [hs w] at e
    rw [e]

theorem not_isTypePlaces_empty : ¬ GlobalTheory.Core.Mi.IsTypePlaces (D := D) ∅ := by
  rintro ⟨-, h⟩
  have hp := D.host.g_prime 0
  have hnu : ¬ IsUnit ((D.host.g 0 : ℕ) : 𝓞 D.host.F) := by
    intro hu
    have := hu.map (Algebra.norm ℤ)
    rw [show ((D.host.g 0 : ℕ) : 𝓞 D.host.F) = algebraMap ℤ _ (D.host.g 0 : ℤ) by simp, Algebra.norm_algebraMap,
      isUnit_pow_iff (Module.finrank_pos.ne'), Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at this
    exact hp.one_lt.ne' this
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((D.host.g 0 : ℕ) : 𝓞 D.host.F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ M := hle (Ideal.mem_span_singleton_self _)
  have hM0 : M ≠ ⊥ := fun e => by
    rw [e, Ideal.mem_bot, Nat.cast_eq_zero] at hmem
    exact hp.ne_zero hmem
  obtain ⟨PP, ⟨hPP, -⟩, -⟩ := h ⟨M, hM.isPrime, hM0⟩ (by rw [Nat.cast_mul]; exact M.mul_mem_right _ hmem)
  simp at hPP

variable {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u)

theorem pinBot_of_matches (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0))
    (hB : B.lev = d.B 0 D.R.rS h0) (hA : B.Adapted (S.tr u).wt) (t : GA D (D.sp.Y 0))
    (ht : Matches S.X S.inst (d.lev 0) (levChi (D.sp.Y 0) d.bot.β d.bot.L) t)
    (hrd : d.rd 0 = (chart0 (F₀ u)).rd d.c.θ) :
    ∃ t₀ : GA D (D.sp.Y 0), PinBot S { d with t := Function.update d.t 0 t₀ } := by
  obtain ⟨a₀, ha₀⟩ := exists_transport_adelic_correction (S.tr u)
  refine ⟨(embA B.d B.o (a₀ * 1))⁻¹ * (iotaX S.X S.inst).symm (1, S.X.xu u) * t, h0, B, a₀, 1, hB, hA, ha₀, one_mem _, one_mem _,
    ?_, hrd⟩
  have e : ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * 1) *
      ((embA B.d B.o (a₀ * 1))⁻¹ * (iotaX S.X S.inst).symm (1, S.X.xu u) * t) = t := by group
  have ht' := ht
  rw [← e] at ht'
  exact ht'

theorem level_side (B : SBes S.X S.inst u d.c.ψ (D.sp.X 0)) (a₀ a : GA D (D.sp.X 0)) (ha : a ∈ Subgroup.center (GA D (D.sp.X 0)))
    (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (x t₀ : GA D (D.sp.Y 0))
    (h : Matches S.X S.inst J χ (x⁻¹ * embA B.d B.o (a₀ * a) * t₀)) (k : GA D (D.sp.X 0)) :
    t₀⁻¹ * embA B.d B.o k * t₀ ∈ J ↔ x⁻¹ * embA B.d B.o (a₀ * k * a₀⁻¹) * x ∈ rowJ S.X S.inst := by
  rw [(h.2 _).1]
  have e1 : a₀ * k * a₀⁻¹ = (a₀ * a) * k * (a₀ * a)⁻¹ := by
    have := Subgroup.mem_center_iff.1 ha k
    rw [mul_assoc a₀ a k, ← this]; group
  have e : (x⁻¹ * embA B.d B.o (a₀ * a) * t₀)⁻¹⁻¹ * (t₀⁻¹ * embA B.d B.o k * t₀) * (x⁻¹ * embA B.d B.o (a₀ * a) * t₀)⁻¹ =
      x⁻¹ * embA B.d B.o (a₀ * k * a₀⁻¹) * x := by
    rw [e1, map_mul _ (a₀ * a * k), map_mul _ (a₀ * a) k, map_inv]; group
  rw [e]

theorem rank_ok : 0 + 2 * D.R.rS + 2 = D.R.m := by
  have := D.R.two_le_m
  obtain ⟨c, hc⟩ := D.R.m_even
  unfold Formalism.BasicNotions.Ranks.rS
  omega

end GlobalTheory.Core.Mi.PinModel

end
