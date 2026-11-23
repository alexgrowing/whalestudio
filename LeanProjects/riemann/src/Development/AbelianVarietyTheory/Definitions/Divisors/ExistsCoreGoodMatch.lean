import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCorePb
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdelEqZeroOfOffDom

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop

namespace GlobalTheory.CovTop.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_core_good_match (hO : OFull D) (hZ : OZeta D) (hV : VolTieG D) (h : 5 ≤ D.host.splitBound)
    (h15 : Nat.Coprime 15 (D.host.g 0 * D.host.g 1)) :
    ∃ T : CoreJ D, LawsJ T ∧ ∀ j, InR D j → ∀ e, ∃ (Y : Deep T.toCore j) (o : ℝ), Y.Good e o ∧ Y.Match ∧
      Y.d.l₂.M = D.host.g 0 * D.host.g 1 * 15 ^ e ∧ ¬ Y.Pull 1 0 := by
  obtain ⟨T, hT, -⟩ := (GlobalTheory.Member.CoreExist.exists_core D hO hZ hV).1
  obtain ⟨s, hs⟩ := Inhab.exists_root h
  refine ⟨T, hT, fun j hj e => ?_⟩
  obtain ⟨Y, o, h1, h2⟩ := Inhab.exists_good_match T hT j hj s hs h15 e
  exact ⟨Y, o, h1, h2, by rw [h1.lev.1.2.1, h1.pd, hT.pins.2.1.1],
    Inhab.not_pull_one_zero Y h1 (Inhab.rank_pos T.toCore hT.pins j hj)⟩

section Cover

variable {T : Core D} {j : ℕ} {Y : Deep T j} {e e' : ℕ} {o o' : ℝ}

theorem chi_eq_one (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) (k) (la) (γ)
    (hγ : γ ∈ ((Y.U σ).X k).Γ) : ((Y.U σ).X k).χ la γ = 1 :=
  GlobalTheory.OneEmbeddingProbe.chi_eq_one _ (h.chiTriv σ hσ) k la γ hγ

theorem exp_unique (h : Y.Good e o) (h' : Y.Good e' o') : e = e' :=
  Nat.pow_right_injective (by norm_num : 2 ≤ 15) (h.pd.symm.trans h'.pd)

theorem size_nonneg (h : Y.Good e o) : 0 ≤ o := (Real.log_natCast_nonneg _).trans h.deg

theorem rank_eq (h : Y.Good e o) : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := (h.unf Y.d.c₂.F.val.toRingHom rfl).1

theorem pull_add {f f' : T.R j} {g g' : Rul Y.d.Xo₂ Y.d.c₂} (h : Y.Pull f g) (h' : Y.Pull f' g') : Y.Pull (f + f') (g + g') := by
  intro k _ _ _ _ _ a b y₂ y' y c1 c2 c3 c4
  exact (evalAt_add _ _ g g' y₂).trans ((congrArg₂ (· + ·) (h k a b y₂ y' y c1 c2 c3 c4) (h' k a b y₂ y' y c1 c2 c3 c4)).trans
    (evalAt_add _ _ f f' y).symm)

theorem pull_mul {f f' : T.R j} {g g' : Rul Y.d.Xo₂ Y.d.c₂} (h : Y.Pull f g) (h' : Y.Pull f' g') : Y.Pull (f * f') (g * g') := by
  intro k _ _ _ _ _ a b y₂ y' y c1 c2 c3 c4
  exact (evalAt_mul _ _ g g' y₂).trans ((congrArg₂ (· * ·) (h k a b y₂ y' y c1 c2 c3 c4) (h' k a b y₂ y' y c1 c2 c3 c4)).trans
    (evalAt_mul _ _ f f' y).symm)

theorem latOver_mono (G : WTZ D.host.E) {B B' : Set (T.R j)} (h : B ⊆ B') : Y.latOver G B ≤ Y.latOver G B' :=
  fun x hx => by
    have h2 : (x : Rul Y.d.Xo₂ Y.d.c₂) ∈ Submodule.span Y.d.c₂.F {g | ∃ f ∈ B, Y.Pull f g} := hx.2
    have h3 : {g | ∃ f ∈ B, Y.Pull f g} ⊆ {g | ∃ f ∈ B', Y.Pull f g} := by
      rintro _ ⟨f, hf, hp⟩; exact ⟨f, h hf, hp⟩
    exact ⟨hx.1, Submodule.span_mono h3 h2⟩

theorem latOver_empty (G : WTZ D.host.E) : Y.latOver G ∅ = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  have h2 : (x : Rul Y.d.Xo₂ Y.d.c₂) ∈ Submodule.span Y.d.c₂.F {g | ∃ f ∈ (∅ : Set (T.R j)), Y.Pull f g} := hx.2
  have e : {g | ∃ f ∈ (∅ : Set (T.R j)), Y.Pull f g} = ∅ := by simp
  rw [e, Submodule.span_empty, Submodule.mem_bot] at h2
  exact (Submodule.mem_bot _).2 (Subtype.ext h2)

end Cover

section Base

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m)

theorem nrmR_smul (σ : D.what₂.LL →+* ℂ) (a : D.what₂.LL) (f : Fin (R.nW i) → D.what₂.LL) :
    nrmR R i σ (a • f) = ‖σ a‖ * nrmR R i σ f := by
  have h : InfinitePlace.mk (sgAt D.what₂.embLL (InfinitePlace.mk σ)) = InfinitePlace.mk σ := by
    unfold sgAt
    split_ifs with h
    · exact h.symm
    · exact InfinitePlace.mk_embedding _
  have h2 : ‖sgAt D.what₂.embLL (InfinitePlace.mk σ) a‖ = ‖σ a‖ := by
    rw [← InfinitePlace.apply, h, InfinitePlace.apply]
  rw [nrmR, map_smulₛₗ, norm_smul, h2, nrmR]

theorem latType_eq : latType R F i = latAll R i ⊓ (spType R F i).restrictScalars (𝓞 D.what₂.LL) := rfl

theorem latGood_inf_latBad (h : eGood R i ∘ₗ eGood R i = eGood R i) : latGood R F i ⊓ latBad R F i = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨y, hy⟩ : x ∈ LinearMap.range (eGood R i) := hx.1.2
  have h0 : eGood R i x = 0 := hx.2.2
  have := LinearMap.congr_fun h y
  rw [LinearMap.comp_apply, hy, h0] at this
  exact (Submodule.mem_bot _).2 this.symm

end Base

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ)

theorem exZ_shiftG (s : ℤ) : exZ Dw (shiftG Dw a (2 * m) s) = exOf Dw (laOf Dw a (2 * m) + s • hodgeWt Dw) m := by
  have h1 := exOf_add (laOf Dw a (2 * m)) (s • hodgeWt Dw) (m : ℤ) 0
  have h2 := exOf_weightOf (Dw := Dw) (fun x => (a x : ℤ)) m
  have h3 : laOf Dw a (2 * m) = weightOf Dw (fun x => (a x : ℤ)) m := by simp [laOf]
  rw [add_zero] at h1
  rw [h1, h3, h2]
  funext x
  rw [shiftG, exZ_add]
  simp only [wtZ, exOf, Pi.add_apply]
  push_cast
  rfl

theorem uMinus_apply (n kc : ℕ) (c0 : ℤ) (τ : Psi H) (k : Fin (Dw.p + Dw.q)) :
    uMinus Dw a n kc c0 τ k = if (k : ℕ) < Dw.p then uWt Dw a n kc τ k else uWt Dw a n kc τ k + c0 := by
  simp only [uMinus, hodgeWt, barWt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem anchor_big (kc : ℕ) (h : kc < Dw.p) (τ : Psi H) : anchor Dw a (2 * m) (kc + 1) τ = a (τ.1, kc) + m := by
  have h' : kc < Dw.p + Dw.q := by omega
  simp [anchor, laOf, weightOf, h, h']

theorem abs_laOf (τ : Psi H) (k : Fin (Dw.p + Dw.q)) : |laOf Dw a (2 * m) τ k| =
    (if (k : ℕ) < Dw.p then a (τ.1, k) else a (conjEmb τ.1, Dw.q - 1 - ((k : ℕ) - Dw.p)) : ℕ) + m := by
  have h3 : laOf Dw a (2 * m) = weightOf Dw (fun x => (a x : ℤ)) m := by simp [laOf]
  rw [h3, weightOf]
  split_ifs
  · exact abs_of_nonneg (by positivity)
  · rw [abs_of_nonpos (by omega)]; ring

end Weights

theorem expL_le {L : ℝ} (h : 0 ≤ L) : expL L * Real.log 3 ≤ 3 * L :=
  (le_div_iff₀ (Real.log_pos (by norm_num))).1 (Nat.floor_le (div_nonneg (by positivity) (Real.log_pos (by norm_num)).le))

end GlobalTheory.CovTop.Model

end
