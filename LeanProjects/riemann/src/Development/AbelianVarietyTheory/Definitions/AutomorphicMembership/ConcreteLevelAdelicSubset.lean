import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

namespace GlobalTheory.Mem.SRe

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  MeasureTheory NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev JR (R : RealDat D A Ks) (F : Face D A) : Set (GA D (Yc D 0)) := levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))

abbrev chiR (R : RealDat D A Ks) (F : Face D A) : GA D (Yc D 0) → ℂ := levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))

abbrev MultR (R : RealDat D A Ks) (F : Face D A) : Submodule ℂ (MMap (MP R)) := Mult R.θ (R.MY 0) (JR R F) (chiR R F)

def DallTie (R : RealDat D A Ks) (F : Face D A) : Prop := D.what₂.Dall = Module.finrank ℂ (MultR R F)

def concreteLevelAdelicSubset (X : HidaSetting D) : Set X.B.I.GA := {x | x.1 = 1 ∧ x.2 ∈ X.K2}

def adelicCharacterOfHidaSetting (X : HidaSetting D) : X.B.I.GA → ℂ := fun x => star (X.chi2 x.2)

def GrpPin (R : RealDat D A Ks) : Prop :=
  ∃ (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
    (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff (eR g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧
      ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)

structure SeeAt (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (D.sp.Y 0)) : Prop where

  fin : t ∈ GfC (Yc D 0)

  conj : ConjLevel t⁻¹ (JR R F) (chiR R F) (iotaX X h ⁻¹' concreteLevelAdelicSubset X) (fun k => adelicCharacterOfHidaSetting X (iotaX X h k))

  mat : RowLevelMatchAt R F X h t

def conjRows (X : HidaSetting D) : Submodule ℂ (L2X X) := (HHX X).comap (conjL (muX X)).toLinearEquiv.toLinearMap

def EvalOn (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (v₀ : (MP R).Vec) (c : ℝ) (E : Submodule ℂ (MMap (MP R))) (E' : Submodule ℂ (L2X X)) : Prop :=
  ∃ J : E ≃ₗ[ℂ] E', ∀ S : E,
    ((J S : E') : L2X X) =ᵐ[muX X] (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) ∧
      ‖((J S : E') : L2X X)‖ ^ 2 = c * (ipM (MP R) R.ν0 R.fd0 (S : MMap (MP R)) (S : MMap (MP R))).re

def RowJ (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (G : GoodOp X) (t : GA D (D.sp.Y 0)) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) : Prop :=
  ∃ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) ∧ ∃ a : ℝ, 0 < a ∧ ∀ x : D.what₂.EE,
    ((j x : EEC X G) : L2X X) =ᵐ[muX X] fun g => (a : ℂ) * ev (MP R) v₀ (R.HE.e (eE x)) ((iotaX X h).symm g * t)

theorem mem_conjRows_iff (X : HidaSetting D) (f : L2X X) : f ∈ conjRows X ↔ conjL (muX X) f ∈ HHX X := Iff.rfl

theorem EEC_le_conjRows (X : HidaSetting D) (G : GoodOp X) : EEC X G ≤ conjRows X := fun _ hF => hF.1

example (X : HidaSetting D) (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    ((1, k) : X.B.I.GA) ∈ concreteLevelAdelicSubset X ∧ adelicCharacterOfHidaSetting X (1, k) = star (X.chi2 k) := ⟨⟨rfl, hk⟩, rfl⟩

theorem evalTieT_iff_evalOn (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X)
    (t : GA D (D.sp.Y 0)) (c : ℝ) (E : Submodule ℂ (MMap (MP R))) :
    EvalTieT (MP R) R.ν0 R.fd0 E X G (iotaX X h).toMulEquiv t c ↔
      ∃ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) ∧ EvalOn R X h t v₀ c E (EEC X G) := Iff.rfl

example (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (v₀ : (MP R).Vec) (x : X.B.I.GA) : ev (MP R) v₀ 0 ((iotaX X h).symm x * t) = 0 := by
  rw [map_zero]; rfl

theorem SeeAt.levelMatchA {R : RealDat D A Ks} {F : Face D A} {X : HidaSetting D}
    {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {t : GA D (D.sp.Y 0)} (hs : SeeAt R F X h t) : LevelMatchA R F X h t := by
  intro k hk
  have e : (t⁻¹⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹ : GA D (D.sp.Y 0)) = (iotaX X h).symm (1, k) := by group
  obtain ⟨h1, h2⟩ := hs.conj (t⁻¹ * (iotaX X h).symm (1, k) * t)
  rw [e] at h1 h2
  have hm := h1.2 (by simp [concreteLevelAdelicSubset, hk])
  refine ⟨hm, ?_⟩
  have := h2 hm
  simp only [adelicCharacterOfHidaSetting, ContinuousMulEquiv.apply_symm_apply] at this
  exact this.symm

theorem exists_rowJ_of_evalOn {R : RealDat D A Ks} {F : Face D A} {X : HidaSetting D}
    {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {G : GoodOp X} {t : GA D (D.sp.Y 0)} {v₀ : (MP R).Vec} {c : ℝ}
    {eE : D.what₂.EE →ₗ[ℂ] R.HE.H} (hc : 0 < c) (hv₀ : ∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) (hE : R.models_HE)
    (hrange : LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e)
    (hnorm : ∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) (hle : R.EEat (R.levR F true) ≤ R.EEat R.triv)
    (hJ2 : EvalOn R X h t v₀ c (EP R F) (EEC X G)) : ∃ j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G, RowJ R eE X h G t j := by
  obtain ⟨J2, hJ2⟩ := hJ2
  obtain ⟨he_inj, he_range, he_ip⟩ := hE
  have hnP : 0 < RealDat.nP F true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  have heE_inj : Function.Injective eE := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hnorm x
    rw [hx, norm_zero] at h1
    have h2 : RealDat.nP F true * ‖x‖ ^ 2 = 0 := by rw [← h1]; ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hnP.ne'
    · exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)
  have hmem : ∀ x, (R.HE.e ∘ₗ eE) x ∈ EP R F := fun x => by
    have : eE x ∈ (R.EEat (R.levR F true)).comap R.HE.e := hrange ▸ LinearMap.mem_range_self eE x
    exact this
  let k : D.what₂.EE →ₗ[ℂ] EP R F := LinearMap.codRestrict (EP R F) (R.HE.e ∘ₗ eE) hmem
  have hk : Function.Bijective k := by
    constructor
    · intro x y hxy
      exact heE_inj (he_inj (congrArg Subtype.val hxy))
    · rintro ⟨y, hy⟩
      have hy' : y ∈ LinearMap.range R.HE.e := he_range ▸ hle hy
      obtain ⟨z, rfl⟩ := hy'
      have hz : z ∈ LinearMap.range eE := by rw [hrange]; exact hy
      obtain ⟨x, rfl⟩ := hz
      exact ⟨x, rfl⟩
  let L : D.what₂.EE ≃ₗ[ℂ] EEC X G := (LinearEquiv.ofBijective k hk).trans J2
  have hLn : ∀ x, ‖L x‖ ^ 2 = (c * RealDat.nP F true) * ‖x‖ ^ 2 := by
    intro x
    have h1 := (hJ2 (k x)).2
    have h2 : ((k x : EP R F) : MMap (MP R)) = R.HE.e (eE x) := rfl
    have h3 : (ipM (MP R) R.ν0 R.fd0 (R.HE.e (eE x)) (R.HE.e (eE x))).re = ‖eE x‖ ^ 2 := by
      calc (ipM (MP R) R.ν0 R.fd0 (R.HE.e (eE x)) (R.HE.e (eE x))).re
          = (inner ℂ (eE x) (eE x)).re := by rw [he_ip]; rfl
        _ = ‖eE x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (eE x)
    show ‖((J2 (k x) : EEC X G) : L2X X)‖ ^ 2 = _
    rw [h1, h2, h3, hnorm x]
    ring
  set a : ℝ := (Real.sqrt (c * RealDat.nP F true))⁻¹ with ha_def
  have hs : 0 < Real.sqrt (c * RealDat.nP F true) := Real.sqrt_pos.mpr (mul_pos hc hnP)
  have ha : 0 < a := inv_pos.mpr hs
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G :=
    { toLinearEquiv := L.trans (LinearEquiv.smulOfNeZero ℂ (EEC X G) (a : ℂ) haC)
      norm_map' := fun x => by
        show ‖(a : ℂ) • L x‖ = ‖x‖
        have hL : ‖L x‖ = Real.sqrt (c * RealDat.nP F true) * ‖x‖ := by
          rw [← Real.sqrt_sq (norm_nonneg (L x)), hLn x, Real.sqrt_mul' _ (sq_nonneg _),
            Real.sqrt_sq (norm_nonneg x)]
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ha.le, hL, ← mul_assoc, ha_def,
          inv_mul_cancel₀ hs.ne', one_mul] }
  refine ⟨j, v₀, hv₀, a, ha, fun x => ?_⟩
  have h1 : ((j x : EEC X G) : L2X X) = (a : ℂ) • ((J2 (k x) : EEC X G) : L2X X) := rfl
  rw [h1]
  filter_upwards [Lp.coeFn_smul (a : ℂ) ((J2 (k x) : EEC X G) : L2X X), (hJ2 (k x)).1] with g h2 h3
  rw [h2, Pi.smul_apply, h3, smul_eq_mul]
  rfl

end GlobalTheory.Mem.SRe

end
