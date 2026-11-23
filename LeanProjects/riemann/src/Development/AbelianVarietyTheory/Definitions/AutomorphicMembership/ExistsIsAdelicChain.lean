import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockDetSingleBlockSecondEqOneOfLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftModelsOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.Mem.Th

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

section Level

theorem mult_anti {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ}
    (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : Mult θ M J χ ≤ Mult θ M J' χ' :=
  Submodule.span_mono fun _ hX => ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩

theorem principal_le_level {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P : LevelP L.Pg L.r ℂ)
    (k : GA D V) (hk : k ∈ levS V β (flag1L L)) :
    k ∈ levS V β (withP L P) ∧ levChi V β (withP L P) k = levChi V β (flag1L L) k := by
  have h1 : rTup β L (finE V k) = 1 := Subgroup.mem_bot.1 hk.2.2
  have h2 : rTup β L (finE V k) ∈ P.H := h1 ▸ P.H.one_mem
  refine ⟨⟨hk.1, hk.2.1, h2⟩, ?_⟩
  unfold levChi
  rw [levFn_withP, levFn_flag1, h1, extendOne_of_mem _ P.H.one_mem]
  exact congrArg Units.val ((congrArg (· * _) (map_one P.chi)).trans (one_mul _))

variable (R : RealDat D A Ks)

def multAt (P : LevelP R.Pg D.R.r ℂ) (t : T) (j : ℕ) : Submodule ℂ (MMap (R.MY j)) :=
  Mult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j P)) (levChi _ (R.βY j) (R.datYt t j P))

def toMM (t : T) (j : ℕ) : R.CC t j →ₗ[ℂ] MMap (R.MY j) :=
  (PiTensorProduct.lift.symm : (SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) ≃ₗ[ℂ] MMap (R.MY j)).toLinearMap ∘ₗ (R.CC t j).subtype

def lvlPart (P : LevelP R.Pg D.R.r ℂ) (t : T) (j : ℕ) : Submodule ℂ (R.CC t j) := (multAt R P t j).comap (toMM R t j)

def ipCC (t : T) (j : ℕ) (U U' : R.CC t j) : ℂ := ipM (R.MY j) (R.νY t j) (R.fdY t j) (toMM R t j U) (toMM R t j U')

def topLift (t : T) : (R.HX t).H →ₗ[ℂ] R.CC t (D.R.m - 1) := R.ioX t ∘ₗ (R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict

def botLift (t : T) : R.CC t 1 →ₗ[ℂ] MMap (R.MY 0) := postOn (R.MY 0) R.e0 ∘ₗ toMM R t 0 ∘ₗ R.ioY t 0

theorem toMM_apply (t : T) (j : ℕ) (U : R.CC t j) (v : (R.MY j).Vec) :
    toMM R t j U v = (U : SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) (PiTensorProduct.tprod ℂ v) := rfl

theorem toMM_injective (t : T) (j : ℕ) : Function.Injective (toMM R t j) :=
  (PiTensorProduct.lift.symm : (SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) ≃ₗ[ℂ] MMap (R.MY j)).injective.comp Subtype.val_injective

theorem range_toMM (t : T) (j : ℕ) : LinearMap.range (toMM R t j) = multAt R R.triv t j := by
  ext X
  constructor
  · rintro ⟨U, rfl⟩
    exact (mem_multT R.θ (R.MY j) _ _ _).1 U.2
  · intro hX
    exact ⟨⟨PiTensorProduct.lift X, Submodule.mem_map_of_mem hX⟩, PiTensorProduct.lift.symm_apply_apply X⟩

theorem multAt_le (P : LevelP R.Pg D.R.r ℂ) (t : T) (j : ℕ) : multAt R P t j ≤ multAt R R.triv t j :=
  mult_anti _ _ (principal_le_level (R.βY j) (R.datYt t j R.triv) P)

theorem map_lvlPart (P : LevelP R.Pg D.R.r ℂ) (t : T) (j : ℕ) : (lvlPart R P t j).map (toMM R t j) = multAt R P t j :=
  Submodule.map_comap_eq_of_le (by rw [range_toMM]; exact multAt_le R P t j)

theorem multAt_zero (P : LevelP R.Pg D.R.r ℂ) (t : T) :
    multAt R P t 0 = Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) := by
  have hr : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]
    simp [Ranks.rankY]
  have e := GlobalTheory.levG_twist_trivial_of_rank_eq (Yc D 0) (R.βY 0) D.R.r D.R.t (r_le_Y 0) hr R.Pg (R.Q t) P R.chi (R.xiR t)
  have e1 : levG (Yc D 0) (R.βY 0) (R.datYt t 0 P) = levG (Yc D 0) (R.βY 0) (R.dat0 P) := e.1
  have e2 : ∀ k ∈ levG (Yc D 0) (R.βY 0) (R.datYt t 0 P),
      levChi (Yc D 0) (R.βY 0) (R.datYt t 0 P) k = levChi (Yc D 0) (R.βY 0) (R.dat0 P) k := e.2
  exact le_antisymm (mult_anti _ _ fun k hk => ⟨e1.ge hk, e2 k (e1.ge hk)⟩) (mult_anti _ _ fun k hk => ⟨e1.le hk, (e2 k hk).symm⟩)

theorem EEat_le (P : LevelP R.Pg D.R.r ℂ) (t : T) : R.EEat P ≤ multAt R P t 0 := by
  rw [multAt_zero]; exact goodPart_le _ _ _ _ _

theorem EEat_le_triv (P : LevelP R.Pg D.R.r ℂ) : R.EEat P ≤ R.EEat R.triv :=
  inf_le_inf_right _ (mult_anti _ _ (principal_le_level (R.βY 0) (R.dat0 R.triv) P))

theorem toMM_dnFrom_topLift (t : T) (y : (R.HX t).H) :
    toMM R t 0 (Lift.dnFrom (R.CC t) (R.ioY t) (D.R.m - 1) (topLift R t y)) = PiTensorProduct.lift.symm (R.thDn t y) := rfl

end Level

section Side

variable {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)

theorem pred_m_add_one (D : D7) : D.R.m - 1 + 1 = D.R.m := by have := D.R.two_le_m; omega

def famCast (Sp : ℕ → Type) [∀ j, NormedAddCommGroup (Sp j)] [∀ j, InnerProductSpace ℂ (Sp j)] {i j : ℕ} (h : i = j) :
    Sp i ≃ₗᵢ[ℂ] Sp j := by
  subst h; exact LinearIsometryEquiv.refl ℂ _

def multCast (μ : D.what₂.Tup) {i j : ℕ} (h : i = j) : S.Mult μ i ≃ₗᵢ[ℂ] S.Mult μ j := famCast (S.Mult μ) h

def topEquiv (μ : D.what₂.Tup) : S.Mult μ (D.R.m - 1 + 1) ≃ₗᵢ[ℂ] S.Amb μ := (multCast S μ (pred_m_add_one D)).trans (S.multTop μ)

theorem downTo_multCast (μ : D.what₂.Tup) {i j : ℕ} (h : i = j) (x : S.Mult μ i) : S.downTo μ j (multCast S μ h x) = S.downTo μ i x := by
  subst h; rfl

theorem iota_topEquiv (μ : D.what₂.Tup) (x : S.Mult μ (D.R.m - 1 + 1)) :
    S.iota μ (topEquiv S μ x) = S.multZero μ (S.downTo μ (D.R.m - 1) (S.io μ (D.R.m - 1) x)) := by
  have h : (S.multTop μ).symm (topEquiv S μ x) = multCast S μ (pred_m_add_one D) x := (S.multTop μ).symm_apply_apply _
  show S.multZero μ (S.downTo μ D.R.m ((S.multTop μ).symm (topEquiv S μ x))) = _
  rw [h, downTo_multCast]
  rfl

theorem toMM_downTo (R : RealDat D A Ks) (μ : D.what₂.Tup) (t : T) (e : ∀ j, S.Mult μ j →ₗ[ℂ] R.CC t j)
    (h0 : ∀ x, toMM R t 0 (e 0 (S.io μ 0 x)) = botLift R t (e 1 x))
    (h1 : ∀ j, 0 < j → j + 1 < D.R.m → ∀ x, e j (S.io μ j x) = R.ioY t j (e (j + 1) x)) (n : ℕ) (hn : 0 < n) (hm : n < D.R.m)
    (x : S.Mult μ n) :
    toMM R t 0 (e 0 (S.downTo μ n x)) = postOn (R.MY 0) R.e0 (toMM R t 0 (Lift.dnFrom (R.CC t) (R.ioY t) n (e n x))) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact h0 x
    · exact (ih h (by omega) (S.io μ n x)).trans
        (congrArg (fun U => postOn (R.MY 0) R.e0 (toMM R t 0 (Lift.dnFrom (R.CC t) (R.ioY t) n U))) (h1 n h hm x))

theorem toMM_iota (R : RealDat D A Ks) (μ : D.what₂.Tup) (t : T) (e : ∀ j, S.Mult μ j →ₗ[ℂ] R.CC t j)
    (eA : S.Amb μ →ₗ[ℂ] (R.HX t).H) (h0 : ∀ x, toMM R t 0 (e 0 (S.io μ 0 x)) = botLift R t (e 1 x))
    (h1 : ∀ j, 0 < j → j + 1 < D.R.m → ∀ x, e j (S.io μ j x) = R.ioY t j (e (j + 1) x))
    (h2 : ∀ x, e (D.R.m - 1) (S.io μ (D.R.m - 1) x) = topLift R t (eA (topEquiv S μ x))) (a : S.Amb μ) :
    toMM R t 0 (e 0 ((S.multZero μ).symm (S.iota μ a))) = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t (eA a))) := by
  have hm := D.R.two_le_m
  have hx : topEquiv S μ ((topEquiv S μ).symm a) = a := (topEquiv S μ).apply_symm_apply a
  have a1 : (S.multZero μ).symm (S.iota μ a) = S.downTo μ (D.R.m - 1) (S.io μ (D.R.m - 1) ((topEquiv S μ).symm a)) :=
    (congrArg (fun w => (S.multZero μ).symm (S.iota μ w)) hx.symm).trans
      ((congrArg (S.multZero μ).symm (iota_topEquiv S μ _)).trans ((S.multZero μ).symm_apply_apply _))
  have a2 := toMM_downTo S R μ t e h0 h1 (D.R.m - 1) (by omega) (by omega) (S.io μ (D.R.m - 1) ((topEquiv S μ).symm a))
  have a3 : e (D.R.m - 1) (S.io μ (D.R.m - 1) ((topEquiv S μ).symm a)) = topLift R t (eA a) :=
    (h2 _).trans (congrArg (fun w => topLift R t (eA w)) hx)
  refine (congrArg (fun w => toMM R t 0 (e 0 w)) a1).trans (a2.trans (congrArg (postOn (R.MY 0) R.e0) ?_))
  exact (congrArg (fun U => toMM R t 0 (Lift.dnFrom (R.CC t) (R.ioY t) (D.R.m - 1) U)) a3).trans (toMM_dnFrom_topLift R t _)

end Side

variable {R : RealDat D A Ks} {F : Face D A} {tup : T → D.what₂.Tup} {b : Bool} {EE : Type} [NormedAddCommGroup EE]
  [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {S : RowSide D EE}

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure MultTie (Y : SideTie R F tup b S) where

  eM : ∀ t j, S.Mult (tup t) j →ₗ[ℂ] R.CC t j

  eM_zero : ∀ t x, toMM R t 0 (eM t 0 x) = R.HE.e (Y.eE (S.multZero (tup t) x))

  eM_range : ∀ t j, 0 < j → j < D.R.m → LinearMap.range (eM t j) = lvlPart R (R.levR F b) t j

  eM_inner : ∀ t j, 0 < j → j < D.R.m → ∀ x y, ipCC R t j (eM t j x) (eM t j y) = ((RealDat.nP F b : ℝ) : ℂ) * ⟪x, y⟫_ℂ

  io_zero : ∀ t x, toMM R t 0 (eM t 0 (S.io (tup t) 0 x)) = botLift R t (eM t 1 x)

  io_mid : ∀ t j, 0 < j → j + 1 < D.R.m → ∀ x, eM t j (S.io (tup t) j x) = R.ioY t j (eM t (j + 1) x)

  io_top : ∀ t x, eM t (D.R.m - 1) (S.io (tup t) (D.R.m - 1) x) = topLift R t (Y.eA t (topEquiv S (tup t) x))

section Inhabitant

def KeepsLevel (R : RealDat D A Ks) (F : Face D A) (b : Bool) : Prop := ∀ t,
  (∀ U ∈ lvlPart R (R.levR F b) t 1, botLift R t U ∈ R.EEat (R.levR F b)) ∧
  (∀ j, 0 < j → j + 1 < D.R.m → ∀ U ∈ lvlPart R (R.levR F b) t (j + 1), R.ioY t j U ∈ lvlPart R (R.levR F b) t j) ∧
  ∀ f ∈ lvlForms (A.MtildeCSD t) (A.leftGroupActionRight t) (F.lvl b).P (F.lvl b).ψ,
    topLift R t (R.jX t f) ∈ lvlPart R (R.levR F b) t (D.R.m - 1)

theorem exists_factor {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (g : Y →ₗ[ℂ] Z) (hg : Function.Injective g) (f : X →ₗ[ℂ] Z) (hf : ∀ x, f x ∈ LinearMap.range g) :
    ∃ h : X →ₗ[ℂ] Y, ∀ x, g (h x) = f x :=
  ⟨(LinearEquiv.ofInjective g hg).symm.toLinearMap ∘ₗ f.codRestrict _ hf, fun x =>
    congrArg Subtype.val ((LinearEquiv.ofInjective g hg).apply_symm_apply ⟨f x, hf x⟩)⟩

theorem eq_mul_of_eq_inv_mul {n : ℝ} (hn : 0 < n) {a c : ℂ} (h : a = ((n⁻¹ : ℝ) : ℂ) * c) : c = (n : ℂ) * a := by
  rw [h, ← mul_assoc, Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hn.ne'), one_mul]

theorem haar_chain (hY : R.models_νY) (hY' : R.models_νY') (t : T) (j : ℕ) (hj : j < D.R.m) :
    (R.νY t j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
  by_cases h1 : j + 1 < D.R.m
  · exact ⟨(hY t j h1).1.1, (hY t j h1).2⟩
  · obtain rfl : j = D.R.m - 1 := by omega
    exact ⟨(hY' t).1.1, (hY' t).2⟩

theorem finiteDimensional_CC (hF : GlobalTheory.Published.HarishChandraFinite) (hi : R.models_inf) (t : T) (j : ℕ) :
    FiniteDimensional ℂ (R.CC t j) := by
  obtain ⟨U, hU, hJ⟩ := GlobalTheory.DefiniteEnd.exists_open_level (Yc D j) (R.βY j) (R.datYt t j R.triv)
  have : FiniteDimensional ℂ (multAt R R.triv t j) := GlobalTheory.MultFinite.hcFinite hF hi ⟨U, hU, fun k hk hk' => by
    obtain ⟨h1, h2⟩ := hJ k hk
    exact ⟨⟨hk', h1⟩, congrArg Units.val h2⟩⟩
  rw [← range_toMM] at this
  exact (LinearEquiv.ofInjective _ (toMM_injective R t j)).symm.finiteDimensional

theorem exists_lvlModel (hF : GlobalTheory.Published.HarishChandraFinite) (hD : GlobalTheory.Published.CuspRapidDecay) (hi : R.models_inf)
    (hY : R.models_νY) (hY' : R.models_νY') (P : LevelP R.Pg D.R.r ℂ) (c : ℝ) (hc : 0 < c) (t : T) (j : ℕ) (hj : j < D.R.m) :
    ∃ H : HMod (R.CC t j), H.Is (lvlPart R P t j) fun U U' => (c : ℂ) * ipCC R t j U U' := by
  have := finiteDimensional_CC hF hi t j
  obtain ⟨hν, hf⟩ := haar_chain hY hY' t j hj
  obtain ⟨h1, h2⟩ := GlobalTheory.SchurConst.ipM_posDef D R.θ _ _ (R.MY j) (levS _ (R.βY j) (R.datYt t j P))
    (levChi _ (R.βY j) (R.datYt t j P)) (R.νY t j) (R.fdY t j) hi hν hf (GlobalTheory.MultFinite.schurMult hD _ _)
    (GlobalTheory.GardingVec.sm_ne_bot D _ _ _)
  refine GlobalTheory.HilbertModel.exists_hmod _ _ _ inferInstance (fun x hx y hy z hz a => ?_) fun x hx h0 => ?_
  · obtain ⟨k1, k2⟩ := h1 _ hx _ hy _ hz a
    unfold ipCC
    rw [map_add, map_smul, k1, k2]
    exact ⟨by ring, by simp⟩
  · have := h2 _ hx fun h => h0 (toMM_injective R t j (h.trans (map_zero _).symm))
    rw [Complex.re_ofReal_mul]
    exact mul_pos hc this

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure HChain (m : ℕ) (E B : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] where

  Sp : ℕ → Type
  [nSp : ∀ j, NormedAddCommGroup (Sp j)]
  [iSp : ∀ j, InnerProductSpace ℂ (Sp j)]
  [fSp : ∀ j, FiniteDimensional ℂ (Sp j)]

  bot : Sp 0 ≃ₗᵢ[ℂ] E

  top : Sp m ≃ₗᵢ[ℂ] B

  io : ∀ j, Sp (j + 1) →ₗ[ℂ] Sp j

attribute [instance] HChain.nSp HChain.iSp HChain.fSp

def chainOf (S : RowSide D EE) (μ : D.what₂.Tup) : HChain D.R.m EE (S.Amb μ) :=
  { Sp := S.Mult μ, bot := S.multZero μ, top := S.multTop μ, io := S.io μ }

@[reducible] def withChain (S : RowSide D EE) (c : ∀ μ, HChain D.R.m EE (S.Amb μ)) : RowSide D EE :=
  { S with
    Mult := fun μ => (c μ).Sp
    instMult := fun μ => (c μ).nSp
    instMulti := fun μ => (c μ).iSp
    instMultf := fun μ => (c μ).fSp
    multZero := fun μ => (c μ).bot
    multTop := fun μ => (c μ).top
    io := fun μ => (c μ).io }

noncomputable def HChain.down {m : ℕ} {E B : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] (c : HChain m E B) : (j : ℕ) → c.Sp j →ₗ[ℂ] c.Sp 0
  | 0 => LinearMap.id
  | j + 1 => (c.down j).comp (c.io j)

theorem downTo_withChain (S : RowSide D EE) (c : ∀ μ, HChain D.R.m EE (S.Amb μ)) (μ : D.what₂.Tup) (j : ℕ) :
    (withChain S c).downTo μ j = (c μ).down j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (fun f : (c μ).Sp j →ₗ[ℂ] (c μ).Sp 0 => f.comp ((c μ).io j)) ih

theorem down_chainOf (S : RowSide D EE) (μ : D.what₂.Tup) (j : ℕ) : (chainOf S μ).down j = S.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (fun f : S.Mult μ j →ₗ[ℂ] S.Mult μ 0 => f.comp (S.io μ j)) ih

theorem iota_withChain (S : RowSide D EE) (c : ∀ μ, HChain D.R.m EE (S.Amb μ)) (μ : D.what₂.Tup) (h : c μ = chainOf S μ) :
    (withChain S c).iota μ = S.iota μ := by
  have e : (withChain S c).iota μ = (c μ).bot.toLinearEquiv.toLinearMap ∘ₗ (c μ).down D.R.m ∘ₗ
      (c μ).top.symm.toLinearEquiv.toLinearMap := by
    rw [← downTo_withChain]; rfl
  rw [e, h, down_chainOf]; rfl

def IsAdelicChain (Y : SideTie R F tup b S) (t : T) (c : HChain D.R.m EE (S.Amb (tup t))) : Prop :=
  ∃ e : ∀ j, c.Sp j →ₗ[ℂ] R.CC t j, (∀ x, toMM R t 0 (e 0 x) = R.HE.e (Y.eE (c.bot x))) ∧
    (∀ j, 0 < j → j < D.R.m → LinearMap.range (e j) = lvlPart R (R.levR F b) t j) ∧
    (∀ j, 0 < j → j < D.R.m → ∀ x y, ipCC R t j (e j x) (e j y) = ((RealDat.nP F b : ℝ) : ℂ) * ⟪x, y⟫_ℂ) ∧
    (∀ x, toMM R t 0 (e 0 (c.io 0 x)) = botLift R t (e 1 x)) ∧
    (∀ j, 0 < j → j + 1 < D.R.m → ∀ x, e j (c.io j x) = R.ioY t j (e (j + 1) x)) ∧
    ∀ x, e (D.R.m - 1) (c.io (D.R.m - 1) x) = topLift R t (Y.eA t (c.top (famCast c.Sp (pred_m_add_one D) x)))

theorem e_eE_mem (Y : SideTie R F tup b S) (x : EE) : R.HE.e (Y.eE x) ∈ R.EEat (R.levR F b) :=
  Y.eE_range.le (LinearMap.mem_range_self _ x)

set_option maxHeartbeats 1000000 in

theorem exists_isAdelicChain (Y : SideTie R F tup b S) (hE : R.models_HE) (hK : KeepsLevel R F b) (t : T)
    (hH : ∀ j, j < D.R.m → ∃ H : HMod (R.CC t j), H.Is (lvlPart R (R.levR F b) t j)
      fun U U' => (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * ipCC R t j U U') :
    ∃ c, IsAdelicChain Y t c := by
  have hm := D.R.two_le_m
  obtain ⟨k0, k1, k2⟩ := hK t
  have key : ∀ j, ∃ H : HMod (R.CC t j), (0 < j → j < D.R.m → H.Is (lvlPart R (R.levR F b) t j)
      fun U U' => (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * ipCC R t j U U') ∧ (D.R.m ≤ j → Nonempty (H.H ≃ₗᵢ[ℂ] S.Amb (tup t))) ∧
      (j = 0 → ∃ z : H.H ≃ₗᵢ[ℂ] EE, ∀ x, HEq (toMM R t j (H.e x)) (R.HE.e (Y.eE (z x)))) := fun j => by
    rcases Nat.eq_zero_or_pos j with rfl | h0
    · obtain ⟨e, he⟩ := exists_factor (toMM R t 0) (toMM_injective R t 0) (R.HE.e ∘ₗ Y.eE) fun x => by
        rw [range_toMM]; exact multAt_le R _ t 0 (EEat_le R _ t (e_eE_mem Y x))
      exact ⟨⟨EE, e⟩, fun h => absurd h (lt_irrefl _), fun h => by omega,
        fun _ => ⟨LinearIsometryEquiv.refl ℂ EE, fun x => heq_of_eq (he x)⟩⟩
    · by_cases hj : j < D.R.m
      · obtain ⟨H, h⟩ := hH j hj
        exact ⟨H, fun _ _ => h, fun h => by omega, fun h => by omega⟩
      · exact ⟨⟨S.Amb (tup t), 0⟩, fun _ h => absurd h hj, fun _ => ⟨LinearIsometryEquiv.refl ℂ _⟩, fun h => by omega⟩
  choose H h1 h2 h3 using key
  obtain ⟨top⟩ := h2 D.R.m le_rfl
  obtain ⟨z, hz⟩ := h3 0 rfl
  have hz' : ∀ x, toMM R t 0 ((H 0).e x) = R.HE.e (Y.eE (z x)) := fun x => eq_of_heq (hz x)
  have mem : ∀ j, 0 < j → j < D.R.m → ∀ x, (H j).e x ∈ lvlPart R (R.levR F b) t j := fun j a c x =>
    (h1 j a c).2.1.le (LinearMap.mem_range_self _ x)
  obtain ⟨f0, hf0⟩ := exists_factor (R.HE.e ∘ₗ Y.eE) (hE.1.comp Y.eE_injective) (botLift R t ∘ₗ (H 1).e) fun x => by
    have a := k0 _ (mem 1 one_pos (by omega) x)
    obtain ⟨y, hy⟩ := hE.2.1.ge (EEat_le_triv R _ a)
    obtain ⟨w, hw⟩ := Y.eE_range.ge (show y ∈ (R.EEat (R.levR F b)).comap R.HE.e from
      (congrArg (· ∈ R.EEat (R.levR F b)) hy).mpr a)
    exact ⟨w, (congrArg R.HE.e hw).trans hy⟩
  obtain ⟨f1, hf1⟩ := exists_factor (H (D.R.m - 1)).e (h1 _ (by omega) (by omega)).1
    (topLift R t ∘ₗ Y.eA t ∘ₗ top.toLinearEquiv.toLinearMap ∘ₗ
      (famCast (fun j => (H j).H) (pred_m_add_one D)).toLinearEquiv.toLinearMap) fun x => by
    have a : LinearMap.range (Y.eA t) ≤ (lvlPart R (R.levR F b) t (D.R.m - 1)).comap (topLift R t) := by
      refine (Y.eA_range t).le.trans (Submodule.span_le.2 fun y hy => hy.elim fun f hf => ?_)
      exact (congrArg (fun w => topLift R t w ∈ lvlPart R (R.levR F b) t (D.R.m - 1)) hf.2).mp (k2 f hf.1)
    exact (h1 _ (by omega) (by omega)).2.1.ge (a (LinearMap.mem_range_self _ _))
  have key2 : ∀ j, ∃ f : (H (j + 1)).H →ₗ[ℂ] (H j).H, (j = 0 → HEq f (z.symm.toLinearEquiv.toLinearMap ∘ₗ f0)) ∧
      (0 < j → j + 1 < D.R.m → ∀ x, (H j).e (f x) = R.ioY t j ((H (j + 1)).e x)) ∧ (j = D.R.m - 1 → HEq f f1) := fun j => by
    rcases Nat.eq_zero_or_pos j with rfl | h0
    · exact ⟨_, fun _ => HEq.rfl, fun h => absurd h (lt_irrefl _), fun h => by omega⟩
    · by_cases hj : j + 1 < D.R.m
      · obtain ⟨f, hf⟩ := exists_factor (H j).e (h1 j h0 (by omega)).1 (R.ioY t j ∘ₗ (H (j + 1)).e) fun x => by
          exact (h1 j h0 (by omega)).2.1.ge (k1 j h0 hj _ (mem _ (by omega) hj x))
        exact ⟨f, fun h => by omega, fun _ _ => hf, fun h => by omega⟩
      · by_cases hj' : j = D.R.m - 1
        · subst hj'
          exact ⟨f1, fun h => by omega, fun _ h => absurd h hj, fun _ => HEq.rfl⟩
        · exact ⟨0, fun h => by omega, fun _ h => absurd h hj, fun h => absurd h hj'⟩
  choose io i0 i1 i2 using key2
  refine ⟨{ Sp := fun j => (H j).H, bot := z, top := top, io := io }, fun j => (H j).e, hz', fun j a c => (h1 j a c).2.1,
    fun j a c x y => ?_, fun x => ?_, i1, fun x => ?_⟩
  · exact eq_mul_of_eq_inv_mul (RealDat.nP_pos (F := F) b) ((h1 j a c).2.2 x y)
  · refine (hz' _).trans (Eq.trans ?_ (hf0 x))
    exact congrArg (fun w => R.HE.e (Y.eE w))
      ((congrArg z (LinearMap.congr_fun (eq_of_heq (i0 0 rfl)) x)).trans (z.apply_symm_apply _))
  · exact (congrArg (H (D.R.m - 1)).e (LinearMap.congr_fun (eq_of_heq (i2 _ rfl)) x)).trans (hf1 x)

theorem topEquiv_withChain (S : RowSide D EE) (c : ∀ μ, HChain D.R.m EE (S.Amb μ)) (μ : D.what₂.Tup)
    (x : (c μ).Sp (D.R.m - 1 + 1)) : topEquiv (withChain S c) μ x = (c μ).top (famCast (c μ).Sp (pred_m_add_one D) x) := rfl

theorem iota_tie_withChain (Y : SideTie R F tup b S) (hE : R.models_HE) (hT : R.chain_Th) (c : ∀ μ, HChain D.R.m EE (S.Amb μ))
    (t : T) (hc : IsAdelicChain Y t (c (tup t))) (x : S.Amb (tup t)) :
    Y.eE ((withChain S c).iota (tup t) x) = R.Th t (Y.eA t x) := by
  refine Exists.elim hc fun e h => ?_
  have a := toMM_iota (withChain S c) R (tup t) t e (Y.eA t) h.2.2.2.1 h.2.2.2.2.1
    (fun y => (h.2.2.2.2.2 y).trans (congrArg (fun w => topLift R t (Y.eA t w)) (topEquiv_withChain S c _ y).symm)) x
  refine hE.1 (Eq.trans ?_ (a.trans (hT t _).symm))
  exact ((h.1 _).trans (congrArg (fun w => R.HE.e (Y.eE w)) ((c (tup t)).bot.apply_symm_apply _))).symm

def sideOfChain (Y : SideTie R F tup b S) (hE : R.models_HE) (hT : R.chain_Th) (c : ∀ μ, HChain D.R.m EE (S.Amb μ))
    (hc : ∀ t, IsAdelicChain Y t (c (tup t))) : SideTie R F tup b (withChain S c) where
  eE := Y.eE
  eE_range := Y.eE_range
  eE_norm := Y.eE_norm
  eA := Y.eA
  eA_range := Y.eA_range
  eA_norm := Y.eA_norm
  eOp_tie := Y.eOp_tie
  iota_tie t := iota_tie_withChain Y hE hT c t (hc t)
  lat_tie := Y.lat_tie

def multTieOfChain (Y : SideTie R F tup b S) (hE : R.models_HE) (hT : R.chain_Th) (c : ∀ μ, HChain D.R.m EE (S.Amb μ))
    (hc : ∀ t, IsAdelicChain Y t (c (tup t))) : MultTie (sideOfChain Y hE hT c hc) where
  eM t := (hc t).choose
  eM_zero t := (hc t).choose_spec.1
  eM_range t := (hc t).choose_spec.2.1
  eM_inner t := (hc t).choose_spec.2.2.1
  io_zero t := (hc t).choose_spec.2.2.2.1
  io_mid t := (hc t).choose_spec.2.2.2.2.1
  io_top t y := ((hc t).choose_spec.2.2.2.2.2 y).trans
    (congrArg (fun w => topLift R t (Y.eA t w)) (topEquiv_withChain S c _ y).symm)

theorem exists_multTie (hF : GlobalTheory.Published.HarishChandraFinite) (hD : GlobalTheory.Published.CuspRapidDecay) (hM : R.IsModels) (hT : R.chain_Th)
    (hK : KeepsLevel R F b) (hinj : Function.Injective tup) (Y : SideTie R F tup b S) :
    ∃ (c : ∀ μ, HChain D.R.m EE (S.Amb μ)) (Y' : SideTie R F tup b (withChain S c)),
      Y'.eE = Y.eE ∧ Y'.eA = Y.eA ∧ (∀ μ, (withChain S c).iota μ = S.iota μ) ∧ Nonempty (MultTie Y') := by
  have key : ∀ μ, ∃ c : HChain D.R.m EE (S.Amb μ), (∀ t (h : tup t = μ), IsAdelicChain Y t (h ▸ c)) ∧
      ((∀ t, tup t ≠ μ) → c = chainOf S μ) := fun μ => by
    by_cases h : ∃ t, tup t = μ
    · obtain ⟨t, rfl⟩ := h
      obtain ⟨c, hc⟩ := exists_isAdelicChain Y hM.HE hK t fun j hj =>
        exists_lvlModel hF hD hM.inf hM.νY hM.νY' _ _ (inv_pos.2 (RealDat.nP_pos (F := F) b)) t j hj
      refine ⟨c, fun t' h => ?_, fun h => absurd rfl (h t)⟩
      obtain rfl := hinj h
      exact hc
    · exact ⟨chainOf S μ, fun t ht => absurd ⟨t, ht⟩ h, fun _ => rfl⟩
  choose c h1 h2 using key
  have hc : ∀ t, IsAdelicChain Y t (c (tup t)) := fun t => h1 _ t rfl
  refine ⟨c, sideOfChain Y hM.HE hT c hc, rfl, rfl, fun μ => ?_, ⟨multTieOfChain Y hM.HE hT c hc⟩⟩
  by_cases h : ∃ t, tup t = μ
  · obtain ⟨t, rfl⟩ := h
    exact LinearMap.ext fun x => Y.eE_injective (((sideOfChain Y hM.HE hT c hc).iota_tie t x).trans (Y.iota_tie t x).symm)
  · exact iota_withChain S c μ (h2 μ fun t ht => h ⟨t, ht⟩)

end Inhabitant

def MultTied {X0 : BaseLevelRowSide D} (Y : RowsTie R F X0) : Prop := Function.Surjective Y.tup ∧ Nonempty (MultTie Y.sharp)

theorem isMultiplicityInner_mul_inner {V : HSp D} {Sp : D.what₂.Tau → SPar} {M : DSModel V Sp} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) {d : ℂ} (hd : d ≠ 0)
    (h : ∀ x y, ipM M μ 𝓕 (e x) (e y) = d * ⟪x, y⟫_ℂ) (x y : H) : IsMultIP M μ 𝓕 (e x) (e y) (d * ⟪x, y⟫_ℂ) := by
  have key : ∀ x y : H, ⟪x, y⟫_ℂ ≠ 0 → IsMultIP M μ 𝓕 (e x) (e y) (d * ⟪x, y⟫_ℂ) := fun x y hxy => by
    rw [← h]
    refine ipM_spec M μ 𝓕 _ _ ?_
    by_contra hn
    exact mul_ne_zero hd hxy ((h x y).symm.trans (by rw [ipM, dif_neg hn]))
  by_cases hxy : ⟪x, y⟫_ℂ = 0
  swap
  · exact key x y hxy
  by_cases hx : x = 0
  · subst hx
    intro v v'
    simp
  have hxx : ⟪x, x⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hx
  have h₁ := key x x hxx
  have h₂ := key x (x + y) (by rwa [inner_add_right, hxy, add_zero])
  intro v v'
  have hf : (fun g => star (e x v g) * e y v' g) = fun g => star (e x v g) * e (x + y) v' g - star (e x v g) * e x v' g := by
    funext g
    simp only [map_add, add_apply, Pi.add_apply]
    ring
  rw [hf]
  refine ⟨(h₂ v v').1.sub (h₁ v v').1, ?_⟩
  rw [integral_sub (h₂ v v').1 (h₁ v v').1, (h₂ v v').2, (h₁ v v').2, inner_add_right]
  ring

namespace MultTie

variable {Y : SideTie R F tup b S} (M : MultTie Y)

def row (t : T) (j : ℕ) : S.Mult (tup t) j →ₗ[ℂ] MMap (R.MY j) := toMM R t j ∘ₗ M.eM t j

theorem range_row (t : T) {j : ℕ} (h0 : 0 < j) (hj : j < D.R.m) : LinearMap.range (M.row t j) = multAt R (R.levR F b) t j := by
  rw [row, LinearMap.range_comp, M.eM_range t j h0 hj, map_lvlPart]

include M in

theorem ioY_mem (t : T) {j : ℕ} (h0 : 0 < j) (hj : j + 1 < D.R.m) {U : R.CC t (j + 1)}
    (hU : U ∈ lvlPart R (R.levR F b) t (j + 1)) : R.ioY t j U ∈ lvlPart R (R.levR F b) t j := by
  obtain ⟨x, rfl⟩ := (M.eM_range t (j + 1) (by omega) hj).ge hU
  exact (M.eM_range t j h0 (by omega)).le ⟨_, M.io_mid t j h0 hj x⟩

end MultTie

namespace MultTied

variable {X0 : BaseLevelRowSide D} {Y : RowsTie R F X0}

end MultTied

example (t : T) (j : ℕ) : lvlPart R R.triv t j = ⊤ := by
  rw [lvlPart, ← range_toMM, LinearMap.range_eq_map, Submodule.comap_map_eq_of_injective (toMM_injective R t j)]

example {X0 : BaseLevelRowSide D} {Y : RowsTie R F X0} (M : MultTie Y.sharp) (t : T) (j : ℕ) (h0 : 0 < j) (hj : j + 1 < D.R.m)
    (x : D.what₂.Mult (Y.tup t) (j + 1)) : M.eM t j (D.what₂.io (Y.tup t) j x) = R.ioY t j (M.eM t (j + 1) x) :=
  M.io_mid t j h0 hj x

example {Y : SideTie R F tup b S} (M : MultTie Y) (h : Nat.card (F.lvl b).P = 6) (t : T) (x : S.Mult (tup t) 1) (hx : ‖x‖ = 1) :
    ipCC R t 1 (M.eM t 1 x) (M.eM t 1 x) = 6 := by
  rw [M.eM_inner t 1 one_pos D.R.two_le_m, inner_self_eq_norm_sq_to_K, hx, RealDat.nP, h]
  simp

example {Y : SideTie R F tup b S} (t : T) [Subsingleton (S.Mult (tup t) 1)] (h : multAt R (R.levR F b) t 1 ≠ ⊥) :
    IsEmpty (MultTie Y) := ⟨fun M => h (by
  rw [← M.range_row t one_pos D.R.two_le_m, LinearMap.range_eq_bot]
  exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])⟩

end GlobalTheory.Mem.Th

end
