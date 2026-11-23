import Formalism.LocalToGlobal.IndefiniteReal.CxToPkgFamIn
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Formalism.LocalToGlobal.HeckeThetaElements.DefsWt
import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

section Twist

def cj (s : Bool) : ℂ →+* ℂ := cond s (starRingEnd ℂ) (RingHom.id ℂ)

theorem cj_cj (s : Bool) (z : ℂ) : cj s (cj s z) = z := by
  cases s <;> simp [cj]

theorem norm_cj (s : Bool) (z : ℂ) : ‖cj s z‖ = ‖z‖ := by
  cases s <;> simp [cj]

theorem cj_conj (s : Bool) (z : ℂ) : cj s (starRingEnd ℂ z) = starRingEnd ℂ (cj s z) := by
  cases s <;> simp [cj]

theorem re_cj (s : Bool) (z : ℂ) : (cj s z).re = z.re := by
  cases s <;> simp [cj]

theorem cj_ofReal (s : Bool) (x : ℝ) : cj s (x : ℂ) = x := by
  cases s <;> simp [cj]

def Tw (_s : Bool) (E : Type) : Type := E

namespace Tw

variable {s : Bool} {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

instance : NormedAddCommGroup (Tw s E) := inferInstanceAs (NormedAddCommGroup E)

def out (x : Tw s E) : E := x

def mk (s : Bool) (x : E) : Tw s E := x

instance : Module ℂ (Tw s E) := Module.compHom E (cj s)

theorem out_smul (z : ℂ) (x : Tw s E) : out (z • x) = cj s z • out x := rfl

theorem out_add (x y : Tw s E) : out (x + y) = out x + out y := rfl

instance : NormedSpace ℂ (Tw s E) where
  norm_smul_le z x := by
    show ‖cj s z • out x‖ ≤ ‖z‖ * ‖out x‖
    rw [norm_smul, norm_cj]

instance : InnerProductSpace ℂ (Tw s E) where
  inner x y := cj s (inner ℂ (out x) (out y))
  norm_sq_eq_re_inner x := by
    show ‖out x‖ ^ 2 = (cj s (inner ℂ (out x) (out x))).re
    rw [re_cj]; exact InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (out x)
  conj_inner_symm x y := by
    show starRingEnd ℂ (cj s (inner ℂ (out y) (out x))) = cj s (inner ℂ (out x) (out y))
    rw [← cj_conj, inner_conj_symm]
  add_left x y z := by
    show cj s (inner ℂ (out x + out y) (out z)) = cj s (inner ℂ (out x) (out z)) + cj s (inner ℂ (out y) (out z))
    rw [inner_add_left, map_add]
  smul_left x y r := by
    show cj s (inner ℂ (cj s r • out x) (out y)) = starRingEnd ℂ r * cj s (inner ℂ (out x) (out y))
    rw [inner_smul_left, map_mul, cj_conj, cj_cj]

theorem inner_eq (x y : Tw s E) : inner ℂ x y = cj s (inner ℂ (out x) (out y)) := rfl

def mkL (s : Bool) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] : E →ₛₗ[cj s] Tw s E where
  toFun := mk s
  map_add' _ _ := rfl
  map_smul' z x := by
    show z • x = cj s (cj s z) • x
    rw [cj_cj]

instance : RingHomSurjective (cj s) := ⟨fun z => ⟨cj s z, cj_cj s z⟩⟩

instance [FiniteDimensional ℂ E] : FiniteDimensional ℂ (Tw s E) :=
  Module.Finite.of_surjective (mkL s E) fun x => ⟨out x, rfl⟩

def map (s : Bool) (f : E →ₗ[ℂ] F) : Tw s E →ₗ[ℂ] Tw s F where
  toFun x := mk s (f (out x))
  map_add' x y := f.map_add (out x) (out y)
  map_smul' z x := f.map_smul (cj s z) (out x)

def sub (s : Bool) (V : Submodule ℂ E) : Submodule ℂ (Tw s E) where
  carrier := {x | out x ∈ V}
  add_mem' hx hy := V.add_mem hx hy
  zero_mem' := V.zero_mem
  smul_mem' z _ hx := V.smul_mem (cj s z) hx

def semi {K X : Type} [Field K] [AddCommGroup X] [Module K X] {σ σ' : K →+* ℂ} (s : Bool) (h : ∀ a, σ' a = cj s (σ a))
    (f : X →ₛₗ[σ] E) : X →ₛₗ[σ'] Tw s E where
  toFun x := mk s (f x)
  map_add' x y := f.map_add x y
  map_smul' a x := by
    show f (a • x) = cj s (σ' a) • f x
    rw [h, cj_cj, map_smulₛₗ]

def rep (s : Bool) {G : Type} [Group G] (ρ : Representation ℂ G E) : Representation ℂ G (Tw s E) where
  toFun g := map s (ρ g)
  map_one' := by ext x; show ρ 1 (out x) = out x; rw [map_one]; rfl
  map_mul' g h := by ext x; show ρ (g * h) (out x) = ρ g (ρ h (out x)); rw [map_mul]; rfl

theorem linInd (s : Bool) {ι : Type} [Fintype ι] {v : ι → E} (h : LinearIndependent ℂ v) :
    LinearIndependent ℂ fun i => mk s (v i) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have h2 := h (fun i => cj s (g i)) hg i
  have h3 := congrArg (cj s) h2
  rwa [cj_cj, map_zero] at h3

theorem span_top (s : Bool) {ι : Type} [Fintype ι] {v : ι → E} (h : Submodule.span ℂ (Set.range v) = ⊤) :
    Submodule.span ℂ (Set.range fun i => mk s (v i)) = ⊤ := by
  have h1 : Set.range (fun i => mk s (v i)) = (mkL s E) '' Set.range v := by
    rw [← Set.range_comp]; rfl
  rw [h1, ← Submodule.map_span, h, Submodule.map_top, LinearMap.range_eq_top]
  intro x
  exact ⟨out x, rfl⟩

end Tw

variable {K : Type} [Field K]

open Classical in

def sgAt (σ₀ : K →+* ℂ) (v : InfinitePlace K) : K →+* ℂ := if v = InfinitePlace.mk σ₀ then σ₀ else v.embedding

open Classical in

def twAt (σ₀ : K →+* ℂ) (v : InfinitePlace K) : Bool := if v.embedding = sgAt σ₀ v then false else true

theorem emb_eq (σ₀ : K →+* ℂ) (v : InfinitePlace K) (a : K) : v.embedding a = cj (twAt σ₀ v) (sgAt σ₀ v a) := by
  unfold twAt
  split_ifs with h
  · rw [h]; rfl
  · unfold sgAt at h ⊢
    split_ifs at h ⊢ with hv
    · subst hv
      rcases InfinitePlace.embedding_mk_eq σ₀ with h' | h'
      · exact absurd h' h
      · rw [h', NumberField.ComplexEmbedding.conjugate_coe_eq]; rfl
    · exact absurd rfl h

theorem sgAt_mk (σ₀ : K →+* ℂ) {v : InfinitePlace K} (hv : v = InfinitePlace.mk σ₀) : sgAt σ₀ v = σ₀ := by
  simp [sgAt, hv]

end Twist

structure HMod (X : Type) [AddCommGroup X] [Module ℂ X] where

  H : Type
  [nH : NormedAddCommGroup H]
  [iH : InnerProductSpace ℂ H]
  [fH : FiniteDimensional ℂ H]

  e : H →ₗ[ℂ] X

attribute [instance] HMod.nH HMod.iH HMod.fH

def HMod.Is {X : Type} [AddCommGroup X] [Module ℂ X] (M : HMod X) (V : Submodule ℂ X) (ip : X → X → ℂ) : Prop :=
  Function.Injective M.e ∧ LinearMap.range M.e = V ∧ ∀ x y, inner ℂ x y = ip (M.e x) (M.e y)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Levels

open Formalism.IndefR.Lev Formalism.IndefR.Mult

def actL (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) (g0 : G0 L.Pg L.r) :
    (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := actG0 V β L g0
  map_add' F F' := by
    funext h
    by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
    · simp only [actG0, dif_pos hk, Pi.add_apply, mul_add]
    · simp only [actG0, dif_neg hk, Pi.add_apply, Pi.zero_apply, add_zero]
  map_smul' c F := by
    funext h
    by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
    · simp only [actG0, dif_pos hk, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [mul_left_comm]
    · simp only [actG0, dif_neg hk, Pi.smul_apply, Pi.zero_apply, smul_zero]

def gaL {G : Type} [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) :=
  ∑ g, c g • actL V β L (eG g)

def levPOf {G K : Type} [Group G] [Field K] {Pg : Finset (Pl D.host.E)} {r : ℕ} (eG : G ≃* G0 Pg r) (σ : K →+* ℂ)
    (P : Subgroup G) (ψ : P →* Kˣ) : LevelP Pg r ℂ :=
  ⟨P.comap eG.symm.toMonoidHom, (Units.map σ.toMonoidHom).comp (ψ.comp (eG.symm.toMonoidHom.subgroupComap P))⟩

def levS (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) : Set (GA D V) := levG V β L

def IsSDFrame (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) : Prop :=
  ∃ c, IsBaseFrame V β Λ (N ^ c)

def IsHeckeAt (V : HSp D) (PP : Pl D.host.E) (k : ℕ) (α : GA D V) : Prop :=
  ∃ (e : AE D) (ϖ : 𝓞 D.host.E), Formalism.L2.NTheta.IsIdemAt e PP ∧ ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2 ∧
    Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α

def hPart {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Subgroup (GA D V)) {Pl0 : Type} (ok : Set Pl0)
    (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) : Submodule ℂ (MMap M) :=
  ⨅ (P : Pl0) (_ : P ∈ ok) (k : ℕ) (_ : k ≤ V.rank) (α : GA D V) (_ : IsHeckeAt V (pl P) k α) (R : Finset (GA D V))
    (_ : Bridge.IsDC J α⁻¹ R),
    LinearMap.ker (heckeOn M R - ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) • LinearMap.id)

def levEnv (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) : Bridge.LevDat D V where
  J := (toAfE V (lev D.sp.cm V.gram β (flag1L L))).comap (finHom V).range.subtype
  χ := (levCharAfE V β (flag1L L)).comp ((finHom V).range.subtype.subgroupComap _)
  Q := (toAfE V (lev D.sp.cm V.gram β (flagL L))).comap (finHom V).range.subtype
  J_le := fun _ h => ⟨h.1, Subgroup.mem_top _⟩
  ch := (levCharAfE V β (flagL L)).comp ((finHom V).range.subtype.subgroupComap _)
  ch_J := fun k => (levCharAfE_flag V β L _ k.2 _).symm

def isTEnv (V : HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V) : Prop :=
  i.2 ≤ V.rank → ∃ α, IsHeckeAt V (pl i.1) i.2 α ∧ (x : GL _ _) = finHom V α⁻¹

def isLocEnv (V : HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V) : Prop :=
  ∃ (e : AE D) (α : GA D V), Formalism.L2.NTheta.IsIdemAt e (pl i.1) ∧ α ∈ GfC V ∧ SuppAt e V α ∧ (x : GL _ _) = finHom V α

def IsMeasDef (V : HSp D) (Kf : Subgroup (GL (Fin V.rank) (EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  IsMeasLevDef V Kf μ ∧ IsFundamentalDomain (GQ V) 𝓕 μ

end Levels

structure CoefA (V : HSp D) where

  W : Type
  [nW : NormedAddCommGroup W]
  [iW : InnerProductSpace ℂ W]
  [fW : FiniteDimensional ℂ W]

  ρ : GA D V →* Module.End ℂ W

attribute [instance] CoefA.nW CoefA.iW CoefA.fW

namespace CoefA

variable {V : HSp D} (c : CoefA V)

def Is : Prop :=
  (∀ h ∈ GfC V, c.ρ h = 1) ∧ (∀ h x y, inner ℂ (c.ρ h x) (c.ρ h y) = inner ℂ x y) ∧ (∀ x, Continuous fun h => c.ρ h x) ∧
    Nontrivial c.W ∧ ∀ U : Submodule ℂ c.W, (∀ h, U.map (c.ρ h) ≤ U) → U = ⊥ ∨ U = ⊤

def coef : Bridge.CoefDat D V where
  W := c.W
  ρ := c.ρ.comp (GQ V).subtype

def ext : (Bridge.Gf V → c.W) →ₗ[ℂ] (GA D V → c.W) where
  toFun f h := c.ρ h⁻¹ (f ((finHom V).rangeRestrict h))
  map_add' f f' := by funext h; simp
  map_smul' a f := by funext h; simp

def toMap {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm] (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) :
    (Bridge.Gf V → c.W) →ₗ[ℂ] (Dm →ₗ[ℂ] (GA D V → ℂ)) where
  toFun f :=
    { toFun := fun v h => pr (c.ext f h) v
      map_add' := fun v v' => by funext h; simp
      map_smul' := fun a v => by funext h; simp }
  map_add' f f' := by ext v h; simp
  map_smul' a f := by ext v h; simp

end CoefA

def levEnvOf (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {Pl0 : Type}
    (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) : Bridge.LevEnv D V (ok × ℕ) :=
  ⟨levEnv V β L, isTEnv V pl ok, isLocEnv V pl ok⟩

section Chars

open Formalism.L2.Host Formalism.L2.JoinChr Formalism.IndefR.Mult

def ChrEq (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) : Prop :=
  IsHeckeChar D c ∧ ∀ (P : Pl D.host.E) (e : AE D), IsPlIdem D e P → ∀ (k : D.host.Eˣ) (x : (AE D)ˣ),
    (x : AE D) = locE D e (k : D.host.E) → ((c x : Circle) : ℂ) = ((χ.locK P k : ℂˣ) : ℂ)

def IsRes (χ : HChar D.host.E) (P : Pl D.host.E) (c : (kP P)ˣ →* ℂˣ) : Prop :=
  ∀ (a : 𝓞 D.host.E) (k : D.host.Eˣ) (u : (kP P)ˣ), (k : D.host.E) = a → (u : kP P) = Ideal.Quotient.mk _ a →
    c u = χ.locK P k

variable (D) in

abbrev Ptw : TPar D := tparRec D

variable (D) in

def labLL (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)

def labE (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) : D.host.E →+* ℂ := σ.comp (labLL D τ)

open Classical in

def lab (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : D.what₂.Tau :=
  if h : ∃ τ, labE σ τ = tauE D ρ ∨ labE σ τ = (starRingEnd ℂ).comp (tauE D ρ) then h.choose else ρ

def kapAt (W : HSp D) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    Fin (W.sig (tauE D ρ)).1 ⊕ Fin (W.sig (tauE D ρ)).2 → ℤ :=
  Formalism.L2.NTheta.kapW (D.hc (lab σ ρ)) _ _

open Classical in

def parAt (W : HSp D) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : SPar :=
  if labE σ (lab σ ρ) = tauE D ρ then Formalism.L2.NTheta.holPar _ _ (kapAt W σ ρ)
  else dualPar (Formalism.L2.NTheta.holPar _ _ (kapAt W σ ρ))

def ipAt {W : HSp D} {σ : D.what₂.LL →+* ℂ} (M : DSModel W (parAt W σ)) (μ : Measure (GA D W)) (𝓕 : Set (GA D W))
    (T T' : MMap M) : ℂ :=
  (∏ ρ, ((dimK _ _ (kapAt W σ ρ) : ℚ) : ℂ)) * ipM M μ 𝓕 T T'

variable {V : HSp D} {S : D.what₂.Tau → SPar}

def cart (M : DSModel V S) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (M.fr τ)⁻¹ * Formalism.REAL.Jm (M.ε τ) * M.fr τ

def onb (M : DSModel V S) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ := (M.fr τ)⁻¹

def lowT (M : DSModel V S) (τ : D.what₂.Tau) : Submodule ℂ (M.sm τ) :=
  (lowKSub (M.ε τ) (M.lam τ) (M.σ τ)).comap (M.sm τ).subtype

abbrev SmT (M : DSModel V S) : Type := ⨂[ℂ] τ, M.sm τ

abbrev LowT (M : DSModel V S) : Type := ⨂[ℂ] τ, lowT M τ

variable (D) in

def aPl (i : Fin D.R.m) (p : ℕ) (τ : D.what₂.Tau) (n : ℕ) : ℕ :=
  if n < p then ⌊Formalism.L2.NTheta.lamAt (D.hc τ) n + (D.hc τ).e i - ((p : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2⌋.toNat else 0

variable (D) in

def aMi (i : Fin D.R.m) (p q : ℕ) (τ : D.what₂.Tau) (n : ℕ) : ℕ :=
  if n < q then ⌊-((D.hc τ).e i + Formalism.L2.NTheta.lamAt (D.hc τ) (p + (q - n) - 1) + ((q - n : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2)⌋.toNat
  else 0

end Chars

section Spaces

open Formalism.IndefR.Lev

variable (D) in

abbrev Yc (j : ℕ) : HSp D := D.sp.Y (min j D.R.m)

variable (D) in

abbrev Wc (i : Fin D.R.m) : HSp D := D.sp.W ((i : ℕ) + 1)

variable (D) in

abbrev Vc (i : Fin D.R.m) : HSp D := D.sp.V ((i : ℕ) + 1)

theorem r_le_Y (j : ℕ) : D.R.r ≤ (Yc D j).rank := by
  show D.R.r ≤ (D.sp.Y (min j D.R.m)).rank
  rw [D.sp.Y_rank _ (min_le_right _ _)]
  exact Nat.le_add_right _ _

theorem r_le_X : D.R.r ≤ D.sp.X'.rank := by
  rw [D.sp.X'_rank]
  exact Nat.le_add_right _ _

theorem r_le_rank_Wc (i : Fin D.R.m) : D.R.r ≤ (Wc D i).rank := by
  show D.R.r ≤ (D.sp.W ((i : ℕ) + 1)).rank
  rw [D.sp.W_rank _ (Nat.succ_pos _) i.2]

theorem r_le_V (i : Fin D.R.m) : D.R.r ≤ (Vc D i).rank := by
  show D.R.r ≤ (D.sp.V ((i : ℕ) + 1)).rank
  rw [D.sp.V_rank _ (Nat.succ_pos _) i.2]
  exact Nat.le_add_right _ _

variable (D) in

structure LevCh (T : Type) where

  C : Formalism.L2.Host.CharFrame D

  xiH : T → Formalism.L2.Host.HChar D.host.E

  mu0 : ℕ → ((AE D)ˣ →* Circle)

  eta : (AE D)ˣ →* Circle

  xi : T → ((AE D)ˣ →* Circle)

  Pg : Finset (Pl D.host.E)

  Q : T → Finset (Pl D.host.E)

  chi : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ

  xiR : T → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ

  ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E)
  ΛX : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)
  ΛV : ∀ i, Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)
  ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E)

  βY : ∀ j, GL (Fin (Yc D j).rank) (EAf D)

  βX : GL (Fin D.sp.X'.rank) (EAf D)

  βV : ∀ i, GL (Fin (Vc D i).rank) (EAf D)

  βW : ∀ i, GL (Fin (Wc D i).rank) (EAf D)

namespace LevCh

variable {T : Type} (L : LevCh D T)

def mu (t : T) : ℕ → ((AE D)ˣ →* Circle) := Lift.tup L.mu0 (L.xi t)

def datYt (t : T) (j : ℕ) (P : LevelP L.Pg D.R.r ℂ) : LevDat D.host.E ℂ (Yc D j).rank :=
  datY _ D.R.r D.R.t j (r_le_Y j) L.Pg (L.Q t) P L.chi (L.xiR t) Frm.B

def dat0 (P : LevelP L.Pg D.R.r ℂ) : LevDat D.host.E ℂ (Yc D 0).rank :=
  datY _ D.R.r D.R.t 0 (r_le_Y 0) L.Pg ∅ P L.chi (fun _ => 1) Frm.B

def datXt (t : T) : LevDat D.host.E ℂ D.sp.X'.rank :=
  datY _ D.R.r D.R.t D.R.m r_le_X L.Pg (L.Q t) (LevelP.triv _ _ _) L.chi (L.xiR t) Frm.B

def datVt (i : Fin D.R.m) (t : T) : LevDat D.host.E ℂ (Vc D i).rank :=
  datY _ D.R.r D.R.t 1 (r_le_V i) L.Pg (L.Q t) (LevelP.triv _ _ _) (fun _ => L.chi ((i : ℕ) + 1)) (L.xiR t) Frm.A

def datWp (i : Fin D.R.m) (P : LevelP L.Pg D.R.r ℂ) : LevDat D.host.E ℂ (Wc D i).rank :=
  datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) L.Pg ∅ P (fun _ _ => 1) (fun _ => 1) Frm.B

abbrev triv : LevelP L.Pg D.R.r ℂ := LevelP.triv _ _ _

structure Is (μ0 : T) : Prop where
  mu0 : ∀ j : Fin D.R.m, ChrEq (L.mu0 ((j : ℕ) + 1)) (L.C.mu0 j)
  eta : ChrEq L.eta L.C.eta
  xi : ∀ t, ChrEq (L.xi t) (L.xiH t)
  xi_inj : Function.Injective L.xiH
  xi_base : L.xiH μ0 = 1
  xi_fin : ∀ t, ∃ n : ℕ, 0 < n ∧ (L.xiH t).OrderDvd n
  xi_triv : ∀ t, (L.xiH t).TrivOn D.host.F
  xi_tame : ∀ t v, (L.xiH t).TameAt v
  Pg : ∀ PP, PP ∈ L.Pg ↔ ∃ k, L.C.P.Div k PP
  Q_pl : ∀ t, IsTwistPlaces D.host.g (L.Q t)
  Q_off : ∀ t, ∀ PP ∈ L.Q t, ((D.host.condN * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧
    ∀ u : D.what₂.Word, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal
  Q_de : ∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
    ∀ t, ∀ PP ∈ L.Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭
  Q_ram : ∀ t PP, ¬ (L.xiH t).UnrAt PP ↔ PP ∈ L.Q t ∨ ∃ PP' ∈ L.Q t, IsConjPl PP' PP
  chi : ∀ (j : Fin D.R.m), ∀ PP ∈ L.Pg, IsRes (L.C.mu0 j) PP (L.chi ((j : ℕ) + 1) PP)⁻¹
  xiR : ∀ t, ∀ PP ∈ L.Q t, IsRes (L.xiH t) PP (L.xiR t PP)
  βY : ∀ j, j < D.R.m → IsSDFrame (Yc D j) (L.βY j) (L.ΛY j) (D.host.g 0 * D.host.g 1)
  βX : IsSDFrame D.sp.X' L.βX L.ΛX 1
  βV : ∀ i, IsSDFrame (Vc D i) (L.βV i) (L.ΛV i) 1
  βW : ∀ i, IsSDFrame (Wc D i) (L.βW i) (L.ΛW i) 1

end LevCh

end Spaces

section Real

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable (D) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m)

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Face where

  P0 : Subgroup G

  ψ0 : P0 →* D.what₂.LLˣ

  P1 : Subgroup G

  ψ1 : P1 →* D.what₂.LLˣ

  Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)

  Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)

  Zsc : DefSub A.fam.amb → IndefScale A.fam.base

namespace Face

variable {D A} (F : Face D A)

abbrev fc : DefSub A.fam.amb → DefFace A.fam.base := faceOf A F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc

abbrev cr : Crd A.fam.amb F.fc := crdOf A F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc

def lvl (b : Bool) : Lvl D.what₂.LL G := cond b (A.fam.lvl F.P1 F.ψ1) (A.fam.lvl F.P0 F.ψ0)

end Face

abbrev sg0 : D.what₂.LL →+* ℂ := sgAt D.what₂.embLL A.v0

abbrev PolF (a b : ℕ) : Type := MvPolynomial (FVar D a b) ℂ

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in

structure RealDat (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] extends LevCh D T where

  hv0 : A.v0 = InfinitePlace.mk D.what₂.embLL

  eG : G ≃* G0 Pg D.R.r

  pl : Pl0 → Pl D.host.E

  Sb : Finset (Pl D.host.E)

  θ : InfFam D

  ψ : AddChar (AF D.host.F) ℂ

  MY : ∀ j, DSModel (Yc D j) (parB (Ptw D) (min j D.R.m))

  MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)

  MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ)

  cX : CoefA D.sp.X'

  cV : ∀ i, CoefA (Vc D i)

  B : Bridge.FamReal D A cX.coef (fun i => (cV i).coef) (fun t => levEnvOf D.sp.X' βX (toLevCh.datXt t) pl (A.ok t))
    (fun i t => levEnvOf (Vc D i) (βV i) (toLevCh.datVt i t) pl (A.ok t))

  prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ

  HX : T → HMod (Bridge.Gf D.sp.X' → cX.W)

  HV : ∀ i, T → HMod (Bridge.Gf (Vc D i) → (cV i).W)

  HE : HMod (MMap (MY 0))

  HW : ∀ i σ, HMod (MMap (MW i σ))

  gE : Representation ℂ G HE.H

  gW : ∀ i σ, Representation ℂ G (HW i σ).H

  jX : ∀ t, A.fam.amb.FR t →ₛₗ[D.what₂.embLL] (HX t).H

  jV : ∀ i t, A.fam.amb.FL i t →ₛₗ[D.what₂.embLL] (HV i t).H

  νY : T → ∀ j, Measure (GA D (Yc D j))
  fdY : T → ∀ j, Set (GA D (Yc D j))

  ν0 : Measure (GA D (Yc D 0))
  fd0 : Set (GA D (Yc D 0))

  νX : T → Measure (GA D D.sp.X')
  fdX : T → Set (GA D D.sp.X')

  νV : ∀ i, T → Measure (GA D (Vc D i))
  fdV : ∀ i, T → Set (GA D (Vc D i))

  νW : ∀ i, Measure (GA D (Wc D i))
  fdW : ∀ i, Set (GA D (Wc D i))

  ωY : T → ∀ k, GA D (Yc D k) × GA D (Yc D (k + 1)) →* Module.End ℂ (WO (Yc D k) (Yc D (k + 1)) → ℂ)

  ωX : T → GA D (Yc D (D.R.m - 1)) × GA D D.sp.X' →* Module.End ℂ (WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ)

  ωP : ∀ i, T → GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)

  vac : ∀ k, WO (Yc D k) (Yc D (k + 1)) → ℂ
  vacX : WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ
  vacP : ∀ i, WO (Vc D i) (Wc D i) → ℂ

  vY : T → ∀ k, WO (Yc D k) (Yc D (k + 1)) → ℂ
  vX : T → WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ

  vP : ∀ i, T → WO (Vc D i) (Wc D i) → ℂ

  ItY : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank →ₗ[ℂ] SmT (MY (k + 1)) →ₗ[ℂ] SmT (MY k)
  ItX : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank →ₗ[ℂ] SmT MX →ₗ[ℂ] SmT (MY (D.R.m - 1))

  ioY : ∀ t k, MultT θ (MY (k + 1)) (levS _ (βY (k + 1)) (toLevCh.datYt t (k + 1) toLevCh.triv))
      (levChi _ (βY (k + 1)) (toLevCh.datYt t (k + 1) toLevCh.triv)) →ₗ[ℂ]
    MultT θ (MY k) (levS _ (βY k) (toLevCh.datYt t k toLevCh.triv)) (levChi _ (βY k) (toLevCh.datYt t k toLevCh.triv))
  ioX : ∀ t, LinearMap.range (cX.toMap prX ∘ₗ (HX t).e) →ₗ[ℂ]
    MultT θ (MY (D.R.m - 1)) (levS _ (βY (D.R.m - 1)) (toLevCh.datYt t (D.R.m - 1) toLevCh.triv))
      (levChi _ (βY (D.R.m - 1)) (toLevCh.datYt t (D.R.m - 1) toLevCh.triv))

  Th : ∀ t, (HX t).H →ₗ[ℂ] HE.H

  BV : ∀ i, D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ

  ioP : ∀ i, LowT (MW i (sg0 D A)) →ₗ[ℂ] (cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank

  thF : ∀ i t, (HV i t).H →ₗ[ℂ] MMap (MW i (sg0 D A))

  thG : ∀ i t, (HV i t).H →ₗ[ℂ] (HW i (sg0 D A)).H

  nW : Fin D.R.m → ℕ

  FW : ∀ i, Arith.FormsL D.what₂.LL Ks (Fin (nW i) → D.what₂.LL) (fun σ => (HW i σ).H) G

  mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T
  twPl : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))

  kap : ℝ

  lam : Fin D.R.m → T → A.fam.base.Ix → InfinitePlace D.what₂.LL → ℝ

  err0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ

namespace RealDat

variable {D A} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def eC (σ : D.what₂.LL →+* ℂ) (g : G) : ℂ := σ ((idemOf A.X).coeff g)

def e0 : (GA D (Yc D 0) → ℂ) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) :=
  gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (eC (A := A) D.what₂.embLL)

def eWf (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : (GA D (Wc D i) → ℂ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
  gaL (Wc D i) (R.βW i) (R.datWp i R.triv) R.eG (eC (A := A) σ)

def EEat (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (MMap (R.MY 0)) :=
  goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) R.e0

def Wall (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : Submodule ℂ (MMap (R.MW i σ)) :=
  Mult R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv))

def Wat (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (MMap (R.MW i σ)) :=
  goodPart R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)) (R.eWf i σ)

def levR (b : Bool) : LevelP R.Pg D.R.r ℂ := levPOf R.eG D.what₂.embLL (F.lvl b).P (F.lvl b).ψ

def levL (b : Bool) (σ : D.what₂.LL →+* ℂ) : LevelP R.Pg D.R.r ℂ := levPOf R.eG σ (F.lvl b).P (F.lvl b).ψ⁻¹

abbrev CC (t : T) (j : ℕ) : Submodule ℂ (SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) :=
  MultT R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv))

def thDn (t : T) : (R.HX t).H →ₗ[ℂ] (SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) :=
  (R.CC t 0).subtype ∘ₗ Lift.thetaDn (R.CC t) (R.ioY t) (D.R.m - 1) ∘ₗ R.ioX t ∘ₗ
    (R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict

def polE (p : Pl0 → D.what₂.LL[X]) (P : Pl0) : ℂ[X] :=
  ((p P).map D.what₂.embLL).comp (C ((A.q P : ℂ) ^ (D.R.m / 2 * D.R.t))⁻¹ * X)

def polW (p : Pl0 → D.what₂.LL[X]) (P : Pl0) : ℂ[X] :=
  (dualPoly ((A.q P : D.what₂.LL) ^ (D.R.r - 1 + D.R.m / 2 * D.R.t)) (p P)).map D.what₂.embLL

def EEp (p : A.fam.base.Ix) : Submodule ℂ R.HE.H :=
  (hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q (polE (A := A) p.1)).comap R.HE.e

def Wp (i : Fin D.R.m) (p : A.fam.base.Ix) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (R.Wat i (sg0 D A) R.triv ⊓
    hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q (polW (A := A) p.1)).comap (R.HW i _).e

def WL (b : Bool) (i : Fin D.R.m) : Submodule D.what₂.LL (Fin (R.nW i) → D.what₂.LL) :=
  (R.FW i).Wgood (F.lvl b).P (F.lvl b).ψ⁻¹ fun g => (idemOf A.X).coeff g

def bL (b : Bool) (i : Fin D.R.m) (k : Fin (Module.finrank D.what₂.LL (R.WL F b i))) : Fin (R.nW i) → D.what₂.LL :=
  (Module.finBasis D.what₂.LL (R.WL F b i) k : Fin (R.nW i) → D.what₂.LL)

def nP (b : Bool) : ℝ := Nat.card (F.lvl b).P

def bC (b : Bool) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (k : Fin (Module.finrank D.what₂.LL (R.WL F b i))) : (R.HW i σ).H :=
  (((Real.sqrt (nP F b))⁻¹ : ℝ) : ℂ) • (R.FW i).j σ (R.bL F b i k)

def WS (b : Bool) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : Submodule ℂ (R.HW i σ).H :=
  Submodule.span ℂ (Set.range (R.bC F b i σ))

include R in
theorem emb0 (a : D.what₂.LL) : A.v0.embedding a = cj (twAt D.what₂.embLL A.v0) (D.what₂.embLL a) := by
  rw [emb_eq D.what₂.embLL A.v0 a, sgAt_mk _ R.hv0]

def toCx : CxData A.fam.amb where
  FC t := Tw (twAt D.what₂.embLL A.v0) (R.HX t).H
  jR t := Tw.semi _ R.emb0 (R.jX t)
  EE := Tw (twAt D.what₂.embLL A.v0) R.HE.H
  Θ t := Tw.map _ (R.Th t)
  EEp p := Tw.sub _ (R.EEp p)
  EEl b := Tw.sub _ ((R.EEat (R.levR F b)).comap R.HE.e)
  FLC i t := Tw (twAt D.what₂.embLL A.v0) (R.HV i t).H
  jL i t := Tw.semi _ R.emb0 (R.jV i t)
  W i := Tw (twAt D.what₂.embLL A.v0) (R.HW i (sg0 D A)).H
  θ' i t := Tw.map _ (R.thG i t)
  Wp i p := Tw.sub _ (R.Wp i p)
  dW b i := Module.finrank D.what₂.LL (R.WL F b i)
  WC b i v := Tw (twAt D.what₂.embLL v) (R.WS F b i (sgAt D.what₂.embLL v))
  bW b i _ k := Tw.mk _ ⟨R.bC F b i _ k, Submodule.subset_span ⟨k, rfl⟩⟩
  eW b i := Tw.map _ (((Real.sqrt (nP F b) : ℝ) : ℂ) • (R.WS F b i (sg0 D A)).subtype)
  M b i := (R.FW i).Mcoord (F.lvl b).P (F.lvl b).ψ⁻¹ (fun g => (idemOf A.X).coeff g) (R.bL F b i)
  nP := nP F
  μ := R.mu
  Tw := R.twPl
  κ _ := R.kap
  lam := R.lam
  err0 := R.err0

def gEx : Representation ℂ G (R.toCx F).EE := Tw.rep (E := R.HE.H) _ R.gE

def gWx (i : Fin D.R.m) : Representation ℂ G ((R.toCx F).W i) := Tw.rep (E := (R.HW i (sg0 D A)).H) _ (R.gW i (sg0 D A))

end RealDat

end Real

end Formalism.IndefR.Links

end
