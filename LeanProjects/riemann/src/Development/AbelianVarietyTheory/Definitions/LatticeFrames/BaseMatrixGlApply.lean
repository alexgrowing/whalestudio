import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Formalism.LocalRingCardinality.PosOfIsomEmb

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {ι : Type} (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

section Coord

variable {K : Type} [Field K] {Y : Type} [Fintype Y] [DecidableEq Y] (V : HSp D) (pr : AE D →+* K)
  (β : Matrix (Fin V.rank) Y K) (γ : Matrix Y (Fin V.rank) K) (βγ : β * γ = 1) (γβ : γ * β = 1)

def coordHom (βγ : β * γ = 1) (γβ : γ * β = 1) : GA D V →* GL Y K :=
  MonoidHom.toHomUnits
    { toFun := fun κ => γ * (mt V κ).map pr * β
      map_one' := by simp [Formalism.L2.Theta.mt, γβ]
      map_mul' := fun κ κ' => by
        have h : (mt V (κ * κ')).map pr = (mt V κ).map pr * (β * γ) * (mt V κ').map pr := by
          rw [βγ, Matrix.mul_one, ← Matrix.map_mul]; simp [Formalism.L2.Theta.mt]
        rw [h]; simp only [Matrix.mul_assoc] }

theorem coordHom_val (κ : GA D V) : (coordHom V pr β γ βγ γβ κ).val = γ * (mt V κ).map pr * β := rfl

theorem eq_coordHom_iff (κ : GA D V) (g : GL Y K) :
    (mt V κ).map pr = β * g.val * γ ↔ g = coordHom V pr β γ βγ γβ κ := by
  constructor
  · intro h
    refine Units.ext ?_
    rw [coordHom_val, h]
    calc g.val = (γ * β) * g.val * (γ * β) := by simp [γβ]
      _ = _ := by simp only [Matrix.mul_assoc]
  · rintro rfl
    rw [coordHom_val]
    calc (mt V κ).map pr = (β * γ) * (mt V κ).map pr * (β * γ) := by simp [βγ]
      _ = _ := by simp only [Matrix.mul_assoc]

def movesGrp (L : GlobalTheory.FinPl.Lat V) (P : GlobalTheory.FinPl.Pl D → Prop) : Subgroup (GA D V) where
  carrier := {κ | GlobalTheory.FinPl.Moves V κ L L P}
  one_mem' := fun y _ => by simp [Formalism.L2.Theta.mt]
  mul_mem' := fun {κ κ'} h h' y hy => by
    have hy' : ∀ i, (mt V κ' *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D P := fun i => by
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
    rw [h' y hy, h _ hy', Matrix.mulVec_mulVec]
    simp [Formalism.L2.Theta.mt]
  inv_mem' := fun {κ} h y hy => by
    have hy' : ∀ i, (mt V κ⁻¹ *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D P := fun i => by
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
    rw [h _ hy', Matrix.mulVec_mulVec]
    have : mt V κ * mt V κ⁻¹ = 1 := by
      simp only [Formalism.L2.Theta.mt]; rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    rw [this, Matrix.one_mulVec]

end Coord

section AtLevel

variable {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP)

def GX.MatAt {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP) (κ : GA D (D.sp.X 0))
    (g : GL (XIx (Fin D.R.k) (Fin D.R.t) 0) H.k) : Prop :=
  (mt (D.sp.X 0) κ).map H.q.pr = (H.FX 0 (Nat.zero_le _)).β * g.val * (H.FX 0 (Nat.zero_le _)).γ

abbrev GX.lev0 {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP) :=
  (H.S.T (Fin D.R.t)).lev 0 (H.s + 1) (Nat.zero_add _)

def GX.mat0 : GA D (D.sp.X 0) →* GL (XIx (Fin D.R.k) (Fin D.R.t) 0) H.k :=
  coordHom (D.sp.X 0) H.q.pr _ _ (H.FX 0 (Nat.zero_le _)).βγ (H.FX 0 (Nat.zero_le _)).γβ

theorem GX.matAt_iff (κ : GA D (D.sp.X 0)) (g : GL (XIx (Fin D.R.k) (Fin D.R.t) 0) H.k) : H.MatAt κ g ↔ g = H.mat0 κ :=
  eq_coordHom_iff _ _ _ _ _ _ κ g

end AtLevel

def OffX.mat0 (i : ι) : GA D (D.sp.X 0) →* GL (Fin (D.sp.X 0).rank) k :=
  coordHom (D.sp.X 0) (o.p i).pr _ _ (o.β 0 i).bb' (o.β 0 i).b'b

def InLev0 (κ : GA D (D.sp.X 0)) : Prop :=
  GlobalTheory.FinPl.Moves (D.sp.X 0) κ (a.x 0).L (a.x 0).L (fun _ => True) ∧
    (∀ i (g : GL (Fin (D.sp.X 0).rank) k), (mt (D.sp.X 0) κ).map (o.p i).pr = (o.β 0 i).b * g.val * (o.β 0 i).b' →
      g • o.Q 0 i = o.Q 0 i) ∧
    ∀ PP g, (G PP).MatAt κ g → embX ((G PP).s + 1) g ∈ (G PP).lev0.J

theorem inLev0_iff (κ : GA D (D.sp.X 0)) : InLev0 o G κ ↔
    GlobalTheory.FinPl.Moves (D.sp.X 0) κ (a.x 0).L (a.x 0).L (fun _ => True) ∧ (∀ i, o.mat0 i κ • o.Q 0 i = o.Q 0 i) ∧
      ∀ PP, embX ((G PP).s + 1) ((G PP).mat0 κ) ∈ (G PP).lev0.J := by
  refine and_congr Iff.rfl (and_congr (forall_congr' fun i => ?_) (forall_congr' fun PP => ?_))
  · simp only [eq_coordHom_iff _ _ _ _ (o.β 0 i).bb' (o.β 0 i).b'b, forall_eq]
    rfl
  · simp only [GX.matAt_iff, forall_eq]

def levelZeroSubgroup : Subgroup (GA D (D.sp.X 0)) :=
  movesGrp (D.sp.X 0) (a.x 0).L (fun _ => True) ⊓
    ((⨅ i, (MulAction.stabilizer (GL (Fin (D.sp.X 0).rank) k) (o.Q 0 i)).comap (o.mat0 i)) ⊓
      ⨅ PP, ((G PP).lev0.J.comap (embX ((G PP).s + 1))).comap (G PP).mat0)

theorem mem_lev0Grp (κ : GA D (D.sp.X 0)) : κ ∈ levelZeroSubgroup o G ↔ InLev0 o G κ := by
  rw [inLev0_iff]
  simp only [levelZeroSubgroup, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  rfl

variable {o G} in

theorem InLev0.mul {κ κ' : GA D (D.sp.X 0)} (h : InLev0 o G κ) (h' : InLev0 o G κ') : InLev0 o G (κ * κ') :=
  (mem_lev0Grp o G _).1 (mul_mem ((mem_lev0Grp o G _).2 h) ((mem_lev0Grp o G _).2 h'))

variable {o G} in

theorem InLev0.inv {κ : GA D (D.sp.X 0)} (h : InLev0 o G κ) : InLev0 o G κ⁻¹ :=
  (mem_lev0Grp o G _).1 (inv_mem ((mem_lev0Grp o G _).2 h))

open scoped Pointwise in
variable {o G} in

theorem InLev0.smul_ker {κ : GA D (D.sp.X 0)} (h : InLev0 o G κ) (i : ι) : o.mat0 i κ • (o.Q 0 i).ker = (o.Q 0 i).ker := by
  rw [← Pair.smul_ker, ((inLev0_iff o G κ).1 h).2.1 i]

structure Arith : Prop where
  unifT : ∀ i, valuation k ((o.p i).pr (incA D (((D.mem u).A.T : ℕ) : D.host.E))) = valuation k ((o.q.1 : 𝒪[k]) : k)
  oneG : ∀ PP, valuation (G PP).k ((G PP).q.pr (incA D (((D.mem u).A.T : ℕ) : D.host.E)) - 1) < 1
  unifG : ∀ PP, valuation (G PP).k ((G PP).q.pr (incA D ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))) =
    valuation (G PP).k (((G PP).S.ϖ : (G PP).kˣ) : (G PP).k)
  under : ∀ PP : a.c.Pg, (G PP).q.v = PP.1.under (𝓞 D.host.F)
  tame : ∀ v, GlobalTheory.FinPl.Tame D v
  unr : ∀ v, v ∉ a.c.S → CharUnramAt D a.c.η v ∧ ∀ j, 1 ≤ j → j ≤ D.R.m → CharUnramAt D (a.c.μ j) v
  pos : ∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef
  lz : a.Lz.SigOK ∧ a.Lz.IsPosDef

theorem Arith.of_local
    (unifT : ∀ i, valuation k ((o.p i).pr (incA D (((D.mem u).A.T : ℕ) : D.host.E))) = valuation k ((o.q.1 : 𝒪[k]) : k))
    (oneG : ∀ PP, valuation (G PP).k ((G PP).q.pr (incA D (((D.mem u).A.T : ℕ) : D.host.E)) - 1) < 1)
    (unifG : ∀ PP, valuation (G PP).k ((G PP).q.pr (incA D ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))) =
      valuation (G PP).k (((G PP).S.ϖ : (G PP).kˣ) : (G PP).k))
    (under : ∀ PP : a.c.Pg, (G PP).q.v = PP.1.under (𝓞 D.host.F))
    (unr : ∀ v, v ∉ a.c.S → CharUnramAt D a.c.η v ∧ ∀ j, 1 ≤ j → j ≤ D.R.m → CharUnramAt D (a.c.μ j) v)
    (lz : a.Lz.SigOK ∧ a.Lz.IsPosDef) : Arith o G :=
  ⟨unifT, oneG, unifG, under, GlobalTheory.FinPl.TamePlaces.tame D, unr, D.X_posDef, lz⟩

end GlobalTheory.SeeSaw

end
