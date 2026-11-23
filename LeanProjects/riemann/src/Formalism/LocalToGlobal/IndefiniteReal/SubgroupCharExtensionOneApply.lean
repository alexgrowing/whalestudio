import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Formalism.LocalToGlobal.Divisibility.DefGroup

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta
open scoped TensorProduct

namespace Formalism.IndefR.Lev

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev EAf (D : D7) : Type := D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F

def swapAE (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →+* EAf D :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom

variable {D : D7}

def finE (V : HSp D) : GA D V →* GL (Fin V.rank) (EAf D) :=
  (Formalism.UG.bc (swapAE D)).comp (finHom V)

def levA (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) : Subgroup (GA D V) :=
  GfC V ⊓ K.comap (finE V)

inductive Frm
  | A
  | B
  deriving DecidableEq

def datY (n r t j : ℕ) (hr : r ≤ n) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ)
    (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (fr : Frm) :
    Formalism.L2.DIV.LevDat D.host.E ℂ n where
  r := r
  hr := hr
  t := t
  s := j
  Pg := Pg
  Q := Q
  P := if fr = Frm.B then P else P.conj
  cg := if fr = Frm.B then χ else fun c PP => (χ c PP)⁻¹
  xq := if fr = Frm.B then fun PP => (ξ PP)⁻¹ else ξ

def datW (r : ℕ) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ) (fr : Frm) : Formalism.L2.DIV.LevDat D.host.E ℂ r where
  r := r
  hr := le_rfl
  t := 1
  s := 0
  Pg := Pg
  Q := ∅
  P := if fr = Frm.B then P else P.conj
  cg := fun _ _ => 1
  xq := fun _ => 1

def withP {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (P' : Formalism.L2.DIV.LevelP L.Pg L.r ℂ) : Formalism.L2.DIV.LevDat D.host.E ℂ n :=
  { L with P := P' }

def flagL {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : Formalism.L2.DIV.LevDat D.host.E ℂ n :=
  withP L (Formalism.L2.DIV.LevelP.full L.Pg L.r ℂ)

def flag1L {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : Formalism.L2.DIV.LevDat D.host.E ℂ n :=
  withP L (Formalism.L2.DIV.LevelP.triv L.Pg L.r ℂ)

def levG (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) : Subgroup (GA D V) :=
  levA V (Formalism.L2.DIV.lev D.sp.cm V.gram β L)

def levChi (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (κ : GA D V) : ℂ :=
  ((Formalism.L2.DIV.levFn β L (finE V κ) : ℂˣ) : ℂ)

def HasType (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (F : GA D V → ℂ) : Prop :=
  ∀ κ ∈ levG V β L, ∀ h, F (h * κ) = levChi V β L κ * F h

def KgQ (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (r : ℕ) (hr : r ≤ V.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    Subgroup (GL (Fin V.rank) (EAf D)) :=
  Formalism.L2.DIV.Kg D.sp.cm V.gram β Pg ⊓
    Formalism.L2.DIV.parLev D.sp.cm V.gram β
      { r := r, hr := hr, t := 1, s := 0, Pg := ∅, Q := Q, P := Formalism.L2.DIV.LevelP.triv ∅ r ℂ, cg := fun _ _ => 1, xq := fun _ => 1 }

def IsBaseFrame (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) :
    Prop :=
  Formalism.L2.DIV.IsFrame β Λ ∧ Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ ∧ 0 < N ∧
    (∀ x ∈ L0c D V, (N : D.host.E) • x ∈ Λ) ∧ ∀ x ∈ Λ, (N : D.host.E) • x ∈ L0c D V

def IsConjPl (PP PP' : Formalism.L2.DIV.Pl D.host.E) : Prop :=
  ∀ c ∈ PP.asIdeal, ∃ c' ∈ PP'.asIdeal, (c' : D.host.E) = star (c : D.host.E)

def IsTypePlaces (gp : Fin 2 → ℕ) (pb : Fin 2 → 𝓞 D.host.E) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  Formalism.L2.DIV.IsTypeDatum gp pb ∧ Pg = Formalism.L2.DIV.primesOf (pb 0 * pb 1)

def IsTwistPlaces (gp : Fin 2 → ℕ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  ∀ PP ∈ Q, (∃ q : ℕ, q.Prime ∧ Nat.card (Formalism.L2.DIV.kP PP) = q ∧ (q : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 ∧ ∀ i, q ≠ gp i) ∧
    ∀ PP' ∈ Q, ¬ IsConjPl PP PP'

def IsLevelLift (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (g0 : Formalism.L2.DIV.G0 L.Pg L.r)
    (κ : GA D V) : Prop :=
  κ ∈ GfC V ∧ finE V κ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L ∧ Formalism.L2.DIV.rTup β L (finE V κ) = g0

def IsLevelActionImage (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (g0 : Formalism.L2.DIV.G0 L.Pg L.r)
    (F F' : GA D V → ℂ) : Prop :=
  ∀ κ, IsLevelLift V β L g0 κ → ∀ h, F' h = (levChi V β (flagL L) κ)⁻¹ * F (h * κ)

open Classical in

def actG0 (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (g0 : Formalism.L2.DIV.G0 L.Pg L.r)
    (F : GA D V → ℂ) : GA D V → ℂ :=
  if hk : ∃ κ, IsLevelLift V β L g0 κ then
    fun h => (levChi V β (flagL L) hk.choose)⁻¹ * F (h * hk.choose)
  else 0

def IsPLevel (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (P : Formalism.L2.DIV.LevelP L.Pg L.r ℂ)
    (F : GA D V → ℂ) : Prop :=
  HasType V β (flag1L L) F ∧ ∀ p : P.H, actG0 V β L p.1 F = fun h => ((P.chi p : ℂˣ) : ℂ) * F h

def eAct (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (e : Formalism.L2.DIV.G0 L.Pg L.r →₀ ℂ) (F : GA D V → ℂ) : GA D V → ℂ :=
  fun h => e.sum fun g c => c * actG0 V β L g F h

def IsMinf {p q : ℕ} (m : Measure (UpqT p q)) : Prop :=
  m.IsHaarMeasure ∧ OmegaDensity m (minfDensity (p + q))

def IsMeasLevW (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D)))
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop) (μ : Measure (GA D V)) : Prop :=
  μ.IsHaarMeasure ∧
  AllSome (IsInfFam (D := D)) fun θ =>
  AllSome (fun A : ∀ ρ : D.what₂.Tau, Matrix (Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2) (Fin V.rank) ℂ =>
    ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2 * A ρ = gramAt D V ρ) fun A =>
  AllSome (fun m : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) => ∀ ρ, good ρ (m ρ)) fun m =>
  ∀ B : ∀ ρ : D.what₂.Tau, Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2), (∀ ρ, MeasurableSet (B ρ)) →
    μ {h | finE V h ∈ K ∧
        ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} = ∏ ρ, m ρ (B ρ)

def IsMeasLev (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) (μ : Measure (GA D V)) : Prop :=
  IsMeasLevW V K (fun _ m => IsMinf m) μ

def IsMeasLevDef (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) (μ : Measure (GA D V)) : Prop :=
  IsMeasLevW V K (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m) μ

def IsMeasFD (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  IsMeasLev V K μ ∧ IsFundamentalDomain (GQ V) 𝓕 μ

def IsL2Pairing (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) (F1 F2 : GA D V → ℂ) (c : ℂ) : Prop :=
  AllSome (IsMeasLev V K) fun μ => AllSome (fun 𝓕 => IsFundamentalDomain (GQ V) 𝓕 μ) fun 𝓕 =>
    IntegrableOn (fun h => F1 h * star (F2 h)) 𝓕 μ ∧ ∫ h in 𝓕, F1 h * star (F2 h) ∂μ = c

def IsDefiniteL2Pairing (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) (F1 F2 : GA D V → ℂ) (c : ℂ) : Prop :=
  AllSome (IsMeasLevDef V K) fun μ => AllSome (fun 𝓕 => IsFundamentalDomain (GQ V) 𝓕 μ) fun 𝓕 =>
    IntegrableOn (fun h => F1 h * star (F2 h)) 𝓕 μ ∧ ∫ h in 𝓕, F1 h * star (F2 h) ∂μ = c

def clSum (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) (F1 F2 : GL (Fin V.rank) (EAf D) → ℂ) : ℂ :=
  ∑ᶠ c : Formalism.L2.DIV.Cl D.sp.cm V.gram K, ((Nat.card (Formalism.L2.DIV.Gam c) : ℂ))⁻¹ *
    (F1 ((Formalism.L2.DIV.rep c : Formalism.L2.DIV.UA D.sp.cm V.gram) : GL (Fin V.rank) (EAf D)) *
      star (F2 ((Formalism.L2.DIV.rep c : Formalism.L2.DIV.UA D.sp.cm V.gram) : GL (Fin V.rank) (EAf D))))

def ClassSumOK (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) : Prop :=
  Finite (Formalism.L2.DIV.Cl D.sp.cm V.gram K) ∧ ∀ c : Formalism.L2.DIV.Cl D.sp.cm V.gram K, Finite (Formalism.L2.DIV.Gam c)

section API

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

theorem mem_levA {K : Subgroup (GL (Fin V.rank) (EAf D))} {κ : GA D V} : κ ∈ levA V K ↔ κ ∈ GfC V ∧ finE V κ ∈ K := Iff.rfl

theorem datY_B_eq_datX (r t m : ℕ) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ)
    (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) :
    datY (D := D) (r + m * t) r t m (Nat.le_add_right _ _) Pg Q P χ ξ Frm.B = Formalism.L2.DIV.datX r t m Pg Q P χ ξ := rfl

theorem datY_A_eq_datV (r t j : ℕ) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ)
    (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) :
    datY (D := D) (r + t) r t 1 (Nat.le_add_right _ _) Pg Q P (fun _ => χ j) ξ Frm.A =
      Formalism.L2.DIV.datV r t j Pg Q P χ ξ := rfl

theorem subgroupCharExtension_one_apply {G N : Type} [Group G] [MulOneClass N] (P : Subgroup G) (x : G) :
    Formalism.L2.DIV.ext1 P (⇑(1 : P →* N)) x = 1 := by
  unfold Formalism.L2.DIV.ext1
  split <;> rfl

theorem levFn_flag1 (x : GL (Fin V.rank) (EAf D)) :
    Formalism.L2.DIV.levFn β (flag1L L) x = Formalism.L2.DIV.levFn β (flagL L) x := by
  have h1 : Formalism.L2.DIV.ext1 (flag1L L).P.H (flag1L L).P.chi (Formalism.L2.DIV.rTup β (flag1L L) x) = 1 :=
    subgroupCharExtension_one_apply _ _
  have h2 : Formalism.L2.DIV.ext1 (flagL L).P.H (flagL L).P.chi (Formalism.L2.DIV.rTup β (flagL L) x) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold Formalism.L2.DIV.levFn
  rw [h1, h2] <;> rfl

theorem levChi_ne_zero (L' : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (κ : GA D V) : levChi V β L' κ ≠ 0 := by
  unfold levChi
  exact Units.ne_zero _

theorem levFn_flag_mul {x y : GL (Fin V.rank) (EAf D)} (hx : x ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L)
    (hy : y ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L) :
    Formalism.L2.DIV.levFn β (flagL L) (x * y) = Formalism.L2.DIV.levFn β (flagL L) x * Formalism.L2.DIV.levFn β (flagL L) y := by
  have hx' : x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) := by
    show x ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β (flagL L) ∧ Formalism.L2.DIV.rTup β (flagL L) x ∈ (flagL L).P.H
    exact ⟨hx, Subgroup.mem_top _⟩
  have hy' : y ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) := by
    show y ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β (flagL L) ∧ Formalism.L2.DIV.rTup β (flagL L) y ∈ (flagL L).P.H
    exact ⟨hy, Subgroup.mem_top _⟩
  have e : ∀ z (hz : z ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L)),
      Formalism.L2.DIV.levChar D.sp.cm V.gram β (flagL L) ⟨z, hz⟩ = Formalism.L2.DIV.levFn β (flagL L) z := by
    intro z hz
    unfold Formalism.L2.DIV.levChar
    simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← e x hx', ← e y hy', ← e (x * y) (Subgroup.mul_mem _ hx' hy'), ← map_mul] <;> rfl

theorem lift_div_mem {g0 : Formalism.L2.DIV.G0 L.Pg L.r} {κ κ' : GA D V} (hκ : IsLevelLift V β L g0 κ)
    (hκ' : IsLevelLift V β L g0 κ') : κ⁻¹ * κ' ∈ levG V β (flag1L L) := by
  obtain ⟨h1, h2, h3⟩ := hκ
  obtain ⟨h1', h2', h3'⟩ := hκ'
  refine mem_levA.mpr ⟨(GfC V).mul_mem ((GfC V).inv_mem h1) h1', ?_⟩
  rw [map_mul, map_inv]
  have hi : (finE V κ)⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L :=
    (Formalism.L2.DIV.parLev D.sp.cm V.gram β L).inv_mem h2
  have hr : Formalism.L2.DIV.rTup β L ((finE V κ)⁻¹ * finE V κ') = 1 := by
    rw [Formalism.L2.DIV.rTup_mul hi h2', Formalism.L2.DIV.rTup_inv h2, h3, h3', inv_mul_cancel]
  show (finE V κ)⁻¹ * finE V κ' ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β (flag1L L) ∧
    Formalism.L2.DIV.rTup β (flag1L L) ((finE V κ)⁻¹ * finE V κ') ∈ (flag1L L).P.H
  exact ⟨(Formalism.L2.DIV.parLev D.sp.cm V.gram β L).mul_mem hi h2', Subgroup.mem_bot.mpr hr⟩

theorem level_action_spec {g0 : Formalism.L2.DIV.G0 L.Pg L.r} {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F)
    (hex : ∃ κ, IsLevelLift V β L g0 κ) : IsLevelActionImage V β L g0 F (actG0 V β L g0 F) := by
  unfold IsLevelActionImage actG0
  intro κ hκ h
  simp only [dif_pos hex]
  have hκ0 : IsLevelLift V β L g0 hex.choose := hex.choose_spec
  have hd := lift_div_mem hκ0 hκ
  have hF1 := hF _ hd (h * hex.choose)
  rw [show h * hex.choose * (hex.choose⁻¹ * κ) = h * κ by rw [mul_assoc, mul_inv_cancel_left]] at hF1
  have hp : finE V (hex.choose⁻¹ * κ) ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := by
    rw [map_mul, map_inv]
    exact (Formalism.L2.DIV.parLev D.sp.cm V.gram β L).mul_mem
      ((Formalism.L2.DIV.parLev D.sp.cm V.gram β L).inv_mem hκ0.2.1) hκ.2.1
  have hm : levChi V β (flagL L) κ =
      levChi V β (flagL L) hex.choose * levChi V β (flagL L) (hex.choose⁻¹ * κ) := by
    calc levChi V β (flagL L) κ = levChi V β (flagL L) (hex.choose * (hex.choose⁻¹ * κ)) := by
          rw [mul_inv_cancel_left]
      _ = _ := by
          unfold levChi
          rw [map_mul (finE V) hex.choose (hex.choose⁻¹ * κ), levFn_flag_mul hκ0.2.1 hp, Units.val_mul]
  have h1 : levChi V β (flag1L L) (hex.choose⁻¹ * κ) = levChi V β (flagL L) (hex.choose⁻¹ * κ) := by
    unfold levChi
    rw [levFn_flag1]
  have n1 := levChi_ne_zero (V := V) (β := β) (flagL L) (hex.choose⁻¹ * κ)
  rw [hF1, h1, hm, mul_inv, mul_assoc, inv_mul_cancel_left₀ n1]

theorem levFn_withP (P : Formalism.L2.DIV.LevelP L.Pg L.r ℂ) (x : GL (Fin V.rank) (EAf D)) :
    Formalism.L2.DIV.levFn β (withP L P) x =
      Formalism.L2.DIV.ext1 P.H P.chi (Formalism.L2.DIV.rTup β L x) * Formalism.L2.DIV.levFn β (flagL L) x := by
  have h2 : Formalism.L2.DIV.ext1 (flagL L).P.H (flagL L).P.chi (Formalism.L2.DIV.rTup β (flagL L) x) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold Formalism.L2.DIV.levFn
  rw [h2, one_mul, mul_assoc] <;> rfl

theorem IsPLevel.hasType {P : Formalism.L2.DIV.LevelP L.Pg L.r ℂ} {F : GA D V → ℂ} (hF : IsPLevel V β L P F) :
    HasType V β (withP L P) F := by
  intro κ hκ h
  obtain ⟨hG, hl⟩ := mem_levA.mp hκ
  have hl' : finE V κ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L ∧
      Formalism.L2.DIV.rTup β L (finE V κ) ∈ P.H := hl
  have hlift : IsLevelLift V β L (Formalism.L2.DIV.rTup β L (finE V κ)) κ := And.intro hG (And.intro hl'.1 rfl)
  have hsp : actG0 V β L (Formalism.L2.DIV.rTup β L (finE V κ)) F h =
      (levChi V β (flagL L) κ)⁻¹ * F (h * κ) := level_action_spec hF.1 ⟨κ, hlift⟩ κ hlift h
  have hp : actG0 V β L (Formalism.L2.DIV.rTup β L (finE V κ)) F h =
      ((P.chi ⟨_, hl'.2⟩ : ℂˣ) : ℂ) * F h := congrFun (hF.2 ⟨_, hl'.2⟩) h
  rw [hp] at hsp
  have n := levChi_ne_zero (V := V) (β := β) (flagL L) κ
  have hc : levChi V β (withP L P) κ = ((P.chi ⟨_, hl'.2⟩ : ℂˣ) : ℂ) * levChi V β (flagL L) κ := by
    have he : Formalism.L2.DIV.ext1 P.H P.chi (Formalism.L2.DIV.rTup β L (finE V κ)) = P.chi ⟨_, hl'.2⟩ :=
      dif_pos hl'.2
    unfold levChi
    rw [levFn_withP, Units.val_mul, he]
  have key : F (h * κ) = levChi V β (flagL L) κ * (((P.chi ⟨_, hl'.2⟩ : ℂˣ) : ℂ) * F h) := by
    rw [hsp, ← mul_assoc, mul_inv_cancel₀ n, one_mul]
  rw [hc, key]
  ring

theorem level_action_unique {g0 : Formalism.L2.DIV.G0 L.Pg L.r} {F F₁ F₂ : GA D V → ℂ} (hex : ∃ κ, IsLevelLift V β L g0 κ)
    (h₁ : IsLevelActionImage V β L g0 F F₁) (h₂ : IsLevelActionImage V β L g0 F F₂) : F₁ = F₂ := by
  obtain ⟨κ, hκ⟩ := hex
  funext h
  rw [h₁ κ hκ h, h₂ κ hκ h]

end API

def toAfE (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) :
    Subgroup (GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
  K.comap (Formalism.UG.bc (swapAE D))

def levCharAfE (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    toAfE V (Formalism.L2.DIV.lev D.sp.cm V.gram β L) →* ℂˣ :=
  (Formalism.L2.DIV.levChar D.sp.cm V.gram β L).comp
    ((Formalism.UG.bc (swapAE D)).subgroupComap (Formalism.L2.DIV.lev D.sp.cm V.gram β L))

theorem finE_eq (V : HSp D) (h : GA D V) : finE V h = Formalism.UG.bc (swapAE D) (finHom V h) := rfl

theorem levCharAfE_flag (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (x : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) (h1 : x ∈ toAfE V (Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L)))
    (h2 : x ∈ toAfE V (Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L))) :
    levCharAfE V β (flag1L L) ⟨x, h1⟩ = levCharAfE V β (flagL L) ⟨x, h2⟩ := by
  show Formalism.L2.DIV.levFn β (flag1L L) (Formalism.UG.bc (swapAE D) x) = Formalism.L2.DIV.levFn β (flagL L) (Formalism.UG.bc (swapAE D) x)
  exact levFn_flag1 _

def LiftsExist (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) : Prop :=
  ∀ g0 : Formalism.L2.DIV.G0 L.Pg L.r, ∃ κ, IsLevelLift V β L g0 κ

end Formalism.IndefR.Lev

end
