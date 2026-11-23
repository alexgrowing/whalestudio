import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CharChange

open Formalism.IndefR.Bridge

section Gen

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}

def InRg (P : ClassPres ι S σ ρ J χ) (w : W) : Prop := ∃ x, P.coef x = w

theorem coef_injective (P : ClassPres ι S σ ρ J χ) : Function.Injective P.coef := by
  intro x x' h
  have : P.coef (x - x') = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.1 (P.coef_inj this)

def cinv (P : ClassPres ι S σ ρ J χ) : W → S.V := Function.invFun P.coef

theorem coef_cinv (P : ClassPres ι S σ ρ J χ) {w : W} (hw : InRg P w) : P.coef (cinv P w) = w :=
  Function.invFun_eq hw

theorem InRg.add {P : ClassPres ι S σ ρ J χ} {w w' : W} (h : InRg P w) (h' : InRg P w') : InRg P (w + w') := by
  obtain ⟨x, rfl⟩ := h; obtain ⟨x', rfl⟩ := h'; exact ⟨x + x', map_add _ _ _⟩

theorem InRg.zero (P : ClassPres ι S σ ρ J χ) : InRg P 0 := ⟨0, map_zero _⟩

theorem InRg.smul {P : ClassPres ι S σ ρ J χ} {w : W} {z : ℂ} (hz : ∃ b : K, σ b = z) (h : InRg P w) :
    InRg P (z • w) := by
  obtain ⟨x, rfl⟩ := h; obtain ⟨b, rfl⟩ := hz; exact ⟨b • x, map_smulₛₗ _ _ _⟩

theorem InRg.sum {P : ClassPres ι S σ ρ J χ} {α : Type} (s : Finset α) (w : α → W) (h : ∀ a ∈ s, InRg P (w a)) :
    InRg P (∑ a ∈ s, w a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using InRg.zero P
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem stabK_one' {y : G} : stabK ι (1 : stab ι J y) = 1 := by
  apply Subtype.ext; simp [stabK]

theorem stabK_mul' {y : G} (a b : stab ι J y) : stabK ι (a * b) = stabK ι b * stabK ι a := by
  apply Subtype.ext
  simp only [stabK, Subgroup.coe_mul, map_mul, Subgroup.coe_inv, InvMemClass.coe_inv]
  group

variable (P : ClassPres ι S σ ρ J χ) (χ' : J →* ℂˣ) (hχ' : ∀ k, ∃ b : K, σ b = (χ' k : ℂ))
  (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x))

def rhoF (c : S.Cl) (g : S.Gam c) (x : S.V) : W :=
  (χ' (stabK ι (P.stabI c g)) : ℂ) • ρ (P.stabI c g : Γ) (P.coef x)

include hχ' hρ in
theorem rhoF_rg (c : S.Cl) (g : S.Gam c) (x : S.V) : InRg P (rhoF P χ' c g x) := by
  obtain ⟨x', hx'⟩ := hρ (P.stabI c g : Γ) x
  exact InRg.smul (hχ' _) ⟨x', hx'⟩

def rhoE (c : S.Cl) (g : S.Gam c) : Module.End K S.V where
  toFun x := cinv P (rhoF P χ' c g x)
  map_add' x x' := by
    apply coef_injective P
    rw [map_add, coef_cinv P (rhoF_rg P χ' hχ' hρ _ _ _), coef_cinv P (rhoF_rg P χ' hχ' hρ _ _ _),
      coef_cinv P (rhoF_rg P χ' hχ' hρ _ _ _)]
    simp only [rhoF, map_add, smul_add]
  map_smul' b x := by
    apply coef_injective P
    rw [map_smulₛₗ, coef_cinv P (rhoF_rg P χ' hχ' hρ _ _ _), coef_cinv P (rhoF_rg P χ' hχ' hρ _ _ _)]
    simp only [rhoF, map_smulₛₗ, RingHom.id_apply, map_smul]
    rw [smul_comm]

theorem coef_rhoE (c : S.Cl) (g : S.Gam c) (x : S.V) :
    P.coef (rhoE P χ' hχ' hρ c g x) = rhoF P χ' c g x :=
  coef_cinv P (rhoF_rg P χ' hχ' hρ _ _ _)

def rhoNew (c : S.Cl) : S.Gam c →* Module.End K S.V where
  toFun := rhoE P χ' hχ' hρ c
  map_one' := by
    apply LinearMap.ext; intro x
    apply coef_injective P
    rw [coef_rhoE]
    simp [rhoF, stabK_one']
  map_mul' g g' := by
    apply LinearMap.ext; intro x
    apply coef_injective P
    rw [Module.End.mul_apply, coef_rhoE, coef_rhoE]
    simp only [rhoF, coef_rhoE, map_mul, stabK_mul', Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, map_smul,
      smul_smul, mul_comm]

def presNew : ClassPres ι ({ S with ρ := rhoNew P χ' hχ' hρ } : CSD K) σ ρ J χ' where
  y := P.y
  reps := P.reps
  stabI := P.stabI
  coef := P.coef
  coef_li := P.coef_li
  coef_span := P.coef_span
  coef_pair := P.coef_pair
  coef_act c g x := coef_rhoE P χ' hχ' hρ c g x

end Gen

section Tr

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable (P : ClassPres ι S σ ρ J χ)

theorem ext_add (f f' : S.Forms) :
    P.ext ((f + f' : S.Forms) : S.Cl → S.V) = P.ext (f : S.Cl → S.V) + P.ext (f' : S.Cl → S.V) :=
  P.extL.map_add f f'

theorem ext_smul (b : K) (f : S.Forms) :
    P.ext ((b • f : S.Forms) : S.Cl → S.V) = σ b • P.ext (f : S.Cl → S.V) :=
  P.extL.map_smulₛₗ b f

theorem ext_inj {f f' : S.Forms} (h : P.ext (f : S.Cl → S.V) = P.ext (f' : S.Cl → S.V)) : f = f' := by
  apply Subtype.ext; funext c
  apply coef_injective P
  rw [← P.ext_rep, ← P.ext_rep, h]

theorem ext_rg (hχ : ∀ k, ∃ b : K, σ b = (χ k : ℂ)) (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x))
    (f : S.Cl → S.V) (h : G) : InRg P (P.ext f h) := by
  obtain ⟨x', hx'⟩ := hρ (P.decG h) (f (P.decC h))
  exact InRg.smul (hχ _) ⟨x', hx'⟩

def Keeps (T : (G → W) →ₗ[ℂ] (G → W)) : Prop :=
  ∀ F ∈ AdForms ι ρ J χ, (∀ h, InRg P (F h)) → T F ∈ AdForms ι ρ J χ ∧ ∀ h, InRg P (T F h)

variable (hχ : ∀ k, ∃ b : K, σ b = (χ k : ℂ)) (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x))
  {T : (G → W) →ₗ[ℂ] (G → W)} (hT : Keeps P T)

include hχ hρ hT in
theorem keeps_ext (f : S.Forms) :
    T (P.ext (f : S.Cl → S.V)) ∈ AdForms ι ρ J χ ∧ ∀ h, InRg P (T (P.ext (f : S.Cl → S.V)) h) :=
  hT _ (ClassPres.extMem_holds P f) (ext_rg P hχ hρ _)

def trForm (f : S.Forms) : S.Forms :=
  ⟨fun c => cinv P (T (P.ext (f : S.Cl → S.V)) (P.y c)), by
    intro c g
    apply coef_injective P
    rw [P.coef_act, coef_cinv P ((keeps_ext P hχ hρ hT f).2 _)]
    exact P.adForms_fixed (keeps_ext P hχ hρ hT f).1 c g⟩

theorem ext_trForm (f : S.Forms) :
    P.ext ((trForm P hχ hρ hT f : S.Forms) : S.Cl → S.V) = T (P.ext (f : S.Cl → S.V)) :=
  P.adForms_ext (ClassPres.extMem_holds P _) (keeps_ext P hχ hρ hT f).1 fun c => by
    rw [P.ext_rep]; exact coef_cinv P ((keeps_ext P hχ hρ hT f).2 _)

def trE : Module.End K S.Forms where
  toFun := trForm P hχ hρ hT
  map_add' f f' := ext_inj P (by rw [ext_add, ext_trForm, ext_trForm, ext_trForm, ext_add, map_add])
  map_smul' b f := ext_inj P (by
    rw [ext_smul, ext_trForm, ext_trForm, ext_smul, RingHom.id_apply, map_smul])

theorem ext_trE (f : S.Forms) :
    P.ext ((trE P hχ hρ hT f : S.Forms) : S.Cl → S.V) = T (P.ext (f : S.Cl → S.V)) :=
  ext_trForm P hχ hρ hT f

end Tr

section Ops

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}

def g0L {Q : Subgroup G} (ch : Q →* ℂˣ) (κ : Q) : (G → W) →ₗ[ℂ] (G → W) where
  toFun := g0Act ch κ
  map_add' F F' := by funext h; simp [g0Act, smul_add]
  map_smul' a F := by funext h; simp only [g0Act, Pi.smul_apply, RingHom.id_apply]; rw [smul_comm]

theorem reductionGroupAction_mul {Q : Subgroup G} (ch : Q →* ℂˣ) (κ κ' : Q) (F : G → W) :
    g0Act ch κ (g0Act ch κ' F) = g0Act ch (κ * κ') F := by
  funext h
  simp only [g0Act, Subgroup.coe_mul, mul_assoc, smul_smul, map_mul, _root_.mul_inv_rev, Units.val_mul, mul_comm]

theorem reductionGroupAction_one {Q : Subgroup G} (ch : Q →* ℂˣ) (F : G → W) : g0Act ch (1 : Q) F = F := by
  funext h; simp [g0Act]

theorem reductionGroupAction_mem_adelicForms {Q : Subgroup G} {G0 : Type} [Group G0] (red : Q →* G0) (hJ : J ≤ Q)
    (hker : ∀ q : Q, red q = 1 ↔ (q : G) ∈ J) (ch : Q →* ℂˣ) (hch : ∀ k : J, ch ⟨k, hJ k.2⟩ = χ k)
    (κ : Q) {F : G → W} (hF : F ∈ AdForms ι ρ J χ) : g0Act ch κ F ∈ AdForms ι ρ J χ := by
  have hF' : ∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * k) = (χ k : ℂ) • ρ γ (F h) := hF
  intro γ h k
  let q : Q := κ⁻¹ * ⟨k, hJ k.2⟩ * κ
  have hq : (q : G) ∈ J := by
    rw [← hker]
    have : red ⟨k, hJ k.2⟩ = 1 := (hker _).2 k.2
    simp [q, map_mul, this]
  let k' : J := ⟨q, hq⟩
  have e : ι γ * h * (k : G) * (κ : G) = ι γ * (h * κ) * (k' : G) := by
    simp only [k', q, Subgroup.coe_mul, Subgroup.coe_inv]; group
  have hc : χ k' = χ k := by
    rw [← hch k', ← hch k]
    have : (⟨(k' : G), hJ k'.2⟩ : Q) = q := rfl
    rw [this]
    simp only [q, map_mul, map_inv]
    rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  show (((ch κ)⁻¹ : ℂˣ) : ℂ) • F (ι γ * h * k * κ) = (χ k : ℂ) • ρ γ ((((ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * κ))
  rw [e, hF', hc, map_smul, smul_comm]

theorem reductionGroupAction_eq_of_same_reduction {Q : Subgroup G} {G0 : Type} [Group G0] (red : Q →* G0) (hJ : J ≤ Q)
    (hker : ∀ q : Q, red q = 1 ↔ (q : G) ∈ J) (ch : Q →* ℂˣ) (hch : ∀ k : J, ch ⟨k, hJ k.2⟩ = χ k)
    {κ κ' : Q} (hκ : red κ = red κ') {F : G → W} (hF : F ∈ AdForms ι ρ J χ) :
    g0Act ch κ F = g0Act ch κ' F := by
  funext h
  exact lift_independent_action_holds ι ρ J χ red ch hJ hker hch κ κ' hκ F hF h

def dcL (A : Finset G) : (G → W) →ₗ[ℂ] (G → W) where
  toFun := dcOp A
  map_add' F F' := by funext h; simp [dcOp, Finset.sum_add_distrib]
  map_smul' a F := by funext h; simp [dcOp, Finset.smul_sum]

end Ops

section DC

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {J : Subgroup G} {x : G} {A : Finset G}

theorem mul_mem_dc (hDC : IsDC J x A) {u : G} (hu : u ∈ J) {a : G} (ha : a ∈ A) :
    ∃ k₁ k₂ : J, u * a = (k₁ : G) * x * k₂ := by
  obtain ⟨j₁, j₂, e⟩ := hDC.1 a ha
  exact ⟨⟨u, hu⟩ * j₁, j₂, by rw [e]; simp [mul_assoc]⟩

open Classical in

def pick (hDC : IsDC J x A) {u : G} (hu : u ∈ J) (a : G) : G :=
  if ha : a ∈ A then (hDC.2 (u * a) (mul_mem_dc hDC hu ha)).exists.choose else a

theorem pick_spec (hDC : IsDC J x A) {u : G} (hu : u ∈ J) {a : G} (ha : a ∈ A) :
    pick hDC hu a ∈ A ∧ (pick hDC hu a)⁻¹ * (u * a) ∈ J := by
  unfold pick; rw [dif_pos ha]
  exact (hDC.2 (u * a) (mul_mem_dc hDC hu ha)).exists.choose_spec

theorem pick_unique (hDC : IsDC J x A) {u : G} (hu : u ∈ J) {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (hab : b⁻¹ * (u * a) ∈ J) : pick hDC hu a = b :=
  (hDC.2 (u * a) (mul_mem_dc hDC hu ha)).unique (pick_spec hDC hu ha) ⟨hb, hab⟩

theorem pick_inv (hDC : IsDC J x A) {u : G} (hu : u ∈ J) {a : G} (ha : a ∈ A) :
    pick hDC (J.inv_mem hu) (pick hDC hu a) = a := by
  obtain ⟨h1, h2⟩ := pick_spec hDC hu ha
  refine pick_unique hDC _ h1 ha ?_
  have : a⁻¹ * (u⁻¹ * pick hDC hu a) = ((pick hDC hu a)⁻¹ * (u * a))⁻¹ := by group
  rw [this]; exact J.inv_mem h2

variable {χ : J →* ℂˣ} {ρ : Γ →* Module.End ℂ W}

theorem dcOp_mem (hDC : IsDC J x A) (Lc : Subgroup G) (hAL : ∀ a ∈ A, a ∈ Lc)
    (hsplit : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x)
    (hχL : ∀ k : J, (k : G) ∈ Lc → χ k = 1) {F : G → W} (hF : F ∈ AdForms ι ρ J χ) :
    dcOp A F ∈ AdForms ι ρ J χ := by
  have hF' : ∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * k) = (χ k : ℂ) • ρ γ (F h) := hF
  intro γ h k
  obtain ⟨k₁, hk₁, k₂, hk₂, hk₁L, hk, hcomm⟩ := hsplit k k.2
  have hχk : χ k = χ ⟨k₂, hk₂⟩ := by
    have e : k = ⟨k₁, hk₁⟩ * ⟨k₂, hk₂⟩ := Subtype.ext hk
    rw [e, map_mul, hχL ⟨k₁, hk₁⟩ hk₁L, one_mul]
  have term : ∀ a ∈ A, F (ι γ * h * k * a) = (χ k : ℂ) • ρ γ (F (h * pick hDC hk₁ a)) := by
    intro a ha
    obtain ⟨h1, h2⟩ := pick_spec hDC hk₁ ha
    set a' := pick hDC hk₁ a
    have hjL : a'⁻¹ * (k₁ * a) ∈ Lc :=
      Lc.mul_mem (Lc.inv_mem (hAL _ h1)) (Lc.mul_mem hk₁L (hAL _ ha))
    let j : J := ⟨a'⁻¹ * (k₁ * a), h2⟩
    have e : ι γ * h * (k : G) * a = ι γ * (h * a') * ((j * ⟨k₂, hk₂⟩ : J) : G) := by
      have hc : k₂ * a = a * k₂ := hcomm a (hAL a ha)
      simp only [j, Subgroup.coe_mul]
      rw [hk]
      calc ι γ * h * (k₁ * k₂) * a = ι γ * h * k₁ * (k₂ * a) := by group
        _ = ι γ * h * k₁ * (a * k₂) := by rw [hc]
        _ = _ := by group
    rw [e, hF', map_mul, hχL j hjL, one_mul, hχk]
  show ∑ a ∈ A, F (ι γ * h * k * a) = (χ k : ℂ) • ρ γ (∑ a ∈ A, F (h * a))
  rw [Finset.sum_congr rfl term, map_sum, Finset.smul_sum]
  exact Finset.sum_nbij' (pick hDC hk₁) (pick hDC (J.inv_mem hk₁))
    (fun a ha => (pick_spec hDC hk₁ ha).1) (fun a ha => (pick_spec hDC _ ha).1)
    (fun a ha => pick_inv hDC hk₁ ha)
    (fun a ha => by
      have := pick_inv hDC (J.inv_mem hk₁) ha
      simpa only [inv_inv] using this)
    (fun a ha => rfl)

end DC

section Main

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable (P : ClassPres ι S σ ρ J χ) (hχ : ∀ k, ∃ b : K, σ b = (χ k : ℂ))
  (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x))
  {Q : Subgroup G} {G0 : Type} [Group G0] (red : Q →* G0) (hsurj : Function.Surjective red) (hJ : J ≤ Q)
  (hker : ∀ q : Q, red q = 1 ↔ (q : G) ∈ J) (ch : Q →* ℂˣ) (hch : ∀ k : J, ch ⟨k, hJ k.2⟩ = χ k)
  (hchK : ∀ q, ∃ b : K, σ b = (ch q : ℂ))

include hker hch hchK in
theorem classPresentation_reductionAction_preserved (κ : Q) : Keeps P (g0L (W := W) ch κ) := by
  intro F hF hv
  refine ⟨reductionGroupAction_mem_adelicForms red hJ hker ch hch κ hF, fun h => ?_⟩
  show InRg P ((((ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * κ))
  refine InRg.smul ?_ (hv _)
  rw [← map_inv]; exact hchK _

def actNew : Representation K G0 S.Forms where
  toFun g := trE P hχ hρ (classPresentation_reductionAction_preserved P red hJ hker ch hch hchK (hsurj g).choose)
  map_one' := by
    apply LinearMap.ext; intro f
    apply ext_inj P
    rw [ext_trE, Module.End.one_apply]
    show g0Act ch _ _ = _
    rw [reductionGroupAction_eq_of_same_reduction red hJ hker ch hch (κ' := 1) (by rw [(hsurj 1).choose_spec, map_one])
      (ClassPres.extMem_holds P f), reductionGroupAction_one]
  map_mul' g g' := by
    apply LinearMap.ext; intro f
    apply ext_inj P
    rw [Module.End.mul_apply, ext_trE, ext_trE, ext_trE]
    show g0Act ch _ _ = g0Act ch _ (g0Act ch _ _)
    rw [reductionGroupAction_mul, reductionGroupAction_eq_of_same_reduction red hJ hker ch hch (κ' := (hsurj g).choose * (hsurj g').choose)
      (by rw [map_mul, (hsurj g).choose_spec, (hsurj g').choose_spec, (hsurj (g * g')).choose_spec])
      (ClassPres.extMem_holds P f)]

theorem actNew_eq (g : G0) (κ : Q) (hκ : red κ = g) (f : S.Forms) :
    P.ext ((actNew P hχ hρ red hsurj hJ hker ch hch hchK g f : S.Forms) : S.Cl → S.V) =
      g0Act ch κ (P.ext (f : S.Cl → S.V)) := by
  show P.ext ((trE P hχ hρ _ f : S.Forms) : S.Cl → S.V) = _
  rw [ext_trE]
  show g0Act ch _ _ = _
  exact reductionGroupAction_eq_of_same_reduction red hJ hker ch hch (by rw [(hsurj g).choose_spec, hκ]) (ClassPres.extMem_holds P f)

def actTieNew : ActTie ι P Q ch (actNew P hχ hρ red hsurj hJ hker ch hch hchK) where
  red := red
  red_surj := hsurj
  red_ker := hker
  act_eq g κ hκ f := actNew_eq P hχ hρ red hsurj hJ hker ch hch hchK g κ hκ f

end Main

section Hecke

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable (P : ClassPres ι S σ ρ J χ) (hχ : ∀ k, ∃ b : K, σ b = (χ k : ℂ))
  (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x))
  {S₀ : CSD K} {χ₀ : J →* ℂˣ} {P₀ : ClassPres ι S₀ σ ρ J χ₀} {I : Type} {op : I → Module.End K S₀.Forms}
  {inR : I → Prop} {isT isLoc : I → G → Prop} (H : HeckeTie ι P₀ op inR isT isLoc)
  (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
    (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
    ∀ k : J, (k : G) ∈ Lc → χ k = 1)

include hloc in
theorem keeps_dc (i : I) (hi : inR i) : Keeps P (dcL (W := W) (H.hA i)) := by
  obtain ⟨Lc, hL1, hL2, hL3⟩ := hloc i hi
  intro F hF hv
  refine ⟨dcOp_mem (H.hDC i hi) Lc (fun a ha => hL1 _ (H.hA_loc i hi a ha)) hL2 hL3 hF, fun h => ?_⟩
  exact InRg.sum _ _ fun a _ => hv _

open Classical in

def opNew (one : I → Prop) (i : I) : Module.End K S.Forms :=
  if hi : inR i then trE P hχ hρ (keeps_dc P H hloc i hi) else if one i then 1 else 0

def heckeNew (one : I → Prop) : HeckeTie ι P (opNew P hχ hρ H hloc one) inR isT isLoc where
  hx := H.hx
  hA := H.hA
  hx_ok := H.hx_ok
  hA_loc := H.hA_loc
  chi_loc i hi k hk := by
    obtain ⟨Lc, hL1, _, hL3⟩ := hloc i hi
    exact hL3 k (hL1 _ hk)
  hDC := H.hDC
  op_eq i hi f := by
    unfold opNew
    rw [dif_pos hi, ext_trE]
    rfl

end Hecke

end GlobalTheory.CharChange

namespace GlobalTheory

open Formalism.IndefR.Bridge GlobalTheory.CharChange

end GlobalTheory
