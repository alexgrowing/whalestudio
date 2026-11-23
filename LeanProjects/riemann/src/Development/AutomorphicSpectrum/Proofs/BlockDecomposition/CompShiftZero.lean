import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

noncomputable section

namespace GlobalTheory.CompanionTheory.ReesUp

open GlobalTheory.CatH (face toLast)

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F)

def comp (r : ℕ) {n : ℕ} (c : Cn Φ.rees n) : Cn (Φ.S r).fn n :=
  fun s => (show Φ.Pr (s.obj (Fin.last n)) from c s) r

def asm {n : ℕ} (x : ∀ r, Cn (Φ.S r).fn n) : Cn Φ.rees n :=
  fun s => (show Φ.Pr (s.obj (Fin.last n)) from fun r => x r s)

theorem ext_comp {n : ℕ} {a b : Cn Φ.rees n} (h : ∀ r, comp Φ r a = comp Φ r b) : a = b :=
  funext fun s => funext fun r => congrFun (h r) s

theorem comp_d (r n : ℕ) (c : Cn Φ.rees n) :
    comp Φ r (d Φ.rees n c) = d (Φ.S r).fn n (comp Φ r c) := by
  funext s
  let e : Φ.rees.obj (s.obj (Fin.last (n + 1))) →+ (Φ.S r).fn.obj (s.obj (Fin.last (n + 1))) :=
    Pi.evalAddMonoidHom (fun r => (Φ.S r).S (s.obj (Fin.last (n + 1)))) r
  change e (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.rees.map (toLast i s)).hom (c (face i s))) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ((Φ.S r).fn.map (toLast i s)).hom (comp Φ r c (face i s))
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  rfl

theorem d_eq_zero_iff (n : ℕ) (c : Cn Φ.rees n) :
    d Φ.rees n c = 0 ↔ ∀ r, d (Φ.S r).fn n (comp Φ r c) = 0 := by
  constructor
  · intro h r
    rw [← comp_d, h]; rfl
  · intro h
    exact ext_comp Φ fun r => by rw [comp_d, h r]; rfl

theorem mem_B_iff (j : ℕ) (a : Cn Φ.rees j) :
    a ∈ (cx Φ.rees).B j ↔ ∀ r, comp Φ r a ∈ (cx (Φ.S r).fn).B j := by
  cases j with
  | zero =>
    constructor
    · intro h r
      have h0 : a = 0 := h
      rw [h0]
      exact Submodule.zero_mem _
    · intro h
      have : a = 0 := ext_comp Φ fun r => h r
      rw [this]
      exact Submodule.zero_mem _
  | succ j =>
    constructor
    · rintro ⟨b, rfl⟩ r
      exact ⟨comp Φ r b, (comp_d Φ r j b).symm⟩
    · intro h
      have h' : ∀ r, ∃ b, d (Φ.S r).fn j b = comp Φ r a := h
      choose b hb using h'
      exact ⟨asm Φ b, ext_comp Φ fun r => by
        change comp Φ r (d Φ.rees j (asm Φ b)) = _
        rw [comp_d]
        exact hb r⟩

theorem pull_cls (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) (j : ℕ) (a : Cn F j) (ha : (cx F).d j a = 0)
    (hb : (cx (G ⋙ F)).d j ((Mor.restrict F G).pullC j a) = 0) :
    (Mor.restrict F G).pull j ((cx F).cls a ha) = (cx (G ⋙ F)).cls ((Mor.restrict F G).pullC j a) hb := rfl

theorem pull_cocycle (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) (j : ℕ) (a : Cn F j) (ha : d F j a = 0) :
    (cx (G ⋙ F)).d j ((Mor.restrict F G).pullC j a) = 0 := by
  change d (G ⋙ F) j _ = 0
  rw [(Mor.restrict F G).d_pullC j a, ha, map_zero]

theorem inj_iff (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) (j : ℕ) :
    InjUpTo (1 : R) ((Mor.restrict F G).pull j) ↔
      ∀ a, d F j a = 0 → (Mor.restrict F G).pullC j a ∈ (cx (G ⋙ F)).B j → a ∈ (cx F).B j := by
  constructor
  · intro h a ha hb
    have := h ((cx F).cls a ha) (by
      rw [pull_cls F G j a ha (pull_cocycle F G j a ha)]
      exact ((CrystallineSemistableComparison.P.cls_surj _ j).2.1 _ _).2 hb)
    rw [one_smul] at this
    exact ((CrystallineSemistableComparison.P.cls_surj _ j).2.1 _ _).1 this
  · intro h x hx
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 x
    rw [one_smul]
    rw [pull_cls F G j a ha (pull_cocycle F G j a ha)] at hx
    exact ((CrystallineSemistableComparison.P.cls_surj _ j).2.1 _ _).2 (h a ha (((CrystallineSemistableComparison.P.cls_surj _ j).2.1 _ _).1 hx))

theorem surj_iff (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) (j : ℕ) :
    SurjUpTo (1 : R) ((Mor.restrict F G).pull j) ↔
      ∀ b, d (G ⋙ F) j b = 0 → ∃ a, d F j a = 0 ∧ (Mor.restrict F G).pullC j a - b ∈ (cx (G ⋙ F)).B j := by
  constructor
  · intro h b hb
    obtain ⟨x, hx⟩ := h ((cx (G ⋙ F)).cls b hb)
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 x
    rw [one_smul, pull_cls F G j a ha (pull_cocycle F G j a ha)] at hx
    exact ⟨a, ha, ((CrystallineSemistableComparison.P.cls_surj _ j).2.2.1 _ _ _ _).1 hx⟩
  · intro h y
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 y
    obtain ⟨a, ha, hm⟩ := h b hb
    refine ⟨(cx F).cls a ha, ?_⟩
    rw [one_smul, pull_cls F G j a ha (pull_cocycle F G j a ha)]
    exact ((CrystallineSemistableComparison.P.cls_surj _ j).2.2.1 _ _ _ _).2 hm

theorem ri_one (G : C' ⥤ C) (n : ℕ) (h : ∀ r, RI 1 n (Φ.S r).fn G) : RI 1 n Φ.rees G := by
  intro j hj
  refine ⟨(inj_iff _ _ _).2 fun a ha hb => ?_, (surj_iff _ _ _).2 fun b hb => ?_⟩
  · refine (mem_B_iff Φ j a).2 fun r => ?_
    exact (inj_iff _ _ _).1 (h r j hj).1 _ ((d_eq_zero_iff Φ j a).1 ha r)
      ((mem_B_iff (Φ.comap G) j _).1 hb r)
  · have hb' := (d_eq_zero_iff (Φ.comap G) j b).1 hb
    have := fun r => (surj_iff _ G j).1 (h r j hj).2 _ (hb' r)
    choose a ha hm using this
    exact ⟨asm Φ a, (d_eq_zero_iff Φ j _).2 ha, (mem_B_iff (Φ.comap G) j _).2 fun r => hm r⟩

def cv {T : C} (x : Φ.rees.obj T) (r : ℕ) : (Φ.S r).fn.obj T := (show Φ.Pr T from x) r

theorem rees_ext {T : C} {x y : Φ.rees.obj T} (h : ∀ r, (cv Φ x r).1 = (cv Φ y r).1) : x = y :=
  funext fun r => Subtype.ext (h r)

theorem cv_map {T T' : C} (φ : T ⟶ T') (x : Φ.rees.obj T) (r : ℕ) :
    (cv Φ ((Φ.rees.map φ).hom x) r).1 = (F.map φ).hom (cv Φ x r).1 := rfl

theorem cv_sub {T : C} (x y : Φ.rees.obj T) (r : ℕ) :
    (cv Φ (x - y) r).1 = (cv Φ x r).1 - (cv Φ y r).1 := rfl

theorem cv_X_zero {T : C} (x : Φ.rees.obj T) : (cv Φ ((X : ℤ[X]) • x) 0).1 = 0 :=
  congrArg Subtype.val (Flt.X_smul_zero Φ T x)

theorem cv_X_succ {T : C} (x : Φ.rees.obj T) (r : ℕ) :
    (cv Φ ((X : ℤ[X]) • x) (r + 1)).1 = Φ.μ • (cv Φ x r).1 := Flt.X_smul_succ Φ T x r

def shiftV {T : C} (m : ∀ r, (Φ.S (r + 1)).S T) : Φ.rees.obj T :=
  show Φ.Pr T from fun r => match r with
    | 0 => 0
    | r + 1 => m r

theorem cv_shift_zero {T : C} (m : ∀ r, (Φ.S (r + 1)).S T) : (cv Φ (shiftV Φ m) 0).1 = 0 := rfl

theorem cv_shift_succ {T : C} (m : ∀ r, (Φ.S (r + 1)).S T) (r : ℕ) :
    (cv Φ (shiftV Φ m) (r + 1)).1 = (m r).1 := rfl

def shiftC {n : ℕ} (m : ∀ r, Cn (Φ.S (r + 1)).fn n) : Cn Φ.rees n :=
  fun s => shiftV Φ fun r => m r s

theorem comp_shift_zero {n : ℕ} (m : ∀ r, Cn (Φ.S (r + 1)).fn n) : comp Φ 0 (shiftC Φ m) = 0 := rfl

theorem comp_shift_succ {n : ℕ} (m : ∀ r, Cn (Φ.S (r + 1)).fn n) (r : ℕ) :
    comp Φ (r + 1) (shiftC Φ m) = m r := rfl

theorem comp_X_zero {n : ℕ} (y : Cn Φ.rees n) : comp Φ 0 ((X : ℤ[X]) • y) = 0 :=
  funext fun s => Flt.X_smul_zero Φ _ (y s)

theorem comp_X_succ {n : ℕ} (y : Cn Φ.rees n) (r : ℕ) (s : ComposableArrows C n) :
    (comp Φ (r + 1) ((X : ℤ[X]) • y) s).1 = Φ.μ • (comp Φ r y s).1 :=
  Flt.X_smul_succ Φ _ (y s) r

def up (ξ : R) (hξ : ∀ r T x, x ∈ (Φ.S r).S T → ξ • x ∈ (Φ.S (r + 1)).S T) (r : ℕ) :
    (Φ.S r).fn ⟶ (Φ.S (r + 1)).fn where
  app T := ModuleCat.ofHom ((ξ • (LinearMap.id : F.obj T →ₗ[R] F.obj T)).restrict fun x hx => hξ r T x hx)
  naturality T T' φ := by
    ext x
    exact Subtype.ext (map_smul (F.map φ).hom ξ x.1).symm

theorem d_shift {μ' ξ : R} (hμ : Φ.μ = μ' * ξ)
    (hξ : ∀ r T x, x ∈ (Φ.S r).S T → ξ • x ∈ (Φ.S (r + 1)).S T) {n : ℕ} (y : Cn Φ.rees (n + 1))
    (x : ∀ r, Cn (Φ.S r).fn n) (hx : ∀ r, d (Φ.S r).fn n (x r) = μ' • comp Φ r y) :
    d Φ.rees n (shiftC Φ fun r => (Mor.ofNatTrans (up Φ ξ hξ r)).pullC n (x r)) = (X : ℤ[X]) • y := by
  refine ext_comp Φ fun r => ?_
  rw [comp_d]
  cases r with
  | zero =>
    rw [comp_X_zero, comp_shift_zero]
    exact map_zero _
  | succ r =>
    rw [comp_shift_succ, (Mor.ofNatTrans (up Φ ξ hξ r)).d_pullC n (x r), hx r]
    funext s
    apply Subtype.ext
    rw [comp_X_succ]
    change ξ • (μ' • (comp Φ r y s).1) = _
    rw [hμ, mul_comm μ' ξ, mul_smul]

theorem comp_unAug (G : C' ⥤ C) (T : C) (x : Φ.rees.obj T) (r : ℕ) :
    comp ((Φ.comap G).comap (StructuredArrow.proj T G)) r (unAug Φ.rees G T x) =
      unAug (Φ.S r).fn G T (cv Φ x r) := rfl

theorem X_smul_eq_zero {T : C} (x : Φ.rees.obj T) (h : ∀ r, Φ.μ • (cv Φ x r).1 = 0) :
    (X : ℤ[X]) • x = 0 :=
  rees_ext Φ fun r => by
    cases r with
    | zero => exact cv_X_zero Φ x
    | succ r => exact (cv_X_succ Φ x r).trans (h r)

theorem desc_rees (G : C' ⥤ C) (μ' ξ : R) (hμ : Φ.μ = μ' * ξ)
    (hξ : ∀ r T x, x ∈ (Φ.S r).S T → ξ • x ∈ (Φ.S (r + 1)).S T)
    (h : ∀ r, Desc μ' (Φ.S r).fn G) : Desc (X : ℤ[X]) Φ.rees G := by
  intro T
  let Ψ := (Φ.comap G).comap (StructuredArrow.proj T G)
  have hξ' : ∀ r T x, x ∈ (Ψ.S r).S T → ξ • x ∈ (Ψ.S (r + 1)).S T := fun r T' x hx => hξ r _ x hx
  have hμ' : Ψ.μ = μ' * ξ := hμ
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · exact (d_eq_zero_iff Ψ 0 _).2 fun r => (h r T).1 (cv Φ x r)
  · refine X_smul_eq_zero Φ x fun r => ?_
    have h0 : μ' • cv Φ x r = 0 := (h r T).2.1 (cv Φ x r) (by
      rw [← comp_unAug Φ G T x r, hx]; rfl)
    have h1 : μ' • (cv Φ x r).1 = 0 := congrArg Subtype.val h0
    rw [hμ, mul_comm μ' ξ, mul_smul, h1, smul_zero]
  · have hy' := (d_eq_zero_iff Ψ 0 y).1 hy
    have := fun r => (h r T).2.2.1 (comp Ψ r y) (hy' r)
    choose z hz using this
    refine ⟨shiftV Φ fun r => ⟨ξ • (z r).1, hξ r T _ (z r).2⟩, ext_comp Ψ fun r => ?_⟩
    cases r with
    | zero =>
      rw [comp_X_zero Ψ]
      funext s
      exact Subtype.ext (map_zero (F.map (s.obj (Fin.last 0)).hom).hom)
    | succ r =>
      funext s
      apply Subtype.ext
      rw [comp_X_succ Ψ]
      have v : (F.map (s.obj (Fin.last 0)).hom).hom (z r).1 = μ' • (comp Ψ r y s).1 :=
        congrArg Subtype.val (congrFun (hz r) s)
      change (F.map (s.obj (Fin.last 0)).hom).hom (ξ • (z r).1) = _
      rw [map_smul, v, hμ', mul_comm μ' ξ, mul_smul]
  · have hy' := (d_eq_zero_iff Ψ (n + 1) y).1 hy
    have := fun r => (h r T).2.2.2 n (comp Ψ r y) (hy' r)
    choose x hx using this
    exact ⟨_, d_shift Ψ hμ' hξ' y x hx⟩

theorem acyc_rees {T T' : C} (i : T ⟶ T') (g : T' ⟶ T') (h : Φ.FAcyc i g) :
    Acyc1 (X : ℤ[X]) (Φ.rees.map i).hom (Φ.rees.map g).hom := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x => ?_⟩
  · refine X_smul_eq_zero Φ x fun r => ?_
    have : (cv Φ x r).1 = 0 := h1 (by
      have e : (cv Φ ((Φ.rees.map i).hom x) r).1 = (cv Φ (0 : Φ.rees.obj T') r).1 := by rw [hx]
      rw [cv_map] at e
      exact e.trans (map_zero (F.map i).hom).symm)
    rw [this, smul_zero]
  · have := fun r => h2 r (cv Φ x r).1 (cv Φ x r).2 (by
      have e : (cv Φ ((Φ.rees.map g).hom x) r).1 = (cv Φ x r).1 := by rw [hx]
      rwa [cv_map] at e)
    choose m hm hm' using this
    refine ⟨shiftV Φ fun r => ⟨m r, hm r⟩, rees_ext Φ fun r => ?_⟩
    rw [cv_map]
    cases r with
    | zero =>
      rw [cv_X_zero, cv_shift_zero]
      exact map_zero _
    | succ r =>
      rw [cv_X_succ, cv_shift_succ]
      exact hm' r
  · have := fun r => h3 r (cv Φ x r).1 (cv Φ x r).2
    choose y hy hy' using this
    refine ⟨shiftV Φ fun r => ⟨y r, hy r⟩, rees_ext Φ fun r => ?_⟩
    rw [cv_sub, cv_map]
    cases r with
    | zero =>
      rw [cv_X_zero, cv_shift_zero, map_zero, sub_zero]
    | succ r =>
      rw [cv_X_succ, cv_shift_succ]
      exact hy' r

theorem main {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (n : ℕ) :
    ((∀ r, RI 1 n (Φ.S r).fn G) → RI 1 n Φ.rees G) ∧
    (∀ μ' ξ : R, Φ.μ = μ' * ξ → (∀ r T x, x ∈ (Φ.S r).S T → ξ • x ∈ (Φ.S (r + 1)).S T) →
      (∀ r, Desc μ' (Φ.S r).fn G) → Desc (X : ℤ[X]) Φ.rees G) ∧
    ∀ {T T' : C} (i : T ⟶ T') (g : T' ⟶ T'), Φ.FAcyc i g →
      Acyc1 (X : ℤ[X]) (Φ.rees.map i).hom (Φ.rees.map g).hom :=
  ⟨ri_one Φ G n, fun μ' ξ hμ hξ h => desc_rees Φ G μ' ξ hμ hξ h, fun i g h => acyc_rees Φ i g h⟩

end GlobalTheory.CompanionTheory.ReesUp
