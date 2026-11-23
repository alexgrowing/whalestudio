import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne

set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer

open CategoryTheory GlobalTheory.CatCoh

abbrev Tot (I : Type) (g : ℕ) : Type := (I → ℂ) × (Fin g → ℂ)

structure Fam (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] where

  V : Opens (I → ℂ)

  τ : Λ →+ ((I → ℂ) → Fin g → ℂ)
  hol : ∀ l, AnalyticOnNhd ℂ (τ l) V

def ellFam : Fam (Fin 1) 1 (ℤ × ℤ) where
  V := ⟨{z | 0 < (z 0).im}, isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply 0))⟩
  τ := { toFun := fun l z _ ↦ l.1 * z 0 + l.2
         map_zero' := by ext; simp
         map_add' := fun l m ↦ by ext; simp; ring }
  hol l := fun z _ ↦ by
    refine AnalyticAt.pi fun _ ↦ ?_
    change AnalyticAt ℂ (fun z : Fin 1 → ℂ ↦ (l.1 : ℂ) * z 0 + l.2) z
    exact (analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt z)).add
      analyticAt_const

theorem ellFam_nontrivial : (fun _ ↦ Complex.I) ∈ ellFam.V ∧
    ellFam.τ (1, 0) (fun _ ↦ Complex.I) = (fun _ ↦ Complex.I) ∧ ellFam.τ (0, 1) (fun _ ↦ Complex.I) = fun _ ↦ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · change (0 : ℝ) < Complex.I.im
    simp
  · funext i
    simp [ellFam]
  · funext i
    simp [ellFam]

theorem ellFam_free (l : ℤ × ℤ) (z : Fin 1 → ℂ) (hz : z ∈ ellFam.V) (h : ellFam.τ l z = 0) : l = 0 := by
  have hz' : 0 < (z 0).im := hz
  have h0 : ((l.1 : ℂ) * z 0 + l.2) = 0 := by
    have := congrFun h 0
    simpa [ellFam] using this
  have him : (l.1 : ℝ) * (z 0).im = 0 := by
    have := congrArg Complex.im h0
    simpa using this
  have h1 : l.1 = 0 := by
    have : (l.1 : ℝ) = 0 := (mul_eq_zero.1 him).resolve_right hz'.ne'
    exact_mod_cast this
  have h2 : l.2 = 0 := by
    rw [h1] at h0
    simpa using h0
  exact Prod.ext h1 h2

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]

def Fam.shift (F : Fam I g Λ) (l : Λ) (p : Tot I g) : Tot I g := (p.1, p.2 + F.τ l p.1)

theorem Fam.shift_zero (F : Fam I g Λ) (p : Tot I g) : F.shift 0 p = p := by
  simp [Fam.shift]

theorem Fam.shift_add (F : Fam I g Λ) (l m : Λ) (p : Tot I g) : F.shift (l + m) p = F.shift l (F.shift m p) := by
  simp only [Fam.shift, map_add, Pi.add_apply, Prod.mk.injEq, true_and]
  abel

theorem Fam.shift_analytic (F : Fam I g Λ) (l : Λ) {W : Set (Tot I g)} (h : ∀ p ∈ W, p.1 ∈ F.V) :
    AnalyticOnNhd ℂ (F.shift l) W := by
  intro p hp
  exact analyticAt_fst.prod (analyticAt_snd.add ((F.hol l p.1 (h p hp)).comp analyticAt_fst))

def dw {W : Opens (Tot I g)} (a : Fin g) : Derivation ℂ (Hol W) (Hol W) := Hol.der ((0, Pi.single a 1) : Tot I g)

def Step {W : Opens (Tot I g)} {C : Type} [CommRing C] (J : Ideal C) (ρ₁ ρ₂ : Hol W →+* C) : Prop :=
  ∃ n : Fin g → C, (∀ a, n a ∈ J) ∧ (∀ a b, n a * n b = 0) ∧ ∀ h, ρ₂ h = ρ₁ h + ∑ a, ρ₁ (dw a h) * n a

def Close {W : Opens (Tot I g)} {C : Type} [CommRing C] (J : Ideal C) (ρ₁ ρ₂ : Hol W →+* C) : Prop :=
  Relation.ReflTransGen (Step J) ρ₁ ρ₂

theorem Close.map {W : Opens (Tot I g)} {C C' : Type} [CommRing C] [CommRing C'] {J : Ideal C} {J' : Ideal C'}
    {ρ₁ ρ₂ : Hol W →+* C} (h : Close J ρ₁ ρ₂) (φ : C →+* C') (hφ : ∀ c ∈ J, φ c ∈ J') :
    Close J' (φ.comp ρ₁) (φ.comp ρ₂) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨n, hn, hnn, hρ⟩ := hs
    refine ih.tail ⟨fun a ↦ φ (n a), fun a ↦ hφ _ (hn a), fun a b ↦ by rw [← map_mul, hnn, map_zero], fun f ↦ ?_⟩
    simp only [RingHom.comp_apply, hρ, map_add, map_sum, map_mul]

theorem Close.comap {W W' : Opens (Tot I g)} {C : Type} [CommRing C] {J : Ideal C}
    {ρ₁ ρ₂ : Hol W' →+* C} (h : Close J ρ₁ ρ₂) (ψ : Hol W →+* Hol W') (hψ : ∀ a f, dw a (ψ f) = ψ (dw a f)) :
    Close J (ρ₁.comp ψ) (ρ₂.comp ψ) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨n, hn, hnn, hρ⟩ := hs
    exact ih.tail ⟨n, hn, hnn, fun f ↦ by simp only [RingHom.comp_apply, hρ, hψ]⟩

theorem Close.sub_mem {W : Opens (Tot I g)} {C : Type} [CommRing C] {J : Ideal C} {ρ₁ ρ₂ : Hol W →+* C}
    (h : Close J ρ₁ ρ₂) (f : Hol W) : ρ₂ f - ρ₁ f ∈ J := by
  induction h with
  | refl => simp
  | @tail b c _ hs ih =>
    obtain ⟨n, hn, -, hρ⟩ := hs
    have e : c f - ρ₁ f = (b f - ρ₁ f) + ∑ a, b (dw a f) * n a := by
      rw [hρ]
      ring
    rw [e]
    exact J.add_mem ih (J.sum_mem fun a _ ↦ J.mul_mem_left _ (hn a))

structure Charts (F : Fam I g Λ) : Type 1 where

  K : Type

  W : K → Opens (Tot I g)
  base : ∀ k, ∀ p ∈ W k, p.1 ∈ F.V

  le : Λ → K → K → Prop
  le_refl : ∀ k, le 0 k k
  le_trans : ∀ {l m k k' k''}, le l k' k → le m k'' k' → le (l + m) k'' k
  maps : ∀ {l k k'}, le l k' k → ∀ p ∈ W k', F.shift l p ∈ W k

def Fam.tot (F : Fam I g Λ) : Opens (Tot I g) := ⟨Prod.fst ⁻¹' F.V, F.V.isOpen.preimage continuous_fst⟩

def Fam.allCharts (F : Fam I g Λ) : Charts F where
  K := {W : Opens (Tot I g) // ∀ p ∈ W, p.1 ∈ F.V}
  W k := k.1
  base k := k.2
  le l k' k := ∀ p ∈ k'.1, F.shift l p ∈ k.1
  le_refl k p hp := by rwa [F.shift_zero]
  le_trans h h' p hp := by rw [F.shift_add]; exact h _ (h' p hp)
  maps h := h

def Fam.totChart (F : Fam I g Λ) : F.allCharts.K := ⟨F.tot, fun _ h ↦ h⟩

namespace Charts

variable {F : Fam I g Λ} (K : Charts F)

def Rich : Prop :=
  (∀ p : Tot I g, p.1 ∈ F.V → ∃ k, p ∈ K.W k) ∧
    ∀ l k₁ k₂ p, p ∈ K.W k₁ → F.shift l p ∈ K.W k₂ → ∃ k, p ∈ K.W k ∧ K.le 0 k k₁ ∧ K.le l k k₂

def Based : Prop := ∃ k, ∀ z ∈ F.V, ((z, 0) : Tot I g) ∈ K.W k

def cst (k : K.K) : Hol F.V →+* Hol (K.W k) :=
  (Hol.comap Prod.fst (fun _ _ ↦ analyticAt_fst) (K.base k)).toRingHom

variable {K} in

def sh {l : Λ} {k k' : K.K} (h : K.le l k' k) : Hol (K.W k) →+* Hol (K.W k') :=
  (Hol.comap (F.shift l) (F.shift_analytic l (K.base k')) (K.maps h)).toRingHom

theorem fn_cst (k : K.K) (f : Hol F.V) {p : Tot I g} (hp : p ∈ K.W k) : (K.cst k f).fn p = f.fn p.1 := by
  exact Hol.fn_comap _ _ _ f hp

variable {K}

theorem fn_sh {l : Λ} {k k' : K.K} (h : K.le l k' k) (f : Hol (K.W k)) {p : Tot I g} (hp : p ∈ K.W k') :
    (sh h f).fn p = f.fn (F.shift l p) := by
  exact Hol.fn_comap _ _ _ f hp

theorem sh_refl {k : K.K} (h : K.le 0 k k) (f : Hol (K.W k)) : sh h f = f := by
  refine Hol.ext_fn fun p hp ↦ ?_
  rw [fn_sh h f hp, F.shift_zero]

theorem sh_sh {l m : Λ} {k k' k'' : K.K} (h : K.le l k' k) (h' : K.le m k'' k') (h'' : K.le (l + m) k'' k)
    (f : Hol (K.W k)) : sh h' (sh h f) = sh h'' f := by
  refine Hol.ext_fn fun p hp ↦ ?_
  rw [fn_sh h' _ hp, fn_sh h f (K.maps h' p hp), fn_sh h'' f hp, F.shift_add]

theorem sh_cst {l : Λ} {k k' : K.K} (h : K.le l k' k) (f : Hol F.V) : sh h (K.cst k f) = K.cst k' f := by
  refine Hol.ext_fn fun p hp ↦ ?_
  rw [fn_sh h _ hp, K.fn_cst k f (K.maps h p hp), K.fn_cst k' f hp]
  rfl

theorem dw_sh {l : Λ} {k k' : K.K} (h : K.le l k' k) (a : Fin g) (f : Hol (K.W k)) : dw a (sh h f) = sh h (dw a f) := by
  refine Hol.ext_fn fun p hp ↦ ?_
  have hb : p.1 ∈ F.V := K.base k' p hp
  have hD : HasFDerivAt (F.τ l) (fderiv ℂ (F.τ l) p.1) p.1 :=
    (F.hol l p.1 hb).differentiableAt.hasFDerivAt
  have hΦ : HasFDerivAt (F.shift l) ((ContinuousLinearMap.fst ℂ (I → ℂ) (Fin g → ℂ)).prod
      (ContinuousLinearMap.snd ℂ (I → ℂ) (Fin g → ℂ) +
        (fderiv ℂ (F.τ l) p.1).comp (ContinuousLinearMap.fst ℂ (I → ℂ) (Fin g → ℂ)))) p :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_snd.add (hD.comp p hasFDerivAt_fst))
  have hder : fderiv ℂ (F.shift l) p ((0, Pi.single a 1) : Tot I g) = (0, Pi.single a 1) := by
    rw [hΦ.fderiv]
    simp
  have e1 := Hol.fn_der_comap (F.shift l) (F.shift_analytic l (K.base k')) (K.maps h)
    ((0, Pi.single a 1) : Tot I g) f hp
  have e2 := Hol.fn_comap (F.shift l) (F.shift_analytic l (K.base k')) (K.maps h)
    (Hol.der ((0, Pi.single a 1) : Tot I g) f) hp
  have e3 := Hol.fn_der ((0, Pi.single a 1) : Tot I g) f (K.maps h p hp)
  rw [hder] at e1
  exact e1.trans (e2.trans e3).symm

theorem dw_cst (k : K.K) (a : Fin g) (f : Hol F.V) : dw a (K.cst k f) = 0 := by
  refine Hol.ext_fn fun p hp ↦ ?_
  have e1 := Hol.fn_der_comap Prod.fst (fun _ _ ↦ analyticAt_fst) (K.base k)
    ((0, Pi.single a 1) : Tot I g) f hp
  rw [fderiv_fst] at e1
  simp only [ContinuousLinearMap.coe_fst', map_zero] at e1
  rw [Hol.fn_of_mem (0 : Hol (K.W k)) hp]
  exact e1.trans rfl

variable (K) in

structure Obj : Type 1 where

  k : K.K

  C : Type
  [ring : CommRing C]
  [alg : Algebra (Hol F.V) C]

  J : Ideal C
  nil : IsNilpotent J

  ρ : Hol (K.W k) →+* C
  ρ_cst : ∀ f, ρ (K.cst k f) = algebraMap (Hol F.V) C f

attribute [instance] Obj.ring Obj.alg

structure Hom (T T' : K.Obj) where

  φ : T.C →ₐ[Hol F.V] T'.C

  deg : Λ
  le : K.le deg T'.k T.k
  mem : ∀ c ∈ T.J, φ c ∈ T'.J
  close : Close T'.J (T'.ρ.comp (sh le)) ((φ : T.C →+* T'.C).comp T.ρ)

theorem Hom.ext' {T T' : K.Obj} {f f' : Hom T T'} (h : ∀ c, f.φ c = f'.φ c) (h' : f.deg = f'.deg) : f = f' := by
  obtain ⟨φ, d, le, mem, cl⟩ := f
  obtain ⟨φ', d', le', mem', cl'⟩ := f'
  obtain rfl : φ = φ' := AlgHom.ext h
  obtain rfl : d = d' := h'
  rfl

instance : Category K.Obj where
  Hom := Hom
  id T := ⟨AlgHom.id _ _, 0, K.le_refl _, fun _ h ↦ h, by
    rw [show T.ρ.comp (sh (K.le_refl T.k)) = T.ρ from RingHom.ext fun f ↦ congrArg T.ρ (sh_refl _ f)]
    exact Relation.ReflTransGen.refl⟩
  comp {T T' T''} f f' := ⟨f'.φ.comp f.φ, f.deg + f'.deg, K.le_trans f.le f'.le, fun c h ↦ f'.mem _ (f.mem c h), by
    rw [show T''.ρ.comp (sh (K.le_trans f.le f'.le)) = (T''.ρ.comp (sh f'.le)).comp (sh f.le) from
      RingHom.ext fun h ↦ congrArg T''.ρ (sh_sh f.le f'.le _ h).symm]
    exact Relation.ReflTransGen.trans (f'.close.comap (sh f.le) (dw_sh f.le)) (f.close.map (f'.φ : T'.C →+* T''.C) f'.mem)⟩
  id_comp f := Hom.ext' (fun _ ↦ rfl) (zero_add _)
  comp_id f := Hom.ext' (fun _ ↦ rfl) (add_zero _)
  assoc f f' f'' := Hom.ext' (fun _ ↦ rfl) (add_assoc _ _ _)

theorem hom_ext {T T' : K.Obj} {f f' : T ⟶ T'} (h : ∀ c, f.φ c = f'.φ c) (h' : f.deg = f'.deg) : f = f' := by
  obtain ⟨φ, d, le, mem, cl⟩ := f
  obtain ⟨φ', d', le', mem', cl'⟩ := f'
  obtain rfl : φ = φ' := AlgHom.ext h
  obtain rfl : d = d' := h'
  rfl

@[simp] theorem comp_φ {T T' T'' : K.Obj} (f : T ⟶ T') (f' : T' ⟶ T'') (c : T.C) : (f ≫ f').φ c = f'.φ (f.φ c) := rfl

@[simp] theorem comp_deg {T T' T'' : K.Obj} (f : T ⟶ T') (f' : T' ⟶ T'') : (f ≫ f').deg = f.deg + f'.deg := rfl

@[simp] theorem id_deg (T : K.Obj) : Hom.deg (𝟙 T) = 0 := rfl

variable (K) in

@[reducible] def Oc : K.Obj ⥤ CommAlgCat.{0} (Hol F.V) where
  obj T := CommAlgCat.of _ T.C
  map f := CommAlgCat.ofHom f.φ

theorem mp_Oc {T T' : K.Obj} (f : T ⟶ T') : mp K.Oc f = f.φ := rfl

variable (K) in

def perZ (per : Λ →+ Hol F.V) : Z1 K.Oc :=
  ⟨fun _ T' f ↦ algebraMap (Hol F.V) T'.C (per f.deg), fun T T' T'' f f' ↦ by
    change algebraMap _ T''.C (per (f.deg + f'.deg)) = f'.φ (algebraMap _ _ _) + algebraMap _ T''.C _
    rw [AlgHom.commutes, map_add, map_add]⟩

variable (K) in

def perCl (per : Λ →+ Hol F.V) : H1 K.Oc := H1.mk _ (K.perZ per)

variable (K) in

@[reducible] def triv (k : K.K) : K.Obj where
  k := k
  C := Hol (K.W k)
  alg := (K.cst k).toAlgebra
  J := ⊥
  nil := ⟨1, by simp⟩
  ρ := RingHom.id _
  ρ_cst _ := rfl

def fromTriv {l : Λ} {k : K.K} (T : K.Obj) (h : K.le l T.k k) (ρ : Hol (K.W k) →+* T.C)
    (hc : ∀ f, ρ (K.cst k f) = algebraMap (Hol F.V) T.C f) (hρ : Close T.J (T.ρ.comp (sh h)) ρ) : K.triv k ⟶ T where
  φ := letI := (K.triv k).alg; { ρ with commutes' := hc }
  deg := l
  le := h
  mem c hc := by rw [Ideal.mem_bot.1 hc, map_zero]; exact T.J.zero_mem
  close := hρ

def ptHom {l : Λ} {k : K.K} (T : K.Obj) (h : K.le l T.k k) : K.triv k ⟶ T :=
  fromTriv T h (T.ρ.comp (sh h)) (fun f ↦ (congrArg T.ρ (sh_cst h f)).trans (T.ρ_cst f)) Relation.ReflTransGen.refl

end Charts

theorem Fam.allCharts_based (F : Fam I g Λ) : F.allCharts.Based := by
  exact ⟨F.totChart, fun z hz ↦ hz⟩

theorem Fam.allCharts_rich (F : Fam I g Λ) : F.allCharts.Rich := by
  refine ⟨fun p hp ↦ ⟨F.totChart, hp⟩, fun l k₁ k₂ p h₁ h₂ ↦ ?_⟩
  have hopen : IsOpen ((k₁.1 : Set (Tot I g)) ∩ F.shift l ⁻¹' (k₂.1 : Set (Tot I g))) :=
    (F.shift_analytic l k₁.2).continuousOn.isOpen_inter_preimage k₁.1.isOpen k₂.1.isOpen
  refine ⟨⟨⟨_, hopen⟩, fun q hq ↦ k₁.2 q hq.1⟩, ⟨h₁, h₂⟩, fun q hq ↦ ?_, fun q hq ↦ hq.2⟩
  rw [F.shift_zero]
  exact hq.1

def Fam.transl (F : Fam I g Λ) (l : Λ) : F.allCharts.triv F.totChart ⟶ F.allCharts.triv F.totChart :=
  Charts.ptHom (l := l) (F.allCharts.triv F.totChart) (fun _ h ↦ h)

theorem Fam.transl_deg (F : Fam I g Λ) (l : Λ) : (F.transl l).deg = l := rfl

def Charts.dualAt {F : Fam I g Λ} (K : Charts F) (k : K.K) (p : Tot I g) (hp : p ∈ K.W k) : K.Obj where
  k := k
  C := DualNumber ℂ
  alg := (((algebraMap ℂ (DualNumber ℂ)).comp (Hol.ev p hp).toRingHom).comp (K.cst k)).toAlgebra
  J := Ideal.span {DualNumber.eps}
  nil := ⟨2, by rw [Ideal.span_singleton_pow, sq, DualNumber.eps_mul_eps]; simp⟩
  ρ := (algebraMap ℂ (DualNumber ℂ)).comp (Hol.ev p hp).toRingHom
  ρ_cst _ := rfl

theorem Charts.dualAt_J_ne_bot {F : Fam I g Λ} (K : Charts F) (k : K.K) (p : Tot I g) (hp : p ∈ K.W k) :
    (K.dualAt k p hp).J ≠ ⊥ := by
  change Ideal.span {DualNumber.eps} ≠ ⊥
  rw [Ne, Ideal.span_singleton_eq_bot]
  intro h
  have := congrArg TrivSqZeroExt.snd h
  simp at this

def tangentAt {W : Opens (Tot I g)} (a : Fin g) (p : Tot I g) (hp : p ∈ W) : Hol W →+* DualNumber ℂ where
  toFun h := TrivSqZeroExt.inl (Hol.ev p hp h) + TrivSqZeroExt.inr (Hol.ev p hp (dw a h))
  map_one' := by simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [Derivation.leibniz, mul_comm]
  map_zero' := by simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp

theorem step_tangentAt {W : Opens (Tot I g)} (a : Fin g) (p : Tot I g) (hp : p ∈ W) :
    Step (Ideal.span {DualNumber.eps}) ((algebraMap ℂ (DualNumber ℂ)).comp (Hol.ev p hp).toRingHom)
      (tangentAt a p hp) := by
  refine ⟨Pi.single a DualNumber.eps, fun b ↦ ?_, fun b c ↦ ?_, fun h ↦ ?_⟩
  · rcases eq_or_ne b a with rfl | hb
    · simp
    · simp [hb]
  · simp only [Pi.single_apply]
    split_ifs <;> simp
  · simp [tangentAt, Pi.single_apply]
    rw [Algebra.smul_def]
    rfl

def Charts.tangentHom {F : Fam I g Λ} (K : Charts F) (k : K.K) (a : Fin g) (p : Tot I g) (hp : p ∈ K.W k) :
    K.triv k ⟶ K.dualAt k p hp :=
  Charts.fromTriv (K.dualAt k p hp) (K.le_refl k) (tangentAt a p hp)
    (fun f ↦ by
      change (TrivSqZeroExt.inl (Hol.ev p hp (K.cst k f)) + TrivSqZeroExt.inr (Hol.ev p hp (dw a (K.cst k f))) :
        DualNumber ℂ) = TrivSqZeroExt.inl (Hol.ev p hp (K.cst k f))
      rw [Charts.dw_cst]; simp)
    (by
      rw [show (K.dualAt k p hp).ρ.comp (Charts.sh (K.le_refl k)) = (K.dualAt k p hp).ρ from
        RingHom.ext fun f ↦ congrArg (K.dualAt k p hp).ρ (Charts.sh_refl _ f)]
      exact Relation.ReflTransGen.single (step_tangentAt a p hp))

example : ∃ (T T' : ellFam.allCharts.Obj) (f : T ⟶ T'), T'.J ≠ ⊥ ∧ f.deg = (0, 1) :=
  ⟨_, _, ellFam.transl (0, 1) ≫
      ellFam.allCharts.tangentHom ellFam.totChart 0 (fun _ ↦ Complex.I, 0) ellFam_nontrivial.1,
    Charts.dualAt_J_ne_bot _ _ _ _, add_zero _⟩

example (F : Fam I g Λ) (per : Λ →+ Hol F.V) (l : Λ) :
    (F.allCharts.perZ per).1 _ _ (F.transl l) = F.allCharts.cst F.totChart (per l) := rfl

end GlobalTheory.AnPer
