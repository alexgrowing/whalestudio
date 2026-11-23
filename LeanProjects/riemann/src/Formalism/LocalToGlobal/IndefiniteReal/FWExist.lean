import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec

noncomputable section

open NumberField IsDedekindDomain Module

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.L2.Pj

section Gen

variable {K L : Type} [Field K] [Field L] [Algebra K L] {C : Type} [AddCommGroup C] [Module K C] {n : ℕ}
  {H : Type} [AddCommGroup H] [Module ℂ H] {X : Type} [AddCommGroup X] [Module ℂ X]

variable (L) in

def crd (b : Basis (Fin n) K C) : C →ₗ[K] (Fin n → L) :=
  (Algebra.linearMap K L).compLeft (Fin n) ∘ₗ b.equivFun.toLinearMap

theorem crd_apply (b : Basis (Fin n) K C) (f : C) (k : Fin n) : crd L b f k = algebraMap K L (b.repr f k) := rfl

theorem crd_injective (b : Basis (Fin n) K C) : Function.Injective (crd L b) := fun _ _ h =>
  b.ext_elem fun k => (algebraMap K L).injective (congrFun h k)

theorem crd_basis (b : Basis (Fin n) K C) (k : Fin n) : crd L b (b k) = Pi.single k 1 := by
  funext l
  rw [crd_apply, b.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : k = l
  · simp [h]
  · simp [h, Ne.symm h]

def extB (σ : L →+* ℂ) (w : Fin n → H) : (Fin n → L) →ₛₗ[σ] H where
  toFun x := ∑ k, σ (x k) • w k
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [mul_smul, Finset.smul_sum]

theorem extB_apply (σ : L →+* ℂ) (w : Fin n → H) (x : Fin n → L) : extB σ w x = ∑ k, σ (x k) • w k := rfl

theorem extB_crd (σ : L →+* ℂ) (b : Basis (Fin n) K C) (jK : C →ₛₗ[σ.comp (algebraMap K L)] H) (f : C) :
    extB σ (fun k => jK (b k)) (crd L b f) = jK f := by
  conv_rhs => rw [← b.sum_repr f]
  rw [map_sum, extB_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ, crd_apply]
  rfl

theorem lc_ker {w : Fin n → H} (hw : LinearIndependent ℂ w) : LinearMap.ker (Fintype.linearCombination ℂ w) = ⊥ :=
  LinearMap.ker_eq_bot'.2 fun c hc => funext (Fintype.linearIndependent_iff.1 hw c hc)

theorem extB_indep (σ : L →+* ℂ) {w : Fin n → H} (hw : LinearIndependent ℂ w) {m : ℕ} {x : Fin m → Fin n → L}
    (hx : LinearIndependent L x) : LinearIndependent ℂ fun k => extB σ w (x k) := by
  let _ : Algebra L ℂ := σ.toAlgebra
  have h1 : LinearIndependent ℂ fun k => algebraMap L ℂ ∘ x k := linearIndependent_algebraMap_comp_iff.2 hx
  exact h1.map' _ (lc_ker hw)

theorem extB_injective (σ : L →+* ℂ) {w : Fin n → H} (hw : LinearIndependent ℂ w) : Function.Injective (extB σ w) := by
  intro x y h
  have h1 : (fun k => σ (x k)) = fun k => σ (y k) := LinearMap.ker_eq_bot.1 (lc_ker hw) h
  exact funext fun k => σ.injective (congrFun h1 k)

variable (K C) in

abbrev HasB (n : ℕ) : Prop := Nonempty (Basis (Fin n) K C)

theorem hasB_finrank [FiniteDimensional K C] : HasB K C (finrank K C) := ⟨Module.finBasis K C⟩

theorem hasB_iff : HasB K C n ↔ FiniteDimensional K C ∧ n = finrank K C :=
  ⟨fun ⟨b⟩ => ⟨Module.Finite.of_basis b, by rw [finrank_eq_card_basis b, Fintype.card_fin]⟩,
    fun ⟨_, h⟩ => h ▸ hasB_finrank⟩

variable (K L C) in
open Classical in

def crdOr (n : ℕ) : C →ₗ[K] (Fin n → L) := if h : HasB K C n then crd L h.some else 0

variable (K C) in
open Classical in

def bOr (n : ℕ) : Fin n → C := if h : HasB K C n then h.some else 0

theorem crdOr_eq (h : HasB K C n) : crdOr K L C n = crd L h.some := dif_pos h

theorem bOr_eq (h : HasB K C n) : bOr K C n = h.some := dif_pos h

theorem crdOr_injective (h : HasB K C n) : Function.Injective (crdOr K L C n) := crdOr_eq (L := L) h ▸ crd_injective _

variable (K L C) in
open Classical in

def secOr (n : ℕ) : LinearMap.range (crdOr K L C n) →ₗ[K] C :=
  if h : Function.Injective (crdOr K L C n) then (LinearEquiv.ofInjective _ h).symm.toLinearMap else 0

theorem secOr_apply (h : HasB K C n) (f : C) :
    secOr K L C n (LinearEquiv.ofInjective _ (crdOr_injective h) f) = f := by
  rw [secOr, dif_pos (crdOr_injective h)]
  exact LinearEquiv.symm_apply_apply _ f

theorem extB_crdOr (h : HasB K C n) (σ : L →+* ℂ) (jK : C →ₛₗ[σ.comp (algebraMap K L)] H) (f : C) :
    extB σ (fun k => jK (bOr K C n k)) (crdOr K L C n f) = jK f := by
  rw [crdOr_eq h, bOr_eq h]
  exact extB_crd σ _ jK f

def EvEx (σ : K →+* ℂ) (ev : H → X) (φ : C → X) : Prop := ∃ j : C →ₛₗ[σ] H, ∀ f, ev (j f) = φ f

open Classical in

def evOr (σ : K →+* ℂ) (ev : H → X) (φ : C → X) : C →ₛₗ[σ] H := if h : EvEx σ ev φ then h.choose else 0

theorem evOr_spec {σ : K →+* ℂ} {ev : H → X} {φ : C → X} (h : EvEx σ ev φ) (f : C) : ev (evOr σ ev φ f) = φ f := by
  rw [evOr, dif_pos h]
  exact h.choose_spec f

variable {G : Type} [Group G] {WL : Type} [AddCommGroup WL] [Module L WL]

def resK [Module K WL] [IsScalarTower K L WL] (σ : L →+* ℂ) (j : WL →ₛₗ[σ] H) (ι : C →ₗ[K] WL) :
    C →ₛₗ[σ.comp (algebraMap K L)] H where
  toFun f := j (ι f)
  map_add' f g := by rw [map_add, map_add]
  map_smul' a f := by
    rw [LinearMap.map_smul, ← algebraMap_smul L a, map_smulₛₗ]
    rfl

def RhoIs (σ : L →+* ℂ) (j : WL →ₛₗ[σ] H) (e : H →ₗ[ℂ] X) (act : G → X →ₗ[ℂ] X) (chi : G →* Lˣ)
    (ρ : G →* (WL →ₗ[L] WL)) : Prop :=
  ∀ g x, e (j (ρ g x)) = σ ((chi g : Lˣ) : L) • act g (e (j x))

open Classical in

def rhoOr (σ : L →+* ℂ) (j : WL →ₛₗ[σ] H) (e : H →ₗ[ℂ] X) (act : G → X →ₗ[ℂ] X) (chi : G →* Lˣ) :
    G →* (WL →ₗ[L] WL) :=
  if h : ∃ ρ, RhoIs σ j e act chi ρ then h.choose else 1

theorem rhoOr_spec {σ : L →+* ℂ} {j : WL →ₛₗ[σ] H} {e : H →ₗ[ℂ] X} {act : G → X →ₗ[ℂ] X} {chi : G →* Lˣ}
    (h : ∃ ρ, RhoIs σ j e act chi ρ) : RhoIs σ j e act chi (rhoOr σ j e act chi) := by
  rw [rhoOr, dif_pos h]
  exact h.choose_spec

theorem RhoIs.unique {σ : L →+* ℂ} {j : WL →ₛₗ[σ] H} {e : H →ₗ[ℂ] X} {act : G → X →ₗ[ℂ] X} {chi : G →* Lˣ}
    (hj : Function.Injective j) (he : Function.Injective e) {ρ ρ' : G →* (WL →ₗ[L] WL)}
    (h : RhoIs σ j e act chi ρ) (h' : RhoIs σ j e act chi ρ') : ρ = ρ' :=
  MonoidHom.ext fun g => LinearMap.ext fun x => hj (he ((h g x).trans (h' g x).symm))

variable (L) in

def rhoB (b : Basis (Fin n) K C) (ρC : G →* (C →ₗ[K] C)) : G →* ((Fin n → L) →ₗ[L] (Fin n → L)) where
  toFun g := Matrix.toLin' ((LinearMap.toMatrix b b (ρC g)).map (algebraMap K L))
  map_one' := by
    rw [map_one, LinearMap.toMatrix_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]
    rfl
  map_mul' g g' := by
    rw [map_mul, LinearMap.toMatrix_mul, Matrix.map_mul, Matrix.toLin'_mul]
    rfl

theorem rhoB_crd (b : Basis (Fin n) K C) (ρC : G →* (C →ₗ[K] C)) (g : G) (f : C) :
    rhoB L b ρC g (crd L b f) = crd L b (ρC g f) := by
  funext k
  show ((LinearMap.toMatrix b b (ρC g)).map (algebraMap K L)).mulVec (algebraMap K L ∘ b.repr f) k = _
  rw [← RingHom.map_mulVec, LinearMap.toMatrix_mulVec_repr, crd_apply]

theorem rhoIs_rhoB (σ : L →+* ℂ) (b : Basis (Fin n) K C) (jK : C →ₛₗ[σ.comp (algebraMap K L)] H) (e : H →ₗ[ℂ] X)
    (act : G → X →ₗ[ℂ] X) (chi : G →* Lˣ) (ρC : G →* (C →ₗ[K] C))
    (h : ∀ g f, e (jK (ρC g f)) = σ ((chi g : Lˣ) : L) • act g (e (jK f))) :
    RhoIs σ (extB σ fun k => jK (b k)) e act chi (rhoB L b ρC) := by
  intro g x
  have hx : x = ∑ k, x k • crd L b (b k) := by
    simp only [crd_basis]
    exact pi_eq_sum_univ' x
  rw [hx]
  simp only [map_sum, map_smulₛₗ, Finset.smul_sum, RingHom.id_apply, rhoB_crd, extB_crd, h]
  exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

end Gen

section Ext

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {C : Type} [AddCommGroup C] [Module K C]
  {WL : Type} [AddCommGroup WL] [Module L WL] [Module K WL] [IsScalarTower K L WL]
  {W : (L →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] {G : Type} [Group G]

theorem exists_ext_of_isKsForm (F : FormsL L K WL W G) (h : F.IsKsForm) (e : C ≃ₗ[K] F.WK) (σ : L →+* ℂ)
    (jK : C →ₛₗ[σ.comp (algebraMap K L)] W σ) : ∃ j : WL →ₛₗ[σ] W σ, ∀ f, j (e f : F.WK) = jK f := by
  obtain ⟨n, b, hb, -, h2, h3, h4⟩ := h
  let B : Basis (Fin n) L WL := Basis.mk h3 h4.ge
  let j : WL →ₛₗ[σ] W σ := (extB σ fun k => jK (e.symm ⟨b k, hb k⟩)).comp B.equivFun.toLinearMap
  have hj : ∀ k, j (b k) = jK (e.symm ⟨b k, hb k⟩) := fun k => by
    have h5 : b k = B k := (Basis.mk_apply h3 h4.ge k).symm
    show ∑ l, σ (B.repr (b k) l) • jK (e.symm ⟨b l, hb l⟩) = _
    rw [Finset.sum_eq_single k]
    · rw [show B.repr (b k) k = 1 by rw [h5]; simp, map_one, one_smul]
    · intro l _ hl
      rw [show B.repr (b k) l = 0 by rw [h5]; simp [hl.symm], map_zero, zero_smul]
    · simp
  have key : ∀ x ∈ Submodule.span K (Set.range b), ∀ hx : x ∈ F.WK, j x = jK (e.symm ⟨x, hx⟩) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact fun _ => hj k
    | zero => intro _; rw [map_zero, show (⟨0, _⟩ : F.WK) = 0 from rfl, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      intro _
      rw [map_add, ihx (h2.le hx), ihy (h2.le hy), ← map_add, ← map_add]
      rfl
    | smul a x hx ih =>
      intro _
      refine (congrArg j (algebraMap_smul L a x).symm).trans ?_
      rw [map_smulₛₗ, ih (h2.le hx)]
      refine (map_smulₛₗ jK a _).symm.trans (congrArg jK ?_)
      rw [← LinearEquiv.map_smul]
      rfl
  refine ⟨j, fun f => ?_⟩
  rw [key _ (h2.ge (e f).2) (e f).2]
  exact congrArg jK (e.symm_apply_apply f)

theorem finrank_of_isKsForm {m : ℕ} (F : FormsL L K (Fin m → L) W G) (h : F.IsKsForm) : m = finrank K F.WK := by
  obtain ⟨n, b, -, h1, h2, h3, h4⟩ := h
  have e1 : finrank L (Fin m → L) = n := by rw [finrank_eq_card_basis (Basis.mk h3 h4.ge), Fintype.card_fin]
  rw [← h2, finrank_span_eq_card h1, Fintype.card_fin, ← e1, finrank_fin_fun]

variable {Rg : Type} [CommRing Rg] [Algebra K Rg] [Algebra (𝓞 K) Rg] [IsScalarTower (𝓞 K) K Rg]

def FullLat (Cs : Submodule K Rg) (Vs : HeightOneSpectrum (𝓞 K) → Set (Rg → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) : Prop :=
  Submodule.IsLattice K (latOf Cs Vs hV)

theorem mkFull_of [Fintype G] [Module (𝓞 K) WL] [IsScalarTower (𝓞 K) K WL] (F : FormsL L K WL W G) {Cs : Submodule K Rg}
    {Vs : HeightOneSpectrum (𝓞 K) → Set (Rg → EReal)} {hV : ∀ la, ∀ v ∈ Vs la, IsVal la v} (ι : Cs →ₗ[K] WL)
    (hW : F.WK = LinearMap.range ι) (hM : ∀ x, x ∈ F.MK ↔ ∃ f : Cs, (∀ la, ∀ v ∈ Vs la, 0 ≤ v (f : Rg)) ∧ ι f = x)
    (h : FullLat Cs Vs hV) : F.MKFull := by
  have e : F.MK = (latOf Cs Vs hV).map (ι.restrictScalars (𝓞 K)) := by
    ext x
    rw [hM, Submodule.mem_map]
    rfl
  refine ⟨e ▸ h.fg.map _, ?_⟩
  rw [e, hW]
  show Submodule.span K (ι '' (latOf Cs Vs hV : Set Cs)) = _
  rw [Submodule.span_image, h.span_eq_top, Submodule.map_top]

end Ext

section Nrm

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem nrmOf_nonneg (v : EReal) : 0 ≤ nrmOf la v := by
  unfold nrmOf
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem nrmOf_top : nrmOf la ⊤ = 0 := by simp [nrmOf]

theorem nrmOf_anti {v w : EReal} (hv : v ≠ ⊥) (h : v ≤ w) : nrmOf la w ≤ nrmOf la v := by
  by_cases hw : w = ⊤
  · rw [hw, nrmOf_top]; exact nrmOf_nonneg la v
  have hv' : v ≠ ⊤ := fun h' => hw (top_le_iff.1 (h' ▸ h))
  simp only [nrmOf, if_neg hw, if_neg hv']
  exact Real.rpow_le_rpow_of_exponent_le (one_lt_absNorm_real la).le (neg_le_neg (EReal.toReal_le_toReal h hv hw))

end Nrm

section NrmM

variable {D : D7} (T : Core D) (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM j la)

theorem nrmM_zero : T.nrmM j la y 0 = 0 := by
  rw [Core.nrmM, (isVal_valSet la y.1 y.2).zero, nrmOf_top]

theorem nrmM_add (f g : T.R j) : T.nrmM j la y (f + g) ≤ max (T.nrmM j la y f) (T.nrmM j la y g) := by
  have hv := isVal_valSet la y.1 y.2
  have h := hv.add f g
  rcases le_total (y.1 f) (y.1 g) with h1 | h1
  · rw [min_eq_left h1] at h
    exact (nrmOf_anti la (hv.ne_bot f) h).trans (le_max_left _ _)
  · rw [min_eq_right h1] at h
    exact (nrmOf_anti la (hv.ne_bot g) h).trans (le_max_right _ _)

theorem nrmM_smul (a : T.Q.c.F) (f : T.R j) : T.nrmM j la y (a • f) = FinitePlace.mk la a * T.nrmM j la y f := by
  have hv := isVal_valSet la y.1 y.2
  by_cases ha : a = 0
  · rw [ha, zero_smul, nrmM_zero, map_zero, zero_mul]
  · rw [Core.nrmM, hv.smul a f ha]
    exact nrmOf_smul la ha (hv.ne_bot f)

end NrmM

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Collected

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev updFW (nW : Fin D.R.m → ℕ)
    (FW : ∀ i, FormsL D.what₂.LL Ks (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G) : RealDat D A Ks :=
  { R with nW := nW, FW := FW }

def evAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) (h : (R.HW i σ).H) : GA D (Wc D i) → ℂ :=
  (R.HW i σ).e h v

def actW (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : G) : MMap (R.MW i σ) →ₗ[ℂ] MMap (R.MW i σ) :=
  postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g))

def chiC (i : Fin D.R.m) (g : G) : ℂˣ :=
  ∏ PP : R.Pg, R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP))

def ChiIs (i : Fin D.R.m) (chi : G →* D.what₂.LLˣ) : Prop :=
  ∀ g, D.what₂.embLL ((chi g : D.what₂.LLˣ) : D.what₂.LL) = (chiC R i g : ℂ)

open Classical in

def chiTop (i : Fin D.R.m) : G →* D.what₂.LLˣ := if h : ∃ chi, ChiIs R i chi then h.choose else 1

def ChiVal : Prop :=
  ∀ i : Fin D.R.m, ∀ PP ∈ R.Pg, ∀ x, ((R.chi ((i : ℕ) + 1) PP x : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange

theorem chiC_mul (i : Fin D.R.m) (g g' : G) : chiC R i (g * g') = chiC R i g * chiC R i g' := by
  simp only [chiC, map_mul, Pi.mul_apply, Finset.prod_mul_distrib]

theorem chiIs_chiTop (h : ChiVal R) (i : Fin D.R.m) : ChiIs R i (chiTop R i) := by
  have h1 : ∀ g, ∃ a, D.what₂.embLL a = (chiC R i g : ℂ) := fun g => by
    have : ((chiC R i g : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
      rw [chiC, Units.coe_prod]
      exact prod_mem fun PP _ => h i PP.1 PP.2 _
    exact this
  choose a ha using h1
  have hne : ∀ g, a g ≠ 0 := fun g h0 => (chiC R i g).ne_zero (by rw [← ha, h0, map_zero])
  have hex : ∃ chi, ChiIs R i chi :=
    ⟨MonoidHom.mk' (fun g => Units.mk0 (a g) (hne g)) fun g g' => Units.ext (D.what₂.embLL.injective (by
      simp only [Units.val_mk0, Units.val_mul, map_mul, ha, chiC_mul])), ha⟩
  rw [chiTop, dif_pos hex]
  exact hex.choose_spec

theorem chiVal_of_roots (h : ∀ PP ∈ R.Pg, ∃ z : D.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP)ˣ))
    (hf : ∀ PP ∈ R.Pg, Finite (kP PP)) : ChiVal R := by
  intro i PP hPP x
  obtain ⟨z, hz⟩ := h PP hPP
  have := hf PP hPP
  have : NeZero (Nat.card (kP PP)ˣ) := ⟨Nat.card_pos.ne'⟩
  have h1 : ((R.chi ((i : ℕ) + 1) PP x : ℂˣ) : ℂ) ^ Nat.card (kP PP)ˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  obtain ⟨k, -, hk⟩ := (hz.map_of_injective D.what₂.embLL.injective).eq_pow_of_pow_eq_one h1
  exact ⟨z ^ k, by rw [map_pow, hk]⟩

def RhoTie : Prop :=
  ∀ i, (∃ ρ, RhoIs (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i _).e (actW R i _) (R.FW i).chi ρ) →
    RhoIs (sg0 D A) ((R.FW i).j (sg0 D A)) (R.HW i _).e (actW R i _) (R.FW i).chi (R.FW i).ρ

def IsUnitV {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} (v : M.Vec) : Prop := ∀ τ, ‖(v τ : M.H τ)‖ = 1

end Collected

section Top

variable (T : CoreJ D)

abbrev Cu (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) : Type :=
  T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n

instance (priority := high) cuGroup (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) : AddCommGroup (Cu T κ i) :=
  Submodule.addCommGroup _

instance (priority := high) cuModule (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) : Module T.Q.c.F (Cu T κ i) :=
  Submodule.module _

def nTop (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) : ℕ := finrank T.Q.c.F (Cu T κ i)

def phiC {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    GA D W → ℂ :=
  hV ▸ T.phiJ j σ a f

theorem inR (i : Fin D.R.m) : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩

theorem hasB_nTop (h : LawsJ T) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) :
    HasB T.Q.c.F (Cu T κ i) (nTop T κ i) :=
  hasB_iff.2 ⟨h.cuspFD _ (inR i) _ _ (dom_wtA (κ i)), rfl⟩

theorem eO_injective (h : T.Q.PinField) : Function.Injective (D.what₂.OtoLL.comp T.Q.eO.toRingHom) := fun x y hxy => by
  have h1 : ((x : T.Q.c.F) : ℂ) = ((y : T.Q.c.F) : ℂ) := by
    rw [← h x, ← h y]
    exact congrArg D.what₂.embLL hxy
  exact RingOfIntegers.coe_injective (Subtype.ext h1)

@[reducible] def algTop (h : T.Q.PinField) : Algebra T.Q.c.F D.what₂.LL :=
  (IsFractionRing.lift (K := T.Q.c.F) (eO_injective T h)).toAlgebra

variable [Algebra T.Q.c.F D.what₂.LL]

def AlgTie : Prop := ∀ x : 𝓞 T.Q.c.F, algebraMap T.Q.c.F D.what₂.LL (x : T.Q.c.F) = D.what₂.OtoLL (T.Q.eO x)

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem algTie_algTop (h : T.Q.PinField) : @AlgTie D T (algTop T h) := fun x =>
  IsFractionRing.lift_algebraMap (K := T.Q.c.F) (eO_injective T h) x

abbrev res (σ : D.what₂.LL →+* ℂ) : T.Q.c.F →+* ℂ := σ.comp (algebraMap T.Q.c.F D.what₂.LL)

abbrev resC (σ : D.what₂.LL →+* ℂ) : T.Q.c.F →+* ℂ := (starRingEnd ℂ).comp (res T σ)

theorem res_embLL (ha : AlgTie T) (h : T.Q.PinField) : res T D.what₂.embLL = T.σ₀ :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 T.Q.c.F)) (RingHom.ext fun x =>
    (congrArg D.what₂.embLL (ha x)).trans (h x))

theorem good_resC {σ : D.what₂.LL →+* ℂ} (h : ¬ GoodEmb T.Q.c (res T σ)) : GoodEmb T.Q.c (resC T σ) := by
  have := goodEmb_goodOf T.Q.c (res T σ)
  rwa [goodOf, if_neg h] at this

variable (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

include R in
theorem base_embedding_good (ha : AlgTie T) (h : T.Q.PinField) : GoodEmb T.Q.c (res T (sg0 D A)) := by
  rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T ha h]
  exact T.good_σ₀

def JEvAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) : Prop :=
  EvEx (res T σ) (evAt R i σ (v₀ i σ)) fun f : Cu T κ i => phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1))

def JEvExists : Prop :=
  ∀ i σ, GoodEmb T.Q.c (res T σ) → ∀ hV, JEvAt T R κ v₀ i σ hV

def phiBar {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i) (f : Cu T κ i) :
    GA D (Wc D i) → ℂ :=
  fun g => starRingEnd ℂ (phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) g)

def JEvBarAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i) : Prop :=
  ∃ v : (R.MW i σ).Vec, IsUnitV v ∧ EvEx (res T σ) (evAt R i σ v) (phiBar T κ hV)

def JEvBar : Prop :=
  ∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → ∀ hV, JEvBarAt T R κ i σ hV

open Classical in

def jTop (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : Cu T κ i →ₛₗ[res T σ] (R.HW i σ).H :=
  if GoodEmb T.Q.c (res T σ) then
    if hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i then
      evOr (res T σ) (evAt R i σ (v₀ i σ)) fun f : Cu T κ i => phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1))
    else 0
  else if h : ∃ hV, JEvBarAt T R κ i σ hV then
    evOr (res T σ) (evAt R i σ h.choose_spec.choose) (phiBar T κ h.choose)
  else 0

theorem jTop_good {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (hσ : GoodEmb T.Q.c (res T σ))
    (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (h : JEvAt T R κ v₀ i σ hV) (f : Cu T κ i) :
    evAt R i σ (v₀ i σ) (jTop T R κ v₀ i σ f) = phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) := by
  rw [jTop, if_pos hσ, dif_pos hV]
  exact evOr_spec h f

theorem jTop_good0 {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (hσ : GoodEmb T.Q.c (res T σ))
    (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (h : ¬ JEvAt T R κ v₀ i σ hV) : jTop T R κ v₀ i σ = 0 := by
  rw [jTop, if_pos hσ, dif_pos hV]
  exact dif_neg h

theorem top_lift_vanishes_off_good_embeddings {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (hσ : ¬ GoodEmb T.Q.c (res T σ))
    (hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i) (h : ¬ JEvBarAt T R κ i σ hV) : jTop T R κ v₀ i σ = 0 := by
  rw [jTop, if_neg hσ, dif_neg fun h' => h h'.choose_spec]

theorem jTop_bar {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (hσ : ¬ GoodEmb T.Q.c (res T σ))
    (hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i) (h : JEvBarAt T R κ i σ hV) :
    ∃ v : (R.MW i σ).Vec, IsUnitV v ∧ ∀ f, evAt R i σ v (jTop T R κ v₀ i σ f) = phiBar T κ hV f := by
  have h' : ∃ hV, JEvBarAt T R κ i σ hV := ⟨hV, h⟩
  refine ⟨h'.choose_spec.choose, h'.choose_spec.choose_spec.1, fun f => ?_⟩
  rw [jTop, if_neg hσ, dif_pos h']
  exact evOr_spec h'.choose_spec.choose_spec.2 f

def jL (i : Fin D.R.m) (n : ℕ) (σ : D.what₂.LL →+* ℂ) : (Fin n → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H :=
  extB σ fun k => jTop T R κ v₀ i σ (bOr T.Q.c.F (Cu T κ i) n k)

def formsN (i : Fin D.R.m) (n : ℕ) : FormsL D.what₂.LL T.Q.c.F (Fin n → D.what₂.LL) (fun σ => (R.HW i σ).H) G where
  WK := LinearMap.range (crdOr T.Q.c.F D.what₂.LL (Cu T κ i) n)
  Pt := T.PtM ((i : ℕ) + 1)
  nrm la y w := T.nrmM ((i : ℕ) + 1) la y (secOr T.Q.c.F D.what₂.LL (Cu T κ i) n w : T.R ((i : ℕ) + 1))
  nrm_nonneg la _ _ := nrmOf_nonneg la _
  nrm_zero la y := by rw [map_zero]; exact nrmM_zero T.toCore _ la y
  nrm_add la y w w' := by rw [map_add]; exact nrmM_add T.toCore _ la y _ _
  nrm_smul la y a w := by
    rw [LinearMap.map_smul]
    exact nrmM_smul T.toCore _ la y a _
  towKs := inferInstance
  ρ := rhoOr (sg0 D A) (jL T R κ v₀ i n _) (R.HW i _).e (actW R i _) (chiTop R i)
  chi := chiTop R i
  j := jL T R κ v₀ i n

def formsOfTop (i : Fin D.R.m) : FormsL D.what₂.LL T.Q.c.F (Fin (R.nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G :=
  formsN T R κ v₀ i (R.nW i)

abbrev topN (n : Fin D.R.m → ℕ) : RealDat D A T.Q.c.F := updFW R n fun i => formsN T R κ v₀ i (n i)

abbrev topR : RealDat D A T.Q.c.F := topN T R κ v₀ (nTop T κ)

def FWEq : Prop := ∀ i, R.FW i = formsOfTop T R κ v₀ i

theorem fwEq_topN (n : Fin D.R.m → ℕ) : FWEq T (topN T R κ v₀ n) κ v₀ := fun _ => rfl

def DimMatch : Prop := ∀ i, R.nW i = nTop T κ i

def FormsExist : Prop := Nonempty (FWTie T (topN T R κ v₀ R.nW) κ v₀)

def FormsExistTop : Prop := Nonempty (FWTie T (topR T R κ v₀) κ v₀)

theorem isKsForm_formsN {i : Fin D.R.m} {m : ℕ} (hb : HasB T.Q.c.F (Cu T κ i) m) : (formsN T R κ v₀ i m).IsKsForm := by
  have e : crdOr T.Q.c.F D.what₂.LL (Cu T κ i) m = crd D.what₂.LL hb.some := crdOr_eq hb
  have e1 : (fun k => crd D.what₂.LL hb.some (hb.some k)) = Pi.basisFun D.what₂.LL (Fin m) :=
    funext fun k => (crd_basis _ k).trans (Pi.basisFun_apply _ _ k).symm
  refine ⟨m, fun k => crd D.what₂.LL hb.some (hb.some k), fun k => ⟨hb.some k, by rw [e]⟩, ?_, ?_, ?_, ?_⟩
  · exact hb.some.linearIndependent.map' _ (LinearMap.ker_eq_bot.2 (crd_injective _))
  · show Submodule.span T.Q.c.F (Set.range (crd D.what₂.LL hb.some ∘ hb.some)) = LinearMap.range (crdOr _ _ _ m)
    rw [e, Set.range_comp, Submodule.span_image, hb.some.span_eq, Submodule.map_top]
  · rw [e1]; exact (Pi.basisFun _ _).linearIndependent
  · rw [e1]; exact (Pi.basisFun _ _).span_eq

theorem jL_crdOr {i : Fin D.R.m} {m : ℕ} (hb : HasB T.Q.c.F (Cu T κ i) m) (σ : D.what₂.LL →+* ℂ) (f : Cu T κ i) :
    jL T R κ v₀ i m σ (crdOr T.Q.c.F D.what₂.LL (Cu T κ i) m f) = jTop T R κ v₀ i σ f :=
  extB_crdOr hb σ (jTop T R κ v₀ i σ) f

theorem jL_eq_zero {i : Fin D.R.m} (m : ℕ) {σ : D.what₂.LL →+* ℂ} (h : jTop T R κ v₀ i σ = 0) : jL T R κ v₀ i m σ = 0 :=
  LinearMap.ext fun x => by
    rw [jL, h, extB_apply]
    simp

def KapIs : Prop :=
  ∀ (i : Fin D.R.m) (τ : D.what₂.Tau),
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).1, (κ i).aP τ k = aPl D i ((Wc D i).sig (tauE D τ)).1 τ k) ∧
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).2,
      (κ i).aM τ k = aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ k) ∧ (κ i).n = D.R.nV

variable (D) in

def KapDom : Prop :=
  (∀ (i : Fin D.R.m) (τ : D.what₂.Tau),
    (Antitone fun k : Fin (D.R.sigW ((i : ℕ) + 1)).1 => aPl D i ((Wc D i).sig (tauE D τ)).1 τ k) ∧
    Antitone fun k : Fin (D.R.sigW ((i : ℕ) + 1)).2 =>
      aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ k) ∧ Even D.R.nV

variable (D) in
theorem kapDom : KapDom D := by
  refine ⟨fun i τ => ?_, ?_⟩
  · rw [show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]
    have hi := i.2
    have hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r := by
      have := D.R.m_add_three_le_k
      simp only [Ranks.sigW, Ranks.r]
      omega
    generalize (D.R.sigW ((i : ℕ) + 1)).1 = p at *
    generalize (D.R.sigW ((i : ℕ) + 1)).2 = q at *
    refine ⟨fun k k' hk => ?_, fun k k' hk => ?_⟩
    · have h1 : (k : ℕ) ≤ k' := hk
      have h2 := k'.2
      have h3 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) (k' - k) k (by omega)
      rw [show (k : ℕ) + (k' - k) = k' by omega, Nat.cast_sub h1] at h3
      simp only [aPl, if_pos k.2, if_pos k'.2]
      exact Int.toNat_le_toNat (Int.floor_le_floor (by linarith))
    · have h1 : (k : ℕ) ≤ k' := hk
      have h2 := k'.2
      have h3 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) (k' - k) (p + (q - k') - 1) (by omega)
      rw [show p + (q - k') - 1 + ((k' : ℕ) - k) = p + (q - k) - 1 by omega, Nat.cast_sub h1] at h3
      simp only [aMi, if_pos k.2, if_pos k'.2, Nat.cast_sub k.2.le, Nat.cast_sub k'.2.le]
      exact Int.toNat_le_toNat (Int.floor_le_floor (by linarith))
  · obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    obtain ⟨c, hc⟩ := D.R.t_odd
    have := D.R.two_le_m
    exact ⟨a + b + c, by simp only [Ranks.nV, Ranks.r]; omega⟩

variable (D) in

def kapTop (i : Fin D.R.m) : WeightFamilies.Wt D ((i : ℕ) + 1) :=
  ⟨_, _, fun τ => ((kapDom D).1 i τ).1, fun τ => ((kapDom D).1 i τ).2, D.R.nV, (kapDom D).2⟩

variable (D) in
theorem kapIs_kapTop : KapIs (kapTop D) := fun _ _ => ⟨fun _ => rfl, fun _ => rfl, rfl⟩

theorem KapIs.eq (h : KapIs κ) (hT : Nonempty D.what₂.Tau) : κ = kapTop D := by
  funext i
  obtain ⟨τ₀⟩ := hT
  have h1 : (κ i).aP = (kapTop D i).aP := funext fun τ => funext (h i τ).1
  have h2 : (κ i).aM = (kapTop D i).aM := funext fun τ => funext (h i τ).2.1
  have h3 : (κ i).n = (kapTop D i).n := (h i τ₀).2.2
  generalize κ i = w at *
  generalize kapTop D i = w' at *
  cases w
  cases w'
  congr

def ChiTie : Prop := ∀ i : Fin D.R.m, T.chiW ((i : ℕ) + 1) T.toCore.σ₀ = R.mu0 ((i : ℕ) + 1)

theorem chiTie_of_chiR (ha : AlgTie T) (hp : T.Q.PinField) (h : ChiR T R) : ChiTie T R := fun i => by
  have e := res_embLL T ha hp
  have h1 := (h i D.what₂.embLL (e ▸ T.toCore.good_σ₀ : GoodEmb T.Q.c (res T D.what₂.embLL))).2.2.2.2 rfl
  exact (congrArg (T.chiW ((i : ℕ) + 1)) e).symm.trans h1

def IsBaseClassLevelAdapted : Prop :=
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) (res T σ))

structure TieIn : Prop where
  laws : LawsJ T
  alg : AlgTie T
  kap : KapIs κ
  hv₀ : ∀ i σ, IsChosenExtremalVector R i σ (v₀ i σ)
  chiR : ChiR T R
  x0 : IsBaseClassLevelAdapted T R

def tieN (n : Fin D.R.m → ℕ) (h : TieIn T R κ v₀) (hb : ∀ i, HasB T.Q.c.F (Cu T κ i) (n i)) :
    FWTie T (topN T R κ v₀ n) κ v₀ where
  alg_eq := h.alg
  e i := LinearEquiv.ofInjective _ (crdOr_injective (hb i))
  ks i := isKsForm_formsN T R κ v₀ (hb i)
  kap := h.kap
  pt _ _ := Equiv.refl _
  nrm_eq i la y f := congrArg (fun g : Cu T κ i => T.nrmM ((i : ℕ) + 1) la y (g : T.R ((i : ℕ) + 1))) (secOr_apply (hb i) f)
  laws := h.laws
  hv₀ := h.hv₀
  chiR := h.chiR
  x0 := h.x0
  ev0 i σ hσ hV hj := jL_eq_zero T R κ v₀ (n i) (jTop_good0 T R κ v₀ hσ hV fun h' => hj ⟨jL T R κ v₀ i (n i) σ, fun f =>
    (congrArg (evAt R i σ (v₀ i σ)) (jL_crdOr T R κ v₀ (hb i) σ f)).trans (jTop_good T R κ v₀ hσ hV h' f)⟩)
  ev i σ hσ hV hj f :=
    (congrArg (evAt R i σ (v₀ i σ)) (jL_crdOr T R κ v₀ (hb i) σ f)).trans
      (jTop_good T R κ v₀ hσ hV ⟨resK σ hj.choose (crdOr T.Q.c.F D.what₂.LL (Cu T κ i) (n i)), hj.choose_spec⟩ f)

theorem formsExistTop_of (h : TieIn T R κ v₀) : FormsExistTop T R κ v₀ :=
  ⟨tieN T R κ v₀ _ h (hasB_nTop T h.laws κ)⟩

theorem formsExist_of (h : TieIn T R κ v₀) (hd : DimMatch T R κ) : FormsExist T R κ v₀ :=
  ⟨tieN T R κ v₀ _ h fun i => hd i ▸ hasB_nTop T h.laws κ i⟩

theorem tieIn_top (h : LawsJ T) (ha : AlgTie T) (hs : ∀ i σ, LowSm (R.MW i σ)) (hc : ChiR T R) (hb : IsBaseClassLevelAdapted T R) :
    TieIn T R (kapTop D) (v0 R) :=
  ⟨h, ha, kapIs_kapTop D, fun i σ => extremal_vector_is_chosen R i σ (hs i σ), hc, hb⟩

end Top

section Comparison₂

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

def FWTie.jK (t : FWTie T R κ v₀) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : Cu T κ i →ₛₗ[res T σ] (R.HW i σ).H :=
  resK σ ((R.FW i).j σ) ((R.FW i).WK.subtype ∘ₗ (t.e i).toLinearMap)

def FWTie.Evaluates (t : FWTie T R κ v₀) : Prop :=
  ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c (res T σ) → ∀ (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (f : Cu T κ i),
    evAt R i σ (v₀ i σ) (t.jK i σ f) = phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1))

theorem FWTie.jEvExists (t : FWTie T R κ v₀) (h : t.Evaluates) : JEvExists T R κ v₀ :=
  fun i σ hσ hV => ⟨t.jK i σ, h i σ hσ hV⟩

theorem FWTie.evaluates (t : FWTie T R κ v₀) (hj : JEvExists T R κ v₀) : t.Evaluates := by
  intro i σ hσ hV
  obtain ⟨jK, hjK⟩ := hj i σ hσ hV
  obtain ⟨j', hj'⟩ := exists_ext_of_isKsForm (R.FW i) (t.ks i) (t.e i) σ jK
  exact t.ev i σ hσ hV ⟨j', fun f => (congrArg (evAt R i σ (v₀ i σ)) (hj' f)).trans (hjK f)⟩

theorem FWTie.mem_MK (t : FWTie T R κ v₀) (i : Fin D.R.m) (f : Cu T κ i) :
    ((t.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) ∈ (R.FW i).MK ↔
      ∀ la (y : T.PtM ((i : ℕ) + 1) la), 0 ≤ y.1 (f : T.R ((i : ℕ) + 1)) := by
  rw [FormsL.mem_MK]
  constructor
  · rintro ⟨_, h⟩ la y
    have h1 : (R.FW i).nrm la ((t.pt i la).symm y) (t.e i f) ≤ 1 := h la ((t.pt i la).symm y)
    rw [t.nrm_eq, Equiv.apply_symm_apply] at h1
    exact (T.nrmM_le_one_iff _ la y _).1 h1
  · intro h
    refine ⟨(t.e i f).2, fun la y => ?_⟩
    exact (t.nrm_eq i la y f).trans_le ((T.nrmM_le_one_iff _ la _ _).2 (h la _))

variable (T R v₀) in

def EvInj : Prop := ∀ i σ, GoodEmb T.Q.c (res T σ) → Function.Injective (evAt R i σ (v₀ i σ))

theorem FWTie.jK_eq (t : FWTie T R κ v₀) (ht : t.Evaluates) (h : EvInj T R v₀) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ}
    (hσ : GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) : t.jK i σ = jTop T R κ v₀ i σ :=
  LinearMap.ext fun f => h i σ hσ ((ht i σ hσ hV f).trans (jTop_good T R κ v₀ hσ hV (t.jEvExists ht i σ hσ hV) f).symm)

def BarTie (t : FWTie T R κ v₀) : Prop :=
  ∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → ∀ hV,
    (JEvBarAt T R κ i σ hV → ∃ v : (R.MW i σ).Vec, IsUnitV v ∧ ∀ f, evAt R i σ v (t.jK i σ f) = phiBar T κ hV f) ∧
      (¬ JEvBarAt T R κ i σ hV → (R.FW i).j σ = 0)

end Comparison₂

section Rows

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (n : Fin D.R.m → ℕ)

theorem rhoTie_topN : RhoTie (topN T R κ v₀ n) := fun _ h => rhoOr_spec h

theorem chiW_topN (h : ChiVal R) : (topN T R κ v₀ n).grp_chiW := fun i g =>
  (chiIs_chiTop R h i g).trans (Units.coe_prod _ _)

theorem barTie_tieN (hl : TieIn T R κ v₀) (hb : ∀ i, HasB T.Q.c.F (Cu T κ i) (n i)) :
    BarTie (tieN T R κ v₀ n hl hb) := fun i σ hσ hV => by
  refine ⟨fun h => ?_, fun h => jL_eq_zero T R κ v₀ (n i) (top_lift_vanishes_off_good_embeddings T R κ v₀ hσ hV h)⟩
  obtain ⟨v, hv, h1⟩ := jTop_bar T R κ v₀ hσ hV h
  exact ⟨v, hv, fun f => (congrArg (evAt R i σ v) (jL_crdOr T R κ v₀ (hb i) σ f)).trans (h1 f)⟩

def IntAll {i : Fin D.R.m} (f : Cu T κ i) : Prop :=
  ∀ la (y : T.PtM ((i : ℕ) + 1) la), 0 ≤ y.1 (f : T.R ((i : ℕ) + 1))

theorem mem_MK_formsN {i : Fin D.R.m} {m : ℕ} (hb : HasB T.Q.c.F (Cu T κ i) m) (x : Fin m → D.what₂.LL) :
    x ∈ (formsN T R κ v₀ i m).MK ↔ ∃ f, IntAll T κ f ∧ crdOr T.Q.c.F D.what₂.LL (Cu T κ i) m f = x := by
  have key : ∀ f la y, (formsN T R κ v₀ i m).nrm la y ⟨crdOr T.Q.c.F D.what₂.LL (Cu T κ i) m f, f, rfl⟩ ≤ 1 ↔
      0 ≤ y.1 (f : T.R ((i : ℕ) + 1)) := fun f la y =>
    (congrArg (fun g : Cu T κ i => T.nrmM ((i : ℕ) + 1) la y (g : T.R ((i : ℕ) + 1)) ≤ 1) (secOr_apply hb f)).to_iff.trans
      (T.nrmM_le_one_iff _ la y _)
  rw [FormsL.mem_MK]
  constructor
  · rintro ⟨⟨f, rfl⟩, h⟩
    exact ⟨f, fun la y => (key f la y).1 (h la y), rfl⟩
  · rintro ⟨f, h, rfl⟩
    exact ⟨⟨f, rfl⟩, fun la y => (key f la y).2 (h la y)⟩

def JUnif : Prop :=
  ∀ i σ, (∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b →
      LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k)) ∧
    Submodule.span ℂ (Set.range (jTop T R κ v₀ i σ)) = ⊤

def IsGeoAct (i : Fin D.R.m) (ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i)) : Prop :=
  (∀ σ g f, (R.HW i σ).e (jTop T R κ v₀ i σ (ρC g f)) =
      σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) • actW R i σ g ((R.HW i σ).e (jTop T R κ v₀ i σ f))) ∧
    ∀ g f, IntAll T κ f → IntAll T κ (ρC g f)

def GeoAct : Prop := ∀ i, ∃ ρC, IsGeoAct T R κ v₀ i ρC

def LatFull : Prop :=
  ∀ i : Fin D.R.m, FullLat (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n)
    (valSet (T.Q.Xo _) T.Q.c (algCls (T.Q.Xo _) T.Q.c)) fun la => isVal_valSet la

theorem indep_bOr (hu : JUnif T R κ v₀) {i : Fin D.R.m} {m : ℕ} (hb : HasB T.Q.c.F (Cu T κ i) m) (σ : D.what₂.LL →+* ℂ) :
    LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (bOr T.Q.c.F (Cu T κ i) m k) :=
  (hu i σ).1 m _ (bOr_eq hb ▸ hb.some.linearIndependent)

theorem rhoIs_jL {i : Fin D.R.m} {m : ℕ} (hb : HasB T.Q.c.F (Cu T κ i) m) {ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i)}
    (h : IsGeoAct T R κ v₀ i ρC) (σ : D.what₂.LL →+* ℂ) :
    RhoIs σ (jL T R κ v₀ i m σ) (R.HW i σ).e (actW R i σ) (chiTop R i) (rhoB D.what₂.LL hb.some ρC) := by
  rw [jL, bOr_eq hb]
  exact rhoIs_rhoB σ hb.some _ _ _ _ ρC (h.1 σ)

theorem rho_formsN (hu : JUnif T R κ v₀) (he : R.models_HW) {i : Fin D.R.m} {m : ℕ} (hb : HasB T.Q.c.F (Cu T κ i) m)
    {ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i)} (h : IsGeoAct T R κ v₀ i ρC) :
    (formsN T R κ v₀ i m).ρ = rhoB D.what₂.LL hb.some ρC :=
  RhoIs.unique (extB_injective _ (indep_bOr T R κ v₀ hu hb _)) (he i _).1
    (rhoOr_spec ⟨_, rhoIs_jL T R κ v₀ hb h _⟩) (rhoIs_jL T R κ v₀ hb h _)

theorem lUnif_topN (hb : ∀ i, HasB T.Q.c.F (Cu T κ i) (n i)) (he : R.models_HW) (hu : JUnif T R κ v₀) (hg : GeoAct T R κ v₀) :
    (topN T R κ v₀ n).LUnif := fun i σ => by
  obtain ⟨ρC, h⟩ := hg i
  refine ⟨fun m b hm => extB_indep σ (indep_bOr T R κ v₀ hu (hb i) σ) hm, ?_, ?_⟩
  · refine top_le_iff.1 ((hu i σ).2.ge.trans (Submodule.span_mono ?_))
    rintro _ ⟨f, rfl⟩
    exact ⟨_, jL_crdOr T R κ v₀ (hb i) σ f⟩
  · have h1 := rhoIs_jL T R κ v₀ (hb i) h σ
    rw [← rho_formsN T R κ v₀ hu he (hb i) h] at h1
    exact h1

theorem mkStable_formsN (hu : JUnif T R κ v₀) (he : R.models_HW) (hg : GeoAct T R κ v₀) {i : Fin D.R.m} {m : ℕ}
    (hb : HasB T.Q.c.F (Cu T κ i) m) : (formsN T R κ v₀ i m).MKStable := fun g x => by
  obtain ⟨ρC, h⟩ := hg i
  have h1 : ∀ f, (formsN T R κ v₀ i m).ρ g (crdOr T.Q.c.F D.what₂.LL (Cu T κ i) m f) =
      crdOr T.Q.c.F D.what₂.LL (Cu T κ i) m (ρC g f) := fun f => by
    rw [rho_formsN T R κ v₀ hu he hb h, crdOr_eq hb]
    exact rhoB_crd _ ρC g f
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨_, (h1 f).symm⟩
  · intro hx
    obtain ⟨f, hf, rfl⟩ := (mem_MK_formsN T R κ v₀ hb x).1 hx
    exact (mem_MK_formsN T R κ v₀ hb _).2 ⟨_, h.2 g f hf, (h1 f).symm⟩

theorem mkFull_formsN (hl : LatFull T κ) {i : Fin D.R.m} {m : ℕ} (hb : HasB T.Q.c.F (Cu T κ i) m) :
    (formsN T R κ v₀ i m).MKFull :=
  mkFull_of _ (crdOr T.Q.c.F D.what₂.LL (Cu T κ i) m) rfl (fun x => (mem_MK_formsN T R κ v₀ hb x).trans
    (exists_congr fun _ => and_congr ⟨fun h la v hv => h la ⟨v, hv⟩, fun h la y => h la y.1 y.2⟩ Iff.rfl)) (hl i)

theorem lIntegral_topN (hb : ∀ i, HasB T.Q.c.F (Cu T κ i) (n i)) (he : R.models_HW) (hu : JUnif T R κ v₀)
    (hg : GeoAct T R κ v₀) (hl : LatFull T κ) : (topN T R κ v₀ n).LIntegral := fun i =>
  ⟨isKsForm_formsN T R κ v₀ (hb i), mkFull_formsN T R κ v₀ hl (hb i), mkStable_formsN T R κ v₀ hu he hg (hb i)⟩

def FormsExistAll : Prop :=
  ∃ t : FWTie T (topR T R κ v₀) κ v₀, RhoTie (topR T R κ v₀) ∧ BarTie t ∧ (topR T R κ v₀).grp_chiW

theorem formsExistAll_of (h : TieIn T R κ v₀) (hc : ChiVal R) : FormsExistAll T R κ v₀ :=
  ⟨tieN T R κ v₀ _ h (hasB_nTop T h.laws κ), rhoTie_topN T R κ v₀ _, barTie_tieN T R κ v₀ _ h _, chiW_topN T R κ v₀ _ hc⟩

theorem formsExistTop_iff : FormsExistTop T R κ v₀ ↔ TieIn T R κ v₀ :=
  ⟨fun ⟨t⟩ => ⟨t.laws, t.alg_eq, t.kap, t.hv₀, t.chiR, t.x0⟩, formsExistTop_of T R κ v₀⟩

theorem evaluates_tieN_iff (h : TieIn T R κ v₀) (hb : ∀ i, HasB T.Q.c.F (Cu T κ i) (n i)) :
    (tieN T R κ v₀ n h hb).Evaluates ↔ JEvExists T R κ v₀ :=
  ⟨fun ht => (tieN T R κ v₀ n h hb).jEvExists ht, fun hj => (tieN T R κ v₀ n h hb).evaluates hj⟩

theorem FWTie.dimMatch {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (t : FWTie T R κ v₀) : DimMatch T R κ := fun i =>
  (finrank_of_isKsForm (R.FW i) (t.ks i)).trans (t.e i).finrank_eq.symm

theorem tie_of_fwEq (h : TieIn T R κ v₀) (hd : DimMatch T R κ) (hf : FWEq T R κ v₀) : Nonempty (FWTie T R κ v₀) := by
  have h1 : ∀ FW, FW = (fun i => formsN T R κ v₀ i (R.nW i)) → Nonempty (FWTie T (updFW R R.nW FW) κ v₀) := by
    rintro _ rfl
    exact formsExist_of T R κ v₀ h hd
  exact h1 R.FW (funext hf)

end Rows

end Formalism.IndefR.FWT
