import Mathlib
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Formalism.LocalToGlobal.LatticeGeometry.ArVolEqOfNef
import Formalism.SharpRestriction.Divisibility.WeightAlgebra

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace Formalism.L2.Geo

section Weights

variable {D : D7} {j : ℕ}

def wtOfN (N : ℕ) (w : WeightFamilies.Wt D j) (τ : D.what₂.Tau) (i : Fin N) : ℤ :=
  if h : i.1 < (D.R.sigW j).1 then (w.aP τ ⟨i.1, h⟩ : ℤ) + ((w.n / 2 : ℕ) : ℤ)
  else if h' : i.1 - (D.R.sigW j).1 < (D.R.sigW j).2 then
    -(w.aM τ (Fin.rev ⟨i.1 - (D.R.sigW j).1, h'⟩) : ℤ) - ((w.n / 2 : ℕ) : ℤ)
  else 0

def wtOf (w : WeightFamilies.Wt D j) : D.what₂.Tau → Fin D.R.r → ℤ := wtOfN D.R.r w

theorem wtOfN_wadd (N : ℕ) (w w' : WeightFamilies.Wt D j) :
    wtOfN N (WeightAlgebra.wadd w w') = wtOfN N w + wtOfN N w' := by
  have hn : (w.n + w'.n) / 2 = w.n / 2 + w'.n / 2 := by
    obtain ⟨a, ha⟩ := w.n_even; obtain ⟨b, hb⟩ := w'.n_even; omega
  funext τ i
  simp only [wtOfN, WeightAlgebra.wadd, Pi.add_apply, hn]
  split_ifs <;> push_cast <;> ring

theorem wtOf_eq_kapW (w : WeightFamilies.Wt D j) (hP : ∀ τ i, (w.aP τ i : ℤ) = D.what₂.kaBig j τ i)
    (hM : ∀ τ c, (w.aM τ c : ℤ) = -D.what₂.kaSmall j τ (Fin.rev c)) (hn : w.n = D.R.nV) :
    wtOf w = DV.kapW D j := by
  funext τ i
  simp only [wtOf, wtOfN, DV.kapW, hP, hM, hn, Fin.rev_rev]
  split_ifs <;> ring

theorem wt_ext {w w' : WeightFamilies.Wt D j} (h1 : w.aP = w'.aP) (h2 : w.aM = w'.aM) (h3 : w.n = w'.n) :
    w = w' := by
  cases w; cases w'; cases h1; cases h2; cases h3; rfl

instance instAddCommSemigroupWt : AddCommSemigroup (WeightFamilies.Wt D j) where
  add := WeightAlgebra.wadd
  add_assoc _ _ _ := wt_ext (funext fun _ => funext fun _ => Nat.add_assoc _ _ _)
    (funext fun _ => funext fun _ => Nat.add_assoc _ _ _) (Nat.add_assoc _ _ _)
  add_comm _ _ := wt_ext (funext fun _ => funext fun _ => Nat.add_comm _ _)
    (funext fun _ => funext fun _ => Nat.add_comm _ _) (Nat.add_comm _ _)

theorem wt_add_def (w w' : WeightFamilies.Wt D j) : w + w' = WeightAlgebra.wadd w w' := rfl

theorem wt_unique {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {w w' : WeightFamilies.Wt D j} (hn : w.n = w'.n)
    (h : wtOf w = wtOf w') : w = w' := by
  have hs := sigW_sum D h1 h2
  refine wt_ext (funext fun τ => funext fun i => ?_) (funext fun τ => funext fun c => ?_) hn
  · have := congrFun (congrFun h τ) ⟨i.1, by have := i.2; omega⟩
    simp only [wtOf, wtOfN, i.2, dif_pos, Fin.eta] at this
    rw [hn] at this
    have h3 : (w.aP τ i : ℤ) = (w'.aP τ i : ℤ) := by omega
    exact_mod_cast h3
  · have hc := (Fin.rev c).2
    have := congrFun (congrFun h τ) ⟨(D.R.sigW j).1 + (Fin.rev c).1, by omega⟩
    have hlt : ¬ ((D.R.sigW j).1 + (Fin.rev c).1 < (D.R.sigW j).1) := by omega
    have hlt' : (D.R.sigW j).1 + (Fin.rev c).1 - (D.R.sigW j).1 < (D.R.sigW j).2 := by omega
    simp only [wtOf, wtOfN, hlt, hlt', dif_pos, dif_neg, not_false_eq_true] at this
    have e : (Fin.rev ⟨(D.R.sigW j).1 + (Fin.rev c).1 - (D.R.sigW j).1, hlt'⟩ : Fin (D.R.sigW j).2) = c := by
      have : (⟨(D.R.sigW j).1 + (Fin.rev c).1 - (D.R.sigW j).1, hlt'⟩ : Fin (D.R.sigW j).2) = Fin.rev c :=
        Fin.ext (by simp)
      rw [this, Fin.rev_rev]
    rw [e, hn] at this
    have h3 : (w.aM τ c : ℤ) = (w'.aM τ c : ℤ) := by omega
    exact_mod_cast h3

end Weights

theorem one_le_prod_of_one_le {ι : Type} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  calc (1 : ℝ) = ∏ _i ∈ s, (1 : ℝ) := by simp
    _ ≤ ∏ i ∈ s, f i := Finset.prod_le_prod (fun _ _ => zero_le_one) h

def weylDim {n : ℕ} (a : Fin n → ℤ) : ℝ :=
  ∏ i : Fin n, ∏ k : Fin n,
    if i < k then ((a i : ℝ) - (a k : ℝ) + ((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ))
    else 1

theorem one_le_weylDim {n : ℕ} (a : Fin n → ℤ) (ha : Antitone a) : 1 ≤ weylDim a := by
  unfold weylDim
  refine one_le_prod_of_one_le _ _ fun i _ => ?_
  refine one_le_prod_of_one_le _ _ fun k _ => ?_
  split_ifs with h
  · have h1 : (a k : ℝ) ≤ a i := by exact_mod_cast ha h.le
    have h2 : (0 : ℝ) < ((k : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by
      have : (i : ℕ) < (k : ℕ) := h
      have : ((i : ℕ) : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    rw [le_div_iff₀ h2]; linarith
  · exact le_rfl

def dimKap (D : D7) (j : ℕ) : ℝ :=
  ∏ τ : D.what₂.Tau, weylDim (D.what₂.kaBig j τ) * weylDim (D.what₂.kaSmall j τ)

theorem one_le_dimKap {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (hP : ∀ τ i, (w.aP τ i : ℤ) = D.what₂.kaBig j τ i)
    (hM : ∀ τ c, (w.aM τ c : ℤ) = -D.what₂.kaSmall j τ (Fin.rev c)) : 1 ≤ dimKap D j := by
  unfold dimKap
  refine one_le_prod_of_one_le _ _ fun τ _ => ?_
  have hB : Antitone (D.what₂.kaBig j τ) := by
    intro a b hab
    rw [← hP, ← hP]; exact_mod_cast w.aPlus_antitone τ hab
  have hS : Antitone (D.what₂.kaSmall j τ) := by
    intro a b hab
    have h1 := hM τ (Fin.rev a); have h2 := hM τ (Fin.rev b)
    rw [Fin.rev_rev] at h1 h2
    have h3 : ((w.aM τ (Fin.rev a) : ℕ) : ℤ) ≤ w.aM τ (Fin.rev b) := by
      exact_mod_cast w.aM_anti τ (Fin.rev_le_rev.mpr hab)
    omega
  exact one_le_mul_of_one_le_of_one_le (one_le_weylDim _ hB) (one_le_weylDim _ hS)

section Val

variable {K : Type} [Field K] [NumberField K]

def vEK (la : HeightOneSpectrum (𝓞 K)) (a : K) : EReal :=
  open Classical in if a = 0 then ⊤ else (((vAdd la a : ℤ) : ℝ) : EReal)

theorem fv_vAdd_mul (la : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    vAdd la (a * b) = vAdd la a + vAdd la b := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr ha) ((Valuation.ne_zero_iff _).mpr hb)]
  ring

theorem fv_vAdd_nonneg (la : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} (ha : (a : K) ≠ 0) :
    0 ≤ vAdd la (a : K) := by
  unfold vAdd
  have h1 := la.valuation_le_one (K := K) a
  have h2 : (la.valuation K) (a : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one] at h3
  omega

theorem vEK_zero (la : HeightOneSpectrum (𝓞 K)) : vEK la (0 : K) = ⊤ := by simp [vEK]

theorem vEK_ne_bot (la : HeightOneSpectrum (𝓞 K)) (a : K) : vEK la a ≠ ⊥ := by
  unfold vEK; split_ifs <;> simp

theorem vEK_of_ne (la : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0) :
    vEK la a = (((vAdd la a : ℤ) : ℝ) : EReal) := by simp [vEK, ha]

theorem vEK_mul (la : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0) (b : K) :
    vEK la (a * b) = (((vAdd la a : ℤ) : ℝ) : EReal) + vEK la b := by
  by_cases hb : b = 0
  · simp [vEK, hb]
  · rw [vEK_of_ne la (mul_ne_zero ha hb), vEK_of_ne la hb, fv_vAdd_mul la ha hb]
    push_cast; rfl

theorem vEK_add (la : HeightOneSpectrum (𝓞 K)) (a b : K) :
    min (vEK la a) (vEK la b) ≤ vEK la (a + b) := by
  by_cases hab : a + b = 0
  · simp [vEK, hab]
  by_cases ha : a = 0
  · subst ha; simp
  by_cases hb : b = 0
  · subst hb; simp
  rw [vEK_of_ne la hab, vEK_of_ne la ha, vEK_of_ne la hb]
  have hn := fun (x : K) (hx : x ≠ 0) => (Valuation.ne_zero_iff (la.valuation K)).mpr hx
  rcases le_max_iff.mp (Valuation.map_add (la.valuation K) a b) with h | h
  · have := (WithZero.log_le_log (hn _ hab) (hn _ ha)).mpr h
    have h' : vAdd la a ≤ vAdd la (a + b) := by unfold vAdd; omega
    exact min_le_of_left_le (by exact_mod_cast h')
  · have := (WithZero.log_le_log (hn _ hab) (hn _ hb)).mpr h
    have h' : vAdd la b ≤ vAdd la (a + b) := by unfold vAdd; omega
    exact min_le_of_right_le (by exact_mod_cast h')

theorem fv_ereal_add_iInf {ι : Type} (c : ℝ) (f : ι → EReal) :
    (c : EReal) + ⨅ i, f i = ⨅ i, ((c : EReal) + f i) := by
  have hc : ∀ x : EReal, ((-c : ℝ) : EReal) + ((c : EReal) + x) = x := by
    intro x
    induction x using EReal.rec with
    | bot => simp
    | top => simp
    | coe x => norm_cast; ring
  have hc' : ∀ x : EReal, (c : EReal) + (((-c : ℝ) : EReal) + x) = x := by
    intro x
    induction x using EReal.rec with
    | bot => simp
    | top => simp
    | coe x => norm_cast; ring
  apply le_antisymm
  · exact le_iInf fun i => add_le_add le_rfl (iInf_le f i)
  · have h1 : ((-c : ℝ) : EReal) + ⨅ i, ((c : EReal) + f i) ≤ ⨅ i, f i :=
      le_iInf fun i => (add_le_add le_rfl (iInf_le (fun i => (c : EReal) + f i) i)).trans (hc (f i)).le
    have h2 := add_le_add (le_refl (c : EReal)) h1
    rwa [hc'] at h2

end Val

structure FormsPkg (D : D7) (G : DV.Geo D.what₂.LL) (NW : ℕ → ℕ) (CompW : ℕ → Type)
    [∀ j, Fintype (CompW j)] (algW : ∀ j, AlgPkg G D.what₂.Tau (NW j) (CompW j))
    (PtY : ℕ → ℕ → Type) : Type 1 where

  KO : Type
  [fKO : Field KO]
  [nfKO : NumberField KO]

  eO : 𝓞 KO ≃+* D.what₂.O

  kL : KO →+* D.what₂.LL

  kL_eO : ∀ x : 𝓞 KO, kL (x : KO) = D.what₂.OtoLL (eO x)

  Cusp : (j : ℕ) → WeightFamilies.Wt D j → Type
  [acgC : ∀ j w, AddCommGroup (Cusp j w)]
  [modC : ∀ j w, Module KO (Cusp j w)]
  [fdC : ∀ j w, FiniteDimensional KO (Cusp j w)]
  [modOC : ∀ j w, Module (𝓞 KO) (Cusp j w)]
  [towC : ∀ j w, IsScalarTower (𝓞 KO) KO (Cusp j w)]

  cmp : ∀ j w (c : CompW j), Cusp j w →ₛₗ[kL] G.Fn ((algW j).Yv c)

  cmp_mem : ∀ j w c (F : Cusp j w),
    cmp j w c F ∈ G.H0 ((algW j).Yv c) ((algW j).Lw c (wtOfN (NW j) w))

  cmp_cusp : ∀ j w c (F : Cusp j w),
    G.vanishOn ((algW j).Yv c) ((algW j).Lw c (wtOfN (NW j) w)) (cmp j w c F) ((algW j).Ybd c)

  cmp_span : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ w (s : ∀ c : CompW j, G.Fn ((algW j).Yv c)),
    (∀ c, s c ∈ G.H0 ((algW j).Yv c) ((algW j).Lw c (wtOfN (NW j) w)) ∧
      G.vanishOn ((algW j).Yv c) ((algW j).Lw c (wtOfN (NW j) w)) (s c) ((algW j).Ybd c)) →
    s ∈ Submodule.span D.what₂.LL (Set.range fun (F : Cusp j w) (c : CompW j) => cmp j w c F)

  cmp_indep : ∀ j w {n : ℕ} (v : Fin n → Cusp j w), LinearIndependent KO v →
    LinearIndependent D.what₂.LL (fun i (c : CompW j) => cmp j w c (v i))

  mulC : ∀ j (w w' : WeightFamilies.Wt D j), Cusp j w → Cusp j w' → Cusp j (WeightAlgebra.wadd w w')

  cmp_mul : ∀ j w w' c (F : Cusp j w) (F' : Cusp j w'),
    cmp j (WeightAlgebra.wadd w w') c (mulC j w w' F F') = cmp j w c F * cmp j w' c F'

  supN : ∀ j w, (KO →+* ℂ) → Cusp j w → ℝ
  supN_nonneg : ∀ j w σ F, 0 ≤ supN j w σ F
  supN_eq_zero : ∀ j w σ F, supN j w σ F = 0 ↔ F = 0
  supN_smul : ∀ j w σ (a : KO) F, supN j w σ (a • F) = ‖σ a‖ * supN j w σ F
  supN_add : ∀ j w σ F G, supN j w σ (F + G) ≤ supN j w σ F + supN j w σ G

  l2NormAlt : ∀ j w, (KO →+* ℂ) → Cusp j w → ℝ
  l2Norm_nonneg_bis : ∀ j w σ F, 0 ≤ l2NormAlt j w σ F
  l2Norm_eq_zero_iff : ∀ j w σ F, l2NormAlt j w σ F = 0 ↔ F = 0
  l2Norm_smul_alt : ∀ j w σ (a : KO) F, l2NormAlt j w σ (a • F) = ‖σ a‖ * l2NormAlt j w σ F
  l2Norm_add_le' : ∀ j w σ F G, l2NormAlt j w σ (F + G) ≤ l2NormAlt j w σ F + l2NormAlt j w σ G
  l2Norm_le_supNorm_alt : ∀ j w σ F, l2NormAlt j w σ F ≤ supN j w σ F

  Cu : ℕ → Type

  Xc : ∀ j, Cu j → Submodule (𝓞 D.host.E) (Fin (WeightFamilies.rho D j) → D.host.E)
  Xc_lat : ∀ j c, Submodule.IsLattice D.host.E (Xc j c)

  FJt : ∀ j (c : Cu j), WeightFamilies.ExpoSet D (Xc j c) → WeightFamilies.Wt D j → Type
  [acgF : ∀ j c χ w, AddCommGroup (FJt j c χ w)]
  [modF : ∀ j c χ w, Module KO (FJt j c χ w)]

  sg : ∀ j (c : Cu j) (χ : WeightFamilies.ExpoSet D (Xc j c)) (w : WeightFamilies.Wt D j), Cusp j w →ₗ[KO] FJt j c χ w

  Pt : ℕ → HeightOneSpectrum (𝓞 KO) → Type

  pt66 : ∀ j la, Pt j la → PtY j (WeightAlgebra.resCh la)

  vAtC : ∀ j la, Pt j la → ∀ w, Cusp j w → EReal
  vAtC_zero : ∀ j la y w, vAtC j la y w 0 = ⊤
  vAtC_ne_bot : ∀ j la y w F, vAtC j la y w F ≠ ⊥
  vAtC_add : ∀ j la y w F G, min (vAtC j la y w F) (vAtC j la y w G) ≤ vAtC j la y w (F + G)
  vAtC_smul : ∀ j la y w (a : KO) F, a ≠ 0 →
    vAtC j la y w (a • F) = (((vAdd la a : ℤ) : ℝ) : EReal) + vAtC j la y w F

  vAtC_mul : ∀ j la y w w' (F : Cusp j w) (F' : Cusp j w'),
    vAtC j la y (WeightAlgebra.wadd w w') (mulC j w w' F F') = vAtC j la y w F + vAtC j la y w' F'

  thAll : ∀ j (w : WeightFamilies.Wt D j), Submodule (𝓞 KO) (Cusp j w)

  shortTh : ∀ j (w : WeightFamilies.Wt D j), Submodule (𝓞 KO) (Cusp j w)

attribute [instance] FormsPkg.fKO FormsPkg.nfKO FormsPkg.acgC FormsPkg.modC FormsPkg.fdC
  FormsPkg.modOC FormsPkg.towC FormsPkg.acgF FormsPkg.modF

namespace FormsPkg

variable {D : D7} {G : DV.Geo D.what₂.LL} {NW : ℕ → ℕ} {CompW : ℕ → Type} [∀ j, Fintype (CompW j)]
  {algW : ∀ j, AlgPkg G D.what₂.Tau (NW j) (CompW j)} {PtY : ℕ → ℕ → Type}
  (P : FormsPkg D G NW CompW algW PtY)

def Mlat (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule (𝓞 P.KO) (P.Cusp j w) where
  carrier := {F | ∀ la (y : P.Pt j la), 0 ≤ P.vAtC j la y w F}
  zero_mem' := fun la y => by rw [P.vAtC_zero]; exact le_top
  add_mem' := fun {F F'} hF hF' la y => (le_min (hF la y) (hF' la y)).trans (P.vAtC_add j la y w F F')
  smul_mem' := fun a F hF la y => by
    change 0 ≤ P.vAtC j la y w (a • F)
    rw [← algebraMap_smul P.KO a F]
    by_cases ha : (algebraMap (𝓞 P.KO) P.KO a) = 0
    · rw [ha, zero_smul, P.vAtC_zero]; exact le_top
    · rw [P.vAtC_smul j la y w _ F ha]
      have h1 : (0 : EReal) ≤ (((vAdd la (algebraMap (𝓞 P.KO) P.KO a) : ℤ) : ℝ) : EReal) := by
        exact_mod_cast fv_vAdd_nonneg la ha
      exact add_nonneg h1 (hF la y)

theorem mem_Mlat {j : ℕ} {w : WeightFamilies.Wt D j} (F : P.Cusp j w) :
    F ∈ P.Mlat j w ↔ ∀ la (y : P.Pt j la), 0 ≤ P.vAtC j la y w F := Iff.rfl

abbrev FnT (_P : FormsPkg D G NW CompW algW PtY) (j : ℕ) : Type := ∀ c : CompW j, G.Fn ((algW j).Yv c)

instance (j : ℕ) : Algebra P.KO (P.FnT j) :=
  RingHom.toAlgebra ((algebraMap D.what₂.LL (∀ c : CompW j, G.Fn ((algW j).Yv c))).comp P.kL)

instance (j : ℕ) : Algebra (𝓞 P.KO) (P.FnT j) :=
  RingHom.toAlgebra ((algebraMap P.KO (P.FnT j)).comp (algebraMap (𝓞 P.KO) P.KO))

instance (j : ℕ) : IsScalarTower (𝓞 P.KO) P.KO (P.FnT j) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem FnT_smul_apply {j : ℕ} (a : P.KO) (f : P.FnT j) (c : CompW j) :
    (a • f) c = P.kL a • f c := by
  rw [Algebra.smul_def a f, Algebra.smul_def (P.kL a) (f c)]; rfl

abbrev Coef (j : ℕ) : Type := P.KO × P.FnT j

abbrev Amb (j : ℕ) : Type := AddMonoidAlgebra (P.Coef j) (WithZero (WeightFamilies.Wt D j))

def tup (j : ℕ) (w : WeightFamilies.Wt D j) : P.Cusp j w →ₗ[P.KO] P.Coef j where
  toFun F := (0, fun c => P.cmp j w c F)
  map_add' F F' := Prod.ext (by simp) (funext fun c => by
    change P.cmp j w c (F + F') = P.cmp j w c F + P.cmp j w c F'
    exact map_add (P.cmp j w c) F F')
  map_smul' a F := Prod.ext (by simp) (funext fun c => by
    change P.cmp j w c (a • F) = (a • (fun c => P.cmp j w c F : P.FnT j)) c
    rw [FnT_smul_apply, LinearMap.map_smulₛₗ])

theorem tup_apply {j : ℕ} {w : WeightFamilies.Wt D j} (F : P.Cusp j w) :
    P.tup j w F = (0, fun c => P.cmp j w c F) := rfl

theorem tup_inj (j : ℕ) (w : WeightFamilies.Wt D j) : Function.Injective (P.tup j w) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hF
  by_contra hne
  have h1 : LinearIndependent P.KO ![F] := by
    rw [linearIndependent_unique_iff]; simpa using hne
  have h2 := (P.cmp_indep j w ![F] h1).ne_zero 0
  apply h2
  have := congrArg Prod.snd hF
  funext c
  exact congrFun this c

theorem tup_mul {j : ℕ} {w w' : WeightFamilies.Wt D j} (F : P.Cusp j w) (F' : P.Cusp j w') :
    P.tup j w F * P.tup j w' F' = P.tup j (w + w') (P.mulC j w w' F F') := by
  refine Prod.ext (zero_mul (0 : P.KO)) (funext fun c => ?_)
  change P.cmp j w c F * P.cmp j w' c F' = P.cmp j (WeightAlgebra.wadd w w') c (P.mulC j w w' F F')
  rw [P.cmp_mul]

theorem mulC_add_left {j : ℕ} {w w' : WeightFamilies.Wt D j} (F F' : P.Cusp j w) (G' : P.Cusp j w') :
    P.mulC j w w' (F + F') G' = P.mulC j w w' F G' + P.mulC j w w' F' G' := by
  apply P.tup_inj j (w + w')
  simp only [map_add, ← P.tup_mul, add_mul]

theorem mulC_add_right {j : ℕ} {w w' : WeightFamilies.Wt D j} (F : P.Cusp j w) (G' G'' : P.Cusp j w') :
    P.mulC j w w' F (G' + G'') = P.mulC j w w' F G' + P.mulC j w w' F G'' := by
  apply P.tup_inj j (w + w')
  simp only [map_add, ← P.tup_mul, mul_add]

theorem mulC_smul_left {j : ℕ} {w w' : WeightFamilies.Wt D j} (a : P.KO) (F : P.Cusp j w) (G' : P.Cusp j w') :
    P.mulC j w w' (a • F) G' = a • P.mulC j w w' F G' := by
  apply P.tup_inj j (w + w')
  simp only [map_smul, ← P.tup_mul, smul_mul_assoc]

theorem mulC_smul_right {j : ℕ} {w w' : WeightFamilies.Wt D j} (a : P.KO) (F : P.Cusp j w) (G' : P.Cusp j w') :
    P.mulC j w w' F (a • G') = a • P.mulC j w w' F G' := by
  apply P.tup_inj j (w + w')
  simp only [map_smul, ← P.tup_mul, mul_smul_comm]

def Vm (j : ℕ) (m : WithZero (WeightFamilies.Wt D j)) : Submodule P.KO (P.Coef j) :=
  WithZero.recZeroCoe (motive := fun _ => Submodule P.KO (P.Coef j))
    (LinearMap.range (Algebra.linearMap P.KO (P.Coef j))) (fun w => LinearMap.range (P.tup j w)) m

theorem mem_Vm_zero {j : ℕ} (r : P.Coef j) : r ∈ P.Vm j 0 ↔ ∃ a : P.KO, algebraMap P.KO (P.Coef j) a = r :=
  Iff.rfl

theorem mem_Vm_coe {j : ℕ} (w : WeightFamilies.Wt D j) (r : P.Coef j) :
    r ∈ P.Vm j (w : WithZero (WeightFamilies.Wt D j)) ↔ ∃ F, P.tup j w F = r := Iff.rfl

theorem Vm_mul {j : ℕ} {m n : WithZero (WeightFamilies.Wt D j)} {r s : P.Coef j} (hr : r ∈ P.Vm j m)
    (hs : s ∈ P.Vm j n) : r * s ∈ P.Vm j (m + n) := by
  induction m using WithZero.recZeroCoe with
  | zero =>
    obtain ⟨a, rfl⟩ := (P.mem_Vm_zero r).mp hr
    rw [zero_add, ← Algebra.smul_def]
    exact Submodule.smul_mem _ a hs
  | coe u =>
    obtain ⟨F, rfl⟩ := (P.mem_Vm_coe u r).mp hr
    induction n using WithZero.recZeroCoe with
    | zero =>
      obtain ⟨b, rfl⟩ := (P.mem_Vm_zero s).mp hs
      rw [add_zero, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ b hr
    | coe v =>
      obtain ⟨F', rfl⟩ := (P.mem_Vm_coe v s).mp hs
      rw [← WithZero.coe_add, P.tup_mul]
      exact ⟨_, rfl⟩

def FormsS (j : ℕ) : Subalgebra P.KO (P.Amb j) where
  carrier := {x | ∀ m, x.coeff m ∈ P.Vm j m}
  mul_mem' := fun {x y} hx hy m => by
    classical
    rw [AddMonoidAlgebra.coeff_mul]
    refine Submodule.finsuppSum_mem _ _ _ _ fun m₁ _ => Submodule.finsuppSum_mem _ _ _ _ fun m₂ _ => ?_
    split_ifs with h
    · subst h; exact P.Vm_mul (hx m₁) (hy m₂)
    · exact zero_mem _
  add_mem' := fun {x y} hx hy m => by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]; exact add_mem (hx m) (hy m)
  algebraMap_mem' := fun a m => by
    classical
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    split_ifs with h
    · subst h; exact ⟨a, rfl⟩
    · exact zero_mem _

theorem mem_FormsS {j : ℕ} (x : P.Amb j) : x ∈ P.FormsS j ↔ ∀ m, x.coeff m ∈ P.Vm j m := Iff.rfl

def cf (j : ℕ) (m : WithZero (WeightFamilies.Wt D j)) : P.FormsS j →ₗ[P.KO] P.Coef j where
  toFun x := (x : P.Amb j).coeff m
  map_add' x y := by simp
  map_smul' a x := by simp

theorem cf_apply {j : ℕ} (m : WithZero (WeightFamilies.Wt D j)) (x : P.FormsS j) : P.cf j m x = (x : P.Amb j).coeff m := rfl

def incS (j : ℕ) (w : WeightFamilies.Wt D j) : P.Cusp j w →ₗ[P.KO] P.FormsS j where
  toFun F := ⟨AddMonoidAlgebra.single (w : WithZero (WeightFamilies.Wt D j)) (P.tup j w F), fun m => by
    classical
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with h
    · subst h; exact ⟨F, rfl⟩
    · exact zero_mem _⟩
  map_add' F F' := by
    apply Subtype.ext
    simp [AddMonoidAlgebra.single_add]
  map_smul' a F := by
    apply Subtype.ext
    simp [AddMonoidAlgebra.smul_single]

theorem incS_coe {j : ℕ} {w : WeightFamilies.Wt D j} (F : P.Cusp j w) :
    (P.incS j w F : P.Amb j) = AddMonoidAlgebra.single (w : WithZero (WeightFamilies.Wt D j)) (P.tup j w F) := rfl

open Classical in
theorem cf_incS {j : ℕ} (m : WithZero (WeightFamilies.Wt D j)) {w : WeightFamilies.Wt D j} (F : P.Cusp j w) :
    P.cf j m (P.incS j w F) = if (w : WithZero (WeightFamilies.Wt D j)) = m then P.tup j w F else 0 := by
  classical
  rw [cf_apply, incS_coe, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem incS_mul_eq {j : ℕ} {w w' : WeightFamilies.Wt D j} (F : P.Cusp j w) (F' : P.Cusp j w') :
    P.incS j w F * P.incS j w' F' = P.incS j (WeightAlgebra.wadd w w') (P.mulC j w w' F F') := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, incS_coe, incS_coe, incS_coe, AddMonoidAlgebra.single_mul_single,
    ← WithZero.coe_add, P.tup_mul]
  rfl

theorem incS_mul {j : ℕ} (w w' : WeightFamilies.Wt D j) (F : P.Cusp j w) (F' : P.Cusp j w') :
    ∃ H : P.Cusp j (WeightAlgebra.wadd w w'), P.incS j w F * P.incS j w' F' = P.incS j (WeightAlgebra.wadd w w') H :=
  ⟨_, P.incS_mul_eq F F'⟩

theorem exists_Fof {j : ℕ} (w : WeightFamilies.Wt D j) (x : P.FormsS j) :
    ∃ F, P.tup j w F = (x : P.Amb j).coeff (w : WithZero (WeightFamilies.Wt D j)) :=
  (P.mem_Vm_coe w _).mp (x.2 (w : WithZero (WeightFamilies.Wt D j)))

def Fof {j : ℕ} (w : WeightFamilies.Wt D j) (x : P.FormsS j) : P.Cusp j w := Classical.choose (P.exists_Fof w x)

theorem tup_Fof {j : ℕ} (w : WeightFamilies.Wt D j) (x : P.FormsS j) :
    P.tup j w (P.Fof w x) = (x : P.Amb j).coeff (w : WithZero (WeightFamilies.Wt D j)) :=
  Classical.choose_spec (P.exists_Fof w x)

theorem Fof_eq_iff {j : ℕ} (w : WeightFamilies.Wt D j) (x : P.FormsS j) (F : P.Cusp j w) :
    P.Fof w x = F ↔ P.tup j w F = (x : P.Amb j).coeff (w : WithZero (WeightFamilies.Wt D j)) :=
  ⟨fun h => h ▸ P.tup_Fof w x, fun h => P.tup_inj j w ((P.tup_Fof w x).trans h.symm)⟩

theorem Fof_add {j : ℕ} (w : WeightFamilies.Wt D j) (x y : P.FormsS j) : P.Fof w (x + y) = P.Fof w x + P.Fof w y := by
  rw [Fof_eq_iff, map_add, tup_Fof, tup_Fof]; simp

theorem Fof_smul {j : ℕ} (w : WeightFamilies.Wt D j) (a : P.KO) (x : P.FormsS j) : P.Fof w (a • x) = a • P.Fof w x := by
  rw [Fof_eq_iff, map_smul, tup_Fof]; simp

theorem Fof_zero {j : ℕ} (w : WeightFamilies.Wt D j) : P.Fof w (0 : P.FormsS j) = 0 := by
  rw [Fof_eq_iff, map_zero]; simp

theorem Fof_incS_self {j : ℕ} (w : WeightFamilies.Wt D j) (F : P.Cusp j w) : P.Fof w (P.incS j w F) = F := by
  rw [Fof_eq_iff, ← cf_apply, cf_incS, if_pos rfl]

theorem Fof_incS_ne {j : ℕ} {u w : WeightFamilies.Wt D j} (h : u ≠ w) (F : P.Cusp j w) : P.Fof u (P.incS j w F) = 0 := by
  rw [Fof_eq_iff, map_zero, ← cf_apply, cf_incS, if_neg (fun h' => h (WithZero.coe_injective h').symm)]

theorem Fof_eq_zero_of_coeff {j : ℕ} (w : WeightFamilies.Wt D j) (x : P.FormsS j)
    (h : (x : P.Amb j).coeff (w : WithZero (WeightFamilies.Wt D j)) = 0) : P.Fof w x = 0 := by
  rw [Fof_eq_iff, map_zero, h]

def scal {j : ℕ} (x : P.FormsS j) : P.KO := ((x : P.Amb j).coeff 0).1

theorem scal_add {j : ℕ} (x y : P.FormsS j) : P.scal (x + y) = P.scal x + P.scal y := by
  simp [scal]

theorem scal_smul {j : ℕ} (a : P.KO) (x : P.FormsS j) : P.scal (a • x) = a * P.scal x := by
  simp [scal]

theorem scal_zero {j : ℕ} : P.scal (0 : P.FormsS j) = 0 := by simp [scal]

theorem scal_incS {j : ℕ} {w : WeightFamilies.Wt D j} (F : P.Cusp j w) : P.scal (P.incS j w F) = 0 := by
  have h := P.cf_incS 0 F
  rw [if_neg (WithZero.coe_ne_zero)] at h
  rw [scal, ← cf_apply, h]; rfl

variable {j : ℕ}

def vAtS (la : HeightOneSpectrum (𝓞 P.KO)) (y : P.Pt j la) (x : P.FormsS j) : EReal :=
  min (vEK la (P.scal x)) (⨅ w, P.vAtC j la y w (P.Fof w x))

variable (la : HeightOneSpectrum (𝓞 P.KO)) (y : P.Pt j la)

theorem vAtS_zero : P.vAtS la y 0 = ⊤ := by
  simp [vAtS, scal_zero, Fof_zero, vAtC_zero, vEK_zero]

theorem vAtS_incS {w : WeightFamilies.Wt D j} (F : P.Cusp j w) : P.vAtS la y (P.incS j w F) = P.vAtC j la y w F := by
  rw [vAtS, scal_incS, vEK_zero, min_eq_right le_top]
  apply le_antisymm
  · exact (iInf_le _ w).trans (by rw [Fof_incS_self])
  · refine le_iInf fun u => ?_
    by_cases h : u = w
    · subst h; rw [Fof_incS_self]
    · rw [Fof_incS_ne P h, P.vAtC_zero]; exact le_top

theorem vAtS_add (x x' : P.FormsS j) : min (P.vAtS la y x) (P.vAtS la y x') ≤ P.vAtS la y (x + x') := by
  unfold vAtS
  rw [scal_add]
  refine le_min ?_ ?_
  · exact (min_le_min (min_le_left _ _) (min_le_left _ _)).trans (vEK_add la _ _)
  · refine le_iInf fun w => ?_
    rw [Fof_add]
    exact (min_le_min ((min_le_right _ _).trans (iInf_le _ w))
      ((min_le_right _ _).trans (iInf_le _ w))).trans (P.vAtC_add _ _ _ _ _ _)

theorem vAtS_smul (a : P.KO) (x : P.FormsS j) (ha : a ≠ 0) :
    P.vAtS la y (a • x) = (((vAdd la a : ℤ) : ℝ) : EReal) + P.vAtS la y x := by
  unfold vAtS
  rw [scal_smul, vEK_mul la ha]
  simp_rw [Fof_smul, P.vAtC_smul _ _ _ _ _ _ ha]
  rw [← fv_ereal_add_iInf, min_add_add_left]

theorem vAtS_ne_bot (x : P.FormsS j) : P.vAtS la y x ≠ ⊥ := by
  classical
  unfold vAtS
  set T : Finset (WeightFamilies.Wt D j) := (x : P.Amb j).coeff.support.preimage
    (fun w => (w : WithZero (WeightFamilies.Wt D j))) WithZero.coe_injective.injOn with hTdef
  have hT : T.inf (fun w => P.vAtC j la y w (P.Fof w x)) ≤ ⨅ w, P.vAtC j la y w (P.Fof w x) := by
    refine le_iInf fun w => ?_
    by_cases hw : w ∈ T
    · exact Finset.inf_le hw
    · have h0 : (x : P.Amb j).coeff (w : WithZero (WeightFamilies.Wt D j)) = 0 := by
        simpa [hTdef, Finsupp.mem_support_iff] using hw
      rw [P.Fof_eq_zero_of_coeff w x h0, P.vAtC_zero]; exact le_top
  have hne : T.inf (fun w => P.vAtC j la y w (P.Fof w x)) ≠ ⊥ := by
    rw [Ne, Finset.inf_eq_bot_iff]; push Not
    exact fun w _ => P.vAtC_ne_bot _ _ _ _ _
  intro h
  rcases min_eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact vEK_ne_bot la _ h1
  · exact hne (le_bot_iff.mp (h1 ▸ hT))

theorem vAtS_mul {w w' : WeightFamilies.Wt D j} (F : P.Cusp j w) (F' : P.Cusp j w') :
    P.vAtS la y (P.incS j w F * P.incS j w' F') = P.vAtS la y (P.incS j w F) + P.vAtS la y (P.incS j w' F') := by
  rw [incS_mul_eq, vAtS_incS, vAtS_incS, vAtS_incS, P.vAtC_mul]

def Forms (j : ℕ) : Type := P.FormsS j

instance instCommRingForms (j : ℕ) : CommRing (P.Forms j) := (P.FormsS j).toCommRing

instance instAlgForms (j : ℕ) : Algebra P.KO (P.Forms j) := (P.FormsS j).algebra

instance instAlgOForms (j : ℕ) : Algebra (𝓞 P.KO) (P.Forms j) :=
  RingHom.toAlgebra ((algebraMap P.KO (P.Forms j)).comp (algebraMap (𝓞 P.KO) P.KO))

instance instTowForms (j : ℕ) : IsScalarTower (𝓞 P.KO) P.KO (P.Forms j) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

def amb (x : P.Forms j) : P.Amb j := (x : P.FormsS j).1

theorem amb_injective : Function.Injective (P.amb (j := j)) := fun _ _ h => Subtype.ext h

@[simp] theorem amb_add (x x' : P.Forms j) : P.amb (x + x') = P.amb x + P.amb x' := rfl

@[simp] theorem amb_mul (x x' : P.Forms j) : P.amb (x * x') = P.amb x * P.amb x' := rfl

@[simp] theorem amb_smul (a : P.KO) (x : P.Forms j) : P.amb (a • x) = a • P.amb x := rfl

@[simp] theorem amb_zero : P.amb (0 : P.Forms j) = 0 := rfl

def inc (j : ℕ) (w : WeightFamilies.Wt D j) : P.Cusp j w →ₗ[P.KO] P.Forms j where
  toFun F := (P.incS j w F : P.FormsS j)
  map_add' F F' := P.amb_injective (by
    change ((P.incS j w (F + F') : P.FormsS j) : P.Amb j) = (P.incS j w F : P.Amb j) + (P.incS j w F' : P.Amb j)
    rw [map_add]; rfl)
  map_smul' a F := P.amb_injective (by
    change ((P.incS j w (a • F) : P.FormsS j) : P.Amb j) = a • (P.incS j w F : P.Amb j)
    rw [map_smul]; rfl)

theorem amb_inc {w : WeightFamilies.Wt D j} (F : P.Cusp j w) :
    P.amb (P.inc j w F) = AddMonoidAlgebra.single (w : WithZero (WeightFamilies.Wt D j)) (P.tup j w F) := rfl

def cfF (j : ℕ) (m : WithZero (WeightFamilies.Wt D j)) : P.Forms j →ₗ[P.KO] P.Coef j where
  toFun x := (P.amb x).coeff m
  map_add' x y := by simp
  map_smul' a x := by simp

open Classical in
theorem cfF_inc (m : WithZero (WeightFamilies.Wt D j)) {w : WeightFamilies.Wt D j} (F : P.Cusp j w) :
    P.cfF j m (P.inc j w F) = if (w : WithZero (WeightFamilies.Wt D j)) = m then P.tup j w F else 0 :=
  P.cf_incS m F

theorem inc_mul_eq {w w' : WeightFamilies.Wt D j} (F : P.Cusp j w) (F' : P.Cusp j w') :
    P.inc j w F * P.inc j w' F' = P.inc j (WeightAlgebra.wadd w w') (P.mulC j w w' F F') :=
  P.incS_mul_eq F F'

theorem inc_mul (w w' : WeightFamilies.Wt D j) (F : P.Cusp j w) (F' : P.Cusp j w') :
    ∃ H : P.Cusp j (WeightAlgebra.wadd w w'), P.inc j w F * P.inc j w' F' = P.inc j (WeightAlgebra.wadd w w') H :=
  ⟨_, P.inc_mul_eq F F'⟩

theorem inc_inj (w : WeightFamilies.Wt D j) : Function.Injective (P.inc j w) := fun F F' h => by
  rw [← P.Fof_incS_self w F, ← P.Fof_incS_self w F']
  exact congrArg (P.Fof w) h

theorem inc_indep (j : ℕ) : iSupIndep fun w : WeightFamilies.Wt D j => LinearMap.range (P.inc j w) := by
  intro w
  rw [Submodule.disjoint_def]
  intro x hx hx'
  obtain ⟨F, rfl⟩ := LinearMap.mem_range.mp hx
  have hle : (⨆ (u) (_ : u ≠ w), LinearMap.range (P.inc j u)) ≤
      LinearMap.ker (P.cfF j (w : WithZero (WeightFamilies.Wt D j))) := by
    refine iSup₂_le fun u hu => ?_
    rintro _ ⟨G', rfl⟩
    rw [LinearMap.mem_ker, cfF_inc, if_neg (fun h => hu (WithZero.coe_injective h))]
  have h0 := hle hx'
  rw [LinearMap.mem_ker, cfF_inc, if_pos rfl] at h0
  rw [P.tup_inj j w (h0.trans (map_zero _).symm), map_zero]

def vAt (la : HeightOneSpectrum (𝓞 P.KO)) (y : P.Pt j la) (x : P.Forms j) : EReal :=
  P.vAtS la y (x : P.FormsS j)

theorem vAt_zero : P.vAt la y 0 = ⊤ := P.vAtS_zero la y

theorem vAt_ne_bot (x : P.Forms j) : P.vAt la y x ≠ ⊥ := P.vAtS_ne_bot la y x

theorem vAt_add (x x' : P.Forms j) : min (P.vAt la y x) (P.vAt la y x') ≤ P.vAt la y (x + x') :=
  P.vAtS_add la y x x'

theorem vAt_smul (a : P.KO) (x : P.Forms j) (ha : a ≠ 0) :
    P.vAt la y (a • x) = (((vAdd la a : ℤ) : ℝ) : EReal) + P.vAt la y x :=
  P.vAtS_smul la y a x ha

theorem vAt_inc {w : WeightFamilies.Wt D j} (F : P.Cusp j w) : P.vAt la y (P.inc j w F) = P.vAtC j la y w F :=
  P.vAtS_incS la y F

theorem vAt_mul {w w' : WeightFamilies.Wt D j} (F : P.Cusp j w) (F' : P.Cusp j w') :
    P.vAt la y (P.inc j w F * P.inc j w' F') = P.vAt la y (P.inc j w F) + P.vAt la y (P.inc j w' F') :=
  P.vAtS_mul la y F F'

theorem Mlat_eq {w : WeightFamilies.Wt D j} (F : P.Cusp j w) :
    F ∈ P.Mlat j w ↔ ∀ la (y : P.Pt j la), 0 ≤ P.vAt la y (P.inc j w F) := by
  simp only [vAt_inc]; rfl

def MlatVal : Prop :=
  ∀ j (w : WeightFamilies.Wt D j) (F : P.Cusp j w), F ∈ P.Mlat j w ↔ ∀ la (y : P.Pt j la), 0 ≤ P.vAt la y (P.inc j w F)

theorem mlatVal : P.MlatVal := fun _ _ F => P.Mlat_eq F

def toWeightFamilies : WeightFamilies.Prov D where
  KO := P.KO
  eO := P.eO
  Cusp := P.Cusp
  Mlat := P.Mlat
  supN := P.supN
  supN_nonneg := P.supN_nonneg
  supN_eq_zero := P.supN_eq_zero
  supN_smul := P.supN_smul
  supN_add := P.supN_add
  l2NormAlt := P.l2NormAlt
  l2Norm_nonneg_bis := P.l2Norm_nonneg_bis
  l2Norm_eq_zero_iff := P.l2Norm_eq_zero_iff
  l2Norm_smul_alt := P.l2Norm_smul_alt
  l2Norm_add_le' := P.l2Norm_add_le'
  l2Norm_le_supNorm_alt := P.l2Norm_le_supNorm_alt
  Cu := P.Cu
  Xc := P.Xc
  Xc_lat := P.Xc_lat
  FJt := P.FJt
  sg := P.sg

def mkPJ (Pr : ModuliIntegralCharts.Prov D) (j : ℕ) (dat : Pr.Dat) (dat_rk : j < D.R.m → Pr.rk dat = D.R.r)
    (dat_jj : j < D.R.m → Pr.jj dat = (D.R.sigW j).1)
    (pt : ∀ la, P.Pt j la → (Pr.loc dat (WeightAlgebra.resCh la)).Pt (Pr.loc dat (WeightAlgebra.resCh la)).YY) :
    WeightAlgebra.PJ D P.toWeightFamilies Pr j where
  Forms := P.Forms j
  rF := P.instCommRingForms j
  aF := P.instAlgForms j
  aFO := P.instAlgOForms j
  stF := P.instTowForms j
  inc := P.inc j
  inc_inj := P.inc_inj
  inc_indep := P.inc_indep j
  inc_mul := P.inc_mul
  dat := dat
  dat_rk := dat_rk
  dat_jj := dat_jj
  Pt := P.Pt j
  pt66 := pt
  vAt := P.vAt
  vAt_zero := P.vAt_zero
  vAt_ne_bot := P.vAt_ne_bot
  vAt_add := P.vAt_add
  vAt_smul := fun la y a x ha => P.vAt_smul la y a x ha
  vAt_mul := fun la y _ _ F F' => P.vAt_mul la y F F'
  Mlat_eq := fun _ F => P.Mlat_eq F
  thAll := P.thAll j
  shortTh := P.shortTh j

def sig0 : P.KO →+* ℂ := D.what₂.embLL.comp P.kL

def MjSat (j : ℕ) (volRec : ℝ) : Prop :=
  ∃ w : WeightFamilies.Wt D j, w.n = D.R.nV ∧ wtOf w = DV.kapW D j ∧
  ∃ (s : Submodule P.KO (P.Cusp j w)) (φ : s →ₛₗ[P.sig0] D.what₂.Mj j),
    (∀ {n : ℕ} (v : Fin n → s), LinearIndependent P.KO v → LinearIndependent ℂ (φ ∘ v)) ∧
    Submodule.span ℂ (Set.range φ) = ⊤ ∧
    (D.what₂.MjLat j).carrier ⊆ Set.range φ ∧
    (∀ x : s, (x : P.Cusp j w) ∈ P.Mlat j w ↔ φ x ∈ (D.what₂.MjLat j).carrier) ∧
    (∀ x : s, ‖φ x‖ = Real.sqrt (volRec * dimKap D j) * P.l2NormAlt j w P.sig0 x)

theorem MjSat.all {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {volRec : ℝ} (h : P.MjSat j volRec)
    (w' : WeightFamilies.Wt D j) (hn' : w'.n = D.R.nV) (hw' : wtOf w' = DV.kapW D j) :
    ∃ (s : Submodule P.KO (P.Cusp j w')) (φ : s →ₛₗ[P.sig0] D.what₂.Mj j),
      (∀ {n : ℕ} (v : Fin n → s), LinearIndependent P.KO v → LinearIndependent ℂ (φ ∘ v)) ∧
      Submodule.span ℂ (Set.range φ) = ⊤ ∧
      (D.what₂.MjLat j).carrier ⊆ Set.range φ ∧
      (∀ x : s, (x : P.Cusp j w') ∈ P.Mlat j w' ↔ φ x ∈ (D.what₂.MjLat j).carrier) ∧
      (∀ x : s, ‖φ x‖ = Real.sqrt (volRec * dimKap D j) * P.l2NormAlt j w' P.sig0 x) := by
  obtain ⟨w, hn, hw, rest⟩ := h
  obtain rfl : w = w' := wt_unique h1 h2 (hn.trans hn'.symm) (hw.trans hw'.symm)
  exact rest

end FormsPkg

end Formalism.L2.Geo
