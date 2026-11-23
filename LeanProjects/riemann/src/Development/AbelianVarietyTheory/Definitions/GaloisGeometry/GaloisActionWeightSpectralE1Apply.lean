import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PushWithIsTranspose
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReductionUniformizerPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime]

def castHQ {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : HQ l E n i ≃ₗ[ℚ_[l]] HQ l E n' i' := by
  subst hn; subst hi; exact LinearEquiv.refl _ _

@[simp] theorem castHQ_refl {E : Spc} {n i : ℤ} (x : HQ l E n i) : castHQ l (E := E) (rfl : n = n) (rfl : i = i) x = x := rfl

theorem pullHQ_map_id (E : Spc) (n i : ℤ) : pullHQ l (𝟙 E) n i = LinearMap.id := by
  unfold pullHQ; rw [pullHl_id]; exact LinearMap.baseChange_id

theorem pullHQ_map_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = pullHQ l f n i ∘ₗ pullHQ l g n i := by
  unfold pullHQ; rw [pullHl_comp]; exact LinearMap.baseChange_comp _ _

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime]

def idx (m : ℕ) (a : ℤ) : Finset ℕ := (Finset.range m).filter fun s => -a ≤ (s : ℤ) ∧ a + 2 * (s : ℤ) < m

theorem mem_idx {m : ℕ} {a : ℤ} {s : ℕ} : s ∈ idx m a ↔ -a ≤ (s : ℤ) ∧ a + 2 * (s : ℤ) < m := by
  unfold idx
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩

def str (a : ℤ) (s : ℕ) : ℕ := (a + 2 * (s : ℤ)).toNat

variable {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

abbrev Summand (a b w : ℤ) (s : ℕ) : Type 1 := HQ l (sch.obj (Ystr J (str a s))) (b - 2 * s) (w - s)

abbrev E1 (a b w : ℤ) : Type 1 := ∀ s : idx (Fintype.card ι) a, Summand l J a b w s

def castStr {t t' : ℕ} {n i n' i' : ℤ} (ht : t = t') (hn : n = n') (hi : i = i') :
    HQ l (sch.obj (Ystr J t)) n i ≃ₗ[ℚ_[l]] HQ l (sch.obj (Ystr J t')) n' i' := by
  subst ht; subst hn; subst hi; exact LinearEquiv.refl _ _

@[simp] theorem castStr_refl {t : ℕ} {n i : ℤ} (x : HQ l (sch.obj (Ystr J t)) n i) :
    castStr l J (rfl : t = t) (rfl : n = n) (rfl : i = i) x = x := rfl

def res (t : ℕ) (n i : ℤ) : HQ l (sch.obj (Ystr J t)) n i →ₗ[ℚ_[l]] HQ l (sch.obj (Ystr J (t + 1))) n i :=
  ∑ j : Fin (t + 2), ((-1 : ℚ_[l]) ^ (j : ℕ)) • pullHQ l (sch.map (δ J t j)) n i

def gys (d t : ℕ) (n i : ℤ) : HQ l (sch.obj (Ystr J (t + 1))) n i →ₗ[ℚ_[l]] HQ l (sch.obj (Ystr J t)) (n + 2) (i + 1) :=
  ∑ j : Fin (t + 2), ((-1 : ℚ_[l]) ^ (j : ℕ)) •
    ((castHQ l (by push_cast; ring) (by push_cast; ring)).toLinearMap ∘ₗ
      Gysin.gysinHQ l (δ J t j) (d - (t + 1)) (d - (t + 1) + 1) n i)

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

theorem str_succ_of_mem {m : ℕ} {a : ℤ} {s : ℕ} (h : s ∈ idx m a) : str a s + 1 = str (a + 1) s := by
  have := (mem_idx.1 h).1
  unfold str; omega

theorem str_succ_of_mem' {m : ℕ} {a : ℤ} {s : ℕ} (h : s ∈ idx m (a + 1)) : str a (s + 1) = str (a + 1) s + 1 := by
  have := (mem_idx.1 h).1
  unfold str; push_cast; omega

theorem str_N (a : ℤ) (s : ℕ) : str a (s + 1) = str (a + 2) s := by
  unfold str; congr 1; push_cast; ring

def prj {a b w : ℤ} (s : ℕ) (h : s ∈ idx (Fintype.card ι) a) : E1 l J a b w →ₗ[ℚ_[l]] Summand l J a b w s :=
  LinearMap.proj (R := ℚ_[l]) (φ := fun s : idx (Fintype.card ι) a => Summand l J a b w s) ⟨s, h⟩

def spectralDifferentialRestriction {m : ℕ} (a b w : ℤ) (s : ℕ) (h : s ∈ idx m a) : Summand l J a b w s →ₗ[ℚ_[l]] Summand l J (a + 1) b w s :=
  (castStr l J (n := b - 2 * s) (i := w - s) (str_succ_of_mem h) rfl rfl).toLinearMap ∘ₗ
    res l J (str a s) (b - 2 * s) (w - s)

theorem d1gys_deg (b : ℤ) (s : ℕ) : b - 2 * ((s + 1 : ℕ) : ℤ) + 2 = b - 2 * (s : ℤ) := by push_cast; ring
theorem d1gys_tw (w : ℤ) (s : ℕ) : w - ((s + 1 : ℕ) : ℤ) + 1 = w - (s : ℤ) := by push_cast; ring

def spectralDifferentialGysin (d : ℕ) {m : ℕ} (a b w : ℤ) (s : ℕ) (h : s ∈ idx m (a + 1)) :
    Summand l J a b w (s + 1) →ₗ[ℚ_[l]] Summand l J (a + 1) b w s :=
  (castStr l J (t := str (a + 1) s) rfl (d1gys_deg b s) (d1gys_tw w s)).toLinearMap ∘ₗ
    gys l J d (str (a + 1) s) (b - 2 * ((s + 1 : ℕ) : ℤ)) (w - ((s + 1 : ℕ) : ℤ)) ∘ₗ
      (castStr l J (n := b - 2 * ((s + 1 : ℕ) : ℤ)) (i := w - ((s + 1 : ℕ) : ℤ)) (str_succ_of_mem' h) rfl rfl).toLinearMap

def d1 (d : ℕ) (a b w : ℤ) : E1 l J a b w →ₗ[ℚ_[l]] E1 l J (a + 1) b w :=
  LinearMap.pi fun s' =>
    (if h : s'.1 ∈ idx (Fintype.card ι) a then spectralDifferentialRestriction l J a b w s'.1 h ∘ₗ prj l J s'.1 h else 0) +
    (if h : s'.1 + 1 ∈ idx (Fintype.card ι) a then spectralDifferentialGysin l J d a b w s'.1 s'.2 ∘ₗ prj l J (s'.1 + 1) h else 0)

def nId (a b w : ℤ) (s : ℕ) : Summand l J a b w (s + 1) ≃ₗ[ℚ_[l]] Summand l J (a + 2) (b - 2) (w - 1) s :=
  castStr l J (str_N a s) (by push_cast; ring) (by push_cast; ring)

def N (a b w : ℤ) : E1 l J a b w →ₗ[ℚ_[l]] E1 l J (a + 2) (b - 2) (w - 1) :=
  LinearMap.pi fun s' =>
    if h : s'.1 + 1 ∈ idx (Fintype.card ι) a then (nId l J a b w s'.1).toLinearMap ∘ₗ prj l J (s'.1 + 1) h else 0

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι] {Z : Scheme.{0}} (J : ι → Z.IdealSheafData)

example : idx 2 (-1) = {1} ∧ idx 2 0 = {0} ∧ idx 2 1 = {0} ∧ idx 2 2 = ∅ ∧ idx 2 (-2) = ∅ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

example (n i : ℤ) : res l J 0 n i = pullHQ l (sch.map (δ J 0 0)) n i - pullHQ l (sch.map (δ J 0 1)) n i := by
  simp [res, Fin.sum_univ_two, sub_eq_add_neg]

end GlobalTheory.EtC.WSS

namespace GlobalTheory.EtC.WSS

open GlobalTheory.EtC GlobalTheory.Strata

variable (l : ℕ) [Fact l.Prime] {ι : Type} [Fintype ι] [LinearOrder ι]

section Galois

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {V : Scheme.{0}} (p : V ⟶ Spec (CommRingCat.of k))
  (I : ι → V.IdealSheafData)

abbrev geomπ : GlobalTheory.Et.geom Ω p ⟶ V := pullback.fst _ _

abbrev geomFam : ι → (GlobalTheory.Et.geom Ω p).IdealSheafData := GlobalTheory.Strata.pull I (geomπ Ω p)

def galS (σ : Ω ≃ₐ[k] Ω) (S : Finset ι) : GlobalTheory.Strata.Y (geomFam Ω p I) S ⟶ GlobalTheory.Strata.Y (geomFam Ω p I) S :=
  (pullIso I (geomπ Ω p) S).hom ≫
    pullback.map (geomπ Ω p) (Yι I S) (geomπ Ω p) (Yι I S) (GlobalTheory.Et.galMap Ω p σ) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, GlobalTheory.Et.galMap_fst]) (by simp) ≫
    (pullIso I (geomπ Ω p) S).inv

@[reassoc (attr := simp)]
theorem galS_Yι (σ : Ω ≃ₐ[k] Ω) (S : Finset ι) :
    galS Ω p I σ S ≫ Yι (geomFam Ω p I) S = Yι (geomFam Ω p I) S ≫ GlobalTheory.Et.galMap Ω p σ := by
  show _ ≫ Yι (GlobalTheory.Strata.pull I (geomπ Ω p)) S = Yι (GlobalTheory.Strata.pull I (geomπ Ω p)) S ≫ _
  rw [← pullIso_hom_fst I (geomπ Ω p) S]
  simp only [galS, Category.assoc, Iso.inv_hom_id_assoc, pullback.map, pullback.lift_fst]

theorem galS_one (S : Finset ι) : galS Ω p I 1 S = 𝟙 _ :=
  (cancel_mono (Yι (geomFam Ω p I) S)).1 (by rw [galS_Yι, galMap_one, Category.comp_id, Category.id_comp])

theorem galS_mul (σ τ : Ω ≃ₐ[k] Ω) (S : Finset ι) : galS Ω p I (σ * τ) S = galS Ω p I σ S ≫ galS Ω p I τ S :=
  (cancel_mono (Yι (geomFam Ω p I) S)).1 (by simp [galMap_mul])

def galStr (σ : Ω ≃ₐ[k] Ω) (t : ℕ) : Ystr (geomFam Ω p I) t ⟶ Ystr (geomFam Ω p I) t :=
  Sigma.desc fun S : Idx ι t => galS Ω p I σ S.1 ≫ inj _ S

@[reassoc (attr := simp)]
theorem inj_galStr (σ : Ω ≃ₐ[k] Ω) {t : ℕ} (S : Idx ι t) :
    inj _ S ≫ galStr Ω p I σ t = galS Ω p I σ S.1 ≫ inj _ S := Sigma.ι_desc _ _

theorem galStr_one (t : ℕ) : galStr Ω p I 1 t = 𝟙 _ :=
  Ystr_hom_ext _ fun S => by rw [inj_galStr, galS_one, Category.id_comp, Category.comp_id]

theorem galStr_mul (σ τ : Ω ≃ₐ[k] Ω) (t : ℕ) : galStr Ω p I (σ * τ) t = galStr Ω p I σ t ≫ galStr Ω p I τ t :=
  Ystr_hom_ext _ fun S => by simp [galS_mul]

@[reassoc]
theorem galStr_Ystrπ (σ : Ω ≃ₐ[k] Ω) (t : ℕ) :
    galStr Ω p I σ t ≫ Ystrπ _ t = Ystrπ _ t ≫ GlobalTheory.Et.galMap Ω p σ :=
  Ystr_hom_ext _ fun S => by simp

@[reassoc]
theorem δ_galStr (σ : Ω ≃ₐ[k] Ω) (t : ℕ) (j : Fin (t + 2)) :
    δ _ t j ≫ galStr Ω p I σ t = galStr Ω p I σ (t + 1) ≫ δ _ t j :=
  Ystr_hom_ext _ fun S => by
    simp only [inj_δ_assoc, inj_galStr, inj_galStr_assoc, Category.assoc, inj_δ]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact (cancel_mono (Yι _ _)).1 (by simp)

variable (a b w : ℤ)

def galoisActionWeightSpectralE1 : Representation ℚ_[l] (Ω ≃ₐ[k] Ω) (E1 l (geomFam Ω p I) a b w) where
  toFun σ := LinearMap.pi fun s => pullHQ l (sch.map (galStr Ω p I σ (str a s))) _ _ ∘ₗ LinearMap.proj s
  map_one' := by
    refine LinearMap.ext fun x => funext fun s => ?_
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
      Function.eval, galStr_one, CategoryTheory.Functor.map_id, pullHQ_map_id, LinearMap.id_apply, Module.End.one_apply]
  map_mul' σ τ := by
    refine LinearMap.ext fun x => funext fun s => ?_
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
      Function.eval, galStr_mul, Functor.map_comp, pullHQ_map_comp, Module.End.mul_apply]

end Galois

end GlobalTheory.EtC.WSS
