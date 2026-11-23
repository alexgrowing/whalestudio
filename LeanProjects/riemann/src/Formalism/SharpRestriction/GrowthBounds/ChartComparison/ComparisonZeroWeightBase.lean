import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.SpanImageEq
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.SpanImageOfSurj
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.L2.G.Cmp

section Zero

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

def cmpZeroMu : ((Tw.fm u μ).lat 0).V →ₛₗ[c.embW u w h] (D.gat u w h).Fn :=
  (cmpSl c u w h).comp (Tw.e0 u μ).symm.toLinearMap

theorem comparison_zero_weight_base (x : ((D.fm u).lat 0).V) : cmpZeroMu c Tw u μ w h (Tw.e0 u μ x) = c.cmp u w h x := by
  show c.cmp u w h ((Tw.e0 u μ).symm (Tw.e0 u μ x)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem cmpZeroMu_li : LinearIndependent (D.gat u w h).Kf
    fun a => cmpZeroMu c Tw u μ w h (((Tw.fm u μ).lat 0).b a) := by
  refine li_basis (cmpZeroMu c Tw u μ w h) (((D.fm u).lat 0).b.map (Tw.e0 u μ)) ?_ _
  have h1 : (fun a => cmpZeroMu c Tw u μ w h ((((D.fm u).lat 0).b.map (Tw.e0 u μ)) a)) =
      fun a => c.cmp u w h (((D.fm u).lat 0).b a) := by
    funext a
    rw [Module.Basis.map_apply, comparison_zero_weight_base]
  rw [h1]
  exact c.cmp_li u w h

theorem cmpZeroMu_image : cmpZeroMu c Tw u μ w h '' (((Tw.fm u μ).lat 0).L : Set _) =
    c.cmp u w h '' (((D.fm u).lat 0).L : Set _) := by
  ext F
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(Tw.e0 u μ).symm y, ?_, rfl⟩
    rw [SetLike.mem_coe, Tw.twist_preserves_base_lattice u μ, LinearEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Tw.e0 u μ x, (Tw.twist_preserves_base_lattice u μ x).1 hx, comparison_zero_weight_base c Tw u μ w h x⟩

theorem cmpZeroMu_int : Submodule.span (D.gat u w h).O
    (cmpZeroMu c Tw u μ w h '' (((Tw.fm u μ).lat 0).L : Set _)) = (D.gat u w h).M := by
  rw [cmpZeroMu_image, c.cmp_M]

theorem cmpZeroMu_muAt : cmpZeroMu c Tw u (D.what₂.muAt w) w h = cmpZero c Tw u w h := rfl

end Zero

section KL

variable {D : D7} (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup)

def KLxMu (j : ℕ) : ((Tw.fm u μ).lat j).V →ₗ[D.what₂.LL] ((Tw.fm u μ).lat (j + 1)).V :=
  ratMap ((Tw.fm u μ).emb j) ((Tw.fm u μ).emb (j + 1)) ((Tw.fm u μ).emb_inj (j + 1)) ((D.chTw u μ).Klin j)

variable {Tw u μ}

theorem KLxMu_eq (j : ℕ) (x : ((Tw.fm u μ).lat j).V) (y : ((Tw.fm u μ).lat (j + 1)).V)
    (hxy : (Tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((Tw.fm u μ).emb j x)) : KLxMu Tw u μ j x = y :=
  ratMap_eq _ _ _ _ x y hxy

theorem KLxMu_eq_KL (j : ℕ) (hK : (Tw.fm u μ).KRat j) : KLxMu Tw u μ j = (Tw.fm u μ).KL j hK :=
  LinearMap.ext fun x => KLxMu_eq j x _ ((Tw.fm u μ).KL_spec j hK x)

theorem KLxMu_muAt (w : D.what₂.places.Pl) (j : ℕ) : KLxMu Tw u (D.what₂.muAt w) j = KLx Tw u w j := rfl

end KL

section Up

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

structure CmpUpMu where
  cmpS : ∀ j, ((Tw.fm u μ).lat (j + 1)).V →ₛₗ[c.embW u w h] Lv.Fm (j + 1)
  liS : ∀ j, j + 1 ≤ D.R.m → LinearIndependent (D.gat u w h).Kf fun a => cmpS j (((Tw.fm u μ).lat (j + 1)).b a)

variable {c Tw u μ w h Lv}

def CmpUpMu.cmp (S : CmpUpMu c Tw u μ w h Lv) : (j : ℕ) → ((Tw.fm u μ).lat j).V →ₛₗ[c.embW u w h] Lv.Fm j
  | 0 => cmpZeroMu c Tw u μ w h
  | j + 1 => S.cmpS j

theorem CmpUpMu.li (S : CmpUpMu c Tw u μ w h Lv) : ∀ j, j ≤ D.R.m →
    LinearIndependent (D.gat u w h).Kf fun a => S.cmp j (((Tw.fm u μ).lat j).b a)
  | 0, _ => cmpZeroMu_li c Tw u μ w h
  | j + 1, hj => S.liS j hj

theorem CmpUpMu.inj (S : CmpUpMu c Tw u μ w h Lv) (j : ℕ) (hj : j ≤ D.R.m) : Function.Injective (S.cmp j) :=
  Formalism.L2.G.Cmp.inj_of_li (S.cmp j) ((Tw.fm u μ).lat j).b (S.li j hj)

theorem CmpUpMu.cmp_zero (S : CmpUpMu c Tw u μ w h Lv) (x : ((D.fm u).lat 0).V) :
    S.cmp 0 (Tw.e0 u μ x) = c.cmp u w h x := comparison_zero_weight_base c Tw u μ w h x

open Classical in

def chainMu (S : CmpUpMu c Tw u μ w h Lv) : Chain Lv where
  Kz j := if hj : j < D.R.m then
      extK (S.cmp j) (S.cmp (j + 1)) ((Tw.fm u μ).lat j).b (S.li j hj.le) (KLxMu Tw u μ j)
    else 0

theorem chainMu_Kz (S : CmpUpMu c Tw u μ w h Lv) (j : ℕ) (hj : j < D.R.m) :
    (chainMu S).Kz j = extK (S.cmp j) (S.cmp (j + 1)) ((Tw.fm u μ).lat j).b (S.li j hj.le) (KLxMu Tw u μ j) :=
  dif_pos hj

theorem chainMu_apply (S : CmpUpMu c Tw u μ w h Lv) (j : ℕ) (hj : j < D.R.m) (x : ((Tw.fm u μ).lat j).V) :
    (chainMu S).Kz j (S.cmp j x) = S.cmp (j + 1) (KLxMu Tw u μ j x) := by
  rw [chainMu_Kz S j hj, extK_apply]

theorem chainMu_cmp_K (S : CmpUpMu c Tw u μ w h Lv) : ∀ j, j < D.R.m →
    ∀ (x : ((Tw.fm u μ).lat j).V) (y : ((Tw.fm u μ).lat (j + 1)).V),
    (Tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((Tw.fm u μ).emb j x) →
    S.cmp (j + 1) y = (chainMu S).Kz j (S.cmp j x) := by
  intro j hj x y hxy
  rw [chainMu_apply S j hj, KLxMu_eq j x y hxy]

theorem chainMu_KL (S : CmpUpMu c Tw u μ w h Lv) (j : ℕ) (hj : j < D.R.m) (hK : (Tw.fm u μ).KRat j)
    (x : ((Tw.fm u μ).lat j).V) : (chainMu S).Kz j (S.cmp j x) = S.cmp (j + 1) ((Tw.fm u μ).KL j hK x) := by
  rw [chainMu_apply S j hj, KLxMu_eq_KL j hK]

theorem chainMu_unique (S : CmpUpMu c Tw u μ w h Lv) (Ch : Chain Lv) (j : ℕ) (hj : j < D.R.m)
    (hK : (Tw.fm u μ).KRat j)
    (hC : ∀ (x : ((Tw.fm u μ).lat j).V) (y : ((Tw.fm u μ).lat (j + 1)).V),
      (Tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((Tw.fm u μ).emb j x) → S.cmp (j + 1) y = Ch.Kz j (S.cmp j x))
    (F : Lv.Fm j) (hF : F ∈ spanK (S.cmp j)) : Ch.Kz j F = (chainMu S).Kz j F := by
  rw [chainMu_Kz S j hj]
  refine extK_unique _ _ _ _ _ (Ch.Kz j) (fun x => ?_) F hF
  rw [KLxMu_eq_KL j hK]
  exact (hC x _ ((Tw.fm u μ).KL_spec j hK x)).symm

theorem chainMu_chainK_mem (S : CmpUpMu c Tw u μ w h Lv) (j : ℕ) (hj : j ≤ D.R.m) (F : Lv.Fm 0)
    (hF : F ∈ spanK (S.cmp 0)) : (chainMu S).chainK j F ∈ spanK (S.cmp j) := by
  cases j with
  | zero => exact hF
  | succ j =>
    show (chainMu S).Kz j ((chainMu S).chainK j F) ∈ _
    rw [chainMu_Kz S j (by omega)]
    exact extK_mem_spanK _ _ _ _ _ _

theorem chainK_forcedMu (S : CmpUpMu c Tw u μ w h Lv) (Ch : Chain Lv)
    (hK : ∀ j, j < D.R.m → (Tw.fm u μ).KRat j)
    (hC : ∀ j, j < D.R.m → ∀ (x : ((Tw.fm u μ).lat j).V) (y : ((Tw.fm u μ).lat (j + 1)).V),
      (Tw.fm u μ).emb (j + 1) y = (D.chTw u μ).K j ((Tw.fm u μ).emb j x) → S.cmp (j + 1) y = Ch.Kz j (S.cmp j x))
    (j : ℕ) (hj : j ≤ D.R.m) (F : Lv.Fm 0) (hF : F ∈ spanK (S.cmp 0)) :
    Ch.chainK j F = (chainMu S).chainK j F := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show Ch.Kz j (Ch.chainK j F) = (chainMu S).Kz j ((chainMu S).chainK j F)
    rw [ih (by omega)]
    exact chainMu_unique S Ch j (by omega) (hK j (by omega)) (hC j (by omega)) _
      (chainMu_chainK_mem S j (by omega) F hF)

theorem li_stepMu (j : ℕ) (f : ((Tw.fm u μ).lat j).V →ₛₗ[c.embW u w h] Lv.Fm j) (hinj : Function.Injective f)
    (hrat : ∀ x, RatFnP (Fl.Pj j) (Lv.comp j) (c.embW u w h) (f x)) :
    LinearIndependent (D.gat u w h).Kf fun a => f (((Tw.fm u μ).lat j).b a) :=
  li_of_rat (c.embW u w h) (evP (Fl.Pj j) (Lv.comp j)) f.toAddMonoidHom (eq_zero_of_forall_evalCoeff_eq_zero (Fl.Pj j) (Lv.comp j))
    (fun a x => LinearMap.map_smulₛₗ f a x) (fun x => (isRational_iff (Fl.Pj j) (Lv.comp j) (c.embW u w h) (f x)).1 (hrat x))
    hinj _ ((Tw.fm u μ).lat j).b.linearIndependent

def CmpUpMu.ofRat (cmpS : ∀ j, ((Tw.fm u μ).lat (j + 1)).V →ₛₗ[c.embW u w h] Lv.Fm (j + 1))
    (injS : ∀ j, j + 1 ≤ D.R.m → Function.Injective (cmpS j))
    (ratS : ∀ j, j + 1 ≤ D.R.m → ∀ x, RatFnP (Fl.Pj (j + 1)) (Lv.comp (j + 1)) (c.embW u w h) (cmpS j x)) :
    CmpUpMu c Tw u μ w h Lv where
  cmpS := cmpS
  liS := fun j hj => li_stepMu (j + 1) (cmpS j) (injS j hj) (ratS j hj)

end Up

section Steps

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

structure StepsMu where
  cmpS : ∀ j, ((Tw.fm u μ).lat (j + 1)).V →ₛₗ[c.embW u w h] Lv.Fm (j + 1)
  injS : ∀ j, j + 1 ≤ D.R.m → Function.Injective (cmpS j)
  ratS : ∀ j, j + 1 ≤ D.R.m → ∀ x, RatFnP (Fl.Pj (j + 1)) (Lv.comp (j + 1)) (c.embW u w h) (cmpS j x)
  latS : ∀ j, j + 1 ≤ D.R.m → ∀ x, cmpS j x ∈ Lv.Int (j + 1) ↔
    x ∈ Formalism.BasicNotions.locW D.what₂.places w ((Tw.fm u μ).lat (j + 1)).L
  surjS : ∀ j, j + 1 ≤ D.R.m → ∀ F ∈ Lv.Int (j + 1),
    RatFnP (Fl.Pj (j + 1)) (Lv.comp (j + 1)) (c.embW u w h) F → ∃ x, cmpS j x = F

variable {c Tw u μ w h Lv}

def StepsMu.up (X : StepsMu c Tw u μ w h Lv) : CmpUpMu c Tw u μ w h Lv := CmpUpMu.ofRat X.cmpS X.injS X.ratS

theorem StepsMu.up_cmp_succ (X : StepsMu c Tw u μ w h Lv) (j : ℕ) : X.up.cmp (j + 1) = X.cmpS j := rfl

theorem StepsMu.intS (X : StepsMu c Tw u μ w h Lv) (hd : DescUp c u w h Lv) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    Submodule.span (D.gat u w h).O
      (X.up.cmp (j + 1) '' (((Tw.fm u μ).lat (j + 1)).L : Set ((Tw.fm u μ).lat (j + 1)).V)) = Lv.Int (j + 1) :=
  span_image_of_surj (Fl.Pj (j + 1)) (Lv.comp (j + 1)) (c.embW u w h) (Lv.Int (j + 1)) (X.cmpS j)
    (Formalism.BasicNotions.intW D.what₂.places w) (fun a ha => (c.embW_int u w h a).1 ha) _ (X.surjS j hj) (X.latS j hj) (hd j hj)

theorem StepsMu.cmp_int (X : StepsMu c Tw u μ w h Lv) (hd : DescUp c u w h Lv) : ∀ j, j ≤ D.R.m →
    Submodule.span (D.gat u w h).O (X.up.cmp j '' (((Tw.fm u μ).lat j).L : Set ((Tw.fm u μ).lat j).V)) = Lv.Int j
  | 0, _ => cmpZeroMu_int c Tw u μ w h
  | j + 1, hj => X.intS hd j hj

end Steps

section ValGen

variable {LL Kf O V W ι : Type} [Field LL] [Field Kf] [CommRing O] [Algebra O Kf] [AddCommGroup V] [Module LL V]
  [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W] {e : LL →+* Kf}

theorem val_quot_nonneg (val : AddValuation LL (WithTop ℤ)) {a d : LL} (ha : a ≠ 0) (hle : val a ≤ val d) :
    0 ≤ val (a⁻¹ * d) := by
  have h1 : val d = val a + val (a⁻¹ * d) := by rw [← AddValuation.map_mul, mul_inv_cancel_left₀ ha]
  by_contra hneg
  rw [not_le] at hneg
  have hatop : val a ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    exact ha
  have h2 : val a + val (a⁻¹ * d) < val a + 0 := WithTop.add_lt_add_left hatop hneg
  rw [add_zero, ← h1] at h2
  exact absurd hle (not_le.2 h2)

theorem val_gen (f : V →ₛₗ[e] W) (A : Subring LL) (val : AddValuation LL (WithTop ℤ)) (hval : ∀ a, a ∈ A ↔ 0 ≤ val a)
    (b : Module.Basis ι LL V) (hli : LinearIndependent Kf fun i => f (b i)) (N : Submodule O W)
    (hN : N ≤ Submodule.span O (Set.range fun i => f (b i))) (t : Kf) (y : V) (hy : f y ∈ scale t N) :
    ∃ (a : LL) (z : V), z ∈ Submodule.span A (Set.range b) ∧ y = a • z ∧
      (a = 0 ∨ ∃ o : O, e a = t * algebraMap O Kf o) := by
  obtain ⟨F, hF, hFy⟩ := hy
  change t • F = f y at hFy
  obtain ⟨l, hl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 (hN hF)
  by_cases hy0 : y = 0
  · exact ⟨0, 0, Submodule.zero_mem _, by rw [hy0, smul_zero], Or.inl rfl⟩
  have hsupp : (b.repr y).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h0
    exact hy0 (b.repr.map_eq_zero_iff.1 h0)
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image _ (fun i => val (b.repr y i)) hsupp
  have ha : b.repr y i0 ≠ 0 := Finsupp.mem_support_iff.1 hi0
  have hyy : y = ∑ i ∈ (b.repr y).support, (b.repr y) i • b i := by
    have h1 := (b.linearCombination_repr y).symm
    rwa [Finsupp.linearCombination_apply, Finsupp.sum] at h1
  have e1 : f y = Finsupp.linearCombination Kf (fun i => f (b i)) ((b.repr y).mapRange e (map_zero e)) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (h := fun i (a : Kf) => a • f (b i)) (fun i => zero_smul _ _)]
    have h1 := congrArg f hyy
    rw [map_sum] at h1
    rw [h1]
    exact Finset.sum_congr rfl fun i _ => LinearMap.map_smulₛₗ f _ _
  have e2 : t • F = Finsupp.linearCombination Kf (fun i => f (b i))
      (l.mapRange (fun o => t * algebraMap O Kf o) (by rw [map_zero, mul_zero])) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (h := fun i (a : Kf) => a • f (b i)) (fun i => zero_smul _ _), ← hl, Finsupp.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show t • (l i • f (b i)) = (t * algebraMap O Kf (l i)) • f (b i)
    rw [mul_smul, algebraMap_smul]
  have h3 := hli (e1.symm.trans (hFy.symm.trans e2))
  have h4 : e (b.repr y i0) = t * algebraMap O Kf (l i0) := by
    have := DFunLike.congr_fun h3 i0
    rwa [Finsupp.mapRange_apply, Finsupp.mapRange_apply] at this
  refine ⟨b.repr y i0, (b.repr y i0)⁻¹ • y, ?_, by rw [smul_smul, mul_inv_cancel₀ ha, one_smul], Or.inr ⟨l i0, h4⟩⟩
  have hz : (b.repr y i0)⁻¹ • y = ∑ i ∈ (b.repr y).support, ((b.repr y i0)⁻¹ * (b.repr y) i) • b i := by
    calc (b.repr y i0)⁻¹ • y = (b.repr y i0)⁻¹ • ∑ i ∈ (b.repr y).support, (b.repr y) i • b i := by rw [← hyy]
      _ = _ := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  rw [hz]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hc : (b.repr y i0)⁻¹ * (b.repr y) i ∈ A := (hval _).2 (val_quot_nonneg val ha (hmin i hi))
  exact Submodule.smul_mem (Submodule.span A (Set.range b)) ⟨_, hc⟩ (Submodule.subset_span ⟨i, rfl⟩)

theorem span_image_le (f : V →ₛₗ[e] W) (A : Subring LL) (hA : ∀ a ∈ A, e a ∈ Set.range (algebraMap O Kf))
    (b : ι → V) (S : Set V) (hS : S ⊆ Submodule.span A (Set.range b)) :
    Submodule.span O (f '' S) ≤ Submodule.span O (Set.range fun i => f (b i)) := by
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  have hx' := hS hx
  clear hx
  show f x ∈ _
  induction hx' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ h1 h2 => rw [map_add]; exact Submodule.add_mem _ h1 h2
  | smul a y _ h1 =>
    obtain ⟨o, ho⟩ := hA a.1 a.2
    have : f (a • y) = o • f y := by
      rw [Subring.smul_def, LinearMap.map_smulₛₗ, ← ho, algebraMap_smul]
    rw [this]
    exact Submodule.smul_mem _ _ h1

end ValGen

section Val

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

def ValScalar : Prop :=
  ∀ (a : D.what₂.LL) (s : ℝ) (ϖ : (D.gat u w h).O), a ≠ 0 → Irreducible ϖ →
    (∃ o : (D.gat u w h).O, c.embW u w h a =
      (algebraMap (D.gat u w h).O (D.gat u w h).Kf ϖ) ^ ⌈s * vUnit (D.gat u w h)⌉ *
        algebraMap (D.gat u w h).O (D.gat u w h).Kf o) →
    DV.ur D w s ≤ (vAdd (D.plEq w) a : ℝ)

def LocFree (j : ℕ) : Prop :=
  ∃ (ι : Type) (b : Module.Basis ι D.what₂.LL ((Tw.fm u μ).lat j).V),
    Formalism.BasicNotions.locW D.what₂.places w ((Tw.fm u μ).lat j).L =
      Submodule.span (Formalism.BasicNotions.intW D.what₂.places w) (Set.range b)

variable {c Tw u μ w h} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

theorem CmpUpMu.val_of (S : CmpUpMu c Tw u μ w h Lv) (j : ℕ) (hj : j ≤ D.R.m)
    (hint : Submodule.span (D.gat u w h).O (S.cmp j '' (((Tw.fm u μ).lat j).L : Set ((Tw.fm u μ).lat j).V)) = Lv.Int j)
    (hs : ValScalar c u w h) (hf : LocFree Tw u μ w j) (y : ((Tw.fm u μ).lat j).V) (s : ℝ)
    (hv : vGeLat (D.gat u w h) (Lv.Int j) (S.cmp j y) s) : WeilJacquetShalikaLaw.VGe D w ((Tw.fm u μ).lat j).L y s := by
  obtain ⟨ϖ, hϖ, hmem⟩ := hv
  obtain ⟨ι, b, hb⟩ := hf
  have hli : LinearIndependent (D.gat u w h).Kf fun i => S.cmp j (b i) :=
    li_of_li (S.cmp j) ((Tw.fm u μ).lat j).b (S.li j hj) b b.linearIndependent
  have hN : Lv.Int j ≤ Submodule.span (D.gat u w h).O (Set.range fun i => S.cmp j (b i)) := by
    rw [← hint]
    refine span_image_le (S.cmp j) (Formalism.BasicNotions.intW D.what₂.places w) (fun a ha => (c.embW_int u w h a).1 ha) b _ ?_
    intro x hx
    rw [← hb]
    exact Submodule.subset_span hx
  obtain ⟨a, z, hz, hy, ha⟩ := val_gen (S.cmp j) (Formalism.BasicNotions.intW D.what₂.places w) (D.what₂.places.val w)
    (fun _ => Iff.rfl) b hli (Lv.Int j) hN _ y hmem
  refine ⟨a, z, by rw [hb]; exact hz, hy, ?_⟩
  by_cases ha0 : a = 0
  · exact Or.inl ha0
  · exact Or.inr (hs a s ϖ ha0 hϖ (ha.resolve_left ha0))

end Val

end Formalism.MainNotions.G.CmpJ

end
