import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing

noncomputable section

namespace GlobalTheory.FlagMod

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

section Tri

variable {R : Type} [CommRing R] {m : ℕ}

theorem tri_mul_diag {B B' : Matrix (Fin m) (Fin m) R} (h : B.BlockTriangular id) (h' : B'.BlockTriangular id)
    (i : Fin m) : (B * B') i i = B i i * B' i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with e | e
    · rw [h e, zero_mul]
    · rw [h' e, mul_zero]
  · simp

variable {N : Type} [AddCommGroup N] [Module R N]

def initSpan (R : Type) [CommRing R] [Module R N] (v : Fin m → N) (i : ℕ) : Submodule R N :=
  Submodule.span R (v '' {j | (j : ℕ) < i})

theorem mem_initSpan {v : Fin m → N} {i : ℕ} {w : N} :
    w ∈ initSpan R v i ↔ ∃ a : Fin m → R, (∀ j : Fin m, i ≤ j → a j = 0) ∧ ∑ j, a j • v j = w := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      refine ⟨Pi.single j 1, fun k hk => Pi.single_eq_of_ne (fun e => ?_) _, by simp [Pi.single_apply]⟩
      subst e
      exact absurd hj (not_lt.2 hk)
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨r • a, fun j hj => by simp [ha j hj], by simp [Finset.smul_sum, smul_smul]⟩
  · rintro ⟨a, ha, rfl⟩
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < i
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [ha j (not_lt.1 hj), zero_smul]; exact Submodule.zero_mem _

theorem initSpan_mono (v : Fin m → N) {i i' : ℕ} (h : i ≤ i') : initSpan R v i ≤ initSpan R v i' :=
  Submodule.span_mono (Set.image_mono fun _ hj => lt_of_lt_of_le hj h)

theorem initSpan_le_of_tri {v v' : Fin m → N} {B : Matrix (Fin m) (Fin m) R} (hB : B.BlockTriangular id)
    (h : ∀ i, v' i = ∑ j, B j i • v j) (i : ℕ) : initSpan R v' i ≤ initSpan R v i := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, hj, rfl⟩
  exact mem_initSpan.2 ⟨fun k => B k j, fun k hk => hB (show (j : ℕ) < k from lt_of_lt_of_le (show (j : ℕ) < i from hj) hk), (h j).symm⟩

theorem sub_diag_mem_initSpan {v v' : Fin m → N} {B : Matrix (Fin m) (Fin m) R} (hB : B.BlockTriangular id)
    (h : ∀ i, v' i = ∑ j, B j i • v j) (i : Fin m) : v' i - B i i • v i ∈ initSpan R v i := by
  refine mem_initSpan.2 ⟨fun k => if k = i then 0 else B k i, fun k hk => ?_, ?_⟩
  · beta_reduce
    split_ifs with e
    · rfl
    · exact hB (show i < k from lt_of_le_of_ne hk (Ne.symm e))
  · beta_reduce
    rw [h, eq_sub_iff_add_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun j => B j i • v j) (Finset.mem_univ i), if_pos rfl, zero_smul, zero_add, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k hk => by rw [if_neg (Finset.ne_of_mem_erase hk)]

theorem existsUnique_sub_mem_initSpan {v : Fin m → N} (hv : LinearIndependent R v) (i : Fin m) {w : N}
    (hw : w ∈ initSpan R v (i + 1)) : ∃! a : R, w - a • v i ∈ initSpan R v i := by
  obtain ⟨b, hb, rfl⟩ := mem_initSpan.1 hw
  have key : ∀ a : R, ∑ j, b j • v j - a • v i = ∑ j, (b - Pi.single i a : Fin m → R) j • v j := fun a => by
    simp [sub_smul, Finset.sum_sub_distrib, Pi.single_apply]
  refine ⟨b i, mem_initSpan.2 ⟨b - Pi.single i (b i), fun j hj => ?_, (key _).symm⟩, fun a ha => ?_⟩
  · by_cases e : j = i
    · subst e; simp
    · have : (i : ℕ) + 1 ≤ j := lt_of_le_of_ne hj fun h => e (Fin.ext h.symm)
      simp [hb j this, Pi.single_eq_of_ne e]
  · obtain ⟨d, hd, h⟩ := mem_initSpan.1 ha
    rw [key] at h
    have := (Fintype.linearIndependent_iffₛ.1 hv) _ _ h i
    rw [hd i le_rfl] at this
    simp only [Pi.sub_apply, Pi.single_eq_same] at this
    exact (sub_eq_zero.1 this.symm).symm

end Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

structure Frames (Y : Model Xo c β) {Z : Scheme.{0}} (π : Z ⟶ Y.X) where
  J : Type
  U : J → Z.Opens
  cover : ⨆ k, U k = ⊤
  M : J → GChart Y
  le : ∀ k, U k ≤ π ⁻¹ᵁ (M k).U
  u : ∀ (k : J) (σ : E →+* ℂ), Matrix (Fin (M k).n) (Fin (Dw.mult σ)) Γ(Z, U k)
  split : ∀ k σ, ∃ w : Matrix (Fin (Dw.mult σ)) (Fin (M k).n) Γ(Z, U k), w * u k σ = 1
  tri : ∀ k k' σ, ∃ B : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Z, U k ⊓ U k'), B.BlockTriangular id ∧
    (chg (M k).toMChart (M k').toMChart).map
        (π.appLE ((M k).U ⊓ (M k').U) (U k ⊓ U k') (inf_le_inf (le k) (le k'))).hom *
      (u k' σ).map (resG Z inf_le_right) = (u k σ).map (resG Z inf_le_left) * B

namespace Frames

variable {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {S S' : Type} [CommRing S] [CommRing S']

theorem inM {k : F.J} {z : Sp S ⟶ Z} (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) :
    ⊤ ≤ x ⁻¹ᵁ (F.M k).U := hx ▸ le_preimage_map π (F.le k) hz

def uAt (k : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (σ : E →+* ℂ) :
    Matrix (Fin (F.M k).n) (Fin (Dw.mult σ)) S := (F.u k σ).map (ev z _ hz)

def vecAt (k : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (σ : E →+* ℂ)
    (i : Fin (Dw.mult σ)) : TanM x Y.t.G :=
  vec (F.M k).toMChart x (F.inM hz hx) (fun j => F.uAt k z hz σ j i)

theorem sum_vecAt (k : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (σ : E →+* ℂ)
    (a : Fin (Dw.mult σ) → S) : ∑ i, a i • F.vecAt k z hz hx σ i =
      vec (F.M k).toMChart x (F.inM hz hx) ((F.uAt k z hz σ).mulVec a) := by
  simp only [vecAt, ← map_smul, ← map_sum]
  congr 1
  funext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, _root_.mul_comm]

theorem uAt_split (k : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (σ : E →+* ℂ) :
    ∃ w : Matrix (Fin (Dw.mult σ)) (Fin (F.M k).n) S, w * F.uAt k z hz σ = 1 := by
  obtain ⟨w, hw⟩ := F.split k σ
  exact ⟨w.map (ev z _ hz), by rw [uAt, ← Matrix.map_mul, hw, Matrix.map_one _ (map_zero _) (map_one _)]⟩

theorem uAt_spMap (k : F.J) (φ : S →+* S') (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k)
    (hz' : ⊤ ≤ (spMap φ ≫ z) ⁻¹ᵁ F.U k) (σ : E →+* ℂ) : F.uAt k (spMap φ ≫ z) hz' σ = (F.uAt k z hz σ).map φ := by
  rw [uAt, uAt, ev_spMap φ z _ hz, Matrix.map_map]; rfl

theorem linearIndependent_vecAt (k : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x)
    (σ : E →+* ℂ) : LinearIndependent S (F.vecAt k z hz hx σ) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  rw [sum_vecAt, LinearEquiv.map_eq_zero_iff] at ha
  obtain ⟨w, hw⟩ := F.uAt_split k z hz σ
  have := congrArg w.mulVec ha
  rw [Matrix.mulVec_mulVec, hw, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  exact congrFun this

theorem tanPull_vecAt (k : F.J) (φ : S →+* S') (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k)
    (hz' : ⊤ ≤ (spMap φ ≫ z) ⁻¹ᵁ F.U k) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) {x' : Sp S' ⟶ Y.X}
    (hx' : (spMap φ ≫ z) ≫ π = x') (e : spMap φ ≫ x = x') (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    tanPull φ e (F.vecAt k z hz hx σ i) = F.vecAt k (spMap φ ≫ z) hz' hx' σ i := by
  rw [vecAt, vecAt, tanPull_vec _ φ e _ (F.inM hz' hx'), uAt_spMap F k φ z hz]
  rfl

def B (k k' : F.J) (σ : E →+* ℂ) : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Z, F.U k ⊓ F.U k') :=
  (F.tri k k' σ).choose

theorem B_tri (k k' : F.J) (σ : E →+* ℂ) : (F.B k k' σ).BlockTriangular id := (F.tri k k' σ).choose_spec.1

theorem B_map_tri (k k' : F.J) (σ : E →+* ℂ) (f : Γ(Z, F.U k ⊓ F.U k') →+* S) :
    ((F.B k k' σ).map f).BlockTriangular id := fun i j h => by
  rw [Matrix.map_apply, F.B_tri k k' σ h, map_zero]

theorem chg_uAt (k k' : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hz' : ⊤ ≤ z ⁻¹ᵁ F.U k')
    (hh : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k')) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x)
    (hM : ⊤ ≤ x ⁻¹ᵁ ((F.M k).U ⊓ (F.M k').U)) (σ : E →+* ℂ) :
    (chg (F.M k).toMChart (F.M k').toMChart).map (ev x _ hM) * F.uAt k' z hz' σ =
      F.uAt k z hz σ * (F.B k k' σ).map (ev z _ hh) := by
  subst hx
  have e := congrArg (fun A => Matrix.map A (ev z _ hh)) (F.tri k k' σ).choose_spec.2
  have e' := (Matrix.map_mul (f := ev z _ hh)).symm.trans (e.trans (Matrix.map_mul (f := ev z _ hh)))
  convert e' using 2
  · ext i j; exact (ev_appLE z π _ hh hM _).symm
  · ext i j; exact (ev_res z _ hh hz' _).symm
  · ext i j; exact (ev_res z _ hh hz _).symm
  · rfl

theorem vecAt_eq_sum (k k' : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hz' : ⊤ ≤ z ⁻¹ᵁ F.U k')
    (hh : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k')) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    F.vecAt k' z hz' hx σ i = ∑ j, (F.B k k' σ).map (ev z _ hh) j i • F.vecAt k z hz hx σ j := by
  have hM := le_preimage_inf (F.inM hz hx) (F.inM hz' hx)
  rw [sum_vecAt, vecAt, ← vec_chg (F.M k).toMChart (F.M k').toMChart x (F.inM hz hx) (F.inM hz' hx) hM]
  congr 1
  funext j
  exact congrFun (congrFun (F.chg_uAt k k' z hz hz' hh hx hM σ) j) i

theorem B_map_mul (k k' k'' : F.J) (z : Sp S ⟶ Z) (h₁ : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k'))
    (h₂ : ⊤ ≤ z ⁻¹ᵁ (F.U k' ⊓ F.U k'')) (h₃ : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k'')) (σ : E →+* ℂ) :
    (F.B k k' σ).map (ev z _ h₁) * (F.B k' k'' σ).map (ev z _ h₂) = (F.B k k'' σ).map (ev z _ h₃) := by
  have a := le_preimage_mono inf_le_left h₁
  have b := le_preimage_mono inf_le_right h₁
  have d := le_preimage_mono inf_le_right h₂
  ext j i
  have e := F.vecAt_eq_sum k' k'' z b d h₂ rfl σ i
  rw [F.vecAt_eq_sum k k'' z a d h₃ rfl σ i] at e
  simp only [F.vecAt_eq_sum k k' z a b h₁ rfl σ, Finset.smul_sum, smul_smul] at e
  rw [Finset.sum_comm] at e
  simp only [← Finset.sum_smul] at e
  have := (Fintype.linearIndependent_iffₛ.1 (F.linearIndependent_vecAt k z a rfl σ)) _ _ e j
  rw [this, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _

theorem B_map_self (k : F.J) (z : Sp S ⟶ Z) (h : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k)) (σ : E →+* ℂ) :
    (F.B k k σ).map (ev z _ h) = 1 := by
  have a := le_preimage_mono inf_le_left h
  ext j i
  have e := F.vecAt_eq_sum k k z a a h rfl σ i
  refine ((Fintype.linearIndependent_iffₛ.1 (F.linearIndependent_vecAt k z a rfl σ))
    (fun j => (1 : Matrix _ _ S) j i) (fun j => (F.B k k σ).map (ev z _ h) j i) ?_ j).symm
  rw [← e]
  simp [Matrix.one_apply]

theorem ev_B_diag_mul (k k' k'' : F.J) (z : Sp S ⟶ Z) (h₁ : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k'))
    (h₂ : ⊤ ≤ z ⁻¹ᵁ (F.U k' ⊓ F.U k'')) (h₃ : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k'')) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    ev z _ h₁ (F.B k k' σ i i) * ev z _ h₂ (F.B k' k'' σ i i) = ev z _ h₃ (F.B k k'' σ i i) :=
  (tri_mul_diag (F.B_map_tri k k' σ _) (F.B_map_tri k' k'' σ _) i).symm.trans
    (congrFun (congrFun (F.B_map_mul k k' k'' z h₁ h₂ h₃ σ) i) i)

theorem isUnit_B_diag (k k' : F.J) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) : IsUnit (F.B k k' σ i i) := by
  refine IsUnit.of_mul_eq_one (resG Z (le_inf inf_le_right inf_le_left) (F.B k' k σ i i)) (ext_ev fun S _ z hz => ?_)
  have h₂ : ⊤ ≤ z ⁻¹ᵁ (F.U k' ⊓ F.U k) := le_preimage_mono (le_inf inf_le_right inf_le_left) hz
  have h₃ : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k) := le_preimage_mono (le_inf inf_le_left inf_le_left) hz
  rw [map_mul, ev_res z _ hz h₂, F.ev_B_diag_mul k k' k z hz h₂ h₃, map_one]
  exact (congrFun (congrFun (F.B_map_self k z h₃ σ) i) i).trans (Matrix.one_apply_eq i)

def T (k k' : F.J) : Ix Dw → Γ(Z, F.U k ⊓ F.U k')ˣ
  | none => Units.map (π.appLE ((F.M k).U ⊓ (F.M k').U) (F.U k ⊓ F.U k') (inf_le_inf (F.le k) (F.le k'))).hom.toMonoidHom
      (thUnit (F.M k) (F.M k'))
  | some p => (F.isUnit_B_diag k k' p.1 p.2).unit

theorem T_some (k k' : F.J) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) : (F.T k k' (some ⟨σ, i⟩)).val = F.B k k' σ i i := rfl

theorem ev_T_none (k k' : F.J) (z : Sp S ⟶ Z) (h : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k')) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x)
    (hM : ⊤ ≤ x ⁻¹ᵁ ((F.M k).U ⊓ (F.M k').U)) :
    ev z _ h (F.T k k' none).val = ev x _ hM (thRat (F.M k) (F.M k')) := by
  subst hx
  exact ev_appLE z π _ h hM _

def TAt (k k' : F.J) (z : Sp S ⟶ Z) (h : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k')) (ix : Ix Dw) : Sˣ :=
  Units.map (ev z _ h).toMonoidHom (F.T k k' ix)

theorem TAt_mul (k k' k'' : F.J) (z : Sp S ⟶ Z) (h₁ : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k'))
    (h₂ : ⊤ ≤ z ⁻¹ᵁ (F.U k' ⊓ F.U k'')) (h₃ : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k'')) :
    F.TAt k k' z h₁ * F.TAt k' k'' z h₂ = F.TAt k k'' z h₃ := by
  funext ix
  apply Units.ext
  rcases ix with _ | ⟨σ, i⟩
  · have a := F.inM (le_preimage_mono inf_le_left h₁) rfl
    have b := F.inM (le_preimage_mono inf_le_right h₁) rfl
    have d := F.inM (le_preimage_mono inf_le_right h₂) rfl
    exact (congrArg₂ (· * ·) (F.ev_T_none k k' z h₁ rfl (le_preimage_inf a b))
      (F.ev_T_none k' k'' z h₂ rfl (le_preimage_inf b d))).trans
      ((ev_thRat_mul _ _ _ _ _ _ (le_preimage_inf a d)).trans (F.ev_T_none k k'' z h₃ rfl _).symm)
  · exact F.ev_B_diag_mul k k' k'' z h₁ h₂ h₃ σ i

def line (ix : Ix Dw) : LB Z := ⟨F.J, F.U, fun k k' => F.T k k' ix⟩

def gr (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) : LB Z := F.line (some ⟨σ, i⟩)

open Classical in

def LL (e : Ix Dw → ℤ) : LB Z := ⟨F.J, F.U, fun k k' => ∏ ix, F.T k k' ix ^ (-e ix)⟩

def de : LB Z := GlobalTheory.CechPic.dual (F.line none)

def detOm : LB Z := ⟨F.J, F.U, fun k k' => (Units.map
  (π.appLE ((F.M k).U ⊓ (F.M k').U) (F.U k ⊓ F.U k') (inf_le_inf (F.le k) (F.le k'))).hom.toMonoidHom
    (detChg (F.M k).toMChart (F.M k').toMChart))⁻¹⟩

theorem isLB_line (ix : Ix Dw) : (F.line ix).IsLB :=
  isLB_of_ev _ F.cover fun k k' k'' _ _ z h₁ h₂ h₃ => congrArg Units.val (congrFun (F.TAt_mul k k' k'' z h₁ h₂ h₃) ix)

theorem isLB_gr (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) : (F.gr σ i).IsLB := F.isLB_line _

theorem isLB_de : F.de.IsLB := GlobalTheory.CechPic.isLB_dual (F.isLB_line none)

open Classical in
theorem ev_LL_g (e : Ix Dw → ℤ) (k k' : F.J) (z : Sp S ⟶ Z) (h : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k')) :
    ev z _ h ((F.LL e).g k k').val = (∏ ix, F.TAt k k' z h ix ^ (-e ix)).val := by
  show (Units.map (ev z _ h).toMonoidHom (∏ ix, F.T k k' ix ^ (-e ix))).val = _
  simp only [map_prod, map_zpow, TAt]

theorem isLB_LL (e : Ix Dw → ℤ) : (F.LL e).IsLB :=
  isLB_of_ev _ F.cover fun k k' k'' _ _ z h₁ h₂ h₃ => by
    refine (congrArg₂ (· * ·) (F.ev_LL_g e k k' z h₁) (F.ev_LL_g e k' k'' z h₂)).trans
      (Eq.trans ?_ (F.ev_LL_g e k k'' z h₃).symm)
    rw [← Units.val_mul, ← Finset.prod_mul_distrib, ← F.TAt_mul k k' k'' z h₁ h₂ h₃]
    simp only [Pi.mul_apply, mul_zpow]

theorem isLB_detOm : F.detOm.IsLB :=
  GlobalTheory.CechPic.isLB_dual (A := ⟨F.J, F.U, fun k k' => Units.map
    (π.appLE ((F.M k).U ⊓ (F.M k').U) (F.U k ⊓ F.U k') (inf_le_inf (F.le k) (F.le k'))).hom.toMonoidHom
      (detChg (F.M k).toMChart (F.M k').toMChart)⟩)
    (isLB_of_ev _ F.cover fun k k' k'' _ _ z h₁ h₂ h₃ => by
      have a := F.inM (le_preimage_mono inf_le_left h₁) rfl
      have b := F.inM (le_preimage_mono inf_le_right h₁) rfl
      have d := F.inM (le_preimage_mono inf_le_right h₂) rfl
      exact (congrArg₂ (· * ·) (ev_appLE z π _ h₁ (le_preimage_inf a b) _)
        (ev_appLE z π _ h₂ (le_preimage_inf b d) _)).trans
        ((ev_detChg_mul _ _ _ _ _ _ (le_preimage_inf a d)).trans (ev_appLE z π _ h₃ _ _).symm))

theorem LL_add_g (e e' : Ix Dw → ℤ) (k k' : F.J) :
    (F.LL (e + e')).g k k' = (show Γ(Z, F.U k ⊓ F.U k')ˣ from (F.LL e).g k k') *
      (show Γ(Z, F.U k ⊓ F.U k')ˣ from (F.LL e').g k k') := by
  classical
  show ∏ ix, F.T k k' ix ^ (-(e + e') ix) = (∏ ix, F.T k k' ix ^ (-e ix)) * ∏ ix, F.T k k' ix ^ (-e' ix)
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun ix _ => by rw [Pi.add_apply, neg_add, zpow_add]

open Classical in

theorem LL_single_neg (ix : Ix Dw) : F.LL (Pi.single ix (-1)) = F.line ix := by
  unfold LL line
  congr 1
  funext k k'
  rw [Finset.prod_eq_single ix (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp) (by simp)]
  simp

open Classical in

theorem LL_single_none : F.LL (Pi.single none 1) = F.de := by
  unfold LL de line GlobalTheory.CechPic.dual
  congr 1
  funext k k'
  rw [Finset.prod_eq_single none (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp) (by simp)]
  simp

def step (z : Sp S ⟶ Z) {x : Sp S ⟶ Y.X} (_hx : z ≫ π = x) (σ : E →+* ℂ) (i : ℕ) : Submodule S (TanM x Y.t.G) where
  carrier := {v | ∀ (S' : Type) [CommRing S'] (φ : S →+* S') (x' : Sp S' ⟶ Y.X) (e : spMap φ ≫ x = x') (k : F.J)
    (z' : Sp S' ⟶ Z) (_ : spMap φ ≫ z = z') (hz' : ⊤ ≤ z' ⁻¹ᵁ F.U k) (hx' : z' ≫ π = x'),
    tanPull φ e v ∈ initSpan S' (F.vecAt k z' hz' hx' σ) i}
  zero_mem' := fun S' _ φ x' e k z' _ hz' hx' => by rw [map_zero]; exact Submodule.zero_mem _
  add_mem' := fun hu hv S' _ φ x' e k z' ez hz' hx' => by
    rw [map_add]; exact Submodule.add_mem _ (hu S' φ x' e k z' ez hz' hx') (hv S' φ x' e k z' ez hz' hx')
  smul_mem' := fun a v hv S' _ φ x' e k z' ez hz' hx' => by
    rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (hv S' φ x' e k z' ez hz' hx')

theorem initSpan_vecAt_eq (k k' : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hz' : ⊤ ≤ z ⁻¹ᵁ F.U k')
    {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (σ : E →+* ℂ) (i : ℕ) :
    initSpan S (F.vecAt k z hz hx σ) i = initSpan S (F.vecAt k' z hz' hx σ) i :=
  le_antisymm
    (initSpan_le_of_tri (F.B_map_tri k' k σ _) (F.vecAt_eq_sum k' k z hz' hz (le_preimage_inf hz' hz) hx σ) i)
    (initSpan_le_of_tri (F.B_map_tri k k' σ _) (F.vecAt_eq_sum k k' z hz hz' (le_preimage_inf hz hz') hx σ) i)

theorem step_eq (k : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (σ : E →+* ℂ)
    (i : ℕ) : F.step z hx σ i = initSpan S (F.vecAt k z hz hx σ) i := by
  have hid : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id _
  refine le_antisymm (fun v hv => ?_) (fun v hv S' _ φ x' e k' z' ez hz' hx' => ?_)
  · have := hv S (RingHom.id S) x (by rw [hid, Category.id_comp]) k z (by rw [hid, Category.id_comp]) hz hx
    convert this using 1
    apply tan_ext_left
    rw [tanPull_left]
    exact ((congrArg (· ≫ (tv v).left) (GlobalTheory.ModelChart.spMap_dualMapR_id S)).trans (Category.id_comp _)).symm
  · subst ez
    rw [F.initSpan_vecAt_eq k' k _ hz' (le_preimage_comp _ hz)]
    obtain ⟨a, ha, rfl⟩ := mem_initSpan.1 hv
    refine mem_initSpan.2 ⟨fun j => φ (a j), fun j hj => (congrArg φ (ha j hj)).trans (map_zero φ), ?_⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smulₛₗ, F.tanPull_vecAt k φ z hz _ hx hx' e]

theorem step_mono (z : Sp S ⟶ Z) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (σ : E →+* ℂ) {i i' : ℕ} (h : i ≤ i') :
    F.step z hx σ i ≤ F.step z hx σ i' := fun _ hv S' _ φ x' e k z' ez hz' hx' =>
  initSpan_mono _ h (hv S' φ x' e k z' ez hz' hx')

theorem tanPull_mem_step (φ : S →+* S') (z : Sp S ⟶ Z) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) {z' : Sp S' ⟶ Z}
    (ez : spMap φ ≫ z = z') {x' : Sp S' ⟶ Y.X} (hx' : z' ≫ π = x') (e : spMap φ ≫ x = x') (σ : E →+* ℂ) (i : ℕ)
    {v : TanM x Y.t.G} (hv : v ∈ F.step z hx σ i) : tanPull φ e v ∈ F.step z' hx' σ i := by
  intro S'' _ ψ x'' e' k z'' ez' hz'' hx''
  have := hv S'' (ψ.comp φ) x'' (by rw [← spMap_comp', Category.assoc, e, e']) k z''
    (by rw [← spMap_comp', Category.assoc, ez, ez']) hz'' hx''
  convert this using 1
  apply tan_ext_left
  rw [tanPull_left, tanPull_left, tanPull_left, dualMap_comp, ← spMap_comp', Category.assoc]

theorem mem_step_iff_of_injective {V K : Type} [CommRing V] [IsLocalRing V] [CommRing K] (φ : V →+* K)
    (hφ : Function.Injective φ) (z : Sp V ⟶ Z) {x : Sp V ⟶ Y.X} (hx : z ≫ π = x) {zK : Sp K ⟶ Z}
    (ez : spMap φ ≫ z = zK) {xK : Sp K ⟶ Y.X} (hxK : zK ≫ π = xK) (e : spMap φ ≫ x = xK) (σ : E →+* ℂ) (i : ℕ)
    (v : TanM x Y.t.G) : v ∈ F.step z hx σ i ↔ tanPull φ e v ∈ F.step zK hxK σ i := by
  refine ⟨F.tanPull_mem_step φ z hx ez hxK e σ i, fun h => ?_⟩
  obtain ⟨k, hz⟩ := exists_chart_of_isLocalRing F.cover z
  subst ez
  have hz' := le_preimage_comp (spMap φ) hz
  rw [F.step_eq k _ hz'] at h
  rw [F.step_eq k z hz]
  obtain ⟨a, ha, h⟩ := mem_initSpan.1 h
  obtain ⟨cv, rfl⟩ := (vec (F.M k).toMChart x (F.inM hz hx)).surjective v
  rw [sum_vecAt, tanPull_vec _ φ e _ (F.inM hz' hxK), F.uAt_spMap k φ z hz] at h
  have h1 := (vec _ _ _).injective h
  obtain ⟨w, hw⟩ := F.uAt_split k z hz σ
  have hm : ∀ {n n' : ℕ} (A : Matrix (Fin n) (Fin n') V) (b : Fin n' → V),
      (A.map φ).mulVec (fun j => φ (b j)) = fun j => φ (A.mulVec b j) := fun A b =>
    funext fun j => (RingHom.map_mulVec φ A b j).symm
  have h2 : a = fun j => φ (w.mulVec cv j) := by
    rw [← hm, ← h1, Matrix.mulVec_mulVec, ← Matrix.map_mul, hw, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec]
  refine mem_initSpan.2 ⟨w.mulVec cv, fun j hj => hφ ?_, ?_⟩
  · rw [map_zero, ← ha j hj, h2]
  · rw [sum_vecAt]
    congr 1
    funext j
    apply hφ
    rw [h2, hm] at h1
    exact congrFun h1 j

theorem existsUnique_sub_mem_step (k : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x)
    (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    F.vecAt k z hz hx σ i ∈ F.step z hx σ (i + 1) ∧
      ∀ w ∈ F.step z hx σ (i + 1), ∃! a : S, w - a • F.vecAt k z hz hx σ i ∈ F.step z hx σ i := by
  rw [F.step_eq k z hz, F.step_eq k z hz]
  exact ⟨Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩,
    fun w hw => existsUnique_sub_mem_initSpan (F.linearIndependent_vecAt k z hz hx σ) i hw⟩

theorem vecAt_sub_mem_step (k k' : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hz' : ⊤ ≤ z ⁻¹ᵁ F.U k')
    (hh : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k')) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    F.vecAt k' z hz' hx σ i - ev z _ hh ((F.gr σ i).g k k').val • F.vecAt k z hz hx σ i ∈ F.step z hx σ i := by
  rw [F.step_eq k z hz]
  exact sub_diag_mem_initSpan (F.B_map_tri k k' σ _) (F.vecAt_eq_sum k k' z hz hz' hh hx σ) i

theorem exists_retraction (k : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x)
    (σ : E →+* ℂ) (i : ℕ) : ∃ r : TanM x Y.t.G →ₗ[S] F.step z hx σ i, ∀ v : F.step z hx σ i, r v = v := by
  obtain ⟨w, hw⟩ := F.uAt_split k z hz σ
  let co : TanM x Y.t.G →ₗ[S] (Fin (Dw.mult σ) → S) :=
    w.mulVecLin ∘ₗ (vec (F.M k).toMChart x (F.inM hz hx)).symm.toLinearMap
  let r : TanM x Y.t.G →ₗ[S] TanM x Y.t.G := ∑ j : Fin (Dw.mult σ), if (j : ℕ) < i then
    (LinearMap.proj j ∘ₗ co).smulRight (F.vecAt k z hz hx σ j) else 0
  have hr : ∀ v, r v = ∑ j : Fin (Dw.mult σ), (if (j : ℕ) < i then co v j else 0) • F.vecAt k z hz hx σ j := fun v => by
    simp only [r, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  refine ⟨r.codRestrict _ fun v => ?_, fun v => Subtype.ext ?_⟩
  · rw [F.step_eq k z hz, hr]
    exact mem_initSpan.2 ⟨_, fun j hj => if_neg (not_lt.2 hj), rfl⟩
  · obtain ⟨a, ha, h⟩ := mem_initSpan.1 ((F.step_eq k z hz hx σ i).le v.2)
    show r v = v
    have hc : co v = a := by
      rw [← h, sum_vecAt]
      simp [co, Matrix.mulVec_mulVec, hw]
    rw [hr, hc, ← h]
    exact Finset.sum_congr rfl fun j _ => by
      split_ifs with hj
      · rfl
      · rw [ha j (not_lt.1 hj)]

theorem dualRestrict_surjective (k : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x)
    (σ : E →+* ℂ) (i : ℕ) : Function.Surjective (F.step z hx σ i).dualRestrict := by
  obtain ⟨r, hr⟩ := F.exists_retraction k z hz hx σ i
  exact fun f => ⟨f ∘ₗ r, LinearMap.ext fun v => by simp [hr]⟩

theorem de_iso_pull (h : (FlagMod.de Y).IsLB) : LBIso F.de ((FlagMod.de Y).pull π) :=
  LBIso.chartPull (A := FlagMod.de Y) (h := π)
    ⟨fun k => F.M k, F.le, fun y k k' hk hk' => by
      refine (map_inv _ _).trans (Eq.trans (congrArg (·⁻¹) ?_) (map_inv _ _).symm)
      refine (gm_res (𝟙 Z) y (inf_le_inf (F.le k) (F.le k') : F.U k ⊓ F.U k' ≤ π ⁻¹ᵁ ((F.M k).U ⊓ (F.M k').U))
        ⟨hk, hk'⟩ (pullU π _ (thUnit (F.M k) (F.M k')))).trans ?_
      exact (gm_pull (𝟙 Z) π y ((F.M k).U ⊓ (F.M k').U) ⟨F.le k hk, F.le k' hk'⟩ _).trans (by rw [Category.id_comp]; rfl)⟩
    (chartPullPull _ π π rfl) (PolBaseChange.lbIso_refl h)

theorem detOm_iso_pull (h : (FlagMod.detOm Y).IsLB) : LBIso F.detOm ((FlagMod.detOm Y).pull π) :=
  LBIso.chartPull (A := FlagMod.detOm Y) (h := π)
    ⟨fun k => (F.M k).toMChart, F.le, fun y k k' hk hk' => by
      refine (map_inv _ _).trans (Eq.trans (congrArg (·⁻¹) ?_) (map_inv _ _).symm)
      refine (gm_res (𝟙 Z) y (inf_le_inf (F.le k) (F.le k') : F.U k ⊓ F.U k' ≤ π ⁻¹ᵁ ((F.M k).U ⊓ (F.M k').U))
        ⟨hk, hk'⟩ (pullU π _ (detChg (F.M k).toMChart (F.M k').toMChart))).trans ?_
      exact (gm_pull (𝟙 Z) π y ((F.M k).U ⊓ (F.M k').U) ⟨F.le k hk, F.le k' hk'⟩ _).trans (by rw [Category.id_comp]; rfl)⟩
    (chartPullPull _ π π rfl) (PolBaseChange.lbIso_refl h)

end Frames

end GlobalTheory.FlagMod
