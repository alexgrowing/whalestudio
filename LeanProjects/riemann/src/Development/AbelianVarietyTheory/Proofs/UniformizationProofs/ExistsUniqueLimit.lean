import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.SecLimit

section Algebra

universe u

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {W W' W'' : Type u} [CommRing W] [CommRing W']
  [CommRing W''] {m : ℕ}

def comb (c : R →+* W) (b : Fin m → W) (z : Fin m → R) : W := ∑ i, c (z i) * b i

def IsBas (c : R →+* W) (S : Set W) (b : Fin m → W) : Prop :=
  (∀ i, b i ∈ S) ∧ ∀ s ∈ S, ∃! z : Fin m → R, s = comb c b z

theorem map_comb {c : R →+* W} {c' : R' →+* W'} {ρ : W →+* W'} {g : R →+* R'} (h : ∀ a, ρ (c a) = c' (g a))
    (b : Fin m → W) (z : Fin m → R) : ρ (comb c b z) = comb c' (fun i => ρ (b i)) (fun i => g (z i)) := by
  simp only [comb, map_sum, map_mul, h]

theorem comb_vecMul {c : R →+* W} {b v : Fin m → W} {a : Matrix (Fin m) (Fin m) R} (h : ∀ i, v i = comb c b (a i))
    (z : Fin m → R) : comb c v z = comb c b (Matrix.vecMul z a) := by
  simp only [comb, h, Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem comb_single (c : R →+* W) (b : Fin m → W) (i : Fin m) : b i = comb c b (Pi.single i 1) := by
  rw [comb, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, zero_mul])
    (fun h => (h (Finset.mem_univ _)).elim), Pi.single_eq_same, map_one, _root_.one_mul]

theorem IsBas.transfer {c : R →+* W} {c' : R →+* W'} {ρ : W →+* W'} (h : ∀ a, ρ (c a) = c' a)
    (hρ : Function.Injective ρ) (U : W'ˣ) {S : Set W} {S' : Set W'}
    (hS : ∀ s', s' ∈ S' ↔ ∃ s ∈ S, s' = ρ s * U) {b : Fin m → W} (hb : IsBas c S b) :
    IsBas c' S' (fun i => ρ (b i) * U) := by
  refine ⟨fun i => (hS _).2 ⟨_, hb.1 i, rfl⟩, fun s' hs' => ?_⟩
  obtain ⟨s, hs, rfl⟩ := (hS _).1 hs'
  refine (existsUnique_congr fun z => ?_).1 (hb.2 s hs)
  have e : comb c' (fun i => ρ (b i) * U) z = ρ (comb c b z) * U := by
    simp only [comb, map_sum, map_mul, h, Finset.sum_mul, _root_.mul_assoc]
  rw [e, Units.mul_left_inj, hρ.eq_iff]

theorem IsBas.reduce {c : R →+* W} {c' : R' →+* W'} {c'' : R'' →+* W''} {ρ : W →+* W'} {ρ' : W' →+* W''}
    {g : R →+* R'} {g' : R' →+* R''} [IsLocalHom g'] (h : ∀ a, ρ (c a) = c' (g a)) (h' : ∀ a, ρ' (c' a) = c'' (g' a))
    {S : Set W} {S' : Set W'} {S'' : Set W''} (hS : ∀ s ∈ S, ρ s ∈ S') (hS' : ∀ s ∈ S', ρ' s ∈ S'')
    (hl : ∀ s ∈ S'', ∃ t ∈ S, s = ρ' (ρ t)) {b : Fin m → W} {b' : Fin m → W'} {b'' : Fin m → W''}
    (hb : IsBas c S b) (hb' : IsBas c' S' b') (hb'' : IsBas c'' S'' b'') : IsBas c' S' (fun i => ρ (b i)) := by
  choose a ha _ using fun i => hb'.2 _ (hS _ (hb.1 i))
  choose e he _ using fun i => hb''.2 _ (hS' _ (hb'.1 i))
  choose t ht ht' using fun i => hl _ (hb''.1 i)
  choose d hd _ using fun i => hb.2 _ (ht i)
  let A : Matrix (Fin m) (Fin m) R' := Matrix.of a
  let E : Matrix (Fin m) (Fin m) R'' := Matrix.of e
  let D : Matrix (Fin m) (Fin m) R'' := Matrix.of fun l i => g' (g (d l i))
  have h₁ : D * (A.map g' * E) = 1 := by
    ext l j
    have e₁ : b'' l = comb c'' b'' (Matrix.vecMul (D l) (A.map g' * E)) := by
      rw [← Matrix.vecMul_vecMul, ← comb_vecMul (a := E) he, ← comb_vecMul (v := fun i => ρ' (ρ (b i)))
        (a := A.map g') fun i => by rw [ha i, map_comb h']; rfl]
      rw [ht' l, hd l, map_comb h, map_comb h']; rfl
    have := congrFun ((hb''.2 _ (hb''.1 l)).unique e₁ (comb_single c'' b'' l)) j
    rw [Matrix.one_apply, ← Matrix.mul_apply_eq_vecMul] at *
    rw [this, Pi.single_apply]
    simp only [eq_comm]
  have hA : IsUnit A.det := by
    have := congrArg Matrix.det h₁
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one, mul_left_comm] at this
    have h₂ : IsUnit (A.map g').det := IsUnit.of_mul_eq_one _ this
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h₂
    exact IsUnit.of_map g' _ h₂
  refine ⟨fun i => hS _ (hb.1 i), fun s hs => ?_⟩
  obtain ⟨y, hy, hy'⟩ := hb'.2 s hs
  refine ⟨Matrix.vecMul y A⁻¹, ?_, fun z hz => ?_⟩
  · beta_reduce
    rw [comb_vecMul (a := A) ha, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
    exact hy
  · beta_reduce at hz
    rw [comb_vecMul (a := A) ha] at hz
    rw [← hy' _ hz, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hA, Matrix.vecMul_one]

theorem existsUnique_limit (I : Ideal R) [IsAdicComplete I R] {T : ℕ → Type u} [∀ e, CommRing (T e)]
    {c : R →+* W} {c' : ∀ e, R ⧸ I ^ (e + 1) →+* T e} {ρ : ∀ e, W →+* T e} {τ : ∀ e, T (e + 1) →+* T e}
    (h : ∀ e a, ρ e (c a) = c' e (Ideal.Quotient.mk _ a)) (hτ : ∀ e s, τ e (ρ (e + 1) s) = ρ e s)
    {S : Set W} {S' : ∀ e, Set (T e)} {b : Fin m → W} (hS : ∀ z, comb c b z ∈ S)
    (hb : IsBas c S b) (hb' : ∀ e, IsBas (c' e) (S' e) (fun i => ρ e (b i)))
    (f : ∀ e, T e) (hf : ∀ e, f e ∈ S' e) (hc : ∀ e, τ e (f (e + 1)) = f e) : ∃! s, s ∈ S ∧ ∀ e, ρ e s = f e := by
  choose z hz hz' using fun e => (hb' e).2 _ (hf e)
  choose y hy using fun e i => Ideal.Quotient.mk_surjective (z e i)
  have key : ∀ e (x : Fin m → R), ρ e (comb c b x) = f e ↔ ∀ i, x i - y e i ∈ I ^ (e + 1) := fun e x => by
    rw [map_comb (h e)]
    simp only [← Ideal.Quotient.eq, hy]
    exact ⟨fun H => congrFun (hz' e _ H.symm), fun H => by rw [funext H]; exact (hz e).symm⟩
  have step : ∀ e i, y (e + 1) i - y e i ∈ I ^ (e + 1) := fun e => (key e _).1 (by
    rw [← hτ, (key (e + 1) _).2 fun i => by rw [sub_self]; exact zero_mem _, hc])
  have hL : ∀ i, ∃ L : R, ∀ e, L - y e i ∈ I ^ (e + 1) := fun i => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance (f := fun e => y e i)
      ((AdicCompletion.isAdicCauchy_iff I R _).2 fun n => by
        rw [smul_eq_mul, Ideal.mul_top]
        exact (SModEq.sub_mem.2 (Ideal.pow_le_pow_right n.le_succ (step n i))).symm)
    refine ⟨L, fun e => ?_⟩
    have := hL (e + 1)
    rw [smul_eq_mul, Ideal.mul_top] at this
    have := add_mem (SModEq.sub_mem.1 this.symm) (step e i)
    rwa [sub_add_sub_cancel] at this
  choose L hL using hL
  refine ⟨comb c b L, ⟨hS L, fun e => (key e L).2 fun i => hL i e⟩, fun s ⟨hs, hs'⟩ => ?_⟩
  obtain ⟨x, rfl, -⟩ := hb.2 s hs
  congr 1
  funext i
  refine sub_eq_zero.1 (IsHausdorff.haus (I := I) (M := R) inferInstance _ fun n => ?_)
  rw [smul_eq_mul, Ideal.mul_top, SModEq.zero]
  have := sub_mem ((key n x).1 (hs' n) i) (hL i n)
  rw [sub_sub_sub_cancel_right] at this
  exact Ideal.pow_le_pow_right n.le_succ this

end Algebra

section Values

variable {X Y Y' Y'' : Scheme.{0}} (L : LB X) {K K' K₃ : Type} [Fintype K] [Fintype K'] [Fintype K₃]

abbrev Vals (Y : Scheme.{0}) : Type 1 :=
  ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z) (_ : {J // Good L z J}), Z.presheaf.stalk z

def pull (h : Y' ⟶ Y) : Vals L Y →+* Vals L Y' where
  toFun w Z r z J := w Z (r ≫ h) z J
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def fn (Y : Scheme.{0}) : Γ(Y, ⊤) →+* Vals L Y where
  toFun a Z r z _ := gs r z ⊤ a
  map_one' := by funext Z r z J; rw [gs_eq r z ⊤ trivial, map_one, map_one]; rfl
  map_mul' _ _ := by funext Z r z J; exact gs_mul r z ⊤ trivial _ _
  map_zero' := by funext Z r z J; rw [gs_eq r z ⊤ trivial, map_zero, map_zero]; rfl
  map_add' _ _ := by funext Z r z J; exact gs_add r z ⊤ trivial _ _

def cst {R : Type} [CommRing R] (f : Y ⟶ Spec (CommRingCat.of R)) : R →+* Vals L Y :=
  (fn L Y).comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

variable {L}

theorem pull_pull (h : Y' ⟶ Y) (h' : Y'' ⟶ Y') (w : Vals L Y) : pull L h' (pull L h w) = pull L (h' ≫ h) w := by
  funext Z r z J
  exact congrArg (fun q => w Z q z J) (Category.assoc _ _ _)

theorem pull_id (w : Vals L Y) : pull L (𝟙 Y) w = w := by
  funext Z r z J
  exact congrArg (fun q => w Z q z J) (Category.comp_id _)

theorem pull_cst {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') {π : Y' ⟶ Y}
    {f : Y ⟶ Spec (CommRingCat.of R)} {f' : Y' ⟶ Spec (CommRingCat.of R')}
    (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) (a : R) : pull L π (cst L f a) = cst L f' (g a) := by
  have e₁ := congrArg (fun Q => Q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  have e₂ := congrArg (fun q => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) w
  funext Z r z J
  exact (gs_pull r π z ⊤ trivial _).symm.trans (congrArg (gs r z ⊤) ((congrArg f'.appTop.hom e₁).trans e₂.symm).symm)

def ev {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) : Vals L Y := fun _ r z J => sval s r z J.1

def evU {φ : K → (Y ⟶ X)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb L φ ε)) : (Vals L Y)ˣ where
  val _ r z J := (val u r z J.1).val
  inv _ r z J := (val u r z J.1).inv
  val_inv := by funext Z r z J; exact (val u r z J.1).val_inv
  inv_val := by funext Z r z J; exact (val u r z J.1).inv_val

variable (L) in

def secVals (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Set (Vals L Y) := Set.range (ev (L := L) (φ := φ) (ε := ε))

variable {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem eq_of_val (hL : L.IsLB) {s s' : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, ev s Y (𝟙 Y) y J = ev s' Y (𝟙 Y) y J) : s = s' :=
  DVR.SecOps.sec_ext (sec_ext_val hL fun y J hJ => h y ⟨J, hJ⟩)

theorem secVals_ext (hL : L.IsLB) {w w' : Vals L Y} (hw : w ∈ secVals L φ ε) (hw' : w' ∈ secVals L φ ε)
    (h : ∀ y J, w Y (𝟙 Y) y J = w' Y (𝟙 Y) y J) : w = w' := by
  obtain ⟨s, rfl⟩ := hw
  obtain ⟨s', rfl⟩ := hw'
  rw [eq_of_val hL h]

theorem ev_pullSec (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) : ev (DVR.pullSec L φ ε s h) = pull L h (ev s) := by
  funext Z r z J
  exact DVR.SectionScalarValuation.sval_pullSec φ ε s h r z J.2

theorem pull_mem {w : Vals L Y} (hw : w ∈ secVals L φ ε) (h : Y' ⟶ Y) {ψ : K → (Y' ⟶ X)} (e : ∀ k, ψ k = h ≫ φ k) :
    pull L h w ∈ secVals L ψ ε := by
  obtain ⟨s, rfl⟩ := hw
  obtain rfl : ψ = fun k => h ≫ φ k := funext e
  exact ⟨_, ev_pullSec s h⟩

theorem ev_comb {R : Type} [CommRing R] {m : ℕ} (g : R →+* Γ(Y, ⊤)) (a : Fin m → R)
    (b : Fin m → LB.Sec (LB.LinComb L φ ε)) {s : LB.Sec (LB.LinComb L φ ε)}
    (hs : ∀ j, s.f j = ∑ i, resTop _ (g (a i)) * (b i).f j) : ev s = comb ((fn L Y).comp g) (fun i => ev (b i)) a := by
  funext Z r z J
  simp only [comb, Finset.sum_apply]
  exact DVR.SectionScalarValuation.sval_lin (fun i => g (a i)) b hs r z J.2

theorem exists_comb {M : LB Y} {m : ℕ} (a : Fin m → Γ(Y, ⊤)) (b : Fin m → LB.Sec M) :
    ∃ s : LB.Sec M, ∀ j, s.f j = ∑ i, resTop _ (a i) * (b i).f j :=
  ⟨⟨fun j => ∑ i, resTop _ (a i) * (b i).f j, fun j j' => by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (DVR.SecOps.secScale (a i) (b i)).compat j j'⟩, fun _ => rfl⟩

theorem comb_mem {R : Type} [CommRing R] {m : ℕ} (g : R →+* Γ(Y, ⊤)) (a : Fin m → R) {b : Fin m → Vals L Y}
    (hb : ∀ i, b i ∈ secVals L φ ε) : comb ((fn L Y).comp g) b a ∈ secVals L φ ε := by
  choose t ht using hb
  obtain rfl : (fun i => ev (t i)) = b := funext ht
  obtain ⟨s, hs⟩ := exists_comb (fun i => g (a i)) t
  exact ⟨s, ev_comb g a t hs⟩

theorem isBas_of_comb (hL : L.IsLB) {R : Type} [CommRing R] {m : ℕ} (g : R →+* Γ(Y, ⊤))
    (b : Fin m → LB.Sec (LB.LinComb L φ ε))
    (hb : ∀ s : LB.Sec (LB.LinComb L φ ε), ∃! a : Fin m → R, ∀ j, s.f j = ∑ i, resTop _ (g (a i)) * (b i).f j) :
    IsBas ((fn L Y).comp g) (secVals L φ ε) (fun i => ev (b i)) := by
  refine ⟨fun i => ⟨_, rfl⟩, ?_⟩
  rintro _ ⟨s, rfl⟩
  refine (existsUnique_congr fun a => ⟨ev_comb g a b, fun H => ?_⟩).1 (hb s)
  obtain ⟨t, ht⟩ := exists_comb (fun i => g (a i)) b
  rw [← ev_comb g a b ht] at H
  rw [eq_of_val hL fun y J => congrFun (congrFun (congrFun (congrFun H _) _) y) J]
  exact ht

theorem mul_mem_iff (hL : L.IsLB) {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {φ₃ : K₃ → (Y ⟶ X)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen) (h : FormEq (Sum.elim φ φ₃) (Sum.elim ε ε₃) φ' ε')
    (w : Vals L Y) : w * evU u ∈ secVals L φ' ε' ↔ w ∈ secVals L φ ε := by
  constructor
  · rintro ⟨s, hs⟩
    have hu' := DVR.invGen_isGen L _ _ u hu
    obtain ⟨t, ht⟩ := exists_sec (φ' := φ) (ε' := ε) hL (fun U _ q => by
      have := h U q
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp] at this ⊢
      rw [← this]
      simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]) (pullMulSec s (𝟙 Y) (LB.invGen L _ _ u) hu')
    refine ⟨t, ?_⟩
    funext Z r z J
    refine (ht Z r z J.1 J.2).trans ?_
    rw [sval_pullMulSec _ _ _ hu' _ z J.2, val_inv, Category.comp_id, Units.mul_inv_eq_iff_eq_mul]
    exact congrFun (congrFun (congrFun (congrFun hs Z) r) z) J
  · rintro ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := exists_sec (φ' := φ') (ε' := ε') hL (fun U _ q => by
      simpa only [Category.id_comp] using h U q) (pullMulSec s (𝟙 Y) u hu)
    refine ⟨t, ?_⟩
    funext Z r z J
    refine (ht Z r z J.1 J.2).trans ?_
    rw [sval_pullMulSec _ _ _ hu _ z J.2, Category.comp_id]
    rfl

theorem pull_evU (u : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) :
    (evU (LB.pullGen L φ ε u h)).val = pull L h (evU u).val := by
  funext Z r z J
  exact congrArg Units.val (val_pull J.2 u h r)

end Values

end GlobalTheory.SecLimit
