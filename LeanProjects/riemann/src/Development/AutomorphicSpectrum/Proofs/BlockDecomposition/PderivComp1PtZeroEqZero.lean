import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeLiftRatioMemIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConeLift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.OntoFirstChernCocycle

section Ring

variable {B : Type} [CommRing B] (a b : Ideal B)

theorem inv_sub_mem {z m : B} (hzm : z * m = 1) (hz : z - 1 ∈ a) : m - 1 ∈ a := by
  have : m - 1 = -((z - 1) * m) := by linear_combination hzm
  rw [this]
  exact neg_mem (a.mul_mem_right _ hz)

theorem log3 (hab : ∀ x y, x ∈ a → y ∈ a → x * y ∈ b) {x y z m : B} (hzm : z * m = 1) (hx : x - 1 ∈ a)
    (hy : y - 1 ∈ a) (hz : z - 1 ∈ a) : x * y * m - 1 - ((y - 1) - (z - 1) + (x - 1)) ∈ b := by
  have hm := inv_sub_mem a hzm hz
  have e : x * y * m - 1 - ((y - 1) - (z - 1) + (x - 1)) =
      (x - 1) * (y - 1) + (-((z - 1) * (m - 1))) + (x - 1) * (m - 1) + (y - 1) * (m - 1) +
        (x - 1) * ((y - 1) * (m - 1)) := by
    linear_combination hzm
  rw [e]
  exact add_mem (add_mem (add_mem (add_mem (hab _ _ hx hy) (neg_mem (hab _ _ hz hm))) (hab _ _ hx hm)) (hab _ _ hy hm))
    (b.mul_mem_left _ (hab _ _ hy hm))

theorem form_key (hab : ∀ x y, x ∈ a → y ∈ a → x * y ∈ b) {W W' Wi t ti c m u e g : B}
    (hW : W = W' * (t * m)) (hWi : W' * Wi = 1) (hti : t * ti = 1) (hcm : c * m = 1)
    (h1 : W - 1 ∈ a) (h2 : W' - 1 ∈ a) (h3 : t * u - 1 ∈ a) (h4 : c * e - 1 ∈ a) (h5 : g + t ∈ a) :
    u - e ∈ a ∧ (W - 1) - (W' - 1) - ((t * u - 1) - (c * e - 1)) - g * (u - e) ∈ b := by
  have hy : t * m - 1 ∈ a := by
    have : t * m - 1 = ((W - 1) - (W' - 1)) * Wi := by
      rw [hW]; linear_combination (1 - t * m) * hWi
    rw [this]
    exact a.mul_mem_right _ (sub_mem h1 h2)
  have hD : u - e ∈ a := by
    have : u - e = ti * ((t * u - 1) - (t * m - 1) - (t * m) * (c * e - 1)) := by
      linear_combination (e - u) * hti + (e * t * ti) * hcm
    rw [this]
    refine a.mul_mem_left _ (sub_mem (sub_mem h3 hy) (a.mul_mem_left _ h4))
  refine ⟨hD, ?_⟩
  have e1 : (W - 1) - (W' - 1) - ((t * u - 1) - (c * e - 1)) - g * (u - e) =
      (W' - 1) * (t * m - 1) + (-((t * m - 1) * (c * e - 1))) + (-((g + t) * (u - e))) := by
    rw [hW]
    linear_combination (t * e) * hcm
  rw [e1]
  exact add_mem (add_mem (hab _ _ h2 hy) (neg_mem (hab _ _ hy h4))) (neg_mem (hab _ _ h5 hD))

end Ring

section Cat

universe v u

variable {R : Type} [CommRing R] {E : Type u} [Category.{v} E] {H : E ⥤ CommAlgCat.{0} R} (a b : IdF H)

def mu {c c' : E} (φ : c ⟶ c') : (H.obj c)ˣ →* (H.obj c')ˣ := Units.map ((H.map φ).hom : H.obj c →* H.obj c')

def dl (W : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ)
    (hW : ∀ {c c' : E} (φ : c ⟶ c'), ((W φ : (H.obj c')ˣ) : H.obj c') - 1 ∈ a.S c') : CH.Cn (sq a b) 1 :=
  fun s => sqMk a b (((W (s.map' 0 1) : (H.obj (s.obj (Fin.last 1)))ˣ) : H.obj (s.obj (Fin.last 1))) - 1) (hW (s.map' 0 1))

def c0 (x : ∀ c, H.obj c) (hx : ∀ c, x c ∈ a.S c) : CH.Cn (sq a b) 0 := fun s => sqMk a b (x _) (hx _)

theorem map_id_sq {T : E} (ρ : T ⟶ T) (h : ρ = 𝟙 T) (x : sqM a b T) : ((sq a b).map ρ).hom x = x := by
  subst h
  simp

theorem sum3 {T : E} {p q r t : H.obj T} (hp : p ∈ a.S T) (hq : q ∈ a.S T) (hr : r ∈ a.S T) (ht : t ∈ a.S T)
    (h : t - ((p - q) + r) ∈ b.S T) :
    (-1 : ℤ) ^ ((0 : Fin 3) : ℕ) • sqMk a b p hp + (-1 : ℤ) ^ ((1 : Fin 3) : ℕ) • sqMk a b q hq +
      (-1 : ℤ) ^ ((2 : Fin 3) : ℕ) • sqMk a b r hr = sqMk a b t ht := by
  have e2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  have e1 : ((1 : Fin 3) : ℕ) = 1 := rfl
  have e0 : ((0 : Fin 3) : ℕ) = 0 := rfl
  rw [e0, e1, e2, pow_zero, pow_one, show (-1 : ℤ) ^ 2 = 1 by norm_num, one_smul, one_smul, neg_one_smul]
  have : sqMk a b p hp + -sqMk a b q hq + sqMk a b r hr = sqMk a b ((p - q) + r) (add_mem (sub_mem hp hq) hr) :=
    Subtype.ext (show Ideal.Quotient.mk (b.S T) p + -Ideal.Quotient.mk (b.S T) q + Ideal.Quotient.mk (b.S T) r = Ideal.Quotient.mk (b.S T) ((p - q) + r) by
      rw [map_add, map_sub]; ring)
  rw [this]
  exact ((sq_eq a b _ _).2 (by
    have := neg_mem h
    rwa [neg_sub] at this))

def rU (W : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ) (s : ComposableArrows E 2) : (H.obj (s.obj (Fin.last 2)))ˣ :=
  mu (s.map' 1 2) (W (s.map' 0 1)) * W (s.map' 1 2) * (W (s.map' 0 2))⁻¹

theorem d_dl (hab : ∀ T x y, x ∈ a.S T → y ∈ a.S T → x * y ∈ b.S T) (W : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ)
    (hW : ∀ {c c' : E} (φ : c ⟶ c'), ((W φ : (H.obj c')ˣ) : H.obj c') - 1 ∈ a.S c') (s : ComposableArrows E 2)
    (hr : (rU W s : H.obj (s.obj (Fin.last 2))) - 1 ∈ a.S _) :
    CH.d (sq a b) 1 (dl a b W hW) s = sqMk a b ((rU W s : H.obj (s.obj (Fin.last 2))) - 1) hr := by
  change ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • ((sq a b).map (toLast i s)).hom (dl a b W hW (face i s)) = _
  rw [Fin.sum_univ_three]
  have t0 := map_id_sq a b (T := s.obj (Fin.last 2)) (toLast 0 s) (s.map_id _) (dl a b W hW (face 0 s))
  have t1 := map_id_sq a b (T := s.obj (Fin.last 2)) (toLast 1 s) (s.map_id _) (dl a b W hW (face 1 s))
  erw [t0, t1]
  have hx : (H.map (s.map' 1 2)).hom ((W (s.map' 0 1) : H.obj _) - 1) ∈ a.S _ := a.map_mem (s.map' 1 2) (hW (s.map' 0 1))
  have t2 : ((sq a b).map (toLast 2 s)).hom (dl a b W hW (face 2 s)) = sqMk a b _ hx := rfl
  erw [t2]
  refine sum3 a b (hW (s.map' 1 2)) (hW (s.map' 0 2)) hx hr ?_
  have e : (H.map (s.map' 1 2)).hom ((W (s.map' 0 1) : H.obj _) - 1) =
      Units.val (mu (s.map' 1 2) (W (s.map' 0 1))) - 1 := by
    rw [map_sub, map_one]; rfl
  have hx' : Units.val (mu (s.map' 1 2) (W (s.map' 0 1))) - 1 ∈ a.S (s.obj (Fin.last 2)) := e ▸ hx
  have key := log3 (a.S (s.obj (Fin.last 2))) (b.S _) (hab _) (Units.mul_inv (W (s.map' 0 2))) hx' (hW (s.map' 1 2)) (hW (s.map' 0 2))
  rw [e]
  exact key

def mv (s : ComposableArrows E 1) (y : H.obj (s.obj 0)) : H.obj (s.obj (Fin.last 1)) := (H.map (s.map' 0 1)).hom y

theorem pderiv_comp1_pt_zero_eq_zero (x : ∀ c, H.obj c) (hx : ∀ c, x c ∈ a.S c) (s : ComposableArrows E 1)
    (hm : x (s.obj (Fin.last 1)) - mv s (x (s.obj 0)) ∈ a.S _) :
    CH.d (sq a b) 0 (c0 a b x hx) s = sqMk a b (x (s.obj (Fin.last 1)) - mv s (x (s.obj 0))) hm := by
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • ((sq a b).map (toLast i s)).hom (c0 a b x hx (face i s)) = _
  rw [Fin.sum_univ_two]
  have t0 := map_id_sq a b (T := s.obj (Fin.last 1)) (toLast 0 s) (s.map_id _) (c0 a b x hx (face 0 s))
  erw [t0]
  have e1 : ((1 : Fin 2) : ℕ) = 1 := rfl
  have e0 : ((0 : Fin 2) : ℕ) = 0 := rfl
  rw [e0, e1, pow_zero, pow_one, one_smul, neg_one_smul]
  exact Subtype.ext (show Ideal.Quotient.mk _ _ + -Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ by
    rw [map_sub, sub_eq_add_neg]; rfl)

theorem rep_of (x : CH.Cn (sq a b) 1) (hx : CH.d (sq a b) 1 x = 0) (j : CH.Cn (sq a b) 0)
    (z : ∀ s : ComposableArrows E 1, H.obj (s.obj (Fin.last 1)))
    (h : ∀ s, (show sqM a b _ from (x - CH.d (sq a b) 0 j) s).1 = Ideal.Quotient.mk _ (z s)) :
    Rep a b z ((CH.cx (sq a b)).cls x hx) := by
  have hf : CH.d (sq a b) 1 (x - CH.d (sq a b) 0 j) = 0 := by
    rw [map_sub, hx, CH.d_d, sub_zero]
  refine ⟨x - CH.d (sq a b) 0 j, hf, ?_, h⟩
  refine (Submodule.Quotient.eq _).2 ?_
  change x - (x - CH.d (sq a b) 0 j) ∈ LinearMap.range (CH.d (sq a b) 0)
  exact ⟨j, by abel⟩

theorem cls_eq_d {F : E ⥤ ModuleCat.{0} R} {x y : CH.Cn F 2} (hx : CH.d F 2 x = 0) (hy : CH.d F 2 y = 0)
    (h : (CH.cx F).cls x hx = (CH.cx F).cls y hy) : ∃ c : CH.Cn F 1, CH.d F 1 c = x - y := by
  obtain ⟨c, hc⟩ := (Submodule.Quotient.eq _).1 h
  exact ⟨c, hc⟩

end Cat

section Cat2

universe v u

variable {R : Type} [CommRing R] {E : Type u} [Category.{v} E] {H : E ⥤ CommAlgCat.{0} R} (a b : IdF H)

theorem mu_comp {c₀ c₁ c₂ : E} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) (x : (H.obj c₀)ˣ) : mu (f ≫ g) x = mu g (mu f x) := by
  ext
  change (H.map (f ≫ g)).hom _ = (H.map g).hom ((H.map f).hom _)
  rw [H.map_comp]
  rfl

def tw (w : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ) (t : ∀ c, (H.obj c)ˣ) {c c' : E} (φ : c ⟶ c') : (H.obj c')ˣ :=
  w φ * (t c' * (mu φ (t c))⁻¹)

theorem tw_units {G : Type} [CommGroup G] (x y z p q r : G) :
    (x * (p * r⁻¹)) * (y * (q * p⁻¹)) * (z * (q * r⁻¹))⁻¹ = x * y * z⁻¹ := by
  simp only [mul_inv, inv_inv]
  have : x * (p * r⁻¹) * (y * (q * p⁻¹)) * (z⁻¹ * (q⁻¹ * r)) = x * y * z⁻¹ * (p * p⁻¹) * (q * q⁻¹) * (r * r⁻¹) := by
    simp only [mul_assoc, mul_left_comm, mul_comm]
  rw [this]
  simp

theorem rU_tw (w : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ) (t : ∀ c, (H.obj c)ˣ) (s : ComposableArrows E 2) :
    rU (fun φ => tw w t φ) s = rU w s := by
  have key : ∀ {c₀ c₁ c₂ : E} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) (h : c₀ ⟶ c₂), h = f ≫ g →
      mu g (tw w t f) * tw w t g * (tw w t h)⁻¹ = mu g (w f) * w g * (w h)⁻¹ := by
    intro c₀ c₁ c₂ f g h e
    subst e
    unfold tw
    rw [map_mul, map_mul, map_inv, mu_comp]
    exact tw_units _ _ _ _ _ _
  exact key (s.map' 0 1) (s.map' 1 2) (s.map' 0 2) (s.map'_comp 0 1 2)

def wt (W : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ) (s : ComposableArrows E 1) : (H.obj (s.obj (Fin.last 1)))ˣ := W (s.map' 0 1)

def mt (s : ComposableArrows E 1) (x : (H.obj (s.obj 0))ˣ) : (H.obj (s.obj (Fin.last 1)))ˣ := mu (s.map' 0 1) x

theorem form_rep (hab : ∀ T x y, x ∈ a.S T → y ∈ a.S T → x * y ∈ b.S T) (W W' : ∀ {c c' : E}, (c ⟶ c') → (H.obj c')ˣ)
    (hW : ∀ {c c' : E} (φ : c ⟶ c'), ((W φ : (H.obj c')ˣ) : H.obj c') - 1 ∈ a.S c')
    (hW' : ∀ {c c' : E} (φ : c ⟶ c'), ((W' φ : (H.obj c')ˣ) : H.obj c') - 1 ∈ a.S c')
    (τ : ∀ c, (H.obj c)ˣ) (hτ : ∀ {c c' : E} (φ : c ⟶ c'), W φ = W' φ * (τ c' * (mu φ (τ c))⁻¹))
    (u g : ∀ c, H.obj c) (h1 : ∀ c, (τ c : H.obj c) * u c - 1 ∈ a.S c) (h2 : ∀ c, g c + τ c ∈ a.S c)
    (hx : CH.d (sq a b) 1 (dl a b W hW - dl a b W' hW') = 0) :
    Rep a b (fun s : ComposableArrows E 1 => g (s.obj (Fin.last 1)) * (u (s.obj (Fin.last 1)) - mv s (u (s.obj 0))))
      ((CH.cx (sq a b)).cls _ hx) := by
  refine rep_of a b _ hx (c0 a b (fun c => (τ c : H.obj c) * u c - 1) h1) _ fun s => ?_
  have hc : Units.val (mt s (τ (s.obj 0))) * mv s (u (s.obj 0)) - 1 ∈ a.S (s.obj (Fin.last 1)) := by
    have := a.map_mem (s.map' 0 1) (h1 (s.obj 0))
    rw [map_sub, map_mul, map_one] at this
    exact this
  have hm : ((τ (s.obj (Fin.last 1)) : H.obj _) * u (s.obj (Fin.last 1)) - 1) -
      mv s ((τ (s.obj 0) : H.obj _) * u (s.obj 0) - 1) ∈ a.S (s.obj (Fin.last 1)) :=
    sub_mem (h1 _) (a.map_mem (s.map' 0 1) (h1 (s.obj 0)))
  have hWt : Units.val (wt W s) = Units.val (wt W' s) * (Units.val (τ (s.obj (Fin.last 1))) *
      ((mt s (τ (s.obj 0)))⁻¹ : (H.obj (s.obj (Fin.last 1)))ˣ).1) := congrArg Units.val (hτ (s.map' 0 1))
  have e := form_key (a.S (s.obj (Fin.last 1))) (b.S _) (hab _) (W := Units.val (wt W s))
    (W' := Units.val (wt W' s)) (Wi := ((wt W' s)⁻¹ : (H.obj (s.obj (Fin.last 1)))ˣ).1)
    (t := (τ (s.obj (Fin.last 1)) : H.obj _)) (ti := ((τ (s.obj (Fin.last 1)))⁻¹ : (H.obj _)ˣ).1)
    (c := Units.val (mt s (τ (s.obj 0)))) (m := ((mt s (τ (s.obj 0)))⁻¹ : (H.obj _)ˣ).1)
    (u := u (s.obj (Fin.last 1))) (e := mv s (u (s.obj 0))) (g := g (s.obj (Fin.last 1)))
    hWt (Units.mul_inv _) (Units.mul_inv _) (Units.mul_inv _) (hW _) (hW' _) (h1 _) hc (h2 _)
  have e2 : mv s ((τ (s.obj 0) : H.obj _) * u (s.obj 0) - 1) =
      Units.val (mt s (τ (s.obj 0))) * mv s (u (s.obj 0)) - 1 := by
    unfold mv
    rw [map_sub, map_mul, map_one]
    rfl
  have e3 := pderiv_comp1_pt_zero_eq_zero a b (fun c => (τ c : H.obj c) * u c - 1) h1 s hm
  have e4 : (dl a b W hW - dl a b W' hW' - CH.d (sq a b) 0 (c0 a b (fun c => (τ c : H.obj c) * u c - 1) h1)) s =
      dl a b W hW s - dl a b W' hW' s - CH.d (sq a b) 0 (c0 a b (fun c => (τ c : H.obj c) * u c - 1) h1) s := rfl
  rw [e4, e3]
  change Ideal.Quotient.mk (b.S (s.obj (Fin.last 1))) (Units.val (wt W s) - 1) - Ideal.Quotient.mk _ (Units.val (wt W' s) - 1) -
    Ideal.Quotient.mk _ (((τ (s.obj (Fin.last 1)) : H.obj _) * u (s.obj (Fin.last 1)) - 1) -
      mv s ((τ (s.obj 0) : H.obj _) * u (s.obj 0) - 1)) = _
  rw [← map_sub, ← map_sub, Ideal.Quotient.eq, e2]
  exact e.2

end Cat2

end GlobalTheory.CompanionTheory.OntoFirstChernCocycle
