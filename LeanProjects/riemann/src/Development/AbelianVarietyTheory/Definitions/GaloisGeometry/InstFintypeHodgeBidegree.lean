import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NegOnePowBoundaryTermsCancel

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CatH

universe v u v' u'

section Wedge

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def wedgeOm {q q' Q : ℕ} (h : q + q' = Q) : Om R B q →ₗ[R] Om R B q' →ₗ[R] Om R B Q :=
  LinearMap.mk₂ R (fun x y ↦ ⟨x.1 * y.1, h ▸ mul_mem x.2 y.2⟩)
    (fun _ _ _ ↦ Subtype.ext (add_mul _ _ _)) (fun _ _ _ ↦ Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ ↦ Subtype.ext (mul_add _ _ _)) (fun _ _ _ ↦ Subtype.ext (mul_smul_comm _ _ _))

variable {R B}

@[simp] theorem coe_wedgeOm {q q' Q : ℕ} (h : q + q' = Q) (x : Om R B q) (y : Om R B q') :
    (wedgeOm R B h x y : DR R B) = x * y := rfl

theorem dOm_wedgeOm {q q' Q : ℕ} (h : q + q' = Q) (x : Om R B q) (y : Om R B q') :
    dOm R B Q (wedgeOm R B h x y) = wedgeOm R B (show q + 1 + q' = Q + 1 by omega) (dOm R B q x) y +
      (-1 : ℤ) ^ q • wedgeOm R B (show q + (q' + 1) = Q + 1 by omega) x (dOm R B q' y) := by
  refine Subtype.ext ?_
  change dDR R B (x.1 * y.1) = dDR R B x.1 * y.1 + (-1 : ℤ) ^ q • (x.1 * dDR R B y.1)
  rw [dDR_mul, sgn_of_mem x.2, add_comm, zsmul_eq_mul, mul_assoc]
  simp

theorem mOm_wedgeOm {R' B' : Type} [CommRing R'] [CommRing B'] [Algebra R' B'] {σ : R →+* R'}
    {α : B →+* B'} (e : SemiHom σ α) {q q' Q : ℕ} (h : q + q' = Q) (x : Om R B q) (y : Om R B q') :
    e.mOm Q (wedgeOm R B h x y) = wedgeOm R' B' h (e.mOm q x) (e.mOm q' y) :=
  Subtype.ext (map_mul e.mDR x.1 y.1)

variable (R B) in

def oneOm : Om R B 0 := ⟨1, by
  change _ ∈ LinearMap.range _ ^ 0
  rw [pow_zero]; exact Submodule.one_le.1 le_rfl⟩

@[simp] theorem coe_oneOm : (oneOm R B : DR R B) = 1 := rfl

theorem dOm_oneOm : dOm R B 0 (oneOm R B) = 0 := Subtype.ext (by
  change dDR R B 1 = 0
  rw [← map_one (algebraMap B (DR R B)), dDR_algebraMap, Derivation.map_one_eq_zero, map_zero])

end Wedge

section Terms

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

def cupTerm {a a' A q q' Q : ℕ} (ha : a + a' = A) (hq : q + q' = Q) :
    Term F a q →ₗ[R] Term F a' q' →ₗ[R] Term F A Q :=
  LinearMap.mk₂ R (fun f g s ↦ wedgeOm R (F.obj (s.obj (Fin.last A))) hq
      (ev (F := OmF F q) s (fr a A (by omega)) (fr_mono _ _ _) (Fin.last A) (Fin.le_last _) f)
      (ev (F := OmF F q') s (bk a a' A ha.le) (bk_mono _ _ _ _) (Fin.last A) (Fin.le_last _) g))
    (fun f f' g ↦ funext fun s ↦ by rw [map_add]; exact LinearMap.map_add₂ _ _ _ _)
    (fun r f g ↦ funext fun s ↦ by rw [map_smul]; exact LinearMap.map_smul₂ _ _ _ _)
    (fun f g g' ↦ funext fun s ↦ by rw [map_add]; exact LinearMap.map_add _ _ _)
    (fun r f g ↦ funext fun s ↦ by rw [map_smul]; exact LinearMap.map_smul _ _ _)

variable {F}

abbrev wedgeF (F : C ⥤ CommAlgCat.{0} R) {q q' Q : ℕ} (hq : q + q' = Q) (T : C) :
    (OmF F q).obj T →ₗ[R] (OmF F q').obj T →ₗ[R] (OmF F Q).obj T := wedgeOm R (F.obj T) hq

theorem cupTerm_apply {a a' A q q' Q : ℕ} (ha : a + a' = A) (hq : q + q' = Q) (f : Term F a q)
    (g : Term F a' q') (s : ComposableArrows C A) :
    cupTerm F ha hq f g s = wedgeF F hq _
      (ev (F := OmF F q) s (fr a A (by omega)) (fr_mono _ _ _) (Fin.last A) (Fin.le_last _) f)
      (ev (F := OmF F q') s (bk a a' A ha.le) (bk_mono _ _ _ _) (Fin.last A) (Fin.le_last _) g) := rfl

theorem ev_cupTerm {a a' A q q' Q K : ℕ} (ha : a + a' = A) (hq : q + q' = Q) (f : Term F a q)
    (g : Term F a' q') (s : ComposableArrows C K)
    (p : Fin (A + 1) → Fin (K + 1)) (hp : Monotone p) (j : Fin (K + 1)) (hj : p (Fin.last A) ≤ j) :
    ev (F := OmF F Q) s p hp j hj (cupTerm F ha hq f g) = wedgeF F hq _
      (ev s (p ∘ fr a A (by omega)) (hp.comp (fr_mono _ _ _)) j ((hp (Fin.le_last _)).trans hj) f)
      (ev s (p ∘ bk a a' A ha.le) (hp.comp (bk_mono _ _ _ _)) j ((hp (Fin.le_last _)).trans hj) g) := by
  refine (mOm_wedgeOm (semiHom_mp F (s.map (homOfLE hj))) hq _ _).trans ?_
  exact congrArg₂ (fun x y ↦ wedgeF F hq _ x y)
    (map_ev s (p ∘ fr a A (by omega)) (hp.comp (fr_mono _ _ _)) (hp (Fin.le_last _)) hj f)
    (map_ev s (p ∘ bk a a' A ha.le) (hp.comp (bk_mono _ _ _ _)) (hp (Fin.le_last _)) hj g)

theorem wedgeF_ev_congr {m n k q q' Q : ℕ} (hq : q + q' = Q) (s : ComposableArrows C k) (j : Fin (k + 1))
    (f : Term F m q) (g : Term F n q')
    {p p' : Fin (m + 1) → Fin (k + 1)} {hp : Monotone p} {hp' : Monotone p'}
    {r r' : Fin (n + 1) → Fin (k + 1)} {hr : Monotone r} {hr' : Monotone r'} {h1 h1' h2 h2'}
    (e1 : ∀ a, (p a : ℕ) = p' a) (e2 : ∀ b, (r b : ℕ) = r' b) :
    wedgeF F hq _ (ev s p hp j h1 f) (ev s r hr j h2 g) =
      wedgeF F hq _ (ev s p' hp' j h1' f) (ev s r' hr' j h2' g) := by
  rw [ev_congr s p p' hp hp' e1, ev_congr s r r' hr hr' e2]

theorem dH_cupTerm {m n k q q' Q : ℕ} (h : m + n = k) (hq : q + q' = Q) (f : Term F m q)
    (g : Term F n q') :
    dH F k Q (cupTerm F h hq f g) = cupTerm F (show m + 1 + n = k + 1 by omega) hq (dH F m q f) g +
      ((-1 : ℤ) ^ m) • cupTerm F (show m + (n + 1) = k + 1 by omega) hq f (dH F n q' g) := by
  subst h
  funext s
  rw [Pi.add_apply, Pi.smul_apply, cupTerm_apply, cupTerm_apply, ev_d, ev_d, d_apply_ev]
  refine (Finset.sum_congr rfl fun (i : Fin (m + n + 2)) _ ↦ congrArg (fun z ↦ (-1 : ℤ) ^ (i : ℕ) • z)
    (ev_cupTerm rfl hq f g s _ (Fin.succAboveOrderEmb i).monotone _ (Fin.le_last _))).trans ?_
  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply]
  rw [← (finCongr (show m + 1 + (n + 1) = m + n + 1 + 1 by omega)).sum_comp, Fin.sum_univ_add,
    Fin.sum_univ_castSucc (n := m + 1), Fin.sum_univ_succ (n := n + 1), smul_add, Finset.smul_sum]
  refine add_rearrange_of_cancel_middle (Finset.sum_congr rfl fun i _ ↦ ?_) (Finset.sum_congr rfl fun j _ ↦ ?_) ?_
  · have := i.isLt
    refine congrArg₂ (· • ·) rfl (wedgeF_ev_congr hq s _ f g (fun a ↦ ?_) (fun b ↦ ?_))
    · have := a.isLt
      rcases lt_or_ge (a : ℕ) i with h1 | h1 <;> fin_index_simp
    · have := b.isLt
      fin_index_simp
  · have := j.isLt
    rw [smul_smul, ← pow_add]
    refine congrArg₂ (· • ·) (congrArg _ (by simp [Fin.val_succ]; omega))
      (wedgeF_ev_congr hq s _ f g (fun a ↦ ?_) (fun b ↦ ?_))
    · have := a.isLt
      fin_index_simp
    · have := b.isLt
      rcases lt_or_ge (b : ℕ) (j + 1) with h1 | h1 <;> fin_index_simp
  · rw [Fin.val_last, Fin.val_zero]
    refine neg_one_pow_boundary_terms_cancel m (wedgeF_ev_congr hq s _ f g (fun a ↦ ?_) (fun b ↦ ?_))
    · have := a.isLt
      fin_index_simp
    · have := b.isLt
      fin_index_simp

theorem dOm_ev {n k q : ℕ} (s : ComposableArrows C k) (p : Fin (n + 1) → Fin (k + 1)) (hp : Monotone p)
    (j : Fin (k + 1)) (h : p (Fin.last n) ≤ j) (f : Term F n q) :
    dOm R (F.obj (s.obj j)) q (ev s p hp j h f) = ev s p hp j h (dV F n q f) :=
  (pOm_dOm F (s.map (homOfLE h)) _).symm

theorem dV_cupTerm {m n k q q' Q : ℕ} (h : m + n = k) (hq : q + q' = Q) (f : Term F m q)
    (g : Term F n q') :
    dV F k Q (cupTerm F h hq f g) = cupTerm F h (show q + 1 + q' = Q + 1 by omega) (dV F m q f) g +
      ((-1 : ℤ) ^ q) • cupTerm F h (show q + (q' + 1) = Q + 1 by omega) f (dV F n q' g) := by
  funext s
  rw [dV_apply, cupTerm_apply]
  refine (dOm_wedgeOm hq _ _).trans ?_
  exact congrArg₂ (· + ·) (congrArg (fun z ↦ wedgeF F _ _ z _) (dOm_ev s _ _ _ _ f))
    (congrArg (fun z ↦ (-1 : ℤ) ^ q • wedgeF F _ _ _ z) (dOm_ev s _ _ _ _ g))

theorem ev_self {M : C ⥤ ModuleCat.{0} R} {m : ℕ} (s : ComposableArrows C m) (p : Fin (m + 1) → Fin (m + 1))
    (hp : Monotone p) (e : ∀ a, (p a : ℕ) = a) (h : p (Fin.last m) ≤ Fin.last m) (f : Cn M m) :
    ev s p hp (Fin.last m) h f = f s := by
  rw [ev_congr s p id hp monotone_id e (Fin.last m) h le_rfl f, ev_apply]
  have hid : s.map (homOfLE (le_rfl : (id (Fin.last m)) ≤ Fin.last m)) = 𝟙 _ := by
    rw [show homOfLE (le_rfl : (id (Fin.last m)) ≤ Fin.last m) = 𝟙 _ from rfl, s.map_id]
  rw [hid, M.map_id]
  rfl

variable (F) in

def oneTerm : Term F 0 0 := fun s ↦ oneOm R (F.obj (s.obj (Fin.last 0)))

theorem coe_ev_oneTerm {k : ℕ} (s : ComposableArrows C k) (p : Fin 1 → Fin (k + 1)) (hp : Monotone p)
    (j : Fin (k + 1)) (h : p (Fin.last 0) ≤ j) :
    (ev s p hp j h (oneTerm F) : (OmF F 0).obj _).1 = 1 :=
  map_one (semiHom_mp F (s.map (homOfLE h))).mDR

theorem oneTerm_cupTerm {a q : ℕ} (ha : 0 + a = a) (hq : 0 + q = q) (f : Term F a q) :
    cupTerm F ha hq (oneTerm F) f = f := by
  funext s
  rw [cupTerm_apply, ev_self s (bk 0 a a ha.le) _ (fun _ ↦ by simp)]
  exact Subtype.ext ((congrArg (· * (f s).1) (coe_ev_oneTerm s _ _ _ _)).trans (one_mul _))

end Terms

section Total

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

instance instFintypeHodgeBidegree (n : ℕ) : Fintype (Bidegree n) :=
  Fintype.subtype (Finset.HasAntidiagonal.antidiagonal n) fun _ ↦
    Finset.HasAntidiagonal.mem_antidiagonal

def Tot.sg {a q n : ℕ} (h : a + q = n) : Term F a q →ₗ[R] Tot F n :=
  LinearMap.single R (fun b : Bidegree n ↦ Term F b.1.1 b.1.2) ⟨(a, q), h⟩

variable {F}

theorem Tot.sg_same {a q n : ℕ} (h : a + q = n) (c : Term F a q) : Tot.sg F h c ⟨(a, q), h⟩ = c :=
  Pi.single_eq_same (M := fun b : Bidegree n ↦ Term F b.1.1 b.1.2) _ _

theorem Tot.sg_of_ne {a q n : ℕ} (h : a + q = n) (c : Term F a q) (b : Bidegree n) (hb : b.1.2 ≠ q) :
    Tot.sg F h c b = 0 :=
  Pi.single_eq_of_ne (M := fun b : Bidegree n ↦ Term F b.1.1 b.1.2) (fun e ↦ hb (by rw [e])) _

theorem Tot.sum_sg {n : ℕ} (c : Tot F n) : ∑ b : Bidegree n, Tot.sg F b.2 (c b) = c :=
  Finset.univ_sum_single c

theorem Tot.induction {n : ℕ} {P : Tot F n → Prop} (h0 : P 0) (ha : ∀ x y, P x → P y → P (x + y))
    (hs : ∀ (a q : ℕ) (h : a + q = n) (c : Term F a q), P (Tot.sg F h c)) (c : Tot F n) : P c := by
  rw [← Tot.sum_sg c]
  exact Finset.sum_induction _ P ha h0 fun b _ ↦ hs _ _ b.2 _

theorem dTot_sg {a q n : ℕ} (h : a + q = n) (c : Term F a q) :
    dTot F n (Tot.sg F h c) = Tot.sg F (show a + 1 + q = n + 1 by omega) (dH F a q c) +
      (-1 : ℤ) ^ a • Tot.sg F (show a + (q + 1) = n + 1 by omega) (dV F a q c) := by
  funext ⟨(A, Q), hb⟩
  dsimp only at hb
  rw [dTot_apply, Pi.add_apply, Pi.smul_apply]
  congr 1
  · by_cases hQ : Q = q
    · subst hQ
      obtain rfl : A = a + 1 := by omega
      rw [totH_succ, Tot.sg_same, Tot.sg_same]
    · rw [Tot.sg_of_ne _ _ _ hQ]
      rcases A with _ | A
      · rfl
      · rw [totH_succ, Tot.sg_of_ne _ _ _ hQ, map_zero]
  · by_cases hQ : Q = q + 1
    · subst hQ
      obtain rfl : A = a := by omega
      rw [totV_succ, Tot.sg_same, Tot.sg_same]
    · rw [Tot.sg_of_ne _ _ _ hQ, smul_zero]
      rcases Q with _ | Q
      · rfl
      · rw [totV_succ, Tot.sg_of_ne _ _ _ (fun e ↦ hQ (congrArg (· + 1) e)), map_zero, smul_zero]

variable (F) in

def Tot.cup {m n N : ℕ} (h : m + n = N) : Tot F m →ₗ[R] Tot F n →ₗ[R] Tot F N :=
  ∑ b : Bidegree m, ∑ b' : Bidegree n, (-1 : ℤ) ^ (b.1.2 * b'.1.1) •
    ((cupTerm F rfl rfl).compl₁₂ (LinearMap.proj b) (LinearMap.proj b')).compr₂
      (Tot.sg F (show b.1.1 + b'.1.1 + (b.1.2 + b'.1.2) = N by have := b.2; have := b'.2; omega))

theorem Tot.cup_apply {m n N : ℕ} (h : m + n = N) (x : Tot F m) (y : Tot F n) :
    Tot.cup F h x y = ∑ b : Bidegree m, ∑ b' : Bidegree n, (-1 : ℤ) ^ (b.1.2 * b'.1.1) •
      Tot.sg F (show b.1.1 + b'.1.1 + (b.1.2 + b'.1.2) = N by have := b.2; have := b'.2; omega)
        (cupTerm F rfl rfl (x b) (y b')) := by
  simp only [Tot.cup, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

theorem Tot.cup_sg {m n N a q a' q' A Q : ℕ} (h : m + n = N) (h₁ : a + q = m) (h₂ : a' + q' = n)
    (ha : a + a' = A) (hq : q + q' = Q) (h₃ : A + Q = N) (f : Term F a q) (g : Term F a' q') :
    Tot.cup F h (Tot.sg F h₁ f) (Tot.sg F h₂ g) =
      (-1 : ℤ) ^ (q * a') • Tot.sg F h₃ (cupTerm F ha hq f g) := by
  subst ha hq
  rw [Tot.cup_apply, Finset.sum_eq_single (⟨(a, q), h₁⟩ : Bidegree m),
    Finset.sum_eq_single (⟨(a', q'), h₂⟩ : Bidegree n), Tot.sg_same, Tot.sg_same]
  · intro b _ hb
    rw [Tot.sg_of_ne h₂ g b (fun e ↦ hb (Subtype.ext (Prod.ext (by have := b.2; dsimp only; omega) e))),
      map_zero, map_zero, smul_zero]
  · exact fun e ↦ absurd (Finset.mem_univ _) e
  · intro b _ hb
    refine Finset.sum_eq_zero fun b' _ ↦ ?_
    rw [Tot.sg_of_ne h₁ f b (fun e ↦ hb (Subtype.ext (Prod.ext (by have := b.2; dsimp only; omega) e))),
      map_zero, LinearMap.zero_apply, map_zero, smul_zero]
  · exact fun e ↦ absurd (Finset.mem_univ _) e

theorem dTot_cup {m n N : ℕ} (h : m + n = N) (x : Tot F m) (y : Tot F n) :
    dTot F N (Tot.cup F h x y) = Tot.cup F (show m + 1 + n = N + 1 by omega) (dTot F m x) y +
      (-1 : ℤ) ^ m • Tot.cup F (show m + (n + 1) = N + 1 by omega) x (dTot F n y) := by
  induction x using Tot.induction with
  | h0 => simp
  | ha x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', smul_add]; abel
  | hs a q h₁ f =>
  induction y using Tot.induction with
  | h0 => simp
  | ha y y' hy hy' => simp only [map_add, hy, hy', smul_add]; abel
  | hs a' q' h₂ g =>
  have e₁ : a + a' + 1 + (q + q') = N + 1 := by omega
  have e₂ : a + a' + (q + q' + 1) = N + 1 := by omega
  rw [Tot.cup_sg h h₁ h₂ rfl rfl (by omega), map_zsmul, dTot_sg, dTot_sg, dTot_sg, dH_cupTerm, dV_cupTerm]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [Tot.cup_sg _ _ h₂ (show a + 1 + a' = a + a' + 1 by omega) rfl e₁,
    Tot.cup_sg _ _ h₂ rfl (show q + 1 + q' = q + q' + 1 by omega) e₂,
    Tot.cup_sg _ h₁ _ (show a + (a' + 1) = a + a' + 1 by omega) rfl e₁,
    Tot.cup_sg _ h₁ _ rfl (show q + (q' + 1) = q + q' + 1 by omega) e₂]
  rw [show (-1 : ℤ) ^ m = (-1) ^ (a + q) by rw [h₁]]
  have hq : ((-1 : ℤ) ^ q) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  simp only [pow_add, add_mul, mul_add, one_mul, mul_one]
  match_scalars
  · ring
  · linear_combination (-(-1 : ℤ) ^ (q * a') * (-1) ^ a) * hq
  · ring
  · ring

variable (F) in

def Tot.one : Tot F 0 := Tot.sg F rfl (oneTerm F)

theorem Tot.one_cup {n : ℕ} (h : 0 + n = n) (x : Tot F n) : Tot.cup F h (Tot.one F) x = x := by
  induction x using Tot.induction with
  | h0 => simp
  | ha x x' hx hx' => simp only [map_add, hx, hx']
  | hs a q e f =>
    rw [Tot.one, Tot.cup_sg h rfl e (zero_add a) (zero_add q) e, oneTerm_cupTerm, zero_mul, pow_zero,
      one_smul]

theorem Tot.one_mem : Tot.one F ∈ ZTot F 0 := by
  have h1 : dH F 0 0 (oneTerm F) = 0 := by
    funext s
    rw [d_apply_ev, Fin.sum_univ_two]
    have e : ∀ i : Fin 2, ev s (Fin.succAboveOrderEmb i) (Fin.succAboveOrderEmb i).monotone (Fin.last _)
        (Fin.le_last _) (oneTerm F) = (oneOm R (F.obj (s.obj (Fin.last 1))) : (OmF F 0).obj _) :=
      fun i ↦ Subtype.ext (coe_ev_oneTerm s _ _ _ _)
    rw [e, e]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    exact zsmul_add_cancel _
  have h2 : dV F 0 0 (oneTerm F) = 0 := funext fun _ ↦ dOm_oneOm
  change dTot F 0 _ = 0
  rw [Tot.one, dTot_sg, h1, h2, map_zero, map_zero, smul_zero, add_zero]

theorem Tot.cup_mem_ZTot {m n N : ℕ} (h : m + n = N) {x : Tot F m} {y : Tot F n}
    (hx : x ∈ ZTot F m) (hy : y ∈ ZTot F n) : Tot.cup F h x y ∈ ZTot F N := by
  change dTot F N _ = 0
  rw [dTot_cup, show dTot F m x = 0 from hx, show dTot F n y = 0 from hy, map_zero,
    LinearMap.zero_apply, map_zero, smul_zero, add_zero]

theorem Tot.cup_mem_BTot_left {m n N : ℕ} (h : m + n = N) {x : Tot F m} {y : Tot F n}
    (hx : x ∈ BTot F m) (hy : y ∈ ZTot F n) : Tot.cup F h x y ∈ BTot F N := by
  cases m with
  | zero => rw [show x = 0 from hx, map_zero, LinearMap.zero_apply]; exact zero_mem _
  | succ m =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    refine ⟨Tot.cup F (show m + n = N by omega) x y, ?_⟩
    rw [dTot_cup, show dTot F n y = 0 from hy, map_zero, smul_zero, add_zero]

theorem Tot.cup_mem_BTot_right {m n N : ℕ} (h : m + n = N) {x : Tot F m} {y : Tot F n}
    (hx : x ∈ ZTot F m) (hy : y ∈ BTot F n) : Tot.cup F h x y ∈ BTot F N := by
  cases n with
  | zero => rw [show y = 0 from hy, map_zero]; exact zero_mem _
  | succ n =>
    obtain ⟨y, rfl⟩ := hy
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    refine ⟨(-1 : ℤ) ^ m • Tot.cup F (show m + n = N by omega) x y, ?_⟩
    rw [map_zsmul, dTot_cup, show dTot F m x = 0 from hx, map_zero, LinearMap.zero_apply, zero_add,
      smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

variable (F) in

def ZTot.cup {m n N : ℕ} (h : m + n = N) : ZTot F m →ₗ[R] ZTot F n →ₗ[R] ZTot F N :=
  LinearMap.mk₂ R (fun x y ↦ ⟨Tot.cup F h x.1 y.1, Tot.cup_mem_ZTot h x.2 y.2⟩)
    (fun _ _ _ ↦ Subtype.ext (LinearMap.map_add₂ _ _ _ _))
    (fun _ _ _ ↦ Subtype.ext (LinearMap.map_smul₂ _ _ _ _))
    (fun _ _ _ ↦ Subtype.ext (LinearMap.map_add _ _ _))
    (fun _ _ _ ↦ Subtype.ext (LinearMap.map_smul _ _ _))

variable (F) in

def Hyp.cup {m n N : ℕ} (h : m + n = N) : Hyp F m →ₗ[R] Hyp F n →ₗ[R] Hyp F N :=
  LinearMap.liftQ₂ _ _ ((ZTot.cup F h).compr₂ (Hyp.mk F N))
    (fun x hx ↦ LinearMap.ext fun y ↦ Hyp.mk_eq_zero.2 (Tot.cup_mem_BTot_left h hx y.2))
    (fun y hy ↦ LinearMap.ext fun x ↦ Hyp.mk_eq_zero.2 (Tot.cup_mem_BTot_right h x.2 hy))

variable (F) in

def Hyp.one : Hyp F 0 := Hyp.mk F 0 ⟨Tot.one F, Tot.one_mem⟩

theorem Hyp.one_cup {n : ℕ} (h : 0 + n = n) (x : Hyp F n) : Hyp.cup F h (Hyp.one F) x = x := by
  obtain ⟨x, rfl⟩ := Hyp.mk_surjective F n x
  exact congrArg (Hyp.mk F n) (Subtype.ext (Tot.one_cup h x.1))

theorem Hyp.one_ne_zero (T : C) [Nontrivial (F.obj T)] : Hyp.one F ≠ 0 := fun h ↦ by
  have h1 : Tot.one F = 0 := Hyp.mk_eq_zero.1 h
  have h2 := (Tot.sg_same rfl (oneTerm F)).symm.trans (congrFun h1 ⟨(0, 0), rfl⟩)
  exact _root_.one_ne_zero (α := DR R (F.obj T))
    (congrArg Subtype.val (congrFun h2 (ComposableArrows.mk₀ T)))

end Total

section Pull

variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'}
  [Category.{v'} C'] {σ : R →+* R'} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  (μ : CoefMap σ F F')

end Pull

section Cone

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

def wedgeCl {m n N : ℕ} (h : m + n = N) (ω : LinearMap.ker (dOm R B m)) (η : LinearMap.ker (dOm R B n)) :
    LinearMap.ker (dOm R B N) :=
  ⟨wedgeOm R B h ω.1 η.1, by
    rw [LinearMap.mem_ker, dOm_wedgeOm, show dOm R B m ω.1 = 0 from ω.2, show dOm R B n η.1 = 0 from η.2,
      map_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero]⟩

variable {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (e : ∀ T : C, B →ₐ[R] F.obj T) (he : ∀ ⦃T T' : C⦄ (φ : T ⟶ T') (b : B), mp F φ (e T b) = e T' b)

theorem cupTerm_coneTerm {m n N : ℕ} (h : m + n = N) (ω : Om R B m) (η : Om R B n) :
    cupTerm F rfl h (coneTerm e m ω) (coneTerm e n η) = coneTerm e N (wedgeOm R B h ω η) := by
  funext s
  rw [cupTerm_apply, ev_self s (fr 0 0 le_rfl) _ (fun _ ↦ rfl), ev_self s (bk 0 0 0 le_rfl) _ (fun _ ↦ by simp)]
  exact (mOm_wedgeOm _ h ω η).symm

theorem coneCl_cup {m n N : ℕ} (h : m + n = N) (ω : LinearMap.ker (dOm R B m))
    (η : LinearMap.ker (dOm R B n)) :
    Hyp.cup F h (coneCl e he m ω) (coneCl e he n η) = coneCl e he N (wedgeCl h ω η) := by
  refine congrArg (Hyp.mk F N) (Subtype.ext ?_)
  refine (Tot.cup_sg h (zero_add m) (zero_add n) rfl h (zero_add N) _ _).trans ?_
  rw [mul_zero, pow_zero, one_smul, cupTerm_coneTerm]
  rfl

end Cone

section Scheme

variable {k k' : Type} [CommRing k] [CommRing k'] {X X' : Scheme.{0}}

def HdR.cup (s : X ⟶ Sp k) {a b n : ℕ} (h : a + b = n) : HdR s a →ₗ[k] HdR s b →ₗ[k] HdR s n :=
  Hyp.cup (OPt s) h

def HdR.one (s : X ⟶ Sp k) : HdR s 0 := Hyp.one (OPt s)

variable {s : X ⟶ Sp k} {a b n : ℕ}

theorem HdR.one_cup (h : 0 + n = n) (x : HdR s n) : HdR.cup s h (HdR.one s) x = x := Hyp.one_cup h x

theorem HdR.ofForm_cup {B : Type} [CommRing B] [Algebra k B] (h : a + b = n)
    (ω : LinearMap.ker (dOm k B a)) (η : LinearMap.ker (dOm k B b)) :
    HdR.cup (algStr k B) h (HdR.ofForm a ω) (HdR.ofForm b η) = HdR.ofForm n (wedgeCl h ω η) :=
  coneCl_cup (R := k) (B := B) (C := AffPt (algStr k B)) (F := OPt (algStr k B)) (fun T ↦ toPt T)
    (fun _ _ φ b ↦ toPt_comp φ b) h ω η

theorem coe_functionsZero_symm {B : Type} [CommRing B] [Algebra k B] (x : B) :
    (((fn0 (R := k) B).symm x : Om k B 0) : DR k B) = algebraMap B (DR k B) x :=
  (coe_eq_algebraMap_zeroEquiv _).trans (congrArg _ ((fn0 (R := k) B).apply_symm_apply x))

theorem HdR.pointEquiv_apply (x : k) :
    HdR.pointEquiv k x = HdR.ofForm 0 ⟨(fn0 k).symm x, dOm_zero_self k _⟩ := rfl

theorem HdR.pointEquiv_cup (x y : k) :
    HdR.cup (algStr k k) (zero_add 0) (HdR.pointEquiv k x) (HdR.pointEquiv k y) = HdR.pointEquiv k (x * y) := by
  rw [HdR.pointEquiv_apply, HdR.pointEquiv_apply, HdR.pointEquiv_apply, HdR.ofForm_cup]
  refine congrArg (HdR.ofForm 0) (Subtype.ext (Subtype.ext ?_))
  exact (congrArg₂ (· * ·) (coe_functionsZero_symm x) (coe_functionsZero_symm y)).trans
    ((map_mul _ _ _).symm.trans (coe_functionsZero_symm (x * y)).symm)

end Scheme

example : HdR.cup (algStr ℤ ℤ) rfl (HdR.pointEquiv ℤ 2) (HdR.pointEquiv ℤ 3) = HdR.pointEquiv ℤ 6 :=
  HdR.pointEquiv_cup 2 3

example : HdR.cup (algStr (ZMod 2) (Polynomial (ZMod 2))) rfl (HdR.one _)
    (HdR.ofForm 1 (tdtForm (ZMod 2))) ≠ 0 := by
  rw [HdR.one_cup]; exact HdR.ofForm_tdt_ne_zero rfl

example {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (ω : Term F 0 1) (g : Term F 1 0) :
    Tot.cup F (show 1 + 1 = 2 from rfl) (Tot.sg F (zero_add 1) ω) (Tot.sg F (add_zero 1) g) ⟨(1, 1), rfl⟩ =
      -cupTerm F rfl rfl ω g := by
  rw [Tot.cup_sg (A := 1) (Q := 1) _ (zero_add 1) (add_zero 1) rfl rfl rfl, Pi.smul_apply, Tot.sg_same]
  simp

end GlobalTheory.HodgeCoh
