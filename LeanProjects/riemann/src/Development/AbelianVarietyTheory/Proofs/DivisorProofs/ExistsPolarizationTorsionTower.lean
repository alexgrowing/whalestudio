import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeilPhi

open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory GlobalTheory.PDivGroup GlobalTheory.CartierDual

section Level

variable {O : Type} [CommRing O] {A B : Type} [CommRing A] [CommRing B]

section Alg

variable [Algebra O A] [Algebra O B]

def ev (y : A →ₐ[O] O) (x : B →ₐ[O] O) : A ⊗[O] B →ₐ[O] O :=
  Algebra.TensorProduct.lift y x fun _ _ => Commute.all _ _

@[simp] theorem ev_tmul (y : A →ₐ[O] O) (x : B →ₐ[O] O) (a : A) (b : B) :
    ev y x (a ⊗ₜ b) = y a * x b := rfl

theorem ev_comp_left (y : A →ₐ[O] O) (x : B →ₐ[O] O) :
    (ev y x).comp Algebra.TensorProduct.includeLeft = y := AlgHom.ext fun a => by simp

theorem ev_comp_right (y : A →ₐ[O] O) (x : B →ₐ[O] O) :
    (ev y x).comp Algebra.TensorProduct.includeRight = x := AlgHom.ext fun a => by simp

theorem exists_ev (ψ : A ⊗[O] B →ₐ[O] O) : ∃ y x, ψ = ev y x :=
  ⟨ψ.comp Algebra.TensorProduct.includeLeft, ψ.comp Algebra.TensorProduct.includeRight, by
    ext a <;> simp [← Algebra.TensorProduct.one_def]⟩

def slice (u : A ⊗[O] B) (x : B →ₐ[O] O) : A := tensorToHom O A B u (toConv x.toLinearMap)

def contr (u : A ⊗[O] B) : CartierDual O A →ₗ[O] B :=
  tensorToHom O B A (TensorProduct.comm O A B u)

theorem apply_slice (u : A ⊗[O] B) (y : A →ₐ[O] O) (x : B →ₐ[O] O) :
    y (slice u x) = ev y x u := by
  unfold slice
  induction u with
  | zero => simp
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
  | tmul a b => simp [mul_comm]

theorem apply_contr (u : A ⊗[O] B) (f : CartierDual O A) (x : B →ₐ[O] O) :
    x (contr u f) = f (slice u x) := by
  unfold slice contr
  induction u with
  | zero => simp
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
  | tmul a b => simp [mul_comm]

theorem ev_map_contr (u : A ⊗[O] B) (x x' : B →ₐ[O] O) (t : CartierDual O A ⊗[O] CartierDual O A) :
    ev x x' (TensorProduct.map (contr u) (contr u) t) = pair O A A t (slice u x ⊗ₜ slice u x') := by
  induction t with
  | zero => simp
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
  | tmul a b => simp [apply_contr]

end Alg

variable [HopfAlgebra O A] [Module.Finite O A] [Module.Projective O A]

theorem conv_apply (x y : WithConv (A →ₐ[O] O)) (a : A) :
    (x * y).ofConv a = ev x.ofConv y.ofConv (comul a) := AlgHom.convMul_apply x y a

structure IsBimul (u : A ⊗[O] A) : Prop where
  one_left : ∀ x : A →ₐ[O] O, ev (1 : WithConv (A →ₐ[O] O)).ofConv x u = 1
  one_right : ∀ x : A →ₐ[O] O, ev x (1 : WithConv (A →ₐ[O] O)).ofConv u = 1
  mul_left : ∀ (y y' : WithConv (A →ₐ[O] O)) (x : A →ₐ[O] O),
    ev (y * y').ofConv x u = ev y.ofConv x u * ev y'.ofConv x u
  mul_right : ∀ (y y' : WithConv (A →ₐ[O] O)) (x : A →ₐ[O] O),
    ev x (y * y').ofConv u = ev x y.ofConv u * ev x y'.ofConv u

variable (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C] [CharZero C]
  {u : A ⊗[O] A} (h : IsBimul u)

include C h

theorem isGroupLikeElem_slice (x : A →ₐ[O] O) : IsGroupLikeElem O (slice u x) where
  counit_eq_one := by
    have := h.one_left x
    rw [← apply_slice] at this
    exact this
  comul_eq_tmul_self := TateFree.eq_of_forall_pts O C (A ⊗[O] A) fun ψ => by
    obtain ⟨y, y', rfl⟩ := exists_ev ψ
    have := h.mul_left (toConv y) (toConv y') x
    rw [← apply_slice, conv_apply] at this
    rw [ev_tmul, apply_slice, apply_slice]
    exact this

theorem slice_one : slice u (1 : WithConv (A →ₐ[O] O)).ofConv = 1 :=
  TateFree.eq_of_forall_pts O C A fun y => by rw [apply_slice, h.one_right, map_one]

theorem slice_mul (x x' : WithConv (A →ₐ[O] O)) :
    slice u (x * x').ofConv = slice u x.ofConv * slice u x'.ofConv :=
  TateFree.eq_of_forall_pts O C A fun y => by
    rw [apply_slice, h.mul_right, map_mul, apply_slice, apply_slice]

def contrHom : CartierDual O A →ₐc[O] A where
  __ := contr u
  counit_comp := LinearMap.ext fun f => by
    have := apply_contr u f (1 : WithConv (A →ₐ[O] O)).ofConv
    rw [slice_one C h] at this
    exact this
  map_comp_comul := LinearMap.ext fun f => TateFree.eq_of_forall_pts O C (A ⊗[O] A) fun ψ => by
    obtain ⟨x, x', rfl⟩ := exists_ev ψ
    have := apply_contr u f (toConv x * toConv x').ofConv
    rw [slice_mul C h, conv_apply, ← pair_comul_tmul, ← ev_map_contr] at this
    exact this.symm
  map_one' := TateFree.eq_of_forall_pts O C A fun x => by
    change x (contr u 1) = _
    rw [apply_contr, map_one]
    exact (isGroupLikeElem_slice C h x).counit_eq_one
  map_mul' f g := TateFree.eq_of_forall_pts O C A fun x => by
    change x (contr u (f * g)) = x (contr u f * contr u g)
    rw [map_mul x, apply_contr, apply_contr, apply_contr, mul_apply,
      (isGroupLikeElem_slice C h x).comul_eq_tmul_self, pair_tmul_tmul]

end Level

theorem exists_hom_dual {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C]
    [IsIntegrallyClosedIn O C] [IsAlgClosed C] [CharZero C] (G : PDivGroup p O)
    (u : ∀ n, G.A n ⊗[O] G.A n) (h : ∀ n, IsBimul (u n))
    (hl : ∀ (n : ℕ) (y : G.A (n + 1) →ₐ[O] O) (x : G.A n →ₐ[O] O),
      ev y (x.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n)) (u (n + 1)) =
        ev (y.comp (G.mulP n : G.A n →ₐ[O] G.A (n + 1))) x (u n)) :
    ∃ φ : G ⟶ G.dual, ∀ (s s' : G.Tate) (n : ℕ),
      muRoot (pairing G O s (tateMap G G.dual O φ s')) n = ev (s.pt n) (s'.pt n) (u n) := by
  have key : ∀ (n : ℕ) (x : G.A n →ₐ[O] O),
      slice (u (n + 1)) (x.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n)) = G.mulP n (slice (u n) x) :=
    fun n x => TateFree.eq_of_forall_pts O C _ fun y => by
      rw [apply_slice, hl, ← apply_slice]
      rfl
  refine ⟨⟨fun n => contrHom C (h n), fun n => BialgHom.ext fun f =>
    TateFree.eq_of_forall_pts O C _ fun x => ?_⟩, fun s s' n => ?_⟩
  · have h1 := apply_contr (u (n + 1)) f (x.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n))
    rw [key] at h1
    exact h1.trans (apply_contr (u n) (CartierDual.map (G.mulP n) f) x).symm
  · rw [muRoot_pairing, ← apply_slice]
    congr 1
    refine eq_of_forall_apply (R := O) fun f => ?_
    rw [apply_charElem, ← apply_contr]
    rfl

end GlobalTheory.WeilPhi

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.WeilPhi

open scoped NNReal

attribute [local instance] Over.cartesianMonoidalCategory

section Weil

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {A : Out.PolAV (Sp C)} {k : ℕ}

theorem weil_mul_swap (hk : 1 ≤ k) {x y : Pts A.A} (hx : x ^ k = 1) (hy : y ^ k = 1) :
    weil A k x y * weil A k y x = 1 := by
  have hxy : (x * y) ^ k = 1 := by rw [mul_pow, hx, hy, _root_.mul_one]
  have h := weil_self hk hxy
  rw [weil_mul_left hk hx hy hxy, weil_mul_right hk hx hy hx, weil_mul_right hk hx hy hy,
    weil_self hk hx, weil_self hk hy, _root_.one_mul, _root_.mul_one] at h
  exact h

theorem weil_level_left (hk : 1 ≤ k) {l : ℕ} (hl : 1 ≤ l) {z s : Pts A.A} (hz : z ^ k = 1)
    (hs : s ^ (k * l) = 1) : weil A (k * l) s z = weil A k (s ^ l) z := by
  have hz' : z ^ (k * l) = 1 := by rw [pow_mul, hz, one_pow]
  have hs' : (s ^ l) ^ k = 1 := by rw [← pow_mul, mul_comm, hs]
  have h1 := weil_mul_swap (Nat.mul_pos hk hl) hz' hs
  rw [weil_level hk hl hz hs] at h1
  exact mul_left_cancel (h1.trans (weil_mul_swap hk hz hs').symm)

end Weil

theorem exists_hom_weil : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), WeilIntegralFinite P → ∀ (G : PDivGroup p O) (tw : G.TorsionTower P.Gt), ∃ φ : G ⟶ G.dual, ∀ (s s' : G.Tate) (n : ℕ), algebraMap O C (muRoot (pairing G O s (tateMap G G.dual O φ s')) n) = (weil P.A (p ^ n) (P.toA (GlobalTheory.DeRham.spOver (s.pt n) ≫ tw.y n)) (P.toA (GlobalTheory.DeRham.spOver (s'.pt n) ≫ tw.y n)) : C) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P hW G tw
  have hi : Function.Injective (algebraMap O C) := P.integers.hom_inj
  haveI : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2
    ⟨hi, fun hx => P.integers.exists_of_le_one (P.integers.mem_of_integral hx)⟩
  let q : ∀ n, WithConv (G.A n →ₐ[O] O) →* Pts P.A.A := fun n => P.toA.comp (tw.pts n O)
  have hq : ∀ n x, q n x ^ p ^ n = 1 := fun n x => by rw [← map_pow, G.pts_pow_self, map_one]
  have hp := one_le_ppow p
  have hu : ∀ n, ∃ u : G.A n ⊗[O] G.A n, ∀ y x : WithConv (G.A n →ₐ[O] O),
      algebraMap O C (ev y.ofConv x.ofConv u) = (weil P.A (p ^ n) (q n y) (q n x) : C) := fun n => by
    obtain ⟨u, hu⟩ := hW (G.A n ⊗[O] G.A n) (p ^ n) (hp n)
      (GlobalTheory.DeRham.spOver Algebra.TensorProduct.includeLeft ≫ tw.y n)
      (GlobalTheory.DeRham.spOver Algebra.TensorProduct.includeRight ≫ tw.y n)
      ((tw.exists_iff n _).1 ⟨_, rfl⟩) ((tw.exists_iff n _).1 ⟨_, rfl⟩)
    refine ⟨u, fun y x => (hu _).trans ?_⟩
    have e : ∀ (ψ : G.A n ⊗[O] G.A n →ₐ[O] O) (i : G.A n →ₐ[O] G.A n ⊗[O] G.A n),
        (Pdiv.ptMap ψ ≫ GlobalTheory.DeRham.spOver i ≫ tw.y n : specO O O ⟶ P.Gt) =
          GlobalTheory.DeRham.spOver (ψ.comp i) ≫ tw.y n := fun ψ i => by
      rw [← GlobalTheory.DeRham.spOver_comp, Category.assoc]
      rfl
    rw [e, e, ev_comp_left, ev_comp_right]
    rfl
  choose u hu using hu
  refine (exists_hom_dual C G u (fun n => ⟨fun x => hi ?_, fun x => hi ?_,
    fun y y' x => hi ?_, fun y y' x => hi ?_⟩) fun n y x => hi ?_).imp
      fun φ hφ s s' n => by rw [hφ]; exact hu n (s.conv n) (s'.conv n)
  · have := weil_pow_left (hp n) (hq n 1) (hq n (.toConv x)) 0
    rw [pow_zero, pow_zero] at this
    rw [hu n 1 (.toConv x), map_one, this, map_one, Units.val_one]
  · have := weil_pow_right (hp n) (hq n 1) (hq n (.toConv x)) 0
    rw [pow_zero, pow_zero] at this
    rw [hu n (.toConv x) 1, map_one, this, map_one, Units.val_one]
  · rw [map_mul, hu n _ (.toConv x), hu n _ (.toConv x), hu n _ (.toConv x), map_mul,
      weil_mul_left (hp n) (hq n _) (hq n _) (hq n _), Units.val_mul]
  · rw [map_mul, hu n (.toConv x), hu n (.toConv x), hu n (.toConv x), map_mul,
      weil_mul_right (hp n) (hq n _) (hq n _) (hq n _), Units.val_mul]
  · have h1 : q (n + 1) (.toConv (x.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n))) = q n (.toConv x) := by
      refine congrArg P.toA ?_
      change GlobalTheory.DeRham.spOver (x.comp _) ≫ tw.y (n + 1) = GlobalTheory.DeRham.spOver x ≫ tw.y n
      rw [← GlobalTheory.DeRham.spOver_comp, Category.assoc, tw.res]
    have h2 : q n (.toConv (y.comp (G.mulP n : G.A n →ₐ[O] G.A (n + 1)))) =
        q (n + 1) (.toConv y) ^ p := by
      refine (congrArg P.toA ?_).trans (map_pow P.toA _ p)
      change GlobalTheory.DeRham.spOver (y.comp _) ≫ tw.y n = (GlobalTheory.DeRham.spOver y ≫ tw.y (n + 1)) ^ p
      rw [← GlobalTheory.DeRham.spOver_comp, Category.assoc, tw.mulP_y, MonObj.comp_pow]
    have a1 := hu (n + 1) (.toConv y) (.toConv (x.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n)))
    have a2 := hu n (.toConv (y.comp (G.mulP n : G.A n →ₐ[O] G.A (n + 1)))) (.toConv x)
    rw [h1] at a1
    rw [h2] at a2
    refine a1.trans (Eq.trans ?_ a2.symm)
    exact congrArg Units.val
      (weil_level_left (hp n) (Fact.out : p.Prime).pos (hq n _) (hq (n + 1) _))

end GlobalTheory.WeilPhi
