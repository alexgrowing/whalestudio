import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NegOnePowBoundaryTermsCancel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupAssocC
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.AltForm
noncomputable section
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

def mulM (A : C ⥤ CommAlgCat.{0} R) : GlobalTheory.CatH.Mult (CH.modF A) where
  mul T := LinearMap.mul R (A.obj T)
  one T := (1 : A.obj T)
  mul_assoc T x y z := mul_assoc (G := A.obj T) x y z
  mul_comm T x y := mul_comm (G := A.obj T) x y
  one_mul T x := one_mul (M := A.obj T) x
  map_mul {X Y} f x y := map_mul (A.map f).hom (show A.obj X from x) y
  map_one {X Y} f := map_one (A.map f).hom

abbrev Co (A : C ⥤ CommAlgCat.{0} R) (n : ℕ) := ∀ s : ComposableArrows C n, A.obj (s.obj (Fin.last n))

variable {A : C ⥤ CommAlgCat.{0} R}

def dd (n : ℕ) (z : Co A n) : Co A (n + 1) := CH.d (CH.modF A) n z

def cp {p q n : ℕ} (h : p + q = n) (f : Co A p) (g : Co A q) : Co A n := (CH.mulP A).cupC h f g

def tm {p n : ℕ} (s : ComposableArrows C n) (f : Co A p) (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    A.obj (s.obj (Fin.last n)) := CH.term (CH.modF A) s f g hg

def one : Co A 0 := fun _ => 1

theorem dd_add {n : ℕ} (f g : Co A n) : dd n (f + g) = dd n f + dd n g := map_add (CH.d (CH.modF A) n) f g
theorem dd_zero {n : ℕ} : dd n (0 : Co A n) = 0 := map_zero (CH.d (CH.modF A) n)
theorem dd_neg {n : ℕ} (f : Co A n) : dd n (-f) = -dd n f := map_neg (CH.d (CH.modF A) n) f
theorem dd_zsmul {n : ℕ} (u : ℤ) (f : Co A n) : dd n (u • f) = u • dd n f := map_zsmul (CH.d (CH.modF A) n) u f

section cp
variable {p q n : ℕ} (h : p + q = n)
theorem cp_add_left (f f' : Co A p) (g : Co A q) : cp h (f + f') g = cp h f g + cp h f' g :=
  LinearMap.map_add₂ ((CH.mulP A).cupC h) f f' g
theorem cp_add_right (f : Co A p) (g g' : Co A q) : cp h f (g + g') = cp h f g + cp h f g' :=
  map_add ((CH.mulP A).cupC h f) g g'
theorem cp_neg_left (f : Co A p) (g : Co A q) : cp h (-f) g = -cp h f g :=
  LinearMap.map_neg₂ ((CH.mulP A).cupC h) f g
theorem cp_neg_right (f : Co A p) (g : Co A q) : cp h f (-g) = -cp h f g :=
  map_neg ((CH.mulP A).cupC h f) g
theorem cp_sub_left (f f' : Co A p) (g : Co A q) : cp h (f - f') g = cp h f g - cp h f' g := by
  rw [sub_eq_add_neg, cp_add_left, cp_neg_left, sub_eq_add_neg]
theorem cp_sub_right (f : Co A p) (g g' : Co A q) : cp h f (g - g') = cp h f g - cp h f g' := by
  rw [sub_eq_add_neg, cp_add_right, cp_neg_right, sub_eq_add_neg]
theorem cp_zero_right (f : Co A p) : cp h f (0 : Co A q) = 0 := map_zero ((CH.mulP A).cupC h f)
theorem cp_zero_left (g : Co A q) : cp h (0 : Co A p) g = 0 := LinearMap.map_zero₂ ((CH.mulP A).cupC h) g
theorem cp_apply (f : Co A p) (g : Co A q) (s : ComposableArrows C n) :
    cp h f g s = tm s f (CH.front h) (CH.front_mono h) * tm s g (CH.back h) (CH.back_mono h) := rfl
end cp

theorem dd_cp {m n k : ℕ} (h : m + n = k) (f : Co A m) (g : Co A n) :
    dd k (cp h f g) = cp (show m + 1 + n = k + 1 by omega) (dd m f) g +
      ((-1 : ℤ) ^ m) • cp (show m + (n + 1) = k + 1 by omega) f (dd n g) :=
  GlobalTheory.CatH.d_cupC (mulM A) h f g

theorem cp_assoc {p q r a b n : ℕ} (h₁ : p + q = a) (h₂ : a + r = n) (h₃ : q + r = b) (h₄ : p + b = n)
    (x : Co A p) (y : Co A q) (z : Co A r) : cp h₂ (cp h₁ x y) z = cp h₄ x (cp h₃ y z) :=
  (GlobalTheory.CompanionTheory.CupAssocC.cup_assocC A).2 h₁ h₂ h₃ h₄ x y z

theorem tm_congr {p n : ℕ} (s : ComposableArrows C n) (f : Co A p) {g g' : Fin (p + 1) → Fin (n + 1)}
    (hg : Monotone g) (hg' : Monotone g') (h : g = g') : tm s f g hg = tm s f g' hg' := by
  subst h; rfl

theorem dd_apply {n : ℕ} (f : Co A n) (s : ComposableArrows C (n + 1)) :
    dd n f s = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • tm s f i.succAbove (Fin.strictMono_succAbove i).monotone := rfl

theorem dd_zero_apply (f : Co A 0) (s : ComposableArrows C 1) :
    dd 0 f s = tm s f (Fin.succAbove 0) (Fin.strictMono_succAbove 0).monotone
      - tm s f (Fin.succAbove 1) (Fin.strictMono_succAbove 1).monotone := by
  rw [dd_apply, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

theorem dd_one_apply (f : Co A 1) (s : ComposableArrows C 2) :
    dd 1 f s = tm s f (Fin.succAbove 0) (Fin.strictMono_succAbove 0).monotone
      - tm s f (Fin.succAbove 1) (Fin.strictMono_succAbove 1).monotone
      + tm s f (Fin.succAbove 2) (Fin.strictMono_succAbove 2).monotone := by
  rw [dd_apply, Fin.sum_univ_three]
  simp [sub_eq_add_neg]

theorem cp_one_one_apply (h : 1 + 1 = 2) (f g : Co A 1) (s : ComposableArrows C 2) :
    cp h f g s = tm s f (Fin.succAbove 2) (Fin.strictMono_succAbove 2).monotone *
      tm s g (Fin.succAbove 0) (Fin.strictMono_succAbove 0).monotone := by
  rw [cp_apply]
  congr 1
  · exact tm_congr s f _ _ (by funext i; fin_cases i <;> rfl)
  · exact tm_congr s g _ _ (by funext i; fin_cases i <;> rfl)

theorem dd_one : dd 0 (one : Co A 0) = 0 := by
  funext s
  rw [dd_zero_apply]
  have e : ∀ (g : Fin 1 → Fin 2) (hg : Monotone g), tm s (one : Co A 0) g hg = 1 := fun g hg =>
    map_one (A.map (s.map (homOfLE (Fin.le_last (g (Fin.last 0)))))).hom
  rw [e, e, sub_self]; rfl

def pw (a b : Co A 1) : Co A 1 := fun s => a s * b s

theorem tm_pw {n : ℕ} (a b : Co A 1) (s : ComposableArrows C n) (g : Fin 2 → Fin (n + 1)) (hg : Monotone g) :
    tm s (pw a b) g hg = tm s a g hg * tm s b g hg :=
  map_mul (A.map (s.map (homOfLE (Fin.le_last (g (Fin.last 1)))))).hom _ _

theorem dd_pw {a b : Co A 1} (ha : dd 1 a = 0) (hb : dd 1 b = 0) (h : 1 + 1 = 2) :
    dd 1 (pw a b) = -(cp h a b + cp h b a) := by
  funext s
  have ea := congrFun ha s
  have eb := congrFun hb s
  rw [dd_one_apply, Pi.zero_apply] at ea eb
  rw [dd_one_apply, tm_pw, tm_pw, tm_pw, Pi.neg_apply, Pi.add_apply, cp_one_one_apply, cp_one_one_apply]
  generalize tm s a (Fin.succAbove 0) _ = a0 at *
  generalize tm s a (Fin.succAbove 1) _ = a1 at *
  generalize tm s a (Fin.succAbove 2) _ = a2 at *
  generalize tm s b (Fin.succAbove 0) _ = b0 at *
  generalize tm s b (Fin.succAbove 1) _ = b1 at *
  generalize tm s b (Fin.succAbove 2) _ = b2 at *
  have e1 : a1 = a0 + a2 := by linear_combination -ea
  have e2 : b1 = b0 + b2 := by linear_combination -eb
  rw [e1, e2]; ring

end
end GlobalTheory.CompanionTheory.AltForm

namespace GlobalTheory.CompanionTheory.AltForm
noncomputable section
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

section filtered
variable {A : C ⥤ CommAlgCat.{0} R}

def In (a : IdF A) {n : ℕ} (z : Co A n) : Prop := ∀ s : ComposableArrows C n, z s ∈ a.S (s.obj (Fin.last n))

variable {a : IdF A} {n : ℕ} {f g : Co A n}

theorem In.add (hf : In a f) (hg : In a g) : In a (f + g) := fun s => (a.S _).add_mem (hf s) (hg s)
theorem In.neg (hf : In a f) : In a (-f) := fun s => (a.S _).neg_mem (hf s)
theorem In.sub (hf : In a f) (hg : In a g) : In a (f - g) := fun s => (a.S _).sub_mem (hf s) (hg s)
theorem In.zsmul (u : ℤ) (hf : In a f) : In a (u • f) := fun s => zsmul_mem (hf s) u
theorem In.zero : In a (0 : Co A n) := fun s => (a.S _).zero_mem
theorem In.tm {p : ℕ} {f : Co A p} (hf : In a f) (s : ComposableArrows C n) (g : Fin (p + 1) → Fin (n + 1))
    (hg : Monotone g) : tm s f g hg ∈ a.S (s.obj (Fin.last n)) :=
  a.map_mem _ (hf (hg.functor ⋙ s))
end filtered

variable {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

theorem In.lvl {n p p' : ℕ} {z : Co Φ.A n} (h : p = p') (hz : In (Fil p) z) : In (Fil p') z := by
  subst h; exact hz

theorem In.mulc (hF : IsFil Φ Fil) {p q n a b : ℕ} (h : p + q = n) {f : Co Φ.A p} {g : Co Φ.A q}
    (hf : In (Fil a) f) (hg : In (Fil b) g) : In (Fil ((a + b : ℕ) : ℤ)) (cp h f g) := fun s =>
  hF.mul a b _ (hf.tm s _ _) (hg.tm s _ _)

theorem In.mulc' (hF : IsFil Φ Fil) {p q n a b c : ℕ} (h : p + q = n) {f : Co Φ.A p} {g : Co Φ.A q}
    (hf : In (Fil a) f) (hg : In (Fil b) g) (hc : a + b = c) : In (Fil c) (cp h f g) :=
  In.lvl hc (hf.mulc hF h hg)

theorem In.unit (hF : IsFil Φ Fil) : In (Fil ((0 : ℕ) : ℤ)) (one : Co Φ.A 0) := fun s => by
  rw [hF.top _ (by simp)]; trivial

def gm (a : Co Φ.A 1) : Co Φ.A 1 := fun s => Φ.dp 2 (a s)

theorem dd_gm {a : Co Φ.A 1} (hJ : In Φ.J a) (ha : dd 1 a = 0) (h : 1 + 1 = 2) :
    dd 1 (gm a) = -cp h a a := by
  funext s
  have ea := congrFun ha s
  rw [dd_one_apply, Pi.zero_apply] at ea
  have key : ∀ (g : Fin 2 → Fin 3) (hg : Monotone g), tm s (gm a) g hg = Φ.dp 2 (tm s a g hg) := fun g hg =>
    Φ.dp_map _ 2 (hJ (hg.functor ⋙ s))
  rw [dd_one_apply, key, key, key, Pi.neg_apply, cp_one_one_apply]
  have h0 := hJ.tm s (Fin.succAbove 0) (Fin.strictMono_succAbove 0).monotone
  have h2 := hJ.tm s (Fin.succAbove 2) (Fin.strictMono_succAbove 2).monotone
  have e1 : tm s a (Fin.succAbove 1) (Fin.strictMono_succAbove 1).monotone =
      tm s a (Fin.succAbove 2) (Fin.strictMono_succAbove 2).monotone +
      tm s a (Fin.succAbove 0) (Fin.strictMono_succAbove 0).monotone := by linear_combination -ea
  rw [e1, Φ.dp_add 2 h2 h0]
  have e2 : Finset.HasAntidiagonal.antidiagonal 2 = {((0 : ℕ), (2 : ℕ)), (1, 1), (2, 0)} := by decide
  rw [e2, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only []
  rw [Φ.dp_zero h2, Φ.dp_zero h0, Φ.dp_one h2, Φ.dp_one h0]
  ring

def Cob (Fil : ℤ → IdF Φ.A) (m : ℕ) : ∀ n : ℕ, Co Φ.A n → Prop
  | 0, z => In (Fil ((m + 1 : ℕ) : ℤ)) z
  | n + 1, z => ∃ b : Co Φ.A n, In (Fil (m : ℤ)) b ∧ In (Fil ((m + 1 : ℕ) : ℤ)) (z - dd n b)

theorem Cob.of_in {m n : ℕ} {z : Co Φ.A n} (h : In (Fil ((m + 1 : ℕ) : ℤ)) z) : Cob Fil m n z := by
  cases n with
  | zero => exact h
  | succ n => exact ⟨0, In.zero, by rw [dd_zero, sub_zero]; exact h⟩

theorem Cob.add {m n : ℕ} {z z' : Co Φ.A n} (h : Cob Fil m n z) (h' : Cob Fil m n z') : Cob Fil m n (z + z') := by
  cases n with
  | zero => exact In.add h h'
  | succ n =>
    obtain ⟨b, hb, he⟩ := h
    obtain ⟨b', hb', he'⟩ := h'
    refine ⟨b + b', hb.add hb', ?_⟩
    have e : z + z' - dd n (b + b') = (z - dd n b) + (z' - dd n b') := by rw [dd_add]; abel
    rw [e]; exact he.add he'

theorem Cob.neg {m n : ℕ} {z : Co Φ.A n} (h : Cob Fil m n z) : Cob Fil m n (-z) := by
  cases n with
  | zero => exact In.neg h
  | succ n =>
    obtain ⟨b, hb, he⟩ := h
    refine ⟨-b, hb.neg, ?_⟩
    have e : -z - dd n (-b) = -(z - dd n b) := by rw [dd_neg]; abel
    rw [e]; exact he.neg

theorem Cob.of_dd {m n : ℕ} {b : Co Φ.A n} (u : ℤ) (h : In (Fil (m : ℤ)) b) : Cob Fil m (n + 1) (u • dd n b) :=
  ⟨u • b, h.zsmul u, by rw [dd_zsmul, sub_self]; exact In.zero⟩

theorem Cob.cp_right (hF : IsFil Φ Fil) {m n p k q : ℕ} (h : n + p = k) {z : Co Φ.A n} {y : Co Φ.A p}
    (hz : Cob Fil m n z) (hy : In (Fil (q : ℤ)) y) (hdy : In (Fil ((q + 1 : ℕ) : ℤ)) (dd p y)) :
    Cob Fil (m + q) k (cp h z y) := by
  cases n with
  | zero =>
    exact Cob.of_in (In.mulc' hF h hz hy (by omega))
  | succ n =>
    obtain ⟨b, hb, he⟩ := hz
    cases k with
    | zero => omega
    | succ k =>
      have h' : n + p = k := by omega
      have e : cp h z y = cp h (z - dd n b) y + dd k (cp h' b y) - ((-1 : ℤ) ^ n) • cp (by omega) b (dd p y) := by
        rw [dd_cp h', cp_sub_left]; abel
      rw [e]
      refine ⟨cp h' b y, In.mulc' hF h' hb hy rfl, ?_⟩
      have e' : cp h (z - dd n b) y + dd k (cp h' b y) - ((-1 : ℤ) ^ n) • cp (by omega) b (dd p y) - dd k (cp h' b y) =
          cp h (z - dd n b) y - ((-1 : ℤ) ^ n) • cp (show n + (p + 1) = k + 1 by omega) b (dd p y) := by abel
      rw [e']
      exact (In.mulc' hF h he hy (by omega)).sub ((In.mulc' hF _ hb hdy (by omega)).zsmul _)

end
end GlobalTheory.CompanionTheory.AltForm

namespace GlobalTheory.CompanionTheory.AltForm
noncomputable section
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
variable {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

def Coc (Fil : ℤ → IdF Φ.A) (a : Co Φ.A 1) : Prop := In (Fil ((1 : ℕ) : ℤ)) a ∧ dd 1 a = 0

noncomputable def wd : ∀ j : ℕ, (Fin j → Co Φ.A 1) → Co Φ.A j
  | 0, _ => one
  | j + 1, c => cp rfl (wd j (c ∘ Fin.castSucc)) (c (Fin.last j))

theorem wd_mem (hF : IsFil Φ Fil) : ∀ (j : ℕ) (c : Fin j → Co Φ.A 1), (∀ k, Coc Fil (c k)) →
    In (Fil (j : ℤ)) (wd j c) ∧ dd j (wd j c) = 0
  | 0, c, _ => ⟨In.unit hF, dd_one⟩
  | j + 1, c, hc => by
    obtain ⟨h1, h2⟩ := wd_mem hF j (c ∘ Fin.castSucc) (fun k => hc _)
    refine ⟨In.mulc' hF rfl h1 (hc _).1 rfl, ?_⟩
    change dd (j + 1) (cp rfl _ _) = 0
    rw [dd_cp, h2, (hc _).2, cp_zero_left, cp_zero_right, smul_zero, add_zero]

theorem In.J (hF : IsFil Φ Fil) {n : ℕ} {a : Co Φ.A n} (h : In (Fil ((1 : ℕ) : ℤ)) a) : In Φ.J a := fun s => by
  have := h s
  rw [Nat.cast_one, hF.one] at this
  exact this

theorem In.ofJ (hF : IsFil Φ Fil) {n : ℕ} {a : Co Φ.A n} (h : In Φ.J a) : In (Fil ((1 : ℕ) : ℤ)) a := fun s => by
  rw [Nat.cast_one, hF.one]
  exact h s

theorem In.pw (hF : IsFil Φ Fil) {a b : Co Φ.A 1} (ha : In (Fil ((1 : ℕ) : ℤ)) a) (hb : In (Fil ((1 : ℕ) : ℤ)) b) :
    In (Fil ((2 : ℕ) : ℤ)) (pw a b) := fun s => hF.mul 1 1 _ (ha s) (hb s)

theorem In.gm (hF : IsFil Φ Fil) {a : Co Φ.A 1} (ha : In (Fil ((1 : ℕ) : ℤ)) a) :
    In (Fil ((2 : ℕ) : ℤ)) (gm a) := fun s => hF.dp_mem 2 _ (In.J hF ha s)

theorem cob_top (hF : IsFil Φ Fil) {j : ℕ} {u : Co Φ.A j} (hu : In (Fil (j : ℤ)) u) (hdu : dd j u = 0)
    {p : Co Φ.A 1} (hp : In (Fil ((2 : ℕ) : ℤ)) p) {S : Co Φ.A 2} (hS : dd 1 p = -S) (h : j + 2 = j + 1 + 1) :
    Cob Fil (j + 2) (j + 1 + 1) (cp h u S) := by
  have e : cp h u S = (-((-1 : ℤ) ^ j)) • dd (j + 1) (cp rfl u p) := by
    rw [dd_cp, hdu, cp_zero_left, zero_add, hS, cp_neg_right, smul_smul, neg_mul, ← mul_pow]
    simp
  rw [e]
  exact Cob.of_dd _ (In.mulc' hF rfl hu hp rfl)

theorem cob_swap_top (hF : IsFil Φ Fil) {j : ℕ} {u : Co Φ.A j} (hu : In (Fil (j : ℤ)) u) (hdu : dd j u = 0)
    {a b : Co Φ.A 1} (ha : Coc Fil a) (hb : Coc Fil b) :
    Cob Fil (j + 2) (j + 1 + 1) (cp rfl (cp rfl u a) b + cp rfl (cp rfl u b) a) := by
  have h2 : j + 2 = j + 1 + 1 := rfl
  have e : cp rfl (cp rfl u a) b + cp rfl (cp rfl u b) a = cp h2 u (cp rfl a b + cp rfl b a) := by
    rw [cp_add_right, cp_assoc rfl rfl rfl h2, cp_assoc rfl rfl rfl h2]
  rw [e]
  exact cob_top hF hu hdu (In.pw hF ha.1 hb.1) (dd_pw ha.2 hb.2 rfl) h2

theorem cob_sq_top (hF : IsFil Φ Fil) {j : ℕ} {u : Co Φ.A j} (hu : In (Fil (j : ℤ)) u) (hdu : dd j u = 0)
    {a : Co Φ.A 1} (ha : Coc Fil a) :
    Cob Fil (j + 2) (j + 1 + 1) (cp rfl (cp rfl u a) a) := by
  have h2 : j + 2 = j + 1 + 1 := rfl
  rw [cp_assoc rfl rfl rfl h2]
  exact cob_top hF hu hdu (In.gm hF ha.1) (dd_gm (In.J hF ha.1) ha.2 rfl) h2

theorem swap_castSucc {j : ℕ} (k' : Fin j) (i : Fin (j + 1)) :
    Equiv.swap k'.castSucc.castSucc k'.castSucc.succ i.castSucc =
      (Equiv.swap k'.castSucc k'.succ i).castSucc := by
  rw [Fin.succ_castSucc]
  exact Function.Injective.swap_apply (Fin.castSucc_injective _) _ _ _

theorem wd_swap (hF : IsFil Φ Fil) : ∀ (j : ℕ) (c : Fin (j + 1) → Co Φ.A 1), (∀ k, Coc Fil (c k)) → ∀ k : Fin j,
    Cob Fil (j + 1) (j + 1) (wd (j + 1) c + wd (j + 1) (c ∘ Equiv.swap k.castSucc k.succ))
  | 0, c, _, k => k.elim0
  | j + 1, c, hc, k => by
    induction k using Fin.lastCases with
    | last =>
      have e1 : ((c ∘ Equiv.swap (Fin.last j).castSucc (Fin.last j).succ) ∘ Fin.castSucc) ∘ Fin.castSucc =
          (c ∘ Fin.castSucc) ∘ Fin.castSucc := by
        funext i
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne]
        · exact fun h => (Fin.castSucc_lt_last i).ne (Fin.castSucc_injective _ h)
        · rw [Fin.succ_last]; exact (Fin.castSucc_lt_last _).ne
      have e2 : (c ∘ Equiv.swap (Fin.last j).castSucc (Fin.last j).succ) (Fin.last (j + 1)) = c (Fin.last j).castSucc := by
        simp only [Function.comp_apply]
        rw [← Fin.succ_last, Equiv.swap_apply_right]
      have e3 : (c ∘ Equiv.swap (Fin.last j).castSucc (Fin.last j).succ) (Fin.last j).castSucc = c (Fin.last (j + 1)) := by
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_left, Fin.succ_last]
      have w1 : wd (j + 1 + 1) (c ∘ Equiv.swap (Fin.last j).castSucc (Fin.last j).succ) =
          cp rfl (cp rfl (wd j ((c ∘ Fin.castSucc) ∘ Fin.castSucc)) (c (Fin.last (j + 1)))) (c (Fin.last j).castSucc) := by
        change cp rfl (cp rfl (wd j (((c ∘ Equiv.swap (Fin.last j).castSucc (Fin.last j).succ) ∘ Fin.castSucc) ∘ Fin.castSucc))
          ((c ∘ Equiv.swap (Fin.last j).castSucc (Fin.last j).succ) (Fin.last j).castSucc))
          ((c ∘ Equiv.swap (Fin.last j).castSucc (Fin.last j).succ) (Fin.last (j + 1))) = _
        rw [e1, e2, e3]
      rw [w1]
      obtain ⟨hu, hdu⟩ := wd_mem hF j ((c ∘ Fin.castSucc) ∘ Fin.castSucc) (fun k => hc _)
      exact cob_swap_top hF hu hdu (hc _) (hc _)
    | cast k' =>
      have e1 : (c ∘ Equiv.swap k'.castSucc.castSucc k'.castSucc.succ) ∘ Fin.castSucc =
          (c ∘ Fin.castSucc) ∘ Equiv.swap k'.castSucc k'.succ := by
        funext i
        simp only [Function.comp_apply]
        rw [swap_castSucc]
      have e2 : (c ∘ Equiv.swap k'.castSucc.castSucc k'.castSucc.succ) (Fin.last (j + 1)) = c (Fin.last (j + 1)) := by
        simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne]
        · exact (Fin.castSucc_lt_last _).ne'
        · rw [Fin.succ_castSucc]; exact (Fin.castSucc_lt_last _).ne'
      have w1 : wd (j + 1 + 1) (c ∘ Equiv.swap k'.castSucc.castSucc k'.castSucc.succ) =
          cp rfl (wd (j + 1) ((c ∘ Fin.castSucc) ∘ Equiv.swap k'.castSucc k'.succ)) (c (Fin.last (j + 1))) := by
        change cp rfl (wd (j + 1) ((c ∘ Equiv.swap k'.castSucc.castSucc k'.castSucc.succ) ∘ Fin.castSucc))
          ((c ∘ Equiv.swap k'.castSucc.castSucc k'.castSucc.succ) (Fin.last (j + 1))) = _
        rw [e1, e2]
      rw [w1]
      change Cob Fil (j + 1 + 1) (j + 1 + 1) (cp rfl (wd (j + 1) (c ∘ Fin.castSucc)) (c (Fin.last (j + 1))) + _)
      rw [← cp_add_left]
      exact Cob.cp_right (q := 1) hF rfl (wd_swap hF j (c ∘ Fin.castSucc) (fun k => hc _) k') (hc _).1
        (by rw [(hc _).2]; exact In.zero)

theorem wd_sq (hF : IsFil Φ Fil) : ∀ (j : ℕ) (c : Fin (j + 1) → Co Φ.A 1), (∀ k, Coc Fil (c k)) → ∀ k : Fin j,
    c k.castSucc = c k.succ → Cob Fil (j + 1) (j + 1) (wd (j + 1) c)
  | 0, c, _, k, _ => k.elim0
  | j + 1, c, hc, k, hk => by
    induction k using Fin.lastCases with
    | last =>
      rw [Fin.succ_last] at hk
      have w1 : wd (j + 1 + 1) c =
          cp rfl (cp rfl (wd j ((c ∘ Fin.castSucc) ∘ Fin.castSucc)) (c (Fin.last j).castSucc)) (c (Fin.last j).castSucc) := by
        change cp rfl (cp rfl (wd j ((c ∘ Fin.castSucc) ∘ Fin.castSucc)) (c (Fin.last j).castSucc)) (c (Fin.last (j + 1))) = _
        rw [← hk]
      rw [w1]
      obtain ⟨hu, hdu⟩ := wd_mem hF j ((c ∘ Fin.castSucc) ∘ Fin.castSucc) (fun k => hc _)
      exact cob_sq_top hF hu hdu (hc _)
    | cast k' =>
      exact Cob.cp_right (q := 1) hF rfl (wd_sq hF j (c ∘ Fin.castSucc) (fun k => hc _) k'
        (by simp only [Function.comp_apply]; rw [hk, Fin.succ_castSucc])) (hc _).1
        (by rw [(hc _).2]; exact In.zero)

theorem wd_change (hF : IsFil Φ Fil) : ∀ (j : ℕ) (c c' : Fin j → Co Φ.A 1) (b : Fin j → Co Φ.A 0), (∀ k, Coc Fil (c k)) →
    (∀ k, Coc Fil (c' k)) → (∀ k, In (Fil ((1 : ℕ) : ℤ)) (b k)) → (∀ k, c' k - c k = dd 0 (b k)) →
    Cob Fil j j (wd j c' - wd j c)
  | 0, c, c', b, _, _, _, _ => by
    change Cob Fil 0 0 (one - one)
    rw [sub_self]
    exact In.zero
  | j + 1, c, c', b, hc, hc', hb, hd => by
    obtain ⟨hu, hdu⟩ := wd_mem hF j (c ∘ Fin.castSucc) (fun k => hc _)
    have ih := wd_change hF j (c ∘ Fin.castSucc) (c' ∘ Fin.castSucc) (b ∘ Fin.castSucc) (fun k => hc _) (fun k => hc' _)
      (fun k => hb _) (fun k => hd _)
    have hz : j + 0 = j := rfl
    have e : wd (j + 1) c' - wd (j + 1) c = cp rfl (wd j (c' ∘ Fin.castSucc) - wd j (c ∘ Fin.castSucc)) (c' (Fin.last j)) +
        ((-1 : ℤ) ^ j) • dd j (cp hz (wd j (c ∘ Fin.castSucc)) (b (Fin.last j))) := by
      have e1 : c' (Fin.last j) = c (Fin.last j) + dd 0 (b (Fin.last j)) := by rw [← hd]; abel
      rw [dd_cp, hdu, cp_zero_left, zero_add, smul_smul, ← mul_pow]
      change cp rfl (wd j (c' ∘ Fin.castSucc)) (c' (Fin.last j)) - cp rfl (wd j (c ∘ Fin.castSucc)) (c (Fin.last j)) = _
      rw [cp_sub_left]
      nth_rewrite 3 [e1]
      rw [cp_add_right]
      simp
      abel
    rw [e]
    exact (Cob.cp_right (q := 1) hF rfl ih (hc' _).1 (by rw [(hc' _).2]; exact In.zero)).add
      (Cob.of_dd _ (In.mulc' hF hz hu (hb _) rfl))

end
end GlobalTheory.CompanionTheory.AltForm

namespace GlobalTheory.CompanionTheory.AltForm
noncomputable section
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

section rep
variable {A : C ⥤ CommAlgCat.{0} R}

def pj (a b : IdF A) {n : ℕ} (z : Co A n) (hz : In a z) : CH.Cn (sq a b) n := fun s => sqMk a b (z s) (hz s)

theorem d_pj (a b : IdF A) {n : ℕ} (z : Co A n) (hz : In a z) (s : ComposableArrows C (n + 1)) :
    (show sqM a b _ from CH.d (sq a b) n (pj a b z hz) s).1 = Ideal.Quotient.mk _ (dd n z s) := by
  change (sqM a b _).subtype (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
    ((sq a b).map (GlobalTheory.CatH.toLast i s)).hom (pj a b z hz (GlobalTheory.CatH.face i s))) =
    Ideal.Quotient.mk _ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • tm s z i.succAbove (Fin.strictMono_succAbove i).monotone)
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul]
  rfl

theorem Rep.zsmul {a b : IdF A} {n : ℕ} {z : Co A n} {c : CH.H (sq a b) n} (u : ℤ) (h : Rep a b z c) :
    Rep a b (u • z) (u • c) := by
  obtain ⟨f, hf, rfl, hv⟩ := h
  refine ⟨u • f, by rw [map_zsmul, hf, smul_zero], ?_, fun s => ?_⟩
  · exact (map_zsmul (Submodule.mkQ _) u _).symm
  · change u • (show sqM a b _ from f s).1 = Ideal.Quotient.mk _ (u • z s)
    rw [hv s, map_zsmul]

theorem Rep.unique {a b : IdF A} {n : ℕ} {z : Co A n} {c c' : CH.H (sq a b) n} (h : Rep a b z c) (h' : Rep a b z c') :
    c = c' := by
  obtain ⟨f, hf, rfl, hv⟩ := h
  obtain ⟨f', hf', rfl, hv'⟩ := h'
  obtain rfl : f = f' := funext fun s => Subtype.ext ((hv s).trans (hv' s).symm)
  rfl

theorem Rep.zero (a b : IdF A) (n : ℕ) : Rep a b (0 : Co A n) 0 := by
  refine ⟨0, map_zero _, ?_, fun s => ?_⟩
  · exact (Submodule.Quotient.mk_zero _).symm
  · exact (map_zero (Ideal.Quotient.mk _)).symm
end rep

variable {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

theorem Rep.of_cob {m n : ℕ} {z z' : Co Φ.A n} {c : CH.H (gr Fil (m : ℤ)) n} (h : Rep (Fil m) (Fil ((m : ℤ) + 1)) z c)
    (hc : Cob Fil m n (z' - z)) : Rep (Fil m) (Fil ((m : ℤ) + 1)) z' c := by
  have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; rfl
  obtain ⟨f, hf, rfl, hv⟩ := h
  cases n with
  | zero =>
    refine ⟨f, hf, rfl, fun s => ?_⟩
    rw [hv s]
    have := hc s
    rw [hcast] at this
    exact Ideal.Quotient.eq.2 (by simpa using (Ideal.neg_mem_iff _).2 this)
  | succ n =>
    obtain ⟨β, hβ, he⟩ := hc
    rw [hcast] at he
    refine ⟨f + CH.d (gr Fil (m : ℤ)) n (pj _ _ β hβ), ?_, ?_, fun s => ?_⟩
    · rw [map_add, hf, zero_add]
      exact CH.d_d _ n _
    · refine (Submodule.Quotient.eq _).2 ?_
      refine ⟨-pj _ _ β hβ, ?_⟩
      change CH.d (gr Fil (m : ℤ)) n (-pj _ _ β hβ) = f - (f + CH.d (gr Fil (m : ℤ)) n (pj _ _ β hβ))
      rw [map_neg]; abel
    · change (show sqM _ _ _ from f s).1 + (show sqM _ _ _ from CH.d (gr Fil (m : ℤ)) n (pj _ _ β hβ) s).1 = _
      rw [hv s, d_pj, ← map_add]
      refine Ideal.Quotient.eq.2 ?_
      have := he s
      have e : z s + dd n β s - z' s = -((z' - z - dd n β) s) := by
        simp only [Pi.sub_apply]; ring
      rw [e]
      exact (Ideal.neg_mem_iff _).2 this

theorem Rep.eq_zero_of_cob {m n : ℕ} {z : Co Φ.A n} {c : CH.H (gr Fil (m : ℤ)) n} (h : Rep (Fil m) (Fil ((m : ℤ) + 1)) z c)
    (hc : Cob Fil m n z) : c = 0 :=
  Rep.unique h (Rep.of_cob (Rep.zero _ _ n) (by simpa using hc))

end
end GlobalTheory.CompanionTheory.AltForm

namespace GlobalTheory.CompanionTheory.AltForm
noncomputable section
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
variable {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

def pr {j : ℕ} (k : Fin j) : Fin 2 → Fin (j + 1) := fun i => ⟨k + i, by omega⟩

theorem pr_mono {j : ℕ} (k : Fin j) : Monotone (pr k) := fun a b hab =>
  show (k : ℕ) + a ≤ k + b from Nat.add_le_add_left hab _

theorem tm_sub {p m n : ℕ} (s : ComposableArrows C n) (f : Co Φ.A p) (g : Fin (m + 1) → Fin (n + 1)) (hg : Monotone g)
    (g' : Fin (p + 1) → Fin (m + 1)) (hg' : Monotone g') :
    (Φ.A.map (s.map (homOfLE (Fin.le_last (g (Fin.last m)))))).hom (tm (hg.functor ⋙ s) f g' hg') =
      tm s f (g ∘ g') (hg.comp hg') :=
  GlobalTheory.CompanionTheory.CupAssocC.term_term (CH.modF Φ.A) s f g hg g' hg'

theorem tm_id {n : ℕ} (s : ComposableArrows C n) (f : Co Φ.A n) : tm s f id monotone_id = f s :=
  GlobalTheory.CompanionTheory.CupAssocC.term_id (CH.modF Φ.A) s f

theorem wd_apply : ∀ (j : ℕ) (c : Fin j → Co Φ.A 1) (s : ComposableArrows C j),
    wd j c s = ∏ k : Fin j, tm s (c k) (pr k) (pr_mono k)
  | 0, c, s => by simp; rfl
  | j + 1, c, s => by
    change cp rfl (wd j (c ∘ Fin.castSucc)) (c (Fin.last j)) s = _
    rw [cp_apply, Fin.prod_univ_castSucc]
    congr 1
    · change (Φ.A.map (s.map (homOfLE (Fin.le_last (CH.front (rfl : j + 1 = j + 1) (Fin.last j)))))).hom
        (wd j (c ∘ Fin.castSucc) ((CH.front_mono (rfl : j + 1 = j + 1)).functor ⋙ s)) = _
      rw [wd_apply, map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [tm_sub]
      exact tm_congr s _ _ _ (funext fun i => Fin.ext (by simp [pr, CH.front]))

variable {d : ℕ} (E : Frame Φ d)

def ca (σ : ∀ T : C, E.D ⟶ T) (i : Fin d) : Co Φ.A 1 := fun s => E.a σ i (s.map (homOfLE (Fin.le_last 0)))

def cx (σ : ∀ T : C, E.D ⟶ T) (x : Φ.A.obj E.D) : Co Φ.A 0 := fun s => (Φ.A.map (σ (s.obj (Fin.last 0)))).hom x

def cb (σ σ' : ∀ T : C, E.D ⟶ T) (i : Fin d) : Co Φ.A 0 := fun s => E.τ i (σ _) (σ' _)

theorem form_eq (σ : ∀ T : C, E.D ⟶ T) {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) :
    E.form σ I x = cp (Nat.add_zero j) (wd j fun k => ca E σ (I k)) (cx E σ x) := by
  funext s
  rw [cp_apply, tm_congr s _ (CH.front_mono _) monotone_id (funext fun i => Fin.ext (by simp [CH.front])), tm_id, wd_apply]
  have id1 : s.map (homOfLE (Fin.le_last (CH.back (Nat.add_zero j) (Fin.last 0)))) = 𝟙 _ := by
    rw [← s.map_id]; rfl
  refine congrArg₂ (· * ·) rfl ?_
  change _ = (Φ.A.map (s.map (homOfLE (Fin.le_last (CH.back (Nat.add_zero j) (Fin.last 0)))))).hom _
  rw [id1, Φ.A.map_id]
  rfl

theorem a_comp (σ : ∀ T : C, E.D ⟶ T) (i : Fin d) {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    E.a σ i (φ ≫ ψ) = (Φ.A.map ψ).hom (E.a σ i φ) + E.a σ i ψ := by
  unfold Frame.a
  rw [← E.nat, E.add i _ (σ T' ≫ ψ) _]
  simp only [Category.assoc]

theorem ca_coc (hF : IsFil Φ Fil) (σ : ∀ T : C, E.D ⟶ T) (i : Fin d) : Coc Fil (ca E σ i) := by
  refine ⟨In.ofJ hF fun s => E.mem i _ _, ?_⟩
  funext s
  rw [dd_one_apply]
  have id2 : s.map (homOfLE (Fin.le_last (Fin.last 2))) = 𝟙 _ := by
    rw [← s.map_id]; rfl
  have e : s.map (homOfLE (show (0 : Fin 3) ≤ Fin.last 2 by decide)) =
      s.map (homOfLE (show (0 : Fin 3) ≤ 1 by decide)) ≫ s.map (homOfLE (show (1 : Fin 3) ≤ Fin.last 2 by decide)) := by
    rw [← s.map_comp]; rfl
  have e0 : tm s (ca E σ i) (Fin.succAbove 0) (Fin.strictMono_succAbove 0).monotone =
      E.a σ i (s.map (homOfLE (show (1 : Fin 3) ≤ Fin.last 2 by decide))) := by
    change (Φ.A.map (s.map (homOfLE (Fin.le_last (Fin.last 2))))).hom _ = _
    rw [id2, Φ.A.map_id]; rfl
  have e1 : tm s (ca E σ i) (Fin.succAbove 1) (Fin.strictMono_succAbove 1).monotone =
      E.a σ i (s.map (homOfLE (show (0 : Fin 3) ≤ Fin.last 2 by decide))) := by
    change (Φ.A.map (s.map (homOfLE (Fin.le_last (Fin.last 2))))).hom _ = _
    rw [id2, Φ.A.map_id]; rfl
  have e2 : tm s (ca E σ i) (Fin.succAbove 2) (Fin.strictMono_succAbove 2).monotone =
      (Φ.A.map (s.map (homOfLE (show (1 : Fin 3) ≤ Fin.last 2 by decide)))).hom
        (E.a σ i (s.map (homOfLE (show (0 : Fin 3) ≤ 1 by decide)))) := rfl
  rw [e0, e1, e2, e, a_comp]
  change _ = (0 : Φ.A.obj _)
  ring

theorem ca_sub (σ σ' : ∀ T : C, E.D ⟶ T) (i : Fin d) : ca E σ' i - ca E σ i = dd 0 (cb E σ σ' i) := by
  funext s
  rw [dd_zero_apply]
  have id1 : s.map (homOfLE (Fin.le_last (Fin.last 1))) = 𝟙 _ := by
    rw [← s.map_id]; rfl
  have e0 : tm s (cb E σ σ' i) (Fin.succAbove 0) (Fin.strictMono_succAbove 0).monotone =
      E.τ i (σ (s.obj (Fin.last 1))) (σ' (s.obj (Fin.last 1))) := by
    change (Φ.A.map (s.map (homOfLE (Fin.le_last (Fin.last 1))))).hom _ = _
    rw [id1, Φ.A.map_id]; rfl
  have e1 : tm s (cb E σ σ' i) (Fin.succAbove 1) (Fin.strictMono_succAbove 1).monotone =
      E.τ i (σ (s.obj 0) ≫ s.map (homOfLE (Fin.le_last 0))) (σ' (s.obj 0) ≫ s.map (homOfLE (Fin.le_last 0))) :=
    (E.nat i _ _ _).symm
  rw [e0, e1]
  change E.τ i (σ' _ ≫ _) (σ' _) - E.τ i (σ _ ≫ _) (σ _) = _
  have h1 := E.add i (σ (s.obj 0) ≫ s.map (homOfLE (Fin.le_last 0))) (σ' (s.obj 0) ≫ s.map (homOfLE (Fin.le_last 0)))
    (σ' (s.obj (Fin.last 1)))
  have h2 := E.add i (σ (s.obj 0) ≫ s.map (homOfLE (Fin.le_last 0))) (σ (s.obj (Fin.last 1))) (σ' (s.obj (Fin.last 1)))
  linear_combination h2 - h1

end
end GlobalTheory.CompanionTheory.AltForm

namespace GlobalTheory.CompanionTheory.AltForm
noncomputable section
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
variable {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
variable {d : ℕ} (E : Frame Φ d)

theorem cx_mem (σ : ∀ T : C, E.D ⟶ T) {q : ℕ} {x : Φ.A.obj E.D} (hx : x ∈ (Fil q).S E.D) :
    In (Fil (q : ℤ)) (cx E σ x) := fun s => (Fil q).map_mem _ hx

theorem cx_sub (hc : E.GrConst Fil) (σ σ' : ∀ T : C, E.D ⟶ T) {q : ℕ} {x : Φ.A.obj E.D} (hx : x ∈ (Fil q).S E.D) :
    In (Fil ((q + 1 : ℕ) : ℤ)) (cx E σ' x - cx E σ x) := fun s => by
  have hcast : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; rfl
  rw [hcast]
  exact hc q _ _ hx

theorem cx_dd (hc : E.GrConst Fil) (σ : ∀ T : C, E.D ⟶ T) {q : ℕ} {x : Φ.A.obj E.D} (hx : x ∈ (Fil q).S E.D) :
    In (Fil ((q + 1 : ℕ) : ℤ)) (dd 0 (cx E σ x)) := fun s => by
  have hcast : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; rfl
  rw [hcast, dd_zero_apply]
  have id1 : s.map (homOfLE (Fin.le_last (Fin.last 1))) = 𝟙 _ := by
    rw [← s.map_id]; rfl
  have e0 : tm s (cx E σ x) (Fin.succAbove 0) (Fin.strictMono_succAbove 0).monotone =
      (Φ.A.map (σ (s.obj (Fin.last 1)))).hom x := by
    change (Φ.A.map (s.map (homOfLE (Fin.le_last (Fin.last 1))))).hom _ = _
    rw [id1, Φ.A.map_id]; rfl
  have e1 : tm s (cx E σ x) (Fin.succAbove 1) (Fin.strictMono_succAbove 1).monotone =
      (Φ.A.map (σ (s.obj 0) ≫ s.map (homOfLE (Fin.le_last 0)))).hom x := by
    rw [Φ.A.map_comp]; rfl
  rw [e0, e1]
  exact hc q _ _ hx

theorem rep_swap (hF : IsFil Φ Fil) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) {j q : ℕ}
    {x : Φ.A.obj E.D} (hx : x ∈ (Fil q).S E.D) (I : Fin (j + 1) → Fin d) (k : Fin j)
    {c : CH.H (gr Fil ((j + 1 + q : ℕ) : ℤ)) (j + 1)}
    (h : Rep (Fil ((j + 1 + q : ℕ) : ℤ)) (Fil (((j + 1 + q : ℕ) : ℤ) + 1)) (E.form σ I x) c) :
    Rep (Fil ((j + 1 + q : ℕ) : ℤ)) (Fil (((j + 1 + q : ℕ) : ℤ) + 1)) (E.form σ (I ∘ Equiv.swap k.castSucc k.succ) x)
      ((-1 : ℤ) • c) := by
  refine Rep.of_cob (Rep.zsmul (-1) h) ?_
  have key := Cob.cp_right (q := q) hF (Nat.add_zero (j + 1)) (wd_swap hF j (fun k => ca E σ (I k)) (fun k => ca_coc E hF σ _) k)
    (cx_mem E σ hx) (cx_dd E hc σ hx)
  rw [cp_add_left] at key
  have e : ∀ X Y : Co Φ.A (j + 1), Y - (-1 : ℤ) • X = X + Y := by
    intro X Y; rw [neg_one_zsmul]; abel
  rw [e, form_eq, form_eq]
  exact key

theorem rep_perm (hF : IsFil Φ Fil) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) {j q : ℕ}
    {x : Φ.A.obj E.D} (hx : x ∈ (Fil q).S E.D) (π : Equiv.Perm (Fin j)) :
    ∀ (I : Fin j → Fin d) (c : CH.H (gr Fil ((j + q : ℕ) : ℤ)) j),
    Rep (Fil ((j + q : ℕ) : ℤ)) (Fil (((j + q : ℕ) : ℤ) + 1)) (E.form σ I x) c →
    Rep (Fil ((j + q : ℕ) : ℤ)) (Fil (((j + q : ℕ) : ℤ) + 1)) (E.form σ (I ∘ π) x) ((Equiv.Perm.sign π : ℤ) • c) := by
  cases j with
  | zero =>
    obtain rfl : π = 1 := Subsingleton.elim _ _
    intro I c h
    simpa using h
  | succ j =>
    have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin j => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
    induction hπ using Submonoid.closure_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      intro I c h
      have hne : k.castSucc ≠ k.succ := (Fin.castSucc_lt_succ (i := k)).ne
      simp only [Equiv.Perm.sign_swap hne]
      simpa using rep_swap E hF σ hc hx I k h
    | one =>
      intro I c h
      simpa using h
    | mul y z _ _ hy hz =>
      intro I c h
      have := hz _ _ (hy I c h)
      rw [smul_smul] at this
      have e : I ∘ ⇑(y * z) = (I ∘ y) ∘ z := by
        funext i; simp
      rw [e, Equiv.Perm.sign_mul, Units.val_mul, mul_comm]
      exact this

theorem rep_sq (hF : IsFil Φ Fil) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) {j q : ℕ}
    {x : Φ.A.obj E.D} (hx : x ∈ (Fil q).S E.D) (I : Fin (j + 1) → Fin d) (k : Fin j) (hk : I k.castSucc = I k.succ)
    {c : CH.H (gr Fil ((j + 1 + q : ℕ) : ℤ)) (j + 1)}
    (h : Rep (Fil ((j + 1 + q : ℕ) : ℤ)) (Fil (((j + 1 + q : ℕ) : ℤ) + 1)) (E.form σ I x) c) : c = 0 := by
  refine Rep.eq_zero_of_cob h ?_
  rw [form_eq]
  exact Cob.cp_right (q := q) hF _ (wd_sq hF j (fun k => ca E σ (I k)) (fun k => ca_coc E hF σ _) k (by simp only [hk]))
    (cx_mem E σ hx) (cx_dd E hc σ hx)

theorem rep_change (hF : IsFil Φ Fil) (σ σ' : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) {j q : ℕ}
    {x : Φ.A.obj E.D} (hx : x ∈ (Fil q).S E.D) (I : Fin j → Fin d)
    {c : CH.H (gr Fil ((j + q : ℕ) : ℤ)) j}
    (h : Rep (Fil ((j + q : ℕ) : ℤ)) (Fil (((j + q : ℕ) : ℤ) + 1)) (E.form σ I x) c) :
    Rep (Fil ((j + q : ℕ) : ℤ)) (Fil (((j + q : ℕ) : ℤ) + 1)) (E.form σ' I x) c := by
  refine Rep.of_cob h ?_
  rw [form_eq, form_eq]
  have e : ∀ (u u' : Co Φ.A j) (y y' : Co Φ.A 0), cp (Nat.add_zero j) u' y' - cp (Nat.add_zero j) u y =
      cp (Nat.add_zero j) (u' - u) y' + cp (Nat.add_zero j) u (y' - y) := by
    intro u u' y y'
    rw [cp_sub_left, cp_sub_right]; abel
  rw [e]
  have hw := wd_mem hF j (fun k => ca E σ (I k)) (fun k => ca_coc E hF σ _)
  refine Cob.add (Cob.cp_right (q := q) hF _ (wd_change hF j (fun k => ca E σ (I k)) (fun k => ca E σ' (I k))
    (fun k => cb E σ σ' (I k)) (fun k => ca_coc E hF σ _) (fun k => ca_coc E hF σ' _)
    (fun k => In.ofJ hF fun s => E.mem _ _ _) (fun k => ca_sub E σ σ' _)) (cx_mem E σ' hx) (cx_dd E hc σ' hx))
    (Cob.of_in (In.mulc' hF _ hw.1 (cx_sub E hc σ σ' hx) (by omega)))

end
end GlobalTheory.CompanionTheory.AltForm

namespace GlobalTheory.CompanionTheory.AltForm

theorem form_alternating : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil)
    {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D) (c : CH.H (gr Fil r) j),
    Rep (Fil r) (Fil (r + 1)) (E.form σ I x) c →
      (¬ Function.Injective I → c = 0) ∧
      (∀ π : Equiv.Perm (Fin j), Rep (Fil r) (Fil (r + 1)) (E.form σ (I ∘ π) x) ((Equiv.Perm.sign π : ℤ) • c)) ∧
      ∀ σ' : ∀ T : C, E.D ⟶ T, Rep (Fil r) (Fil (r + 1)) (E.form σ' I x) c := by
  intro R _ C _ Φ Fil hF d E σ hc j q r hr I x hx c h
  have hr' : r = ((j + q : ℕ) : ℤ) := by push_cast; exact hr
  subst hr'
  refine ⟨fun hI => ?_, fun π => rep_perm E hF σ hc hx π I c h, fun σ' => rep_change E hF σ σ' hc hx I h⟩
  have hex : ∃ a b, a < b ∧ I a = I b := by
    obtain ⟨a, b, hab, hne⟩ : ∃ a b, I a = I b ∧ a ≠ b := by simpa [Function.Injective] using hI
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨a, b, hlt, hab⟩
    · exact ⟨b, a, hlt, hab.symm⟩
  obtain ⟨a, b, hlt, hab⟩ := hex
  cases j with
  | zero => exact a.elim0
  | succ j =>
    have ha : (a : ℕ) < j := by have := b.isLt; have : (a : ℕ) < b := hlt; omega
    let k : Fin j := ⟨a, ha⟩
    have hka : k.castSucc = a := Fin.ext rfl
    have hne : k.castSucc ≠ k.succ := (Fin.castSucc_lt_succ (i := k)).ne
    have hnb : k.castSucc ≠ b := by rw [hka]; exact hlt.ne
    have h1 := rep_perm E hF σ hc hx (Equiv.swap k.succ b) I c h
    have h2 : (I ∘ Equiv.swap k.succ b) k.castSucc = (I ∘ Equiv.swap k.succ b) k.succ := by
      simp only [Function.comp_apply]
      rw [Equiv.swap_apply_of_ne_of_ne hne hnb, Equiv.swap_apply_left, hka, hab]
    have h3 := rep_sq E hF σ hc hx _ k h2 h1
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap k.succ b)) with e | e
    · rw [e] at h3; simpa using h3
    · rw [e] at h3; simpa using h3

end GlobalTheory.CompanionTheory.AltForm
