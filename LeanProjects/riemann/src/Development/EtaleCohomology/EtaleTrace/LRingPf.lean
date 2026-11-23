import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleTrace.LRingPf

section Cast
variable {q : ℕ} {E : Spc}

theorem cast_cast {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'') (x : Ht q E n i) :
    Ht.cast h3 h4 (Ht.cast h1 h2 x) = Ht.cast (h1.trans h3) (h2.trans h4) x := by
  subst h1 h2 h3 h4; rfl

theorem cast_add {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x y : Ht q E n i) :
    Ht.cast h1 h2 (x + y) = Ht.cast h1 h2 x + Ht.cast h1 h2 y := by
  subst h1 h2; rfl

theorem cast_nsmul {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (k : ℕ) (x : Ht q E n i) :
    Ht.cast h1 h2 (k • x) = k • Ht.cast h1 h2 x := by
  subst h1 h2; rfl

theorem cast_usmul {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (k : ℤˣ) (x : Ht q E n i) :
    Ht.cast h1 h2 (k • x) = k • Ht.cast h1 h2 x := by
  subst h1 h2; rfl

theorem red_cast (Q q' : ℕ) {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht Q E n i) :
    red Q q' E n' i' (Ht.cast h1 h2 x) = Ht.cast h1 h2 (red Q q' E n i x) := by
  subst h1 h2; rfl

theorem pull_cast {E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast h1 h2 x) = Ht.cast h1 h2 (pull _ f _ _ x : Ht q E n i) := by
  subst h1 h2; rfl

theorem cup_cast_left {n m i j n' i' : ℤ} (h1 : n = n') (h2 : i = i') (a : Ht q E n i) (b : Ht q E m j) :
    cup q (Ht.cast h1 h2 a) b = Ht.cast (by rw [h1]) (by rw [h2]) (cup q a b) := by
  subst h1 h2; rfl

theorem cup_cast_right {n m i j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (a : Ht q E n i) (b : Ht q E m j) :
    cup q a (Ht.cast h1 h2 b) = Ht.cast (by rw [h1]) (by rw [h2]) (cup q a b) := by
  subst h1 h2; rfl

end Cast

section BC
variable {R A M N P : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

def bc (B : M →ₗ[R] N →ₗ[R] P) : A ⊗[R] M →ₗ[A] A ⊗[R] N →ₗ[A] A ⊗[R] P :=
  TensorProduct.curry ((TensorProduct.lift B).baseChange A ∘ₗ
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap)

theorem bc_tmul (B : M →ₗ[R] N →ₗ[R] P) (a a' : A) (x : M) (y : N) :
    bc B (a ⊗ₜ x) (a' ⊗ₜ y) = (a * a') ⊗ₜ B x y := by
  simp [bc, TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]

theorem tmul_eq (a : A) (x : M) : (a ⊗ₜ[R] x : A ⊗[R] M) = a • ((1 : A) ⊗ₜ x) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end BC

end LateralTheory.EtaleTrace.LRingPf

namespace LateralTheory.EtaleTrace.LRingPf

section SlopeTestRemainingChoices
variable {q : ℕ} {E : Spc} {n m r : ℤ} (h : n + m = r)

theorem cc_add_left (a a' : Ht q E n 0) (b : Ht q E m 0) :
    Ht.cast h (add_zero 0) (cup q (a + a') b) = Ht.cast h (add_zero 0) (cup q a b) + Ht.cast h (add_zero 0) (cup q a' b) := by
  rw [map_add, AddMonoidHom.add_apply, cast_add]

theorem cc_add_right (a : Ht q E n 0) (b b' : Ht q E m 0) :
    Ht.cast h (add_zero 0) (cup q a (b + b')) = Ht.cast h (add_zero 0) (cup q a b) + Ht.cast h (add_zero 0) (cup q a b') := by
  rw [map_add, cast_add]

theorem zsmul_nat [NeZero q] (z : ZMod q) {n i : ℤ} (a : Ht q E n i) : z • a = z.val • a := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact Nat.cast_smul_eq_nsmul (ZMod q) z.val a

theorem cc_smul_left [NeZero q] (z : ZMod q) (a : Ht q E n 0) (b : Ht q E m 0) :
    Ht.cast h (add_zero 0) (cup q (z • a) b) = z • Ht.cast h (add_zero 0) (cup q a b) := by
  rw [zsmul_nat, zsmul_nat, map_nsmul, AddMonoidHom.nsmul_apply, cast_nsmul]

theorem cc_smul_right [NeZero q] (z : ZMod q) (a : Ht q E n 0) (b : Ht q E m 0) :
    Ht.cast h (add_zero 0) (cup q a (z • b)) = z • Ht.cast h (add_zero 0) (cup q a b) := by
  rw [zsmul_nat, zsmul_nat, map_nsmul, cast_nsmul]

theorem red_cc (hB : A11) (Q : ℕ) [NeZero Q] (hd : q ∣ Q) (a : Ht Q E n 0) (b : Ht Q E m 0) :
    red Q q E r 0 (Ht.cast h (add_zero 0) (cup Q a b)) =
      Ht.cast h (add_zero 0) (cup q (red Q q E n 0 a) (red Q q E m 0 b)) := by
  rw [red_cast, (hB Q q hd E).1 a b]

end SlopeTestRemainingChoices

section Adic
variable (l : ℕ) [Fact l.Prime]

instance nz (j : ℕ) : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

omit [Fact l.Prime] in
theorem dvd_succ (j : ℕ) : l ^ j ∣ l ^ (j + 1) := pow_dvd_pow l (Nat.le_succ j)

variable (E : Spc) {n m r : ℤ} (h : n + m = r)

def cupF (x : Hl l E n 0) (y : Hl l E m 0) : ∀ j, HtL l j E r 0 := fun j =>
  Ht.cast h (add_zero 0) (cup (l ^ j) (show Ht (l ^ j) E n 0 from x.1 j) (show Ht (l ^ j) E m 0 from y.1 j))

theorem cupF_mem (hB : A11) (x : Hl l E n 0) (y : Hl l E m 0) : cupF l E h x y ∈ HlSub l E r 0 := by
  intro j
  have hx := x.2 j
  have hy := y.2 j
  exact (red_cc h hB _ (dvd_succ l j) (x.1 (j + 1)) (y.1 (j + 1))).trans <| congrArg₂ (fun a b => Ht.cast h (add_zero 0) (cup (l ^ j) a b)) hx hy

def cupL (hB : A11) : Hl l E n 0 →ₗ[ℤ_[l]] Hl l E m 0 →ₗ[ℤ_[l]] Hl l E r 0 :=
  LinearMap.mk₂ ℤ_[l] (fun x y => ⟨cupF l E h x y, cupF_mem l E h hB x y⟩)
    (fun x x' y => Subtype.ext (funext fun j => cc_add_left h (x.1 j) (x'.1 j) (y.1 j)))
    (fun c x y => Subtype.ext (funext fun j => cc_smul_left h (PadicInt.toZModPow j c) (x.1 j) (y.1 j)))
    (fun x y y' => Subtype.ext (funext fun j => cc_add_right h (x.1 j) (y.1 j) (y'.1 j)))
    (fun c x y => Subtype.ext (funext fun j => cc_smul_right h (PadicInt.toZModPow j c) (x.1 j) (y.1 j)))

theorem cupL_apply (hB : A11) (x : Hl l E n 0) (y : Hl l E m 0) (j : ℕ) :
    (cupL l E h hB x y).1 j = Ht.cast h (add_zero 0) (cup (l ^ j) (show Ht (l ^ j) E n 0 from x.1 j)
      (show Ht (l ^ j) E m 0 from y.1 j)) := rfl

end Adic

end LateralTheory.EtaleTrace.LRingPf

namespace LateralTheory.EtaleTrace.LRingPf

section Ext
variable {R A M N P : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module A P]

theorem ext1 {f g : A ⊗[R] M →ₗ[A] P} (H : ∀ x, f ((1 : A) ⊗ₜ x) = g ((1 : A) ⊗ₜ x)) : f = g := by
  apply LinearMap.ext; intro u
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [tmul_eq, map_smul, map_smul, H]
  | add u u' hu hu' => rw [map_add, map_add, hu, hu']

theorem ext2 {f g : A ⊗[R] M →ₗ[A] A ⊗[R] N →ₗ[A] P}
    (H : ∀ x y, f ((1 : A) ⊗ₜ x) ((1 : A) ⊗ₜ y) = g ((1 : A) ⊗ₜ x) ((1 : A) ⊗ₜ y)) : f = g := by
  apply LinearMap.ext; intro u
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [tmul_eq, map_smul, map_smul]; congr 1; exact ext1 (H x)
  | add u u' hu hu' => rw [map_add, map_add, hu, hu']

end Ext

section Aux2
variable {q : ℕ} {E E' : Spc} {n m r : ℤ} (h : n + m = r)

theorem pull_cc (h6 : DivisorNaturality) [NeZero q] (f : E ⟶ E') (a : Ht q E' n 0) (b : Ht q E' m 0) :
    pull _ f _ _ (Ht.cast h (add_zero 0) (cup q a b)) = Ht.cast h (add_zero 0) (cup q (pull _ f _ _ a) (pull _ f _ _ b)) := by
  rw [pull_cast, (h6 q).1 f a b]

theorem one_cc (h6 : DivisorRingCompatibility) [NeZero q] (hi : GlobalTheory.EtC.Inv q E) (a : Ht q E n 0) :
    Ht.cast (zero_add n) (add_zero 0) (cup q (one q E) a) = a := by
  rw [(h6 q E).1 hi a, cast_cast]; rfl

theorem assoc_cc (h6 : DivisorRingCompatibility) [NeZero q] {k s t w : ℤ} (h1 : n + m = s) (h2 : s + k = w) (h3 : m + k = t) (h4 : n + t = w)
    (a : Ht q E n 0) (b : Ht q E m 0) (c : Ht q E k 0) :
    Ht.cast h2 (add_zero 0) (cup q (Ht.cast h1 (add_zero 0) (cup q a b)) c) =
      Ht.cast h4 (add_zero 0) (cup q a (Ht.cast h3 (add_zero 0) (cup q b c))) := by
  rw [cup_cast_left, cup_cast_right, cast_cast, cast_cast, (h6 q E).2.1 a b c, cast_cast]

theorem comm_cc (h6 : DivisorRingCompatibility) [NeZero q] (h' : m + n = r) (a : Ht q E n 0) (b : Ht q E m 0) :
    Ht.cast h (add_zero 0) (cup q a b) = ((n * m).negOnePow : ℤ) • Ht.cast h' (add_zero 0) (cup q b a) := by
  rw [(h6 q E).2.2 a b, cast_usmul, cast_cast, Units.smul_def]

end Aux2

section V
variable (l : ℕ) [Fact l.Prime]

def cupQ (h11 : A11) (X : Scheme.{0}) {n m r : ℤ} (h : n + m = r) : V l X n →ₗ[ℚ_[l]] V l X m →ₗ[ℚ_[l]] V l X r :=
  bc (cupL l (sch.obj X) h h11)

theorem cupQ_tmul (h11 : A11) (X : Scheme.{0}) {n m r : ℤ} (h : n + m = r) (x : Hl l (sch.obj X) n 0) (y : Hl l (sch.obj X) m 0) :
    cupQ l h11 X h ((1 : ℚ_[l]) ⊗ₜ x) ((1 : ℚ_[l]) ⊗ₜ y) = (1 : ℚ_[l]) ⊗ₜ cupL l (sch.obj X) h h11 x y := by
  rw [cupQ, bc_tmul, mul_one]

theorem isCup_cupQ (h11 : A11) (X : Scheme.{0}) {n m r : ℤ} (h : n + m = r) : IsCup l X h (cupQ l h11 X h) := by
  intro x y z hz
  rw [cupQ_tmul]
  congr 1
  exact Subtype.ext (funext fun j => (hz j).symm)

theorem cupV_eq (h11 : A11) (X : Scheme.{0}) {n m r : ℤ} (h : n + m = r) : cupV l X h = cupQ l h11 X h := by
  have hs : IsCup l X h (cupV l X h) := pick_spec ⟨_, isCup_cupQ l h11 X h⟩
  apply ext2
  intro x y
  rw [hs x y (cupL l (sch.obj X) h h11 x y) (fun j => rfl), cupQ_tmul]

theorem pb_tmul {Y X : Scheme.{0}} (f : Y ⟶ X) (n : ℤ) (x : Hl l (sch.obj X) n 0) :
    pb l f n ((1 : ℚ_[l]) ⊗ₜ x) = (1 : ℚ_[l]) ⊗ₜ pullHl l (sch.map f) n 0 x := by
  simp [pb, pullHQ, LinearMap.baseChange_tmul]

theorem inv_of (X : Scheme.{0}) (hl : IsUnit (l : Γ(X, ⊤))) (j : ℕ) : GlobalTheory.EtC.Inv (l ^ j) (sch.obj X) := by
  intro U hU
  obtain ⟨y⟩ := hU
  let y' : U ⟶ X := y
  rw [Nat.cast_pow]
  apply IsUnit.pow
  simpa using hl.map y'.appTop.hom

theorem unit_pull {Y X : Scheme.{0}} (f : Y ⟶ X) (hl : IsUnit (l : Γ(X, ⊤))) : IsUnit (l : Γ(Y, ⊤)) := by
  simpa using hl.map f.appTop.hom

def z0 (h11 : A11) (X : Scheme.{0}) (hl : IsUnit (l : Γ(X, ⊤))) : Hl l (sch.obj X) 0 0 :=
  ⟨fun j => one (l ^ j) (sch.obj X), fun j => ((h11 _ _ (dvd_succ l j) _).2.1 (inv_of l X hl (j + 1))).1⟩

theorem oneV_eq (h11 : A11) (X : Scheme.{0}) (hl : IsUnit (l : Γ(X, ⊤))) : oneV l X = (1 : ℚ_[l]) ⊗ₜ z0 l h11 X hl := by
  have hs := pick_spec (P := fun c : V l X 0 => ∀ z : Hl l (sch.obj X) 0 0, (∀ j, z.1 j = one (l ^ j) (sch.obj X)) →
    c = 1 ⊗ₜ z) ⟨(1 : ℚ_[l]) ⊗ₜ z0 l h11 X hl, fun z hz => by
      congr 1; exact Subtype.ext (funext fun j => (hz j).symm)⟩
  exact hs _ (fun j => rfl)

end V

end LateralTheory.EtaleTrace.LRingPf

namespace LateralTheory.EtaleTrace

end LateralTheory.EtaleTrace
