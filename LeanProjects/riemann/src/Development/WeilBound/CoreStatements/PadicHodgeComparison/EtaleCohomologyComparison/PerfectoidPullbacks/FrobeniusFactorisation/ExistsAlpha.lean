import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeLimitSystemStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison.Pb.Fa

variable {W A : Type} [CommRing W] [CommRing A] [Algebra W A]

def ev {L T : Type 1} [AddCommGroup L] [Module W L] [AddCommGroup T] [Module A T] (g : L →+ T)
    (hg : ∀ (w : W) y, g (w • y) = algebraMap W A w • g y) : A ⊗[W] L →+ T :=
  TensorProduct.liftAddHom (AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun y => a • g y) fun y y' => by rw [map_add, smul_add])
    fun a a' => AddMonoidHom.ext fun y => add_smul a a' (g y)) fun w a y => by
      change (w • a) • g y = a • g (w • y)
      rw [hg, Algebra.smul_def, mul_comm, mul_smul]

theorem ev_tmul {L T : Type 1} [AddCommGroup L] [Module W L] [AddCommGroup T] [Module A T] (g : L →+ T)
    (hg : ∀ (w : W) y, g (w • y) = algebraMap W A w • g y) (a : A) (y : L) : ev g hg (a ⊗ₜ y) = a • g y := rfl

theorem ev_smul {L T : Type 1} [AddCommGroup L] [Module W L] [AddCommGroup T] [Module A T] (g : L →+ T)
    (hg : ∀ (w : W) y, g (w • y) = algebraMap W A w • g y) (a : A) (z : A ⊗[W] L) : ev g hg (a • z) = a • ev g hg z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b y => rw [TensorProduct.smul_tmul', ev_tmul, ev_tmul, smul_eq_mul, mul_smul]
  | add z z' h h' => rw [smul_add, map_add, map_add, h, h', smul_add]

theorem add_ext {L : Type 1} [AddCommGroup L] [Module W L] {T : Type 1} [AddCommGroup T] {f f' : A ⊗[W] L →+ T}
    (h : ∀ a y, f (a ⊗ₜ y) = f' (a ⊗ₜ y)) (z : A ⊗[W] L) : f z = f' z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b y => exact h b y
  | add z z' h h' => rw [map_add, map_add, h, h']

theorem ev_bij {L T : Type 1} [AddCommGroup L] [Module W L] [AddCommGroup T] [Module A T] (g : L →+ T)
    (hg : ∀ (w : W) y, g (w • y) = algebraMap W A w • g y)
    (h : Tens W (N := fun _ : Unit => A) (M := fun _ => L) (M' := T) fun _ a y => a • g y) : Function.Bijective (ev g hg) := by
  obtain ⟨e, he⟩ := h
  have : ⇑(ev g hg) = e ∘ (fun z => Pi.single () z) := funext fun z =>
    add_ext (f := ev g hg) (f' := e.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Unit => A ⊗[W] L) ())) (fun a y => (he () a y).symm) z
  rw [this]
  exact e.bijective.comp ⟨Pi.single_injective (M := fun _ : Unit => A ⊗[W] L) (), fun f => ⟨f (), funext fun _ => Pi.single_eq_same _ _⟩⟩

theorem core [IsDomain W] [IsDiscreteValuationRing W] (l : ℕ) (hl : Irreducible (l : W)) (S : Sys.{1} W) (c : ℕ) (h1 : Module.Finite W S.lim)
    (h2 : ∀ n (x : S.M n), ((l : W) ^ n) • x = 0) (h3 : ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (h4 : ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x) [Module.Flat W A] [IsAdicComplete (Ideal.span {(l : A)}) A]
    (T : Sys.{1} A) (g : ∀ n, S.M n →+ T.M n) (hg : ∀ n (w : W) y, g n (w • y) = algebraMap W A w • g n y)
    (hr : ∀ n y, T.r n (g (n + 1) y) = g n (S.r n y))
    (hb : ∀ n, Tens W (N := fun _ : Unit => A) (M := fun _ => S.M n) (M' := T.M n) fun _ a y => a • g n y)
    (g' : ∀ n, S.lim →+ T.M n) (hg' : ∀ n (w : W) y, g' n (w • y) = algebraMap W A w • g' n y) (e : ∀ n y, g' n y = g n (y.1 n)) :
    (∀ w, (∀ n, ev (g' n) (hg' n) w = 0) → w = 0) ∧
      ∀ z : ∀ n, T.M n, (∀ n, T.r n (z (n + 1)) = z n) → ∃ w, ∀ n, ev (g' n) (hg' n) w = (l ^ c) • z n := by
  obtain ⟨hs, α, hα⟩ := GlobalTheory.T.flat_base_change_limit_system W l hl S c h1 h2 h3 h4 A
  have hev : ∀ n w, ev (g' n) (hg' n) w = ev (g n) (hg n) ((Tw.pr S n).baseChange A w) := fun n =>
    add_ext (f' := (ev (g n) (hg n)).comp ((Tw.pr S n).baseChange A).toAddMonoidHom) fun a y => by
      rw [ev_tmul, e]; rfl
  have hbij := fun n => ev_bij (g n) (hg n) (hb n)
  refine ⟨fun w hw => hs w fun n => (hbij n).1 (by rw [← hev, hw, map_zero]), fun z hz => ?_⟩
  choose u hu using fun n => (hbij n).2 (z n)
  have hc : ∀ n, (S.r n).baseChange A (u (n + 1)) = u n := fun n => (hbij n).1 (by
    rw [hu, ← hz, ← hu]
    exact add_ext (f := (ev (g n) (hg n)).comp ((S.r n).baseChange A).toAddMonoidHom)
      (f' := (T.r n).toAddMonoidHom.comp (ev (g (n + 1)) (hg (n + 1)))) (fun a y => by
        change a • g n (S.r n y) = T.r n (a • g (n + 1) y)
        rw [map_smul, hr]) _)
  refine ⟨α ⟨u, hc⟩, fun n => ?_⟩
  rw [hev, hα, ev_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact congrArg _ (hu n)

theorem exists_alpha {P H : Type 1} [AddCommGroup P] [AddCommGroup H] {T : ℕ → Type 1} [∀ n, AddCommGroup (T n)] (E : ∀ n, P →+ T n)
    (ν : ∀ n, H →+ T n) (k : ℕ) (hs : ∀ w, (∀ n, E n w = 0) → w = 0) (hx : ∀ x, ∃ w, ∀ n, E n w = k • ν n x) :
    ∃ α : H →+ P, ∀ n x, E n (α x) = k • ν n x := by
  choose a ha using hx
  exact ⟨AddMonoidHom.mk' a fun x y => sub_eq_zero.1 (hs _ fun n => by
    rw [map_sub, map_add, ha, ha, ha, map_add, nsmul_add, sub_self]), fun n x => ha x n⟩

theorem alpha_op {P H P' H' : Type 1} [AddCommGroup P] [AddCommGroup H] [AddCommGroup P'] [AddCommGroup H'] {T T' : ℕ → Type 1}
    [∀ n, AddCommGroup (T n)] [∀ n, AddCommGroup (T' n)] {E : ∀ n, P →+ T n} {ν : ∀ n, H →+ T n} {k : ℕ} {α : H →+ P}
    (hα : ∀ n x, E n (α x) = k • ν n x) {E' : ∀ n, P' →+ T' n} {ν' : ∀ n, H' →+ T' n} {k' : ℕ} {α' : H' →+ P'}
    (hα' : ∀ n x, E' n (α' x) = k' • ν' n x) (hs : ∀ w, (∀ n, E' n w = 0) → w = 0) (o : ∀ n, T n →+ T' n) (x : H) (x' : H') (w' : P')
    (h1 : ∀ n, E' n w' = o n (E n (α x))) (h2 : ∀ n, ν' n x' = o n (ν n x)) :
    k • α' x' = k' • w' ∧ (k = k' → α' x' = w') :=
  ⟨sub_eq_zero.1 (hs _ fun n => by
      rw [map_sub, map_nsmul, map_nsmul, hα', h1, hα, map_nsmul, h2, smul_comm, sub_self]),
    fun h => sub_eq_zero.1 (hs _ fun n => by rw [map_sub, hα', h1, hα, map_nsmul, h2, h, sub_self])⟩

section Pack
variable {S S' : Sys.{1} W} {T T' H H' : Sys.{1} A}

def E (g : Sys.Hom S T (algebraMap W A)) (n : ℕ) : A ⊗[W] S.lim →+ T.M n :=
  ev (A := A) (AddMonoidHom.mk' (fun y : S.lim => g.f n (y.1 n)) fun _ _ => map_add (g.f n) _ _)
    fun w y => LinearMap.map_smulₛₗ (g.f n) w _

theorem E_tmul (g : Sys.Hom S T (algebraMap W A)) (n : ℕ) (a : A) (y : S.lim) : E g n (a ⊗ₜ y) = a • g.f n (y.1 n) := rfl

theorem E_smul (g : Sys.Hom S T (algebraMap W A)) (n : ℕ) (a : A) (w : A ⊗[W] S.lim) : E g n (a • w) = a • E g n w := ev_smul _ _ a w

theorem E_r (g : Sys.Hom S T (algebraMap W A)) (n : ℕ) (w : A ⊗[W] S.lim) : T.r n (E g (n + 1) w) = E g n w :=
  add_ext (f := (T.r n).toAddMonoidHom.comp (E g (n + 1))) (fun a y => by
    change T.r n (a • g.f (n + 1) (y.1 (n + 1))) = a • g.f n (y.1 n)
    rw [map_smul, g.comm, y.2 n]) w

def nuL {ψ : A →+* A} (ν : Sys.Hom H T ψ) (n : ℕ) : H.lim →+ T.M n :=
  AddMonoidHom.mk' (fun x : H.lim => ν.f n (x.1 n)) fun _ _ => map_add (ν.f n) _ _

def beta (g : Sys.Hom S T (algebraMap W A)) (μ : Sys.Hom T H (RingHom.id A)) : A ⊗[W] S.lim →ₗ[A] H.lim where
  toFun w := ⟨fun n => μ.f n (E g n w), fun n => by rw [μ.comm, E_r]⟩
  map_add' w w' := Subtype.ext (funext fun n => by
    change μ.f n (E g n (w + w')) = μ.f n (E g n w) + μ.f n (E g n w')
    rw [map_add, map_add])
  map_smul' a w := Subtype.ext (funext fun n => by
    change μ.f n (E g n (a • w)) = a • μ.f n (E g n w)
    rw [E_smul, map_smul])

structure Pin (l : ℕ) (g : Sys.Hom S T (algebraMap W A)) {ψ : A →+* A} (ν : Sys.Hom H T ψ) (e : ℕ) (α : H.lim →+ A ⊗[W] S.lim) : Prop where
  sep : ∀ w, (∀ n, E g n w = 0) → w = 0
  pin : ∀ n x, E g n (α x) = (l ^ e) • nuL ν n x

theorem pin_ex [IsDomain W] [IsDiscreteValuationRing W] (l : ℕ) (hl : Irreducible (l : W)) (c : ℕ) (h1 : Module.Finite W S.lim)
    (h2 : ∀ n (x : S.M n), ((l : W) ^ n) • x = 0) (h3 : ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y)
    (h4 : ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x) [Module.Flat W A] [IsAdicComplete (Ideal.span {(l : A)}) A]
    (g : Sys.Hom S T (algebraMap W A))
    (hb : ∀ n, Tens W (N := fun _ : Unit => A) (M := fun _ => S.M n) (M' := T.M n) fun _ a y => a • g.f n y)
    {ψ : A →+* A} (ν : Sys.Hom H T ψ) : ∃ α, Pin l g ν c α := by
  obtain ⟨hs, hx⟩ := core l hl S c h1 h2 h3 h4 T (fun n => (g.f n).toAddMonoidHom) (fun n w y => LinearMap.map_smulₛₗ (g.f n) w y)
    (fun n y => g.comm n y) hb (fun n => AddMonoidHom.mk' (fun y : S.lim => g.f n (y.1 n)) fun _ _ => map_add (g.f n) _ _)
    (fun n w y => LinearMap.map_smulₛₗ (g.f n) w _) fun _ _ => rfl
  obtain ⟨α, hα⟩ := exists_alpha (E g) (nuL ν) (l ^ c) hs fun x => hx (fun n => nuL ν n x) fun n => (ν.lim x).2 n
  exact ⟨α, hs, hα⟩

variable {l e e' : ℕ} {g : Sys.Hom S T (algebraMap W A)} {g' : Sys.Hom S' T' (algebraMap W A)} {ψ : A →+* A} {ν : Sys.Hom H T ψ}
  {ν' : Sys.Hom H' T' ψ} {α : H.lim →+ A ⊗[W] S.lim} {α' : H'.lim →+ A ⊗[W] S'.lim}

theorem Pin.lin (h : Pin l g ν e α) (a : A) (x : H.lim) : α (a • x) = ψ a • α x :=
  sub_eq_zero.1 (h.sep _ fun n => by
    rw [map_sub, E_smul, h.pin, h.pin, smul_comm, sub_eq_zero]
    exact congrArg _ (LinearMap.map_smulₛₗ (ν.f n) a _))

theorem Pin.fac (h : Pin l g ν e α) (μ : Sys.Hom T H (RingHom.id A)) (x y : H.lim) (hy : ∀ n, μ.f n (ν.f n (x.1 n)) = y.1 n) :
    beta g μ (α x) = ((l : A) ^ e) • y := Subtype.ext (funext fun n => by
  change μ.f n (E g n (α x)) = ((l : A) ^ e) • y.1 n
  rw [h.pin, map_nsmul, ← hy, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; rfl)

theorem Pin.op (h : Pin l g ν e α) (h' : Pin l g' ν' e' α') {τ : A →+* A} (oT : ∀ n, T.M n →ₛₗ[τ] T'.M n) (oS : S.lim → S'.lim)
    (hS : ∀ n y, g'.f n ((oS y).1 n) = oT n (g.f n (y.1 n))) (o : A ⊗[W] S.lim →+ A ⊗[W] S'.lim) (ho : ∀ a y, o (a ⊗ₜ y) = τ a ⊗ₜ oS y)
    (x : H.lim) (x' : H'.lim) (hx : ∀ n, ν'.f n (x'.1 n) = oT n (ν.f n (x.1 n))) :
    ((l : A) ^ e) • α' x' = ((l : A) ^ e') • o (α x) ∧ (e = e' → α' x' = o (α x)) := by
  have := alpha_op h.pin h'.pin h'.sep (fun n => (oT n).toAddMonoidHom) x x' (o (α x)) (fun n =>
    add_ext (f := (E g' n).comp o) (f' := (oT n).toAddMonoidHom.comp (E g n)) (fun a y => by
      change E g' n (o (a ⊗ₜ y)) = oT n (a • g.f n (y.1 n))
      rw [ho, E_tmul, hS, LinearMap.map_smulₛₗ]) _) hx
  rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  exact ⟨this.1, fun he => this.2 (by rw [he])⟩

def tmap {L L' : Type 1} [AddCommGroup L] [Module W L] [AddCommGroup L'] [Module W L'] (τ : A →+* A) {τW : W →+* W} (o : L →ₛₗ[τW] L')
    (hτ : ∀ w, τ (algebraMap W A w) = algebraMap W A (τW w)) : A ⊗[W] L →+ A ⊗[W] L' :=
  TensorProduct.liftAddHom (AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun y => τ a ⊗ₜ[W] o y) fun y y' => by rw [map_add, tmul_add])
    fun a a' => AddMonoidHom.ext fun y => by
      change τ (a + a') ⊗ₜ[W] o y = τ a ⊗ₜ[W] o y + τ a' ⊗ₜ[W] o y
      rw [map_add, add_tmul]) fun w a y => by
      change τ (w • a) ⊗ₜ[W] o y = τ a ⊗ₜ[W] o (w • y)
      rw [LinearMap.map_smulₛₗ, Algebra.smul_def, map_mul, hτ, ← Algebra.smul_def, smul_tmul]

end Pack

end CrystallineSemistableComparison.Pb.Fa
