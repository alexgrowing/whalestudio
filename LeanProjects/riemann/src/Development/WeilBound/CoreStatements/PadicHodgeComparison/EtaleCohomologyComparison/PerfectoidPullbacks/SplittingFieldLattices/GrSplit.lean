import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

section Base
variable (O : Type) [CommRing O] {A : Type} [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)

structure GrSplit (m : ℕ) : Type 1 where
  N : Fin m → Type
  [ab : ∀ i, AddCommGroup (N i)]
  [md : ∀ i, Module O (N i)]
  [flat : ∀ i, Module.Flat O (N i)]
  ν : ∀ i, N i →ₗ[O] A
  mem : ∀ (i : Fin m) n, ν i n ∈ pdP γ i
  inj : ∀ (i : Fin m) n, ν i n ∈ pdP γ (i + 1) → n = 0
  surj : ∀ (i : Fin m), ∀ x ∈ pdP γ i, ∃ n, x - ν i n ∈ pdP γ (i + 1)
  nil : pdP γ m = ⊥

attribute [instance] GrSplit.ab GrSplit.md GrSplit.flat

structure LatBase (l m : ℕ) : Prop where
  tf : TFBase γ l m
  fg : ∀ r, (pdP γ r).FG
  prime : I.IsPrime
  val : ∀ x y : A, x ∈ Ideal.span {y} ⊔ I ∨ y ∈ Ideal.span {x} ⊔ I
  dv : ∀ x : A, x ∉ I → ∃ n : ℕ, (l : A) ^ n ∈ Ideal.span {x} ⊔ I
  cpl : IsAdicComplete (Ideal.span {(l : A)}) A
  closed : ∀ (r : ℕ) (x : A), (∀ n : ℕ, x ∈ Ideal.span {(l : A) ^ n} ⊔ pdP γ r) → x ∈ pdP γ r

variable {O} {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O))

abbrev κA (O : Type) [CommRing O] {A : Type} [CommRing A] [Algebra O A] (I : Ideal A) : O →+* A ⧸ I :=
  (Ideal.Quotient.mk I).comp (algebraMap O A)

abbrev TS (l s : ℕ) (𝒱 : Set X.Opens) : ObjectProperty (Thick (nlFun γ 0 X q (κA O I))) := St (TF l s) 𝒱

abbrev TO (l s : ℕ) (𝒱 : Set X.Opens) : ObjectProperty (Thick (smFun X q)) :=
  St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) 𝒱

def nmO : NMor (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) γ q (κA O I) (algebraMap O A) where
  hI := by classical exact GlobalTheory.LogCris.Ex.isDPMorphism_bot γ _
  u := 𝟙 X
  g := RingHom.id O
  hu := by simp
  hκ a r h := by
    have : a = r := by simpa [sub_eq_zero] using Ideal.Quotient.eq.1 h
    rw [← this]; rfl

theorem nmO_mem (l s : ℕ) (𝒱 : Set X.Opens) (T : Thick (nlFun γ 0 X q (κA O I))) (h : TS γ q l s 𝒱 T) :
    TO q l s 𝒱 (((nmO γ q).mor 0).obj T) := by
  obtain ⟨⟨h0, h1⟩, V, hV, hU⟩ := h
  exact ⟨⟨h0, h1⟩, V, hV, hU⟩

def smO (l s : ℕ) (𝒱 : Set X.Opens) : SMor (sP (TO q l s 𝒱)) (sP (TS γ q l s 𝒱)) (algebraMap O A) :=
  (nmO γ q).smor _ _ (nmO_mem γ q l s 𝒱)

def muB (l s : ℕ) (𝒱 : Set X.Opens) (j : ℕ) : HdR q j →ₛₗ[algebraMap O A] HO (TS γ q l s 𝒱) j :=
  ((smO γ q l s 𝒱).o.pull j).comp (resK q (TO q l s 𝒱) j)

end Base

section Red
variable {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L))

abbrev HM (r : Option ℤ) (c : b.R) (j : ℕ) : Type 1 := CH.H (sq (IdF.top (sP Q).A) (stdI Q r c)) j

def redM (r : Option ℤ) (c : b.R) (j : ℕ) : HO Q j →ₗ[b.R] HM Q r c j := (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).pull j

theorem stdI_le (r : Option ℤ) (c : b.R) (n : ℕ) (T : Q.FullSubcategory) : (stdI Q r (c ^ (n + 1))).S T ≤ (stdI Q r (c ^ n)).S T := by
  simp only [stdI]
  dsimp only [IdF.sup, IdF.span]
  refine sup_le_sup_left ?_ _
  rw [Ideal.span_singleton_le_span_singleton, map_pow, map_pow, pow_succ]
  exact dvd_mul_right _ _

def trM (r : Option ℤ) (c : b.R) (n j : ℕ) : HM Q r (c ^ (n + 1)) j →ₗ[b.R] HM Q r (c ^ n) j :=
  (sqLe (fun _ => le_rfl) (stdI_le Q r c n)).pull j

def quoM (r : ℤ) (j : ℕ) : HO Q j →ₗ[b.R] HQ Q 0 r j := (toSq (sFil Q 0) (sFil Q r) fun T => T.obj.pdPow_zero).pull j

end Red

end CrystallineSemistableComparison.Pb
