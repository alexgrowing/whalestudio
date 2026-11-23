import Mathlib

set_option autoImplicit false

noncomputable section

namespace CrystallineSemistableComparison.Pb.Lat

section Inj
variable {A B : Type} [CommRing A] [CommRing B] (ι : A →+* B) {J : Ideal B} (δ : DividedPowers J)

def DPClosed : Prop := ∀ x : A, ι x ∈ J → ∀ n : ℕ, ∃ y : A, ι y = δ.dpow n (ι x)

variable {ι δ}

def dpowC (h : DPClosed ι δ) (n : ℕ) (x : A) : A := by
  classical exact if hx : ι x ∈ J then Classical.choose (h x hx n) else 0

theorem dpowC_spec (h : DPClosed ι δ) {n : ℕ} {x : A} (hx : ι x ∈ J) : ι (dpowC h n x) = δ.dpow n (ι x) := by
  rw [dpowC, dif_pos hx]; exact Classical.choose_spec (h x hx n)

def dpComap (hι : Function.Injective ι) (h : DPClosed ι δ) : DividedPowers (J.comap ι) where
  dpow := dpowC h
  dpow_null {n x} hx := by rw [dpowC, dif_neg (show ¬ ι x ∈ J from hx)]
  dpow_zero {x} hx := hι (by rw [dpowC_spec h hx, δ.dpow_zero hx, map_one])
  dpow_one {x} hx := hι (by rw [dpowC_spec h hx, δ.dpow_one hx])
  dpow_mem {n x} hn hx := by
    show ι _ ∈ J
    rw [dpowC_spec h hx]; exact δ.dpow_mem hn hx
  dpow_add {n x y} hx hy := hι (by
    have hxy : ι (x + y) ∈ J := by rw [map_add]; exact J.add_mem hx hy
    rw [dpowC_spec h hxy, map_add, δ.dpow_add hx hy, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, dpowC_spec h hx, dpowC_spec h hy])
  dpow_mul {n a x} hx := hι (by
    have hax : ι (a * x) ∈ J := by rw [map_mul]; exact J.mul_mem_left _ hx
    rw [dpowC_spec h hax, map_mul, δ.dpow_mul hx, map_mul, map_pow, dpowC_spec h hx])
  mul_dpow {m n x} hx := hι (by
    rw [map_mul, map_mul, dpowC_spec h hx, dpowC_spec h hx, dpowC_spec h hx, δ.mul_dpow hx, map_natCast])
  dpow_comp {m n x} hn hx := hι (by
    have h1 : ι (dpowC h n x) ∈ J := by rw [dpowC_spec h hx]; exact δ.dpow_mem hn hx
    rw [dpowC_spec h h1, dpowC_spec h hx, δ.dpow_comp hn hx, map_mul, map_natCast, dpowC_spec h hx])

theorem dpComap_dpow (hι : Function.Injective ι) (h : DPClosed ι δ) {n : ℕ} {x : A} (hx : ι x ∈ J) :
    ι ((dpComap hι h).dpow n x) = δ.dpow n (ι x) := dpowC_spec h hx

end Inj

section Lat
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

def η : B := ((l : ℚ) ^ M)⁻¹ • f ξ

def dpE (i : ℕ) : B := ((i.factorial : ℚ))⁻¹ • η f ξ l M ^ i

def sub : Subring B := Subring.closure (Set.range f ∪ Set.range (dpE f ξ l M))

def A : Type := ↥(sub f ξ l M)

instance : CommRing (A f ξ l M) := inferInstanceAs (CommRing ↥(sub f ξ l M))

def ι : A f ξ l M →+* B := (sub f ξ l M).subtype

theorem ι_injective : Function.Injective (ι f ξ l M) := Subtype.val_injective

def ofW : W →+* A f ξ l M := f.codRestrict (sub f ξ l M) fun w => Subring.subset_closure (Or.inl ⟨w, rfl⟩)

instance : Algebra W (A f ξ l M) := (ofW f ξ l M).toAlgebra

theorem ι_ofW (w : W) : ι f ξ l M (ofW f ξ l M w) = f w := rfl

def dpA (i : ℕ) : A f ξ l M := ⟨dpE f ξ l M i, Subring.subset_closure (Or.inr ⟨i, rfl⟩)⟩

theorem ι_dpA (i : ℕ) : ι f ξ l M (dpA f ξ l M i) = dpE f ξ l M i := rfl

def IB : Ideal B := Ideal.span {f ξ}

def γB : DividedPowers (IB f ξ) := by classical exact DividedPowers.RatAlgebra.dividedPowers (IB f ξ)

def I : Ideal (A f ξ l M) := (IB f ξ).comap (ι f ξ l M)

def γ (h : DPClosed (ι f ξ l M) (γB f ξ)) : DividedPowers (I f ξ l M) := dpComap (ι_injective f ξ l M) h

theorem ι_γ (h : DPClosed (ι f ξ l M) (γB f ξ)) {n : ℕ} {x : A f ξ l M} (hx : x ∈ I f ξ l M) :
    ι f ξ l M ((γ f ξ l M h).dpow n x) = (γB f ξ).dpow n (ι f ξ l M x) := dpComap_dpow _ h hx

def mapM {M M' : ℕ} (h : sub f ξ l M ≤ sub f ξ l M') : A f ξ l M →+* A f ξ l M' := Subring.inclusion h

structure Hyp (m : ℕ) : Prop where
  one_le : 1 ≤ m
  nil : f ξ ^ m = 0
  gr : ∀ i < m, ∀ (a : W) (b : B), f a * f ξ ^ i = f ξ ^ (i + 1) * b → ξ ∣ a
  dom : IsDomain (W ⧸ Ideal.span {ξ})
  val : ∀ x y : W ⧸ Ideal.span {ξ}, x ∣ y ∨ y ∣ x
  dv : ∀ x : W ⧸ Ideal.span {ξ}, x ≠ 0 → ∃ n : ℕ, x ∣ (l : W ⧸ Ideal.span {ξ}) ^ n
  l0 : (l : W ⧸ Ideal.span {ξ}) ≠ 0
  cpl : IsAdicComplete (Ideal.span {(l : W ⧸ Ideal.span {ξ})}) (W ⧸ Ideal.span {ξ})
  unit : ∀ n : ℕ, n ≠ 0 → ∃ (k : ℕ) (u : W), (n : W) * u = (l : W) ^ k

end Lat

section Map
variable {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B'] [Algebra ℚ B']
  (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)

def map (g : B →+* B') (h : ∀ x ∈ sub f ξ l M, g x ∈ sub f' ξ' l M) : A f ξ l M →+* A f' ξ' l M :=
  g.restrict (sub f ξ l M) (sub f' ξ' l M) h

theorem ι_map (g : B →+* B') (h : ∀ x ∈ sub f ξ l M, g x ∈ sub f' ξ' l M) (x : A f ξ l M) :
    ι f' ξ' l M (map f ξ f' ξ' l M g h x) = g (ι f ξ l M x) := rfl

end Map

end CrystallineSemistableComparison.Pb.Lat
