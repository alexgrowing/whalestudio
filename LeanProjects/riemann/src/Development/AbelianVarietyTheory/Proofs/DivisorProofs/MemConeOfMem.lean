import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.Mean4O
open scoped NNReal

namespace GlobalTheory.VertForm

section Algebra

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {D : ℕ}

variable (E D) in

abbrev Form : Type u := MultilinearMap ℝ (fun _ : Fin (D + 1) => E) ℝ

def IsSymm (num : Form E D) : Prop := ∀ (v : Fin (D + 1) → E) (π : Equiv.Perm (Fin (D + 1))), num (v ∘ π) = num v

def rad (num : Form E D) : Submodule ℝ E where
  carrier := {x | ∀ (v : Fin (D + 1) → E) (j : Fin (D + 1)), num (Function.update v j x) = 0}
  add_mem' hx hy v j := by rw [num.map_update_add, hx v j, hy v j, add_zero]
  zero_mem' v j := num.map_update_zero v j
  smul_mem' c x hx v j := by rw [num.map_update_smul, hx v j, smul_zero]

theorem map_congr_rad (num : Form E D) {v w : Fin (D + 1) → E} (h : ∀ j, v j - w j ∈ rad num) : num v = num w := by
  classical
  have key (S : Finset (Fin (D + 1))) : num (S.piecewise v w) = num w := by
    induction S using Finset.induction_on with
    | empty => rw [Finset.piecewise_empty]
    | insert j S hj ih =>
      have e : v j = (v j - w j) + w j := by abel
      rw [Finset.piecewise_insert, e, num.map_update_add, h j, zero_add, ← Finset.piecewise_eq_of_notMem S v w hj,
        Function.update_eq_self, ih]
  rw [← key Finset.univ, Finset.piecewise_univ]

def cone (num : Form E D) (G : Set E) : Set E := {x | ∃ z ∈ Submodule.span ℝ≥0 G, x - z ∈ rad num}

variable {num : Form E D} {G : Set E}

theorem mem_cone_of_mem {x : E} (h : x ∈ G) : x ∈ cone num G := ⟨x, Submodule.subset_span h, by simp⟩

theorem zero_mem_cone : (0 : E) ∈ cone num G := ⟨0, zero_mem _, by simp⟩

theorem add_mem_cone {x y : E} (hx : x ∈ cone num G) (hy : y ∈ cone num G) : x + y ∈ cone num G := by
  obtain ⟨z, hz, h⟩ := hx
  obtain ⟨w, hw, h'⟩ := hy
  exact ⟨z + w, add_mem hz hw, by rw [add_sub_add_comm]; exact add_mem h h'⟩

theorem smul_mem_cone {x : E} {c : ℝ} (hc : 0 ≤ c) (hx : x ∈ cone num G) : c • x ∈ cone num G := by
  obtain ⟨z, hz, h⟩ := hx
  exact ⟨c • z, Submodule.smul_mem _ (⟨c, hc⟩ : ℝ≥0) hz, by rw [← smul_sub]; exact Submodule.smul_mem _ c h⟩

theorem sum_mem_cone {ι : Type*} (s : Finset ι) {x : ι → E} (h : ∀ i ∈ s, x i ∈ cone num G) :
    ∑ i ∈ s, x i ∈ cone num G :=
  Finset.sum_induction x (· ∈ cone num G) (fun _ _ => add_mem_cone) zero_mem_cone h

theorem mem_cone_of_rad {x y : E} (hy : y ∈ cone num G) (h : x - y ∈ rad num) : x ∈ cone num G := by
  obtain ⟨z, hz, h'⟩ := hy
  exact ⟨z, hz, by rw [← sub_add_sub_cancel x y z]; exact add_mem h h'⟩

end Algebra

section Bundles

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} {p : X ⟶ Sp k} {q : X' ⟶ Sp k}

variable (p) in

abbrev Cl : Type 1 := HermLB p →₀ ℝ

def cl (L : HermLB p) : Cl p := Finsupp.single L 1

def pullCl (π : X' ⟶ X) (hπ : π ≫ p = q) : Cl p →ₗ[ℝ] Cl q := Finsupp.lmapDomain ℝ ℝ fun L => L.pull π hπ

theorem pullCl_cl (π : X' ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) : pullCl π hπ (cl L) = cl (L.pull π hπ) :=
  Finsupp.mapDomain_single

def IsArForm [IsIntegral X] (D : ℕ) (num : Form (Cl p) D) : Prop :=
  ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), IsArFun L D Φ →
    ∀ a : Fin (D + 1) → ι → ℝ, Φ (∏ j, lin (a j)) = num fun j => ∑ i, a j i • cl (L i)

variable (p) in

def oneB : HermLB p := fnB (fun _ _ => 2) (fun _ y => CxPts.cInfAt_const 2 y) fun _ _ _ _ _ _ _ => rfl

def NefOver (L : HermLB p) (l : ℕ) : Prop :=
  ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
    [Field κ] [Finite κ] [CharP κ l] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection κ (L.B.pull i) 1

theorem nefFib_iff (L : HermLB p) : NefFib L ↔ ∀ l : ℕ, l.Prime → NefOver L l :=
  ⟨fun h _ _ Z i _ _ κ _ _ _ _ hZ => h Z i κ hZ, fun h Z i _ _ κ _ _ _ hZ =>
    h (ringChar κ) (CharP.char_is_prime κ _) Z i κ hZ⟩

end Bundles

section Covers

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def Lies (V' V : Cover Y) (π : V'.X ⟶ V.X) : Prop := ∃ g : V'.G ⟶ V.G, g ≫ V.j = V'.j ≫ π ∧ g ≫ V.π = V'.π

theorem lies_id (V : Cover Y) : Lies V V (𝟙 _) := ⟨𝟙 _, by simp, by simp⟩

end Covers

end GlobalTheory.VertForm

end
