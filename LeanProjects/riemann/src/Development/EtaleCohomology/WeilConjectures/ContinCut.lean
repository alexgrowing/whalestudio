import Development.EtaleCohomology.WeilConjectures.CurveCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.ContinCut

universe u v

def Chev : Prop := ∀ (l : ℕ) [Fact l.Prime] (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M]
  (K : ℕ → Submodule ℤ_[l] M), Antitone K → (∀ x, (∀ k, x ∈ K k) → x = 0) →
  ∀ N : ℕ, ∃ k, ∀ y ∈ K k, ∃ z : M, y = (l : ℤ_[l]) ^ N • z

def AbsCont : Prop := ∀ (l : ℕ) [Fact l.Prime] (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type u) [AddCommGroup M] [Module ℤ_[l] M] [Module.Finite ℤ_[l] M] (ρ : Representation ℤ_[l] G M)
  (K : ℕ → Submodule ℤ_[l] M), Antitone K → (∀ x, (∀ k, x ∈ K k) → x = 0) →
  (∀ (x : M) (k : ℕ), IsOpen {g : G | ρ g x - x ∈ K k}) →
  ∀ (φ : M →ₗ[ℤ_[l]] ℚ_[l]) (x : M), Continuous fun g => φ (ρ g x)

def Stab : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K], (l : K) ≠ 0 →
  ∀ {X : Scheme.{0}} (p : X ⟶ Sp K), IsProper p → ∀ (n : ℤ) (x : Hl l (sch.obj (geom (AlgebraicClosure K) p)) n 0)
    (k : ℕ), IsOpen {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
      (galHl l (AlgebraicClosure K) p n 0 σ x).1 k = x.1 k}

def FinGen : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K], (l : K) ≠ 0 →
  ∀ {X : Scheme.{0}} (p : X ⟶ Sp K), IsProper p → ∀ n : ℤ,
    Module.Finite ℤ_[l] (Hl l (sch.obj (geom (AlgebraicClosure K) p)) n 0)

def evk (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) (k : ℕ) : Hl l E n i →ₗ[ℤ_[l]] HtL l k E n i :=
  (LinearMap.proj (R := ℤ_[l]) (φ := fun k => HtL l k E n i) k).comp (HlSub l E n i).subtype

theorem evk_apply (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) (k : ℕ) (x : Hl l E n i) : evk l E n i k x = x.1 k := rfl

theorem evk_anti (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) : Antitone fun k => LinearMap.ker (evk l E n i k) := by
  intro a b hab x hx
  simp only [LinearMap.mem_ker, evk_apply] at hx ⊢
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact hx
  | succ d ih =>
    apply ih (Nat.le_add_right _ _)
    have h2 : red (l ^ (a + d + 1)) (l ^ (a + d)) E n i (x.1 (a + d + 1)) = x.1 (a + d) := x.2 (a + d)
    have h3 : (x.1 (a + d + 1) : Ht (l ^ (a + d + 1)) E n i) = 0 := hx
    rw [← h2, h3]; exact map_zero (red (l ^ (a + d + 1)) (l ^ (a + d)) E n i)

end LateralTheory.EWeil.ContinCut
