import Development.EtaleCohomology.WeilConjectures.FermatCount

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et Polynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.CurveCut

section Defs
variable (k : Type) [Field k]

abbrev Kb : Type := AlgebraicClosure (RatFunc k)

abbrev Gal : Type := Kb k ≃ₐ[RatFunc k] Kb k

abbrev OK : Type := integralClosure k[X] (Kb k)

def geo : Subgroup (Gal k) where
  carrier := {g | ∀ x : Kb k, IsAlgebraic k x → g x = x}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb x hx := by rw [AlgEquiv.mul_apply, hb x hx, ha x hx]
  inv_mem' {a} ha x hx := a.symm_apply_eq.2 (ha x hx).symm

instance geo_normal : (geo k).Normal := ⟨fun g hg σ x hx => by
  have h : IsAlgebraic k (σ.symm x) := hx.algHom (σ.symm.toAlgHom.restrictScalars k)
  change σ (g (σ.symm x)) = x
  rw [hg _ h, σ.apply_symm_apply]⟩

variable {k}

def Deg (r : ℕ) (g : Gal k) : Prop := ∀ x : Kb k, IsAlgebraic k x → g x = x ^ (Nat.card k ^ r)

def Inert (h : k[X]) (g : Gal k) : Prop := ∃ P : Ideal (OK k), P.IsPrime ∧ algebraMap k[X] (OK k) h ∉ P ∧
  ∀ s s' : OK k, (s' : Kb k) = g s → s' - s ∈ P

def ram (h : k[X]) : Subgroup (Gal k) := Subgroup.normalClosure {g | Inert h g}

instance ram_normal (h : k[X]) : (ram h).Normal := Subgroup.normalClosure_normal

def FrobAt {k' : Type} [Field k'] [Algebra k k'] (a : k') (g : Gal k) : Prop :=
  ∃ ψ : OK k →+* AlgebraicClosure k', (∀ p : k[X], ψ (algebraMap k[X] (OK k) p) = algebraMap k' _ (aeval a p)) ∧
    ∀ s s' : OK k, (s' : Kb k) = g s → ψ s' = ψ s ^ Nat.card k'

def pt {h : k[X]} {k' : Type} [Field k'] [Algebra k k'] (φ : Localization.Away h →ₐ[k] k') : k' :=
  φ (algebraMap k[X] (Localization.Away h) X)

def gen {h : k[X]} (h0 : h ≠ 0) : Localization.Away h →+* RatFunc k :=
  IsLocalization.Away.lift h (g := algebraMap k[X] (RatFunc k)) (IsUnit.mk0 _ (by simpa using h0))

variable (l : ℕ) [Fact l.Prime] {V : Type 1} [AddCommGroup V] [Module ℚ_[l] V]

def Eig (T : V →ₗ[ℚ_[l]] V) (α : AlgebraicClosure ℚ_[l]) : Prop :=
  Module.End.HasEigenvalue (T.baseChange (AlgebraicClosure ℚ_[l])) α

def EWt (T : V →ₗ[ℚ_[l]] V) (Q : ℕ) (S : Set ℝ) : Prop :=
  ∀ α, Eig l T α → ∀ ι : AlgebraicClosure ℚ_[l] →+* ℂ, Real.logb Q (‖ι α‖ ^ 2) ∈ S

variable {l}

def Cts (ρ : Representation ℚ_[l] (Gal k) V) : Prop := ∀ (v : V) (μ : Module.Dual ℚ_[l] V), Continuous fun g => μ (ρ g v)

def IsLisse (h : k[X]) (ρ : Representation ℚ_[l] (Gal k) V) : Prop :=
  Module.Finite ℚ_[l] V ∧ Cts ρ ∧ ∀ g, Inert h g → ρ g = 1

def Z1 (h : k[X]) (ρ : Representation ℚ_[l] (Gal k) V) : Submodule ℚ_[l] (geo k → V) where
  carrier := {c | (∀ μ : Module.Dual ℚ_[l] V, Continuous fun g => μ (c g)) ∧
    (∀ g g', c (g * g') = c g + ρ g (c g')) ∧ ∀ g, g.1 ∈ ram h → c g = 0}
  zero_mem' := ⟨fun μ => by simpa using continuous_const, by simp, by simp⟩
  add_mem' {a b} ha hb := ⟨fun μ => by simp only [Pi.add_apply, map_add]; exact (ha.1 μ).add (hb.1 μ),
    fun g g' => by simp only [Pi.add_apply, ha.2.1, hb.2.1, map_add]; abel,
    fun g hg => by simp [ha.2.2 g hg, hb.2.2 g hg]⟩
  smul_mem' r a ha := ⟨fun μ => by simpa using ha.1 (r • μ),
    fun g g' => by simp only [Pi.smul_apply, ha.2.1, map_smul, smul_add], fun g hg => by simp [ha.2.2 g hg]⟩

def cj (σ : Gal k) (g : geo k) : geo k := ⟨σ⁻¹ * g * σ, (geo_normal k).conj_mem' _ g.2 σ⟩

theorem cj_mul (σ : Gal k) (g g' : geo k) : cj σ (g * g') = cj σ g * cj σ g' := Subtype.ext (by simp [cj, mul_assoc])

theorem rho_cj (ρ : Representation ℚ_[l] (Gal k) V) (σ : Gal k) (g : geo k) (v : V) :
    ρ σ (ρ (cj σ g) v) = ρ g (ρ σ v) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]; simp [cj, mul_assoc]

def actZ (h : k[X]) (ρ : Representation ℚ_[l] (Gal k) V) (σ : Gal k) : Z1 h ρ →ₗ[ℚ_[l]] Z1 h ρ where
  toFun c := ⟨fun g => ρ σ (c.1 (cj σ g)),
    fun μ => (c.2.1 (μ.comp (ρ σ))).comp (Continuous.subtype_mk (by fun_prop) _),
    fun g g' => by beta_reduce; rw [cj_mul, c.2.2.1, map_add, rho_cj],
    fun g hg => by beta_reduce; rw [c.2.2.2 (cj σ g) ((ram_normal h).conj_mem' _ hg σ), map_zero]⟩
  map_add' a b := Subtype.ext (funext fun g => map_add (ρ σ) _ _)
  map_smul' r a := Subtype.ext (funext fun g => map_smul (ρ σ) _ _)

def B1 (h : k[X]) (ρ : Representation ℚ_[l] (Gal k) V) : Submodule ℚ_[l] (Z1 h ρ) where
  carrier := {c | ∃ v, ∀ g, c.1 g = ρ g v - v}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨v, hv⟩ ⟨w, hw⟩
    exact ⟨v + w, fun g => by change a.1 g + b.1 g = _; rw [hv, hw, map_add]; abel⟩
  smul_mem' := by
    rintro r a ⟨v, hv⟩
    exact ⟨r • v, fun g => by change r • a.1 g = _; rw [hv, map_smul, smul_sub]⟩

def actH (h : k[X]) (ρ : Representation ℚ_[l] (Gal k) V) (σ : Gal k) : (Z1 h ρ ⧸ B1 h ρ) →ₗ[ℚ_[l]] (Z1 h ρ ⧸ B1 h ρ) :=
  Submodule.mapQ _ _ (actZ h ρ σ) (by
    rintro c ⟨v, hv⟩
    exact ⟨ρ σ v, fun g => by change ρ σ (c.1 (cj σ g)) = _; rw [hv, map_sub, rho_cj]⟩)

abbrev actI (ρ : Representation ℚ_[l] (Gal k) V) (σ : Gal k) := ρ.toInvariants (geo k) σ

variable (l) in

def genRep {h : k[X]} (h0 : h ≠ 0) {X : Scheme.{0}} (f : X ⟶ Sp (Localization.Away h)) (n : ℤ) :
    Representation ℚ_[l] (Gal k) (HX l (Kb k) (fibre f (gen h0)) n) := galHQ l (Kb k) (fibre f (gen h0)) n 0

end Defs

def FrobEx : Prop := ∀ (k : Type) [Field k] [Finite k],
  (∀ (k' : Type) [Field k'] [Finite k'] [Algebra k k'] (a : k'), ∃ g : Gal k, FrobAt a g) ∧ ∃ g : Gal k, Deg 1 g

def Special : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (h : k[X]) (h0 : h ≠ 0) {X : Scheme.{0}} (f : X ⟶ Sp (Localization.Away h)), IsProper f → Smooth f → ∀ n : ℤ,
  Module.Finite ℚ_[l] (HX l (Kb k) (fibre f (gen h0)) n) ∧ (∀ g, Inert h g → genRep l h0 f n g = 1) ∧
  ∀ (k' : Type) [Field k'] [Finite k'] [Algebra k k'] (φ : Localization.Away h →ₐ[k] k')
    (Ω : Type) [Field Ω] [Algebra k' Ω] [IsAlgClosure k' Ω] (σ : Ω ≃ₐ[k'] Ω), IsFrob σ → ∀ g : Gal k, FrobAt (pt φ) g →
    ∃ e : HX l Ω (fibre f φ.toRingHom) n ≃ₗ[ℚ_[l]] HX l (Kb k) (fibre f (gen h0)) n,
      ∀ x, e (geoF l (fibre f φ.toRingHom) n σ x) = genRep l h0 f n g⁻¹ (e x)

def Contin : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K], (l : K) ≠ 0 →
  ∀ {X : Scheme.{0}} (p : X ⟶ Sp K), IsProper p → ∀ (n : ℤ) (v : HX l (AlgebraicClosure K) p n)
    (μ : Module.Dual ℚ_[l] (HX l (AlgebraicClosure K) p n)), Continuous fun g => μ (galHQ l (AlgebraicClosure K) p n 0 g v)

def TraceC : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (h : k[X]), h ≠ 0 → ∀ {V : Type 1} [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] (Gal k) V), IsLisse h ρ →
  Module.Finite ℚ_[l] (Z1 h ρ) ∧
  ∀ (k' : Type) [Field k'] [Finite k'] [Algebra k k'] (A : Finset k') (Fr : k' → Gal k) (σ : Gal k),
    (∀ a, a ∈ A ↔ aeval a h ≠ 0) → (∀ a ∈ A, FrobAt a (Fr a)) → Deg (Module.finrank k k') σ →
    ∑ a ∈ A, LinearMap.trace ℚ_[l] V (ρ (Fr a)) =
      (Nat.card k' : ℚ_[l]) * (LinearMap.trace ℚ_[l] V (ρ σ) - LinearMap.trace ℚ_[l] _ (actZ h ρ σ))

def Rankin : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (h : k[X]), h ≠ 0 → ∀ {V : Type 1} [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] (Gal k) V), IsLisse h ρ →
  ∀ w : ℝ, (∀ (k' : Type) [Field k'] [Finite k'] [Algebra k k'] (φ : Localization.Away h →ₐ[k] k') (g : Gal k),
    FrobAt (pt φ) g → ∀ r : ℕ, 0 < r → ∃ a : ℚ, LinearMap.trace ℚ_[l] V (ρ g⁻¹ ^ r) = (a : ℚ_[l])) →
  (∃ (k' : Type) (_ : Field k') (_ : Finite k') (_ : Algebra k k') (φ : Localization.Away h →ₐ[k] k') (g : Gal k),
    FrobAt (pt φ) g ∧ EWt l (ρ g⁻¹) (Nat.card k') (Set.Iic w)) →
  ∀ (k' : Type) [Field k'] [Finite k'] [Algebra k k'] (φ : Localization.Away h →ₐ[k] k') (g : Gal k),
    FrobAt (pt φ) g → EWt l (ρ g⁻¹) (Nat.card k') (Set.Iic w)

def LowBd : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (h : k[X]), h ≠ 0 → ∀ {V : Type 1} [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] (Gal k) V), IsLisse h ρ →
  ∀ w : ℝ, (∀ (k' : Type) [Field k'] [Finite k'] [Algebra k k'] (φ : Localization.Away h →ₐ[k] k') (g : Gal k),
    FrobAt (pt φ) g → EWt l (ρ g⁻¹) (Nat.card k') (Set.Ici w)) →
  ∀ σ : Gal k, Deg 1 σ → EWt l (actI ρ σ⁻¹) (Nat.card k) (Set.Ici w) ∧ EWt l (actH h ρ σ⁻¹) (Nat.card k) (Set.Ici w)

def Leray : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k], (l : k) ≠ 0 →
  ∀ (h : k[X]) (h0 : h ≠ 0) {X : Scheme.{0}} (f : X ⟶ Sp (Localization.Away h)), IsProper f → Smooth f →
  FinT l (f ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away h)))) ∧
  ∀ (n : ℤ) (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (σ : Ω ≃ₐ[k] Ω), IsFrob σ → ∀ g : Gal k, Deg 1 g →
    ∀ α, IsEig l (f ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away h)))) n σ α →
      Eig l (actI (genRep l h0 f n) g⁻¹) α ∨ Eig l (actH h (genRep l h0 f (n - 1)) g⁻¹) α

def EmptyH : Prop := Base → ∀ (q : ℕ) (X : Scheme.{0}), IsEmpty X → ∀ n i : ℤ, Subsingleton (Ht q (sch.obj X) n i)

end LateralTheory.EWeil.CurveCut

end
