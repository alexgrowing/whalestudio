import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsProps

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

structure PerC (R : Per l K) : Type 1 where
  C : Type
  K₀ : Type
  [ringC : CommRing C]
  [fieldK : Field K₀]
  c : R.A →+* C
  ι : C →+* R.B
  φ : C →+* C
  σ : K.fixingSubgroup → C →+* C
  q : ℚ_[l] →+* C
  k : K₀ →+* C

attribute [instance] PerC.ringC PerC.fieldK

variable {R : Per l K}

structure PerC.Facts (C : PerC R) : Prop where
  ι_c : ∀ a, C.ι (C.c a) = R.i a
  ι_q : ∀ z, C.ι (C.q z) = R.q z
  ι_inj : Function.Injective C.ι
  t_unit : IsUnit (C.c R.t)
  φ_c : ∀ a, C.φ (C.c a) = C.c (R.φ a)
  φ_q : ∀ z, C.φ (C.q z) = C.q z
  frobenius_fixes_z : ∀ z, R.φ (R.z z) = R.z z
  σ_c : ∀ g a, C.σ g (C.c a) = C.c (R.σA g a)
  σ_q : ∀ g z, C.σ g (C.q z) = C.q z
  φ_σ : ∀ g a, R.φ (R.σA g a) = R.σA g (R.φ a)

structure Iso (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (K₀ : Type) [Field K₀] : Type 2 where
  D : Model l K → ℕ → Type 1
  [ab : ∀ M j, AddCommGroup (D M j)]
  [md : ∀ M j, Module K₀ (D M j)]
  φ : ∀ M j, D M j →+ D M j
  pull : ∀ {M N : Model l K} (u : M.X ⟶ N.X), u ≫ N.p = M.p → ∀ j, D N j →ₗ[K₀] D M j

attribute [instance] Iso.ab Iso.md

variable (G : Model l K → Prop) (C : PerC R) (I : Iso l K C.K₀)

structure CrysCmp where
  c : ∀ (M : Model l K) (n : ℕ), M.V n →+ (Module.Dual C.K₀ (I.D M n) →+ C.C)
  lin : ∀ (M : Model l K) (n : ℕ) (z : ℚ_[l]) (v : M.V n) (f : Module.Dual C.K₀ (I.D M n)), c M n (z • v) f = C.q z * c M n v f
  lin' : ∀ (M : Model l K) (n : ℕ) (k : C.K₀) (v : M.V n) (f : Module.Dual C.K₀ (I.D M n)), c M n v (k • f) = C.k k * c M n v f
  fin : ∀ (M : Model l K) (n : ℕ), G M → FiniteDimensional ℚ_[l] (M.V n) ∧ FiniteDimensional C.K₀ (I.D M n)
  equi : ∀ (M : Model l K) (n : ℕ), G M → ∀ (σ : K.fixingSubgroup) (v : M.V n) (f : Module.Dual C.K₀ (I.D M n)),
    c M n (M.act n σ v) f = C.σ σ (c M n v f)
  inj : ∀ (M : Model l K) (n : ℕ), G M → ∀ {a : ℕ} (b : Module.Basis (Fin a) ℚ_[l] (M.V n)) (z : Fin a → C.C),
    (∀ f, ∑ i, z i * c M n (b i) f = 0) → z = 0
  phi : ∀ (M : Model l K) (n : ℕ), G M → ∀ {m : ℕ} (b : Module.Basis (Fin m) C.K₀ (I.D M n)) (v : M.V n)
    (f : Module.Dual C.K₀ (I.D M n)), c M n v f = ∑ s, C.φ (c M n v (b.coord s)) * C.k (f (I.φ M n (b s)))
  nat : ∀ (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ), G M → G N →
    ∀ (v : N.V n) (f : Module.Dual C.K₀ (I.D M n)), c M n (Model.pullV u hu n v) f = c N n v (f ∘ₗ I.pull u hu n)

variable {G} in

structure BPhi {D : Dat R} (β : BMap G D) where
  pull : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N}, D.Mo u hu a b →
    ∀ j, (D.H' b).N j →+ (D.H' a).N j
  nat : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N} (m : D.Mo u hu a b),
    G M → G N → ∀ (j : ℕ) (x : (D.H' b).N j), β.β' a j (pull m j x) = D.pullA m j (β.β' b j x)
  inj : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j : ℕ, ∃ n : ℕ, ∀ x, β.β' a j x = 0 → R.t ^ n • x = 0

structure FMap (D : Dat R)
    (pull : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N}, D.Mo u hu a b →
      ∀ j, (D.H' b).N j →+ (D.H' a).N j) where
  k : ℕ
  ψ : ∀ {M : Model l K} (a : D.Ch M) (j : ℕ), (D.H' a).N j →+ (Module.Dual C.K₀ (I.D M j) →+ C.C)
  fin : ∀ (M : Model l K), G M → ∀ j : ℕ, FiniteDimensional C.K₀ (I.D M j)
  pull_id : ∀ (M : Model l K), G M → ∀ (j : ℕ) (x : I.D M j), I.pull (𝟙 M.X) (Category.id_comp _) j x = x
  lin : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (c : R.A) (x : (D.H' a).N j) (f : Module.Dual C.K₀ (I.D M j)),
    ψ a j (c • x) f = C.c (R.φ^[k] c) * ψ a j x f
  lin' : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (c : C.K₀) (x : (D.H' a).N j) (f : Module.Dual C.K₀ (I.D M j)),
    ψ a j x (c • f) = C.k c * ψ a j x f
  act : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (σ : K.fixingSubgroup) (x : (D.H' a).N j)
    (f : Module.Dual C.K₀ (I.D M j)), ψ a j ((D.H' a).act j σ x) f = C.σ σ (ψ a j x f)
  phi : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) {m : ℕ} (b : Module.Basis (Fin m) C.K₀ (I.D M j)) (x : (D.H' a).N j)
    (f : Module.Dual C.K₀ (I.D M j)), ψ a j (D.phi' a j x) f = ∑ s, C.φ (ψ a j x (b.coord s)) * C.k (f (I.φ M j (b s)))
  nat : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N} (m : D.Mo u hu a b),
    G M → G N → ∀ (j : ℕ) (x : (D.H' b).N j) (f : Module.Dual C.K₀ (I.D M j)), ψ a j (pull m j x) f = ψ b j x (f ∘ₗ I.pull u hu j)
  fac : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) {m : ℕ} (b : Module.Basis (Fin m) C.K₀ (I.D M j)),
    ∃ w : Fin m → ((D.H' a).N j →+ R.B) → R.B,
      (∀ f, GMod.Fn R (D.H' a) j f → ∀ (s : Fin m) (σ : K.fixingSubgroup), R.σ σ (w s f) = w s f) ∧
      ∀ x f, GMod.Fn R (D.H' a) j f → f ((D.phi' a j)^[k] x) = ∑ s, C.ι (ψ a j x (b.coord s)) * w s f

def FactorisationSpanProperty : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (R : Per l K) (G : Model l K → Prop)
  (C : PerC R) (I : Iso l K C.K₀) (D : Dat R) (β : BMap G D) (β₁ : BPhi β), FMap G C I D β₁.pull → D.Span G C.ι.range

def FrobeniusComparison : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (R : Per l K) (G : Model l K → Prop)
  (C : PerC R) (I : Iso l K C.K₀) (D : Dat R), R.Facts → C.Facts → EtSide G → D.Laws G → EMap G D →
    ∀ (β : BMap G D) (β₁ : BPhi β), PMap G D → FMap G C I D β₁.pull → Nonempty (CrysCmp G C I)

theorem fac : FactorisationSpanProperty := by
  intro l _ K R G C I D β β₁ F M hM a j
  have := F.fin M hM j
  obtain ⟨w, hw, h⟩ := F.fac a hM j (Module.finBasis _ _)
  exact ⟨F.k, _, w, hw, fun x => ⟨_, fun s => ⟨_, rfl⟩, h x⟩⟩

end CrystallineSemistableComparison
