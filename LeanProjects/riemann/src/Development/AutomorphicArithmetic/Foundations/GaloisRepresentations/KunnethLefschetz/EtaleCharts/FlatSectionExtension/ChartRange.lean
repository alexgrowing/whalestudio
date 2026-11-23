import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PBData

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

variable {K : Type} [CommRing K] {W Z Y T : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
  {D : E.LineData Y} {d : ℕ}

def tN (B : Blow q i π D d) (α : B.ι) {N : Z.Opens} (h : N ≤ B.V α) (m : Fin d) : Γ(Z, N) :=
  (Z.presheaf.map (homOfLE h).op).hom ((B.c α).t m)

def IsTr (B : Blow q i π D d) (α β : B.ι) {N : Z.Opens} (h₁ : N ≤ B.V α) (h₂ : N ≤ B.V β)
    (G : Matrix (Fin d) (Fin d) Γ(Z, N)) : Prop :=
  ∀ m, tN B β h₂ m = ∑ l, G m l * tN B α h₁ l

def LocMat (B : Blow q i π D d) (α β : B.ι) {V : Scheme.{0}} (p : V ⟶ W) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)) : Prop :=
  ∀ x : V, ∃ (U : V.Opens) (N : Z.Opens) (_ : x ∈ U) (_ : IsAffineOpen N) (h₁ : N ≤ B.V α) (h₂ : N ≤ B.V β)
    (hU : ⊤ ≤ (U.ι ≫ p ≫ i) ⁻¹ᵁ N) (G : Matrix (Fin d) (Fin d) Γ(Z, N)), IsTr B α β h₁ h₂ G ∧
      M.map U.ι.appTop.hom = G.map ((U.ι ≫ p ≫ i).appLE N ⊤ hU).hom

def uV (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} (y : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (m : Fin d) : Γ(V, ⊤) :=
  (y.appLE ((B.c α).C k) ⊤ h).hom ((B.c α).u k m)

theorem chart_range (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} (y : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) :
    Set.range y ⊆ Set.range ((B.c α).C k).ι := by
  rintro _ ⟨x, rfl⟩
  simpa using h (Set.mem_univ x)

def secOf (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} (y : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) : V ⟶ D.Y :=
  IsOpenImmersion.lift ((B.c α).C k).ι y (chart_range B α k y h) ≫ B.σ α k

theorem secOf_f (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} (y : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) :
    secOf B α k y h ≫ D.f = y := by
  unfold secOf
  rw [Category.assoc, B.σ_f, IsOpenImmersion.lift_fac]

abbrev oW (B : Blow q i π D d) (α : B.ι) : W.Opens := i ⁻¹ᵁ B.V α

abbrev WP (B : Blow q i π D d) : Scheme.{0} := ∐ fun α : B.ι => (oW B α : Scheme.{0})

def cP (B : Blow q i π D d) : WP B ⟶ W := Sigma.desc fun α => (oW B α).ι

def wI (B : Blow q i π D d) (α : B.ι) : (oW B α : Scheme.{0}) ⟶ WP B :=
  Sigma.ι (fun α : B.ι => (oW B α : Scheme.{0})) α

abbrev oT (B : Blow q i π D d) (j : T ⟶ Y) (p : B.ι × Fin d) : T.Opens := j ⁻¹ᵁ (B.c p.1).C p.2

abbrev TP (B : Blow q i π D d) (j : T ⟶ Y) : Scheme.{0} := ∐ fun p : B.ι × Fin d => (oT B j p : Scheme.{0})

def eP (B : Blow q i π D d) (j : T ⟶ Y) : TP B j ⟶ T := Sigma.desc fun p => (oT B j p).ι

def tI (B : Blow q i π D d) (j : T ⟶ Y) (p : B.ι × Fin d) : (oT B j p : Scheme.{0}) ⟶ TP B j :=
  Sigma.ι (fun p : B.ι × Fin d => (oT B j p : Scheme.{0})) p

theorem oT_le (B : Blow q i π D d) (j : T ⟶ Y) (p : B.ι × Fin d) : ⊤ ≤ ((oT B j p).ι ≫ j) ⁻¹ᵁ (B.c p.1).C p.2 := by
  intro x _
  simpa using x.2

theorem rho_range (B : Blow q i π D d) (j : T ⟶ Y) (r : T ⟶ W) (hw : j ≫ π = r ≫ i) (p : B.ι × Fin d) :
    Set.range ((oT B j p).ι ≫ r) ⊆ Set.range (oW B p.1).ι := by
  rintro _ ⟨x, rfl⟩
  have h1 : (j x.1 : Y) ∈ (B.c p.1).C p.2 := x.2
  have h2 : π (j x.1) ∈ B.V p.1 := (B.c p.1).C_le p.2 h1
  have h3 : i (r x.1) = π (j x.1) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hw]
  have h4 : r x.1 ∈ oW B p.1 := by
    change i (r x.1) ∈ B.V p.1
    rw [h3]; exact h2
  rw [Scheme.Hom.comp_apply, Scheme.Opens.range_ι]
  exact h4

def rhoC (B : Blow q i π D d) (j : T ⟶ Y) (r : T ⟶ W) (hw : j ≫ π = r ≫ i) (p : B.ι × Fin d) :
    (oT B j p : Scheme.{0}) ⟶ (oW B p.1 : Scheme.{0}) :=
  IsOpenImmersion.lift (oW B p.1).ι ((oT B j p).ι ≫ r) (rho_range B j r hw p)

def rhoP (B : Blow q i π D d) (j : T ⟶ Y) (r : T ⟶ W) (hw : j ≫ π = r ≫ i) : TP B j ⟶ WP B :=
  Sigma.desc fun p : B.ι × Fin d => rhoC B j r hw p ≫ wI B p.1

def tauP (B : Blow q i π D d) (j : T ⟶ Y) : TP B j ⟶ D.Y :=
  Sigma.desc fun p => secOf B p.1 p.2 ((oT B j p).ι ≫ j) (oT_le B j p)

def IsV (B : Blow q i π D d) (j : T ⟶ Y) (v : Fin d → Γ(TP B j, ⊤)) : Prop :=
  ∀ p m, (tI B j p).appTop.hom (v m) = uV B p.1 p.2 ((oT B j p).ι ≫ j) (oT_le B j p) m

def GMat (B : Blow q i π D d) {V : Scheme.{0}} (a b : V ⟶ WP B) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)) : Prop :=
  ∀ x : V, ∃ (U : V.Opens) (α β : B.ι) (a₁ : (U : Scheme.{0}) ⟶ oW B α) (b₁ : (U : Scheme.{0}) ⟶ oW B β), x ∈ U ∧
    U.ι ≫ a = a₁ ≫ wI B α ∧ U.ι ≫ b = b₁ ≫ wI B β ∧ LocMat B α β (U.ι ≫ a ≫ cP B) (M.map U.ι.appTop.hom)

end UpperTheory.Gal.KunnethLefschetz.G.PX
