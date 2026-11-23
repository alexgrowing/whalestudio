import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory

universe v u v' u'

namespace CrystallineSemistableComparison.Pb

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

structure IdF (A : C ⥤ CommAlgCat.{0} R) where
  S : ∀ T : C, Ideal (A.obj T)
  map_mem : ∀ {T T' : C} (φ : T ⟶ T') {x : A.obj T}, x ∈ S T → (A.map φ).hom x ∈ S T'

variable {A : C ⥤ CommAlgCat.{0} R}

def IdF.top (A : C ⥤ CommAlgCat.{0} R) : IdF A := ⟨fun _ => ⊤, fun _ _ _ => trivial⟩

def IdF.bot (A : C ⥤ CommAlgCat.{0} R) : IdF A :=
  ⟨fun _ => ⊥, fun φ x hx => by rw [Ideal.mem_bot.1 hx, map_zero]; exact Ideal.zero_mem _⟩

def IdF.sup (a b : IdF A) : IdF A :=
  ⟨fun T => a.S T ⊔ b.S T, fun φ x hx => by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (a.map_mem φ hy) (b.map_mem φ hz)⟩

def IdF.span (A : C ⥤ CommAlgCat.{0} R) (c : R) : IdF A :=
  ⟨fun T => Ideal.span {algebraMap R (A.obj T) c}, fun φ x hx => by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, AlgHom.commutes]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)⟩

abbrev sqM (a b : IdF A) (T : C) : Submodule R (A.obj T ⧸ b.S T) :=
  ((a.S T).map (Ideal.Quotient.mk (b.S T))).restrictScalars R

def sqMk (a b : IdF A) {T : C} (x : A.obj T) (hx : x ∈ a.S T) : sqM a b T :=
  ⟨Ideal.Quotient.mk _ x, Ideal.mem_map_of_mem _ hx⟩

def sqMap {T T' : C} (a b : IdF A) (φ : T ⟶ T') : sqM a b T →ₗ[R] sqM a b T' :=
  (Ideal.quotientMapₐ (b.S T') (A.map φ).hom (fun _ hx => b.map_mem φ hx)).toLinearMap.restrict fun x hx => by
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    exact Ideal.mem_map_of_mem (Ideal.Quotient.mk (b.S T')) (a.map_mem φ hy)

def sq (a b : IdF A) : C ⥤ ModuleCat.{0} R where
  obj T := ModuleCat.of R (sqM a b T)
  map φ := ModuleCat.ofHom (sqMap a b φ)
  map_id T := by
    ext ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sqMap, LinearMap.restrict_apply]
  map_comp φ ψ := by
    ext ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sqMap, LinearMap.restrict_apply]

def sqLe {a b a' b' : IdF A} (ha : ∀ T, a.S T ≤ a'.S T) (hb : ∀ T, b.S T ≤ b'.S T) :
    CH.Mor (sq a b) (sq a' b') (RingHom.id R) where
  G := 𝟭 C
  τ T := (Ideal.Quotient.factorₐ R (hb T)).toLinearMap.restrict fun x hx => by
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    exact Ideal.mem_map_of_mem (Ideal.Quotient.mk (b'.S T)) (ha T hy)
  nat φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

structure PDF (R : Type) [CommRing R] (C : Type u) [Category.{v} C] where
  A : C ⥤ CommAlgCat.{0} R
  J : IdF A
  dp : ∀ {T : C}, ℕ → A.obj T → A.obj T
  dp_zero : ∀ {T : C} {x : A.obj T}, x ∈ J.S T → dp 0 x = 1
  dp_one : ∀ {T : C} {x : A.obj T}, x ∈ J.S T → dp 1 x = x
  dp_zero_right : ∀ {T : C} {k : ℕ}, k ≠ 0 → dp k (0 : A.obj T) = 0
  dp_add : ∀ {T : C} (k : ℕ) {x y : A.obj T}, x ∈ J.S T → y ∈ J.S T →
    dp k (x + y) = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, dp ij.1 x * dp ij.2 y
  dp_map : ∀ {T T' : C} (φ : T ⟶ T') (k : ℕ) {x : A.obj T}, x ∈ J.S T → (A.map φ).hom (dp k x) = dp k ((A.map φ).hom x)

variable (Φ : PDF R C)

structure Poly where
  P : C → C
  j : ∀ T : C, T ⟶ P T
  X : ∀ T : C, Φ.A.obj (P T)
  X_mem : ∀ T, X T ∈ Φ.J.S (P T)
  univ : ∀ {T T' : C} (φ : T ⟶ T') (x : Φ.A.obj T'), x ∈ Φ.J.S T' →
    ∃! ψ : P T ⟶ T', j T ≫ ψ = φ ∧ (Φ.A.map ψ).hom (X T) = x
  span : ∀ (T : C) (z : Φ.A.obj (P T)), ∃ b : ℕ →₀ Φ.A.obj T,
    z = b.sum fun k c => (Φ.A.map (j T)).hom c * Φ.dp k (X T)

variable {Φ}

def Poly.Crit (Q : Poly Φ) (a : ℤ → IdF Φ.A) (r : ℤ) : Prop :=
  ∀ (T : C) (b : ℕ →₀ Φ.A.obj T),
    (b.sum fun k c => (Φ.A.map (Q.j T)).hom c * Φ.dp k (Q.X T)) ∈ (a r).S (Q.P T) ↔ ∀ k : ℕ, b k ∈ (a (r - k)).S T

structure Poly.Ladder (Q : Poly Φ) (a b : ℤ → IdF Φ.A) (r : ℤ) : Prop where
  le : ∀ (r' : ℤ) (T : C), (b r').S T ≤ (a r').S T
  ca : ∀ r' ≤ r, Q.Crit a r'
  cb : ∀ r' ≤ r, Q.Crit b r'

variable (Φ) in

structure Frame (d : ℕ) where
  D : C
  ne : ∀ T : C, Nonempty (D ⟶ T)
  τ : Fin d → ∀ {T : C}, (D ⟶ T) → (D ⟶ T) → Φ.A.obj T
  mem : ∀ (i : Fin d) {T : C} (σ σ' : D ⟶ T), τ i σ σ' ∈ Φ.J.S T
  add : ∀ (i : Fin d) {T : C} (σ σ' σ'' : D ⟶ T), τ i σ σ'' = τ i σ σ' + τ i σ' σ''
  nat : ∀ (i : Fin d) {T T' : C} (σ σ' : D ⟶ T) (φ : T ⟶ T'), τ i (σ ≫ φ) (σ' ≫ φ) = (Φ.A.map φ).hom (τ i σ σ')
  bij : ∀ {T : C} (σ : D ⟶ T) (y : Fin d → Φ.A.obj T), (∀ i, y i ∈ Φ.J.S T) → ∃! σ' : D ⟶ T, ∀ i, τ i σ σ' = y i

structure IsFil (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) : Prop where
  top : ∀ r ≤ (0 : ℤ), ∀ T, (Fil r).S T = ⊤
  one : ∀ T, (Fil 1).S T = Φ.J.S T
  anti : ∀ {r r' : ℤ}, r ≤ r' → ∀ T, (Fil r').S T ≤ (Fil r).S T
  mul : ∀ (r r' : ℕ) (T : C) {x y : Φ.A.obj T}, x ∈ (Fil r).S T → y ∈ (Fil r').S T → x * y ∈ (Fil ((r + r' : ℕ) : ℤ)).S T
  dp_mem : ∀ (k : ℕ) (T : C) {x : Φ.A.obj T}, x ∈ Φ.J.S T → Φ.dp k x ∈ (Fil k).S T

abbrev gr (Fil : ℤ → IdF Φ.A) (r : ℤ) : C ⥤ ModuleCat.{0} R := sq (Fil r) (Fil (r + 1))

namespace Frame

variable {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T)

def a (i : Fin d) {T T' : C} (φ : T ⟶ T') : Φ.A.obj T' := E.τ i (σ T ≫ φ) (σ T')

def form {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C j) : Φ.A.obj (s.obj (Fin.last j)) :=
  (∏ k : Fin j, (Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
    (E.a σ (I k) (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le)))) * (Φ.A.map (σ _)).hom x

def GrConst (Fil : ℤ → IdF Φ.A) : Prop :=
  ∀ (q : ℕ) {T : C} (σ σ' : E.D ⟶ T) {x : Φ.A.obj E.D}, x ∈ (Fil q).S E.D →
    (Φ.A.map σ).hom x - (Φ.A.map σ').hom x ∈ (Fil ((q : ℤ) + 1)).S T

end Frame

abbrev Idx (j d : ℕ) : Type := {I : Fin j → Fin d // StrictMono I}

def Rep (a b : IdF A) {j : ℕ} (z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))) (c : CH.H (sq a b) j) : Prop :=
  ∃ (f : CH.Cn (sq a b) j) (hf : CH.d (sq a b) j f = 0), c = (CH.cx (sq a b)).cls f hf ∧
    ∀ s, (show sqM a b _ from f s).1 = Ideal.Quotient.mk _ (z s)

variable {R' : Type} [CommRing R'] {C' : Type u'} [Category.{v'} C']

structure SMor (Φ : PDF R C) (Φ' : PDF R' C') (σ : R →+* R') where
  G : C' ⥤ C
  ρ : ∀ T : C', Φ.A.obj (G.obj T) →+* Φ'.A.obj T
  comm : ∀ (T : C') (r : R), ρ T (algebraMap R _ r) = algebraMap R' _ (σ r)
  nat : ∀ {T T' : C'} (φ : T ⟶ T') (x : Φ.A.obj (G.obj T)), ρ T' ((Φ.A.map (G.map φ)).hom x) = (Φ'.A.map φ).hom (ρ T x)
  mem : ∀ (T : C') {x : Φ.A.obj (G.obj T)}, x ∈ Φ.J.S _ → ρ T x ∈ Φ'.J.S T
  dp : ∀ (T : C') (k : ℕ) {x : Φ.A.obj (G.obj T)}, x ∈ Φ.J.S _ → ρ T (Φ.dp k x) = Φ'.dp k (ρ T x)

variable {Φ' : PDF R' C'} {σ : R →+* R'}

def SMor.Le (m : SMor Φ Φ' σ) (a : IdF Φ.A) (a' : IdF Φ'.A) : Prop :=
  ∀ (T : C') (x : Φ.A.obj (m.G.obj T)), x ∈ a.S _ → m.ρ T x ∈ a'.S T

def SMor.sq (m : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.Le a a') (hb : m.Le b b') :
    CH.Mor (sq a b) (sq a' b') σ where
  G := m.G
  τ T :=
    { toFun := fun x => ⟨Ideal.quotientMap (b'.S T) (m.ρ T) (fun y hy => hb T y hy) (show sqM a b _ from x).1, by
        obtain ⟨x, hx⟩ := x
        obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
        exact Ideal.mem_map_of_mem (Ideal.Quotient.mk (b'.S T)) (ha T y hy)⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun r x => Subtype.ext (by
        obtain ⟨x, hx⟩ := x
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        change Ideal.Quotient.mk _ (m.ρ T (r • y)) = Ideal.Quotient.mk _ (σ r • m.ρ T y)
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, m.comm]) }
  nat φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Subtype.ext (congrArg (Ideal.Quotient.mk _) (m.nat φ y))

def SMor.Fr (m : SMor Φ Φ' σ) {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D) : Prop :=
  ∀ (i : Fin d) {T : C'} (s s' : E'.D ⟶ T), m.ρ T (E.τ i (e ≫ m.G.map s) (e ≫ m.G.map s')) = E'.τ i s s'

def PDF.res (Φ : PDF R C) (G : C' ⥤ C) : PDF R C' where
  A := G ⋙ Φ.A
  J := ⟨fun T => Φ.J.S (G.obj T), fun φ _ hx => Φ.J.map_mem (G.map φ) hx⟩
  dp k x := Φ.dp k x
  dp_zero := Φ.dp_zero
  dp_one := Φ.dp_one
  dp_zero_right := Φ.dp_zero_right
  dp_add := Φ.dp_add
  dp_map φ := Φ.dp_map (G.map φ)

def IdF.res (a : IdF A) (G : C' ⥤ C) : IdF (G ⋙ A) := ⟨fun T => a.S (G.obj T), fun φ _ hx => a.map_mem (G.map φ) hx⟩

end CrystallineSemistableComparison.Pb
