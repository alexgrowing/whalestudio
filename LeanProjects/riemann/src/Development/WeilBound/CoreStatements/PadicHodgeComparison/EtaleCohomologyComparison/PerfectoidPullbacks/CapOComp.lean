import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

universe w w' v u v' u'

namespace CrystallineSemistableComparison.Pb

def Tens (R : Type) [CommRing R] {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    {M : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {M' : Type w'} [AddCommGroup M']
    (f : ∀ i, N i → M i → M') : Prop :=
  ∃ g : (∀ i, N i ⊗[R] M i) ≃+ M', ∀ i n x, g (Pi.single i (n ⊗ₜ x)) = f i n x

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {R' : Type} [CommRing R'] {C' : Type u'} [Category.{v'} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'}

def SMor.LeC (m : SMor Φ Φ' σ) (c : R') (a : IdF Φ.A) (a' : IdF Φ'.A) : Prop :=
  ∀ (T : C') (x : Φ.A.obj (m.G.obj T)), x ∈ a.S _ → algebraMap R' _ c * m.ρ T x ∈ a'.S T

def SMor.qC (m : SMor Φ Φ' σ) (c : R') {b : IdF Φ.A} {b' : IdF Φ'.A} (hb : m.LeC c b b') (T : C') :
    Φ.A.obj (m.G.obj T) ⧸ b.S _ →+ Φ'.A.obj T ⧸ b'.S T :=
  QuotientAddGroup.map (b.S _).toAddSubgroup (b'.S T).toAddSubgroup
    ((AddMonoidHom.mulLeft (algebraMap R' _ c)).comp (m.ρ T).toAddMonoidHom) fun x hx => hb T x hx

theorem SMor.qC_mk (m : SMor Φ Φ' σ) (c : R') {b : IdF Φ.A} {b' : IdF Φ'.A} (hb : m.LeC c b b') (T : C') (x) :
    m.qC c hb T (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap R' _ c * m.ρ T x) := rfl

def SMor.sqC (m : SMor Φ Φ' σ) (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') :
    CH.Mor (Pb.sq a b) (Pb.sq a' b') σ where
  G := m.G
  τ T :=
    { toFun := fun x => ⟨m.qC c hb T (show sqM a b _ from x).1, by
        obtain ⟨x, hx⟩ := x
        obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
        exact Ideal.mem_map_of_mem (Ideal.Quotient.mk (b'.S T)) (ha T y hy)⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun r x => Subtype.ext (by
        obtain ⟨x, hx⟩ := x
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        change Ideal.Quotient.mk _ (_ * m.ρ T (r • y)) = Ideal.Quotient.mk _ (σ r • (_ * m.ρ T y))
        refine congrArg (Ideal.Quotient.mk _) ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, m.comm, mul_left_comm]) }
  nat φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Subtype.ext (congrArg (Ideal.Quotient.mk _) ?_)
    change _ * m.ρ _ _ = (Φ'.A.map φ).hom (_ * _)
    rw [map_mul, AlgHom.commutes]
    exact congrArg _ (m.nat φ y)

def Cosieve (U : ObjectProperty C) : Prop := ∀ ⦃T T' : C⦄, (T ⟶ T') → U T → U T'

def capS {ι : Type} (U : ι → ObjectProperty C) (S : Finset ι) : ObjectProperty C := fun T => ∀ α ∈ S, U α T

abbrev HU (F : C ⥤ ModuleCat.{w} R) (U : ObjectProperty C) (j : ℕ) : Type (max u v w) := CH.H (U.ι ⋙ F) j

def resU (F : C ⥤ ModuleCat.{w} R) {U V : ObjectProperty C} (h : V ≤ U) : CH.Mor (U.ι ⋙ F) (V.ι ⋙ F) (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

def morU {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} (m : CH.Mor F F' σ) {U : ObjectProperty C}
    {U' : ObjectProperty C'} (h : ∀ T, U' T → U (m.G.obj T)) : CH.Mor (U.ι ⋙ F) (U'.ι ⋙ F') σ where
  G := U.lift (U'.ι ⋙ m.G) fun T => h _ T.property
  τ T := m.τ T.obj
  nat φ x := m.nat φ.hom x

def capT {ι : Type} (U : ι → ObjectProperty C) {n : ℕ} (i : Fin n → ι) : ObjectProperty C := fun T => ∀ a, U (i a) T

abbrev cechH (F : C ⥤ ModuleCat.{w} R) {ι : Type} (U : ι → ObjectProperty C) (q : ℕ) : Cos.{max u v w} R where
  X n := ∀ i : Fin (n + 1) → ι, HU F (capT U i) q
  δ n k := LinearMap.pi fun i => ((resU F (U := capT U (i ∘ k.succAbove)) (V := capT U i) fun _ h _ => h _).pull q).comp
    (LinearMap.proj (i ∘ k.succAbove))
  rel n j i x := by
    funext t
    have e : (t ∘ (j.succAbove i).succAbove) ∘ (i.predAbove j).succAbove = (t ∘ j.succAbove) ∘ i.succAbove :=
      funext fun k => congrArg t (Fin.succAbove_succAbove_succAbove_predAbove j i k)
    have key : ∀ (a a' : Fin (n + 2) → ι) (b b' : Fin (n + 1) → ι) (hb : b = b') h1 h2 h3 h4,
        (resU F (U := capT U a) (V := capT U t) h1).pull q ((resU F (U := capT U b) (V := capT U a) h2).pull q (x b)) =
        (resU F (U := capT U a') (V := capT U t) h3).pull q ((resU F (U := capT U b') (V := capT U a') h4).pull q (x b')) := by
      intro a a' b b' hb h1 h2 h3 h4
      subst hb
      obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x b)
      rw [← hz]
      rfl
    exact key _ _ _ _ e _ _ _ _

structure Serre (R : Type) [CommRing R] where
  P : ∀ (M : Type w) [AddCommGroup M] [Module R M], Prop
  zero : ∀ (M : Type w) [AddCommGroup M] [Module R M], Subsingleton M → P M
  mid : ∀ (M₁ M₂ M₃ : Type w) [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃), Function.Exact f g → P M₁ → P M₃ → P M₂

def AFG (c : R) (M : Type w) [AddCommGroup M] [Module R M] : Prop :=
  ∃ (n : ℕ) (N : Submodule R M), N.FG ∧ ∀ x : M, c ^ n • x ∈ N

def rs {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom

def capO {X : Scheme.{0}} {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) : X.Opens := ⨅ a, U (i a)

theorem capO_le {X : Scheme.{0}} {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (a : Fin n) : capO U i ≤ U (i a) :=
  iInf_le (fun a => U (i a)) a

theorem capO_comp {X : Scheme.{0}} {ι : Type} (U : ι → X.Opens) {m n : ℕ} (i : Fin n → ι) (θ : Fin m → Fin n) :
    capO U i ≤ capO U (i ∘ θ) := le_iInf fun b => capO_le U i (θ b)

structure VB {O : Type} [CommRing O] {X : Scheme.{0}} (str : ∀ V : X.Opens, O →+* Γ(X, V)) {ι : Type} (U : ι → X.Opens)
    (K : Cos.{w} O) where
  κ : ι → Type
  [fin : ∀ α, Fintype (κ α)]
  g : ∀ α β, κ α → κ β → Γ(X, U α ⊓ U β)
  e : ∀ (n : ℕ) (a : Fin (n + 1)), K.X n ≃+ ∀ i : Fin (n + 1) → ι, κ (i a) → Γ(X, capO U i)
  e_smul : ∀ n a (c : O) x i k, e n a (c • x) i k = str _ c * e n a x i k
  e_δ : ∀ n (a : Fin (n + 1)) (b : Fin (n + 2)) x (i : Fin (n + 2) → ι) (k : κ (i (b.succAbove a))),
    e (n + 1) (b.succAbove a) (K.δ n b x) i k = rs (capO_comp U i b.succAbove) (e n a x (i ∘ b.succAbove) k)
  e_chg : ∀ n (a b : Fin (n + 1)) x (i : Fin (n + 1) → ι) (k : κ (i a)),
    e n a x i k = ∑ k' : κ (i b), rs (le_inf (capO_le U i a) (capO_le U i b)) (g (i a) (i b) k k') * e n b x i k'

end CrystallineSemistableComparison.Pb
