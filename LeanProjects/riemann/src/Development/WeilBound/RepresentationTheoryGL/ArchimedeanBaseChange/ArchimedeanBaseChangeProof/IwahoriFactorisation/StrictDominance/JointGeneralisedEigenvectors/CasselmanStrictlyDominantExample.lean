import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Formalism.SatakeDualWeyl.StatementF
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG

namespace PositivityTheory.SphericalProduct

def exampleCass : CassData (Multiplicative ℤ) where
  N := ⊥
  Nm := ⊥
  T := ⊤
  J := ⊥
  isOpen_J := isOpen_discrete _
  isCompact_J := by simpa using (Set.finite_singleton (1 : Multiplicative ℤ)).isCompact
  isClosed_N := isClosed_discrete _
  isClosed_Nm := isClosed_discrete _
  isClosed_alt := isClosed_discrete _
  norm_N t _ := Subgroup.mem_normalizer_iff.2 fun h => by simp [mul_comm]
  norm_Nm t _ := Subgroup.mem_normalizer_iff.2 fun h => by simp [mul_comm]
  fact_low x hx := ⟨1, one_mem _, 1, one_mem _, 1, one_mem _, by simpa using hx⟩
  fact_up x hx := ⟨1, one_mem _, 1, one_mem _, 1, one_mem _, by simpa using hx⟩

def IwahoriGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ),
    ∃ D : CassData (GL (Fin n) k), D.N = unipB k (Fin n) ∧ D.Nm = unipBLower k (Fin n) ∧
      D.T = (diagT k (Fin n)).range ∧ D.J = iwahori k (Fin n)

def DomGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (D : CassData (GL (Fin n) k)), D.N = unipB k (Fin n) → D.Nm = unipBLower k (Fin n) →
      D.T = (diagT k (Fin n)).range → D.J = iwahori k (Fin n) →
    ∀ ϖ : kˣ, ord k ϖ = 1 → ∀ (l : Fin n → ℤ) (t : D.T), (t : GL (Fin n) k) = diagT k (Fin n) (fun i => ϖ ^ l i) →
      (Antitone l → D.IsDom t) ∧ (StrictAnti l → D.IsStrDom t)

def IsLowUniM {L : Type} [Field L] {n : ℕ} (g : GL (Fin n) L) : Prop :=
  (∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) L) i j = 0) ∧ ∀ i : Fin n, (g : Matrix (Fin n) (Fin n) L) i i = 1

theorem twKer_eq_jacSub {G : Type} [Group G] [TopologicalSpace G] (D : CassData G) (P : G → Prop)
    (hP : ∀ g, g ∈ D.N ↔ P g) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    twKer ρ D.N 1 = jacSub ρ P := by
  unfold twKer jacSub
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · rintro ⟨n, v, rfl⟩
    exact ⟨n, (hP _).1 n.2, v, rfl⟩
  · rintro ⟨u, hu, v, rfl⟩
    exact ⟨⟨u, (hP _).2 hu⟩, v, rfl⟩

def IwahoriGLV : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ n : ℕ, ∃ D : CassData (GL (Fin n) L), D.J = IwGL L n ∧ (∀ g, g ∈ D.N ↔ IsUniM g) ∧
      (∀ g, g ∈ D.Nm ↔ IsLowUniM g) ∧ ∀ g, g ∈ D.T ↔ IsDiagM g

def IwahoriU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ n : ℕ, ∃ D : CassData (GU σ n), D.J = IwU σ n ∧
      (∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L)) ∧ (∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L)) ∧
      ∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L)

def DomGLV : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (D : CassData (GL (Fin n) L)), D.J = IwGL L n → (∀ g, g ∈ D.N ↔ IsUniM g) →
      (∀ g, g ∈ D.Nm ↔ IsLowUniM g) → (∀ g, g ∈ D.T ↔ IsDiagM g) → ∀ t : D.T,
      ((∀ i j : Fin n, i ≤ j → ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j) ≤
          ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)) → D.IsDom t) ∧
      (IsStrictDom (t : GL (Fin n) L) → D.IsStrDom t)

def DomU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (D : CassData (GU σ n)), D.J = IwU σ n →
      (∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L)) → (∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L)) →
      (∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L)) → ∀ t : D.T,
      ((∀ i j : Fin n, i ≤ j → ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j j) ≤
          ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)) → D.IsDom t) ∧
      (IsStrictDom ((t : GU σ n) : GL (Fin n) L) → D.IsStrDom t)

end PositivityTheory.SphericalProduct

end
