import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.StableBlock

noncomputable section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun
open PositivityTheory.Rg.BcB.SpectralAccumulation (TypeB HasType InfBdd)
open GroundTheory.Automorphic.AutomorphicForm (constantTerm)
open UpperTheory.V.Cj.S (Pl HasCap fL res BddS Ix opIx Act2 tOp)

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

structure Lev (bad : Set (Pl E)) (K : Subgroup (GL (Fin N) (Af E))) : Prop where
  isOpen : IsOpen (K : Set (GL (Fin N) (Af E)))
  int : ∀ u ∈ K, ∀ w, GeneralLinearGroup.map (pLoc E w) u ∈ KGL w N
  loc : ∀ w ∉ bad, ∀ k ∈ KGL w N, locGL E N w k ∈ K

structure EigT (bad : Set (Pl E)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (φ : Sm E N)
    (m : (E →+* ℂ) → Multiset ℂ) (B : Pl E → Multiset ℂˣ) : Prop where
  ne : φ ≠ 0
  aut : IsAutForm φ
  ty : TypeB K W φ
  cap : HasCap φ m
  sat : ∀ w ∉ bad, IsSatVecGL w (fL N w) φ (B w)

def MTo (m : ℕ → (E →+* ℂ) → Multiset ℂ) (m₀ : (E →+* ℂ) → Multiset ℂ) : Prop :=
  ∀ τ (ε : ℝ), 0 < ε → ∀ᶠ k in atTop, Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) (m k τ) (m₀ τ)

def STo (q n : ℕ) (B : ℕ → Multiset ℂˣ) (C : Multiset ℂˣ) : Prop :=
  ∀ i : ℕ, Tendsto (fun k => satEig q n (B k) i) atTop (𝓝 (satEig q n C i))

def Excl (X : Set (CuspSub E N)) (φ : Sm E N) : Prop :=
  ∀ π ∈ X, ∀ ψ ∈ π.V, ∀ z : ℂ, ¬ ∀ g, φ.1 g = ψ.1 g * Complex.exp (z * PositivityTheory.Rg.BcB.logAbs g.val.det)

def Read (bad : Set (Pl E)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (m₀ : (E →+* ℂ) → Multiset ℂ)
    (X : Set (CuspSub E N)) (P : Sm E N → Prop) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (D : J → CD E N) (C : J → Pl E → Multiset ℂˣ),
    (∀ j, (∀ π ∈ X, ¬ (D j).Has π) ∧ ∀ w ∉ bad, (D j).Sat w (C j w)) ∧
    ∀ (φ : ℕ → Sm E N) (m : ℕ → (E →+* ℂ) → Multiset ℂ) (B : ℕ → Pl E → Multiset ℂˣ),
      (∀ k, EigT bad K W (φ k) (m k) (B k) ∧ P (φ k)) → MTo m m₀ →
      ∃ (j : J) (s : ℕ → ℕ), StrictMono s ∧ ∀ w ∉ bad, STo (qV E w) N (fun k => B (s k) w) (C j w)

end

def LevShrink : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (bad : Set (Pl E))
  (K : Subgroup (GL (Fin N) (Af E))), IsOpen (K : Set (GL (Fin N) (Af E))) → (∀ w ∉ bad, ∀ k ∈ KGL w N, locGL E N w k ∈ K) →
    ∃ K' ≤ K, Lev bad K' ∧ ∀ c : GL (Fin N) (Af E), (∀ w, GeneralLinearGroup.map (pLoc E w) c ∈ KGL w N) → ∀ u ∈ K', c⁻¹ * u * c ∈ K'

def TypeSat : Prop := ∀ (G : Type) [Group G] (W : Submodule ℂ (G → ℂ)), FiniteDimensional ℂ W →
  ∃ W' : Submodule ℂ (G → ℂ), FiniteDimensional ℂ W' ∧ ∀ f : G → ℂ, (∀ a, (fun k => f (a * k)) ∈ W) → ∀ b, (fun k => f (k * b)) ∈ W'

def IwaT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ) (bad : Set (Pl E))
  (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), Lev bad K → FiniteDimensional ℂ W →
    ∃ (K' : Subgroup (GL (Fin (r + s)) (Af E))) (W' : Submodule ℂ (Kinf E (r + s) → ℂ)), Lev bad K' ∧ FiniteDimensional ℂ W' ∧ ∀ φ m B, EigT bad K W φ m B → (∃ g, constantTerm r φ.1 g ≠ 0) →
      ∃ φ', EigT bad K' W' φ' m B ∧ ∃ x y, res (constantTerm r φ'.1) x y ≠ 0

def SliceT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ) (bad : Set (Pl E))
  (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), Lev bad K → FiniteDimensional ℂ W →
    ∃ (K₁ : Subgroup (GL (Fin r) (Af E))) (W₁ : Submodule ℂ (Kinf E r → ℂ)) (K₂ : Subgroup (GL (Fin s) (Af E)))
      (W₂ : Submodule ℂ (Kinf E s → ℂ)), Lev bad K₁ ∧ FiniteDimensional ℂ W₁ ∧ Lev bad K₂ ∧ FiniteDimensional ℂ W₂ ∧
      ∀ φ : Sm E (r + s), IsAutForm φ → TypeB K W φ →
        (∀ y (f : Sm E r), (f.1 = fun x => res (constantTerm r φ.1) x y) → TypeB K₁ W₁ f) ∧
        ∀ x (f : Sm E s), f.1 = res (constantTerm r φ.1) x → TypeB K₂ W₂ f

def StabT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (bad : Set (Pl E))
  (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)), Lev bad K → FiniteDimensional ℂ W →
    ∀ S : Submodule ℂ (Sm E N), BddS S → (∀ φ ∈ S, TypeB K W φ) → ∃ V : Submodule ℂ (Sm E N), S ≤ V ∧ FiniteDimensional ℂ V ∧
      (∀ φ ∈ V, IsAutForm φ ∧ TypeB K W φ) ∧ (∀ w ∉ bad, V ≤ fixed (fL N w) (KGL w N)) ∧ ∀ i : Ix N bad, ∀ φ ∈ V, opIx i φ ∈ V

def StepT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ) (bad : Set (Pl E))
  (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), Lev bad K → FiniteDimensional ℂ W →
    ∃ (K₁ : Subgroup (GL (Fin r) (Af E))) (W₁ : Submodule ℂ (Kinf E r → ℂ)) (K₂ : Subgroup (GL (Fin s) (Af E)))
      (W₂ : Submodule ℂ (Kinf E s → ℂ)), Lev bad K₁ ∧ FiniteDimensional ℂ W₁ ∧ Lev bad K₂ ∧ FiniteDimensional ℂ W₂ ∧
      ∀ φ m B, EigT bad K W φ m B → (∃ g, constantTerm r φ.1 g ≠ 0) → ∃ φ₁ φ₂ m₁ m₂ B₁ B₂,
        EigT bad K₁ W₁ φ₁ m₁ B₁ ∧ EigT bad K₂ W₂ φ₂ m₂ B₂ ∧
        (∀ t, m t = (m₁ t).map (· + ((-((s : ℝ) / 2) : ℝ) : ℂ)) + (m₂ t).map (· + (((r : ℝ) / 2 : ℝ) : ℂ))) ∧
        ∀ ν ν' : HChar E, ν.IsAbsPow (-((s : ℝ) / 2)) → ν'.IsAbsPow ((r : ℝ) / 2) →
          ∀ w ∉ bad, B w = (B₁ w).map (· * ν.val w) + (B₂ w).map (· * ν'.val w)

def CuspMem : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), 1 ≤ N → ∀ (bad : Set (Pl E)), bad.Finite →
  ∀ K W (φ : Sm E N) m B, EigT bad K W φ m B → IsCuspForm φ →
    ∃ π : CuspSub E N, φ ∈ π.V ∧ (∀ t, π.HasInfChar t (m t)) ∧ ∀ w ∉ bad, (CG.mk π).HasSat w (B w)

def CuspFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), 1 ≤ N → ∀ (K : Subgroup (GL (Fin N) (Af E)))
  (W : Submodule ℂ (Kinf E N → ℂ)) (R : ℝ), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W →
    {π : CuspSub E N | GlobalTheory.DiscSpec.IsNormalised π ∧ HasType K W π.V ∧ InfBdd R π.V}.Finite

def NormTw : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), 1 ≤ N → ∀ (bad : Set (Pl E)) K W, Lev bad K →
  ∀ (π : CuspSub E N) (φ : Sm E N) (m : (E →+* ℂ) → Multiset ℂ), φ ∈ π.V → φ ≠ 0 → TypeB K W φ → (∀ t, π.HasInfChar t (m t)) →
    ∃ (π₀ : CuspSub E N) (z : ℂ), GlobalTheory.DiscSpec.IsNormalised π₀ ∧ π = π₀.twist (Model.absC E z) ∧ HasType K W π₀.V ∧
      (∀ t, π₀.HasInfChar t ((m t).map (· - z))) ∧ ∑ t, (m t).sum = (N : ℂ) * (Fintype.card (E →+* ℂ) : ℂ) * z ∧
      ∃ ψ ∈ π₀.V, ∃ z' : ℂ, ∀ g, φ.1 g = ψ.1 g * Complex.exp (z' * PositivityTheory.Rg.BcB.logAbs g.val.det)

def NormUniq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), 1 ≤ N → ∀ (π π₀ : CuspSub E N) (z : ℂ),
  (∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E N t * g) = ψ.1 g) → GlobalTheory.DiscSpec.IsNormalised π₀ →
    CG.mk (π₀.twist (Model.absC E z)) = CG.mk π → π₀ = π

def SatComb : Prop :=
  (∀ (q n : ℕ) (B : Multiset ℂˣ) (c : ℕ → ℂˣ) (c₀ : ℂˣ), Tendsto (fun k => (c k : ℂ)) atTop (𝓝 (c₀ : ℂ)) →
    STo q n (fun k => B.map (· * c k)) (B.map (· * c₀))) ∧
  ∀ (q r s : ℕ) (B₁ B₂ : ℕ → Multiset ℂˣ) (C₁ C₂ : Multiset ℂˣ) (α β : ℂˣ), q ≠ 0 → STo q r B₁ C₁ → STo q s B₂ C₂ →
    STo q (r + s) (fun k => (B₁ k).map (· * α) + (B₂ k).map (· * β)) (C₁.map (· * α) + C₂.map (· * β))

def SplitLim : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (m₀ : (E →+* ℂ) → Multiset ℂ) (α β : ℂ),
  ∃ T : Finset (((E →+* ℂ) → Multiset ℂ) × ((E →+* ℂ) → Multiset ℂ)), ∀ m m₁ m₂ : ℕ → (E →+* ℂ) → Multiset ℂ,
    (∀ k t, m k t = (m₁ k t).map (· + α) + (m₂ k t).map (· + β)) → MTo m m₀ →
    ∃ p ∈ T, ∃ s : ℕ → ℕ, StrictMono s ∧ MTo (fun k => m₁ (s k)) p.1 ∧ MTo (fun k => m₂ (s k)) p.2

def CDAdd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ) (D₁ : CD E r) (D₂ : CD E s) (ν ν' : HChar E),
  1 ≤ r → 1 ≤ s → ∃ D : CD E (r + s), (∀ π : CuspSub E (r + s), ¬ D.Has π) ∧ ∀ w B₁ B₂, ν.UnrAt w → ν'.UnrAt w → D₁.Sat w B₁ →
    D₂.Sat w B₂ → D.Sat w (B₁.map (· * ν.val w) + B₂.map (· * ν'.val w))

def CuspCase : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), 1 ≤ N → ∀ (bad : Set (Pl E)) (K : Subgroup (GL (Fin N) (Af E)))
  (W : Submodule ℂ (Kinf E N → ℂ)) m₀ (X : Set (CuspSub E N)), bad.Finite → Lev bad K → FiniteDimensional ℂ W →
    (∀ π ∈ X, ∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E N t * g) = ψ.1 g) → Read bad K W m₀ X fun φ => IsCuspForm φ ∧ Excl X φ

def CtCase : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ), 1 ≤ r → 1 ≤ s → ∀ bad : Set (Pl E),
  (∀ K (W : Submodule ℂ (Kinf E r → ℂ)) m₀, Lev bad K → FiniteDimensional ℂ W → Read (N := r) bad K W m₀ ∅ fun _ => True) →
  (∀ K (W : Submodule ℂ (Kinf E s → ℂ)) m₀, Lev bad K → FiniteDimensional ℂ W → Read (N := s) bad K W m₀ ∅ fun _ => True) →
  ∀ K (W : Submodule ℂ (Kinf E (r + s) → ℂ)) m₀ X, Lev bad K → FiniteDimensional ℂ W → Read (N := r + s) bad K W m₀ X fun φ => ∃ g, constantTerm r φ.1 g ≠ 0

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp
