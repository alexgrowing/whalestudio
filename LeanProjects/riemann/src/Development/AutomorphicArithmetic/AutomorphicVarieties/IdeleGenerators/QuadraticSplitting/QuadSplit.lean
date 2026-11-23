import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Matrix

namespace UpperTheory.V.Sd.S2

section Alg

variable {k : Type} [Field k]

def mix (γ : kˣ) (A B : Matrix (Fin 2) (Fin 2) k) : M4 k :=
  (2 : k)⁻¹ • !![A 1 1 + B 1 1, A 1 0 / γ - B 1 0, B 1 1 - A 1 1, A 1 0 / γ + B 1 0;
    γ * A 0 1 - B 0 1, A 0 0 + B 0 0, -(γ * A 0 1) - B 0 1, A 0 0 - B 0 0;
    B 1 1 - A 1 1, -(A 1 0 / γ) - B 1 0, A 1 1 + B 1 1, -(A 1 0 / γ) + B 1 0;
    γ * A 0 1 + B 0 1, A 0 0 - B 0 0, -(γ * A 0 1) + B 0 1, A 0 0 + B 0 0]

variable {Γ₀ Γ : Type} [Group Γ₀] [Group Γ]

structure IsMix (j : Γ₀ →* Γ) (t : Γ) (α β : kˣ) (ρ : Γ₀ →* GL (Fin 2) k) (R : Γ →* GL (Fin 4) k) : Prop where
  two : (2 : k) ≠ 0
  inj : Function.Injective j
  index : j.range.index = 2
  nmem : t ∉ j.range
  sq : ∀ u, j u = t * t → (ρ u : Matrix (Fin 2) (Fin 2) k) = Matrix.diagonal ![(α : k) ^ 2, (β : k) ^ 2]
  on : ∀ h h', j h' = t⁻¹ * j h * t → (R (j h) : M4 k) = mix (β / α) (ρ h) (ρ h')
  off : (R t : M4 k) = Matrix.diagonal ![(β : k), -(α : k), -(β : k), (α : k)]

def Flag {S : Type} (A : S → GL (Fin 2) k) (κ : Fin 2 → S → kˣ) : Prop :=
  ∃ g : GL (Fin 2) k, ∀ s, (g * A s * g⁻¹ : GL (Fin 2) k) 1 0 = 0 ∧ ∀ i, (g * A s * g⁻¹ : GL (Fin 2) k) i i = (κ i s : k)

end Alg

section Norm

variable {l : ℕ} [Fact l.Prime]

def Rib (A : GL (Fin 2) (Qbar l)) (x : (Qbar l)ˣ) : Prop :=
  ‖A 0 0 - 1‖ < 1 ∧ ‖A 1 1 - x‖ < 1 ∧ ‖A 1 0‖ < 1 ∧ ‖A 0 1‖ ≤ 1

def LowQ (n : M4 (Qbar l)) : Prop := IsLow n ∧ (∀ i j, ‖n i j‖ ≤ 1) ∧ ‖n 2 1‖ < 1 ∧ ‖n 2 0‖ = 1

def up {c : Coef l} {Γ : Type} [Group Γ] (χ : Γ →* c.Oˣ) : Γ →* (Qbar l)ˣ :=
  (Units.map (algebraMap c.O (Qbar l)).toMonoidHom).comp χ

end Norm

section Gal

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

def SplitIn (p : ℕ) (k₀ : IntermediateField ℚ Ω) : Prop :=
  ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → Dec (F := ℚ) A ≤ k₀.fixingSubgroup

structure MixDat (k₀ : IntermediateField ℚ Ω) [NumberField k₀] [IsTotallyReal k₀] (ι : Qbar l ≃+* ℂ) (x : G ℚ Ω →* (Qbar l)ˣ)
    (k t : ℕ) (r : G k₀ Ω →* GL (Fin 2) (Qbar l)) : Prop where
  hk : 2 ≤ k
  ht : 2 ≤ t
  dvd : l - 1 ∣ k
  cont : Continuous r
  irr : IrrOpen r
  att : ∃ π : TR.CuspSub k₀ 2, AttR ι r π ∧
    ∃ v v', v ≠ v' ∧ π.HasInfChar v (infOf ![(k : ℤ) + t, -(t : ℤ)]) ∧ π.HasInfChar v' (infOf ![(k : ℤ), 0])
  det : Matrix.GeneralLinearGroup.det.comp r = cycBar k₀ Ω l ^ k * x.comp (resQ k₀)
  res : ResSum r ![1, x.comp (resQ k₀)]
  away : TypeAway r ![1, x.comp (resQ k₀)]
  above : ∀ A A' : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g : G ℚ Ω, g ∉ k₀.fixingSubgroup → (∀ y, g y ∈ A ↔ y ∈ A') →
    (OrdAt r ![(k : ℤ) + t, -(t : ℤ)] ![x.comp (resQ k₀), 1] A ∧ OrdAt r ![(k : ℤ), 0] ![1, x.comp (resQ k₀)] A') ∨
    (OrdAt r ![(k : ℤ), 0] ![1, x.comp (resQ k₀)] A ∧ OrdAt r ![(k : ℤ) + t, -(t : ℤ)] ![x.comp (resQ k₀), 1] A')

variable {D : Raw Ω c} (T : Tower D)

structure Hyp (k₀ : IntermediateField ℚ Ω) (φ : G ℚ Ω →* (Qbar l)ˣ) : Prop where
  good : D.Good
  ok : T.Ok
  two : T.Two
  deep : T.Deep
  deg : Module.finrank ℚ k₀ = 2
  sp2 : SplitIn 2 k₀
  spl : SplitIn l k₀
  ps : ∀ g : G T.F Ω, T.rb wPs g = 1 ↔ resQ T.F g ∈ k₀.fixingSubgroup
  φ_in : ∀ g ∈ k₀.fixingSubgroup, φ g = 1
  φ_out : ∀ g ∉ k₀.fixingSubgroup, φ g = -1

abbrev ch (i : Fin 4) : G ℚ Ω →* (Qbar l)ˣ := up (chi D T.pr i)

structure CharDat (k₀ : IntermediateField ℚ Ω) (φ : G ℚ Ω →* (Qbar l)ˣ) : Prop where
  unit : ∀ (χ : G ℚ Ω →* c.Oˣ) g, ‖(up χ g : Qbar l)‖ = 1
  mul : ∀ i g, ch T i g * ch T i.rev g = up D.th g
  inn : ∀ g : G T.F Ω, resQ T.F g ∈ k₀.fixingSubgroup → ∀ i, Cong (ch T i (resQ T.F g)) (![up D.ξ, 1, up D.ξ, 1] i (resQ T.F g))
  out : resQ T.F T.g0 ∉ k₀.fixingSubgroup
  sq : ¬ Cong 1 (up D.ξ (resQ T.F T.g0 * resQ T.F T.g0))
  c3 : Cong (ch T 3 (resQ T.F T.g0)) 1 ∨ Cong (ch T 3 (resQ T.F T.g0)) (-1)
  c1 : Cong (ch T 1 (resQ T.F T.g0)) (-ch T 3 (resQ T.F T.g0))
  c2 : Cong (ch T 2 (resQ T.F T.g0)) (-ch T 0 (resQ T.F T.g0))
  mult : ∀ k : ℕ, l - 1 ∣ k → ∀ g : G T.F Ω, Cong (up D.th (resQ T.F g)) ((cycBar ℚ Ω l ^ k * up D.ξ * φ) (resQ T.F g))
  cont : ∀ k : ℕ, Continuous (up D.th / (cycBar ℚ Ω l ^ k * up D.ξ * φ) : G ℚ Ω →* (Qbar l)ˣ)
  al : ∀ (g : G T.F Ω) (n : ℕ), T.rb wAl g ^ n = 1 ↔ Cong (up D.ξ (resQ T.F g) ^ n) 1
  xi : ∀ g : G ℚ Ω, Cong (up D.ξ g) 1 → D.ξ g = 1
  om : ∀ g : G ℚ Ω, D.om g = 1 ↔ Cong (cycBar ℚ Ω l g) 1
  om_open : IsOpen (D.om.ker : Set (G ℚ Ω))

structure IndDat (k₀ : IntermediateField ℚ Ω) [NumberField k₀] [IsTotallyReal k₀] (φ : G ℚ Ω →* (Qbar l)ˣ) (ι : Qbar l ≃+* ℂ) (k t : ℕ)
    (r : G k₀ Ω →* GL (Fin 2) (Qbar l)) (α β : (Qbar l)ˣ) (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) (δ : G T.F Ω →* (Qbar l)ˣ) : Prop where
  hyp : Hyp T k₀ φ
  chars : CharDat T k₀ φ
  dat : MixDat k₀ ι (up D.ξ) k t r
  rib : ∀ h : G k₀ Ω, resQ k₀ h ∈ T.F.fixingSubgroup → Rib (r h) (up D.ξ (resQ k₀ h))
  ns : ∃ h : G k₀ Ω, resQ k₀ h ∈ T.F.fixingSubgroup ∧ ‖r h 0 1‖ = 1
  mix : IsMix (resQ k₀) (resQ T.F T.g0) α β r R
  cont : Continuous R
  gsp : ∀ g, IsGSp (((cycBar ℚ Ω l ^ k * up D.ξ * φ) g : (Qbar l)ˣ) : Qbar l) (R g : M4 (Qbar l))
  α_cong : Cong α (ch T 3 (resQ T.F T.g0))
  β_cong : Cong β (ch T 0 (resQ T.F T.g0))
  δ_cont : Continuous δ
  δ_sq : ∀ g, δ g ^ 2 * (cycBar ℚ Ω l ^ k * up D.ξ * φ) (resQ T.F g) = up D.th (resQ T.F g)
  δ_one : ∀ g, Cong (δ g) 1

def twF (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) (δ : G T.F Ω →* (Qbar l)ˣ) : G T.F Ω →* M4 (Qbar l) :=
  (Units.coeHom _).comp (tw (R.comp (resQ T.F)) δ)

structure GlobOk (ρ : G T.F Ω →* M4 (Qbar l)) : Prop where
  cont : Continuous ρ
  mult : ∀ g, IsGSp (up D.th (resQ T.F g) : Qbar l) (ρ g)
  kill : ∀ g ∈ (T.fr ∅).N, ρ g = 1
  nrm : (ρ T.g0).IsDiag
  int : ∀ g i j, ‖ρ g i j‖ ≤ 1
  diag : ∀ g i, ‖ρ g i i - ch T i (resQ T.F g)‖ < 1
  supp : ∀ g i j, i ≠ j → wt i j ∉ vV → ‖ρ g i j‖ < 1
  ent : (∃ g, ‖ρ g 1 0‖ = 1) ∨ ((∃ g, ‖ρ g 1 2‖ = 1) ∧ ∃ g, ‖ρ g 3 0‖ = 1)

structure LocOk (P : PD T.ι (G T.F Ω) (Qbar l)) : Prop where
  low : ∀ v, LowQ (P.n v)
  flag : ∀ v, ∀ s ∈ Dec (F := T.F) (T.pl v), IsUp (adj (P.n v) * P.r s * P.n v)
  mu : ∀ v, ∀ s ∈ muOf l (Dec (F := T.F) (T.pl v)), ∀ i, P.ψ v i s = 1
  char : ∀ v, ∀ s ∈ Dec (F := T.F) (T.pl v), ∀ i, ‖P.ψ v i s - ch T i (resQ T.F s)‖ < 1

end Gal

def MixEx : Prop :=
  ∀ (k Γ₀ Γ : Type) [Field k] [Group Γ₀] [Group Γ] (j : Γ₀ →* Γ) (t : Γ) (α β : kˣ) (ρ : Γ₀ →* GL (Fin 2) k) (μ : Γ →* kˣ),
    (2 : k) ≠ 0 → Function.Injective j → j.range.index = 2 → t ∉ j.range →
    (∀ u, j u = t * t → (ρ u : Matrix (Fin 2) (Fin 2) k) = Matrix.diagonal ![(α : k) ^ 2, (β : k) ^ 2]) →
    (∀ h, Matrix.GeneralLinearGroup.det (ρ h) = μ (j h)) → α * β = μ t →
    ∃ R : Γ →* GL (Fin 4) k, IsMix j t α β ρ R ∧ ∀ g, IsGSp (μ g : k) (R g : M4 k)

def MixCp : Prop :=
  ∀ (k Γ₀ Γ : Type) [Field k] [Group Γ₀] [Group Γ] (j : Γ₀ →* Γ) (t : Γ) (α β : kˣ) (ρ : Γ₀ →* GL (Fin 2) k) (R : Γ →* GL (Fin 4) k),
    IsMix j t α β ρ R → ∀ s : Γ, s ∉ j.range →
      (∀ g g' : Γ₀, j g' = s⁻¹ * j g * s → (R (j g) : M4 k).charpoly =
        (ρ g : Matrix (Fin 2) (Fin 2) k).charpoly * (ρ g' : Matrix (Fin 2) (Fin 2) k).charpoly) ∧
      ∀ g : Γ₀, j g = s * s → (R s : M4 k).charpoly = (ρ g : Matrix (Fin 2) (Fin 2) k).charpoly.comp (X ^ 2)

def MixIrr : Prop :=
  ∀ (k Γ₀ Γ : Type) [Field k] [Group Γ₀] [Group Γ] (j : Γ₀ →* Γ) (t : Γ) (α β : kˣ) (ρ : Γ₀ →* GL (Fin 2) k) (R : Γ →* GL (Fin 4) k),
    IsMix j t α β ρ R → ∀ U : Subgroup Γ, ¬ U ≤ j.range → IsIrr (ρ.comp (U.comap j).subtype) →
    (¬ ∃ M : GL (Fin 2) k, ∀ h h', j h ∈ U → j h' = t⁻¹ * j h * t → ρ h' = M * ρ h * M⁻¹) → IsIrr (R.comp U.subtype)

def MixCont : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ₀ Γ : Type) [Group Γ₀] [Group Γ] [TopologicalSpace Γ₀] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (j : Γ₀ →* Γ) (t : Γ) (α β : (Qbar l)ˣ) (ρ : Γ₀ →* GL (Fin 2) (Qbar l)) (R : Γ →* GL (Fin 4) (Qbar l)),
    IsMix j t α β ρ R → Topology.IsOpenEmbedding j → Continuous ρ → Continuous R

def SignTw : Prop :=
  ∀ (k Γ : Type) [Field k] [IsAlgClosed k] [Group Γ] (ρ ρ' : Γ →* GL (Fin 2) k) (H' : Subgroup Γ) (M : GL (Fin 2) k),
    IsIrr (ρ.comp H'.subtype) → (∀ h ∈ H', ρ' h = M * ρ h * M⁻¹) → ∀ s, (∀ h ∈ H', s * h * s⁻¹ ∈ H') →
    Matrix.GeneralLinearGroup.det (ρ' s) = Matrix.GeneralLinearGroup.det (ρ s) → ρ' (s * s) = M * ρ (s * s) * M⁻¹

def LocLine : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (S : Type) (A : S → GL (Fin 2) (Qbar l)) (x : S → (Qbar l)ˣ) (κ : Fin 2 → S → (Qbar l)ˣ),
    (∃ s, ¬ Cong (x s) 1) → (∀ s, Rib (A s) (x s)) → Flag A κ →
    (∀ s, Matrix.GeneralLinearGroup.det (A s) = κ 0 s * κ 1 s) ∧
    ((∀ s, Cong (κ 0 s) (x s)) → ∃ u : Qbar l, ‖u‖ ≤ 1 ∧
      ∀ s, (A s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ ![u, 1] = (κ 0 s : Qbar l) • ![u, 1]) ∧
    ((∀ s, Cong (κ 0 s) 1) → ∃ w : Qbar l, ‖w‖ < 1 ∧
      ∀ s, (A s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ ![1, w] = (κ 0 s : Qbar l) • ![1, w])

def MixFlag : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (γ : (Qbar l)ˣ) (u w : Qbar l), ‖(γ : Qbar l)‖ = 1 → ‖u‖ ≤ 1 → ‖w‖ < 1 →
    (∃ n : M4 (Qbar l), LowQ n ∧ ∀ (A B : Matrix (Fin 2) (Fin 2) (Qbar l)) (a a' b b' : Qbar l), a ≠ 0 → b ≠ 0 →
      A *ᵥ ![u, 1] = a • ![u, 1] → B *ᵥ ![1, w] = b • ![1, w] → A.det = a * a' → B.det = b * b' →
      IsUp (adj n * mix γ A B * n) ∧ ∀ i, (adj n * mix γ A B * n) i i = ![a, b, b', a'] i) ∧
    ∃ n : M4 (Qbar l), LowQ n ∧ ∀ (A B : Matrix (Fin 2) (Fin 2) (Qbar l)) (a a' b b' : Qbar l), a ≠ 0 → b ≠ 0 →
      A *ᵥ ![1, w] = a • ![1, w] → B *ᵥ ![u, 1] = b • ![u, 1] → A.det = a * a' → B.det = b * b' →
      IsUp (adj n * mix γ A B * n) ∧ ∀ i, (adj n * mix γ A B * n) i i = ![b, a, a', b'] i

def MixRes : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (γ x : (Qbar l)ˣ) (A B : GL (Fin 2) (Qbar l)), ‖(γ : Qbar l)‖ = 1 → ‖(x : Qbar l)‖ = 1 →
    Rib A x → Rib B x →
    (∀ i j, ‖mix γ A B i j‖ ≤ 1) ∧ (∀ i, ‖mix γ A B i i - ![(x : Qbar l), 1, x, 1] i‖ < 1) ∧
    (∀ i j, i ≠ j → wt i j ∉ vV → ‖mix γ A B i j‖ < 1) ∧
    (‖A 0 1‖ = 1 → ‖mix γ A B 1 0‖ = 1 ∨ (‖mix γ A B 1 2‖ = 1 ∧ ‖mix γ A B 3 0‖ = 1))

def SqrtChar : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] (η : Γ →* (Qbar l)ˣ), Continuous η →
    (∀ g, Cong (η g) 1) → ∃ δ : Γ →* (Qbar l)ˣ, Continuous δ ∧ (∀ g, δ g ^ 2 = η g) ∧ ∀ g, Cong (δ g) 1

def Descend : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), (∀ x : c.O, ‖(x : Qbar l)‖ ≤ 1 ∧ (x ∈ maximalIdeal c.O ↔ ‖(x : Qbar l)‖ < 1)) ∧
    ∀ (ι Γ : Type) [Finite ι] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
      (P : PD ι Γ (Qbar l)), Continuous P.r → (∀ g i j, ‖P.r g i j‖ ≤ 1) → (∀ v i j, ‖P.n v i j‖ ≤ 1) →
      ∃ (c₁ : Coef l) (_ : c.O ≤ c₁.O) (Q : PD ι Γ c₁.O), Q.map (algebraMap c₁.O (Qbar l)) = P ∧ Q.Cont (maximalIdeal c₁.O)

def QuadSplit : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (k₀ : IntermediateField ℚ Ω) [NumberField k₀], Module.finrank ℚ k₀ = 2 →
    ∀ p : ℕ, p.Prime → SplitIn p k₀ → SplitL k₀ p ∧ ∃ w w' : Pl k₀, w ≠ w' ∧ ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal ∧ ((p : ℕ) : 𝓞 k₀) ∈ w'.asIdeal ∧
      ∀ A A' : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∀ g : G ℚ Ω, g ∉ k₀.fixingSubgroup → (∀ y, g y ∈ A ↔ y ∈ A') →
        (IsPlaceOver A w ∧ IsPlaceOver A' w') ∨ (IsPlaceOver A w' ∧ IsPlaceOver A' w)

def EmbEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    (∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ τ : F →+* Qbar l, EmbAt w τ) ∧
    ∀ (w w' : Pl F) (τ τ' : F →+* Qbar l), EmbAt w τ → EmbAt w' τ' →
      InfinitePlace.mk (ι.toRingHom.comp τ) = InfinitePlace.mk (ι.toRingHom.comp τ') → w = w'

def ConjCc : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (a b : G ℚ Ω), IsConjEl a → IsConjEl b → IsConj a b

def MuIne : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ muOf l (Dec (F := F) A), s ∈ Ine (F := F) A ∧ cycZ F Ω l s = 1

def AutL : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (ι : Qbar l ≃+* ℂ) (R : G ℚ Ω →* GL (Fin 4) (Qbar l)), Continuous R → IsAutR ι R → IsIrr (R.comp (resQ T.L)) →
    IsAutC ι (R.comp (resQ T.L))

def PsiNe : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    D.Good → T.Ok → T.Two → ∃ g ∈ T.G', T.rb wPs g ≠ 1

def Chars : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (k₀ : IntermediateField ℚ Ω) (φ : G ℚ Ω →* (Qbar l)ˣ), Hyp T k₀ φ → CharDat T k₀ φ

def HypEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    D.Good → T.Ok → T.Two → T.Deep → ∃ (k₀ : IntermediateField ℚ Ω) (_ : NumberField k₀) (_ : IsTotallyReal k₀) (φ : G ℚ Ω →* (Qbar l)ˣ),
      Hyp T k₀ φ ∧ (resQ k₀).range = k₀.fixingSubgroup ∧ k₀.fixingSubgroup.index = 2 ∧ Topology.IsOpenEmbedding (resQ k₀)

def MixOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (k₀ : IntermediateField ℚ Ω) [NumberField k₀] [IsTotallyReal k₀] (φ : G ℚ Ω →* (Qbar l)ˣ) (ι : Qbar l ≃+* ℂ),
    Hyp T k₀ φ → CharDat T k₀ φ → ∃ k t r, MixDat k₀ ι (up D.ξ) k t r

def MixConj : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k₀ : IntermediateField ℚ Ω) [NumberField k₀]
    [IsTotallyReal k₀] (ι : Qbar l ≃+* ℂ) (x : G ℚ Ω →* (Qbar l)ˣ) (k t : ℕ) (r r' : G k₀ Ω →* GL (Fin 2) (Qbar l)),
    MixDat k₀ ι x k t r → RepIso r r' → MixDat k₀ ι x k t r'

def RibOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (k₀ : IntermediateField ℚ Ω) [NumberField k₀] [IsTotallyReal k₀] (φ : G ℚ Ω →* (Qbar l)ˣ) (ι : Qbar l ≃+* ℂ) (k t : ℕ)
    (r : G k₀ Ω →* GL (Fin 2) (Qbar l)), Hyp T k₀ φ → CharDat T k₀ φ → MixDat k₀ ι (up D.ξ) k t r →
    ∀ u : G k₀ Ω, resQ k₀ u = resQ T.F T.g0 * resQ T.F T.g0 → ∃ r', RepIso r r' ∧ r' u 0 1 = 0 ∧ r' u 1 0 = 0 ∧
      (∀ h : G k₀ Ω, resQ k₀ h ∈ T.F.fixingSubgroup → Rib (r' h) (up D.ξ (resQ k₀ h))) ∧
      ∃ h : G k₀ Ω, resQ k₀ h ∈ T.F.fixingSubgroup ∧ ‖r' h 0 1‖ = 1

def IndEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    D.Good → T.Ok → T.Two → T.Deep → ∀ ι : Qbar l ≃+* ℂ,
    ∃ (k₀ : IntermediateField ℚ Ω) (_ : NumberField k₀) (_ : IsTotallyReal k₀) (φ : G ℚ Ω →* (Qbar l)ˣ) (k t : ℕ)
      (r : G k₀ Ω →* GL (Fin 2) (Qbar l)) (α β : (Qbar l)ˣ) (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) (δ : G T.F Ω →* (Qbar l)ˣ),
      IndDat T k₀ φ ι k t r α β R δ

def AllInd (p : ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D),
    (Qbar l ≃+* ℂ) → (G ℚ Ω →* GL (Fin 4) (Qbar l)) → (G T.F Ω →* (Qbar l)ˣ) → Prop) : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (k₀ : IntermediateField ℚ Ω) [NumberField k₀] [IsTotallyReal k₀] (φ : G ℚ Ω →* (Qbar l)ˣ) (ι : Qbar l ≃+* ℂ) (k t : ℕ)
    (r : G k₀ Ω →* GL (Fin 2) (Qbar l)) (α β : (Qbar l)ˣ) (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) (δ : G T.F Ω →* (Qbar l)ˣ),
    IndDat T k₀ φ ι k t r α β R δ → p T ι R δ

def IndIrr : Prop := AllInd fun T _ R _ => IsIrr ((R.comp (resQ T.F)).comp T.G'.subtype)

def IndAutQ : Prop := AllInd fun _ ι R _ => IsAutR ι R

def IndGlob : Prop := AllInd fun T _ R δ => GlobOk T (twF T R δ)

def IndKill : Prop := AllInd fun T _ R δ => ∀ g ∈ (T.fr ∅).N, twF T R δ g = 1

def IndFlag : Prop := AllInd fun {Ω} _ _ _ {l} _ _ {D} T _ R _ => ∃ m : Fin 4 → ℤ, (∀ i : Fin 3, m i.succ + 2 ≤ m i.castSucc) ∧
  ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ n : M4 (Qbar l), LowQ n ∧ ∀ s ∈ Dec (F := T.F) A,
    IsUp (adj n * (R (resQ T.F s) : M4 (Qbar l)) * n) ∧ ∀ i,
      ‖(adj n * (R (resQ T.F s) : M4 (Qbar l)) * n) i i - ((![up D.ξ, 1, up D.ξ, 1] i (resQ T.F s) : (Qbar l)ˣ) : Qbar l)‖ < 1 ∧
      (s ∈ Ine (F := T.F) A → (adj n * (R (resQ T.F s) : M4 (Qbar l)) * n) i i = ((cycBar T.F Ω l s ^ m i : (Qbar l)ˣ) : Qbar l))

def IndDel : Prop := AllInd fun {Ω} _ _ _ {l} _ _ _ T _ _ δ => ∃ (b : ℤ) (N : ℕ) (U : Subgroup (G T.F Ω)), 0 < N ∧
  (∀ g, (δ g ^ 2 * cycBar T.F Ω l g ^ (-b)) ^ N = 1) ∧ IsOpen (U : Set (G T.F Ω)) ∧
  ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := T.F) A,
    (s ∈ U → δ s ^ 2 = cycBar T.F Ω l s ^ b) ∧ (cycZ T.F Ω l s = 1 → δ s = 1)

def IndLoc : Prop := AllInd fun {Ω} _ _ _ {l} _ _ _ T _ R δ => ∃ n, LocOk T ⟨twF T R δ, n⟩ ∧ ∃ (m : Fin 4 → ℤ) (b : ℤ) (N : ℕ),
  (∀ i : Fin 3, m i.succ + 2 ≤ m i.castSucc) ∧ T.Wts (fun i => 2 * m i + b) ⟨twF T R δ, n⟩ ∧ 0 < N ∧
  ∀ g, (δ g ^ 2 * cycBar T.F Ω l g ^ (-b)) ^ N = 1

def Final : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (ι : Qbar l ≃+* ℂ) (P : PD T.ι (G T.F Ω) (Qbar l)), GlobOk T P.r → LocOk T P → T.IsSeed ι P →
    ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPair ι h Q ∧
      Fr.InV (Φ := T.fr ∅) (Q.map (residue c₁.O)) ∧
      (Ent (Q.map (residue c₁.O)).r (-wAl) ∨ (Ent (Q.map (residue c₁.O)).r wBe ∧ Ent (Q.map (residue c₁.O)).r (-wTh)))

end UpperTheory.V.Sd.S2
