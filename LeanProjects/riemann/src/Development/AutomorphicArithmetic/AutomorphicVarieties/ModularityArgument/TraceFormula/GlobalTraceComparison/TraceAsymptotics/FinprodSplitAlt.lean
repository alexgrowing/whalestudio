import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

def cv {G : Type} [Group G] (K : Subgroup G) (f g : G → ℂ) : G → ℂ := fun y => hint K fun z => f z * g (z⁻¹ * y)

def cf (q a b j : ℕ) (p : Fin (a + 1) × Fin (b + 1)) : ℂ :=
  if (p.1 : ℕ) + p.2 = j then
    (q : ℂ) ^ ((((p.1 : ℕ) : ℂ) * ((b : ℂ) - (p.2 : ℕ)) + ((p.2 : ℕ) : ℂ) * ((a : ℂ) - (p.1 : ℕ))) / 2) else 0

def chi {E : Type} [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (a b : ℕ) (w : Pl E) (m : GLw a w × GLw b w) : ℂ :=
  (μ.loc w ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂˣ)

def HintSph : Prop := ∀ (G : Type) [Group G] (K : Subgroup G) (u : G → ℂ), (∀ k ∈ K, ∀ x, u (x * k) = u x) → hint K u = ∑ᶠ q : G ⧸ K, u q.out

def CvHecke : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ f g : G → ℂ, IsHecke K f → IsHecke K g → IsHecke K (cv K f g)

def CvOp : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (f g : G → ℂ), IsHecke K f → IsHecke K g →
  ∀ x ∈ fixed ρ K, levOp ρ K K (cv K f g) LinearMap.id x = levOp ρ K K f LinearMap.id (levOp ρ K K g LinearMap.id x) ∧
    levOp ρ K K g LinearMap.id x ∈ fixed ρ K ∧ levOp ρ K K g LinearMap.id x = heckeVec ρ K g x

def CtSph : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a b : ℕ) (h : a + b = n) (f : GLw n w → ℂ), IsHecke (KGL w n) f → ∀ m,
  ct h w f m = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) *
      ∑ᶠ q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w, f (blk h w m (Multiplicative.toAdd q.out)) ∧
    (Function.support fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w =>
      f (blk h w m (Multiplicative.toAdd q.out))).Finite

def CtLin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a b : ℕ) (h : a + b = n) (f g : GLw n w → ℂ) (c : ℂ), IsHecke (KGL w n) f → IsHecke (KGL w n) g →
  ct h w (fun y => f y + g y) = (fun m => ct h w f m + ct h w g m) ∧ ct h w (fun y => c * f y) = fun m => c * ct h w f m

def CtUnit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a b : ℕ) (h : a + b = n), ct h w ((KGL w n : Set _).indicator 1) = (K2 a b w : Set _).indicator 1

def CtT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a b : ℕ) (h : a + b = n) (j : Fin (n + 1)) (m : GLw a w × GLw b w),
  ct h w (Tj ℂ n (Ov E w) (unif w) j) m = ∑ p : Fin (a + 1) × Fin (b + 1),
    cf (qV E w) a b j p * (Tj ℂ a (Ov E w) (unif w) p.1 m.1 * Tj ℂ b (Ov E w) (unif w) p.2 m.2)

def CtMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n a b : ℕ) (h : a + b = n) (f g : GLw n w → ℂ), IsHecke (KGL w n) f → IsHecke (KGL w n) g →
  ct h w (cv (KGL w n) f g) = cv (K2 a b w) (ct h w f) (ct h w g)

def SatSum : Prop := ∀ (q a b : ℕ), q ≠ 0 → ∀ (B₁ B₂ : Multiset ℂˣ) (c₁ c₂ : ℂˣ), B₁.card = a → B₂.card = b → ∀ j : ℕ,
  satEig q (a + b) (B₁.map (· * c₁) + B₂.map (· * c₂)) j = ∑ p : Fin (a + 1) × Fin (b + 1),
    cf q a b j p * (c₁ : ℂ) ^ (p.1 : ℕ) * (c₂ : ℂ) ^ (p.2 : ℕ) * (satEig q a B₁ p.1 * satEig q b B₂ p.2)

def MuTw : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (μ : HChar E), μ.UnrAt w → ∀ (a b : ℕ),
  (∀ m ∈ K2 a b w, chi μ a b w m = 1) ∧ (∀ m m', chi μ a b w (m * m') = chi μ a b w m * chi μ a b w m') ∧
  ∀ (i j : ℕ) (m : GLw a w × GLw b w), i ≤ a → j ≤ b → Tj ℂ a (Ov E w) (unif w) i m.1 * Tj ℂ b (Ov E w) (unif w) j m.2 ≠ 0 →
    chi μ a b w m = ((μ.val w ^ b : ℂˣ) : ℂ) ^ i * ((μ.val w ^ a : ℂˣ) : ℂ) ^ j

def LevelU : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w → (∀ f : GLw n w → ℂ, Lc (KGL w n) f → Lc (KL n w) fun x : UL n w => f x.1) ∧
  ∀ f : GLw n w → ℂ, IsHecke (KGL w n) f → IsHecke (KL n w) fun x : UL n w => f x.1

def UnitHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (w : Pl E), IsOpen (KL n w : Set (UL n w)) ∧ IsHecke (KL n w) ((KL n w : Set _).indicator 1) ∧
  IsOpen (KGL w n : Set (GLw n w)) ∧ IsCompact (KGL w n : Set (GLw n w)) ∧
  IsOpen (K2 a b w : Set (GLw a w × GLw b w)) ∧ IsCompact (K2 a b w : Set (GLw a w × GLw b w)) ∧
  ∀ k ∈ KGL w n, thL n w k ∈ KGL w n

def TrUnit : Prop := ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G),
  twTr ρ K K ((K : Set G).indicator 1) LinearMap.id = (Module.finrank ℂ (fixed ρ K) : ℂ)

def CompSplit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)) (w : Pl E), IsSplitAt w → ∀ σ : SmIrr (UL n w), IsCompU π w σ →
  ∃ τ : SmIrr (GLw n w), IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧
    (fixed σ.ρ (KL n w) ≠ ⊥ → fixed τ.ρ (KGL w n) ≠ ⊥) ∧
    Module.finrank ℂ (fixed σ.ρ (KL n w)) = Module.finrank ℂ (fixed τ.ρ (KGL w n)) ∧
    ∀ f : GLw n w → ℂ, IsHecke (KGL w n) f →
      twTr σ.ρ (KL n w) (KL n w) (fun x => f x.1) LinearMap.id = twTr τ.ρ (KGL w n) (KGL w n) f LinearMap.id

def TrSph : Prop := ExAct → SplitLine → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (τ : SmIrr (GLw n w)) (B : Multiset ℂˣ), HasSatGL w τ.ρ B → ∀ e,
  twTr τ.ρ (KGL w n) (KGL w n) (fn1 n w e) LinearMap.id = ev1 n w e B

def UnramOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (π : Submodule ℂ (UA E n → ℂ)) (K' : ∀ w : Pl E, Subgroup (UL n w)), HasLevel S π K' →
  ∀ w ∈ S, K' w = KL n w → IsUnramU π w

def FinprodSplit : Prop := ∀ (α : Type) (S : Set α) (Z T : Finset α) (F : α → ℂ), (∀ w ∈ Z, w ∈ S) → (∀ w ∈ T, w ∈ S) → Disjoint T Z →
  (∀ w ∈ S, w ∉ Z → w ∉ T → F w = 1) → ∏ᶠ w ∈ S, F w = (∏ w ∈ Z, F w) * ∏ w ∈ T, F w

def InfInj : Prop := ∀ (n : ℕ) (l l' : DomWeight n), infOfWeight l = infOfWeight l' → l = l'

def SwapCl : Prop := ∀ (G H : Type) [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] (θ : G →* G) (θ' : H →* H) (K : Subgroup G)
  (K' : Subgroup H) (S : Set (G × H)) (f : G × H → ℂ), Subsingleton H → (∀ x ∈ S, ∀ g, g⁻¹ * x * θ.prodMap θ' g ∈ S) →
  clSum (θ'.prodMap θ) (K'.prod K) (Prod.swap '' S) 1 (fun y => f y.swap) = clSum (θ.prodMap θ') (K.prod K') S 1 f

def CtSwap : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ) (g : GLw n w),
  ctMu (Nat.zero_add n) w μ f (1, g) = ctMu (Nat.add_zero n) w μ f (g, 1) ∧
    ctMu (Nat.add_zero n) w μ f (g, 1) = avg fun k : KGL w n => f (toSub _ ((k : GLw n w)⁻¹ * g * k))

def DcosSep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ), ordL (ϖ : w.adicCompletion E) = 1 → ∀ x : Fin n → ℤ, StrictAnti x →
  Lc (KGL w n) (dcos n w (tdiag ϖ x)) ∧ ∀ y, dcos n w (tdiag ϖ x) y ≠ 0 → y.val.charpoly.Separable

def DcosTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ), ordL (ϖ : w.adicCompletion E) = 1 → ∀ (τ : SmIrr (GLw n w)),
  fixed τ.ρ (KGL w n) ≠ ⊥ → ∃ x : Fin n → ℤ, StrictAnti x ∧ trc τ.ρ (KGL w n) (dcos n w (tdiag ϖ x)) ≠ 0

def TrLevel : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (f : G → ℂ) (K₁ K₂ : Subgroup G),
  IsOpen (K₂ : Set G) → K₂ ≤ K₁ → K₁ ≤ K → IsHecke K₁ f → FiniteDimensional ℂ (fixed ρ K₂) →
  twTr ρ K K₂ f LinearMap.id = twTr ρ K K₁ f LinearMap.id

def admitted : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (τ : SmIrr (GLw n w)) (U : Subgroup (GLw n w)), IsOpen (U : Set (GLw n w)) →
  FiniteDimensional ℂ (fixed τ.ρ U)

def RCtEx : Prop := ExAct → CtLin → CtUnit → CtT → CtMul → SatSum → MuTw → HintSph → CtEx

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
