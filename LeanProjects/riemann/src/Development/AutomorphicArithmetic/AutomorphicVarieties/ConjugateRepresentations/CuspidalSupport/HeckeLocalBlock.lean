import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HasCapOneFn
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFinite
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Satake

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

namespace UpperTheory.V.Cj.S

abbrev Pl (E : Type) [Field E] : Type := HeightOneSpectrum (𝓞 E)

def hkOp {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) {K : Subgroup G}
    (hK : IsCommensurated K) {h : G → ℂ} (hh : h ∈ Hecke ℂ K) : Module.End ℂ V where
  toFun := heckeVec ρ K h
  map_add' x y := by
    simp only [heckeVec, map_add, smul_add]
    exact finsum_add_distrib (finite_heckeVec hK hh ρ x) (finite_heckeVec hK hh ρ y)
  map_smul' c x := (map_heckeVec hK hh (ρ' := ρ) (c • LinearMap.id) (fun g y => (map_smul (ρ g) c y).symm) x).symm

def Act2 {X Y : Type} {M : Submodule ℂ (X → ℂ)} {N : Submodule ℂ (Y → ℂ)} (A : Module.End ℂ M) (B : Module.End ℂ N)
    (F G : X → Y → ℂ) : Prop :=
  ∃ H : X → Y → ℂ, (∀ y, ∃ f : M, (f.1 = fun x => F x y) ∧ (A f).1 = fun x => H x y) ∧
    ∀ x, ∃ f : N, f.1 = H x ∧ (B f).1 = G x

def coef (q r s j : ℕ) (p : Fin (r + 1) × Fin (s + 1)) : ℂ :=
  if (p.1 : ℕ) + p.2 = j then (q : ℂ) ^ ((p.1 : ℕ) * (s - p.2)) else 0

def sub1 {r s : ℕ} (S : Finset (Fin (r + s))) : Finset (Fin r) := Finset.univ.filter fun i => Fin.castAdd s i ∈ S

def sub2 {r s : ℕ} (S : Finset (Fin (r + s))) : Finset (Fin s) := Finset.univ.filter fun i => Fin.natAdd r i ∈ S

def pair1 {r s : ℕ} (S : Finset (Fin (r + s))) (p : satakePairs (sub1 S)) : satakePairs S :=
  ⟨(Fin.castAdd s p.1.1, Fin.castAdd s p.1.2), by simpa [sub1] using p.2.1, by simpa [sub1] using p.2.2.1, p.2.2.2⟩

def pair2 {r s : ℕ} (S : Finset (Fin (r + s))) (p : satakePairs (sub2 S)) : satakePairs S :=
  ⟨(Fin.natAdd r p.1.1, Fin.natAdd r p.1.2), by simpa [sub2] using p.2.1, by simpa [sub2] using p.2.2.1,
    Nat.add_lt_add_left p.2.2.2 r⟩

section Forms

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def res {r s : ℕ} (F : GA E (r + s) → ℂ) (x : GA E r) (y : GA E s) : ℂ := F (blk x y)

def NI (r : ℕ) {n : ℕ} (F : GA E n → ℂ) : Prop := ∀ (X : UPos n r → Ad E) (g : GA E n), F (unipGL X * g) = F g

variable [IsTotallyComplex E]

variable (a) in

abbrev fL (w : Pl E) : Representation ℂ (GL (Fin a) (w.adicCompletion E)) (Sm E a) := locOf (finRep E a) w

variable (a) in

def tOp (w : Pl E) {ϖ : w.adicCompletion E} (hu : IsUnifV E w ϖ) (j : ℕ) : Module.End ℂ (Sm E a) :=
  hkOp (fL a w) (Final.GLintComm E w a) (Tj_mem_hecke hu j)

structure Eig (φ : Sm E a) (m : (E →+* ℂ) → Multiset ℂ) (B : Pl E → Multiset ℂˣ) : Prop where
  ne : φ ≠ 0
  aut : IsAutForm φ
  cap : HasCap φ m
  sat : ∀ᶠ w in Filter.cofinite, IsSatVecGL w (fL a w) φ (B w)

variable (E a) in

def Supp (k : ℕ) (m : (E →+* ℂ) → Multiset ℂ) (B : Pl E → Multiset ℂˣ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ) (π : ∀ i, CG E (n i)) (μ : ι → (E →+* ℂ) → Multiset ℂ),
    k ≤ Fintype.card ι ∧ (∀ i, 1 ≤ n i) ∧ ∑ i, n i = a ∧ (∀ i t, (π i).HasInfChar t (μ i t)) ∧ (∀ t, ∑ i, μ i t = m t) ∧
    ∀ᶠ w in Filter.cofinite, ∃ C : ι → Multiset ℂˣ, (∀ i, (π i).HasSat w (C i)) ∧ ∑ i, C i = B w

variable (a) in

abbrev Ix (T : Set (Pl E)) : Type :=
  ((E →+* ℂ) × ℂ) ⊕ (Σ w : {w : Pl E // w ∉ T}, {h : GL (Fin a) (w.1.adicCompletion E) → ℂ // h ∈ Hecke ℂ (KGL w.1 a)})

def opIx {T : Set (Pl E)} : Ix a T → Module.End ℂ (Sm E a)
  | .inl p => cap p.1 p.2
  | .inr p => hkOp (fL a p.1.1) (Final.GLintComm E p.1.1 a) p.2.2

abbrev BddS (S : Submodule ℂ (Sm E a)) : Prop := Bdd (S.map (Cm.smEq E a).toLinearMap)

variable (E a) in

def Comm : Set (Module.End ℂ (Sm E a)) :=
  {T | (∀ k, Commute T (cptRep E a k)) ∧ (∀ z ∈ (isExpLieAlgebra E a).centerU, Commute T (Cm.uTC E a z)) ∧
    ∀ φ, IsAutForm φ → IsAutForm (T φ)}

def hull (S : Submodule ℂ (Sm E a)) : Submodule ℂ (Sm E a) := Submodule.span ℂ {ψ | ∃ T ∈ Comm E a, ∃ φ ∈ S, ψ = T φ}

def capB {n : ℕ} (e : Fin a ↪ Fin n) (t : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E n) :=
  Formalism.REAL.qdet (fun i j => Eop t (e i) (e j)) (u + ((a : ℂ) - 1) / 2)

variable (a) in

def CI (m : (E →+* ℂ) → Multiset ℂ) : Submodule ℂ (Sm E a) :=
  LinearMap.range (Cm.ofCusp E a) ⊓ ⨅ (t) (u), Module.End.eigenspace (cap t u) ((m t).map (u + ·)).prod

theorem mem_CI {m : (E →+* ℂ) → Multiset ℂ} {φ : Sm E a} :
    φ ∈ CI a m ↔ IsCuspForm φ ∧ ∀ t u, cap t u φ = ((m t).map (u + ·)).prod • φ := by
  simp only [CI, Submodule.mem_inf, Cm.mem_range_ofCusp, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

end Forms

def TensEig : Prop :=
  ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ι κ : Type) (A : ι → Module.End ℂ V) (B : κ → Module.End ℂ W), (∀ i i', Commute (A i) (A i')) →
    (∀ k k', Commute (B k) (B k')) → ∀ z : V ⊗[ℂ] W, z ≠ 0 →
    ∃ (v : V) (w : W) (l : ι → ℂ) (m : κ → ℂ), v ≠ 0 ∧ w ≠ 0 ∧ (∀ i, A i v = l i • v) ∧ (∀ k, B k w = m k • w) ∧
      ∀ (σ : Type) [Fintype σ] (c : σ → ℂ) (i : σ → ι) (k : σ → κ) (e : ℂ),
        ∑ p, c p • TensorProduct.map (A (i p)) (B (k p)) z = e • z → ∑ p, c p * l (i p) * m (k p) = e

def TwoVar : Prop :=
  ∀ (X Y : Type) (M : Submodule ℂ (X → ℂ)) (N : Submodule ℂ (Y → ℂ)) (V : Submodule ℂ M) (W : Submodule ℂ N),
    FiniteDimensional ℂ V → FiniteDimensional ℂ W → ∀ (ι κ : Type) (A : ι → Module.End ℂ M) (B : κ → Module.End ℂ N),
    (∀ i, ∀ v ∈ V, A i v ∈ V) → (∀ k, ∀ w ∈ W, B k w ∈ W) → (∀ i i', ∀ v ∈ V, A i (A i' v) = A i' (A i v)) →
    (∀ k k', ∀ w ∈ W, B k (B k' w) = B k' (B k w)) → ∀ F : X → Y → ℂ, (∃ x y, F x y ≠ 0) →
    (∀ y, ∃ f ∈ V, f.1 = fun x => F x y) → (∀ x, ∃ f ∈ W, f.1 = F x) →
    ∃ v ∈ V, ∃ w ∈ W, ∃ (l : ι → ℂ) (m : κ → ℂ), v ≠ 0 ∧ w ≠ 0 ∧ (∀ i, A i v = l i • v) ∧ (∀ k, B k w = m k • w) ∧
      ∀ (σ : Type) [Fintype σ] (c : σ → ℂ) (i : σ → ι) (k : σ → κ) (G : σ → X → Y → ℂ) (e : ℂ),
        (∀ p, Act2 (A (i p)) (B (k p)) F (G p)) → (∀ x y, ∑ p, c p * G p x y = e * F x y) →
        ∑ p, c p * l (i p) * m (k p) = e

def CapArith : Prop :=
  ∀ (m m₁ m₂ : Multiset ℂ) (α β : ℂ),
    (∀ u : ℂ, (m₁.map (u + α + ·)).prod * (m₂.map (u + β + ·)).prod = (m.map (u + ·)).prod) →
    m = m₁.map (· + α) + m₂.map (· + β)

def SatArith : Prop :=
  ∀ (q r s : ℕ), q ≠ 0 → ∀ (B B₁ B₂ : Multiset ℂˣ), B.card = r + s → B₁.card = r → B₂.card = s →
    (∀ j ≤ r + s, ∑ p, coef q r s j p * satEig q r B₁ p.1 * satEig q s B₂ p.2 = satEig q (r + s) B j) →
    ∀ α β : ℂˣ, (α : ℂ) = (q : ℂ) ^ ((s : ℂ) / 2) → (β : ℂ) = (q : ℂ) ^ (-((r : ℂ) / 2)) →
      B = B₁.map (· * α) + B₂.map (· * β)

def SumInner : Prop :=
  ∀ (r s : ℕ) (R : Type) [Fintype R] (S : Finset (Fin (r + s)))
    (g : (satakePairs (sub1 S) → R) → (satakePairs (sub2 S) → R) → ℂ),
    ∑ c : satakePairs S → R, g (c ∘ pair1 S) (c ∘ pair2 S) =
      (Fintype.card R : ℂ) ^ ((sub1 S).card * (s - (sub2 S).card)) * ∑ c₁, ∑ c₂, g c₁ c₂

def MatBlock : Prop :=
  ∀ (L : Type) [Field L] (O : Subring L) (r s : ℕ) (π : L) (hπ : π ≠ 0) (S : Finset (Fin (r + s))) (c : satakePairs S → O),
    ∃ X : UPos (r + s) r → L, satakeGL O hπ S c =
      unipGL X * blk (satakeGL O hπ (sub1 S) (c ∘ pair1 S)) (satakeGL O hπ (sub2 S) (c ∘ pair2 S))

def HkSum : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ϖ : w.adicCompletion E) (hϖ : ϖ ∈ Ov E w)
    (hu : IsUnifV E w ϖ) [Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩)] (j : ℕ), j ≤ n → ∀ x ∈ fixed ρ (KGL w n),
    heckeVec ρ (KGL w n) (Tj ℂ n (Ov E w) ϖ j) x = ∑ i : SatakeIdx w hϖ (n := n) j, ρ (satakeB w hϖ hu i) x

def HkLocal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r s : ℕ) (ϖ : w.adicCompletion E) (hϖ : ϖ ∈ Ov E w)
    (hu : IsUnifV E w ϖ) [Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩)] (j : ℕ)
    (Φ : GL (Fin (r + s)) (w.adicCompletion E) → ℂ),
    (∀ (X : UPos (r + s) r → w.adicCompletion E) g, Φ (unipGL X * g) = Φ g) →
    ∑ i : SatakeIdx w hϖ (n := r + s) j, Φ (satakeB w hϖ hu i) =
      ∑ p : Fin (r + 1) × Fin (s + 1), coef (qV E w) r s j p *
        ∑ i₁ : SatakeIdx w hϖ (n := r) p.1, ∑ i₂ : SatakeIdx w hϖ (n := s) p.2,
          Φ (blk (satakeB w hϖ hu i₁) (satakeB w hϖ hu i₂))

def SatOfEig : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V), x ≠ 0 → x ∈ fixed ρ (KGL w n) →
    (∀ h ∈ Hecke ℂ (KGL w n), ∃ c : ℂ, heckeVec ρ (KGL w n) h x = c • x) → ∃ B, IsSatVecGL w ρ x B

def HeckeLocalBlock : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r s : ℕ),
    (∀ b₁ b₂, finGL E (r + s) (locGL E (r + s) w (blk b₁ b₂)) =
      blk (finGL E r (locGL E r w b₁)) (finGL E s (locGL E s w b₂))) ∧
    (∀ X : UPos (r + s) r → w.adicCompletion E, ∃ Y : UPos (r + s) r → Ad E,
      finGL E (r + s) (locGL E (r + s) w (unipGL X)) = unipGL Y) ∧
    (∀ (x : GA E r) (y : GA E s) (Y : UPos (r + s) r → Ad E), ∃ Y' : UPos (r + s) r → Ad E,
      blk x y * unipGL Y = unipGL Y' * blk x y) ∧
    ∀ k₁ ∈ KGL w r, ∀ k₂ ∈ KGL w s, blk k₁ k₂ ∈ KGL w (r + s)

def TauSat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (τ : SmIrr (GL (Fin a) (Af E))) (v : τ.V), v ≠ 0 →
    ∀ᶠ w : Pl E in Filter.cofinite, ∃ B, HasSatGL w (locOf τ.ρ w) B ∧ IsSatVecGL w (locOf τ.ρ w) v B

def LevelSplit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
    ∃ L' : Subgroup (GL (Fin a) (Af E)), IsOpen (L' : Set (GL (Fin a) (Af E))) ∧ L' ≤ L ∧ ∃ T : Set (Pl E), T.Finite ∧
      ∀ w ∉ T, (∀ k ∈ KGL w a, locGL E a w k ∈ L') ∧
        ∀ u ∈ L', ∃ k ∈ KGL w a, ∃ u' ∈ L', GeneralLinearGroup.map (pLoc E w) u' = 1 ∧ u = locGL E a w k * u'

def CapAct : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (t : E →+* ℂ) (u : ℂ),
    (∀ g, Commute (cap (a := a) t u) (rt E a g)) ∧ (∀ o : Op E a, Commute (cap t u) (act o)) ∧
      (∀ z, Commute (cap t u) (Cm.uTC E a z)) ∧ ∀ t' u', Commute (cap (a := a) t u) (cap t' u')

def CapOfEig : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), φ ≠ 0 →
    (∀ t u, ∃ c : ℂ, cap t u φ = c • φ) → ∃ m, HasCap φ m

def TypesComm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (V : Submodule ℂ (archCompact E a → ℂ)),
    FiniteDimensional ℂ V → ∀ T : Module.End ℂ (Sm E a), (∀ k, Commute T (cptRep E a k)) → ∀ φ : Sm E a,
    (∀ g, (fun k : archCompact E a => φ.1 (g * infEmb E a k.1)) ∈ V) →
    ∀ g, (fun k : archCompact E a => (T φ).1 (g * infEmb E a k.1)) ∈ V

def HullBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Submodule ℂ (Sm E a)), BddS S →
    ∀ L : Subgroup (GL (Fin a) (Af E)), IsOpen (L : Set (GL (Fin a) (Af E))) → BddS (hull S ⊓ fixed (finRep E a) L)

def HullOps : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Submodule ℂ (Sm E a)),
    S ≤ hull S ∧ (∀ t u, ∀ φ ∈ hull S, cap t u φ ∈ hull S) ∧ ∀ g, ∀ φ ∈ hull S, finRep E a g φ ∈ hull S

def StabSp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Submodule ℂ (Sm E a)), BddS S →
    ∃ T : Set (Pl E), T.Finite ∧ ∃ V : Submodule ℂ (Sm E a), S ≤ V ∧ FiniteDimensional ℂ V ∧ (∀ φ ∈ V, IsAutForm φ) ∧
      (∀ w ∉ T, V ≤ fixed (fL a w) (KGL w a)) ∧ ∀ i : Ix a T, ∀ φ ∈ V, opIx i φ ∈ V

def OpComm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (T : Set (Pl E)) (i i' : Ix a T) (φ : Sm E a),
    (∀ w ∉ T, φ ∈ fixed (fL a w) (KGL w a)) → opIx i (opIx i' φ) = opIx i' (opIx i φ)

def SingleBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ →
    BddS (Submodule.span ℂ {φ})

def SliceBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (φ : Sm E (r + s)), IsAutForm φ →
    ∃ (S₁ : Submodule ℂ (Sm E r)) (S₂ : Submodule ℂ (Sm E s)), BddS S₁ ∧ BddS S₂ ∧
      (∀ y, ∃ f ∈ S₁, f.1 = fun x => res (constantTerm r φ.1) x y) ∧ ∀ x, ∃ f ∈ S₂, f.1 = res (constantTerm r φ.1) x

def RtK : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (m) (B), Eig φ m B →
    ∀ k ∈ GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a), Eig (rt E a k φ) m B

def Iwa : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (φ : Sm E (r + s)) (m) (B), Eig φ m B →
    (∃ g, constantTerm r φ.1 g ≠ 0) → ∃ φ' : Sm E (r + s), Eig φ' m B ∧ ∃ x y, res (constantTerm r φ'.1) x y ≠ 0

def CtCap : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n r : ℕ) (φ : Sm E n), IsAutForm φ →
    ∃ ψ : Sm E n, ψ.1 = constantTerm r φ.1 ∧ NI r ψ.1 ∧ ∀ t u, (cap t u ψ).1 = constantTerm r (cap t u φ).1

def CtSat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n r : ℕ) (φ ψ : Sm E n), IsAutForm φ →
    ψ.1 = constantTerm r φ.1 → ψ ≠ 0 → ∀ w B, IsSatVecGL w (fL n w) φ B → IsSatVecGL w (fL n w) ψ B

def Slice : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a n : ℕ) (e : Fin a ↪ Fin n) (g : GA E n),
    ∃ f : Sm E n →ₗ[ℂ] Sm E a, (∀ ψ x, (f ψ).1 x = ψ.1 (g * emb e x)) ∧
      ∀ t i j ψ, f (Eop t (e i) (e j) ψ) = Eop t i j (f ψ)

def CapBlock : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (ψ : Sm E (r + s)), NI r ψ.1 → ∀ t u x y,
    res (cap t u ψ).1 x y = res (capB (e2 r s) t (u + (r : ℂ) / 2) (capB (e1 r s) t (u - (s : ℂ) / 2) ψ)).1 x y

def CapRel : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (ψ : Sm E (r + s)), NI r ψ.1 → ∀ t u,
    Act2 (cap (a := r) t (u - (s : ℂ) / 2)) (cap (a := s) t (u + (r : ℂ) / 2)) (res ψ.1) (res (cap t u ψ).1)

def HkRel : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (ψ : Sm E (r + s)), NI r ψ.1 →
    ∀ w : Pl E, ψ ∈ fixed (fL (r + s) w) (KGL w (r + s)) → ∀ (ϖ : w.adicCompletion E) (hu : IsUnifV E w ϖ), ∀ j ≤ r + s,
    ∃ G : Fin (r + 1) × Fin (s + 1) → GA E r → GA E s → ℂ,
      (∀ p, Act2 (tOp r w hu p.1) (tOp s w hu p.2) (res ψ.1) (G p)) ∧
      ∀ x y, ∑ p, coef (qV E w) r s j p * G p x y = res (tOp (r + s) w hu j ψ).1 x y

def PairEig : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (F : GA E r → GA E s → ℂ)
    (S₁ : Submodule ℂ (Sm E r)) (S₂ : Submodule ℂ (Sm E s)), BddS S₁ → BddS S₂ → (∃ x y, F x y ≠ 0) →
    (∀ y, ∃ f ∈ S₁, f.1 = fun x => F x y) → (∀ x, ∃ f ∈ S₂, f.1 = F x) →
    ∃ (φ₁ : Sm E r) (φ₂ : Sm E s) (m₁ m₂ : (E →+* ℂ) → Multiset ℂ) (B₁ B₂ : Pl E → Multiset ℂˣ),
      Eig φ₁ m₁ B₁ ∧ Eig φ₂ m₂ B₂ ∧
      (∀ t u v G (e : ℂ), Act2 (cap (a := r) t u) (cap (a := s) t v) F G → (∀ x y, G x y = e * F x y) →
        ((m₁ t).map (u + ·)).prod * ((m₂ t).map (v + ·)).prod = e) ∧
      ∀ᶠ w in Filter.cofinite, ∀ (ϖ : HeightOneSpectrum.adicCompletion E w) (hu : IsUnifV E w ϖ)
        (c : Fin (r + 1) × Fin (s + 1) → ℂ) (G : Fin (r + 1) × Fin (s + 1) → GA E r → GA E s → ℂ) (e : ℂ),
        (∀ p, Act2 (tOp r w hu p.1) (tOp s w hu p.2) F (G p)) → (∀ x y, ∑ p, c p * G p x y = e * F x y) →
        ∑ p, c p * satEig (qV E w) r (B₁ w) p.1 * satEig (qV E w) s (B₂ w) p.2 = e

def Step : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (φ : Sm E (r + s)) (m) (B), Eig φ m B →
    (∃ g, constantTerm r φ.1 g ≠ 0) →
    ∃ (φ₁ : Sm E r) (φ₂ : Sm E s) (m₁ m₂ : (E →+* ℂ) → Multiset ℂ) (B₁ B₂ : Pl E → Multiset ℂˣ),
      Eig φ₁ m₁ B₁ ∧ Eig φ₂ m₂ B₂ ∧
      (∀ t, m t = (m₁ t).map (· + ((-((s : ℝ) / 2) : ℝ) : ℂ)) + (m₂ t).map (· + (((r : ℝ) / 2 : ℝ) : ℂ))) ∧
      ∀ ν ν' : HChar E, ν.IsAbsPow (-((s : ℝ) / 2)) → ν'.IsAbsPow ((r : ℝ) / 2) →
        ∀ᶠ w in Filter.cofinite, B w = (B₁ w).map (· * ν.val w) + (B₂ w).map (· * ν'.val w)

def CiBasic : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (m : (E →+* ℂ) → Multiset ℂ),
    IsStable (CI a m) ∧ ∃ c : ℂ, ∀ φ ∈ CI a m, lie E a (oneL E a) φ = c • φ

def CiCompl : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (m : (E →+* ℂ) → Multiset ℂ),
    ∀ U ≤ CI a m, IsStable U → ∃ D ≤ CI a m, IsStable D ∧ U ⊓ D = ⊥ ∧ U ⊔ D = CI a m

def CuspProj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (m : (E →+* ℂ) → Multiset ℂ),
    (∀ t, Multiset.card (m t) = a) → ∀ φ : CI a m, φ ≠ 0 →
    ∃ π : CuspSub E a, (∀ t, π.HasInfChar t (m t)) ∧ ∃ p : CI a m →ₗ[ℂ] π.V, p φ ≠ 0 ∧
      ∀ g (x y : CI a m), y.1 = finRep E a g x.1 → p y = π.finPart g (p x)

def SuppCusp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (φ : Sm E a) (m) (B), Eig φ m B →
    IsCuspForm φ → Supp E a 1 m B

def SuppTwist : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a k : ℕ) (m) (B), Supp E a k m B →
    ∀ (x : ℝ) (ν : HChar E), ν.IsAbsPow x → Supp E a k (fun t => (m t).map (· + (x : ℂ))) fun w => (B w).map (· * ν.val w)

def SuppAdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s k l : ℕ) (m₁ m₂) (B₁ B₂), Supp E r k m₁ B₁ →
    Supp E s l m₂ B₂ → Supp E (r + s) (k + l) (fun t => m₁ t + m₂ t) fun w => B₁ w + B₂ w

end UpperTheory.V.Cj.S
