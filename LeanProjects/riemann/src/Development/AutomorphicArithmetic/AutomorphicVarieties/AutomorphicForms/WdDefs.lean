import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp

namespace UpperTheory.V.Af.Wd

def IsTri {k W ι : Type} [Field k] [AddCommGroup W] [Module k W] {n : ℕ} (T : ι → End k W) (d : ι → Fin n → k) : Prop :=
  ∃ b : Basis (Fin n) k W, ∀ a, (∀ i j, j < i → LinearMap.toMatrix b b (T a) i j = 0) ∧
    ∀ i, LinearMap.toMatrix b b (T a) i i = d a i

def ops {Γ R : Type} (N : R) (ρ : Γ → R) : Option Γ → R := fun a => a.elim N ρ

@[simp] theorem ops_none {Γ R : Type} (N : R) (ρ : Γ → R) : ops N ρ none = N := rfl

@[simp] theorem ops_some {Γ R : Type} (N : R) (ρ : Γ → R) (a : Γ) : ops N ρ (some a) = ρ a := rfl

def cycL {l : ℕ} [Fact l.Prime] (L : FinExt l) : GQ l →* (↥L.1)ˣ :=
  (Units.map (algebraMap ℚ_[l] ↥L.1 : ℚ_[l] →* ↥L.1)).comp (Loc.PP l).χQ

def FrobPow {l : ℕ} [Fact l.Prime] (g : GQ l) (k : ℕ) : Prop :=
  ∀ c : ↥(MaximalUnramifiedExtension l), g (c : Om l) = (((frobUr l ^ k) c : ↥(MaximalUnramifiedExtension l)) : Om l)

example : IsTri (fun _ : Unit => (1 : End ℚ (Fin 2 → ℚ))) (fun _ (_ : Fin 2) => 1) :=
  ⟨Pi.basisFun ℚ _, fun _ => ⟨fun i j h => by simp [Matrix.one_apply, h.ne'], fun i => by simp⟩⟩

example {l : ℕ} [Fact l.Prime] : FrobPow (1 : GQ l) 0 := fun _ => rfl

def TriSnoc : Prop :=
  ∀ (k W' W W'' ι : Type) [Field k] [AddCommGroup W'] [Module k W'] [AddCommGroup W] [Module k W] [AddCommGroup W'']
    [Module k W''] (n : ℕ) (T' : ι → End k W') (T : ι → End k W) (T'' : ι → End k W'') (f : W' →ₗ[k] W) (p : W →ₗ[k] W''),
    Function.Injective f → Function.Surjective p → Function.Exact f p → finrank k W'' = 1 →
    (∀ a x, f (T' a x) = T a (f x)) → (∀ a x, p (T a x) = T'' a (p x)) → ∀ d : ι → Fin (n + 1) → k,
    IsTri T' (fun a i => d a (Fin.castSucc i)) → (∀ a y, T'' a y = d a (Fin.last n) • y) → IsTri T d

def TriInit : Prop :=
  ∀ (k W ι : Type) [Field k] [AddCommGroup W] [Module k W] (n : ℕ) (T : ι → End k W) (d : ι → Fin (n + 1) → k), IsTri T d →
    ∃ (S : Submodule k W) (hS : ∀ a, ∀ x ∈ S, T a x ∈ S) (p : W →ₗ[k] k), Function.Surjective p ∧ LinearMap.ker p = S ∧
      (∀ a x, p (T a x) = d a (Fin.last n) * p x) ∧ IsTri (fun a => (T a).restrict (hS a)) (fun a i => d a (Fin.castSucc i))

def TriMono : Prop :=
  ∀ (k W Γ : Type) [Field k] [AddCommGroup W] [Module k W] (n : ℕ) (N : End k W) (ρ : Γ → End k W) (c : Γ → k)
    (μ : Γ → Fin n → k), (∀ σ, ρ σ * N = c σ • (N * ρ σ)) → IsTri (ops N ρ) (ops 0 μ) → N ≠ 0 →
    ∃ i j, ∀ σ, μ σ i = c σ * μ σ j

def TriDiag : Prop :=
  ∀ (W I : Type) [AddCommGroup W] [Module ℂ W] [Group I] (n : ℕ) (ρ : I →* End ℂ W) (d : I → Fin n → ℂ),
    (Set.range ρ).Finite → IsTri (fun s => ρ s) d →
    ∃ b : Basis (Fin n) ℂ W, ∀ s, LinearMap.toMatrix b b (ρ s) = Matrix.diagonal (d s)

def LetterExact : Prop :=
  ∀ (LL U D' D D'' F : Type) [Field LL] [Field U] [AddCommGroup D'] [Module LL D'] [AddCommGroup D] [Module LL D]
    [AddCommGroup D''] [Module LL D''] [Field F] [Algebra LL F] (m' : U →+* End LL D') (m : U →+* End LL D)
    (m'' : U →+* End LL D'') (τ : U →+* F) (T : D' →ₗ[LL] D) (S : D →ₗ[LL] D'') (hT : ∀ c, T ∘ₗ m' c = m c ∘ₗ T)
    (hS : ∀ c, S ∘ₗ m c = m'' c ∘ₗ S), Function.Exact T S → Function.Surjective S →
    Function.Exact (letterLin m' m F τ T hT) (letterLin m m'' F τ S hS) ∧ Function.Surjective (letterLin m m'' F τ S hS)

def DLeft : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) (V' V V'' : Type)
    [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
    [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    [AddCommGroup V''] [Module ↥L.1 V''] [Module ℚ_[l] V''] [IsScalarTower ℚ_[l] ↥L.1 V'']
    (ρ' : Representation ↥L.1 ↥(GK K) V') (ρ : Representation ↥L.1 ↥(GK K) V) (ρ'' : Representation ↥L.1 ↥(GK K) V'')
    (f : V' →ₗ[↥L.1] V) (p : V →ₗ[↥L.1] V'') (hf : ∀ g v, f (ρ' g v) = ρ g (f v)) (hp : ∀ g v, p (ρ g v) = ρ'' g (p v)),
    Function.Injective f → Function.Exact f p →
    Function.Injective (dmap P hf) ∧ Function.Exact (dmap P hf) (dmap P hp)

def DRight : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (V' V V'' : Type)
    [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
    [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V]
    [AddCommGroup V''] [Module ↥L.1 V''] [Module ℚ_[l] V''] [IsScalarTower ℚ_[l] ↥L.1 V'']
    (ρ' : Representation ↥L.1 ↥(GK K) V') (ρ : Representation ↥L.1 ↥(GK K) V) (ρ'' : Representation ↥L.1 ↥(GK K) V'')
    (f : V' →ₗ[↥L.1] V) (p : V →ₗ[↥L.1] V'') (_ : ∀ g v, f (ρ' g v) = ρ g (f v)) (hp : ∀ g v, p (ρ g v) = ρ'' g (p v)),
    Function.Injective f → Function.Surjective p → Function.Exact f p → IsPst (Loc.PP l) ρ →
    IsPst (Loc.PP l) ρ' ∧ IsPst (Loc.PP l) ρ'' ∧ Function.Surjective (dmap (Loc.PP l) hp)

def WdExact : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ) (K L : FinExt l) (V' V V'' : Type)
    [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
    [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V]
    [AddCommGroup V''] [Module ↥L.1 V''] [Module ℚ_[l] V''] [IsScalarTower ℚ_[l] ↥L.1 V'']
    (ρ' : Representation ↥L.1 ↥(GK K) V') (ρ : Representation ↥L.1 ↥(GK K) V) (ρ'' : Representation ↥L.1 ↥(GK K) V'')
    (f : V' →ₗ[↥L.1] V) (p : V →ₗ[↥L.1] V'') (hf : ∀ g v, f (ρ' g v) = ρ g (f v)) (hp : ∀ g v, p (ρ g v) = ρ'' g (p v)),
    Function.Injective f → Function.Surjective p → Function.Exact f p → IsPst (Loc.PP l) ρ →
    IsPst (Loc.PP l) ρ' ∧ IsPst (Loc.PP l) ρ'' ∧ Function.Injective (wdLin (Loc.PP l) ι hf) ∧
      Function.Surjective (wdLin (Loc.PP l) ι hp) ∧ Function.Exact (wdLin (Loc.PP l) ι hf) (wdLin (Loc.PP l) ι hp)

def WdTri : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Om l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (L : FinExt l) (n : ℕ) (V : Type) [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) (κ : Fin n → ↥(GK Bw.Kw) →* (↥L.1)ˣ)
    (μ : ↥(Weil h) → Fin n → ℂ), IsTri (fun g => ρ g) (fun g i => (κ i g : ↥L.1)) →
    (∀ i (hi : IsPst (Loc.PP l) (Loc.chRep (κ i))) σ y,
      haveI := hi.finite; wdRho (Loc.PP l) ι Bw h hj (Loc.chRep (κ i)) σ y = μ σ i • y) →
    ∀ hV : IsPst (Loc.PP l) ρ,
      haveI := hV.finite; IsTri (ops (wdN (Loc.PP l) ι ρ) fun σ => wdRho (Loc.PP l) ι Bw h hj ρ σ) (ops 0 μ)

def Line : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (ι : Om l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (L : FinExt l) (V : Type) [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V), finrank ↥L.1 V = 1 → ∀ (hV : IsPst P ρ)
    (x : ↥(Dpst P ρ)), x ≠ 0 → ∀ c : ↥L.1, c ≠ 0 → (phiD P ρ ^ resDeg l w) x = c • x →
    ∀ (σ : ↥(Weil h)) (s : ↥L.1), actD P ρ (weilToGK Bw h σ) x = s • x → ∀ y,
      haveI := hV.finite; wdRho P ι Bw h hj ρ σ y = ι ((c ^ (-deg σ) * s : ↥L.1) : Om l) • y

def TiltFrob : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (y : OCb l) (m : ℕ), 0 < m → y ^ l ^ m = y → ∀ (g : GQ l) (k : ℕ), FrobPow g k →
    (Loc.AIP l).actT g y = y ^ l ^ k

def WittPer : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (r : ℕ) (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ℤ_[l]), Continuous M →
    (∀ g : ↥(GK K), (g : GQ l) ∈ Loc.Iq l → M g = 1) → ∃ W : Matrix (Fin r) (Fin r) (Loc.Bcr l), IsUnit W.det ∧
      (∀ g, (M g).map (fun z => algebraMap ℚ_[l] (Loc.Bcr l) (z : ℚ_[l])) * W.map ((Loc.PP l).actQ (g : GQ l)) = W) ∧
      ∀ (g : ↥(GK K)) (k : ℕ), FrobPow (g : GQ l) k →
        (M g).map (fun z => algebraMap ℚ_[l] (Loc.Bcr l) (z : ℚ_[l])) * W.map ((Loc.PP l).φB ^ k) = W

def IntBasis : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (V : Type) [AddCommGroup V]
    [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    (ρ : Representation ℚ_[l] Γ V), (∀ x, Continuous fun g => ρ g x) →
    ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] V) (M : Γ →* Matrix (Fin n) (Fin n) ℤ_[l]), Continuous M ∧
      ∀ g i j, ((M g i j : ℤ_[l]) : ℚ_[l]) = e.repr (ρ g (e j)) i

def UnrPer : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (η : ↥(GK K) →* (↥L.1)ˣ), Continuous (fun g => ((η g : ↥L.1) : Om l)) →
    (∀ g : ↥(GK K), (g : GQ l) ∈ Loc.Iq l → η g = 1) → ∃ u : ↥L.1 ⊗[ℚ_[l]] Bst (Loc.PP l), u ≠ 0 ∧
      (∀ g, stRep (Loc.PP l) (Loc.chRep η) g u = u) ∧
      ∀ (g : ↥(GK K)) (k : ℕ), FrobPow (g : GQ l) k → (η g : ↥L.1) • (phiV (Loc.PP l) ↥L.1 ↥L.1 ^ k) u = u

def TwistPer : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (κ χ η : ↥(GK K) →* (↥L.1)ˣ) (m : ℤ),
    (∀ g, κ g = cycL L (g : GQ l) ^ m * χ g * η g) → Continuous (fun g => ((η g : ↥L.1) : Om l)) →
    (∀ g : ↥(GK K), (g : GQ l) ∈ Loc.Iq l → η g = 1) → ∃ y : ↥L.1 ⊗[ℚ_[l]] Bst (Loc.PP l), y ≠ 0 ∧
      (∀ g, stRep (Loc.PP l) (Loc.chRep κ) g y = (χ g : ↥L.1) • y) ∧
      ∀ (g : ↥(GK K)) (k : ℕ), FrobPow (g : GQ l) k →
        ((η g : ↥L.1) * (l : ↥L.1) ^ (m * k)) • (phiV (Loc.PP l) ↥L.1 ↥L.1 ^ k) y = y

def BrFacts : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw →
    FrobPow (weilToGK Bw h (frob h) : GQ l) (resDeg l w) ∧
    (∀ (L : FinExt l) (s : ↥(Dec (F := F) A)), ((cycL L (Bw.e s : GQ l) : ↥L.1) : Om l) = (cycBar F Ω l s : Qbar l)) ∧
    ∀ M : ℕ, 1 ≤ M → ∃ K' : FinExt l, ∀ s : ↥(Dec (F := F) A), (Bw.e s : GQ l) ∈ GK K' →
      ∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ

def CharWD : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Om l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (L : FinExt l) (κ χ : ↥(GK Bw.Kw) →* (↥L.1)ˣ) (m : ℤ), Continuous (fun g => ((κ g : ↥L.1) : Om l)) →
    (∃ K' : FinExt l, ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ GK K' → χ g = 1) →
    (∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ Loc.Iq l → κ g = cycL L (g : GQ l) ^ m * χ g) →
    ∀ (hκ : IsPst (Loc.PP l) (Loc.chRep κ)) (σ : ↥(Weil h)) y,
      haveI := hκ.finite
      wdRho (Loc.PP l) ι Bw h hj (Loc.chRep κ) σ y = (((normV w : ℕ) : ℂ) ^ (m * deg σ) *
        ι (((κ (weilToGK Bw h σ) * cycL L (weilToGK Bw h σ : GQ l) ^ (-m) : (↥L.1)ˣ) : ↥L.1) : Om l)) • y

def WeilDense : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    DenseRange (Subgroup.inclusion (Weil_le_Dec h))

def CharEnd : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), w ∈ placesOver F l →
    ∀ (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (a : ℤ), Continuous (fun s => (ψ s : Qbar l)) →
    (∀ σ : ↥(Weil h), ι (ψ (Subgroup.inclusion (Weil_le_Dec h) σ) : Qbar l) = ((normV w : ℕ) : ℂ) ^ (a * deg σ)) →
    a = 0 ∧ ψ = 1

def FinVal : Prop :=
  ∀ (F Ω C : Type) [Field F] [Field Ω] [Algebra F Ω] [Group C] (M : ℕ), 1 ≤ M → ∀ χ : G F Ω →* C, KillsMu M χ →
    (Set.range χ).Finite

def Model : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l))
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ) (χ : Fin n → G F Ω →* (Qbar l)ˣ), (∀ i, (Set.range (χ i)).Finite) →
    IsFlagOn r (Dec (F := F) A) κ → IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
    ∃ (L : FinExt l) (ρ : Representation ↥L.1 ↥(GK Bw.Kw) (Fin n → ↥L.1)) (κL χL : Fin n → ↥(GK Bw.Kw) →* (↥L.1)ˣ),
      IsPst (Loc.PP l) ρ ∧ wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype) = wdPst (Loc.PP l) ι Bw h hj ρ ∧
      IsTri (fun g => ρ g) (fun g i => (κL i g : ↥L.1)) ∧
      (∀ i s, ((κL i (Bw.e s) : ↥L.1) : Om l) = (κ i s : Qbar l)) ∧
      ∀ i (s : ↥(Dec (F := F) A)), ((χL i (Bw.e s) : ↥L.1) : Om l) = (χ i s : Qbar l)

end UpperTheory.V.Af.Wd
