import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

namespace Formalism.MainNotions.DeltaInvariantLattices

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations PowerSeries Module TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Coh

variable (PD) (H : Subgroup G) (T : LocLat G Qp LL O)

def BlochKatoCocyclesSubgroup : Submodule LL (H → T.V) where
  carrier := {c | c ∈ continuousCocycles (T.ρ.comp H.subtype) ∧
    ∃ x : T.V ⊗[Qp] B, ∀ g : H, c g ⊗ₜ[Qp] (1 : B) = actVB PD T.ρ g x - x}
  zero_mem' := ⟨(continuousCocycles _).zero_mem, 0, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, x, hx⟩ ⟨hb, y, hy⟩
    refine ⟨(continuousCocycles _).add_mem ha hb, x + y, fun g => ?_⟩
    simp only [Pi.add_apply, TensorProduct.add_tmul, hx, hy, map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, x, hx⟩
    refine ⟨(continuousCocycles _).smul_mem c ha, c • x, fun g => ?_⟩
    simp only [Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

def H1fSubmodule : Submodule O (LatticeCohomology (resLat T H)) :=
  ((latticeCocycles (resLat T H) ⊓ (BlochKatoCocyclesSubgroup PD H T).restrictScalars O).comap
    (latticeCocycles (resLat T H)).subtype).map (Submodule.mkQ _)

def resFun : (G → T.V) →ₗ[O] (H → T.V) := LinearMap.funLeft O T.V (Subtype.val : H → G)

theorem resFun_Z1T (c : G → T.V) (hc : c ∈ latticeCocycles T.L) : resFun H T c ∈ latticeCocycles (resLat T H) := by
  obtain ⟨⟨hcont, hcoc⟩, hmem⟩ := hc
  refine ⟨⟨hcont.comp continuous_subtype_val, fun g h => hcoc g h⟩, ?_⟩
  intro g _
  exact hmem g (Set.mem_univ _)

theorem resFun_B1T (c : G → T.V) (hc : c ∈ latticeCoboundaries T.L) : resFun H T c ∈ latticeCoboundaries (resLat T H) := by
  obtain ⟨x, hx, rfl⟩ := hc
  exact ⟨x, hx, by ext h; rfl⟩

def res : LatticeCohomology T.L →ₗ[O] LatticeCohomology (resLat T H) :=
  Submodule.mapQ _ _
    (((resFun H T).comp (latticeCocycles T.L).subtype).codRestrict (latticeCocycles (resLat T H))
      (fun c => resFun_Z1T H T c c.2))
    (by
      intro c hc
      simp only [Submodule.mem_comap, Submodule.subtype_apply] at hc ⊢
      exact resFun_B1T H T c hc)

end Coh

variable (W : LocWach PD LL O v n)

def OverLetter (τ : K →ₐ[Qp] LL) (i : ZMod n) : Prop :=
  τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i

def JumpsLet (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) : Prop :=
  ∀ τ : K →ₐ[Qp] LL, ∀ i, (OverLetter W) τ i → JumpsInV PD T.ρ τ (Set.Icc (-(M i : ℤ)) (h i))

def mx (M : ZMod n → ℕ) : ℕ := ⨆ i, M i

def smulA (T : LocLat G Qp LL O) (a : LetA O n) : W.DD T →ₗ[LetA O n] W.DD T :=
  a • LinearMap.id

def aN (T : LocLat G Qp LL O) (a : LetA O n) : Submodule (LetA O n) (W.DD T) :=
  (W.N T).map ((smulA W) T a)

def invN (T : LocLat G Qp LL O) (a : LetA O n) : Submodule (LetA O n) (W.DD T) :=
  (W.N T).comap ((smulA W) T a)

def mapA {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) : W.DD T →ₗ[LetA O n] W.DD T' :=
  (W.map f).restrictScalars (LetA O n)

def φspan (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) :
    Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (W.φD T '' (S : Set (W.DD T)))

def FreeLetter (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) (i : ZMod n) : Prop :=
  ∃ (r : ℕ) (b : Fin r → W.DD T), (∀ j, b j ∈ S) ∧
    ∀ x ∈ S, ∃! a : Fin r → PowerSeries O, x = ∑ j, (Pi.single i (a j) : LetA O n) • b j

def FreeA (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) : Prop :=
  ∃ (r : ℕ) (b : Fin r → W.DD T), (∀ j, b j ∈ S) ∧
    ∀ x ∈ S, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j

def IsTensLat (T T' T'' : LocLat G Qp LL O) (b : T.V →ₗ[LL] T'.V →ₗ[LL] T''.V) : Prop :=
  Function.Bijective (TensorProduct.lift b) ∧
    (∀ g x y, T''.ρ g (b x y) = b (T.ρ g x) (T'.ρ g y)) ∧
    T''.L.T = Submodule.span O {z | ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = b x y}

def χL : G →* LLˣ := (Units.map (algebraMap Qp LL : Qp →* LL)).comp PD.χ

def XjN (T : LocLat G Qp LL O) (j : ℤ) : Submodule (LetA O n) (W.DD T) :=
  if 0 ≤ j then (invN W) T (W.X ^ j.toNat) else (aN W) T (W.X ^ (-j).toNat)

def wachFree (T : LocLat G Qp LL O) : Prop :=
  W.N T = ⨆ i, W.Nl T i ∧ ∀ i, (FreeLetter W) T (W.Nl T i) i

def wachDual (T T' : LocLat G Qp LL O) (P : T.V →ₗ[LL] T'.V →ₗ[LL] LL) : Prop :=
  IsDualLat T.L T'.L P →
    ∃ β : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.EE, Function.Bijective β.flip ∧
      (∀ x y, β (W.φD T x) (W.φD T' y) = W.φE (β x y)) ∧
      (∀ g x y, β (W.γD T g x) (W.γD T' g y) = W.γE g (β x y)) ∧
      ∀ y, y ∈ W.N T' ↔ ∀ x ∈ W.N T, β x y ∈ Set.range (algebraMap (LetA O n) W.EE)

def wachTensor (T T' T'' : LocLat G Qp LL O) (b : T.V →ₗ[LL] T'.V →ₗ[LL] T''.V) : Prop :=
  IsTensLat T T' T'' b →
    ∃ β : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.DD T'', Function.Bijective (TensorProduct.lift β) ∧
      (∀ x y, β (W.φD T x) (W.φD T' y) = W.φD T'' (β x y)) ∧
      (∀ g x y, β (W.γD T g x) (W.γD T' g y) = W.γD T'' g (β x y)) ∧
      W.N T'' = Submodule.span (LetA O n) {w | ∃ x ∈ W.N T, ∃ y ∈ W.N T', w = β x y}

def p2 (T : LocLat G Qp LL O) : Prop :=
  (∀ g, ∀ x ∈ W.N T, W.γD T g x ∈ W.N T) ∧
    (∀ g, ∀ x ∈ W.N T, W.γD T g x - x ∈ (aN W) T letπ) ∧
    (∀ x ∈ W.N T, W.γ T x - x ∈ (aN W) T W.X)

def p3 (T : LocLat G Qp LL O) : Prop :=
  (∀ x : ↥(W.N T), W.cmp T x = 0 → (x : W.DD T) ∈ (aN W) T letπ) ∧
    Submodule.span LL (Set.range (W.cmp T)) = Dcris PD T.ρ ∧
    (∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T),
      W.cmp T ⟨_, hk⟩ = ((PD.p : LL) ^ k) • φVB PD (LL := LL) (V := T.V) (W.cmp T x))

def QRoot (i : ZMod n) (ζ : LL) : Prop :=
  (∃ c : O, algebraMap O LL c = ζ) ∧ (∃ m : ℕ, ζ ^ (PD.p ^ m) = 1) ∧
    PowerSeries.constantCoeff (W.lev i ζ W.Q) = 0

def vanI (i : ZMod n) (ζ : LL) (k : ℕ) : Ideal (LetA O n) :=
  (Ideal.span {(PowerSeries.X : PowerSeries LL) ^ k}).comap (W.lev i ζ)

def p5 (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) : Prop :=
  (∀ i, ∀ x ∈ W.Nl T (i - 1), W.Q ^ (M i) • W.φD T x ∈ W.N T) ∧
    (∀ i, ∀ y ∈ W.Nl T i, W.Q ^ (h i) • y ∈ (φspan W) T (W.Nl T (i - 1))) ∧
    (∀ x : W.DD T, (∃ k : ℕ, W.Q ^ k • x ∈ W.N T) →
      (x ∈ W.N T ↔ ∀ i ζ, (QRoot W) i ζ → ∀ k : ℕ, W.Q ^ k • x ∈ W.N T →
        W.Q ^ k • x ∈ (vanI W) i ζ k • W.N T))

def ιDi (T : LocLat G Qp LL O) (i : ZMod n) : Submodule LL (T.V ⊗[Qp] BdR) :=
  (DcrisL PD T.ρ (W.emb i)).map (ιV PD (LL := LL) (V := T.V))

def FilC (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (a : ℤ) : Submodule LL (T.V ⊗[Qp] BdR) :=
  FildR PD T.ρ τ a ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ'

def p4 (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (T : LocLat G Qp LL O) : Prop :=
  (∀ (i : ZMod n) (ζ : LL), (∃ m : ℕ, ζ ^ (PD.p ^ m) = 1) →
    PowerSeries.constantCoeff (W.lev i ζ W.X) = 0 →
      (∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ ((letE i : LetA O n) • x) k ∈ ιDi W T i ∧
        (k < 0 → W.levN T i ζ x k = 0)) ∧
      Submodule.span LL (Set.range fun x : ↥(W.N T) => W.levN T i ζ ((letE i : LetA O n) • x) 0) =
        ιDi W T i) ∧
  (∀ (i : ZMod n) (ζ : LL) (τ : K →ₐ[Qp] LL), Pt i ζ τ →
    ((∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ),
        W.levN T i ζ ⟨_, hk⟩ j ∈ ιDi W T i ∧ (j < k → W.levN T i ζ ⟨_, hk⟩ j = 0)) ∧
      Submodule.span LL {w | ∃ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T),
        w = W.levN T i ζ ⟨_, hk⟩ k} = ιDi W T i) ∧
    (∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ ((letE i : LetA O n) • x) k ∈
      ιDi W T i ⊓ FilC (PD := PD) T τ (-k)) ∧
    ∀ (k : ℤ), ∀ w ∈ FildR PD T.ρ τ (-k), ∃ (x : ↥(W.N T)) (c : LL), c ≠ 0 ∧
      (∀ j < k, c • W.levN T i ζ ((letE i : LetA O n) • x) j ∈ FilC (PD := PD) T τ (-j + 1)) ∧
      c • W.levN T i ζ ((letE i : LetA O n) • x) k - w ∈ FilC (PD := PD) T τ (-k + 1))

def p6V {T' T : LocLat G Qp LL O} (f : LatHom T'.L T.L) : Prop :=
  Function.Bijective f.f →
    (∀ x ∈ W.N T', W.map f x = 0 → x = 0) ∧
      ∀ x ∈ W.N T, ∃ k : ℕ, ∃ y ∈ W.N T', W.map f y = ((PD.p : ℕ) : LetA O n) ^ k • x

def wachSaturated (T : LocLat G Qp LL O) : Prop :=
  ∀ x : W.DD T, (∃ k : ℕ, ((PD.p : ℕ) : LetA O n) ^ k • x ∈ W.N T) → x ∈ W.N T

abbrev cokN {T₁ T₂ : LocLat G Qp LL O} (f : LatHom T₁.L T₂.L) : Type :=
  ↥(W.N T₂) ⧸ ((W.N T₁).map ((mapA W) f)).comap (W.N T₂).subtype

def wachShortExact {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L) : Prop :=
  IsSESLat (Qp := Qp) ι π →
    (∀ x ∈ W.N T₀, W.map ι x = 0 → x = 0) ∧
    (∀ y ∈ W.N T₁, W.map π y = 0 →
      ∃ k : ℕ, ∃ x ∈ W.N T₀, W.map ι x = ((PD.p : ℕ) : LetA O n) ^ k • y) ∧
    (∀ z ∈ W.N T₂, ∃ k : ℕ, ∃ y ∈ W.N T₁, W.map π y = ((PD.p : ℕ) : LetA O n) ^ k • z) ∧
    (∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀) ∧
    Module.length O ((cokN W) π) < ⊤

def H1fIntegralCyclotomicLayer (T : LocLat G Qp LL O) : Submodule O (LatticeCohomology (resLat T W.GKs)) := H1fSubmodule PD W.GKs T

def p7 (T : LocLat G Qp LL O) : Prop :=
  ∀ (J : Multiset ℕ) (y z : W.DD T),
    (J.map fun j => (W.φA ^ j) W.Q).prod • y ∈ W.N T → z ∈ (aN W) T letπ →
      ∀ h : (y, z) ∈ W.divisibleCocycles T, W.cl T ⟨(y, z), h⟩ ∈ (H1fIntegralCyclotomicLayer W) T

def p8 (T : LocLat G Qp LL O) (M : ℕ) : Prop :=
  ∀ (Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L),
    IsSESLat (Qp := Qp) ι π → IsCrys PD Tp.ρ →
    ∀ e ∈ W.N W.one, W.φD W.one e = e → (∀ g, W.γD W.one g e = e) →
    ∀ x ∈ W.N Tp, ∀ c : O, W.map π x = c • e →
      (∃ y ∈ (invN W) T (W.Q ^ M), W.map ι y = W.φD Tp x - x) ∧
      (∃ z ∈ (aN W) T W.X, W.map ι z = W.γ Tp x - x)

def InAΔ (a : LetA O n) : Prop := a ∈ W.AΔ

def Eat (E : ZMod n → Polynomial O) (π' : LetA O n) : LetA O n :=
  fun i => Polynomial.aeval (π' i) (E i)

def wachRingRelations (e s' : ℕ) (π' : LetA O n) (E : ZMod n → Polynomial O) : Prop :=
  (InAΔ W) π' ∧
    (∀ a, (InAΔ W) a → ∃! f : ZMod n → PowerSeries O, ∀ i, a i = PowerSeries.subst (π' i) (f i)) ∧
    (∃ w : (LetA O n)ˣ, π' = (w : LetA O n) * letπ ^ s') ∧
    (∀ i, (E i).natDegree = e) ∧
    (∃ w : (LetA O n)ˣ, W.q = (w : LetA O n) * Eat E π') ∧
    (∃ w : (LetA O n)ˣ, W.φA π' = (w : LetA O n) * π' * Eat E π' ^ s') ∧
    (∃ w : (LetA O n)ˣ, W.γA W.gam π' - π' = (w : LetA O n) * π' * Eat E π') ∧
    (∃ E₀ : Polynomial K₀,
      (∀ i, (E i).map (algebraMap O LL) = E₀.map (W.emb i).toRingHom) ∧
      ∃ ϖ : K, Polynomial.aeval ϖ E₀ = 0 ∧
        ∀ τ : K →ₐ[Qp] LL, v (τ ϖ) = ((1 / (e : ℚ) : ℚ) : WithTop ℚ))

def wachModuleOverLetters (T : LocLat G Qp LL O) (π' : LetA O n) : Prop :=
  (∃ (r : ℕ) (b : Fin r → W.DD T), (∀ j, b j ∈ W.NΔ T) ∧
    (∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j) ∧
    (∀ x ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ j, (InAΔ W) (a j)) ∧ x = ∑ j, a j • b j)) ∧
  ∀ x ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γ T x - x = π' • x'

def p9 (T : LocLat G Qp LL O) : Prop :=
  W.s = 1 → PD.p ≠ 2 →
    W.DelF.card = (PD.p - 1) / finrank K₀ K ∧
    (∃ π' E, (wachRingRelations W) (finrank K₀ K) ((PD.p - 1) / finrank K₀ K) π' E ∧ (wachModuleOverLetters W) T π') ∧
    (finrank K₀ K = 1 →
      (wachRingRelations W) 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) ∧
        (wachModuleOverLetters W) T W.π₀)

def p10 (T : LocLat G Qp LL O) : Prop :=
  ∀ N₁ : Submodule (LetA O n) (W.DD T), (FreeA W) T N₁ → IsBaseChange W.EE N₁.subtype →
    (∀ x ∈ N₁, W.γ T x ∈ N₁) → (∀ x ∈ N₁, W.γ T x - x ∈ N₁.map ((smulA W) T letπ)) →
    (∀ x ∈ N₁, ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ N₁) →
    (∀ y ∈ N₁, ∃ k : ℕ, W.Q ^ k • y ∈ (φspan W) T N₁) →
    N₁ = W.N T

def wachTwistIso (T T' : LocLat G Qp LL O) (j : ℤ) : Prop :=
  IsTwist (χL (PD := PD) ^ j) T.L T'.L →
    ∃ ψ : W.DD T ≃ₗ[W.EE] W.DD T', (∀ x, ψ (W.φD T x) = W.φD T' (ψ x)) ∧
      (∀ g x, W.γD T' g (ψ x) = (((W.χΓ g) ^ j : Oˣ) : O) • ψ (W.γD T g x)) ∧
      ((XjN W) T j).map ((ψ : W.DD T →ₗ[W.EE] W.DD T').restrictScalars (LetA O n)) = W.N T'

def uU : Oˣ := W.χΓ W.gam

def Jumps (T : LocLat G Qp LL O) : Set ℤ := {a | ∃ τ : K →ₐ[Qp] LL, IsJumpV PD T.ρ τ a}

abbrev quo (T : LocLat G Qp LL O) (S₁ S₂ : Submodule (LetA O n) (W.DD T)) : Type :=
  ↥S₁ ⧸ S₂.comap S₁.subtype

def SSEig (T : LocLat G Qp LL O) (S₁ S₂ : Submodule (LetA O n) (W.DD T)) (C : Set Oˣ) : Prop :=
  Module.Free O (quo W T S₁ S₂) ∧ Module.Finite O (quo W T S₁ S₂) ∧
    ∃ F : Finset Oˣ, (F : Set Oˣ) = C ∧
      (∀ x ∈ S₁, Polynomial.aeval (W.γ T) (∏ c ∈ F, (Polynomial.X - Polynomial.C (c : O))) x ∈ S₂) ∧
      ∀ c ∈ F, ∃ x ∈ S₁, x ∉ S₂ ∧ W.γ T x - (c : O) • x ∈ S₂

def DInv (T : LocLat G Qp LL O) (x : W.DD T) : Prop := ∀ δ ∈ W.DelF, W.γD T δ x = x

def IsExp (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : W.DD T) (f : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  (∃ m : ℤ, ∀ k < m, f k = 0) ∧ ∃ (a : LetA O n) (h : a • x ∈ W.N T), W.lev i ζ a ≠ 0 ∧
    ∀ k : ℤ, W.levN T i ζ ⟨a • x, h⟩ k = ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ a) • f (k - j)

def consT (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (T : LocLat G Qp LL O) : Prop :=
  (∀ i : ℕ, ∀ x ∈ W.N T,
    W.γ T (W.X ^ i • x) - ((uU W : O) ^ i) • (W.X ^ i • x) ∈ aN W T (W.X ^ (i + 1))) ∧
  (∀ y : ℕ, 1 ≤ y → SSEig W T (invN W T (W.Q ^ y)) (W.N T)
    {c | ∃ a ∈ Jumps (PD := PD) T, ∃ j : ℕ, 1 ≤ j ∧ j ≤ y ∧ c = (uU W) ^ (-(a + j))}) ∧
  SSEig W T (W.N T) (aN W T W.Q) {c | ∃ a ∈ Jumps (PD := PD) T, c = (uU W) ^ (-a)} ∧
  (W.s = 1 → ∀ (π' : LetA O n) (E : ZMod n → Polynomial O),
    wachRingRelations W (finrank K₀ K) ((PD.p - 1) / finrank K₀ K) π' E →
    ∀ (y : ℕ) (x : W.DD T), DInv W T x → Eat E π' ^ y • x ∈ W.N T →
      ∃ x', DInv W T x' ∧ Eat E π' ^ y • x' ∈ W.N T ∧ W.γ T x - x - π' • x' ∈ W.N T) ∧
  (W.s = 1 → ∀ (π' : LetA O n) (E : ZMod n → Polynomial O),
    wachRingRelations W (finrank K₀ K) ((PD.p - 1) / finrank K₀ K) π' E →
    ∀ (i : ZMod n) (ζ : LL) (τ : K →ₐ[Qp] LL), Pt i ζ τ →
      PowerSeries.constantCoeff (W.lev i ζ π') ≠ 0 ∧
      (E i).eval₂ (algebraMap O LL) (PowerSeries.constantCoeff (W.lev i ζ π')) = 0 ∧
      (∀ m m' : ℤ, m ≠ m' → (uU W) ^ m ≠ (uU W) ^ m') ∧
      ∀ (x x' : W.DD T) (f f' : ℤ → T.V ⊗[Qp] BdR), π' • x' = W.γ T x - x →
        IsExp W T i ζ x f → IsExp W T i ζ x' f' →
        (∀ d₀ : T.V ⊗[Qp] BdR, (∀ k, f k ∈ Submodule.span LL {d₀}) →
          ∀ k, f' k ∈ Submodule.span LL {d₀}) ∧
        ∀ m : ℤ, (∀ k < m, f k = 0) → (∀ k < m, f' k = 0) ∧
          PowerSeries.constantCoeff (W.lev i ζ π') • f' m =
            (algebraMap O LL (((uU W) ^ m : Oˣ) : O) - 1) • f m) ∧
  (W.s = 1 → finrank K₀ K = 1 →
    let c : ℤ → LL := fun x => (algebraMap O LL (((uU W) ^ (-x) : Oˣ) : O) - 1) / (-(PD.p : LL))
    c 0 = 0 ∧ ∀ x y : ℤ, v (c x - c y) = v (((x - y : ℤ) : LL)))

def p2a (T : LocLat G Qp LL O) : Prop :=
  Function.Surjective (W.cl T) ∧
    ∀ w : ↥(W.divisibleCocycles T), W.cl T w = 0 ↔
      ∃ m : W.DD T, (w : W.DD T × W.DD T) = (W.φD T m - m, W.γ T m - m)

def p2aK (T : LocLat G Qp LL O) : Prop :=
  W.s = 1 → PD.p ≠ 2 →
    Function.Surjective (W.clK T) ∧
      ∀ w : ↥(W.wachCocyclesDelta T), W.clK T w = 0 ↔ ∃ m : W.DD T, DInv W T m ∧
        (w : W.DD T × W.DD T) = (W.φD T m - m, W.γD T W.gamK m - m)

def p2b (T : LocLat G Qp LL O) : Prop :=
  ∀ κ : LatticeCohomology T.L, κ ∈ latticeFiniteCohomology PD T.L ↔ res W.GKs T κ ∈ H1fIntegralCyclotomicLayer W T

def p2c (T : LocLat G Qp LL O) (M : ℕ) : Prop :=
  (∃ w : LetA O n, W.γA W.gam W.Q = w * W.Q ∧ w - 1 ∈ Ideal.span {W.X}) ∧
  ∀ (y z : W.DD T), y ∈ invN W T (W.Q ^ M) → z ∈ aN W T W.X → ∀ h : (y, z) ∈ W.divisibleCocycles T,
    W.cl T ⟨(y, z), h⟩ ∈ H1fIntegralCyclotomicLayer W T ∧
      (W.cl T ⟨(y, z), h⟩ = 0 → ∃ m ∈ W.N T, y = W.φD T m - m ∧ z = W.γ T m - m)

def p2d {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L) (M : ℕ) :
    Prop :=
  IsSESLat (Qp := Qp) ι π →
  ∀ (y₂ z₂ : W.DD T₂), y₂ ∈ invN W T₂ (W.Q ^ M) → z₂ ∈ aN W T₂ W.X → (y₂, z₂) ∈ W.divisibleCocycles T₂ →
  ∀ (y₁ z₁ : W.DD T₁), y₁ ∈ invN W T₁ (W.Q ^ M) → z₁ ∈ aN W T₁ W.X →
    W.map π y₁ = y₂ → W.map π z₁ = z₂ →
    ∃ w : W.DD T₀, W.map ι w = (W.γ T₁ y₁ - y₁) - (W.φD T₁ z₁ - z₁) ∧
      w ∈ (invN W T₀ (W.Q ^ M)).map (smulA W T₀ W.X) ∧
      ∃ k : ℕ, ∃ y₀ ∈ invN W T₀ (W.Q ^ M), ∃ z₀ ∈ aN W T₀ W.X,
        ((PD.p : ℕ) : LetA O n) ^ k • w = (W.γ T₀ y₀ - y₀) - (W.φD T₀ z₀ - z₀)

def wachLengthLatticeMap {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L) (M h : ZMod n → ℕ) : Prop :=
  π.Onto → JumpsLet W T₁ M h →
    (∀ i, ∀ y ∈ W.Nl T₂ i, W.X ^ (⨆ j, (M j + h j)) • y ∈ (W.Nl T₁ i).map (mapA W π)) ∧
    (W.s = 1 → ∀ π' : LetA O n, InAΔ W π' →
      (∃ w : (LetA O n)ˣ, π' = (w : LetA O n) * letπ ^ ((PD.p - 1) / finrank K₀ K)) →
      ∀ i, ∀ y ∈ W.Nl T₂ i, (∀ δ ∈ W.DelF, W.γD T₂ δ y - y ∈ (W.Nl T₁ i).map (mapA W π)) →
        π' ^ ⌈((finrank K₀ K * ⨆ j, (M j + h j) : ℕ) : ℚ) / ((PD.p : ℚ) - 1)⌉₊ • y ∈
          (W.Nl T₁ i).map (mapA W π))

variable (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)

def WachFreeDualTensor : Prop :=
  (∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → wachFree W T) ∧
  (∀ (T T' : LocLat G Qp LL O) (P : T.V →ₗ[LL] T'.V →ₗ[LL] LL), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    wachDual W T T' P) ∧
  (∀ (T T' T'' : LocLat G Qp LL O) (b : T.V →ₗ[LL] T'.V →ₗ[LL] T''.V),
    IsCrys PD T.ρ → IsCrys PD T'.ρ → IsCrys PD T''.ρ → wachTensor W T T' T'' b)

def P2W : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → p2 W T

def P3W : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → p3 W T

def P4W : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → p4 W Pt T

def P5W : Prop :=
  ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ → JumpsLet W T M h → p5 W T M h

def WachSaturationExactness : Prop :=
  (∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → wachSaturated W T) ∧
  (∀ (T' T : LocLat G Qp LL O) (f : LatHom T'.L T.L), IsCrys PD T'.ρ → IsCrys PD T.ρ → p6V W f) ∧
  (∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsCrys PD T₀.ρ → IsCrys PD T₁.ρ → IsCrys PD T₂.ρ → wachShortExact W ι π)

def WachCrystallineExtension : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → p7 W T

def WachMaxJumpBound : Prop :=
  ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ → JumpsLet W T M h → p8 W T (mx M)

def P9W : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → p9 W T

def WachTwistCharacterisation : Prop :=
  (∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → p10 W T) ∧
  (∀ (T T' : LocLat G Qp LL O) (j : ℤ), IsCrys PD T.ρ → IsCrys PD T'.ρ → wachTwistIso W T T' j)

def ConsW : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → consT W Pt T

def HerrComplexFirstProperty : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → p2a W T ∧ p2aK W T

def HerrComplexSecondProperty : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → p2b W T

def HerrComplexThirdProperty : Prop :=
  ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ → JumpsLet W T M h → p2c W T (mx M)

def HerrComplexFourthProperty : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L) (M h : ZMod n → ℕ),
    IsCrys PD T₀.ρ → IsCrys PD T₁.ρ → IsCrys PD T₂.ρ → JumpsLet W T₁ M h → p2d W ι π (mx M)

def WachLatticeLengthLemma : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (π : LatHom T₁.L T₂.L) (M h : ZMod n → ℕ),
    IsCrys PD T₁.ρ → IsCrys PD T₂.ρ → wachLengthLatticeMap W π M h

def WachMainTheorem : Prop :=
  WachFreeDualTensor W ∧ P2W W ∧ P3W W ∧ P4W W Pt ∧ P5W W ∧ WachSaturationExactness W ∧ WachCrystallineExtension W ∧ WachMaxJumpBound W ∧ P9W W ∧ WachTwistCharacterisation W

def Prop2W : Prop := HerrComplexFirstProperty W ∧ HerrComplexSecondProperty W ∧ HerrComplexThirdProperty W ∧ HerrComplexFourthProperty W

def ConclusionW₂ : Prop := WachMainTheorem W Pt ∧ ConsW W Pt ∧ Prop2W W ∧ WachLatticeLengthLemma W

def Adm2W (Font : LocLat G Qp LL O → Prop) : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Font T → p2a W T ∧ p2aK W T

theorem wach_gamma_stable_first (T : LocLat G Qp LL O) :
    (∀ g, ∀ x ∈ W.N T, W.γD T g x ∈ W.N T) ∧
      (∀ g, ∀ x ∈ W.N T, W.γD T g x - x ∈ (aN W) T letπ) := by
  refine ⟨fun g x hx => W.N_Γ T g x hx, fun g x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := W.N_π T g x hx
  rw [hxy]
  exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩

section Etale

variable {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
  {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
  (E : EtTie W RA RW inclR φR gR πA)

def TAinf (inclR : RA →ₐ[O] RW) (T : LocLat G Qp LL O) : Submodule O (TW RW T) :=
  LinearMap.range (TensorProduct.map inclR.toLinearMap (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T))

def NAinf (T : LocLat G Qp LL O) : Submodule O (TW RW T) :=
  Submodule.span O {z | ∃ a : RA, ∃ x ∈ W.N T, z = inclR a • E.jD T x}

def p1et (T : LocLat G Qp LL O) : Prop :=
  (∃ (r : ℕ) (b : Fin r → W.DD T), (∀ j, b j ∈ W.N T) ∧
    (∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j) ∧
    ∀ y : TW RW T, ∃! c : Fin r → RW, y = ∑ j, c j • E.jD T (b j)) ∧
  ∀ y : TW RW T, TWmap φR T y = y ↔ ∃ t : ↥T.L.T, y = (1 : RW) ⊗ₜ[O] t

def wachInfiniteLevelJumpBound (T : LocLat G Qp LL O) (M h : ℕ) : Prop :=
  (∀ z ∈ TAinf inclR T, inclR (E.io W.X) ^ h • z ∈ NAinf W E T) ∧
    ∀ z ∈ NAinf W E T, inclR (E.io W.X) ^ M • z ∈ TAinf inclR T

def wachInfiniteLevel (T : LocLat G Qp LL O) : Prop := ∃ k : ℕ, wachInfiniteLevelJumpBound W E T k k

def WachEtaleComparison : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → p1et W E T ∧ wachInfiniteLevel W E T

def WachInfiniteLevelBound : Prop :=
  ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ → JumpsLet W T M h →
    wachInfiniteLevelJumpBound W E T (mx M) (mx h)

def Adm1W : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    (W.N T).FG ∧ IsBaseChange W.EE (W.N T).subtype ∧
    (∀ g, ∀ x ∈ W.N T, W.γD T g x ∈ W.N T) ∧
    (∀ g, ∀ x ∈ W.N T, W.γD T g x - x ∈ (aN W) T letπ) ∧
    Function.Injective (E.jD T) ∧ Submodule.span RW (Set.range (E.jD T)) = ⊤ ∧
    (∀ x, E.jD T (W.φD T x) = TWmap φR T (E.jD T x)) ∧
    ∀ (g : G) x, E.jD T (W.γD T (W.resΓ g) x) = TWact (gR g) T g (E.jD T x)

theorem prismatic_comparison_holds : Adm1W W E := fun T hT =>
  ⟨W.N_fg T, W.N_base T hT, (wach_gamma_stable_first W T).1, (wach_gamma_stable_first W T).2, E.jD_inj T, E.jD_span T, E.jD_φ T,
    E.jD_act T⟩

end Etale

section Disc

def ConvD (v : AddValuation LL (WithTop ℚ)) (f : PowerSeries LL) : Prop :=
  ∀ r : ℚ, 0 < r → ∀ C : ℚ, ∃ k₀ : ℕ, ∀ k ≥ k₀,
    (C : WithTop ℚ) ≤ v (PowerSeries.coeff k f) + (((k : ℚ) * r : ℚ) : WithTop ℚ)

def AtoLL (a : LetA O n) : ZMod n → PowerSeries LL := fun i => (a i).map (algebraMap O LL)

def γPS (g : W.Gam) (f : ZMod n → PowerSeries LL) : ZMod n → PowerSeries LL :=
  fun i => PowerSeries.subst ((W.γ₀ g PowerSeries.X).map (algebraMap O LL)) (f i)

def φPS (f : ZMod n → PowerSeries LL) : ZMod n → PowerSeries LL :=
  fun i => PowerSeries.subst ((W.φ₀ PowerSeries.X).map (algebraMap O LL)) (f (i - 1))

variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]

structure RRTie {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    (E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA) (ιA : Ai →+* B) (tS : B) where
  RR : Type
  [rRR : CommRing RR]

  toPS : RR →+* (ZMod n → PowerSeries LL)
  toPS_inj : Function.Injective toPS
  toPS_range : ∀ f, f ∈ Set.range toPS ↔ ∀ i, ConvD v (f i)

  βA : (O ⊗[Zl] Ai) →+* LL ⊗[Qp] B
  βA_tmul : ∀ (a : O) (w : Ai), βA (a ⊗ₜ[Zl] w) = algebraMap O LL a ⊗ₜ[Qp] ιA w
  ioR : RR →+* LL ⊗[Qp] B
  ioR_A : ∀ (a : LetA O n) (r : RR), toPS r = AtoLL a → ioR r = βA (E.io a)
  ioR_LL : ∀ (c : LL) (r : RR), (toPS r = fun _ => PowerSeries.C c) → ioR r = c ⊗ₜ[Qp] (1 : B)
  ioR_G : ∀ (g : G) (r r' : RR), toPS r' = γPS W (W.resΓ g) (toPS r) →
    ioR r' = Algebra.TensorProduct.map (AlgHom.id Qp LL)
      ((PD.actB g).toAlgHom.restrictScalars Qp) (ioR r)
  ioR_φ : ∀ r r' : RR, toPS r' = φPS W (toPS r) →
    ioR r' = Algebra.TensorProduct.map (AlgHom.id Qp LL) PD.φ (ioR r)
  constant_coeff_zero_tie : ∀ r : RR, (∀ i, PowerSeries.constantCoeff (toPS r i) = 0 ∧
    (1 + PowerSeries.X) * PowerSeries.derivative LL (toPS r i) = 1) → ioR r = (1 : LL) ⊗ₜ[Qp] tS
  ioX_unit : ∀ j : ℕ, IsUnit (βA (E.io ((W.φA ^ j) W.X)))

end Disc

end Local

section Theory

def ptK (LT : LocTheory) (HW : HWOf LT) {l : ℕ} [Fact l.Prime] {K : FinExt l} {s : ℕ} {LL : FinExt l}
    (h : Good K s LL) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : Prop :=
  ∃ τs : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, (HW l).IsPt h i ζ τs ∧
    ∀ (x : ↥K.1) (y : ↥(Ks K s)), (y : Om l) = (x : Om l) → τ x = τs y

def p1L (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachFreeDualTensor ((HW l).W K s LL h)

def p2L (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    P2W ((HW l).W K s LL h)

def p3L (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (F : FonOf LT AI HW) (_C : CmpOf LT AI HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    P3W ((HW l).W K s LL h)

def p4L (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (F : FonOf LT AI HW) (_C : CmpOf LT AI HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    P4W ((HW l).W K s LL h) (ptK LT HW h)

def p5L (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    P5W ((HW l).W K s LL h)

def p6L (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachSaturationExactness ((HW l).W K s LL h)

def p7L (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachCrystallineExtension ((HW l).W K s LL h)

def p8L (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachMaxJumpBound ((HW l).W K s LL h)

def p9L (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    P9W ((HW l).W K s LL h)

def p10L (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachTwistCharacterisation ((HW l).W K s LL h)

def consL (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ConsW ((HW l).W K s LL h) (ptK LT HW h)

def p2aL (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    HerrComplexFirstProperty ((HW l).W K s LL h)

def p2bL (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    HerrComplexSecondProperty ((HW l).W K s LL h)

def p2cL (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    HerrComplexThirdProperty ((HW l).W K s LL h)

def p2dL (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    HerrComplexFourthProperty ((HW l).W K s LL h)

def wachLengthLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachLatticeLengthLemma ((HW l).W K s LL h)

def wachTheoremLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (F : FonOf LT AI HW) (_C : CmpOf LT AI HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachMainTheorem ((HW l).W K s LL h) (ptK LT HW h)

def prop2L (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Prop2W ((HW l).W K s LL h)

def ConclusionL (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (F : FonOf LT AI HW) (_C : CmpOf LT AI HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ConclusionW₂ ((HW l).W K s LL h) (ptK LT HW h)

variable (LT : LocTheory) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
  (HW : HWOf LT) (Et : FonOf LT AI HW)

def p1eL : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachEtaleComparison ((HW l).W K s LL h) ((Et l).E K s LL h).tie

def p5eL : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachInfiniteLevelBound ((HW l).W K s LL h) ((Et l).E K s LL h).tie

def PrismaticComparisonLocal : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Adm1W ((HW l).W K s LL h) ((Et l).E K s LL h).tie

theorem prismatic_comparison_local_holds : PrismaticComparisonLocal LT AI HW Et := fun l _ K s LL h => prismatic_comparison_holds _ _

def HerrDescriptionLocal : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Adm2W ((HW l).W K s LL h) (p1et ((HW l).W K s LL h) ((Et l).E K s LL h).tie)

end Theory

section Design

def P1 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := p1L D.loc HW D.locA F

def P2 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := p2L D.loc HW D.locA F

def P3 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : CmpOf D.loc D.locA HW F) : Prop := p3L D.loc HW D.locA F C

def P4 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : CmpOf D.loc D.locA HW F) : Prop := p4L D.loc HW D.locA F C

def P5 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := p5L D.loc HW D.locA F

def P6 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := p6L D.loc HW D.locA F

def P7 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := p7L D.loc HW D.locA F

def P8 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := p8L D.loc HW D.locA F

def P9 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := p9L D.loc HW D.locA F

def product_first_zeroth_parts (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := p10L D.loc HW D.locA F

def Pr2a (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := p2aL D.loc HW D.locA F

def Pr2b (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := p2bL D.loc HW D.locA F

def Pr2c (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := p2cL D.loc HW D.locA F

def Pr2d (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := p2dL D.loc HW D.locA F

def thm1 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : CmpOf D.loc D.locA HW F) : Prop := wachTheoremLocal D.loc HW D.locA F C

def cons (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := consL D.loc HW D.locA F

def prop2 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := prop2L D.loc HW D.locA F

def lem3 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := wachLengthLocal D.loc HW D.locA F

def adm1 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := PrismaticComparisonLocal D.loc D.locA HW F

theorem chebyshev_bounds_one_fifth (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : adm1 D HW F :=
  prismatic_comparison_local_holds D.loc D.locA HW F

def adm2 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := HerrDescriptionLocal D.loc D.locA HW F

def admitted (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := adm1 D HW F ∧ adm2 D HW F

def aux₃ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : CmpOf D.loc D.locA HW F) : Prop :=
  thm1 D HW F C ∧ cons D HW F ∧ prop2 D HW F ∧ lem3 D HW F

def ConclusionE (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  p1eL D.loc D.locA HW F ∧ p5eL D.loc D.locA HW F

structure Pend (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) where
  rr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    RRTie ((HW l).W K s LL h) ((F l).E K s LL h).tie (D.locA l).ιA
      ((((l : ℚ_[l]) ^ s)⁻¹) • (D.loc l).tB)

def Stmt (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : CmpOf D.loc D.locA HW F) : Prop :=
  admitted D HW F → aux₃ D HW F C ∧ ConclusionE D HW F

theorem wach_theorem_iff_properties (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : CmpOf D.loc D.locA HW F) : thm1 D HW F C ↔ P1 D HW F ∧ P2 D HW F ∧ P3 D HW F C ∧ P4 D HW F C ∧
    P5 D HW F ∧ P6 D HW F ∧ P7 D HW F ∧ P8 D HW F ∧ P9 D HW F ∧ product_first_zeroth_parts D HW F := by
  unfold thm1 wachTheoremLocal WachMainTheorem P1 P2 P3 P4 P5 P6 P7 P8 P9 product_first_zeroth_parts p1L p2L p3L p4L p5L p6L p7L p8L p9L p10L
  constructor
  · intro h
    exact ⟨fun l _ K s LL hg => (h l K s LL hg).1,
      fun l _ K s LL hg => (h l K s LL hg).2.1,
      fun l _ K s LL hg => (h l K s LL hg).2.2.1,
      fun l _ K s LL hg => (h l K s LL hg).2.2.2.1,
      fun l _ K s LL hg => (h l K s LL hg).2.2.2.2.1,
      fun l _ K s LL hg => (h l K s LL hg).2.2.2.2.2.1,
      fun l _ K s LL hg => (h l K s LL hg).2.2.2.2.2.2.1,
      fun l _ K s LL hg => (h l K s LL hg).2.2.2.2.2.2.2.1,
      fun l _ K s LL hg => (h l K s LL hg).2.2.2.2.2.2.2.2.1,
      fun l _ K s LL hg => (h l K s LL hg).2.2.2.2.2.2.2.2.2⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ l _ K s LL hg
    exact ⟨h1 l K s LL hg, h2 l K s LL hg, h3 l K s LL hg, h4 l K s LL hg, h5 l K s LL hg, h6 l K s LL hg, h7 l K s LL hg, h8 l K s LL hg, h9 l K s LL hg, h10 l K s LL hg⟩

theorem herr_prop_two_iff (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : prop2 D HW F ↔ Pr2a D HW F ∧ Pr2b D HW F ∧ Pr2c D HW F ∧ Pr2d D HW F := by
  unfold prop2 prop2L Prop2W Pr2a Pr2b Pr2c Pr2d p2aL p2bL p2cL p2dL
  constructor
  · intro h
    exact ⟨fun l _ K s LL hg => (h l K s LL hg).1,
      fun l _ K s LL hg => (h l K s LL hg).2.1,
      fun l _ K s LL hg => (h l K s LL hg).2.2.1,
      fun l _ K s LL hg => (h l K s LL hg).2.2.2⟩
  · rintro ⟨h1, h2, h3, h4⟩ l _ K s LL hg
    exact ⟨h1 l K s LL hg, h2 l K s LL hg, h3 l K s LL hg, h4 l K s LL hg⟩

end Design

end Formalism.MainNotions.DeltaInvariantLattices
