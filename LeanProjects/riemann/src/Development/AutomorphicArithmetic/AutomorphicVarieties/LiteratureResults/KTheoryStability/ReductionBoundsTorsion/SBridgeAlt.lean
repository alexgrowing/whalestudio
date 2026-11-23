import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB

def SChain : Prop :=
  (∀ (G : Type) [Group G] (m : ℕ) (z : Chn G (m + 2)), bd G m (bd G (m + 1) z) = 0) ∧
  (∀ (G H : Type) [Group G] [Group H] (f : G →* H) (m : ℕ) (z : Chn G (m + 1)),
    bd H m (cmap f (m + 1) z) = cmap f m (bd G m z)) ∧
  (∀ (G H K : Type) [Group G] [Group H] [Group K] (f : G →* H) (g : H →* K) (m : ℕ) (z : Chn G m),
    cmap (g.comp f) m z = cmap g m (cmap f m z)) ∧
  ∀ (G : Type) [Group G] (g : G) (m : ℕ) (z : Chn G (m + 1)), IsCyc z →
    IsBd (cmap (MulAut.conj g).toMonoidHom (m + 1) z - z)

def SEv : Prop :=
  ∀ (G H Y : Type) [Group G] [Group H] [MulAction H Y] (ρ : G →* H) (k : ℕ) (F : (Fin (k + 2) → Y) → ℝ),
    Inv ρ F → dC F = 0 → (∀ (y : Y) (z : Chn G (k + 1)), IsBd z → ev ρ F y z = 0) ∧
      ∀ (y y' : Y) (z : Chn G (k + 1)), IsCyc z → ev ρ F y z = ev ρ F y' z

def SSep : Prop :=
  ∀ (G : Type) [Group G] (k : ℕ) (z : Chn G (k + 1)), IsCyc z → ¬IsBd z →
    ∃ c : (Fin (k + 2) → G) → ℝ, Inv (MonoidHom.id G) c ∧ dC c = 0 ∧ ev (MonoidHom.id G) c 1 z ≠ 0

def SBridge : Prop :=
  ∀ k : ℕ, ∃ θ : ∀ (G : Type) [Group G], LinearMap.ker (bd G k) →ₗ[ℝ] ℝ ⊗[ℤ] grpH G (k + 1),
    (∀ (G : Type) [Group G], Function.Surjective (θ G)) ∧
    (∀ (G : Type) [Group G] (z : LinearMap.ker (bd G k)), θ G z = 0 ↔ IsBd z.1) ∧
    ∀ (G H : Type) [Group G] [Group H] (f : G →* H) (z : LinearMap.ker (bd G k)) (z' : LinearMap.ker (bd H k)),
      z'.1 = cmap f (k + 1) z.1 → θ H z' = LinearMap.baseChange ℝ (grpHMap f (k + 1)).hom (θ G z)

def SStab : Prop :=
  ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (k n n' : ℕ) (h : n ≤ n'), 2 * (k + 1) + 4 ≤ n →
    (∀ z : Chn (GL (Fin n) R) (k + 1), IsCyc z → IsBd (cmap (stab R n n' h) (k + 1) z) → IsBd z) ∧
    ∀ z' : Chn (GL (Fin n') R) (k + 1), IsCyc z' →
      ∃ z : Chn (GL (Fin n) R) (k + 1), IsCyc z ∧ IsBd (cmap (stab R n n' h) (k + 1) z - z')

def SFin : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ N k : ℕ,
    ∃ s : Finset (Chn (Gm L N) (k + 1)), (∀ z ∈ s, IsCyc z) ∧
      ∀ z : Chn (Gm L N) (k + 1), IsCyc z → ∃ z' ∈ Submodule.span ℝ (s : Set (Chn (Gm L N) (k + 1))), IsBd (z - z')

def SPsi : Prop :=
  ∀ (R : Type) [CommRing R] (d n k : ℕ) (h : n ≤ (d + 1) * n) (z : Chn (GL (Fin n) R) (k + 1)), IsCyc z → IsPrim z →
    IsBd (cmap (psi R (d + 1) n) (k + 1) z - ((d : ℝ) + 1) • cmap (stab R n ((d + 1) * n) h) (k + 1) z)

def PV (R : Type) [CommRing R] (k : ℕ) : Prop :=
  ∀ n : ℕ, 2 * (k + 1) + 4 ≤ n → ∀ z : Chn (GL (Fin n) R) (k + 1), IsCyc z → IsPrim z → IsBd z

def SBig : Prop :=
  ∀ k : ℕ, (∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → k + 1 < nrComplexPlaces L → PV (𝓞 L) k) →
    ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → PV (𝓞 L) k

def SAff : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ k : ℕ, k + 1 < nrComplexPlaces L →
    ∀ (n r : ℕ) (H : Type) [Group H] (f : H →* Gm L (n + r)) (f₀ : H →* Gm L n),
      (∀ x, ∃ B : Matrix (Fin n) (Fin r) (𝓞 L), (f x : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) =
        Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (f₀ x : Matrix (Fin n) (Fin n) (𝓞 L)) B 0 1)) →
      ∀ z : Chn H (k + 1), IsCyc z →
        IsBd (cmap f (k + 1) z - cmap ((stab (𝓞 L) n (n + r) (Nat.le_add_right n r)).comp f₀) (k + 1) z)

def SPrime : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], ∃ π : 𝓞 L, Prime π ∧ 25 ≤ Ideal.absNorm (Ideal.span {π})

def SHecke : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ k : ℕ, k + 1 < nrComplexPlaces L →
    ∀ (π : 𝓞 L) (hπ : Prime π), ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ F : (Fin (k + 2) → GK L N) → ℝ,
      Inv (toK L N) F → dC F = 0 →
      (∀ z : Chn (Gm L N) (k + 1), IsCyc z → ∃ C : ℝ, ∀ r : ℕ,
        |ev (toK L N) ((hecke (toK L N) (MonoidHom.id (GK L N)) (qel L N π hπ.ne_zero))^[r] F) 1 z| ≤
          C * (3 / 5 : ℝ) ^ r) →
      ∀ z : Chn (Gm L N) (k + 1), IsCyc z → ev (toK L N) F 1 z = 0

def SStokes : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (U : Set V), IsOpen U → Convex ℝ U →
    ∀ (q : ℕ) (ω : Form V q), ContDiffOn ℝ 1 ω U → ∀ y : Fin (q + 2) → V, (∀ j, y j ∈ U) →
      dC (intS ω) y = intS (extDeriv ω) y

def SHt : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ N : ℕ, 1 ≤ N →
    Continuous (ht : Gp L N → ℝ) ∧ (∀ γ x, ht (emb L N γ * x) = ht x) ∧ (∃ c, 0 < c ∧ ∀ x : Gp L N, c ≤ ht x) ∧
      ∀ K : Set (Gp L N), IsCompact K → ∃ C, ∀ g ∈ K, ∀ x, ht (x * g) ≤ C * ht x

def SPU : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∃ a : ℕ, ∀ N : ℕ, 1 ≤ N →
    Nonempty (PU L N fun x => ht x ^ a)

def SMom : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ A : ℕ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    ∃ d : Dom L N, IntegrableOn (fun x => ht (ofS L N x) ^ A) d.D d.μ

def SWhit : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N k : ℕ) (Ht : Gp L N → ℝ), PU L N Ht → (∀ γ x, Ht (emb L N γ * x) = Ht x) →
    (∀ x, 0 ≤ Ht x) → ∀ c : (Fin (k + 2) → Gm L N) → ℝ, Inv (MonoidHom.id (Gm L N)) c → dC c = 0 →
      ∃ ω : Form (HS L N) (k + 1), Good ω ∧ (∀ γ, FInv ω (emb L N γ)) ∧
        (∀ s : InfinitePlace L → ℂˣ, (∀ w w', ‖(s w : ℂ)‖ = ‖(s w' : ℂ)‖) → FInv ω (scal L N s)) ∧
        (∀ z : Chn (Gm L N) (k + 1), IsCyc z → ev (emb L N) (intP ω) (one L N) z = ev (MonoidHom.id (Gm L N)) c 1 z) ∧
        ∃ C, ∀ x, ‖fr ω x‖ ≤ C * Ht x ^ (k + 1)

def SCen : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N k : ℕ) (ω : Form (HS L N) (k + 1)), Good ω → (∀ γ, FInv ω (emb L N γ)) →
    (∀ s : InfinitePlace L → ℂˣ, (∀ w w', ‖(s w : ℂ)‖ = ‖(s w' : ℂ)‖) → FInv ω (scal L N s)) →
    ∀ B : Gp L N → ℝ, (∀ K : Set (Gp L N), IsCompact K → ∃ C, ∀ g ∈ K, ∀ x, B (x * g) ≤ C * B x) →
      (∀ x, ‖fr ω x‖ ≤ B x) →
      ∃ ω' : Form (HS L N) (k + 1), Good ω' ∧ (∀ γ, FInv ω' (emb L N γ)) ∧ (∀ s, FInv ω' (scal L N s)) ∧
        (∀ z : Chn (Gm L N) (k + 1), IsCyc z →
          ev (emb L N) (intP ω') (one L N) z = ev (emb L N) (intP ω) (one L N) z) ∧
        ∃ C, ∀ x, ‖fr ω' x‖ ≤ C * B x

def Lz {L : Type} [Field L] [NumberField L] {N : ℕ} (d : Dom L N) (f : Gp L N → ℝ) : Prop :=
  Continuous f ∧ (∀ γ x, f (emb L N γ * x) = f x) ∧ (∀ s x, f (scal L N s * x) = f x) ∧
    IntegrableOn (fun x => f (ofS L N x) ^ 2) d.D d.μ ∧ ∫ x in d.D, f (ofS L N x) ∂d.μ = 0

def SGap : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ (π : 𝓞 L) (hπ : Prime π),
    25 ≤ Ideal.absNorm (Ideal.span {π}) → ∀ N : ℕ, 3 ≤ N → ∀ (d : Dom L N) (f : Gp L N → ℝ), Lz d f →
      Lz d (hecke (toK L N) (toP L N) (qel L N π hπ.ne_zero) f) ∧
        ∫ x in d.D, hecke (toK L N) (toP L N) (qel L N π hπ.ne_zero) f (ofS L N x) ^ 2 ∂d.μ ≤
          (3 / 5 : ℝ) ^ 2 * ∫ x in d.D, f (ofS L N x) ^ 2 ∂d.μ

def SLoc : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N k : ℕ), 1 ≤ N → ∀ (d : Dom L N) (z : Chn (Gm L N) (k + 1)), IsCyc z →
    ∃ C : ℝ, ∀ ω : Form (HS L N) (k + 1), Good ω → (∀ γ, FInv ω (emb L N γ)) → (∀ s, FInv ω (scal L N s)) →
      IntegrableOn (fun x => ‖fr ω (ofS L N x)‖ ^ 2) d.D d.μ →
      |ev (emb L N) (intP ω) (one L N) z| ≤ C * √(∫ x in d.D, ‖fr ω (ofS L N x)‖ ^ 2 ∂d.μ)

def SMean : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N q : ℕ), 1 ≤ N → ∀ (d : Dom L N) (ω : Form (HS L N) q),
    ContinuousOn ω (Pos L N) → (∀ γ, FInv ω (emb L N γ)) → (∀ s, FInv ω (scal L N s)) →
    IntegrableOn (fun x => fr ω (ofS L N x)) d.D d.μ →
      ∃ ωb : Form (HS L N) q, (∀ g, FInv ωb g) ∧
        ∀ x, fr ωb x = (d.μ.real d.D)⁻¹ • ∫ y in d.D, fr ω (ofS L N y) ∂d.μ

def SInv : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N k : ℕ) (ω : Form (HS L N) (k + 1)), (∀ g, FInv ω g) →
    Good ω ∧ (Odd k → ∀ (n : ℕ) (h : n ≤ N) (z : Chn (Gm L n) (k + 1)), IsCyc z → IsPrim z →
      ev (emb L N) (intP ω) (one L N) (cmap (stab (𝓞 L) n N h) (k + 1) z) = 0)

def PVBig : Prop :=
  ∀ k : ℕ, Odd k → ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → k + 1 < nrComplexPlaces L → PV (𝓞 L) k

def SJoin : Prop :=
  SChain → SEv → SSep → SStab → SPrime → SHecke → SHt → SPU → SMom → SWhit → SCen → SGap → SLoc → SMean → SInv → PVBig

end PositivityTheory.KB

end
