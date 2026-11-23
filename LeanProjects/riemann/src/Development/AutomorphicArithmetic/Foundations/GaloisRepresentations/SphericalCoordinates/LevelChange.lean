import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.IsCoordA
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemOfMemHeckeLevel
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

def RhoSig : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.a = 1 → D.m = 1 → ∀ t₀ : D.F →+* ℂ, (∀ i, D.tau i = t₀) →
    ∃ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀

def GUnif : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.a = 1 → D.m = 1 → ∀ t₀ : D.F →+* ℂ, (∀ i, D.tau i = t₀) →
    ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ (gb : GBase D.toG ℂ), IsStd D gb → ∀ N : ℕ, 3 ≤ N → N.Coprime p → ∀ X : GenModel gb N,
    SmoothOfRelativeDimension (D.n - 1) X.s ∧ QuasiCompact X.s ∧ IsSeparated X.s ∧
    ∃ (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL : _), FineAt (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N) ∧
      Nonempty (Unif (gfam X.univ hX hL) (RingHom.id ℂ) ρ N (D.Cls N))

def SheetOf : Prop :=
  ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ)
    (Cl : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (U : Unif F (RingHom.id ℂ) ρ N Cl) (i : Fin U.n), 3 ≤ N → FullMark N (U.Di i) (U.t i) →
    ∃ S : Sheet F.s F.A (U.Di i) ρ, (∀ P, S.u P = U.u i P) ∧ ∀ P z, (S.ex P z).left = (U.ex i P z).left

def FixFinite : Prop :=
  ∀ (Z Y : Scheme.{0}) (sZ : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (d : ℕ) (c₁ c₂ : Y ⟶ Z) (h₁ : c₁ ≫ sZ = s') (h₂ : c₂ ≫ sZ = s'),
    IsSeparated sZ → QuasiCompact s' → LocallyOfFiniteType s' →
    (∀ y : CxPts s' (RingHom.id ℂ), y.1 ≫ c₁ = y.1 ≫ c₂ → ∃ A, GlobalTheory.W1.IsTan d c₁ c₂ h₁ h₂ y A ∧ (1 - A).det ≠ 0) →
    {y : CxPts s' (RingHom.id ℂ) | y.1 ≫ c₁ = y.1 ≫ c₂}.Finite

def PDicEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ B : GlobalTheory.LKCx.Form G, Nonempty (PDic L B.β)

def RDicEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (t₀ : D.F →+* ℂ), (∀ i, D.tau i = t₀) → ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ B : GlobalTheory.LKCx.Form G, Nonempty (RDic L v B.β ρ t₀)

def RdAct : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (B : GlobalTheory.LKCx.Form G) (y : GlobalTheory.LKCx.grp G B.β) (h₁ h₂ : G.GAf) (w : VQ D),
    rd L (trivX B) h₁ (actY L y w) = L.actG (h₁⁻¹ * B.toAf y * h₂) (rd L (trivX B) h₂ w)

def RdForm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (B : GlobalTheory.LKCx.Form G) (h₁ : G.GAf), ∃ c : (AfP p)ˣ, ∀ u w : VQ D,
    (D.EF.baseChange ℚ).baseChange (AfP p) (rd L (trivX B) h₁ u) (rd L (trivX B) h₁ w) =
      (c : AfP p) * algebraMap ℚ (AfP p) (formB L B.β u w)

def RdDense : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (h₁ : G.GAf) (n : ℕ), 0 < n → ∀ z : AfP p ⊗[ℚ] VQ D,
    ∃ w : VQ D, ∃ e ∈ LaHat D, z = rd L x h₁ w + n • e

def AdOfWit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (B : GlobalTheory.LKCx.Form G) (D' : PLat D.O D.inv) (j : D'.La →+ VQ D), IsPlace L B.β D' j →
    ∀ f nu, IsWit D' f nu → ∃ h₁, Reads L (trivX B) D' f j h₁

def WitOfAd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (B : GlobalTheory.LKCx.Form G) (N : ℕ), 0 < N → N.Coprime p → ∀ (h₁ : G.GAf) (M : AddSubgroup (VQ D)), IsPLat D M →
    (∃ s : ℚ, 0 < s ∧ PerfAt L B.β s M) → ∃ (D' : PLat D.O D.inv) (t : D.La → D'.La) (j : D'.La →+ VQ D), D.Cls N D' t ∧ IsPlace L B.β D' j ∧
      IsCoordA L (trivX B) N D' t j h₁ ∧ IsLocP D' j M

def CoordKN : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (N : ℕ), 0 < N → N.Coprime p → ∀ (D' : PLat D.O D.inv) (t : D.La → D'.La) (j : D'.La →+ VQ D) (h₁ h₂ : G.GAf),
    IsCoordA L x N D' t j h₁ → (IsCoordA L x N D' t j h₂ ↔ h₂⁻¹ * h₁ ∈ L.KN N)

def PlaceEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (t₀ : D.F →+* ℂ), (∀ i, D.tau i = t₀) → ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ (N : ℕ) (D' : PLat D.O D.inv) (t : D.La → D'.La), D.Cls N D' t → (∃ P, IsPeriod D' ρ P) →
    ∃ (q : GlobalTheory.LKCx.FCls G) (j : D'.La →+ VQ D), IsPlace L (Quot.out q).β D' j

def PlacePer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) (j : D'.La →+ VQ D), IsPlace L β D' j →
    (∀ P, IsPeriod D' ρ P → ∃ Q, IsPerQ L β ρ Q ∧ ∀ u, Q (j u) = P u) ∧
    ∀ Q, IsPerQ L β ρ Q → 2 * D.g = Module.finrank ℤ D.La → IsPeriod D' ρ (Q.comp j)

def PlaceLoc : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (D' : PLat D.O D.inv) (j : D'.La →+ VQ D), IsPlace L β D' j → HalfPerf p D' →
    ∃ M, IsPLat D M ∧ (∃ s : ℚ, 0 < s ∧ PerfAt L β s M) ∧ IsLocP D' j M

def LatForm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β β' : G.Cˣ) (D' D'' : PLat D.O D.inv) (j : D'.La →+ VQ D) (j'' : D''.La →+ VQ D), IsPlace L β D' j →
    IsPlace L β' D'' j'' → ∀ (w : D''.La →ₗ[D.O] D'.La) (m : ℤ), 0 < m → (∀ u u', D'.EF (w u) (w u') = m * D''.EF u u') →
    ∃ (y : G.Cˣ) (s : ℚˣ), 0 < (s : ℚ) ∧ (y : G.C) * β' * sh G y = algebraMap ℚ G.C s * β ∧ ∀ u, j (w u) = L.rep (y : G.C) (j'' u)

def ClsScalar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N N' : ℕ) (D' : PLat D.O D.inv) (t : D.La → D'.La) (D'' : PLat D.O D.inv) (t'' : D.La → D''.La), D.Cls N D' t → D.Cls N' D'' t'' →
    ∀ (w : D''.La ≃+ D'.La) (r : ℚ), 0 < r → (∀ u u', (D'.EF (w u) (w u') : ℚ) = r * D''.EF u u') → r = 1

def LatIso : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (N : ℕ), 0 < N → N.Coprime p →
    ∀ (D' : PLat D.O D.inv) (t : D.La → D'.La) (D'' : PLat D.O D.inv) (t'' : D.La → D''.La) (j : D'.La →+ VQ D) (j'' : D''.La →+ VQ D) (a a'' : G.GAf × Gr G 1) (N₁ N₂ : ℕ) t₁ t₂,
    D.Cls N₁ D' t₁ → D.Cls N₂ D'' t₂ → IsPlace L B.β D' j → IsPlace L B.β D'' j'' → IsCoordA L (trivX B) N D' t j a.1 →
    IsCoordA L (trivX B) N D'' t'' j'' a''.1 → IsLocP D' j (PD.lat a.2) → IsLocP D'' j'' (PD.lat a''.2) →
    ∀ y : GlobalTheory.LKCx.grp G B.β, (a.1⁻¹ * B.toAf y * a''.1 ∈ L.KN N ∧ a.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a''.2 ∈ (KHT p G.m G.n 1 G.Fw)) ↔
      ∃ w : D''.La ≃ₗ[D.O] D'.La, IsMarkedIsom N D'' D' t'' t w ∧ ∀ u, j (w u) = actY L y (j'' u)

def CoordEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (t₀ : D.F →+* ℂ), (∀ i, D.tau i = t₀) → ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ (PD : ∀ B : GlobalTheory.LKCx.Form G, PDic L B.β) (RD : ∀ B : GlobalTheory.LKCx.Form G, RDic L v B.β ρ t₀) (N : ℕ), 0 < N → N.Coprime p → ∀ (D' : PLat D.O D.inv) (t : D.La → D'.La) (P : D'.La →+ (Fin D.g → ℂ)), D.Cls N D' t → IsPeriod D' ρ P →
    ∃ (q : GlobalTheory.LKCx.FCls G) (a : GlobalTheory.LKCx.Dat G v (Quot.out q).β) (j : D'.La →+ VQ D),
      IsCoord L (Quot.out q) (PD _) (RD _) N D' t P j a

def CoordOcc : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (t₀ : D.F →+* ℂ), (∀ i, D.tau i = t₀) → ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ (PD : ∀ B : GlobalTheory.LKCx.Form G, PDic L B.β) (RD : ∀ B : GlobalTheory.LKCx.Form G, RDic L v B.β ρ t₀) (N : ℕ), 0 < N → N.Coprime p → ∀ (B : GlobalTheory.LKCx.Form G) (a : GlobalTheory.LKCx.Dat G v B.β),
    ∃ (D' : PLat D.O D.inv) (t : D.La → D'.La) (P : D'.La →+ (Fin D.g → ℂ)) (j : D'.La →+ VQ D), D.Cls N D' t ∧ IsPeriod D' ρ P ∧ IsCoord L B (PD _) (RD _) N D' t P j a

def CoordIso : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (v : InfinitePlace G.F) (t₀ : D.F →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (PD : ∀ B : GlobalTheory.LKCx.Form G, PDic L B.β) (RD : ∀ B : GlobalTheory.LKCx.Form G, RDic L v B.β ρ t₀) (N : ℕ), 0 < N → N.Coprime p →
    ∀ (D' : PLat D.O D.inv) (t : D.La → D'.La) (P : D'.La →+ (Fin D.g → ℂ)) (D'' : PLat D.O D.inv) (t'' : D.La → D''.La) (P'' : D''.La →+ (Fin D.g → ℂ)),
    D.Cls N D' t → D.Cls N D'' t'' → ∀ (q q'' : GlobalTheory.LKCx.FCls G) (a : GlobalTheory.LKCx.Dat G v (Quot.out q).β)
      (a'' : GlobalTheory.LKCx.Dat G v (Quot.out q'').β) j j'', IsCoord L (Quot.out q) (PD _) (RD _) N D' t P j a →
      IsCoord L (Quot.out q'') (PD _) (RD _) N D'' t'' P'' j'' a'' →
      ((∃ (w : D''.La ≃ₗ[D.O] D'.La) (h : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ)), IsMarkedIsom N D'' D' t'' t w ∧ ∀ u, P (w u) = h (P'' u)) ↔
        (⟨q, Quot.mk _ a⟩ : GlobalTheory.LKCx.AllPts G v (L.KN N) (KHT p G.m G.n 1 G.Fw)) = ⟨q'', Quot.mk _ a''⟩)

def CoordMove : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (v : InfinitePlace G.F) (t₀ : D.F →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (B : GlobalTheory.LKCx.Form G) (PD : PDic L B.β) (RD : RDic L v B.β ρ t₀) (N : ℕ)
    (D' : PLat D.O D.inv) (t : D.La → D'.La) (P : D'.La →+ (Fin D.g → ℂ)) (D'' : PLat D.O D.inv) (t'' : D.La → D''.La) (P'' : D''.La →+ (Fin D.g → ℂ))
    (w : D''.La ≃ₗ[D.O] D'.La), IsMarkedIsom N D'' D' t'' t w → (∀ u, P'' u = P (w u)) → ∀ (j : D'.La →+ VQ D) (j'' : D''.La →+ VQ D),
    (∀ u, j'' u = j (w u)) → ∀ a, IsCoord L B PD RD N D' t P j a → IsCoord L B PD RD N D'' t'' P'' j'' a

def UnifG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (t₀ : D.F →+* ℂ), (∀ i, D.tau i = t₀) → ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ (PD : ∀ B : GlobalTheory.LKCx.Form G, PDic L B.β) (RD : ∀ B : GlobalTheory.LKCx.Form G, RDic L v B.β ρ t₀) (N : ℕ), 0 < N → N.Coprime p → ∀ (F : Fam ℂ D.O D.La D.g) (U : Unif F (RingHom.id ℂ) ρ N (D.Cls N)),
    ∃ Φ : CxPts F.s (RingHom.id ℂ) ≃ GlobalTheory.LKCx.AllPts G v (L.KN N) (KHT p G.m G.n 1 G.Fw), ∀ x, ∃ (q : GlobalTheory.LKCx.FCls G) (a : GlobalTheory.LKCx.Dat G v (Quot.out q).β)
      (i : Fin U.n) (P : (U.Di i).La →+ (Fin D.g → ℂ)) (j : (U.Di i).La →+ VQ D), Φ x = ⟨q, Quot.mk _ a⟩ ∧ IsPeriod (U.Di i) ρ P ∧
      x.1 = U.u i P ∧ IsCoord L (Quot.out q) (PD _) (RD _) N (U.Di i) (U.t i) P j a

def StabTriv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → D.m = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (t₀ : D.F →+* ℂ), (∀ i, D.tau i = t₀) → ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ (PD : ∀ B : GlobalTheory.LKCx.Form G, PDic L B.β) (RD : ∀ B : GlobalTheory.LKCx.Form G, RDic L v B.β ρ t₀) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (B : GlobalTheory.LKCx.Form G) (a : GlobalTheory.LKCx.Dat G v B.β) (y : GlobalTheory.LKCx.grp G B.β),
    Sees B (L.KN N : Set G.GAf) a y → y = 1

def IsogCoord : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (B : GlobalTheory.LKCx.Form G) (N N' : ℕ), 0 < N → N.Coprime p → 0 < N' → N'.Coprime p → ∀ h : G.GAf, (∀ u ∈ L.KN N', h * u * h⁻¹ ∈ L.KN N) →
    ∀ (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) (t : D.La → D'.La) (D'' : PLat D.O D.inv) (t'' : D.La → D''.La) P P'' (inc : D'.La →ₗ[D.O] D''.La) (d : ℕ),
    IsPeriod D' ρ P → IsPeriod D'' ρ P'' → (∀ u, P'' (inc u) = P u) → d.Coprime p → (∀ u'', ∃ u, inc u = d • u'') →
    ∀ f nu f'' nu'', IsWit D' f nu → IsWit D'' f'' nu'' → (∀ a, ∃ u, f N' a = t a + N' • u) → (∀ a, ∃ u, f'' N a = t'' a + N • u) →
    (∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
      (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w) →
    ∀ (j : D'.La →+ VQ D) (h₁ : G.GAf) (M : AddSubgroup (VQ D)), IsPlace L B.β D' j → IsCoordA L (trivX B) N' D' t j h₁ → IsLocP D' j M →
    ∃ j'' : D''.La →+ VQ D, (∀ u, j'' (inc u) = j u) ∧ IsPlace L B.β D'' j'' ∧ IsCoordA L (trivX B) N D'' t'' j'' (h₁ * h⁻¹) ∧
      IsLocP D'' j'' M

def RegSep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (B : GlobalTheory.LKCx.Form G) (a : GlobalTheory.LKCx.Dat G v B.β) (y : GlobalTheory.LKCx.grp G B.β),
    GlobalTheory.LKCx.FixL G v B.β y a.2.1 → GlobalTheory.LKCx.RegAf G (a.1.1⁻¹ * B.toAf y * a.1.1) →
    (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable

def InvMin : Prop :=
  ∀ (K A : Type) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] [Nontrivial A] (u : Aˣ),
    minpoly K ((u⁻¹ : Aˣ) : A) = invPoly (minpoly K (u : A)) ∧ (minpoly K ((u⁻¹ : Aˣ) : A)).natDegree = (minpoly K (u : A)).natDegree ∧
    ((minpoly K (u : A)).Separable → (minpoly K ((u⁻¹ : Aˣ) : A)).Separable)

def MinBridge : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (D' : PLat D.O D.inv) (j : D'.La →+ VQ D), IsPlace L β D' j → ∀ (ga : D'.La →ₗ[D.O] D'.La) (c : G.C),
    (∀ u, j (ga u) = L.rep c (j u)) → IsMinOf (algebraMap (𝓞 D.F) D.O) ga ((minpoly G.F c).map (L.e.symm : G.F →+* D.F))

def EigSame : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ) (B : GlobalTheory.LKCx.Form G) (K : Subgroup G.GAf) (S : Set G.GAf),
    (∀ u ∈ K, ∀ g, u⁻¹ * g * u ∈ S ↔ g ∈ S) → ∀ a a' : GlobalTheory.LKCx.Dat G v B.β,
    (Quot.mk _ a : GlobalTheory.LKCx.Form.Pts v B K (KHT p G.m G.n 1 G.Fw)) = Quot.mk _ a' → ∃ E : GlobalTheory.LKCx.grp G B.β ≃ GlobalTheory.LKCx.grp G B.β, E 1 = 1 ∧ ∀ y,
      (Sees B S a y ↔ Sees B S a' (E y)) ∧ (Sees B S a y →
        minpoly G.F ((((E y : GlobalTheory.LKCx.grp G B.β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧
        GlobalTheory.RootSumWeights.eigL G v B.β (E y) a'.2.1 = GlobalTheory.RootSumWeights.eigL G v B.β y a.2.1)

def SumPts : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ) (K : Subgroup G.GAf) (S : Set G.GAf),
    (∀ u ∈ K, ∀ g, u⁻¹ * g * u ∈ S ↔ g ∈ S) →
    (∀ (B : GlobalTheory.LKCx.Form G) (a : GlobalTheory.LKCx.Dat G v B.β) y, Sees B (K : Set G.GAf) a y → y = 1) →
    (∀ (B : GlobalTheory.LKCx.Form G) (a : GlobalTheory.LKCx.Dat G v B.β) y y', Sees B S a y → Sees B S a y' → y = y') →
    ∀ (T : Type) (Φ : T ≃ GlobalTheory.LKCx.AllPts G v K (KHT p G.m G.n 1 G.Fw)) (Fb : Finset T) (w : T → ℂ),
    (∀ x, ∃ (q : GlobalTheory.LKCx.FCls G) (a : GlobalTheory.LKCx.Dat G v (Quot.out q).β), Φ x = ⟨q, Quot.mk _ a⟩ ∧ (x ∈ Fb ↔ ∃ y, Sees (Quot.out q) S a y) ∧
      ∀ y, Sees (Quot.out q) S a y → w x = c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v _ y a.2.1)) →
    ∑ x ∈ Fb, w x = GlobalTheory.RootSumWeights.cxTotalM G v c K (S.indicator 1) (KHT p G.m G.n 1 G.Fw) (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1)

def LevelChange : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ) (K K' : Subgroup G.GAf) (h : G.GAf),
    K' ≤ GlobalTheory.HeckeCorr.heckeLevel K h⁻¹ → K'.relIndex K ≠ 0 →
    (∀ (B : GlobalTheory.LKCx.Form G) (a : GlobalTheory.LKCx.Dat G v B.β) y, Sees B (K : Set G.GAf) a y → y = 1) →
    {x : GlobalTheory.LKCx.AllPts G v K' (KHT p G.m G.n 1 G.Fw) | ∃ y, Sees (Quot.out x.1) {g | h * g ∈ K} (Quot.out x.2) y}.Finite →
    GlobalTheory.RootSumWeights.cxTotalM G v c K' ({g | h * g ∈ K}.indicator 1) (KHT p G.m G.n 1 G.Fw) (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1) =
      (K'.relIndex (GlobalTheory.HeckeCorr.heckeLevel K h⁻¹) : ℂ) *
        GlobalTheory.RootSumWeights.cxTotalM G v c K (Formalism.UG.dosetInd ℂ K h⁻¹) (KHT p G.m G.n 1 G.Fw) (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1)

def AdCore : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (D' : PLat D.O D.inv) (j : D'.La →+ VQ D), IsPlace L β D' j → ∀ f nu, IsWit D' f nu →
    ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (c : (AfP p)ˣ), Triv G (AfP p) β x c ∧ Reads L x D' f j 1

def Rigid : Prop :=
  ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La)
    (P : D'.La →+ (Fin g → ℂ)) (w : D'.La ≃ₗ[O] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), 3 ≤ N → FullMark N D' t → IsPeriod D' ρ P →
    IsMarkedIsom N D' D' t t w → (∀ u, P (w u) = h (P u)) → ∀ u, w u = u

def IsogForm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (h : G.GAf) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' D'' : PLat D.O D.inv) P P'' (inc : D'.La →ₗ[D.O] D''.La),
    IsPeriod D' ρ P → IsPeriod D'' ρ P'' → (∀ u, P'' (inc u) = P u) → ∀ f nu f'' nu'', IsWit D' f nu → IsWit D'' f'' nu'' →
    (∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
      (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w) →
    ∃ r : ℚ, 0 < r ∧ ∀ u u', (D''.EF (inc u) (inc u') : ℚ) = r * D'.EF u u'

def FixLine : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (v : InfinitePlace G.F) (t₀ : D.F →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (β : G.Cˣ) (RD : RDic L v β ρ t₀) (Q : VQ D →+ (Fin D.g → ℂ))
    (z : GlobalTheory.LKCx.PosV G v β), IsPerQ L β ρ Q → RD.rel Q z.1 → ∀ y : GlobalTheory.LKCx.grp G β,
    (GlobalTheory.LKCx.FixL G v β y z.1 ↔ ∃ H : Matrix (Fin D.g) (Fin D.g) ℂ, ∀ w, Q (actY L y w) = H *ᵥ Q w) ∧ (GlobalTheory.LKCx.FixL G v β y z.1 → GlobalTheory.LKCx.FixL G v β y⁻¹ z.1)

def ActY : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β),
    (∀ u w, formB L β (actY L y u) (actY L y w) = (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * formB L β u w) ∧
    (∀ c w, actY L y (actQ D c w) = actQ D c (actY L y w)) ∧
    (∀ (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q Q' : VQ D →+ (Fin D.g → ℂ)), IsPerQ L β ρ Q → (∀ w, Q' (actY L y w) = Q w) → IsPerQ L β ρ Q') ∧
    ∀ (v : InfinitePlace G.F) (z : GlobalTheory.LKCx.PosV G v β), sh G β = β → ∃ z' : GlobalTheory.LKCx.PosV G v β,
      z'.1 = (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1

def IntMult : Prop :=
  ∀ (O : Type) [Ring O] (bar : O → O) (D' : PLat O bar) (ga : D'.La →ₗ[O] D'.La) (r : ℚ), 0 < r →
    (∀ u u', (D'.EF (ga u) (ga u') : ℚ) = r * D'.EF u u') → ∃ m : ℤ, 0 < m ∧ ∀ u u', D'.EF (ga u) (ga u') = m * D'.EF u u'

def ModelEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → Nonempty (Model b N)

def GenCmp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (R' : Type) [CommRing R'] [Algebra ℚ R'] (φ : R →+* R') (gb : GBase D.toG R'), gb.ρ = φ b.ρ → (∀ i, gb.t i = φ.comp (b.t i)) → ∀ (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (X : GenModel gb N), ∃ j : X.X ⟶ pullback M.s (spMap φ), IsOpenImmersion j ∧ IsClosedImmersion j ∧ j ≫ pullback.snd _ _ = X.s ∧ IsGPull X.univ M.univ (j ≫ pullback.fst _ _)

def GenPts : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (φ : R →+* ℂ) (gb : GBase D.toG ℂ), gb.ρ = φ b.ρ → (∀ i, gb.t i = φ.comp (b.t i)) → ∀ (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (X : GenModel gb N) (j : X.X ⟶ pullback M.s (spMap φ)), IsOpenImmersion j → IsClosedImmersion j → j ≫ pullback.snd _ _ = X.s → IsGPull X.univ M.univ (j ≫ pullback.fst _ _) → ∀ y' : Sp ℂ ⟶ M.X, y' ≫ M.s = spMap φ → ∃! y : Sp ℂ ⟶ X.X, y ≫ X.s = 𝟙 _ ∧ y ≫ j ≫ pullback.fst _ _ = y'

def BaseC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.a = 1 → D.m = 1 → ∀ t₀ : D.F →+* ℂ, (∀ i, D.tau i = t₀) →
    ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ gb : GBase D.toG ℂ, IsStd D gb →
    ∃ b : Base D ℂ, gb.ρ = b.ρ ∧ (∀ i, gb.t i = (RingHom.id ℂ).comp (b.t i)) ∧ b.IsType (RingHom.id ℂ) ρ

def GFine : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (b : Base D ℂ) (gb : GBase D.toG ℂ) (N : ℕ) (M : Model b N) (X : GenModel gb N)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (h : SmoothOfRelativeDimension D.g M.univ.A.hom) (hL) (f : X.X ⟶ M.X), f ≫ M.s = X.s → IsGPull X.univ M.univ f →
    (∀ y' : Sp ℂ ⟶ M.X, y' ≫ M.s = spMap (RingHom.id ℂ) → ∃! y : Sp ℂ ⟶ X.X, y ≫ X.s = 𝟙 _ ∧ y ≫ f = y') →
    FineAt (M.univ.fam h hL) (RingHom.id ℂ) ρ N (D.Cls N) →
    ∃ (hX : SmoothOfRelativeDimension D.g X.univ.A.hom) (hL' : _), FineAt (gfam X.univ hX hL') (RingHom.id ℂ) ρ N (D.Cls N)

end UpperTheory.Gal.W2
