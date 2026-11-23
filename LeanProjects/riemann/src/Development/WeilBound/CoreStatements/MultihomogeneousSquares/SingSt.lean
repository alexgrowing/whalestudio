import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares

noncomputable section

namespace SquareStatements.Sing

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open GroundTheory.Heights₂.Heights.LowerBoundFree (valAt)
open scoped ComplexOrder

def col (p q : ℕ) (m : Fin (p + q)) : Fin (p + q) :=
  if h : (m : ℕ) < p then wEmb p q ⟨m, h⟩ else omEmb p q ⟨m - p, by have := m.2; omega⟩

def revDual {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ := (Aᵀ⁻¹).submatrix Fin.rev Fin.rev

def grN {r : ℕ} (Γ : Matrix (Fin r) (Fin r) ℂ) (k : ℕ) : ℝ := Real.sqrt (leadMinor Γ (k + 1) / leadMinor Γ k)

def mu (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) (m : Fin (p + q)) : ℝ :=
  if (m : ℕ) < p then grN (wBlock Γ) m else (grN (revDual (omBlock Γ)) (p + q - 1 - m))⁻¹

def C4 : Prop :=
  ∀ (p q : ℕ) (G h : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), IsBlockDiag p G → G.PosDef → IsBlockDiag p h → h.det ≠ 0 →
    (∀ m, 0 < mu p q (hᴴ * G * h) m) ∧ ∀ i : Fin (p + q), detFac p i h ≠ 0 ∧
      ∑ m ∈ Finset.Iic i, Real.log (mu p q (hᴴ * G * h) m) = blockPot p i G h + Real.log ‖detFac p i h‖

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}

def Tot (tie : FlagTie M 𝔐) (𝔐' : HodgeCpt Y S y) (Fl : 𝔐'.Flag) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) : Prop :=
  HodgeOver 𝔐' 𝔐 pr (algebraMap M.Ω Φ) j ∧ (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) ∧
    (∀ τ (k : Fin D.p), Fl.b (.inl τ) k = colFrame (fun a => j (tie.eW τ a)) (wBlock (M.g τ)) k) ∧
    ∀ τ (v : Fin D.q → 𝔐.Vgen (.inr τ)), (∀ a b, tie.eO τ a (v b) = if a = b then 1 else 0) →
      ∀ k : Fin D.q, Fl.b (.inr τ) k = colFrame (fun a => j (v a)) (omBlock (M.g τ))ᵀ⁻¹ k.rev

def inFrame (M : FlagModel y (CMType H) (D.p + D.q) D.p) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk)
    (τ : CMType H) (B : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Φ) : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Φ :=
  ((F.T τ).map (algebraMap M.Ω Φ))⁻¹ * M.g τ * B

def Adapted (𝔐' : HodgeCpt Y S y) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐'.X) (B : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Φ)
    (h : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) : Prop :=
  IsBlockDiag D.p B ∧ B.BlockTriangular id ∧ B.det ≠ 0 ∧ IsBlockDiag D.p h ∧ h.det ≠ 0 ∧
    ∀ a b, ValAt 𝔐'.ξ z (inFrame M F τ B a b) (h a b)

end

def C0 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (𝔐' : HodgeCpt Y S y)
    (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐'.X) (w : (Σ k, ι k) → ℂ),
    HodgeOver 𝔐' 𝔐 pr (algebraMap M.Ω Φ) j → CoordsAt 𝔐'.ξ y z w →
    CoordsAt 𝔐.ξ M.x (z ≫ pr) (basePart M.blk w) ∧ (𝔐'.Interior z ↔ 𝔐.Interior (z ≫ pr)) ∧
      (∀ a r, ValAt 𝔐.ξ (z ≫ pr) a r → ValAt 𝔐'.ξ z (algebraMap M.Ω Φ a) r) ∧
      ∀ s, RegAt M.x (mCoordIdeal (basePart M.blk w)) s →
        ValAt 𝔐'.ξ z (algebraMap M.Ω Φ s) (valAt M.x s (basePart M.blk w))

def C1 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐) (𝔐' : HodgeCpt Y S y)
    (Fl : 𝔐'.Flag) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐'.X)
    (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H),
    Tot tie 𝔐' Fl pr j → M.IsFrame F → (𝔐.V (.inl τ)).IsFrameAt (tie.wFrame F τ) ⟨centre (z ≫ pr), 𝔐.all _⟩ →
    (omBundle 𝔐 τ).IsFrameAt (tie.omFrame F τ) ⟨centre (z ≫ pr), 𝔐.all _⟩ → ∃ B h, Adapted 𝔐' F τ z B h

def C2 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐' : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐'.X)
    (wb : (Σ k, baseIdx ι M.blk k) → ℂ) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    (B : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Φ) (h : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ),
    M.IsFrame F → M.GoodAt F (mCoordIdeal wb) →
    (∀ s, RegAt M.x (mCoordIdeal wb) s → ValAt 𝔐'.ξ z (algebraMap M.Ω Φ s) (valAt M.x s wb)) →
    (∀ k, M.x ⟨k, F.c k⟩ ≠ 0) → Adapted 𝔐' F τ z B h → ∀ i : Fin (D.p + D.q),
    (∀ k, M.blk (τ, i) = some k → ∀ m : ι k,
      ValAt 𝔐'.ξ z ((∏ a ∈ Finset.Iic i, B (col D.p D.q a) (col D.p D.q a)) * detFac D.p i (M.g τ) * y ⟨k, m⟩ *
          ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k'))
        (detFac D.p i h * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) wb * minorIJ h I (stepCols (D.p + D.q) D.p i))) ∧
    (M.blk (τ, i) = none → valAt M.x (F.υ (τ, i)) wb ≠ 0 ∧
      ValAt 𝔐'.ξ z ((∏ a ∈ Finset.Iic i, B (col D.p D.q a) (col D.p D.q a)) * detFac D.p i (M.g τ) *
          algebraMap M.Ω Φ (M.lam (τ, i)) * ∏ k', algebraMap M.Ω Φ (M.x ⟨k', F.c k'⟩) ^ (-M.b (τ, i) k'))
        (detFac D.p i h * valAt M.x (F.υ (τ, i)) wb))

def C5 : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type)
    (N j : ℕ) (M : FlagModel y Ψ N j) (wb : (Σ k, baseIdx ι M.blk k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk)
    (h : Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) (k : K), wb ∈ mcPts (mCoordIdeal M.x) →
    M.IsFrame F → M.GoodAt F (mCoordIdeal wb) → IsBlockDiag j h → h.det ≠ 0 → M.blk p = some k →
    ∃ m : ι k, ∑ I, valAt M.x (F.u ⟨k, m⟩ I) wb * minorIJ h I (stepCols N j p.2) ≠ 0

def GradedLineNormsW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐) (𝔐' : HodgeCpt Y S y)
    (Fl : 𝔐'.Flag) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐'.X)
    (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    (B : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Φ) (h G : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ),
    Tot tie 𝔐' Fl pr j → M.IsFrame F → (𝔐.V (.inl τ)).IsFrameAt (tie.wFrame F τ) ⟨centre (z ≫ pr), 𝔐.all _⟩ →
    Adapted 𝔐' F τ z B h → IsBlockDiag D.p G → G.PosDef → 𝔐'.Interior z →
    𝔐.M.GramAt 𝔐.t.PP.L (z ≫ pr) (tie.wFrame F τ) (wBlock G) → ∀ k : Fin D.p,
      𝔐'.M.IsGrNorm 𝔐'.t.PP.L (𝔐'.V (.inl τ)) (Fl.b (.inl τ)) k z (B (wEmb D.p D.q k) (wEmb D.p D.q k))
        (grN (wBlock (hᴴ * G * h)) k)

def GradedLineNormsDualOmega : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐) (𝔐' : HodgeCpt Y S y)
    (Fl : 𝔐'.Flag) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐'.X)
    (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    (B : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) Φ) (h G : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ),
    Tot tie 𝔐' Fl pr j → M.IsFrame F → (omBundle 𝔐 τ).IsFrameAt (tie.omFrame F τ) ⟨centre (z ≫ pr), 𝔐.all _⟩ →
    Adapted 𝔐' F τ z B h → IsBlockDiag D.p G → G.PosDef → 𝔐'.Interior z →
    DualGramAt 𝔐.M 𝔐.t.PP.L (z ≫ pr) (𝔐.Vgen (.inr τ)) (tie.omFrame F τ) (omBlock G) → ∀ k : Fin D.q,
      𝔐'.M.IsGrNorm 𝔐'.t.PP.L (𝔐'.V (.inr τ)) (Fl.b (.inr τ)) k z (B (omEmb D.p D.q k.rev) (omEmb D.p D.q k.rev))⁻¹
        (grN (revDual (omBlock (hᴴ * G * h))) k)

def GramFramesOverModel : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)]
    (x : (Σ k, J k) → Ω) (x' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S x) (A' : HodgeCpt Y S x') (pr : A'.X ⟶ A.X)
    (i : Ω →+* Ω') (j : A.Li →+ A'.Li) (z : Spec (CommRingCat.of ℂ) ⟶ A'.X) (r : ℕ) (b : Fin r → A.Li)
    (X : Matrix (Fin r) (Fin r) Ω') (h : Matrix (Fin r) (Fin r) ℂ),
    HodgeOver A' A pr i j → (∀ p q, ValAt A'.ξ z (X p q) (h p q)) →
    (A'.Interior z → ∀ Γ, A.M.GramAt A.t.PP.L (z ≫ pr) b Γ →
      A'.M.GramAt A'.t.PP.L z (colFrame (fun a => j (b a)) X) (hᴴ * Γ * h)) ∧
    ∀ L : Lat A.ξ A.Li, h.det ≠ 0 → L.IsFrameAt b ⟨centre (z ≫ pr), A.all _⟩ →
      (L.pull A'.ξ pr j).IsFrameAt (colFrame (fun a => j (b a)) X) ⟨centre z, A'.all _⟩

end SquareStatements.Sing
