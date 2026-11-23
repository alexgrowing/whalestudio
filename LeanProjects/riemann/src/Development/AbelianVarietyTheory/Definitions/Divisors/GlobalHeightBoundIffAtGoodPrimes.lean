import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
import Formalism.SharpRestriction.Divisibility.LatticeTransfer

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O

namespace GlobalTheory.MixedLocalChains

section One

variable {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : DV.Mdl D p N rk)

def Comm : Prop := ∀ (E E' : M.Z.VDiv) (a : M.Z.Ch), M.Z.capDeg E (M.Z.cD E' * a) = M.Z.capDeg E' (M.Z.cD E * a)

def Cons (rt : Bool × Rt D.what₂.Tau N → M.Z.LB) (chern : MvPolynomial (Rt D.what₂.Tau N) ℝ →ₗ[ℝ] ℝ) : Prop :=
  ∀ G : MvPolynomial (Vm D.what₂.Tau N) ℚ, G.IsWeightedHomogeneous (wt D.what₂.Tau N) (dimFl D.what₂.Tau N) →
    ((M.Z.capDeg M.Z.divP (evC M rt G) : ℚ) : ℝ) / (M.cov : ℝ) = chern (collapse D _ (toR G))

def Local : Prop := ∀ (τ : Emb D p) (k : ℕ), 1 ≤ k → ∀ m : ℕ, m + k = dimFl D.what₂.Tau N + 1 →
  ∀ Q : MvPolynomial M.Z.LB ℚ, Q.IsHomogeneous m →
    chk (M.lie τ) k (evQ _ Q) + chk (M.om τ) k (evQ _ Q) =
      (∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ * chDiv (M.lie (phiPow D (n + 1) τ)).x (k - 1) (evQ _ Q)) -
        chDiv (M.lie τ).x (k - 1) (evQ _ Q) / ((p : ℝ) - 1)

def LocalFin (o : ℕ) : Prop := ∀ (τ : Emb D p) (k : ℕ), 1 ≤ k → ∀ Q : M.Z.Ch,
    (1 - ((p : ℝ) ^ (o * k))⁻¹) * (chk (M.lie τ) k Q + chk (M.om τ) k Q + chDiv (M.lie τ).x (k - 1) Q / ((p : ℝ) - 1)) =
      ∑ n ∈ Finset.range o, ((p : ℝ) ^ ((n + 1) * k))⁻¹ * chDiv (M.lie (phiPow D (n + 1) τ)).x (k - 1) Q

end One

def Pin {p : ℕ} [Fact p.Prime] (W : ValuationSubring ℂ) (jc : KW p →+* ℂ) : Prop :=
  ∀ a : KW p, jc a ∈ W ↔ a ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (KW p)).range

structure Term {D : D7} (Y : ShimX D.what₂.Tau) (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] (w : ι → ℝ)
    (jc : ι → (KW p →+* ℂ)) (M : ∀ la, DV.Mdl D p Y.N (rkOf (PsiOf D (jc la)) Y.N Y.j))
    (rt : ∀ la, Bool × Rt D.what₂.Tau Y.N → (M la).Z.LB) : Prop where
  sum_w : ∑ la, w la = 1
  lie : ∀ (Sx : Finset ℕ) (R : ℝ) (τ0 : D.what₂.Tau) (τ' : ι → Emb D p), (∀ la, (jc la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin (rkOf (PsiOf D (jc la)) Y.N Y.j (τ' la))) (i' : Fin Y.N), (∀ la, (i' : ℕ) = i la) →
    ∀ G : MvPolynomial (Vm D.what₂.Tau Y.N) ℚ, G.IsWeightedHomogeneous (wt D.what₂.Tau Y.N) (dimFl D.what₂.Tau Y.N) →
      Y.arMix Sx R p (dRt D.what₂.Tau Y.N (τ0, i') * toR G) = Real.log p * ∑ la, w la *
        ((((M la).Z.capDeg (((M la).lie (τ' la)).Dv (i la)) (evC (M la) (rt la) G) : ℚ) : ℝ) / ((M la).cov : ℝ))
  om : ∀ (Sx : Finset ℕ) (R : ℝ) (τ0 : D.what₂.Tau) (τ' : ι → Emb D p), (∀ la, (jc la).comp (τ' la) = tauEmb D τ0) →
    ∀ (i : ∀ la, Fin (Y.N - rkOf (PsiOf D (jc la)) Y.N Y.j (τ' la))) (i' : Fin Y.N), (∀ la, (i' : ℕ) = Y.j + i la) →
    ∀ G : MvPolynomial (Vm D.what₂.Tau Y.N) ℚ, G.IsWeightedHomogeneous (wt D.what₂.Tau Y.N) (dimFl D.what₂.Tau Y.N) →
      Y.arMix Sx R p (dRt D.what₂.Tau Y.N (τ0, i') * toR G) = Real.log p * ∑ la, w la *
        ((((M la).Z.capDeg (((M la).om (τ' la)).Dv (i la)) (evC (M la) (rt la) G) : ℚ) : ℝ) / ((M la).cov : ℝ))

def Roots {D : D7} {p : ℕ} [Fact p.Prime] {N j : ℕ} (jc : KW p →+* ℂ) (M : DV.Mdl D p N (rkOf (PsiOf D jc) N j))
    (rt : Bool × Rt D.what₂.Tau N → M.Z.LB) : Prop :=
  ∀ (t : D.what₂.Tau) (τ : Emb D p), jc.comp τ = tauEmb D t →
    (∀ (i : Fin (rkOf (PsiOf D jc) N j τ)) (i' : Fin N), (i' : ℕ) = i →
      rt (false, (t, i')) = (M.lie τ).x i ∧ rt (true, (t, i')) = (M.lie τ).x' i) ∧
    ∀ (i : Fin (N - rkOf (PsiOf D jc) N j τ)) (i' : Fin N), (i' : ℕ) = j + i →
      rt (false, (t, i')) = (M.om τ).x i ∧ rt (true, (t, i')) = (M.om τ).x' i

def GlobAt {D : D7} (Y : ShimX D.what₂.Tau) (p : ℕ) : Prop := ∀ (Sx : Finset ℕ) (R : ℝ) (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau Y.N + 1 → ∀ Q : MvPolynomial (Vm D.what₂.Tau Y.N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau Y.N) m →
    Y.arMix Sx R p ((tagDR D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k) -
          tagHT D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k)) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          Y.chern (chLie Y.j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) * collapse D _ Q)) -
        Y.chern (chLie Y.j (k - 1) (Sum.inl τ) * collapse D _ Q) / ((p : ℝ) - 1))

theorem globalHeightBound_iff_atGoodPrimes {D : D7} (Y : ShimX D.what₂.Tau) : GlobalTheory.CovHt.DeRhamMinusHodgeTateGoodPrimesAt Y ↔
    ∀ p : ℕ, p.Prime → p ≠ 2 → UnramE D p → p ∉ Y.lev → GlobAt Y p :=
  ⟨fun h p a b c d Sx R => h Sx R p a b c d, fun h Sx R p a b c d => h p a b c d Sx R⟩

section Pairs

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O]
  [CharP (ResidueField O) p] {B : Vert.Model O}

def IsCk {E E' : B.X.Modules} (φ : B.GenIso E E') (r k : ℕ) (f : PicSym B.X →ₗ[ℚ] ℚ) : Prop :=
  ∀ M : Vert.Model.FlagModel φ r, GlobalTheory.IsNormalScheme M.B.X → M.relDim = 0 → ∀ Q : PicSym B.X,
    ck (M.toFPair p) k (picSymPull M.π.f Q) = M.π.fibreDeg 1 * f Q

def ckP {E E' : B.X.Modules} (φ : B.GenIso E E') (r k : ℕ) : PicSym B.X →ₗ[ℚ] ℚ :=
  Classical.epsilon (IsCk p φ r k)

variable (B) in

structure Pres where
  r : ℕ
  E : B.X.Modules
  E' : B.X.Modules
  vb : GlobalTheory.VB.IsVB E r
  vb' : GlobalTheory.VB.IsVB E' r
  ψ : E' ⟶ E
  iso : IsIso (B.genRes.map ψ)

def Pres.mod (P : Pres B) : B.X.Modules := cokernel P.ψ

def Pres.ck (P : Pres B) (k : ℕ) : PicSym B.X →ₗ[ℚ] ℚ := haveI := P.iso; ckP p (Vert.Model.GenIso.ofHom P.ψ) P.r k

def Kills (g : Γ(B.X, ⊤)) (F : B.X.Modules) : Prop := smulHom F g = 0

def IsRootOfP (g : Γ(B.X, ⊤)) (a : ℕ) : Prop := ∃ u : Γ(B.X, ⊤)ˣ, g ^ a = u * (p : Γ(B.X, ⊤))

variable (B) in

def fibI : B.X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop (Ideal.span {(p : Γ(B.X, ⊤))})

def IsFrob (F F' : B.X.Modules) : Prop := ∃ h : (p : Γ((fibI p B).subscheme, ⊤)) = 0,
  Nonempty (F' ≅ (Scheme.Modules.pushforward (fibI p B).subschemeι).obj ((Scheme.Modules.pullback
    (GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out h ≫ (fibI p B).subschemeι)).obj F))

def IsExt (F₁ F₂ F₃ : B.X.Modules) : Prop := ∃ S : ShortComplex B.X.Modules, S.ShortExact ∧
  Nonempty (S.X₁ ≅ F₁) ∧ Nonempty (S.X₂ ≅ F₂) ∧ Nonempty (S.X₃ ≅ F₃)

variable (B) in

structure Chain {ι : Type} (φ : ι → ι) (o : ℕ) where
  π : Γ(B.X, ⊤)
  g : Γ(B.X, ⊤)
  π_root : IsRootOfP p π (p - 1)
  g_root : IsRootOfP p g p
  lw : ι → Pres B
  wl : ∀ τ, (lw τ).E ⟶ (lw τ).E'
  lw_wl : ∀ τ, (lw τ).ψ ≫ wl τ = smulHom _ π
  oo : ι → Pres B
  q : ℕ → ι → Pres B
  l : ℕ → ℕ → ι → Pres B
  c3 : ∀ τ, IsExt (cokernel (wl τ)) (q 0 τ).mod (oo τ).mod
  step : ∀ n < o, ∀ τ, IsExt (q (n + 1) τ).mod (q n τ).mod (l n 0 τ).mod
  l_frob : ∀ n < o, ∀ i ≤ n, ∀ τ, Kills g (l n i τ).mod ∧ IsFrob p (l n i τ).mod (l n (i + 1) τ).mod
  l_last : ∀ n < o, ∀ τ, Nonempty ((l n (n + 1) τ).mod ≅ cokernel (smulHom (lw (φ^[n + 1] τ)).E' (p : Γ(B.X, ⊤))))
  q_frob : ∀ n < o, ∀ τ, Kills g (q (n + 1) τ).mod ∧ IsFrob p (q (n + 1) τ).mod (q n (φ τ)).mod

def Reads {Z : ITh} {r : ℕ} (F : FPair Z r) (a : Z.Ch → PicSym B.X) (b : Z.VDiv → B.VDivQ) {E E' : B.X.Modules}
    (φ : B.GenIso E E') : Prop :=
  ∃ P : Vert.Model.FlagPair φ r, ∀ i, a (Z.c1 (F.x i)) = (B.toITh p).c1 ((P.toFPair p).x i) ∧ b (F.Dv i) = (P.toFPair p).Dv i

end Pairs

def HasChain {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
    {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ) (o : ℕ) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
  ∀ c : (nmodel z.Z).Comp, ∃ (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c))
    (Ch : Chain p B (phiPow D (p := p) 1) o), GlobalTheory.IsNormalScheme B.X ∧ f.relDim = 0 ∧ ∀ τ,
      (Ch.lw τ).r = rkOf (PsiOf D jc) N j τ ∧ (Ch.oo τ).r = N - rkOf (PsiOf D jc) N j τ ∧
      Reads p ((mdlOf z jc).lie τ) (fun x => picSymPull f.f (picSymPull ((nmodel z.Z).compι c) x))
        (fun d => Vert.Model.vPullQ f.comp_str (NModel.vResQ c d))
        (haveI := (Ch.lw τ).iso; (Vert.Model.GenIso.ofHom (Ch.lw τ).ψ).symm) ∧
      Reads p ((mdlOf z jc).om τ) (fun x => picSymPull f.f (picSymPull ((nmodel z.Z).compι c) x))
        (fun d => Vert.Model.vPullQ f.comp_str (NModel.vResQ c d))
        (haveI := (Ch.oo τ).iso; Vert.Model.GenIso.ofHom (Ch.oo τ).ψ)

def AtGood (Q : ∀ (D : D7) (O : Setup D) (p : ℕ) [Fact p.Prime] (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits)
    (_ : KW p →+* ℂ) (_ : AdmAt O.S O.κ (Fact.out : p.Prime) hW), Prop) : Prop :=
  ∀ (D : D7) (O : Setup D), O.Core → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → UnramE D p → p ∉ O.Y.lev →
    ∀ (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (jc : KW p →+* ℂ), Pin W jc →
      ∀ z : AdmAt O.S O.κ (Fact.out : p.Prime) hW, Q D O p W hW jc z

def ChainSt : Prop := AtGood fun _ _ _ _ _ _ jc z => ∀ o, HasChain z jc o

def LocalSt : Prop := AtGood fun _ _ _ _ _ _ jc z => Local (mdlOf z jc)

def ConsSt : Prop := AtGood fun _ O _ _ _ _ jc z => Cons (mdlOf z jc) (rootOf z jc) O.Y.chern

def TermSt : Prop := ∀ (D : D7) (O : Setup D), O.Core → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → UnramE D p → p ∉ O.Y.lev →
  ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (W : ι → ValuationSubring ℂ) (hW : ∀ la, (p : ℂ) ∈ (W la).nonunits)
    (jc : ι → (KW p →+* ℂ)) (z : ∀ la, AdmAt O.S O.κ (Fact.out : p.Prime) (hW la)), (∀ la, Pin (W la) (jc la)) ∧
    Term O.Y p w jc (fun la => mdlOf (z la) (jc la)) (fun la => rootOf (z la) (jc la))

end GlobalTheory.MixedLocalChains

end
