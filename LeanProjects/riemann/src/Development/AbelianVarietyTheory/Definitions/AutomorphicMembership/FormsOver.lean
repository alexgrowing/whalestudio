import Mathlib
import Formalism.LocalToGlobal.LatticeGeometry.ViewsC
import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam

variable {D : D7} {A : Amb D}

structure CmList (A : Amb D) : Type where
  ψ : D.what₂.Tau ≃ GlobalTheory.AllWt.Psi A.H
  ψ_val : ∀ t, (ψ t).1 = DV.tauEmb D t

section One

variable {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (L : CmList A)

theorem Lv.good_σ₀ (κ : Lv A) : Formalism.L2.PjFree.GoodEmb κ.c κ.σ₀ := rfl

theorem FinalTheorems.isUnf : Formalism.L2.PjFree.IsUnf (s.U κ.σ₀) := (s.unf _ κ.good_σ₀).1

instance FinalTheorems.compNe : Nonempty s.Comp := (s.unf _ κ.good_σ₀).2.1

abbrev FinalTheorems.Bd : Type :=
  ∀ k : s.Comp, GlobalTheory.HodgeDomain.BdData D.what₂.Tau j (N - j)
    (GlobalTheory.TrueCx.gammaU ((s.U κ.σ₀).X k) (GlobalTheory.TrueCx.le_of_isUnf _ s.isUnf S.p_eq) (GlobalTheory.TrueCx.cmEquiv _ s.isUnf L.ψ k))

def FinalTheorems.cx (B : s.Bd L) (fl : s.Comp → D.what₂.Tau → ℂˣ) : CxPkg D.what₂.Tau N j s.Comp :=
  GlobalTheory.TrueCx.cxTrue (s.U κ.σ₀) s.isUnf S.p_eq (lt_of_lt_of_le two_pos S.two_le) L.ψ B fl

def Sig.wt (S : Sig A N j) (L : CmList A) : (D.what₂.Tau → Fin N → ℤ) →+ GlobalTheory.AllWt.Weight S.Dw where
  toFun la := fun τ i => la (L.ψ.symm τ) (Fin.cast S.rank_eq i)
  map_zero' := rfl
  map_add' _ _ := rfl

example (S : Sig A N j) (L : CmList A) (la : D.what₂.Tau → Fin N → ℤ) (t : D.what₂.Tau) (i : Fin (S.Dw.p + S.Dw.q)) :
    S.wt L la (L.ψ t) i = la t (Fin.cast S.rank_eq i) := by
  simp [Sig.wt]

def FinalTheorems.Lw (Φ : s.Flag) (k : s.Comp) : (D.what₂.Tau → Fin N → ℤ) →+ (Φ.C k).Y.Dv :=
  AddMonoidHom.mk' (fun la => (Φ.C k).Lw (S.wt L la)) fun a b => by
    have h := GlobalTheory.AllWt.exOf_add (Dw := S.Dw) (S.wt L a) (S.wt L b) 0 0
    rw [add_zero] at h
    simp only [FlagCpt.Lw, map_add, h]

variable (C : CxSt D.what₂.LL) (K : CutSt C) (R : ResSt C)

def FinalTheorems.alg (Φ : s.Flag) (hd : ∀ k, (Φ.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N)
    (Mb : ℝ → (D.what₂.Tau → Fin N → ℝ) → ℚ → ∀ k, Adl C (Φ.C k).Y) :
    AlgPkg (geoOf C K R) D.what₂.Tau N s.Comp where
  Yv k := (Φ.C k).Y
  Ybd k := (Φ.C k).Ybd
  bd k := (Φ.C k).bd
  bd_supp _ := rfl
  Lw k := s.Lw L Φ k
  dim_eq := hd
  degA _ M := Adl.deg M
  degA_ofW k Δ W ι := deg_ofW C _ Δ W ι
  degA_twist _ M ci cf := deg_twist M ci cf
  semipos M := ∀ k, Adl.SemiPos (M k)
  nefFib M := ∀ k, Adl.NefFib (M k)
  Mbar := Mb

structure Kit (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (ng : NgPkg) : Type 1 where
  Φ : s.Flag
  dim_eq : ∀ k, (Φ.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N
  key : KeySec s.Xo κ.c
  B : s.Bd L
  fl : s.Comp → D.what₂.Tau → ℂˣ
  Mb : ℝ → (D.what₂.Tau → Fin N → ℝ) → ℚ → ∀ k, Adl C (Φ.C k).Y
  pad : PadPkg D N j s.Comp jC ng
  levIn : ∀ M, pad.levIn M ↔ κ.inK M

end One

section Fam

variable (F : SrcFam A) (L : CmList A) (C : CxSt D.what₂.LL) (K : CutSt C) (R : ResSt C)
  (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (ng : NgPkg)

abbrev Kits : Type 1 := ∀ N j hN hj (κ : Lv A), Kit (F.src N j hN hj κ) L C jC ng

variable {F L C jC ng} (k : Kits F L C jC ng)

abbrev Kits.at (w : Dat D (Lv A)) : Kit (F.at w) L C jC ng := k w.N w.j w.two_le w.j_le w.κ

def shimOf (w : Dat D (Lv A)) : ShimU D (geoOf C K R) jC ng w where
  Comp := (F.at w).Comp
  cx := (F.at w).cx L (k.at w).B (k.at w).fl
  alg := (F.at w).alg L C K R (k.at w).Φ (k.at w).dim_eq (k.at w).Mb
  pad := (k.at w).pad

abbrev FormsOver : Type 1 :=
  FormsPkg D (geoOf C K R) (fun j => (datW D F.κg j).N) (fun j => (shimOf K R k (datW D F.κg j)).Comp)
    (fun j => (shimOf K R k (datW D F.κg j)).alg)
    (fun j p => ((shimOf K R k (datW D F.κg j)).pad.loc p).Pt ((shimOf K R k (datW D F.κg j)).pad.loc p).YY)

def famOf (hg : F.κg.primes = Finset.univ.image D.host.g) (P : FormsOver K R k) : ShimFam D (geoOf C K R) (Lv A) where
  levPr := Lv.primes
  levPr_prime _ _ hp := Nat.prime_of_mem_primeFactors hp
  κg := F.κg
  levPr_κg := hg
  jC := jC
  ng := ng
  U := shimOf K R k
  forms := P

example (hg : F.κg.primes = Finset.univ.image D.host.g) (P : FormsOver K R k) (w : Dat D (Lv A)) :
    ((famOf K R k hg P).U w).Comp = (F.at w).Comp := rfl

end Fam

section Comparison₂

def ambOf (Q : Par D) (h : Q.PinHost) : Amb D := ⟨Q.H, h.1, h.2.1, h.2.2.1⟩

example (Q : Par D) (h : Q.PinHost) : (ambOf Q h).H = Q.H := rfl

abbrev MD {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : Type 1 :=
  Σ (l : Level H) (Dw : Datum H), Moduli Dw l

def trRul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {m m' : MD H} (h : m = m')
    {c : Coeff m.1} {c' : Coeff m'.1} (hle : c.F ≤ c'.F) (f : Rul m.2.2 c) : Rul m'.2.2 c' := by
  subst h; exact GlobalTheory.FieldBC.rulBC hle f

structure ParTie (Q : Par D) (h : Q.PinHost) (F : SrcFam (ambOf Q h)) : Prop where
  same : ∀ j, InR D j → (⟨Q.l, Q.Dw j, Q.Xo j⟩ : MD Q.H) =
    ⟨F.κg.l, (F.sig _ _ (datW D F.κg j).two_le (datW D F.κg j).j_le).Dw, (F.at (datW D F.κg j)).Xo⟩
  le : Q.c.F ≤ F.κg.c.F

variable {T : Top D} (h : LawsP T) {F : SrcFam (ambOf T.Q h.pins.1)} (t : ParTie T.Q h.pins.1 F) {L : CmList (ambOf T.Q h.pins.1)}
  {C : CxSt D.what₂.LL} (K : CutSt C) (R : ResSt C) {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
  (k : Kits F L C jC ng)

def cmpAt {j : ℕ} (hj : InR D j) (n : ℕ) (i : (F.at (datW D F.κg j)).Comp) (f : T.R j) :
    ((k.at (datW D F.κg j)).Φ.C i).Y.Fn :=
  ((k.at (datW D F.κg j)).Φ.C i).val
    ((show Rul (F.at (datW D F.κg j)).Xo (datW D F.κg j).κ.c from trRul (t.same j hj) (c := T.Q.c) (c' := F.κg.c) t.le f) *
      (k.at (datW D F.κg j)).key.ρ.val ^ (n / 2))

structure FormsAre (P : FormsOver K R k) : Prop where
  base : P.toWeightFamilies = recB h.toLawsCore
  kL : ∀ (x : P.KO) (x' : T.Q.c.F), HEq x x' → D.what₂.embLL (P.kL x) = (x' : ℂ)
  cmp : ∀ j (hj : InR D j) w i (f : P.Cusp j w) (f' : (recB h.toLawsCore).Cusp j w), HEq f f' →
    P.cmp j w i f = cmpAt h t k hj w.n i f'.1
  pts : ∀ j (_ : InR D j) (la : HeightOneSpectrum (𝓞 P.KO)) (la' : HeightOneSpectrum (𝓞 T.Q.c.F)), HEq la la' →
    ∃ e : P.Pt j la ≃ T.PtA j la', (∀ y, j < D.R.m → HEq (P.pt66 j la y) (imgV (e y))) ∧
      ∀ y w (f : P.Cusp j w) (f' : (recB h.toLawsCore).Cusp j w), HEq f f' → P.vAtC j la y w f = vAtV (e y) f'.1
  th : ∀ j (hj : InR D j) w, HEq (P.thAll j w) ((recPJ h j hj).thAll w) ∧ HEq (P.shortTh j w) ((recPJ h j hj).shortTh w)

def PtsTie : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ p,
  T.G.PY j p = ((k.at (datW D F.κg j)).pad.loc p).Pt ((k.at (datW D F.κg j)).pad.loc p).YY

end Comparison₂

end GlobalTheory.ShFam
