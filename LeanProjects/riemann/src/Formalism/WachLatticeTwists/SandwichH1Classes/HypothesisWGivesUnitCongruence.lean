import Formalism.WachLatticeTwists.SandwichH1Classes.PerturbationForEveryTwist

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

structure Lat (ℓ : ℕ) [Fact ℓ.Prime] (G : Type) [Group G] (r : ℕ) where
  ρ : G → Matrix (Fin r) (Fin r) ℤ_[ℓ]
  one : ρ 1 = 1
  mul : ∀ g h, ρ (g * h) = ρ h * ρ g

def Lat.sl {ℓ : ℕ} [Fact ℓ.Prime] {G : Type} [Group G] {r : ℕ} (L : Lat ℓ G r) {OC : Type} [CommRing OC]
    [Algebra ℤ_[ℓ] OC] (actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)) : SL actO r where
  Mx g := (L.ρ g).map (algebraMap ℤ_[ℓ] OC)
  one := by rw [L.one, Matrix.map_one _ (map_zero _) (map_one _)]
  mul := by
    intro g h
    rw [L.mul, Matrix.map_mul]
    congr 1
    ext i j
    simp

structure HypWc (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (r : ℕ) (ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ]) (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ]))
    (πs ξ : As) (M0 h0 : ℕ) where

  Xx : Matrix (Fin r) (Fin r) WC

  Xi : Matrix (Fin r) (Fin r) WC
  inv1 : Xx * Xi = 1
  inv2 : Xi * Xx = 1

  fixH : ∀ h ∈ H, Xx.map (act h) * ((ρ h).map (algebraMap ℤ_[ℓ] WC)) = Xx

  P : Matrix (Fin r) (Fin r) WC
  W1 : Xx.map φ = P * Xx

  P1 : Matrix (Fin r) (Fin r) As
  map_eq_xi_power_smul : (P1.map jA).map ι = (ι (jA ξ)) ^ M0 • P

  Q1 : Matrix (Fin r) (Fin r) As
  product_eq_xi_power_smul_one : P1 * Q1 = (ξ ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) As)

  Gm : Gg → Matrix (Fin r) (Fin r) As
  W2 : ∀ g, Xx.map (act g) * ((ρ g).map (algebraMap ℤ_[ℓ] WC)) = ((Gm g).map jA).map ι * Xx

  W3 : ∀ g i j, (Gm g - 1) i j ∈ Ideal.span {(ℓ : As), πs}

  W4 : ∀ E ∈ En, ∃ E' : Matrix (Fin r) (Fin r) As,
    Xx * E.map (algebraMap ℤ_[ℓ] WC) = (E'.map jA).map ι * Xx

structure Setup (ℓ : ℕ) [Fact ℓ.Prime] where

  Tt : TateTr ℓ

  As : Type

  AA : Type

  WC : Type

  OC : Type
  [cAs : CommRing As]
  [cAA : CommRing AA]
  [cWC : CommRing WC]
  [cOC : CommRing OC]
  [aAA : Algebra ℤ_[ℓ] AA]
  [aWC : Algebra ℤ_[ℓ] WC]
  [aOC : Algebra ℤ_[ℓ] OC]
  [tOC : TopologicalSpace OC]
  [trOC : IsTopologicalRing OC]
  [csOC : ContinuousConstSMul ℤ_[ℓ] OC]
  jA : As →+* AA
  ι : AA →+* WC
  φ : WC →+* WC

  ϑ : AA →+* OC

  ϑs : As →+* Tt.Om
  emb : Tt.Oi →+* OC

  Gg : Type
  [gGg : Group Gg]

  G : Type
  [gG : Group G]
  [tG : TopologicalSpace G]
  p : G →* Gg

  Hs : Subgroup Gg

  H : Subgroup G
  act : Gg →* (WC ≃+* WC)
  actA : Gg →* (AA ≃+* AA)
  actO : Gg →* (OC ≃ₐ[ℤ_[ℓ]] OC)
  χ : Gg →* ℤ_[ℓ]ˣ
  πs : As
  ξ : As
  x : As

  cx : Gg → As

  γ : Gg

  σ : As →+* As

  gg : G

  z : Tt.Om
  z' : Tt.Om

  ϖ : Tt.Om
  ϖ₁ : Tt.Om

  ϖ' : Tt.Om
  c : OC
  s : ℕ

attribute [instance] Setup.cAs Setup.cAA Setup.cWC Setup.cOC Setup.aAA Setup.aWC Setup.aOC Setup.tOC Setup.trOC
  Setup.csOC Setup.gGg Setup.gG Setup.tG

namespace Setup

variable {ℓ : ℕ} [Fact ℓ.Prime] (R : Setup ℓ)

def w : ℤ_[ℓ]ˣ := R.χ (R.p R.gg)

structure Facts (r M0 h0 : ℕ) : Prop where
  lemA : LemmaAProp R.ι R.φ r
  injι : Function.Injective R.ι
  injj : Function.Injective R.jA
  phix : R.φ (R.ι (R.jA R.x)) = R.ι (R.jA R.x * R.jA R.ξ)
  xinzd : ∀ a : R.WC, R.ι (R.jA R.ξ) * a = 0 → a = 0
  thx : (R.ϑ (R.jA R.x)) ^ (ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1)) * R.c = (ℓ : R.OC)
  eqι : ∀ g a, R.ι (R.actA g a) = R.act g (R.ι a)
  eqϑ : ∀ g a, R.ϑ (R.actA g a) = R.actO g (R.ϑ a)
  actZ : ∀ g (t : ℤ_[ℓ]), R.act g (algebraMap ℤ_[ℓ] R.WC t) = algebraMap ℤ_[ℓ] R.WC t
  algι : ∀ t : ℤ_[ℓ], R.ι (algebraMap ℤ_[ℓ] R.AA t) = algebraMap ℤ_[ℓ] R.WC t
  algϑ : ∀ t : ℤ_[ℓ], R.ϑ (algebraMap ℤ_[ℓ] R.AA t) = algebraMap ℤ_[ℓ] R.OC t
  gx : ∀ g, R.actA g (R.jA R.x) = R.jA (R.cx g) * R.jA R.x
  gσ : ∀ a, R.actA R.γ (R.jA a) = R.jA (R.σ a)
  embϑ : ∀ a, R.emb (algebraMap R.Tt.Om R.Tt.Oi (R.ϑs a)) = R.ϑ (R.jA a)
  lnzd : ∀ a : R.OC, (ℓ : R.OC) * a = 0 → a = 0
  σ1 : ∀ a, R.σ a - a ∈ Ideal.span {(ℓ : R.As), R.πs}
  σ2 : ∀ a ∈ Ideal.span {(ℓ : R.As), R.πs}, R.σ a - a ∈ (Ideal.span {(ℓ : R.As), R.πs}) ^ 2
  ϑπ : R.ϑs R.πs = R.ϖ'
  dv' : R.ϖ' ∣ (ℓ : R.Tt.Om)
  zz : R.z * R.z' = algebraMap ℤ_[ℓ] R.Tt.Om (ℓ : ℤ_[ℓ])
  ϖϖ : R.ϖ * R.ϖ₁ = algebraMap ℤ_[ℓ] R.Tt.Om (ℓ : ℤ_[ℓ])
  dvd : R.z * R.ϖ ∣ R.ϖ' ^ (ℓ ^ (R.s + n0 ℓ (M0 + h0)))
  pg : R.p R.gg = R.γ ^ (ℓ ^ (R.s + n0 ℓ (M0 + h0) + 1))
  fixx : R.actO (R.p R.gg) (R.ϑ (R.jA R.x)) = R.ϑ (R.jA R.x)
  s1 : 1 ≤ R.s
  s2 : ℓ = 2 → 2 ≤ R.s
  valγ : PadicInt.valuation ((R.χ R.γ : ℤ_[ℓ]) - 1) = R.s
  omtf : ∀ a : R.Tt.Om, (ℓ : ℤ_[ℓ]) • a = 0 → a = 0

def TateX (r : ℕ) : Prop :=
  IsAdicComplete (Ideal.span {R.ϖ}) (Fin r → R.Tt.Xm) ∧ R.Tt.T2 R.z

end Setup

def SL.ofFun {ℓ : ℕ} [Fact ℓ.Prime] {G : Type} [Group G] {OC : Type} [CommRing OC] [Algebra ℤ_[ℓ] OC]
    (actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)) {r : ℕ} (Um : G → Matrix (Fin r) (Fin r) OC) : SL actO r := by
  classical
  exact if h : Um 1 = 1 ∧ ∀ g h, Um (g * h) = (Um h).map (actO g) * Um g then ⟨Um, h.1, h.2⟩
    else ⟨fun _ => 1, rfl, fun g h => by
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]⟩

def matrixMapOnH1 {ℓ : ℕ} [Fact ℓ.Prime] {G G' : Type} [Group G] [Group G'] [TopologicalSpace G'] {OC : Type}
    [CommRing OC] [Algebra ℤ_[ℓ] OC] [TopologicalSpace OC] [IsTopologicalRing OC]
    [ContinuousConstSMul ℤ_[ℓ] OC] {actO : G →* (OC ≃ₐ[ℤ_[ℓ]] OC)} {r : ℕ} (S S' : SL actO r)
    (Y : Matrix (Fin r) (Fin r) OC) (p : G' →* G) :
    H1 (S.rep.comp p) →ₗ[ℤ_[ℓ]] H1 (S'.rep.comp p) := by
  classical
  exact if h : Inter S S' Y then (h.eqMap.comap p).onH else 0

section W

variable {ℓ : ℕ} [Fact ℓ.Prime] (R : Setup ℓ) {r : ℕ} (L : Lat ℓ R.Gg r)
  {En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])} {M0 h0 : ℕ}
  (W : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r L.ρ En R.πs R.ξ M0 h0)

def UmW (g : R.Gg) : Matrix (Fin r) (Fin r) R.OC :=
  (((R.cx g) ^ M0 • W.Gm g).map R.jA).map R.ϑ

def VmW : Matrix (Fin r) (Fin r) R.Tt.Om := (W.Gm (R.p R.gg)).map R.ϑs

def repT (i : ℤ) : Representation ℤ_[ℓ] R.G (Fin r → R.OC) :=
  (((L.sl R.actO).twist R.χ i).rep).comp R.p

def repD (i : ℤ) : Representation ℤ_[ℓ] R.G (Fin r → R.OC) :=
  (((SL.ofFun R.actO (UmW R L W)).twist R.χ i).rep).comp R.p

def pieceW (Y Y' : Matrix (Fin r) (Fin r) R.OC) (i : ℤ)
    (infm : (Fin r → R.Tt.Om) →ₗ[ℤ_[ℓ]] H1 (repD R L W i))
    (infX : (Fin r → R.Tt.Xm) →ₗ[ℤ_[ℓ]] H1 (repD R L W i)) :
    Piece ℓ (ModuleCat.of ℤ_[ℓ] (H1 (repT R L i))) where
  E := ModuleCat.of ℤ_[ℓ] (H1 (repD R L W i))
  HH := ModuleCat.of ℤ_[ℓ] (H1 ((repD R L W i).comp R.H.subtype))
  Wm := ModuleCat.of ℤ_[ℓ] (Fin r → R.Tt.Om)
  WX := ModuleCat.of ℤ_[ℓ] (Fin r → R.Tt.Xm)
  gm := R.Tt.gmI (VmW R L W) R.w i
  gX := R.Tt.gXI (VmW R L W) R.w i
  lam := matrixMapOnH1 ((L.sl R.actO).twist R.χ i) ((SL.ofFun R.actO (UmW R L W)).twist R.χ i) Y' R.p
  io := matrixMapOnH1 ((SL.ofFun R.actO (UmW R L W)).twist R.χ i) ((L.sl R.actO).twist R.χ i) Y R.p
  infm := infm
  infX := infX
  res := H1.res (repD R L W i) R.H.subtype continuous_subtype_val

def InfPin (i : ℤ) (infm : (Fin r → R.Tt.Om) →ₗ[ℤ_[ℓ]] H1 (repD R L W i))
    (infX : (Fin r → R.Tt.Xm) →ₗ[ℤ_[ℓ]] H1 (repD R L W i)) : Prop :=
  (∀ v, ∃ c : Z1 (repD R L W i), H1.mk (repD R L W i) c = infm v ∧ (∀ h ∈ R.H, c.1 h = 0) ∧
    c.1 R.gg = fun k => R.emb (algebraMap R.Tt.Om R.Tt.Oi (v k))) ∧
  ∀ v, ∃ c : Z1 (repD R L W i), H1.mk (repD R L W i) c = infX v ∧ (∀ h ∈ R.H, c.1 h = 0) ∧
    c.1 R.gg = fun k => R.emb (v k : R.Tt.Oi)

end W

def StatWSandwichC : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Setup ℓ) (r : ℕ) (L : Lat ℓ R.Gg r)
    (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])) (M0 h0 : ℕ)
    (W : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r L.ρ En R.πs R.ξ M0 h0),
    R.Facts r M0 h0 →
    ∃ (A : Matrix (Fin r) (Fin r) R.AA) (Y' : Matrix (Fin r) (Fin r) R.OC),
      A.map R.ι = (R.ι (R.jA R.x)) ^ M0 • W.Xx ∧
      A.map R.ϑ * Y' = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) ∧
      Y' * A.map R.ϑ = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC)

def StatGmCocycle : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Setup ℓ) (r : ℕ) (L : Lat ℓ R.Gg r)
    (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])) (M0 h0 : ℕ)
    (W : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r L.ρ En R.πs R.ξ M0 h0),
    R.Facts r M0 h0 → W.Gm 1 = 1 ∧ ∀ h, W.Gm (R.γ * h) = (W.Gm h).map R.σ * W.Gm R.γ

def StatGmIter : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Setup ℓ) (r : ℕ) (L : Lat ℓ R.Gg r)
    (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])) (M0 h0 : ℕ)
    (W : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r L.ρ En R.πs R.ξ M0 h0),
    R.Facts r M0 h0 → ∀ (k : ℕ) (i : Fin r),
      W.Gm (R.γ ^ k) i = (⇑(gamN R.σ (W.Gm R.γ)))^[k] (Pi.single i 1)

def HypothesisWGivesUnitCongruence : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Setup ℓ) (r : ℕ) (L : Lat ℓ R.Gg r)
    (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])) (M0 h0 : ℕ)
    (W : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r L.ρ En R.πs R.ξ M0 h0),
    R.Facts r M0 h0 → ∀ a b, R.z * R.ϖ ∣ (VmW R L W - 1) a b

def StatWInter : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Setup ℓ) (r : ℕ) (L : Lat ℓ R.Gg r)
    (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])) (M0 h0 : ℕ)
    (W : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r L.ρ En R.πs R.ξ M0 h0)
    (A : Matrix (Fin r) (Fin r) R.AA), R.Facts r M0 h0 →
    A.map R.ι = (R.ι (R.jA R.x)) ^ M0 • W.Xx →
    ∀ g, (A.map R.ϑ).map (R.actO g) * (L.sl R.actO).Mx g = UmW R L W g * A.map R.ϑ

def StatUmVm : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Setup ℓ) (r : ℕ) (L : Lat ℓ R.Gg r)
    (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])) (M0 h0 : ℕ)
    (W : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r L.ρ En R.πs R.ξ M0 h0),
    R.Facts r M0 h0 →
    UmW R L W (R.p R.gg) = (VmW R L W).map (fun a => R.emb (algebraMap R.Tt.Om R.Tt.Oi a))

def StatPieceW : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Setup ℓ) (r : ℕ) (L : Lat ℓ R.Gg r)
    (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])) (M0 h0 : ℕ)
    (W : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r L.ρ En R.πs R.ξ M0 h0)
    (U : Finset ℤ) (A : Matrix (Fin r) (Fin r) R.AA) (Y' : Matrix (Fin r) (Fin r) R.OC),
    R.Facts r M0 h0 → R.TateX r → A.map R.ι = (R.ι (R.jA R.x)) ^ M0 • W.Xx →
    A.map R.ϑ * Y' = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
    Y' * A.map R.ϑ = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
    R.Tt.HTdec (VmW R L W) R.w U →
    ∀ (i : ℤ) (infm : (Fin r → R.Tt.Om) →ₗ[ℤ_[ℓ]] H1 (repD R L W i))
      (infX : (Fin r → R.Tt.Xm) →ₗ[ℤ_[ℓ]] H1 (repD R L W i)),
      (pieceW R L W (A.map R.ϑ) Y' i infm infX).InfRes → (pieceW R L W (A.map R.ϑ) Y' i infm infX).T4 →
      (pieceW R L W (A.map R.ϑ) Y' i infm infX).Inputs R.w U i

structure LLRest (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (Gr : ℕ → Md ℓ) where

  HK : Md ℓ

  Hm : ℕ → Md ℓ
  f : ∀ k, Gr k →ₗ[ℤ_[ℓ]] Hm (k + 1)
  p : ∀ k, Hm (k + 1) →ₗ[ℤ_[ℓ]] Hm k
  res : HK →ₗ[ℤ_[ℓ]] Hm n
  cor : Hm n →ₗ[ℤ_[ℓ]] HK

def LLRest.toLL {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} {Gr : ℕ → Md ℓ} (X : LLRest ℓ n Gr)
    (piece : ∀ k, Piece ℓ (Gr k)) : LLData ℓ n :=
  { HK := X.HK, Hm := X.Hm, Gr := Gr, piece := piece, f := X.f, p := X.p, res := X.res, cor := X.cor }

def StatLLW : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Setup ℓ) (r : ℕ) (L : Lat ℓ R.Gg r)
    (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ])) (M0 h0 : ℕ)
    (W : HypWc ℓ R.As R.AA R.WC R.jA R.ι R.φ R.Gg R.Hs R.act r L.ρ En R.πs R.ξ M0 h0)
    (U : Finset ℤ) (A : Matrix (Fin r) (Fin r) R.AA) (Y' : Matrix (Fin r) (Fin r) R.OC),
    R.Facts r M0 h0 → R.TateX r → A.map R.ι = (R.ι (R.jA R.x)) ^ M0 • W.Xx →
    A.map R.ϑ * Y' = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
    Y' * A.map R.ϑ = (ℓ : R.OC) • (1 : Matrix (Fin r) (Fin r) R.OC) →
    R.Tt.HTdec (VmW R L W) R.w U →
    ∀ (a : ℤ) (n d : ℕ) (X : LLRest ℓ n (fun k => ModuleCat.of ℤ_[ℓ] (H1 (repT R L (a + k)))))
      (infm : ∀ k : ℕ, (Fin r → R.Tt.Om) →ₗ[ℤ_[ℓ]] H1 (repD R L W (a + k)))
      (infX : ∀ k : ℕ, (Fin r → R.Tt.Xm) →ₗ[ℤ_[ℓ]] H1 (repD R L W (a + k))), d ≠ 0 →
      (∀ k : ℕ, InfPin R L W (a + k) (infm k) (infX k) ∧
        (pieceW R L W (A.map R.ϑ) Y' (a + k) (infm k) (infX k)).InfRes ∧
        (pieceW R L W (A.map R.ϑ) Y' (a + k) (infm k) (infX k)).T4) →
      (X.toLL fun k => pieceW R L W (A.map R.ϑ) Y' (a + k) (infm k) (infX k)).LES →
      (X.toLL fun k => pieceW R L W (A.map R.ϑ) Y' (a + k) (infm k) (infX k)).T5 →
      (X.toLL fun k => pieceW R L W (A.map R.ϑ) Y' (a + k) (infm k) (infX k)).CorRes d →
      TorsKilled ℓ X.HK (cLL ℓ (mOf ℓ R.s (M0 + h0)) U a (a + n) d)

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
