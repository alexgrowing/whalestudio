import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Links

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable (R : RealDat D A Ks) (F : Face D A)

abbrev num (C CH : ℝ) : IndefNum A.fam.base := (F.fc (R.toCx F).zs).Z.num C CH

def LStable : Prop := (R.toCx F).zs.Stable

def LBlock : Prop := (R.toCx F).zs.InBlock

def LRatZ : Prop := (R.toCx F).RatZ

def LPos : Prop := ∀ b, (lv (F.fc (R.toCx F).zs) b).Pos

def LProviso : Prop := ∀ b, (lv (F.fc (R.toCx F).zs) b).Proviso

def LTypes : Prop := ∀ b, (lv (F.fc (R.toCx F).zs) b).Types

def LPartsOrth : Prop := ∀ b, (R.toCx F).PartsOrth b (fc := F.fc)

def LIota : Prop := ∀ b, (R.toCx F).H2 F.cr b

def LRatMu : Prop := ∀ b, (R.toCx F).RATmu F.cr b

def LPartsE : Prop := ∀ b, (R.toCx F).H3 F.cr b

def LPosScal : Prop := 0 < R.kap ∧ ∀ i t p v, 0 < R.lam i t p v

def LScalE : Prop := ∀ b, (R.toCx F).H4 F.cr b

def LUnif : Prop :=
  ∀ i σ, (∀ (n : ℕ) (b : Fin n → (Fin (R.nW i) → D.what₂.LL)), LinearIndependent D.what₂.LL b →
      LinearIndependent ℂ fun k => (R.FW i).j σ (b k)) ∧
    Submodule.span ℂ (Set.range ((R.FW i).j σ)) = ⊤ ∧
    ∀ g x, (R.HW i σ).e ((R.FW i).j σ ((R.FW i).ρ g x)) = σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) •
      postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e ((R.FW i).j σ x))

def LLevelW : Prop := ∀ b i σ, R.WS F b i σ = (R.Wat i σ (R.levL F b σ)).comap (R.HW i σ).e

def LIntegral : Prop := ∀ i, (R.FW i).IsKsForm ∧ (R.FW i).MKFull ∧ (R.FW i).MKStable

def LMLat : Prop := ∀ b, (R.toCx F).MLat b

def LTheta : Prop := ∀ b, (R.toCx F).H5 F.cr b

def LRatTh : Prop := ∀ b, (R.toCx F).RATth F.cr b

def LPartsW : Prop := ∀ b, (R.toCx F).H3W F.cr b

def LScalW : Prop := ∀ b, (R.toCx F).ThmA F.cr b

def LScalConj : Prop := ∀ b, (R.toCx F).GalD F.cr b

def LDims : Prop := ∀ b, ((R.toCx F).data F.cr b).DimensionsOfPartsAgree

def LCovol (C CH : ℝ) : Prop := ((R.toCx F).data F.cr false).L3 (R.num F C CH)

def LOnto (C CH : ℝ) : Prop := ((R.toCx F).data F.cr false).ON (R.num F C CH)

def LLamLow (C CH : ℝ) : Prop := ((R.toCx F).data F.cr true).L6 (R.num F C CH)

def LPassage (C CH : ℝ) : Prop := Passage (R.num F C CH) ((R.toCx F).data F.cr false) ((R.toCx F).data F.cr true)

def LFun (C CH : ℝ) : Prop := ((R.toCx F).data F.cr false).FUN (R.num F C CH)

variable {R F}

def LPair (Y : RealCol R F) : Prop := ((R.toCx F).colOf F.cr Y.toCol).PairingFactorsThroughPeriods

def LPeriod (Y : RealCol R F) : Prop := ((R.toCx F).colOf F.cr Y.toCol).L1e

end RealDat

open RealDat in

structure ConcreteLinks (R : RealDat D A Ks) (F : Face D A) (Y : RealDat.RealCol R F) (C CH : ℝ) : Prop where
  stable : R.LStable F
  block : R.LBlock F
  ratZ : R.LRatZ F
  pos : R.LPos F
  proviso : R.LProviso F
  types : R.LTypes F
  partsOrth : R.LPartsOrth F
  iota : R.LIota F
  ratMu : R.LRatMu F
  partsE : R.LPartsE F
  posScal : R.LPosScal
  scalE : R.LScalE F
  unif : R.LUnif
  levelW : R.LLevelW F
  integral : R.LIntegral
  mLat : R.LMLat F
  theta : R.LTheta F
  ratTh : R.LRatTh F
  partsW : R.LPartsW F
  scalW : R.LScalW F
  scalConj : R.LScalConj F
  dims : R.LDims F
  covol : R.LCovol F C CH
  onto : R.LOnto F C CH
  lamLow : R.LLamLow F C CH
  pair : LPair Y
  period : LPeriod Y
  passage : R.LPassage F C CH
  fun0 : R.LFun F C CH

namespace RealDat

variable {R : RealDat D A Ks} {F : Face D A}

theorem nP_pos (b : Bool) : 0 < nP F b := by
  unfold nP
  exact_mod_cast Nat.card_pos

theorem h0 (h : R.IsTup F) : (R.toCx F).H0 := by
  refine ⟨h.mu_conj, fun w => ⟨fun hw => h.mu_ne w hw, fun hne => ?_⟩⟩
  by_contra hw
  exact hne (h.mu_off w hw)

theorem untw (h : R.IsTup F) (C CH : ℝ) : ((R.toCx F).data F.cr false).Untwisted (R.num F C CH) := by
  intro w hw j
  have hW : ¬ R.NonzeroIndexPlace F w := fun hh => hw (h.tw w hh)
  have hμ : ((R.toCx F).data F.cr false).μ w = A.μ0 := h.mu_off w hw
  have hn : ¬ (((R.toCx F).data F.cr false).Iw j A.μ0 w ≠ 0 ∨ ((R.toCx F).data F.cr false).Iw j A.μ0 (conjPl w) ≠ 0 ∨
    jw ((lv (F.fc (R.toCx F).zs) false).HT j A.μ0) w ((lv (F.fc (R.toCx F).zs) false).Tl j A.μ0) ≠ 0 ∨
    (F.Zsc (R.toCx F).zs).F0 w j ≠ 0 ∨ (F.Zsc (R.toCx F).zs).F0 (conjPl w) j ≠ 0) := fun hh => hW ⟨w, Or.inl rfl, j, hh⟩
  push Not at hn
  obtain ⟨h1, h2, h3, h4, -⟩ := hn
  refine ⟨?_, h4⟩
  unfold IndefData.Aw
  rw [hμ, h1, h2, h3]
  simp

theorem ewNorm (b : Bool) : (R.toCx F).EWnorm b := by
  intro j x y
  show cj _ (inner ℂ ((((Real.sqrt (nP F b) : ℝ) : ℂ)) • ((Tw.out x : R.WS F b j (sg0 D A)) : (R.HW j (sg0 D A)).H))
      ((((Real.sqrt (nP F b) : ℝ) : ℂ)) • ((Tw.out y : R.WS F b j (sg0 D A)) : (R.HW j (sg0 D A)).H))) =
    ((nP F b : ℝ) : ℂ) * cj _ (inner ℂ ((Tw.out x : R.WS F b j (sg0 D A)) : (R.HW j (sg0 D A)).H)
      ((Tw.out y : R.WS F b j (sg0 D A)) : (R.HW j (sg0 D A)).H))
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (nP_pos b).le, map_mul, cj_ofReal]
  rfl

theorem kForm (hU : R.LUnif) (b : Bool) : (R.toCx F).KForm b := by
  intro j v
  have hc : (((Real.sqrt (nP F b))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have := Real.sqrt_pos.2 (nP_pos (F := F) b)
    exact_mod_cast (inv_pos.2 this).ne'
  have hL : LinearIndependent D.what₂.LL (R.bL F b j) :=
    (Module.finBasis D.what₂.LL (R.WL F b j)).linearIndependent.map' (R.WL F b j).subtype (Submodule.ker_subtype _)
  have h1 : LinearIndependent ℂ (R.bC F b j (sgAt D.what₂.embLL v)) :=
    ((hU j _).1 _ _ hL).units_smul fun _ => Units.mk0 _ hc
  have h2 := linearIndependent_span h1
  have h3 : Submodule.span ℂ (Set.range fun k => (⟨R.bC F b j (sgAt D.what₂.embLL v) k, Submodule.subset_span ⟨k, rfl⟩⟩ :
      R.WS F b j (sgAt D.what₂.embLL v))) = ⊤ := Submodule.span_range_subtype_eq_top_iff _ _ |>.2 rfl
  exact ⟨Tw.linInd (E := R.WS F b j (sgAt D.what₂.embLL v)) _ h2, Tw.span_top (E := R.WS F b j (sgAt D.what₂.embLL v)) _ h3⟩

theorem cxLinks {Y : RealCol R F} {C CH : ℝ} (hC : R.Char F) (hL : ConcreteLinks R F Y C CH) :
    (R.toCx F).CxLinks F.cr Y.toCol C CH where
  stable := hL.stable
  inBlock := hL.block
  ratZ := hL.ratZ
  pos := hL.pos
  proviso := hL.proviso
  types := hL.types
  partsOrth := hL.partsOrth
  h0 := h0 hC.tup
  h2 := hL.iota
  ratMu := hL.ratMu
  h3 := hL.partsE
  h4pos := ⟨fun _ => hL.posScal.1, hL.posScal.2, nP_pos⟩
  h4 := hL.scalE
  kForm := kForm hL.unif
  mLat := hL.mLat
  ewNorm := ewNorm
  h5 := hL.theta
  ratTh := hL.ratTh
  h3W := hL.partsW
  thmA := hL.scalW
  galD := hL.scalConj
  l1d := hL.dims
  l3 := hL.covol
  on := hL.onto
  l6 := hL.lamLow
  l1b := hL.pair
  l1e := hL.period
  untw := untw hC.tup C CH
  passage := hL.passage
  fun0 := hL.fun0

end RealDat

def concretePkg {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep) (R : RealDat D A Ks) (F : Face D A)
    (Y : RealDat.RealCol R F) (C CH : ℝ) (hC : R.Char F) (_hY : Y.Char) (hL : ConcreteLinks R F Y C CH) :
    IndefPkg A.fam.amb (faceOf A F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) C CH :=
  cxPkgF A hOk hsep F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx F) Y.toCol C CH (RealDat.cxLinks hC hL)

theorem concretePkg_spec {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep) (R : RealDat D A Ks) (F : Face D A)
    (Y : RealDat.RealCol R F) (C CH : ℝ) (hC : R.Char F) (hY : Y.Char) (hL : ConcreteLinks R F Y C CH) :
    (concretePkg hOk hsep R F Y C CH hC hY hL).Zs = (R.toCx F).zs ∧
      (concretePkg hOk hsep R F Y C CH hC hY hL).core.base.toIndefData = (R.toCx F).data F.cr false ∧
      (concretePkg hOk hsep R F Y C CH hC hY hL).core.cols.toIndefData = (R.toCx F).data F.cr true ∧
      (concretePkg hOk hsep R F Y C CH hC hY hL).core.base.μ = R.mu := ⟨rfl, rfl, rfl, rfl⟩

theorem concreteToPkg {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep) (R : RealDat D A Ks) (F : Face D A)
    (Y : RealDat.RealCol R F) (C CH : ℝ) (hC : R.Char F) (hY : Y.Char) (hL : ConcreteLinks R F Y C CH) :
    Nonempty (IndefPkg A.fam.amb (faceOf A F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) C CH) :=
  ⟨concretePkg hOk hsep R F Y C CH hC hY hL⟩

end Links

end Formalism.IndefR.Links

end
