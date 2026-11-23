import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def IntFrame (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : IsAffineOpen U) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)) : Prop :=
  (∀ σ, ∃ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)) (e : Fin (Dw.mult σ) ↪ Fin n),
    (∀ i, v (e i) = w σ i) ∧ (∀ i, IsTanAtG (Y Z.i).t (hU.fromSpec ≫ Z.π) (v i)) ∧
    ∀ u, IsTanAtG (Y Z.i).t (hU.fromSpec ≫ Z.π) u → ∃! cf, IsCombAtG (Y Z.i).t (hU.fromSpec ≫ Z.π) v cf u) ∧
  ∀ (k : Type) [Field k] (φ : Γ(Z.X, U) →+* k), Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn →
    Z.FlagAt (spMap φ ≫ hU.fromSpec) (w.bc φ)

def HasDR (Z : Mdl Y i₀) : Prop :=
  (∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) ∧
  ∀ x : Z.X, ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), x ∈ U ∧ IntFrame Z hU w

def IsDRFlag (Z Z' : Mdl Y i₀) : Prop :=
  Z'.i = Z.i ∧ HasDR Z' ∧ (∃ f, IsMap Z' Z f) ∧ ∀ Z'' : Mdl Y i₀, HasDR Z'' → (∃ g, IsMap Z'' Z g) → ∃ h, IsMap Z'' Z' h

def IsGrLB (Z : Mdl Y i₀) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) (L : LB Z.X) : Prop :=
  L.IsLB ∧ ∃ (hU : ∀ i, IsAffineOpen (L.U i)) (w : ∀ i, Vecs Dw (Y Z.i).t Γ(Z.X, L.U i)), (∀ i, IntFrame Z (hU i) (w i)) ∧
    ∀ (i i' : L.ι) (k : Type) [Field k] (φ : Γ(Z.X, L.U i) →+* k) (φ' : Γ(Z.X, L.U i') →+* k)
      (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k),
      spMap φ ≫ (hU i).fromSpec = spMap φ' ≫ (hU i').fromSpec → Set.range (spMap φ ≫ (hU i).fromSpec) ⊆ Z.opn →
      (∀ σ a, ∃ cf : Fin (Dw.mult σ) → k, cf a = d σ a ∧ (∀ b, a < b → cf b = 0) ∧
        IsCombAtG (Y Z.i).t (spMap φ ≫ (hU i).fromSpec ≫ Z.π) ((w i').bc φ' σ) cf ((w i).bc φ σ a)) →
      valR (spMap φ ≫ (hU i).fromSpec) _ (L.g i i').val = ∏ σ, ∏ a, d σ a ^ e σ a

def Mdl.genO (Z : Mdl Y i₀) : Z.X.Opens := Z.X.basicOpen ((p : ℕ) : Γ(Z.X, ⊤))

def Mdl.Pt.ev {Z : Mdl Y i₀} (y : Z.Pt) {U : Z.X.Opens} (h : ⊤ ≤ y.z ⁻¹ᵁ U) : Γ(Z.X, U) →+* ↥(intO ↥y.C.S) :=
  (Scheme.ΓSpecIso (CommRingCat.of ↥(intO ↥y.C.S))).hom.hom.comp (y.z.appLE U ⊤ h).hom

def Mdl.nrm {Z : Mdl Y i₀} (F : Z.X.Modules) (f : Γ(F, Z.genO)) (y : Z.Pt) : ℝ :=
  sSup {r | ∃ (U : Z.X.Opens) (_ : IsAffineOpen U) (h : ⊤ ≤ y.z ⁻¹ᵁ U) (k : ℕ) (g : Γ(F, U))
    (lam : Γ(F, U) →ₛₗ[y.ev h] ↥(intO ↥y.C.S)),
    (F.presheaf.map (homOfLE (inf_le_left : U ⊓ Z.genO ≤ U)).op).hom g =
      p ^ k • (F.presheaf.map (homOfLE (inf_le_right : U ⊓ Z.genO ≤ Z.genO)).op).hom f ∧
    r = ‖((lam g : ↥(intO ↥y.C.S)) : ↥y.C.S)‖ * (p : ℝ) ^ k}

end Free

variable {D : D7} {A : Amb D} {N j : ℕ}

structure At (S : Sig A N j) (κ : Lv A) (p : ℕ) : Type where
  hp : p.Prime
  W : ValuationSubring ℂ
  hW : (p : ℂ) ∈ W.nonunits
  B : Bases (S.sys.Y p W hp hW) ⟨κ.l, κ.c, κ.good p hp⟩
  YY : Mdl (S.sys.Y p W hp hW) ⟨κ.l, κ.c, κ.good p hp⟩
  isYY : IsDRFlag (B.X none) YY
  hasDat : ∀ (Z : Mdl (S.sys.Y p W hp hW) ⟨κ.l, κ.c, κ.good p hp⟩) (y : Z.Pt),
    Nonempty (DatAt (S.sys.Y p W hp hW Z.i) y.P)

variable {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (a : At S κ p)

abbrev Y : LocalSystem S.Xo p a.W := S.sys.Y p a.W a.hp a.hW

abbrev Mdl : Type := GlobalTheory.LocM.Mdl a.Y ⟨κ.l, κ.c, κ.good p a.hp⟩

abbrev Xm : a.Mdl := a.B.X none

abbrev Xn (n : ℕ) : a.Mdl := a.B.X (some n)

abbrev Pt (Z : a.Mdl) : Type := Z.Pt

abbrev fld {Z : a.Mdl} (y : a.Pt Z) : CF p := y.fld

def dat {Z : a.Mdl} (y : a.Pt Z) : DatAt (a.Y Z.i) y.P := (a.hasDat Z y).some

abbrev Ylat {Z : a.Mdl} (y : a.Pt Z) : Type := (a.dat y).Ylat

def chX {Z : a.Mdl} (y : a.Pt Z) : Type := a.Ylat y

instance {Z : a.Mdl} (y : a.Pt Z) : AddCommGroup (a.chX y) := inferInstanceAs (AddCommGroup (a.Ylat y))

instance {Z : a.Mdl} (y : a.Pt Z) : Module (𝓞 D.host.E) (a.chX y) :=
  Module.compHom (a.Ylat y) (A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)

def phi {Z : a.Mdl} (y : a.Pt Z) : a.Ylat y ≃+ a.chX y := AddEquiv.refl _

abbrev Gen (Z : a.Mdl) : Type := Z.Gen

abbrev ZP (Z : a.Mdl) : Type := Z.X

abbrev spz {Z : a.Mdl} (x x' : a.ZP Z) : Prop := x ⤳ x'

abbrev abP {Z : a.Mdl} (x : a.ZP Z) : Prop := Z.abP x

abbrev inQ {Z : a.Mdl} (x : a.ZP Z) : Prop := Z.inQ x

abbrev isGenP {Z : a.Mdl} (x : a.ZP Z) : Prop := Z.isGenP x

abbrev gpt {Z : a.Mdl} (η : a.Gen Z) : a.ZP Z := η.1

abbrev abAt {Z : a.Mdl} (η : a.Gen Z) : Prop := Z.abP η.1

abbrev Sh (Z : a.Mdl) : Type := Z.Sh

def IsInv {Z : a.Mdl} (F : a.Sh Z) : Prop := GlobalTheory.VB.IsVB F.toMod 1

def IsLocFree {Z : a.Mdl} (F : a.Sh Z) : Prop := ∃ r, GlobalTheory.VB.IsVB F.toMod r

abbrev Sec {Z : a.Mdl} (F : a.Sh Z) : Type := Γ(F.toMod, Z.genO)

def H0 {Z : a.Mdl} (F : a.Sh Z) : AddSubgroup (a.Sec F) :=
  (F.toMod.presheaf.map (homOfLE (le_top : Z.genO ≤ ⊤)).op).hom.range

def nrm {Z : a.Mdl} (F : a.Sh Z) (f : a.Sec F) (y : a.Pt Z) : ℝ := GlobalTheory.LocM.Mdl.nrm F.toMod f y

def GIso {Z : a.Mdl} (F₁ F₂ : a.Sh Z) : Type :=
  {_φ : F₁.toMod.restrict Z.genO.ι ≅ F₂.toMod.restrict Z.genO.ι // a.IsInv F₁ ∧ a.IsInv F₂}

abbrev Idl (Z : a.Mdl) : Type := Z.Idl

abbrev blowUp (Z : a.Mdl) (J : a.Idl Z) : a.Mdl := GlobalTheory.LocM.blowUp Z J

abbrev powP {Z : a.Mdl} (J : a.Idl Z) : Prop := Z.powP J

def Corr (Z₁ Z₂ : a.Mdl) : Type := PLift (GlobalTheory.LocM.NatCorr Z₁ Z₂)

abbrev diagCl (Z₁ Z₂ : a.Mdl) (_c : a.Corr Z₁ Z₂) : a.Mdl := GlobalTheory.LocM.natDiagCl Z₁ Z₂

open Classical in

def expo (_a : At S κ p) (l : PsiT D → ℕ → ℤ) (σ : D.host.E →+* ℂ) (i : Fin (S.Dw.mult σ)) : ℤ :=
  ∑ t : D.what₂.Tau, ((if σ = DV.tauEmb D t then l (D.eTau t) (i + 1) else 0) +
    if σ = conjEmb (DV.tauEmb D t) then -l (D.eTau t) (N - i) else 0)

open Classical in

def Lb (l : PsiT D → ℕ → ℤ) : a.Sh a.YY :=
  if h : ∃ L, IsGrLB a.YY (a.expo l) L then a.YY.ofMod (GlobalTheory.LB.toMod h.choose) else ⟨0, 0, 0, 0, 0⟩

namespace GIso

variable {a} {Z : a.Mdl} {F₁ F₂ F₃ : a.Sh Z}

def mk (φ : F₁.toMod.restrict Z.genO.ι ≅ F₂.toMod.restrict Z.genO.ι) (h₁ : a.IsInv F₁) (h₂ : a.IsInv F₂) :
    a.GIso F₁ F₂ := ⟨φ, h₁, h₂⟩

def iso (φ : a.GIso F₁ F₂) : F₁.toMod.restrict Z.genO.ι ≅ F₂.toMod.restrict Z.genO.ι := φ.1

theorem isInv_left (φ : a.GIso F₁ F₂) : a.IsInv F₁ := φ.2.1

theorem isInv_right (φ : a.GIso F₁ F₂) : a.IsInv F₂ := φ.2.2

@[simp] theorem iso_mk (φ : F₁.toMod.restrict Z.genO.ι ≅ F₂.toMod.restrict Z.genO.ι) (h₁ : a.IsInv F₁)
    (h₂ : a.IsInv F₂) : (mk φ h₁ h₂).iso = φ := rfl

theorem ext {φ ψ : a.GIso F₁ F₂} (h : φ.iso = ψ.iso) : φ = ψ := Subtype.ext h

def refl (h : a.IsInv F₁) : a.GIso F₁ F₁ := mk (Iso.refl _) h h

def symm (φ : a.GIso F₁ F₂) : a.GIso F₂ F₁ := mk φ.iso.symm φ.isInv_right φ.isInv_left

def trans (φ : a.GIso F₁ F₂) (ψ : a.GIso F₂ F₃) : a.GIso F₁ F₃ := mk (φ.iso ≪≫ ψ.iso) φ.isInv_left ψ.isInv_right

@[simp] theorem iso_refl (h : a.IsInv F₁) : (refl h).iso = Iso.refl _ := rfl

@[simp] theorem iso_symm (φ : a.GIso F₁ F₂) : φ.symm.iso = φ.iso.symm := rfl

@[simp] theorem iso_trans (φ : a.GIso F₁ F₂) (ψ : a.GIso F₂ F₃) : (φ.trans ψ).iso = φ.iso ≪≫ ψ.iso := rfl

@[simp] theorem symm_symm (φ : a.GIso F₁ F₂) : φ.symm.symm = φ := rfl

def equivIso (h₁ : a.IsInv F₁) (h₂ : a.IsInv F₂) :
    a.GIso F₁ F₂ ≃ (F₁.toMod.restrict Z.genO.ι ≅ F₂.toMod.restrict Z.genO.ι) where
  toFun := iso
  invFun φ := mk φ h₁ h₂
  left_inv _ := rfl
  right_inv _ := rfl

end GIso

example {Z : a.Mdl} (F : a.Sh Z) (f : a.Sec F) (y : a.Pt Z) : 0 ≤ a.nrm F f y := by
  refine Real.sSup_nonneg ?_
  rintro r ⟨U, -, h, k, g, lam, -, rfl⟩
  positivity

example {Z : a.Mdl} (y : a.Pt Z) (c : 𝓞 D.host.E) (u : a.Ylat y) : c • a.phi y u = a.phi y (A.H.bar c • u) := rfl

example (σ : D.host.E →+* ℂ) (i : Fin (S.Dw.mult σ)) : a.expo 0 σ i = 0 := by simp [expo]

end At

structure LawSt (ct : At S κ p) : Prop where
  nrm_nonneg : ∀ {Z : ct.Mdl} (F : ct.Sh Z) (f : ct.Sec F) (y : ct.Pt Z), 0 ≤ ct.nrm F f y
  norm_le_one_of_mem_sections : ∀ {Z : ct.Mdl} (F : ct.Sh Z) (f : ct.Sec F), f ∈ ct.H0 F → ∀ y, ct.nrm F f y ≤ 1
  Lb_inv : ∀ l, ct.IsInv (ct.Lb l)
  isGenP_ab : ∀ {Z} (x : ct.ZP Z), ct.isGenP x → ct.abP x
  genFin : ∀ Z, Finite (ct.Gen Z)
  genNe : ∀ Z, Nonempty (ct.Gen Z)
  phi_conj : ∀ {Z : ct.Mdl} (y : ct.Pt Z) (c c' : 𝓞 D.host.E),
    (c' : D.host.E) = D.host.conj (c : D.host.E) → ∀ a : ct.Ylat y, ct.phi y (c' • a) = c • ct.phi y a

structure MotSt (ct : At S κ p) : Type 1 where
  be : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ct.Ylat y →ₗ[ℤ] ct.Ylat y →ₗ[ℤ] ℝ
  be_symm : ∀ {Z : ct.Mdl} (y : ct.Pt Z) (a b : ct.Ylat y), be y a b = be y b a
  be_bal : ∀ {Z : ct.Mdl} (y : ct.Pt Z) (c c' : 𝓞 D.host.E), (c' : D.host.E) = D.host.conj (c : D.host.E) →
    ∀ a b : ct.Ylat y, be y (c • a) b = be y a (c' • b)
  be_posDef : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ (ct.Ylat y)),
    ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ k, c i * c k * be y (b i) (b k)
  yl_rank : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ∃ ρ : ℕ, Module.finrank ℤ (ct.Ylat y) = 2 * D.R.f * ρ ∧
    (1 ≤ j → j + 1 ≤ N → ρ ≤ j ∧ ρ + j ≤ N)
  psiV : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ct.Ylat y → ℝ
  tau : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ct.Ylat y → ct.chX y → ((ct.fld y).C)ˣ
  tau_add_left : ∀ {Z : ct.Mdl} (y : ct.Pt Z) a a' χ, tau y (a + a') χ = tau y a χ * tau y a' χ
  tau_add_right : ∀ {Z : ct.Mdl} (y : ct.Pt Z) a χ χ', tau y a (χ + χ') = tau y a χ * tau y a χ'
  tau_symm : ∀ {Z : ct.Mdl} (y : ct.Pt Z) a b, tau y a (ct.phi y b) = tau y b (ct.phi y a)
  tau_smul : ∀ {Z : ct.Mdl} (y : ct.Pt Z) (c : 𝓞 D.host.E) a χ, tau y (c • a) χ = tau y a (c • χ)
  be_tau : ∀ {Z : ct.Mdl} (y : ct.Pt Z) a b, be y a b = vU p (tau y a (ct.phi y b))
  multiplicationLatticeFirst : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ct.Ylat y → ct.Ylat y → ct.chX y
  multiplicationLatticeSecond : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ct.Ylat y → ct.Ylat y → ct.chX y
  mulC : ∀ {Z : ct.Mdl} (y : ct.Pt Z), ct.Ylat y → ct.Ylat y → ((ct.fld y).C)ˣ
  psiV_def : ∀ {Z : ct.Mdl} (y : ct.Pt Z) a, psiV y a = vU p (mulC y a (w0 D • a))
  dimB : ct.Pt ct.Xm → ℕ
  dimB_add : ∀ y, dimB y + Module.finrank ℤ (ct.Ylat y) = D.R.f * N
  be_eq : ∀ {Z : ct.Mdl} (y : ct.Pt Z) (u v : ct.Ylat y), be y u v = (ct.dat y).beta u v

structure ShfSt (ct : At S κ p) : Type 1 where
  vrat : ∀ {Z : ct.Mdl} {F₁ F₂ : ct.Sh Z}, ct.GIso F₁ F₂ → ct.Pt Z → ℝ
  SES : ct.Mdl → Type
  ExactMod : ∀ {Z : ct.Mdl}, SES Z → ℕ → Prop
  homSh : ∀ {Z}, ct.Sh Z → ct.Sh Z → ct.Sh Z
  homSh_inv : ∀ {Z} (F₁ F₂ : ct.Sh Z), ct.IsInv F₁ → ct.IsInv F₂ → ct.IsInv (homSh F₁ F₂)
  isoSec : ∀ {Z} {F₁ F₂ : ct.Sh Z}, ct.GIso F₁ F₂ → ct.Sec (homSh F₁ F₂)
  nrm_isoSec : ∀ {Z} {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) (y : ct.Pt Z),
    ct.nrm (homSh F₁ F₂) (isoSec φ) y = (p : ℝ) ^ (-(vrat φ y))
  isoSymm : ∀ {Z} {F₁ F₂ : ct.Sh Z}, ct.GIso F₁ F₂ → ct.GIso F₂ F₁
  vrat_symm : ∀ {Z} {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) (y : ct.Pt Z),
    vrat (isoSymm φ) y = -(vrat φ y)
  oX : ct.Sh ct.Xm
  oX_inv : ct.IsInv oX
  secOf : ∀ {F : ct.Sh ct.Xm}, ct.GIso oX F → ct.Sec F
  nrm_secOf : ∀ {F : ct.Sh ct.Xm} (φ : ct.GIso oX F) y, ct.nrm F (secOf φ) y = (p : ℝ) ^ (-(vrat φ y))

structure FlgSt (ct : At S κ p) : Type 1 where
  FlagData : ct.Mdl → Type
  flagCl : ∀ Z, FlagData Z → ct.Mdl
  allFlags : FlagData ct.Xm
  YY_eq : ct.YY = flagCl ct.Xm allFlags

structure FrmSt (ct : At S κ p) : Type 1 where
  nrmRef : ∀ l, ct.Sec (ct.Lb l) → ct.Pt ct.YY → ℝ
  LieV : ct.Pt ct.YY → Type
  [lvAdd : ∀ y, AddCommGroup (LieV y)]
  [lvMod : ∀ y, Module (ct.fld y).C (LieV y)]
  lieL : ∀ y, AddSubgroup (LieV y)
  eig : ∀ y, PsiT D × Bool → Submodule (ct.fld y).C (LieV y)
  Wst : ∀ y, PsiT D × Bool → ℕ → Submodule (ct.fld y).C (LieV y)
  Wst_le : ∀ y σ i, Wst y σ i ≤ eig y σ
  taut : ∀ y, PsiT D × Bool → ℕ → AddSubgroup (LieV y)
  taut_eq : ∀ y σ i, taut y σ i = (Wst y σ i).toAddSubgroup ⊓ lieL y
  nrmIn : ∀ l, ct.Sec (ct.Lb l) → ∀ y : ct.Pt ct.YY, (PsiT D × Bool → ℕ → AddSubgroup (LieV y)) → ℝ
  nrmRef_def : ∀ l f y, nrmRef l f y =
    nrmIn l f y (fun σ i => (Wst y σ i).toAddSubgroup ⊓ ((eig y σ).toAddSubgroup ⊓ lieL y))
  nrm_Lb_def : ∀ l f y, ct.nrm (ct.Lb l) f y = nrmIn l f y (taut y)

attribute [instance] FrmSt.lvAdd FrmSt.lvMod

structure ChtSt (ct : At S κ p) : Type 1 where
  DVP : Type
  dvRho : DVP → ℕ
  Ext : DVP → Type
  Chart : ct.Mdl → (y : DVP) → Ext y → Type
  chAt : ∀ {Z y e}, Chart Z y e → Prop
  chOpen : ∀ {Z y e}, Chart Z y e → Prop
  chAbExact : ∀ {Z y e}, Chart Z y e → Prop
  chModU : ∀ {Z y e}, Chart Z y e → Prop
  chConst : ∀ {Z y e}, Chart Z y e → Prop
  pbPrinc : ∀ {Z y e}, ct.Idl Z → Chart Z y e → Prop
  redK : ∀ Z, DVP → ct.ZP Z
  dvRho_pos_iff : ∀ Z (y : DVP), 0 < dvRho y ↔ ¬ ct.abP (redK Z y)
  genK : ∀ {Z}, ct.Gen Z → DVP
  redK_genK : ∀ {Z} (η : ct.Gen Z), redK Z (genK η) = ct.gpt η
  imgM : ∀ {Z y e}, Chart Z y e → ct.ZP Z
  imgU : ∀ {Z y e}, Chart Z y e → ct.ZP Z
  img_spz : ∀ {Z y e} (χ : Chart Z y e), ct.spz (imgU χ) (imgM χ)
  imgU_inQ : ∀ {Z y e} (χ : Chart Z y e), ct.inQ (imgU χ)
  chAt_imgM : ∀ {Z y e} (χ : Chart Z y e), chAt χ → imgM χ = redK Z y
  chAbExact_imgU : ∀ {Z y e} (χ : Chart Z y e), chAbExact χ → ¬ ct.abP (imgU χ)
  RFam : ∀ y, Ext y → Type
  chFam : ∀ {Z y e}, Chart Z y e → RFam y e
  ptK : ∀ Z, DVP → ct.Pt Z
  ptK_good : ∀ Z y, Subsingleton (ct.Ylat (ptK Z y)) ↔ dvRho y = 0
  vpi : ∀ {y}, Ext y → ℝ
  vpi_pos : ∀ {y} (e : Ext y), 0 < vpi e
  ordGe : ∀ {Z y e}, Chart Z y e → ∀ F : ct.Sh Z, ct.Sec F → ℝ → Prop
  yEta : ∀ {Z}, ct.Gen Z → ct.Pt Z
  yEta_good : ∀ {Z} (η : ct.Gen Z), Subsingleton (ct.Ylat (yEta η)) ↔ ct.abAt η

structure TorSt (ct : At S κ p) : Type 1 where
  PL : Type
  phiAt : PL → ∀ {Z : ct.Mdl}, ct.Pt Z → ℝ
  phiAt_zero : ∀ (φ : PL) {Z : ct.Mdl} (y : ct.Pt Z), Subsingleton (ct.Ylat y) → phiAt φ y = 0
  divGe : ∀ {Z : ct.Mdl} (F : ct.Sh Z), ct.Sec F → ℚ → PL → Prop
  IvD : Option ℕ → Type
  jIdl : ∀ b, IvD b → ct.Idl ((ct.B.X b))

structure FJSt (ct : At S κ p) : Type 1 where
  FJd : Type
  Chr : FJd → Type
  fjN : ∀ l, ct.Sec (ct.Lb l) → (t : FJd) → Chr t → ℝ

structure UniSt (ct : At S κ p) : Type 1 where
  Unim : Type
  latStd : ℕ → Unim

structure ThbSt (ct : At S κ p) (un : UniSt ct) : Type 1 where
  LBG : un.Unim → Type
  LBGq : un.Unim → Type
  resQ : ∀ {La}, LBG La → LBGq La
  PPq : ∀ La, LBGq La
  symmG : ∀ {La}, LBG La → Prop
  rigG : ∀ {La}, LBG La → Prop
  LBGt : ∀ (y : ct.Pt ct.Xm), un.Unim → Type
  LBB : ∀ (y : ct.Pt ct.Xm), un.Unim → Type
  resGt : ∀ {La}, LBG La → ∀ y, LBGt y La
  prPull : ∀ {y La}, LBB y La → LBGt y La
  principal : ∀ {y La}, LBB y La → Prop
  StrictHenselianAcyclic : un.Unim → Type
  squareRootLineBundle : un.Unim → Type
  res2 : ∀ {La}, StrictHenselianAcyclic La → squareRootLineBundle La
  PoiQ : ∀ La, squareRootLineBundle La
  biext : ∀ {La}, StrictHenselianAcyclic La → Prop
  dg : ∀ {La}, StrictHenselianAcyclic La → LBG La
  dgq : ∀ {La}, squareRootLineBundle La → LBGq La
  dg_res : ∀ {La} (P : StrictHenselianAcyclic La), resQ (dg P) = dgq (res2 P)
  PPq_def : ∀ La, PPq La = dgq (PoiQ La)

structure KeySt (ct : At S κ p) : Type 1 where
  piPP : ct.Sh ct.Xm
  keySh : ℕ → ct.Sh ct.Xm
  keySh_inv : ct.IsInv piPP → ∀ c, ct.IsInv (keySh c)

structure BdySt (ct : At S κ p) : Type 1 where
  BPt : Type
  Rl : BPt → Type
  [iRr : ∀ z, CommRing (Rl z)]
  [iRd : ∀ z, IsDomain (Rl z)]
  [iRl : ∀ z, IsLocalRing (Rl z)]
  [iRn : ∀ z, IsNoetherianRing (Rl z)]
  [iRi : ∀ z, IsIntegrallyClosed (Rl z)]
  [iRc : ∀ z, IsAdicComplete (IsLocalRing.maximalIdeal (Rl z)) (Rl z)]
  Yb : BPt → Type
  [iYa : ∀ z, AddCommGroup (Yb z)]
  [iYm : ∀ z, Module (𝓞 D.host.E) (Yb z)]
  Xb : BPt → Type
  [iXa : ∀ z, AddCommGroup (Xb z)]
  [iXm : ∀ z, Module (𝓞 D.host.E) (Xb z)]
  phib : ∀ z, Yb z ≃+ Xb z
  phib_conj : ∀ z (c c' : 𝓞 D.host.E), (c' : D.host.E) = D.host.conj (c : D.host.E) →
    ∀ a : Yb z, phib z (c' • a) = c • phib z a
  taub : ∀ z, Yb z → Xb z → (FractionRing (Rl z))ˣ
  taub_add_left : ∀ z a a' χ, taub z (a + a') χ = taub z a χ * taub z a' χ
  taub_add_right : ∀ z a χ χ', taub z a (χ + χ') = taub z a χ * taub z a χ'
  taub_symm : ∀ z a b, taub z a (phib z b) = taub z b (phib z a)
  taub_smul : ∀ z (c : 𝓞 D.host.E) a χ, taub z (c • a) χ = taub z a (c • χ)
  taub_pos : ∀ z a, ((taub z a (phib z a) : (FractionRing (Rl z))ˣ) : FractionRing (Rl z)) ∈
    (algebraMap (Rl z) (FractionRing (Rl z))).range
  Sg : BPt → Type
  [iSg : ∀ z, AddCommGroup (Sg z)]
  [iSk : ∀ z, Module (FractionRing (Rl z)) (Sg z)]
  [iSm : ∀ z, Module (Rl z) (Sg z)]
  [iSt : ∀ z, IsScalarTower (Rl z) (FractionRing (Rl z)) (Sg z)]
  Sreg : ∀ z, Submodule (Rl z) (Sg z)
  fc : ∀ z, Sg z →ₗ[FractionRing (Rl z)] (Xb z → FractionRing (Rl z))
  trU : ∀ z, Yb z → Xb z → (Rl z)ˣ

attribute [instance] BdySt.iRr BdySt.iRd BdySt.iRl BdySt.iRn BdySt.iRi BdySt.iRc BdySt.iYa BdySt.iYm BdySt.iXa BdySt.iXm BdySt.iSg BdySt.iSk BdySt.iSm BdySt.iSt

structure ThgSt (ct : At S κ p) (un : UniSt ct) : Type 1 where
  Tors : ct.Pt ct.Xm → un.Unim → ℕ → Type
  [atAdd : ∀ y La n, AddCommGroup (Tors y La n)]
  [atFin : ∀ y La n, Fintype (Tors y La n)]
  at_tors : ∀ y La n (x : Tors y La n), n • x = 0
  at_card : ∀ y nW n, 0 < n → Fintype.card (Tors y (un.latStd nW) n) = n ^ (2 * (D.R.f * N * nW))
  Th : ct.Pt ct.Xm → un.Unim → ℕ → Type
  [thGrp : ∀ y La n, Group (Th y La n)]
  ovr : ∀ y La n, Th y La n →* Multiplicative (Tors y La n)
  ovr_surj : ∀ y La n, Function.Surjective (ovr y La n)
  scal : ∀ y La n, ((ct.fld y).C)ˣ →* Th y La n
  scal_inj : ∀ y La n, Function.Injective (scal y La n)
  scal_central : ∀ y La n a g, scal y La n a * g = g * scal y La n a
  ker_ovr : ∀ y La n g, ovr y La n g = 1 ↔ ∃ a, scal y La n a = g
  dl : ∀ y La n, Th y La n ≃* Th y La n
  dl_ovr : ∀ y La n g, ovr y La n (dl y La n g) = (ovr y La n g)⁻¹
  dl_scal : ∀ y La n a, dl y La n (scal y La n a) = scal y La n a
  dl_dl : ∀ y La n g, dl y La n (dl y La n g) = g
  Sn : ct.Pt ct.Xm → un.Unim → ℕ → Type
  [snAdd : ∀ y La n, AddCommGroup (Sn y La n)]
  [snMod : ∀ y La n, Module (ct.fld y).C (Sn y La n)]
  act : ∀ y La n, Th y La n →* Module.End (ct.fld y).C (Sn y La n)
  act_scal : ∀ y La n a s, act y La n (scal y La n a) s = (a : (ct.fld y).C) • s
  vth : ∀ y La n, Sn y La n
  alp : ℕ → 𝓞 D.host.E
  alp_spec : ∀ n, ModuliIntegralCharts.NHyp D p n →
    (alp n : D.host.E) * D.host.conj (alp n : D.host.E) = (n : D.host.E) ∧
    ((∃ mm : ℕ, n = mm ^ 2 ∧ alp n = (mm : 𝓞 D.host.E)) ∨ (alp n : D.host.E) ∈ D.host.K)
  th1 : ∀ y nW, Sn y (un.latStd nW) 1
  pbAl : ∀ y nW n, Sn y (un.latStd nW) 1 →ₗ[(ct.fld y).C] Sn y (un.latStd nW) n
  vth_def : ∀ y nW n, ModuliIntegralCharts.NHyp D p n → vth y (un.latStd nW) n = pbAl y nW n (th1 y nW)

attribute [instance] ThgSt.atAdd ThgSt.atFin ThgSt.thGrp ThgSt.snAdd ThgSt.snMod

structure JetSt (ct : At S κ p) (un : UniSt ct) (tg : ThgSt ct un) : Type 1 where
  Jet : ct.Pt ct.Xm → un.Unim → ℕ → ℕ → Type
  [jAdd : ∀ y La n DF, AddCommGroup (Jet y La n DF)]
  [jMod : ∀ y La n DF, Module (ct.fld y).C (Jet y La n DF)]
  intJet : ∀ y La n DF, AddSubgroup (Jet y La n DF)
  jet : ∀ y La n DF, tg.Sn y La n →ₗ[(ct.fld y).C] Jet y La n DF
  FB : ∀ (y : ct.Pt ct.Xm) (nW n : ℕ), (Fin nW → ct.chX y) → Type
  [fbAdd : ∀ y nW n χ, AddCommGroup (FB y nW n χ)]
  [fbMod : ∀ y nW n χ, Module (ct.fld y).C (FB y nW n χ)]
  nB : ∀ {y nW n χ}, FB y nW n χ → ℝ
  sgc : ∀ y nW n χ, tg.Sn y (un.latStd nW) n →ₗ[(ct.fld y).C] FB y nW n χ
  trB : ∀ y nW n (a : Fin nW → ct.Ylat y) χ,
    FB y nW n χ ≃ₗ[(ct.fld y).C] FB y nW n (χ + n • fun i => ct.phi y (a i))
  trB_norm : ∀ y nW n a χ σ, nB (trB y nW n a χ σ) = nB σ
  jX : ∀ y nW n DF χ, FB y nW n χ →ₗ[(ct.fld y).C] Jet y (un.latStd nW) n DF
  intJet_free : ∀ y nW n DF, ∃ (N : ℕ) (b : Module.Basis (Fin N) (ct.fld y).C (Jet y (un.latStd nW) n DF)),
    ∀ v, v ∈ intJet y (un.latStd nW) n DF ↔ ∀ i, ‖b.repr v i‖ ≤ 1
  jX_int : ∀ y nW n DF χ (σ : FB y nW n χ), nB σ ≤ 1 → jX y nW n DF χ σ ∈ intJet y (un.latStd nW) n DF
  jet_fourier : ∀ y nW n DF (s : tg.Sn y (un.latStd nW) n) (t : (ct.fld y).C), t ≠ 0 →
    ∃ F₀ : Finset (Fin nW → ct.chX y), ∀ F : Finset (Fin nW → ct.chX y), F₀ ⊆ F →
      ∃ v ∈ intJet y (un.latStd nW) n DF,
        jet y (un.latStd nW) n DF s - ∑ χ ∈ F, jX y nW n DF χ (sgc y nW n χ s) = t • v

attribute [instance] JetSt.jAdd JetSt.jMod JetSt.fbAdd JetSt.fbMod

structure EvlSt (ct : At S κ p) : Type 1 where
  LieGt : ct.Pt ct.Xm → PsiT D × Bool → Type
  LieB : ct.Pt ct.Xm → PsiT D × Bool → Type
  LieT : ct.Pt ct.Xm → PsiT D × Bool → Type
  [lgAdd : ∀ y σ, AddCommGroup (LieGt y σ)]
  [lbAdd : ∀ y σ, AddCommGroup (LieB y σ)]
  [ltAdd : ∀ y σ, AddCommGroup (LieT y σ)]
  resB : ∀ y σ, LieGt y σ →+ LieB y σ
  incT : ∀ y σ, LieT y σ →+ LieGt y σ
  kapGt : ∀ y σ, LieGt y σ → LieGt y σ → (ct.fld y).C
  kapB : ∀ y σ, LieB y σ → LieB y σ → (ct.fld y).C
  Harm : ct.Pt ct.Xm → Type
  SecP : ct.Pt ct.Xm → Type
  evA : ∀ y, Harm y → SecP y → (ct.fld y).C
  evGt : ∀ y, Harm y → SecP y → (ct.fld y).C

attribute [instance] EvlSt.lgAdd EvlSt.lbAdd EvlSt.ltAdd

structure HTpSt (ct : At S κ p) : Type 1 where
  Tp : ∀ {Z : ct.Mdl}, ct.Pt Z → Type
  [tpAdd : ∀ {Z : ct.Mdl} (y : ct.Pt Z), AddCommGroup (Tp y)]
  OmV : ∀ {Z : ct.Mdl}, ct.Pt Z → Type
  [omAdd : ∀ {Z : ct.Mdl} (y : ct.Pt Z), AddCommGroup (OmV y)]
  [omMod : ∀ {Z : ct.Mdl} (y : ct.Pt Z), Module (ct.fld y).C (OmV y)]
  om : ∀ {Z : ct.Mdl} (y : ct.Pt Z), AddSubgroup (OmV y)
  ht : ∀ {Z : ct.Mdl} (y : ct.Pt Z), Tp y →+ OmV y
  om_smul : ∀ {Z} (y : ct.Pt Z) (a : (ct.fld y).C), ‖a‖ ≤ 1 → ∀ v ∈ om y, a • v ∈ om y
  TC : ∀ {Z}, ct.Pt Z → Type
  [tcAdd : ∀ {Z} (y : ct.Pt Z), AddCommGroup (TC y)]
  [tcMod : ∀ {Z} (y : ct.Pt Z), Module (ct.fld y).C (TC y)]
  iT : ∀ {Z} (y : ct.Pt Z), Tp y →+ TC y
  iT_span : ∀ {Z} (y : ct.Pt Z), Submodule.span (ct.fld y).C (Set.range (iT y)) = ⊤
  htC : ∀ {Z} (y : ct.Pt Z), TC y →ₗ[(ct.fld y).C] OmV y
  htC_iT : ∀ {Z} (y : ct.Pt Z) t, htC y (iT y t) = ht y t
  psiC : ∀ {Z} (y : ct.Pt Z), TC y →ₗ[(ct.fld y).C] TC y →ₗ[(ct.fld y).C] (ct.fld y).C
  lieGt1 : ∀ {Z} (y : ct.Pt Z), Submodule (ct.fld y).C (TC y)
  eT : ∀ {Z} (y : ct.Pt Z), PsiT D → TC y →ₗ[(ct.fld y).C] TC y

attribute [instance] HTpSt.tpAdd HTpSt.omAdd HTpSt.omMod HTpSt.tcAdd HTpSt.tcMod

structure HTmSt (ct : At S κ p) (sh : ShfSt ct) (hq : HTpSt ct) : Type 1 where
  IsHTBlowup : ct.Mdl → ct.Mdl → Prop
  eOmP : ∀ Z : ct.Mdl, Bool → PsiT D → ct.Sh Z
  htSES : ∀ Z : ct.Mdl, PsiT D → sh.SES Z
  BT : ℕ → Type
  extA : ∀ {n}, BT n → Prop
  compat : ∀ {n}, BT n → BT (n + 1) → Prop
  HTn : ℕ → Type
  htEval : ∀ {n}, HTn n → ∀ y : ct.Pt (ct.Xn n), hq.Tp y →+ hq.OmV y
  htIdl : ∀ {n}, HTn n → ct.Idl (ct.Xn n)
  IsHTBlowup_def : ∀ n Z', 3 ≤ n → (IsHTBlowup Z' (ct.Xn n) ↔ ∃ h : HTn n,
    (∀ (y : ct.Pt (ct.Xn n)) (t : hq.Tp y), htEval h y t ∈ hq.om y ∧
      ∃ v ∈ hq.om y, htEval h y t - hq.ht y t = ((p : (ct.fld y).C) ^ n) • v) ∧
    Z' = ct.blowUp (ct.Xn n) (htIdl h))
  wFib : ∀ {n}, HTn n → ∀ y : ct.Pt (ct.Xn n), PsiT D → AddSubgroup (hq.TC y)
  omSh : ∀ Z, ct.Sh Z
  omPat : ∀ {Z} (y : ct.Pt Z), AddSubgroup (hq.OmV y)
  omPat_def : ∀ n Z', 3 ≤ n → IsHTBlowup Z' (ct.Xn n) → ∀ y : ct.Pt Z',
    omPat y = hq.om y ⊓ (Ospan (C := (ct.fld y).C) (Set.range (hq.ht y)) ⊔
      (hq.om y).map (DistribSMul.toAddMonoidHom (hq.OmV y) ((p : (ct.fld y).C) ^ n)))
  BPt : ct.Mdl → Type
  bfld : ∀ {Z}, BPt Z → CF p
  OmB : ∀ {Z}, BPt Z → Type
  [obAdd : ∀ {Z} (y : BPt Z), AddCommGroup (OmB y)]
  [obMod : ∀ {Z} (y : BPt Z), Module (bfld y).C (OmB y)]
  omB : ∀ {Z} (y : BPt Z), AddSubgroup (OmB y)
  omPB : ∀ {Z} (y : BPt Z), AddSubgroup (OmB y)
  eOmB : ∀ {Z} (y : BPt Z), PsiT D → AddSubgroup (OmB y)
  eB : ∀ {Z} (y : BPt Z), PsiT D → OmB y →ₗ[(bfld y).C] OmB y

attribute [instance] HTmSt.obAdd HTmSt.obMod

structure CrDSt (ct : At S κ p) : Type 1 where
  nefQ : (PsiT D → ℕ → ℝ) → Prop
  Crv : Type
  eDeg : Crv → ℤ
  Pm : Crv → ℤ
  Pm_nonneg : ∀ c, 0 ≤ Pm c
  degLie : Crv → PsiT D → Bool → ℤ
  degLdR : Crv → (PsiT D → ℕ → ℝ) → ℝ
  CrvQ : Type
  degGrQ : CrvQ → PsiT D → ℕ → ℤ
  nefQ_def : ∀ l : PsiT D → ℕ → ℝ, nefQ l ↔
    ∀ C : CrvQ, 0 ≤ -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 N, l τ i * (degGrQ C τ i : ℝ)
  degGrD : Crv → PsiT D → ℕ → ℤ
  degLdR_def : ∀ CC (μ : PsiT D → ℕ → ℝ), degLdR CC μ =
    -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 N, μ τ i * (degGrD CC τ i : ℝ)
  degLie_f : ∀ CC τ, degLie CC τ false = ∑ i ∈ Finset.Icc 1 j, degGrD CC τ i
  degLie_alt : ∀ CC τ, degLie CC τ true = -∑ i ∈ Finset.Icc (j + 1) N, degGrD CC τ i
  eDeg_def : DV.UnramE D p → ∀ CC, eDeg CC = -∑ᶠ τ, (degLie CC τ false + degLie CC τ true)
  Pm_head : ∀ CC τ i, 1 ≤ i → i ≤ j → ∑ k ∈ Finset.Icc 1 i, degGrD CC τ k ≤ Pm CC
  Pm_tail : ∀ CC τ i, j ≤ i → i ≤ N → -∑ k ∈ Finset.Icc (i + 1) N, degGrD CC τ k ≤ Pm CC

structure CrHSt (ct : At S κ p) (fg : FlgSt ct) : Type 1 where
  nefHT : ct.Mdl → (PsiT D → ℕ → ℝ) → Prop
  descK : ct.Mdl → (PsiT D → ℕ → ℤ) → Prop
  bdryLoci : ct.Mdl → Prop
  htFlags : ∀ Z, fg.FlagData Z
  YsP : ct.Mdl → Type
  ysBd : ∀ {Z}, YsP Z → Prop
  FlP : Type
  hFl : ∀ {Z}, YsP Z → FlP
  FlCl : Type
  flMem : FlP → FlCl → Prop
  flDim : FlCl → ℕ
  Sum1 : Type
  locus : Sum1 → FlCl
  bdryLoci_def : ∀ Z, bdryLoci Z ↔ ∃ S : Set Sum1, S.Finite ∧
    (∀ x : YsP Z, ysBd x → ∃ ℓ ∈ S, flMem (hFl x) (locus ℓ)) ∧
    ∀ ℓ ∈ S, flDim (locus ℓ) + D.R.f * (N - 1) = D.R.f * (N * (N - 1) / 2)
  CrvS : ct.Mdl → Type
  degGr : ∀ {Z}, CrvS Z → PsiT D → ℕ → ℤ
  nefHT_def : ∀ Z (l : PsiT D → ℕ → ℝ), nefHT Z l ↔
    ∀ C : CrvS Z, 0 ≤ -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 N, l τ i * (degGr C τ i : ℝ)

structure Stages (ct : At S κ p) : Type 1 where
  lw : LawSt ct
  mo : MotSt ct
  sh : ShfSt ct
  fg : FlgSt ct
  fr : FrmSt ct
  ch : ChtSt ct
  tr : TorSt ct
  fj : FJSt ct
  un : UniSt ct
  tb : ThbSt ct un
  ky : KeySt ct
  bd : BdySt ct
  tg : ThgSt ct un
  jt : JetSt ct un tg
  ev : EvlSt ct
  hq : HTpSt ct
  hm : HTmSt ct sh hq
  cd : CrDSt ct
  cr : CrHSt ct fg

namespace Stages

variable {ct : At S κ p} (st : Stages ct)

def loc : ModuliIntegralCharts.Loc D N j p where
  Mdl := @At.Mdl _ _ _ _ _ _ _ ct
  Xm := @At.Xm _ _ _ _ _ _ _ ct
  YY := ct.YY
  Xn := @At.Xn _ _ _ _ _ _ _ ct
  Pt := @At.Pt _ _ _ _ _ _ _ ct
  fld := @At.fld _ _ _ _ _ _ _ ct
  Ylat := @At.Ylat _ _ _ _ _ _ _ ct
  ylAdd := fun _ => inferInstance
  ylMod := fun _ => inferInstance
  ylFree := fun _ => inferInstance
  ylFin := fun _ => inferInstance
  be := @MotSt.be _ _ _ _ _ _ _ _ st.mo
  be_symm := @MotSt.be_symm _ _ _ _ _ _ _ _ st.mo
  be_bal := @MotSt.be_bal _ _ _ _ _ _ _ _ st.mo
  be_posDef := @MotSt.be_posDef _ _ _ _ _ _ _ _ st.mo
  yl_rank := @MotSt.yl_rank _ _ _ _ _ _ _ _ st.mo
  Gen := @At.Gen _ _ _ _ _ _ _ ct
  abAt := @At.abAt _ _ _ _ _ _ _ ct
  Sh := @At.Sh _ _ _ _ _ _ _ ct
  IsInv := @At.IsInv _ _ _ _ _ _ _ ct
  IsLocFree := @At.IsLocFree _ _ _ _ _ _ _ ct
  Sec := @At.Sec _ _ _ _ _ _ _ ct
  secAdd := fun _ => inferInstance
  H0 := @At.H0 _ _ _ _ _ _ _ ct
  nrm := @At.nrm _ _ _ _ _ _ _ ct
  nrm_nonneg := @LawSt.nrm_nonneg _ _ _ _ _ _ _ _ st.lw
  norm_le_one_of_mem_sections := @LawSt.norm_le_one_of_mem_sections _ _ _ _ _ _ _ _ st.lw
  GIso := @At.GIso _ _ _ _ _ _ _ ct
  vrat := @ShfSt.vrat _ _ _ _ _ _ _ _ st.sh
  Lb := @At.Lb _ _ _ _ _ _ _ ct
  Lb_inv := @LawSt.Lb_inv _ _ _ _ _ _ _ _ st.lw
  nrmRef := @FrmSt.nrmRef _ _ _ _ _ _ _ _ st.fr
  DVP := @ChtSt.DVP _ _ _ _ _ _ _ _ st.ch
  dvRho := @ChtSt.dvRho _ _ _ _ _ _ _ _ st.ch
  Ext := @ChtSt.Ext _ _ _ _ _ _ _ _ st.ch
  Chart := @ChtSt.Chart _ _ _ _ _ _ _ _ st.ch
  chAt := @ChtSt.chAt _ _ _ _ _ _ _ _ st.ch
  chOpen := @ChtSt.chOpen _ _ _ _ _ _ _ _ st.ch
  chAbExact := @ChtSt.chAbExact _ _ _ _ _ _ _ _ st.ch
  chModU := @ChtSt.chModU _ _ _ _ _ _ _ _ st.ch
  chConst := @ChtSt.chConst _ _ _ _ _ _ _ _ st.ch
  PL := @TorSt.PL _ _ _ _ _ _ _ _ st.tr
  phiAt := @TorSt.phiAt _ _ _ _ _ _ _ _ st.tr
  phiAt_zero := @TorSt.phiAt_zero _ _ _ _ _ _ _ _ st.tr
  divGe := @TorSt.divGe _ _ _ _ _ _ _ _ st.tr
  FJd := @FJSt.FJd _ _ _ _ _ _ _ _ st.fj
  Chr := @FJSt.Chr _ _ _ _ _ _ _ _ st.fj
  fjN := @FJSt.fjN _ _ _ _ _ _ _ _ st.fj
  Unim := @UniSt.Unim _ _ _ _ _ _ _ _ st.un
  LBG := @ThbSt.LBG _ _ _ _ _ _ _ _ _ st.tb
  LBGq := @ThbSt.LBGq _ _ _ _ _ _ _ _ _ st.tb
  resQ := @ThbSt.resQ _ _ _ _ _ _ _ _ _ st.tb
  PPq := @ThbSt.PPq _ _ _ _ _ _ _ _ _ st.tb
  symmG := @ThbSt.symmG _ _ _ _ _ _ _ _ _ st.tb
  rigG := @ThbSt.rigG _ _ _ _ _ _ _ _ _ st.tb
  LBGt := @ThbSt.LBGt _ _ _ _ _ _ _ _ _ st.tb
  LBB := @ThbSt.LBB _ _ _ _ _ _ _ _ _ st.tb
  resGt := @ThbSt.resGt _ _ _ _ _ _ _ _ _ st.tb
  prPull := @ThbSt.prPull _ _ _ _ _ _ _ _ _ st.tb
  principal := @ThbSt.principal _ _ _ _ _ _ _ _ _ st.tb
  psiV := @MotSt.psiV _ _ _ _ _ _ _ _ st.mo
  piPP := @KeySt.piPP _ _ _ _ _ _ _ _ st.ky
  keySh := @KeySt.keySh _ _ _ _ _ _ _ _ st.ky
  latStd := @UniSt.latStd _ _ _ _ _ _ _ _ st.un
  At := @ThgSt.Tors _ _ _ _ _ _ _ _ _ st.tg
  atAdd := @ThgSt.atAdd _ _ _ _ _ _ _ _ _ st.tg
  atFin := @ThgSt.atFin _ _ _ _ _ _ _ _ _ st.tg
  at_tors := @ThgSt.at_tors _ _ _ _ _ _ _ _ _ st.tg
  at_card := @ThgSt.at_card _ _ _ _ _ _ _ _ _ st.tg
  Th := @ThgSt.Th _ _ _ _ _ _ _ _ _ st.tg
  thGrp := @ThgSt.thGrp _ _ _ _ _ _ _ _ _ st.tg
  ovr := @ThgSt.ovr _ _ _ _ _ _ _ _ _ st.tg
  ovr_surj := @ThgSt.ovr_surj _ _ _ _ _ _ _ _ _ st.tg
  scal := @ThgSt.scal _ _ _ _ _ _ _ _ _ st.tg
  scal_inj := @ThgSt.scal_inj _ _ _ _ _ _ _ _ _ st.tg
  scal_central := @ThgSt.scal_central _ _ _ _ _ _ _ _ _ st.tg
  ker_ovr := @ThgSt.ker_ovr _ _ _ _ _ _ _ _ _ st.tg
  dl := @ThgSt.dl _ _ _ _ _ _ _ _ _ st.tg
  dl_ovr := @ThgSt.dl_ovr _ _ _ _ _ _ _ _ _ st.tg
  dl_scal := @ThgSt.dl_scal _ _ _ _ _ _ _ _ _ st.tg
  dl_dl := @ThgSt.dl_dl _ _ _ _ _ _ _ _ _ st.tg
  Sn := @ThgSt.Sn _ _ _ _ _ _ _ _ _ st.tg
  snAdd := @ThgSt.snAdd _ _ _ _ _ _ _ _ _ st.tg
  snMod := @ThgSt.snMod _ _ _ _ _ _ _ _ _ st.tg
  act := @ThgSt.act _ _ _ _ _ _ _ _ _ st.tg
  act_scal := @ThgSt.act_scal _ _ _ _ _ _ _ _ _ st.tg
  vth := @ThgSt.vth _ _ _ _ _ _ _ _ _ st.tg
  Jet := @JetSt.Jet _ _ _ _ _ _ _ _ _ _ st.jt
  jAdd := @JetSt.jAdd _ _ _ _ _ _ _ _ _ _ st.jt
  jMod := @JetSt.jMod _ _ _ _ _ _ _ _ _ _ st.jt
  intJet := @JetSt.intJet _ _ _ _ _ _ _ _ _ _ st.jt
  jet := @JetSt.jet _ _ _ _ _ _ _ _ _ _ st.jt
  LieGt := @EvlSt.LieGt _ _ _ _ _ _ _ _ st.ev
  LieB := @EvlSt.LieB _ _ _ _ _ _ _ _ st.ev
  LieT := @EvlSt.LieT _ _ _ _ _ _ _ _ st.ev
  lgAdd := @EvlSt.lgAdd _ _ _ _ _ _ _ _ st.ev
  lbAdd := @EvlSt.lbAdd _ _ _ _ _ _ _ _ st.ev
  ltAdd := @EvlSt.ltAdd _ _ _ _ _ _ _ _ st.ev
  resB := @EvlSt.resB _ _ _ _ _ _ _ _ st.ev
  incT := @EvlSt.incT _ _ _ _ _ _ _ _ st.ev
  kapGt := @EvlSt.kapGt _ _ _ _ _ _ _ _ st.ev
  kapB := @EvlSt.kapB _ _ _ _ _ _ _ _ st.ev
  Harm := @EvlSt.Harm _ _ _ _ _ _ _ _ st.ev
  SecP := @EvlSt.SecP _ _ _ _ _ _ _ _ st.ev
  evA := @EvlSt.evA _ _ _ _ _ _ _ _ st.ev
  evGt := @EvlSt.evGt _ _ _ _ _ _ _ _ st.ev
  Tp := @HTpSt.Tp _ _ _ _ _ _ _ _ st.hq
  tpAdd := @HTpSt.tpAdd _ _ _ _ _ _ _ _ st.hq
  OmV := @HTpSt.OmV _ _ _ _ _ _ _ _ st.hq
  omAdd := @HTpSt.omAdd _ _ _ _ _ _ _ _ st.hq
  omMod := @HTpSt.omMod _ _ _ _ _ _ _ _ st.hq
  om := @HTpSt.om _ _ _ _ _ _ _ _ st.hq
  ht := @HTpSt.ht _ _ _ _ _ _ _ _ st.hq
  IsHTBlowup := @HTmSt.IsHTBlowup _ _ _ _ _ _ _ _ _ _ st.hm
  eOmP := @HTmSt.eOmP _ _ _ _ _ _ _ _ _ _ st.hm
  SES := @ShfSt.SES _ _ _ _ _ _ _ _ st.sh
  ExactMod := @ShfSt.ExactMod _ _ _ _ _ _ _ _ st.sh
  htSES := @HTmSt.htSES _ _ _ _ _ _ _ _ _ _ st.hm
  nefHT := @CrHSt.nefHT _ _ _ _ _ _ _ _ _ st.cr
  nefQ := @CrDSt.nefQ _ _ _ _ _ _ _ _ st.cd
  descK := @CrHSt.descK _ _ _ _ _ _ _ _ _ st.cr
  bdryLoci := @CrHSt.bdryLoci _ _ _ _ _ _ _ _ _ st.cr
  BT := @HTmSt.BT _ _ _ _ _ _ _ _ _ _ st.hm
  extA := @HTmSt.extA _ _ _ _ _ _ _ _ _ _ st.hm
  compat := @HTmSt.compat _ _ _ _ _ _ _ _ _ _ st.hm
  Crv := @CrDSt.Crv _ _ _ _ _ _ _ _ st.cd
  eDeg := @CrDSt.eDeg _ _ _ _ _ _ _ _ st.cd
  Pm := @CrDSt.Pm _ _ _ _ _ _ _ _ st.cd
  Pm_nonneg := @CrDSt.Pm_nonneg _ _ _ _ _ _ _ _ st.cd
  degLie := @CrDSt.degLie _ _ _ _ _ _ _ _ st.cd
  degLdR := @CrDSt.degLdR _ _ _ _ _ _ _ _ st.cd

theorem bs_loc (b : Option ℕ) : bs st.loc b = ct.B.X b := by cases b <;> rfl

def ex : ModuliIntegralCharts.ExtA D st.loc where
  FlagData := @FlgSt.FlagData _ _ _ _ _ _ _ _ st.fg
  flagCl := @FlgSt.flagCl _ _ _ _ _ _ _ _ st.fg
  allFlags := @FlgSt.allFlags _ _ _ _ _ _ _ _ st.fg
  YY_eq := @FlgSt.YY_eq _ _ _ _ _ _ _ _ st.fg
  Idl := @At.Idl _ _ _ _ _ _ _ ct
  blowUp := @At.blowUp _ _ _ _ _ _ _ ct
  powP := @At.powP _ _ _ _ _ _ _ ct
  pbPrinc := @ChtSt.pbPrinc _ _ _ _ _ _ _ _ st.ch
  Corr := @At.Corr _ _ _ _ _ _ _ ct
  corr_sub := fun _ _ => ⟨fun ⟨_⟩ ⟨_⟩ => rfl⟩
  diagCl := @At.diagCl _ _ _ _ _ _ _ ct
  IvD := @TorSt.IvD _ _ _ _ _ _ _ _ st.tr
  jIdl := fun b d => match b, d with
    | none, d => st.tr.jIdl none d
    | some n, d => st.tr.jIdl (some n) d
  ZP := @At.ZP _ _ _ _ _ _ _ ct
  spz := @At.spz _ _ _ _ _ _ _ ct
  abP := @At.abP _ _ _ _ _ _ _ ct
  inQ := @At.inQ _ _ _ _ _ _ _ ct
  isGenP := @At.isGenP _ _ _ _ _ _ _ ct
  isGenP_ab := @LawSt.isGenP_ab _ _ _ _ _ _ _ _ st.lw
  gpt := @At.gpt _ _ _ _ _ _ _ ct
  abAt_iff := fun _ => Iff.rfl
  gpt_notQ := fun η => η.2.1
  genFin := @LawSt.genFin _ _ _ _ _ _ _ _ st.lw
  genNe := @LawSt.genNe _ _ _ _ _ _ _ _ st.lw
  redK := @ChtSt.redK _ _ _ _ _ _ _ _ st.ch
  dvRho_pos_iff := @ChtSt.dvRho_pos_iff _ _ _ _ _ _ _ _ st.ch
  genK := @ChtSt.genK _ _ _ _ _ _ _ _ st.ch
  redK_genK := @ChtSt.redK_genK _ _ _ _ _ _ _ _ st.ch
  imgM := @ChtSt.imgM _ _ _ _ _ _ _ _ st.ch
  imgU := @ChtSt.imgU _ _ _ _ _ _ _ _ st.ch
  img_spz := @ChtSt.img_spz _ _ _ _ _ _ _ _ st.ch
  imgU_inQ := @ChtSt.imgU_inQ _ _ _ _ _ _ _ _ st.ch
  chAt_imgM := @ChtSt.chAt_imgM _ _ _ _ _ _ _ _ st.ch
  chAbExact_imgU := @ChtSt.chAbExact_imgU _ _ _ _ _ _ _ _ st.ch
  RFam := @ChtSt.RFam _ _ _ _ _ _ _ _ st.ch
  chFam := @ChtSt.chFam _ _ _ _ _ _ _ _ st.ch
  ptK := @ChtSt.ptK _ _ _ _ _ _ _ _ st.ch
  ptK_good := @ChtSt.ptK_good _ _ _ _ _ _ _ _ st.ch
  vpi := @ChtSt.vpi _ _ _ _ _ _ _ _ st.ch
  vpi_pos := @ChtSt.vpi_pos _ _ _ _ _ _ _ _ st.ch
  ordGe := @ChtSt.ordGe _ _ _ _ _ _ _ _ st.ch
  yEta := @ChtSt.yEta _ _ _ _ _ _ _ _ st.ch
  yEta_good := @ChtSt.yEta_good _ _ _ _ _ _ _ _ st.ch
  homSh := @ShfSt.homSh _ _ _ _ _ _ _ _ st.sh
  homSh_inv := @ShfSt.homSh_inv _ _ _ _ _ _ _ _ st.sh
  isoSec := @ShfSt.isoSec _ _ _ _ _ _ _ _ st.sh
  nrm_isoSec := @ShfSt.nrm_isoSec _ _ _ _ _ _ _ _ st.sh
  isoSymm := @ShfSt.isoSymm _ _ _ _ _ _ _ _ st.sh
  vrat_symm := @ShfSt.vrat_symm _ _ _ _ _ _ _ _ st.sh
  LieV := @FrmSt.LieV _ _ _ _ _ _ _ _ st.fr
  lvAdd := @FrmSt.lvAdd _ _ _ _ _ _ _ _ st.fr
  lvMod := @FrmSt.lvMod _ _ _ _ _ _ _ _ st.fr
  lieL := @FrmSt.lieL _ _ _ _ _ _ _ _ st.fr
  eig := @FrmSt.eig _ _ _ _ _ _ _ _ st.fr
  Wst := @FrmSt.Wst _ _ _ _ _ _ _ _ st.fr
  Wst_le := @FrmSt.Wst_le _ _ _ _ _ _ _ _ st.fr
  taut := @FrmSt.taut _ _ _ _ _ _ _ _ st.fr
  taut_eq := @FrmSt.taut_eq _ _ _ _ _ _ _ _ st.fr
  nrmIn := @FrmSt.nrmIn _ _ _ _ _ _ _ _ st.fr
  nrmRef_def := @FrmSt.nrmRef_def _ _ _ _ _ _ _ _ st.fr
  nrm_Lb_def := @FrmSt.nrm_Lb_def _ _ _ _ _ _ _ _ st.fr
  om_smul := @HTpSt.om_smul _ _ _ _ _ _ _ _ st.hq
  TC := @HTpSt.TC _ _ _ _ _ _ _ _ st.hq
  tcAdd := @HTpSt.tcAdd _ _ _ _ _ _ _ _ st.hq
  tcMod := @HTpSt.tcMod _ _ _ _ _ _ _ _ st.hq
  iT := @HTpSt.iT _ _ _ _ _ _ _ _ st.hq
  iT_span := @HTpSt.iT_span _ _ _ _ _ _ _ _ st.hq
  htC := @HTpSt.htC _ _ _ _ _ _ _ _ st.hq
  htC_iT := @HTpSt.htC_iT _ _ _ _ _ _ _ _ st.hq
  psiC := @HTpSt.psiC _ _ _ _ _ _ _ _ st.hq
  lieGt1 := @HTpSt.lieGt1 _ _ _ _ _ _ _ _ st.hq
  eT := @HTpSt.eT _ _ _ _ _ _ _ _ st.hq
  HTn := @HTmSt.HTn _ _ _ _ _ _ _ _ _ _ st.hm
  htEval := @HTmSt.htEval _ _ _ _ _ _ _ _ _ _ st.hm
  htIdl := @HTmSt.htIdl _ _ _ _ _ _ _ _ _ _ st.hm
  IsHTBlowup_def := @HTmSt.IsHTBlowup_def _ _ _ _ _ _ _ _ _ _ st.hm
  wFib := @HTmSt.wFib _ _ _ _ _ _ _ _ _ _ st.hm
  htFlags := @CrHSt.htFlags _ _ _ _ _ _ _ _ _ st.cr
  omSh := @HTmSt.omSh _ _ _ _ _ _ _ _ _ _ st.hm
  omPat := @HTmSt.omPat _ _ _ _ _ _ _ _ _ _ st.hm
  omPat_def := @HTmSt.omPat_def _ _ _ _ _ _ _ _ _ _ st.hm
  BPt := @HTmSt.BPt _ _ _ _ _ _ _ _ _ _ st.hm
  bfld := @HTmSt.bfld _ _ _ _ _ _ _ _ _ _ st.hm
  OmB := @HTmSt.OmB _ _ _ _ _ _ _ _ _ _ st.hm
  obAdd := @HTmSt.obAdd _ _ _ _ _ _ _ _ _ _ st.hm
  obMod := @HTmSt.obMod _ _ _ _ _ _ _ _ _ _ st.hm
  omB := @HTmSt.omB _ _ _ _ _ _ _ _ _ _ st.hm
  omPB := @HTmSt.omPB _ _ _ _ _ _ _ _ _ _ st.hm
  eOmB := @HTmSt.eOmB _ _ _ _ _ _ _ _ _ _ st.hm
  eB := @HTmSt.eB _ _ _ _ _ _ _ _ _ _ st.hm
  YsP := @CrHSt.YsP _ _ _ _ _ _ _ _ _ st.cr
  ysBd := @CrHSt.ysBd _ _ _ _ _ _ _ _ _ st.cr
  FlP := @CrHSt.FlP _ _ _ _ _ _ _ _ _ st.cr
  hFl := @CrHSt.hFl _ _ _ _ _ _ _ _ _ st.cr
  FlCl := @CrHSt.FlCl _ _ _ _ _ _ _ _ _ st.cr
  flMem := @CrHSt.flMem _ _ _ _ _ _ _ _ _ st.cr
  flDim := @CrHSt.flDim _ _ _ _ _ _ _ _ _ st.cr
  Sum1 := @CrHSt.Sum1 _ _ _ _ _ _ _ _ _ st.cr
  locus := @CrHSt.locus _ _ _ _ _ _ _ _ _ st.cr
  bdryLoci_def := @CrHSt.bdryLoci_def _ _ _ _ _ _ _ _ _ st.cr
  CrvS := @CrHSt.CrvS _ _ _ _ _ _ _ _ _ st.cr
  degGr := @CrHSt.degGr _ _ _ _ _ _ _ _ _ st.cr
  nefHT_def := @CrHSt.nefHT_def _ _ _ _ _ _ _ _ _ st.cr
  CrvQ := @CrDSt.CrvQ _ _ _ _ _ _ _ _ st.cd
  degGrQ := @CrDSt.degGrQ _ _ _ _ _ _ _ _ st.cd
  nefQ_def := @CrDSt.nefQ_def _ _ _ _ _ _ _ _ st.cd
  degGrD := @CrDSt.degGrD _ _ _ _ _ _ _ _ st.cd
  degLdR_def := @CrDSt.degLdR_def _ _ _ _ _ _ _ _ st.cd
  degLie_f := @CrDSt.degLie_f _ _ _ _ _ _ _ _ st.cd
  degLie_alt := @CrDSt.degLie_alt _ _ _ _ _ _ _ _ st.cd
  eDeg_def := @CrDSt.eDeg_def _ _ _ _ _ _ _ _ st.cd
  Pm_head := @CrDSt.Pm_head _ _ _ _ _ _ _ _ st.cd
  Pm_tail := @CrDSt.Pm_tail _ _ _ _ _ _ _ _ st.cd

def locB : BoundaryLocalData.LocB D st.loc where
  chX := @At.chX _ _ _ _ _ _ _ ct
  xAdd := fun {Z : ct.Mdl} (y : ct.Pt Z) => (inferInstance : AddCommGroup (ct.chX (Z := Z) y))
  xMod := fun {Z : ct.Mdl} (y : ct.Pt Z) => (inferInstance : Module (𝓞 D.host.E) (ct.chX (Z := Z) y))
  phi := @At.phi _ _ _ _ _ _ _ ct
  phi_conj := @LawSt.phi_conj _ _ _ _ _ _ _ _ st.lw
  tau := @MotSt.tau _ _ _ _ _ _ _ _ st.mo
  tau_add_left := @MotSt.tau_add_left _ _ _ _ _ _ _ _ st.mo
  tau_add_right := @MotSt.tau_add_right _ _ _ _ _ _ _ _ st.mo
  tau_symm := @MotSt.tau_symm _ _ _ _ _ _ _ _ st.mo
  tau_smul := @MotSt.tau_smul _ _ _ _ _ _ _ _ st.mo
  be_tau := @MotSt.be_tau _ _ _ _ _ _ _ _ st.mo
  multiplicationLatticeFirst := @MotSt.multiplicationLatticeFirst _ _ _ _ _ _ _ _ st.mo
  multiplicationLatticeSecond := @MotSt.multiplicationLatticeSecond _ _ _ _ _ _ _ _ st.mo
  mulC := @MotSt.mulC _ _ _ _ _ _ _ _ st.mo
  psiV_def := @MotSt.psiV_def _ _ _ _ _ _ _ _ st.mo
  StrictHenselianAcyclic := @ThbSt.StrictHenselianAcyclic _ _ _ _ _ _ _ _ _ st.tb
  squareRootLineBundle := @ThbSt.squareRootLineBundle _ _ _ _ _ _ _ _ _ st.tb
  res2 := @ThbSt.res2 _ _ _ _ _ _ _ _ _ st.tb
  PoiQ := @ThbSt.PoiQ _ _ _ _ _ _ _ _ _ st.tb
  biext := @ThbSt.biext _ _ _ _ _ _ _ _ _ st.tb
  dg := @ThbSt.dg _ _ _ _ _ _ _ _ _ st.tb
  dgq := @ThbSt.dgq _ _ _ _ _ _ _ _ _ st.tb
  dg_res := @ThbSt.dg_res _ _ _ _ _ _ _ _ _ st.tb
  PPq_def := @ThbSt.PPq_def _ _ _ _ _ _ _ _ _ st.tb
  BPt := @BdySt.BPt _ _ _ _ _ _ _ _ st.bd
  Rl := @BdySt.Rl _ _ _ _ _ _ _ _ st.bd
  iRr := @BdySt.iRr _ _ _ _ _ _ _ _ st.bd
  iRd := @BdySt.iRd _ _ _ _ _ _ _ _ st.bd
  iRl := @BdySt.iRl _ _ _ _ _ _ _ _ st.bd
  iRn := @BdySt.iRn _ _ _ _ _ _ _ _ st.bd
  iRi := @BdySt.iRi _ _ _ _ _ _ _ _ st.bd
  iRc := @BdySt.iRc _ _ _ _ _ _ _ _ st.bd
  Yb := @BdySt.Yb _ _ _ _ _ _ _ _ st.bd
  iYa := @BdySt.iYa _ _ _ _ _ _ _ _ st.bd
  iYm := @BdySt.iYm _ _ _ _ _ _ _ _ st.bd
  Xb := @BdySt.Xb _ _ _ _ _ _ _ _ st.bd
  iXa := @BdySt.iXa _ _ _ _ _ _ _ _ st.bd
  iXm := @BdySt.iXm _ _ _ _ _ _ _ _ st.bd
  phib := @BdySt.phib _ _ _ _ _ _ _ _ st.bd
  phib_conj := @BdySt.phib_conj _ _ _ _ _ _ _ _ st.bd
  taub := @BdySt.taub _ _ _ _ _ _ _ _ st.bd
  taub_add_left := @BdySt.taub_add_left _ _ _ _ _ _ _ _ st.bd
  taub_add_right := @BdySt.taub_add_right _ _ _ _ _ _ _ _ st.bd
  taub_symm := @BdySt.taub_symm _ _ _ _ _ _ _ _ st.bd
  taub_smul := @BdySt.taub_smul _ _ _ _ _ _ _ _ st.bd
  taub_pos := @BdySt.taub_pos _ _ _ _ _ _ _ _ st.bd
  Sg := @BdySt.Sg _ _ _ _ _ _ _ _ st.bd
  iSg := @BdySt.iSg _ _ _ _ _ _ _ _ st.bd
  iSk := @BdySt.iSk _ _ _ _ _ _ _ _ st.bd
  iSm := @BdySt.iSm _ _ _ _ _ _ _ _ st.bd
  iSt := @BdySt.iSt _ _ _ _ _ _ _ _ st.bd
  Sreg := @BdySt.Sreg _ _ _ _ _ _ _ _ st.bd
  fc := @BdySt.fc _ _ _ _ _ _ _ _ st.bd
  trU := @BdySt.trU _ _ _ _ _ _ _ _ st.bd
  oX := @ShfSt.oX _ _ _ _ _ _ _ _ st.sh
  oX_inv := @ShfSt.oX_inv _ _ _ _ _ _ _ _ st.sh
  secOf := @ShfSt.secOf _ _ _ _ _ _ _ _ st.sh
  nrm_secOf := @ShfSt.nrm_secOf _ _ _ _ _ _ _ _ st.sh
  keySh_inv := @KeySt.keySh_inv _ _ _ _ _ _ _ _ st.ky
  dimB := @MotSt.dimB _ _ _ _ _ _ _ _ st.mo
  dimB_add := @MotSt.dimB_add _ _ _ _ _ _ _ _ st.mo
  FB := @JetSt.FB _ _ _ _ _ _ _ _ _ _ st.jt
  fbAdd := @JetSt.fbAdd _ _ _ _ _ _ _ _ _ _ st.jt
  fbMod := @JetSt.fbMod _ _ _ _ _ _ _ _ _ _ st.jt
  nB := @JetSt.nB _ _ _ _ _ _ _ _ _ _ st.jt
  sgc := @JetSt.sgc _ _ _ _ _ _ _ _ _ _ st.jt
  trB := @JetSt.trB _ _ _ _ _ _ _ _ _ _ st.jt
  trB_norm := @JetSt.trB_norm _ _ _ _ _ _ _ _ _ _ st.jt
  alp := @ThgSt.alp _ _ _ _ _ _ _ _ _ st.tg
  alp_spec := @ThgSt.alp_spec _ _ _ _ _ _ _ _ _ st.tg
  th1 := @ThgSt.th1 _ _ _ _ _ _ _ _ _ st.tg
  pbAl := @ThgSt.pbAl _ _ _ _ _ _ _ _ _ st.tg
  vth_def := @ThgSt.vth_def _ _ _ _ _ _ _ _ _ st.tg
  jX := @JetSt.jX _ _ _ _ _ _ _ _ _ _ st.jt
  intJet_free := @JetSt.intJet_free _ _ _ _ _ _ _ _ _ _ st.jt
  jX_int := @JetSt.jX_int _ _ _ _ _ _ _ _ _ _ st.jt
  jet_fourier := @JetSt.jet_fourier _ _ _ _ _ _ _ _ _ _ st.jt

end Stages

end GlobalTheory.LocM
