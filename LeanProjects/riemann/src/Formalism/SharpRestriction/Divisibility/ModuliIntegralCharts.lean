import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.ParConsts
import Formalism.GelfandTransference.EnergyIdentity

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts

open Formalism.BasicNotions NumberField

structure CF (p : ℕ) where
  C : Type
  [fld : NontriviallyNormedField C]
  [ultra : IsUltrametricDist C]
  [ac : IsAlgClosed C]
  [cpl : CompleteSpace C]
  [ch0 : CharZero C]
  norm_p : ‖(p : C)‖ = (p : ℝ)⁻¹

attribute [instance] CF.fld CF.ultra CF.ac CF.cpl CF.ch0

def Ospan {C V : Type} [NormedField C] [AddCommGroup V] [Module C V] (S : Set V) : AddSubgroup V :=
  AddSubgroup.closure {v | ∃ a : C, ‖a‖ ≤ 1 ∧ ∃ s ∈ S, v = a • s}

section Forms

variable {E : Type} [Field E] [NumberField E]

def SymB (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] :
    Submodule ℝ (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) where
  carrier := {β | (∀ a b, β a b = β b a) ∧
    ∀ (c c' : 𝓞 E), (c' : E) = cj (c : E) → ∀ a b, β (c • a) b = β a (c' • b)}
  add_mem' := by
    rintro β γ ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨fun a b => ?_, fun c c' h a b => ?_⟩
    · simp [h1 a b, h3 a b]
    · simp [h2 c c' h a b, h4 c c' h a b]
  zero_mem' := by simp
  smul_mem' := by
    rintro t β ⟨h1, h2⟩
    refine ⟨fun a b => ?_, fun c c' h a b => ?_⟩
    · simp [h1 a b]
    · simp [h2 c c' h a b]

def phiC (cj : E → E) {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y] (b : SymB cj Y) : ℝ :=
  sInf {x | ∃ l : SymB cj Y →ₗ[ℝ] ℝ,
    (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
    (∀ β : SymB cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β) ∧ x = l b}

end Forms

abbrev PsiT (D : Formalism.BasicNotions.D7) : Type := ↥(D.R.Psi)

structure Loc (D : Formalism.BasicNotions.D7) (r j p : ℕ) where

  Mdl : Type

  Xm : Mdl

  YY : Mdl

  Xn : ℕ → Mdl

  Pt : Mdl → Type

  fld : ∀ {Z : Mdl}, Pt Z → CF p

  Ylat : ∀ {Z : Mdl}, Pt Z → Type
  [ylAdd : ∀ {Z : Mdl} (y : Pt Z), AddCommGroup (Ylat y)]
  [ylMod : ∀ {Z : Mdl} (y : Pt Z), Module (𝓞 D.host.E) (Ylat y)]
  [ylFree : ∀ {Z : Mdl} (y : Pt Z), Module.Free ℤ (Ylat y)]
  [ylFin : ∀ {Z : Mdl} (y : Pt Z), Module.Finite ℤ (Ylat y)]

  be : ∀ {Z : Mdl} (y : Pt Z), Ylat y →ₗ[ℤ] Ylat y →ₗ[ℤ] ℝ
  be_symm : ∀ {Z : Mdl} (y : Pt Z) (a b : Ylat y), be y a b = be y b a
  be_bal : ∀ {Z : Mdl} (y : Pt Z) (c c' : 𝓞 D.host.E), (c' : D.host.E) = D.host.conj (c : D.host.E) →
    ∀ a b : Ylat y, be y (c • a) b = be y a (c' • b)

  be_posDef : ∀ {Z : Mdl} (y : Pt Z), ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ (Ylat y)),
    ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ k, c i * c k * be y (b i) (b k)

  yl_rank : ∀ {Z : Mdl} (y : Pt Z), ∃ ρ : ℕ, Module.finrank ℤ (Ylat y) = 2 * D.R.f * ρ ∧
    (1 ≤ j → j + 1 ≤ r → ρ ≤ j ∧ ρ + j ≤ r)

  Gen : Mdl → Type

  abAt : ∀ {Z : Mdl}, Gen Z → Prop

  Sh : Mdl → Type

  IsInv : ∀ {Z : Mdl}, Sh Z → Prop

  IsLocFree : ∀ {Z : Mdl}, Sh Z → Prop

  Sec : ∀ {Z : Mdl}, Sh Z → Type
  [secAdd : ∀ {Z : Mdl} (F : Sh Z), AddCommGroup (Sec F)]

  H0 : ∀ {Z : Mdl} (F : Sh Z), AddSubgroup (Sec F)

  nrm : ∀ {Z : Mdl} (F : Sh Z), Sec F → Pt Z → ℝ
  nrm_nonneg : ∀ {Z : Mdl} (F : Sh Z) (f : Sec F) (y : Pt Z), 0 ≤ nrm F f y

  norm_le_one_of_mem_sections : ∀ {Z : Mdl} (F : Sh Z) (f : Sec F), f ∈ H0 F → ∀ y, nrm F f y ≤ 1

  GIso : ∀ {Z : Mdl}, Sh Z → Sh Z → Type

  vrat : ∀ {Z : Mdl} {F₁ F₂ : Sh Z}, GIso F₁ F₂ → Pt Z → ℝ

  Lb : (PsiT D → ℕ → ℤ) → Sh YY
  Lb_inv : ∀ l, IsInv (Lb l)

  nrmRef : ∀ l, Sec (Lb l) → Pt YY → ℝ

  DVP : Type

  dvRho : DVP → ℕ

  Ext : DVP → Type

  Chart : Mdl → (y : DVP) → Ext y → Type

  chAt : ∀ {Z y e}, Chart Z y e → Prop

  chOpen : ∀ {Z y e}, Chart Z y e → Prop

  chAbExact : ∀ {Z y e}, Chart Z y e → Prop

  chModU : ∀ {Z y e}, Chart Z y e → Prop

  chConst : ∀ {Z y e}, Chart Z y e → Prop

  PL : Type

  phiAt : PL → ∀ {Z : Mdl}, Pt Z → ℝ

  phiAt_zero : ∀ (φ : PL) {Z : Mdl} (y : Pt Z), Subsingleton (Ylat y) → phiAt φ y = 0

  divGe : ∀ {Z : Mdl} (F : Sh Z), Sec F → ℚ → PL → Prop

  FJd : Type

  Chr : FJd → Type

  fjN : ∀ l, Sec (Lb l) → (t : FJd) → Chr t → ℝ

  Unim : Type

  LBG : Unim → Type

  LBGq : Unim → Type
  resQ : ∀ {La}, LBG La → LBGq La

  PPq : ∀ La, LBGq La

  symmG : ∀ {La}, LBG La → Prop
  rigG : ∀ {La}, LBG La → Prop

  LBGt : ∀ (y : Pt Xm), Unim → Type
  LBB : ∀ (y : Pt Xm), Unim → Type
  resGt : ∀ {La}, LBG La → ∀ y, LBGt y La
  prPull : ∀ {y La}, LBB y La → LBGt y La

  principal : ∀ {y La}, LBB y La → Prop

  psiV : ∀ {Z : Mdl} (y : Pt Z), Ylat y → ℝ

  piPP : Sh Xm

  keySh : ℕ → Sh Xm

  latStd : ℕ → Unim

  At : Pt Xm → Unim → ℕ → Type
  [atAdd : ∀ y La n, AddCommGroup (At y La n)]
  [atFin : ∀ y La n, Fintype (At y La n)]

  at_tors : ∀ y La n (x : At y La n), n • x = 0
  at_card : ∀ y nW n, 0 < n → Fintype.card (At y (latStd nW) n) = n ^ (2 * (D.R.f * r * nW))

  Th : Pt Xm → Unim → ℕ → Type
  [thGrp : ∀ y La n, Group (Th y La n)]
  ovr : ∀ y La n, Th y La n →* Multiplicative (At y La n)
  ovr_surj : ∀ y La n, Function.Surjective (ovr y La n)
  scal : ∀ y La n, ((fld y).C)ˣ →* Th y La n
  scal_inj : ∀ y La n, Function.Injective (scal y La n)
  scal_central : ∀ y La n a g, scal y La n a * g = g * scal y La n a
  ker_ovr : ∀ y La n g, ovr y La n g = 1 ↔ ∃ a, scal y La n a = g

  dl : ∀ y La n, Th y La n ≃* Th y La n
  dl_ovr : ∀ y La n g, ovr y La n (dl y La n g) = (ovr y La n g)⁻¹
  dl_scal : ∀ y La n a, dl y La n (scal y La n a) = scal y La n a
  dl_dl : ∀ y La n g, dl y La n (dl y La n g) = g

  Sn : Pt Xm → Unim → ℕ → Type
  [snAdd : ∀ y La n, AddCommGroup (Sn y La n)]
  [snMod : ∀ y La n, Module (fld y).C (Sn y La n)]
  act : ∀ y La n, Th y La n →* Module.End (fld y).C (Sn y La n)
  act_scal : ∀ y La n a s, act y La n (scal y La n a) s = (a : (fld y).C) • s

  vth : ∀ y La n, Sn y La n

  Jet : Pt Xm → Unim → ℕ → ℕ → Type
  [jAdd : ∀ y La n DF, AddCommGroup (Jet y La n DF)]
  [jMod : ∀ y La n DF, Module (fld y).C (Jet y La n DF)]
  intJet : ∀ y La n DF, AddSubgroup (Jet y La n DF)
  jet : ∀ y La n DF, Sn y La n →ₗ[(fld y).C] Jet y La n DF

  LieGt : Pt Xm → PsiT D × Bool → Type
  LieB : Pt Xm → PsiT D × Bool → Type
  LieT : Pt Xm → PsiT D × Bool → Type
  [lgAdd : ∀ y σ, AddCommGroup (LieGt y σ)]
  [lbAdd : ∀ y σ, AddCommGroup (LieB y σ)]
  [ltAdd : ∀ y σ, AddCommGroup (LieT y σ)]
  resB : ∀ y σ, LieGt y σ →+ LieB y σ
  incT : ∀ y σ, LieT y σ →+ LieGt y σ

  kapGt : ∀ y σ, LieGt y σ → LieGt y σ → (fld y).C
  kapB : ∀ y σ, LieB y σ → LieB y σ → (fld y).C

  Harm : Pt Xm → Type
  SecP : Pt Xm → Type
  evA : ∀ y, Harm y → SecP y → (fld y).C
  evGt : ∀ y, Harm y → SecP y → (fld y).C

  Tp : ∀ {Z : Mdl}, Pt Z → Type
  [tpAdd : ∀ {Z : Mdl} (y : Pt Z), AddCommGroup (Tp y)]

  OmV : ∀ {Z : Mdl}, Pt Z → Type
  [omAdd : ∀ {Z : Mdl} (y : Pt Z), AddCommGroup (OmV y)]
  [omMod : ∀ {Z : Mdl} (y : Pt Z), Module (fld y).C (OmV y)]
  om : ∀ {Z : Mdl} (y : Pt Z), AddSubgroup (OmV y)

  ht : ∀ {Z : Mdl} (y : Pt Z), Tp y →+ OmV y

  IsHTBlowup : Mdl → Mdl → Prop

  eOmP : ∀ Z : Mdl, Bool → PsiT D → Sh Z

  SES : Mdl → Type
  ExactMod : ∀ {Z : Mdl}, SES Z → ℕ → Prop

  htSES : ∀ Z : Mdl, PsiT D → SES Z

  nefHT : Mdl → (PsiT D → ℕ → ℝ) → Prop

  nefQ : (PsiT D → ℕ → ℝ) → Prop

  descK : Mdl → (PsiT D → ℕ → ℤ) → Prop

  bdryLoci : Mdl → Prop

  BT : ℕ → Type
  extA : ∀ {n}, BT n → Prop
  compat : ∀ {n}, BT n → BT (n + 1) → Prop

  Crv : Type

  eDeg : Crv → ℤ
  Pm : Crv → ℤ
  Pm_nonneg : ∀ c, 0 ≤ Pm c

  degLie : Crv → PsiT D → Bool → ℤ

  degLdR : Crv → (PsiT D → ℕ → ℝ) → ℝ

attribute [instance] Loc.ylAdd Loc.ylMod Loc.ylFree Loc.ylFin Loc.secAdd Loc.atAdd Loc.atFin Loc.thGrp Loc.snAdd
  Loc.snMod Loc.jAdd Loc.jMod Loc.lgAdd
  Loc.lbAdd Loc.ltAdd Loc.tpAdd Loc.omAdd Loc.omMod

section LocDefs

variable {D : Formalism.BasicNotions.D7}

namespace Loc

variable {r j p : ℕ} (L : Loc D r j p)

theorem be_expand {Z : L.Mdl} (y : L.Pt Z) {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ (L.Ylat y))
    (u v : L.Ylat y) : L.be y u v =
      ∑ i, ∑ k, ((b.repr u i : ℤ) : ℝ) * ((b.repr v k : ℤ) : ℝ) * L.be y (b i) (b k) := by
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem be_pos {Z : L.Mdl} (y : L.Pt Z) (a : L.Ylat y) (ha : a ≠ 0) : 0 < L.be y a a := by
  obtain ⟨ι, _, b, h⟩ := L.be_posDef y
  rw [L.be_expand y b a a]
  refine h (fun i => ((b.repr a i : ℤ) : ℝ)) fun h0 => ha (b.repr.injective (Finsupp.ext fun i => ?_))
  simpa using congrFun h0 i

private theorem sum4 {A B C E : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype E] (F : A → B → C → E → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e = ∑ c, ∑ e, ∑ a, ∑ b, F a b c e :=
  calc _ = ∑ a, ∑ c, ∑ b, ∑ e, F a b c e := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ e, F a b c e := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ e, ∑ b, F a b c e :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem be_posDef_basis {Z : L.Mdl} (y : L.Pt Z) {κ : Type} [Fintype κ]
    (b' : Module.Basis κ ℤ (L.Ylat y)) (c' : κ → ℝ) (hc : c' ≠ 0) :
    0 < ∑ m, ∑ n, c' m * c' n * L.be y (b' m) (b' n) := by
  classical
  obtain ⟨ι, _, b, h⟩ := L.be_posDef y
  have hne : (fun i => ∑ m, c' m * ((b.repr (b' m) i : ℤ) : ℝ)) ≠ 0 := by
    intro h0
    apply hc
    funext m0
    have hd : ∀ m, ∑ i, ((b.repr (b' m) i : ℤ) : ℝ) * ((b'.repr (b i) m0 : ℤ) : ℝ) = if m = m0 then 1 else 0 := by
      intro m
      have h1 := congrArg (fun v => b'.repr v m0) (b.sum_repr (b' m))
      simp only [map_sum, map_zsmul, Finsupp.finsetSum_apply, Finsupp.smul_apply, Module.Basis.repr_self,
        Finsupp.single_apply, smul_eq_mul] at h1
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) h1
      push_cast at h2
      simpa using h2
    have key : ∑ i, (∑ m, c' m * ((b.repr (b' m) i : ℤ) : ℝ)) * ((b'.repr (b i) m0 : ℤ) : ℝ) = c' m0 := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc, ← Finset.mul_sum, hd]
      simp
    rw [← key]
    exact Finset.sum_eq_zero fun i _ => by rw [congrFun h0 i]; simp
  refine lt_of_lt_of_eq (h _ hne) ?_
  simp only [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  refine (sum4 _).trans ?_
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [L.be_expand y b (b' m) (b' n), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem gram_posDef {Z : L.Mdl} (y : L.Pt Z) {κ : Type} [Fintype κ] (b' : Module.Basis κ ℤ (L.Ylat y)) :
    (Matrix.of fun m n => L.be y (b' m) (b' n)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.IsHermitian.ext fun m n => by simp [L.be_symm y])
    fun c hc => lt_of_lt_of_eq (L.be_posDef_basis y b' c hc) ?_
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum, Pi.star_apply, star_trivial]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring

def good {Z : L.Mdl} (y : L.Pt Z) : Prop := Subsingleton (L.Ylat y)

def beS {Z : L.Mdl} (y : L.Pt Z) : SymB (fun x : D.host.E => D.host.conj x) (L.Ylat y) :=
  ⟨L.be y, L.be_symm y, fun c c' h a b => L.be_bal y c c' h a b⟩

def phiCy {Z : L.Mdl} (y : L.Pt Z) : ℝ := phiC (fun x : D.host.E => D.host.conj x) (L.beS y)

def dP {Z : L.Mdl} (y : L.Pt Z) : ℕ := Module.finrank ℤ (L.Ylat y)

theorem dP_le (h1 : 1 ≤ j) (h2 : j + 1 ≤ r) {Z : L.Mdl} (y : L.Pt Z) : L.dP y ≤ 2 * D.R.f * min j (r - j) := by
  obtain ⟨ρ, h, hb⟩ := L.yl_rank y
  obtain ⟨h3, h4⟩ := hb h1 h2
  rw [dP, h]
  exact Nat.mul_le_mul_left _ (le_min h3 (by omega))

def cJ {Z : L.Mdl} (y : L.Pt Z) (n DF : ℕ) : ℝ :=
  ((L.dP y : ℝ) ^ 5 * (D.R.f : ℝ) ^ 2 * D.host.rdE ^ 2 / 2) * (DF : ℝ) ^ 2 / (n : ℝ)

def SymLift (y : L.Pt L.Xm) (La : L.Unim) (n : ℕ) (sg : L.At y La n → L.Th y La n) : Prop :=
  ∀ x, L.ovr y La n (sg x) = Multiplicative.ofAdd x ∧ L.dl y La n (sg x) = (sg x)⁻¹ ∧ sg x ^ n = 1

def secJet (y : L.Pt L.Xm) (La : L.Unim) (n DF : ℕ) (sg : L.At y La n → L.Th y La n) :
    Set (L.Jet y La n DF) :=
  Set.range fun x => L.jet y La n DF (L.act y La n (sg x) (L.vth y La n))

end Loc

def Dom {α : Type} [LE α] (r : ℕ) (l : PsiT D → ℕ → α) : Prop :=
  ∀ τ i, 1 ≤ i → i < r → l τ (i + 1) ≤ l τ i

def NHyp (D : Formalism.BasicNotions.D7) (p n : ℕ) : Prop :=
  Odd n ∧ Nat.Coprime n p ∧
    ((∃ mm : ℕ, n = mm ^ 2) ∨ ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧
      (π : D.host.E) * D.host.conj (π : D.host.E) = (n : D.host.E))

end LocDefs

section Ext

def bs {D : D7} {r j p : ℕ} (L : Loc D r j p) : Option ℕ → L.Mdl
  | none => L.Xm
  | some n => L.Xn n

def LvOK (N : ℕ) : Option ℕ → Prop
  | none => True
  | some n => 3 ≤ n ∧ n ≤ N

def isCp {D : D7} {r j p : ℕ} (L : Loc D r j p) {Z : L.Mdl} (y : L.Pt Z) : Prop :=
  Dense {x : (L.fld y).C | IsAlgebraic ℚ x}

def IsChart {D : D7} {r j p : ℕ} (L : Loc D r j p) {Z y e} (χ : L.Chart Z y e) : Prop :=
  L.chAt χ ∧ L.chOpen χ ∧ L.chAbExact χ ∧ L.chModU χ ∧ L.chConst χ

structure ExtA (D : D7) {r j p : ℕ} (L : Loc D r j p) where

  FlagData : L.Mdl → Type

  flagCl : ∀ Z, FlagData Z → L.Mdl

  allFlags : FlagData L.Xm

  YY_eq : L.YY = flagCl L.Xm allFlags

  Idl : L.Mdl → Type

  blowUp : ∀ Z, Idl Z → L.Mdl

  powP : ∀ {Z}, Idl Z → Prop

  pbPrinc : ∀ {Z y e}, Idl Z → L.Chart Z y e → Prop

  Corr : L.Mdl → L.Mdl → Type

  corr_sub : ∀ Z₁ Z₂, Subsingleton (Corr Z₁ Z₂) := by intros; infer_instance

  diagCl : ∀ Z₁ Z₂, Corr Z₁ Z₂ → L.Mdl

  IvD : Option ℕ → Type

  jIdl : ∀ b, IvD b → Idl (bs L b)

  ZP : L.Mdl → Type

  spz : ∀ {Z}, ZP Z → ZP Z → Prop

  abP : ∀ {Z}, ZP Z → Prop

  inQ : ∀ {Z}, ZP Z → Prop

  isGenP : ∀ {Z}, ZP Z → Prop

  isGenP_ab : ∀ {Z} (x : ZP Z), isGenP x → abP x

  gpt : ∀ {Z}, L.Gen Z → ZP Z
  abAt_iff : ∀ {Z} (η : L.Gen Z), L.abAt η ↔ abP (gpt η)
  gpt_notQ : ∀ {Z} (η : L.Gen Z), ¬ inQ (gpt η)

  genFin : ∀ Z, Finite (L.Gen Z)
  genNe : ∀ Z, Nonempty (L.Gen Z)

  redK : ∀ Z, L.DVP → ZP Z

  dvRho_pos_iff : ∀ Z (y : L.DVP), 0 < L.dvRho y ↔ ¬ abP (redK Z y)

  genK : ∀ {Z}, L.Gen Z → L.DVP
  redK_genK : ∀ {Z} (η : L.Gen Z), redK Z (genK η) = gpt η

  imgM : ∀ {Z y e}, L.Chart Z y e → ZP Z
  imgU : ∀ {Z y e}, L.Chart Z y e → ZP Z
  img_spz : ∀ {Z y e} (χ : L.Chart Z y e), spz (imgU χ) (imgM χ)

  imgU_inQ : ∀ {Z y e} (χ : L.Chart Z y e), inQ (imgU χ)

  chAt_imgM : ∀ {Z y e} (χ : L.Chart Z y e), L.chAt χ → imgM χ = redK Z y

  chAbExact_imgU : ∀ {Z y e} (χ : L.Chart Z y e), L.chAbExact χ → ¬ abP (imgU χ)

  RFam : ∀ y, L.Ext y → Type

  chFam : ∀ {Z y e}, L.Chart Z y e → RFam y e

  ptK : ∀ Z, L.DVP → L.Pt Z
  ptK_good : ∀ Z y, L.good (ptK Z y) ↔ L.dvRho y = 0

  vpi : ∀ {y}, L.Ext y → ℝ
  vpi_pos : ∀ {y} (e : L.Ext y), 0 < vpi e

  ordGe : ∀ {Z y e}, L.Chart Z y e → ∀ F : L.Sh Z, L.Sec F → ℝ → Prop

  yEta : ∀ {Z}, L.Gen Z → L.Pt Z
  yEta_good : ∀ {Z} (η : L.Gen Z), L.good (yEta η) ↔ L.abAt η

  homSh : ∀ {Z}, L.Sh Z → L.Sh Z → L.Sh Z
  homSh_inv : ∀ {Z} (F₁ F₂ : L.Sh Z), L.IsInv F₁ → L.IsInv F₂ → L.IsInv (homSh F₁ F₂)
  isoSec : ∀ {Z} {F₁ F₂ : L.Sh Z}, L.GIso F₁ F₂ → L.Sec (homSh F₁ F₂)
  nrm_isoSec : ∀ {Z} {F₁ F₂ : L.Sh Z} (φ : L.GIso F₁ F₂) (y : L.Pt Z),
    L.nrm (homSh F₁ F₂) (isoSec φ) y = (p : ℝ) ^ (-(L.vrat φ y))
  isoSymm : ∀ {Z} {F₁ F₂ : L.Sh Z}, L.GIso F₁ F₂ → L.GIso F₂ F₁
  vrat_symm : ∀ {Z} {F₁ F₂ : L.Sh Z} (φ : L.GIso F₁ F₂) (y : L.Pt Z),
    L.vrat (isoSymm φ) y = -(L.vrat φ y)

  LieV : L.Pt L.YY → Type
  [lvAdd : ∀ y, AddCommGroup (LieV y)]
  [lvMod : ∀ y, Module (L.fld y).C (LieV y)]
  lieL : ∀ y, AddSubgroup (LieV y)
  eig : ∀ y, PsiT D × Bool → Submodule (L.fld y).C (LieV y)
  Wst : ∀ y, PsiT D × Bool → ℕ → Submodule (L.fld y).C (LieV y)
  Wst_le : ∀ y σ i, Wst y σ i ≤ eig y σ

  taut : ∀ y, PsiT D × Bool → ℕ → AddSubgroup (LieV y)
  taut_eq : ∀ y σ i, taut y σ i = (Wst y σ i).toAddSubgroup ⊓ lieL y

  nrmIn : ∀ l, L.Sec (L.Lb l) → ∀ y : L.Pt L.YY, (PsiT D × Bool → ℕ → AddSubgroup (LieV y)) → ℝ

  nrmRef_def : ∀ l f y, L.nrmRef l f y =
    nrmIn l f y (fun σ i => (Wst y σ i).toAddSubgroup ⊓ ((eig y σ).toAddSubgroup ⊓ lieL y))

  nrm_Lb_def : ∀ l f y, L.nrm (L.Lb l) f y = nrmIn l f y (taut y)

  om_smul : ∀ {Z} (y : L.Pt Z) (a : (L.fld y).C), ‖a‖ ≤ 1 → ∀ v ∈ L.om y, a • v ∈ L.om y

  TC : ∀ {Z}, L.Pt Z → Type
  [tcAdd : ∀ {Z} (y : L.Pt Z), AddCommGroup (TC y)]
  [tcMod : ∀ {Z} (y : L.Pt Z), Module (L.fld y).C (TC y)]
  iT : ∀ {Z} (y : L.Pt Z), L.Tp y →+ TC y
  iT_span : ∀ {Z} (y : L.Pt Z), Submodule.span (L.fld y).C (Set.range (iT y)) = ⊤
  htC : ∀ {Z} (y : L.Pt Z), TC y →ₗ[(L.fld y).C] L.OmV y
  htC_iT : ∀ {Z} (y : L.Pt Z) t, htC y (iT y t) = L.ht y t
  psiC : ∀ {Z} (y : L.Pt Z), TC y →ₗ[(L.fld y).C] TC y →ₗ[(L.fld y).C] (L.fld y).C
  lieGt1 : ∀ {Z} (y : L.Pt Z), Submodule (L.fld y).C (TC y)

  eT : ∀ {Z} (y : L.Pt Z), PsiT D → TC y →ₗ[(L.fld y).C] TC y

  HTn : ℕ → Type

  htEval : ∀ {n}, HTn n → ∀ y : L.Pt (L.Xn n), L.Tp y →+ L.OmV y

  htIdl : ∀ {n}, HTn n → Idl (L.Xn n)

  IsHTBlowup_def : ∀ n Z', 3 ≤ n → (L.IsHTBlowup Z' (L.Xn n) ↔ ∃ h : HTn n,
    (∀ (y : L.Pt (L.Xn n)) (t : L.Tp y), htEval h y t ∈ L.om y ∧
      ∃ v ∈ L.om y, htEval h y t - L.ht y t = ((p : (L.fld y).C) ^ n) • v) ∧
    Z' = blowUp (L.Xn n) (htIdl h))

  wFib : ∀ {n}, HTn n → ∀ y : L.Pt (L.Xn n), PsiT D → AddSubgroup (TC y)

  htFlags : ∀ Z, FlagData Z

  omSh : ∀ Z, L.Sh Z

  omPat : ∀ {Z} (y : L.Pt Z), AddSubgroup (L.OmV y)

  omPat_def : ∀ n Z', 3 ≤ n → L.IsHTBlowup Z' (L.Xn n) → ∀ y : L.Pt Z',
    omPat y = L.om y ⊓ (Ospan (C := (L.fld y).C) (Set.range (L.ht y)) ⊔
      (L.om y).map (DistribSMul.toAddMonoidHom (L.OmV y) ((p : (L.fld y).C) ^ n)))

  BPt : L.Mdl → Type
  bfld : ∀ {Z}, BPt Z → CF p
  OmB : ∀ {Z}, BPt Z → Type
  [obAdd : ∀ {Z} (y : BPt Z), AddCommGroup (OmB y)]
  [obMod : ∀ {Z} (y : BPt Z), Module (bfld y).C (OmB y)]
  omB : ∀ {Z} (y : BPt Z), AddSubgroup (OmB y)
  omPB : ∀ {Z} (y : BPt Z), AddSubgroup (OmB y)
  eOmB : ∀ {Z} (y : BPt Z), PsiT D → AddSubgroup (OmB y)
  eB : ∀ {Z} (y : BPt Z), PsiT D → OmB y →ₗ[(bfld y).C] OmB y

  YsP : L.Mdl → Type
  ysBd : ∀ {Z}, YsP Z → Prop

  FlP : Type
  hFl : ∀ {Z}, YsP Z → FlP
  FlCl : Type
  flMem : FlP → FlCl → Prop
  flDim : FlCl → ℕ

  Sum1 : Type
  locus : Sum1 → FlCl

  bdryLoci_def : ∀ Z, L.bdryLoci Z ↔ ∃ S : Set Sum1, S.Finite ∧
    (∀ x : YsP Z, ysBd x → ∃ ℓ ∈ S, flMem (hFl x) (locus ℓ)) ∧
    ∀ ℓ ∈ S, flDim (locus ℓ) + D.R.f * (r - 1) = D.R.f * (r * (r - 1) / 2)

  CrvS : L.Mdl → Type

  degGr : ∀ {Z}, CrvS Z → PsiT D → ℕ → ℤ

  nefHT_def : ∀ Z (l : PsiT D → ℕ → ℝ), L.nefHT Z l ↔
    ∀ C : CrvS Z, 0 ≤ -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 r, l τ i * (degGr C τ i : ℝ)

  CrvQ : Type

  degGrQ : CrvQ → PsiT D → ℕ → ℤ

  nefQ_def : ∀ l : PsiT D → ℕ → ℝ, L.nefQ l ↔
    ∀ C : CrvQ, 0 ≤ -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 r, l τ i * (degGrQ C τ i : ℝ)

  degGrD : L.Crv → PsiT D → ℕ → ℤ
  degLdR_def : ∀ CC (μ : PsiT D → ℕ → ℝ), L.degLdR CC μ =
    -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 r, μ τ i * (degGrD CC τ i : ℝ)
  degLie_f : ∀ CC τ, L.degLie CC τ false = ∑ i ∈ Finset.Icc 1 j, degGrD CC τ i
  degLie_alt : ∀ CC τ, L.degLie CC τ true = -∑ i ∈ Finset.Icc (j + 1) r, degGrD CC τ i

  eDeg_def : DV.UnramE D p → ∀ CC, L.eDeg CC = -∑ᶠ τ, (L.degLie CC τ false + L.degLie CC τ true)

  Pm_head : ∀ CC τ i, 1 ≤ i → i ≤ j → ∑ k ∈ Finset.Icc 1 i, degGrD CC τ k ≤ L.Pm CC

  Pm_tail : ∀ CC τ i, j ≤ i → i ≤ r → -∑ k ∈ Finset.Icc (i + 1) r, degGrD CC τ k ≤ L.Pm CC

attribute [instance] ExtA.lvAdd ExtA.lvMod ExtA.tcAdd ExtA.tcMod ExtA.obAdd ExtA.obMod

namespace ExtA

variable {D : D7} {r j p : ℕ} {L : Loc D r j p}

inductive ZZ (G : ExtA D L) (N : ℕ) : L.Mdl → Prop
  | base (b : Option ℕ) : LvOK N b → ZZ G N (bs L b)
  | flag {Z : L.Mdl} (s : G.FlagData Z) : ZZ G N Z → ZZ G N (G.flagCl Z s)
  | blow {Z : L.Mdl} (I : G.Idl Z) : ZZ G N Z → G.powP I →
      (∀ (y : L.DVP) (e : L.Ext y) (χ : L.Chart Z y e), 0 < L.dvRho y → IsChart L χ →
        G.pbPrinc I χ) → ZZ G N (G.blowUp Z I)
  | diag {Z₁ Z₂ : L.Mdl} (c : G.Corr Z₁ Z₂) : ZZ G N Z₁ → ZZ G N Z₂ → ZZ G N (G.diagCl Z₁ Z₂ c)
  | jblow (b : Option ℕ) (d : G.IvD b) : LvOK N b → ZZ G N (G.blowUp (bs L b) (G.jIdl b d))

def IsHT (G : ExtA D L) {n : ℕ} (h : G.HTn n) : Prop :=
  ∀ (y : L.Pt (L.Xn n)) (t : L.Tp y), G.htEval h y t ∈ L.om y ∧
    ∃ v ∈ L.om y, G.htEval h y t - L.ht y t = ((p : (L.fld y).C) ^ n) • v

def omP (G : ExtA D L) {n : ℕ} (h : G.HTn n) (y : L.Pt (L.Xn n)) : AddSubgroup (L.OmV y) :=
  L.om y ⊓ (Ospan (C := (L.fld y).C) (Set.range (G.htEval h y)) ⊔
    (L.om y).map (DistribSMul.toAddMonoidHom (L.OmV y) ((p : (L.fld y).C) ^ n)))

def aHT (_G : ExtA D L) : Prop :=
  ∀ (Z : L.Mdl) (y : L.Pt Z), (∀ t, L.ht y t ∈ L.om y) ∧
    ∀ v ∈ L.om y, ((p : (L.fld y).C) ^ 2) • v ∈ Ospan (C := (L.fld y).C) (Set.range (L.ht y))

def aKrull (G : ExtA D L) : Prop :=
  ∀ (Z : L.Mdl) (η : L.Gen Z) (x : G.ZP Z), G.spz x (G.gpt η) → x = G.gpt η ∨ G.isGenP x

def aNorm (G : ExtA D L) : Prop :=
  ∀ (Z : L.Mdl) (F : L.Sh Z), L.IsInv F → ∀ f : L.Sec F,
    ((∀ η, L.nrm F f (G.yEta η) ≤ 1) → f ∈ L.H0 F) ∧
    ∀ B : ℝ, (∀ η, L.nrm F f (G.yEta η) ≤ B) → ∀ y, L.nrm F f y ≤ B

def aTube (G : ExtA D L) : Prop :=
  ∀ (Z : L.Mdl) (η : L.Gen Z), L.abAt η → ∀ F : L.Sh Z, L.IsInv F → ∀ f : L.Sec F,
    ∃ y, L.good y ∧ isCp L y ∧ L.nrm F f y = L.nrm F f (G.yEta η)

def aOrd1 (G : ExtA D L) : Prop :=
  ∀ (Z : L.Mdl) (y : L.DVP) (e : L.Ext y) (χ : L.Chart Z y e), IsChart L χ →
    ∀ F : L.Sh Z, L.IsInv F → ∀ (et : L.Sec F) (i : ℚ) (φ : L.PL), L.divGe F et i φ →
      G.ordGe χ F et ((i : ℝ) * L.phiAt φ (G.ptK Z y) / G.vpi e)

def aOrd2 (G : ExtA D L) : Prop :=
  ∀ (Z : L.Mdl) (y : L.DVP) (e : L.Ext y) (χ : L.Chart Z y e), L.chAt χ →
    ∀ F : L.Sh Z, L.IsInv F → ∀ et ∈ L.H0 F, ∀ a : ℝ, G.ordGe χ F et a →
      L.nrm F et (G.ptK Z y) ≤ (p : ℝ) ^ (-(a * G.vpi e))

def aOrd3 (G : ExtA D L) : Prop :=
  ∀ (Z : L.Mdl) (F : L.Sh Z), L.IsInv F → ∀ (et : L.Sec F) (i : ℚ) (φ : L.PL),
    (∀ y : L.DVP, L.nrm F et (G.ptK Z y) ≤ (p : ℝ) ^ (-((i : ℝ) * L.phiAt φ (G.ptK Z y)))) →
    ∀ y, L.nrm F et y ≤ (p : ℝ) ^ (-((i : ℝ) * L.phiAt φ y))

def aSub (G : ExtA D L) : Prop :=
  ∀ (n : ℕ) (Z' : L.Mdl), 3 ≤ n → L.IsHTBlowup Z' (L.Xn n) →
    (∀ τ, L.ExactMod (L.htSES Z' τ) (n - 2)) → ∀ (C : G.CrvS Z') (τ : PsiT D),
      (∀ i, 1 ≤ i → i ≤ r → ∑ k ∈ Finset.Icc 1 i, G.degGr C τ k ≤ 0) ∧
      ∑ k ∈ Finset.Icc 1 r, G.degGr C τ k = 0

def aClose (G : ExtA D L) : Prop :=
  ∀ (n : ℕ) (Z' : L.Mdl), 3 ≤ n → L.IsHTBlowup Z' (L.Xn n) → ∀ CQ : G.CrvQ,
    ∃ (c : ℕ) (s : Finset (G.CrvS Z')) (m : G.CrvS Z' → ℕ), 0 < c ∧
      ∀ τ i, 1 ≤ i → i ≤ r → (c : ℤ) * G.degGrQ CQ τ i = ∑ C ∈ s, (m C : ℤ) * G.degGr C τ i

def ChartLiftsThroughSteps (G : ExtA D L) : Prop :=
  ∀ y : L.DVP, 0 < L.dvRho y → ∀ N, ∃ (e : L.Ext y) (φ : G.RFam y e), ∀ b, LvOK N b →
    ∃ χ : L.Chart (bs L b) y e, IsChart L χ ∧ G.chFam χ = φ

def aCl (G : ExtA D L) : Prop :=
  (∀ Z (s : G.FlagData Z) y e (χ : L.Chart Z y e), IsChart L χ →
    ∃ χ' : L.Chart (G.flagCl Z s) y e, IsChart L χ' ∧ G.chFam χ' = G.chFam χ) ∧
  (∀ Z (I : G.Idl Z) y e (χ : L.Chart Z y e), IsChart L χ → G.powP I → G.pbPrinc I χ →
    ∃ χ' : L.Chart (G.blowUp Z I) y e, IsChart L χ' ∧ G.chFam χ' = G.chFam χ) ∧
  (∀ Z₁ Z₂ (c : G.Corr Z₁ Z₂) y e (χ₁ : L.Chart Z₁ y e) (χ₂ : L.Chart Z₂ y e),
    IsChart L χ₁ → IsChart L χ₂ → G.chFam χ₁ = G.chFam χ₂ →
    ∃ χ' : L.Chart (G.diagCl Z₁ Z₂ c) y e, IsChart L χ' ∧ G.chFam χ' = G.chFam χ₁) ∧
  (∀ b (d : G.IvD b) y e (χ : L.Chart (bs L b) y e), IsChart L χ → G.pbPrinc (G.jIdl b d) χ →
    ∃ χ' : L.Chart (G.blowUp (bs L b) (G.jIdl b d)) y e, IsChart L χ' ∧ G.chFam χ' = G.chFam χ)

def aHTI (G : ExtA D L) : Prop :=
  ∀ n, 3 ≤ n → ∀ h : G.HTn n, G.IsHT h → G.powP (G.htIdl h) ∧
    ∀ (y : L.DVP) (e : L.Ext y) (χ : L.Chart (L.Xn n) y e), 0 < L.dvRho y → IsChart L χ →
      G.pbPrinc (G.htIdl h) χ

def p0 (_G : ExtA D L) : Prop :=
  ∀ l : PsiT D → ℕ → ℤ,
    (∀ f y, L.nrmRef l f y = L.nrm (L.Lb l) f y) ∧
    (L.H0 (L.Lb l) : Set _) = {f | ∀ y, L.nrmRef l f y ≤ 1}

def pC (G : ExtA D L) : Prop :=
  ∀ y : L.DVP, 0 < L.dvRho y → ∀ N,
    (∃ e : L.Ext y, ∀ Z, G.ZZ N Z → ∃ χ : L.Chart Z y e, IsChart L χ) ∧
    ∀ b, LvOK N b → ∀ (e : L.Ext y) (χ : L.Chart (bs L b) y e), IsChart L χ →
      ∀ d : G.IvD b, G.pbPrinc (G.jIdl b d) χ

def pNV (G : ExtA D L) : Prop :=
  ∀ N Z, G.ZZ N Z → ∀ η : L.Gen Z, L.abAt η

def pTR (G : ExtA D L) : Prop :=
  ∀ N Z, G.ZZ N Z →
    (∀ F : L.Sh Z, L.IsInv F → ∀ f : L.Sec F,
      ∃ y₀, L.good y₀ ∧ ∀ y, L.nrm F f y ≤ L.nrm F f y₀) ∧
    (∀ F₁ F₂ : L.Sh Z, L.IsInv F₁ → L.IsInv F₂ → ∀ (φ : L.GIso F₁ F₂) (a b : ℝ),
      (∀ y, L.good y → isCp L y → a ≤ L.vrat φ y ∧ L.vrat φ y ≤ b) →
      ∀ y, a ≤ L.vrat φ y ∧ L.vrat φ y ≤ b)

def pORD (G : ExtA D L) : Prop :=
  ∀ N Z, G.ZZ N Z → ∀ F : L.Sh Z, L.IsInv F →
    ∀ et ∈ L.H0 F, ∀ (i : ℚ) (φ : L.PL), L.divGe F et i φ →
      ∀ y, L.nrm F et y ≤ (p : ℝ) ^ (-((i : ℝ) * L.phiAt φ y))

def pFJ (_G : ExtA D L) : Prop :=
  ∀ l (f : L.Sec (L.Lb l)), (∀ y, L.nrmRef l f y ≤ 1) → ∀ t χ, L.fjN l f t χ ≤ 1

def pHTa (G : ExtA D L) : Prop :=
  ∀ n, 3 ≤ n → (∃ h : G.HTn n, G.IsHT h) ∧
    ∀ y : L.Pt (L.Xn n), LinearMap.ker (G.htC y) = G.lieGt1 y ∧
      ∀ x, x ∈ G.lieGt1 y ↔ ∀ z ∈ G.lieGt1 y, G.psiC y x z = 0

def pHTb (G : ExtA D L) : Prop :=
  ∀ n, 3 ≤ n →
    (∀ h : G.HTn n, G.IsHT h → ∀ y : L.Pt (L.Xn n),
      G.omP h y = Ospan (C := (L.fld y).C) (Set.range (L.ht y)) ∧
      G.omP h y ≤ L.om y ∧
      (∀ v ∈ L.om y, ((p : (L.fld y).C) ^ 2) • v ∈ G.omP h y) ∧
      ∀ τ, G.wFib h y τ = (G.lieGt1 y ⊓ LinearMap.range (G.eT y τ)).toAddSubgroup ⊓
        Ospan (C := (L.fld y).C) (Set.range (G.iT y))) ∧
    ∀ Z', L.IsHTBlowup Z' (L.Xn n) →
      G.ZZ n Z' ∧ G.ZZ n (G.flagCl Z' (G.htFlags Z')) ∧
      (∀ y : L.Pt Z', G.omPat y = Ospan (C := (L.fld y).C) (Set.range (L.ht y)) ∧
        G.omPat y ≤ L.om y ∧ ∀ v ∈ L.om y, ((p : (L.fld y).C) ^ 2) • v ∈ G.omPat y) ∧
      L.IsLocFree (G.omSh Z') ∧
      (∀ s τ, L.IsLocFree (L.eOmP Z' s τ)) ∧
      (∀ τ, L.ExactMod (L.htSES Z' τ) (n - 2))

def pHTc (G : ExtA D L) : Prop :=
  ∀ n, 3 ≤ n → ∀ Z', L.IsHTBlowup Z' (L.Xn n) →
    (∀ l : PsiT D → ℕ → ℝ, Dom r l → L.nefHT Z' l ∧ L.nefQ l) ∧
    (∀ y : G.BPt Z', (∀ τ, G.eOmB y τ = (G.omPB y).map (G.eB y τ).toAddMonoidHom) ∧
      G.omPB y ≤ G.omB y ∧ ∀ v ∈ G.omB y, ((p : (G.bfld y).C) ^ 2) • v ∈ G.omPB y) ∧
    L.bdryLoci Z'

def pHTd (_G : ExtA D L) : Prop :=
  ∀ n, 3 ≤ n → ∀ Z', L.IsHTBlowup Z' (L.Xn n) → ∀ l : PsiT D → ℕ → ℤ, L.descK Z' l

def pGG (_G : ExtA D L) : Prop :=
  ∃ B : ∀ n, 3 ≤ n → L.BT n, (∀ n h, L.extA (B n h)) ∧
    ∀ n (h : 3 ≤ n), L.compat (B n h) (B (n + 1) (Nat.le_succ_of_le h))

def pDR (_G : ExtA D L) : Prop :=
  (∀ CC : L.Crv, ((p : ℤ) - 2) * L.Pm CC ≤ L.eDeg CC ∧
      ∀ τ, L.degLie CC τ false = L.degLie CC τ true) ∧
    ∀ μ : PsiT D → ℕ → ℝ, Dom r μ →
      (∀ τ τ', 2 * (D.R.f : ℝ) * (μ τ' 1 - μ τ' r) ≤ ((p : ℝ) - 2) * (μ τ j - μ τ (j + 1))) →
      ∀ CC, 0 ≤ L.degLdR CC μ

end ExtA

end Ext

structure Prov (D : Formalism.BasicNotions.D7) where

  Dat : Type
  rk : Dat → ℕ
  jj : Dat → ℕ
  jj_range : ∀ w, 1 ≤ jj w ∧ jj w + 1 ≤ rk w

  loc : ∀ (w : Dat) (p : ℕ), Loc D (rk w) (jj w) p

  ex : ∀ (w : Dat) (p : ℕ), ExtA D (loc w p)

  NgC : ℕ → Type
  NgC_ne : ∀ g, Nonempty (NgC g)

  KF : ℕ → ℕ → Type

  kfNorm : ∀ {g c : ℕ}, KF g c → NgC g → ℝ

  pbKF : ∀ (w : Dat) (p : ℕ) {c : ℕ}, KF (D.R.f * rk w) c → (loc w p).Sec ((loc w p).keySh c)

  levIn : Dat → ℕ → Prop

  Xg : Dat → Type

  bc : ∀ {w} (p : ℕ), Xg w → (loc w p).Mdl

  DivX : ∀ {w}, Xg w → Type

  effD : ∀ {w} {Z : Xg w}, DivX Z → Prop
  noVertD : ∀ {w} {Z : Xg w}, DivX Z → Prop
  posBdD : ∀ {w} {Z : Xg w}, DivX Z → Prop

  ampleOnAbelianBase : ∀ {w} (Z : Xg w), ℕ → DivX Z → Prop

  Met : Dat → Type
  nefFib : ∀ {w}, Met w → Prop
  ampleGen : ∀ {w}, Met w → Prop
  limRA : ∀ {w}, Met w → Prop

variable {D : Formalism.BasicNotions.D7}

theorem Prov.dP_le (X : Prov D) (w : X.Dat) (p : ℕ) {Z : (X.loc w p).Mdl} (y : (X.loc w p).Pt Z) :
    (X.loc w p).dP y ≤ 2 * D.R.f * min (X.jj w) (X.rk w - X.jj w) :=
  (X.loc w p).dP_le (X.jj_range w).1 (X.jj_range w).2 y

theorem Prov.dP_le_of (X : Prov D) {w : X.Dat} {m : ℕ} (hm : min (X.jj w) (X.rk w - X.jj w) ≤ m) (p : ℕ)
    {Z : (X.loc w p).Mdl} (y : (X.loc w p).Pt Z) : (X.loc w p).dP y ≤ 2 * D.R.f * m :=
  (X.dP_le w p y).trans (Nat.mul_le_mul_left _ hm)

def adm1 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).aHT

def adm2 (_D : Formalism.BasicNotions.D7) (_X : Prov _D) : Prop := Formalism.HadamardInequality.Transference

def adm3 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).aKrull

def ArchimedeanSignatureMatching (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).aNorm

def adm5 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).aTube

def adm6 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).aOrd1

def adm7 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).aOrd2

def adm8 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).aOrd3

def adm9 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).aSub

def adm10 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).aClose

def adm11 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).ChartLiftsThroughSteps

def adm12 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).aCl

def adm13 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).aHTI

def admitted (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop :=
  adm1 D X ∧ adm2 D X ∧ adm3 D X ∧ ArchimedeanSignatureMatching D X ∧ adm5 D X ∧ adm6 D X ∧ adm7 D X ∧ adm8 D X ∧ adm9 D X ∧
    adm10 D X ∧ adm11 D X ∧ adm12 D X ∧ adm13 D X

def Conclusion1 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).p0

def Conclusion2 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).pC

def PointsLemma (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).pNV

def Conclusion4 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).pTR

def Conclusion5 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).pORD

def Conclusion6 (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop := ∀ w p, p.Prime → (X.ex w p).pFJ

def division_rows_rational_lattice (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop :=
  ∀ w p, p.Prime →
    (∀ La, ∃ P : (X.loc w p).LBG La, (X.loc w p).resQ P = (X.loc w p).PPq La ∧
      (X.loc w p).symmG P ∧ (X.loc w p).rigG P ∧
      ∀ y, ∃ M : (X.loc w p).LBB y La, (X.loc w p).principal M ∧
        (X.loc w p).resGt P y = (X.loc w p).prPull M) ∧
    (∀ Z (y : (X.loc w p).Pt Z) (a : (X.loc w p).Ylat y),
      (X.loc w p).psiV y a = (X.loc w p).be y a a / 2) ∧
    (X.loc w p).IsInv (X.loc w p).piPP

def Conclusion8 (D : Formalism.BasicNotions.D7) (X : Prov D) (ka : ℝ) : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∃ c : ℕ, 1 ≤ c ∧ 4 ∣ c ∧ ∃ kf : X.KF g c, ∀ z, X.kfNorm kf z = Real.exp (c * g * ka)

def KeyFormulaLineBundle (D : Formalism.BasicNotions.D7) (X : Prov D) (ka : ℝ) : Prop :=
  ∀ w p, p.Prime → ∀ (c : ℕ) (kf : X.KF (D.R.f * X.rk w) c),
    (∀ z, X.kfNorm kf z = Real.exp (c * (D.R.f * X.rk w : ℕ) * ka)) →
    (X.loc w p).IsInv ((X.loc w p).keySh c) ∧
    ∀ y, (X.loc w p).nrm ((X.loc w p).keySh c) (X.pbKF w p kf) y = 1

def LinkConditions (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop :=
  ∀ w p, p.Prime → ∀ n DF nW : ℕ, NHyp D p n → 3 * DF + 2 ≤ n →
    ∀ y : (X.loc w p).Pt (X.loc w p).Xm,
      (∃ sg, (X.loc w p).SymLift y ((X.loc w p).latStd nW) n sg) ∧
      ∀ sg, (X.loc w p).SymLift y ((X.loc w p).latStd nW) n sg →
      ∃ t : ((X.loc w p).fld y).C,
        (p : ℝ) ^ (-((X.loc w p).cJ y n DF * (X.loc w p).phiCy y)) ≤ ‖t‖ ∧
        ∀ v ∈ (X.loc w p).intJet y ((X.loc w p).latStd nW) n DF,
          t • v ∈ Ospan (C := ((X.loc w p).fld y).C)
            ((X.loc w p).secJet y ((X.loc w p).latStd nW) n DF sg)

def jet_form_downstream' (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop :=
  ∀ w p, p.Prime → ∀ n DF nW : ℕ, NHyp D p n → 3 * DF + 2 ≤ n →
    ∀ y : (X.loc w p).Pt (X.loc w p).Xm,
      ∀ sg, (X.loc w p).SymLift y ((X.loc w p).latStd nW) n sg →
      ∀ t : ((X.loc w p).fld y).C,
        ‖t‖ ≤ (p : ℝ) ^ (-((X.loc w p).cJ y n DF * (X.loc w p).phiCy y)) →
        ∀ v ∈ (X.loc w p).intJet y ((X.loc w p).latStd nW) n DF,
          t • v ∈ Ospan (C := ((X.loc w p).fld y).C)
            ((X.loc w p).secJet y ((X.loc w p).latStd nW) n DF sg)

def RunConditions (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop :=
  ∀ w p, p.Prime → ∀ (y : (X.loc w p).Pt (X.loc w p).Xm),
    (∀ σ : PsiT D × Bool,
      Function.Surjective ((X.loc w p).resB y σ) ∧ Function.Injective ((X.loc w p).incT y σ) ∧
      ((X.loc w p).incT y σ).range = ((X.loc w p).resB y σ).ker ∧
      (∀ u u', (X.loc w p).kapGt y σ u u' =
        (X.loc w p).kapB y σ ((X.loc w p).resB y σ u) ((X.loc w p).resB y σ u'))) ∧
    ∀ P s, (X.loc w p).evA y P s = (X.loc w p).evGt y P s

def HodgeTateGroupConditions (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop :=
  ∀ w p, p.Prime → (X.ex w p).pHTa ∧ (X.ex w p).pHTb ∧ (X.ex w p).pHTc ∧ (X.ex w p).pHTd ∧
    (X.ex w p).pGG

def DeRhamUnramified (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop :=
  ∀ w (p : ℕ), p.Prime → p ≠ 2 → DV.UnramE D p → (X.ex w p).pDR

def Prov.LevelForIntegralModel (X : Prov D) (w : X.Dat) : Prop :=
  X.levIn w 12 ∨ X.levIn w (D.host.g 0 * D.host.g 1)

def GlobalIntegralModel (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop :=
  ∀ w, X.LevelForIntegralModel w → ∃ (Z : X.Xg w) (m₀ : ℕ) (BD : X.DivX Z),
    (∀ p : ℕ, p.Prime → ∃ d : (X.ex w p).IvD none,
      X.bc p Z = (X.ex w p).blowUp (X.loc w p).Xm ((X.ex w p).jIdl none d)) ∧
    X.effD BD ∧ X.noVertD BD ∧ X.posBdD BD ∧ X.ampleOnAbelianBase Z m₀ BD

def IntegralModelAndNefLimit (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop :=
  GlobalIntegralModel D X ∧ ∀ w (M : X.Met w), X.nefFib M → X.ampleGen M → X.limRA M

def familyJetConsequence (D : Formalism.BasicNotions.D7) (X : Prov D) : Prop :=
  Conclusion1 D X ∧ Conclusion2 D X ∧ PointsLemma D X ∧ Conclusion4 D X ∧ Conclusion5 D X ∧ Conclusion6 D X ∧ division_rows_rational_lattice D X ∧ LinkConditions D X ∧
    RunConditions D X ∧ HodgeTateGroupConditions D X ∧ DeRhamUnramified D X ∧ IntegralModelAndNefLimit D X

def Stmt (D : Formalism.BasicNotions.D7) (X : Prov D) (ka : ℝ) : Prop :=
  admitted D X → familyJetConsequence D X ∧ Conclusion8 D X ka ∧ KeyFormulaLineBundle D X ka

abbrev ObjClass : Type 1 := ∀ {D : Formalism.BasicNotions.D7}, Prov D → Prop

def UniformExportStatement (𝒪 : ObjClass) (ka : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (X : Prov D), 𝒪 X → Stmt D X ka

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : ∀ x (i : Fm.Ix x), Prov (Fm.D x i)) : Prop :=
  ∀ x (i : Fm.Ix x), admitted (Fm.D x i) (XF x i)

def ChernFormFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : ∀ x (i : Fm.Ix x), Prov (Fm.D x i)) : Prop :=
  ∀ x (i : Fm.Ix x), familyJetConsequence (Fm.D x i) (XF x i)

def KeyFormulaFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : ∀ x (i : Fm.Ix x), Prov (Fm.D x i)) (ka : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), Conclusion8 (Fm.D x i) (XF x i) ka ∧ KeyFormulaLineBundle (Fm.D x i) (XF x i) ka

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : ∀ x (i : Fm.Ix x), Prov (Fm.D x i)) (ka : ℝ) : Prop :=
  AdmF Fm XF → ChernFormFamily Fm XF ∧ KeyFormulaFamily Fm XF ka

theorem rules_family_of_uniform {𝒪 : ObjClass} {ka : ℝ} (h : UniformExportStatement 𝒪 ka) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (XF : ∀ x (i : Fm.Ix x), Prov (Fm.D x i)) (hO : ∀ x i, 𝒪 (XF x i)) : KudlaFamilyStatement Fm XF ka :=
  fun a => ⟨fun x i => (h _ _ (hO x i) (a x i)).1, fun x i => (h _ _ (hO x i) (a x i)).2⟩

def FamilyPacketImplication {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Prov (Fm.D x i)) (ka : ℝ) : Prop :=
  (∀ x hx i, admitted (Fm.D x i) (XF x hx i)) →
    ∀ x hx i, familyJetConsequence (Fm.D x i) (XF x hx i) ∧ Conclusion8 (Fm.D x i) (XF x hx i) ka ∧ KeyFormulaLineBundle (Fm.D x i) (XF x hx i) ka

theorem familyPacket_of_uniformPacket {𝒪 : ObjClass} {ka : ℝ} (h : UniformExportStatement 𝒪 ka) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (XF : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Prov (Fm.D x i)) (hO : ∀ x hx i, 𝒪 (XF x hx i)) : FamilyPacketImplication Fm XF ka :=
  fun a x hx i => h _ _ (hO x hx i) (a x hx i)

def DerivativeStatementDesign (Fm : Formalism.MainNotions.DFamP)
    (XF : ∀ ε h0 h1 x (i : (Fm ε h0 h1).Ix x), Prov ((Fm ε h0 h1).D x i)) : Prop :=
  ∃ ka : ℝ, ∀ ε h0 h1, KudlaFamilyStatement (Fm ε h0 h1) (XF ε h0 h1) ka

def AdmissibleEpsilonFamily (Fm : Formalism.MainNotions.DFamP)
    (XF : ∀ ε h0 h1 x, (Fm ε h0 h1).x1 < x → ∀ i : (Fm ε h0 h1).Ix x, Prov ((Fm ε h0 h1).D x i)) : Prop :=
  ∃ ka : ℝ, ∀ ε h0 h1, FamilyPacketImplication (Fm ε h0 h1) (XF ε h0 h1) ka

end Formalism.MainNotions.ModuliIntegralCharts

end
