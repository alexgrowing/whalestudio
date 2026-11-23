import Mathlib
import Formalism.LocalToGlobal.Columns.ColForms
import Formalism.LocalToGlobal.Columns.ColFormsLemmas
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LocalToGlobal.Columns.RowForms
import Formalism.LocalToGlobal.Columns.RowFormsSym
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces

open NumberField IsDedekindDomain Module MvPolynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

namespace Br

section Idx

variable {N n : ℕ} (hN : N = n + 1)

def iC (i : Fin n) : Fin N := ⟨i.1, by have := i.2; omega⟩

def iS (i : Fin n) : Fin N := ⟨i.1 + 1, by have := i.2; omega⟩

def iL : Fin N := ⟨n, by omega⟩

theorem iC_inj : Function.Injective (iC hN) := by
  intro i j h
  exact Fin.ext (by simpa [iC] using h)

end Idx

section Numbers

variable {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)

def aBr (i : Fin n) : ℤ := sg.w i - lam.w (iS hN i)

def bBr (i : Fin n) : ℤ := lam.w (iC hN i) - sg.w i

def Interlace : Prop := ∀ i, 0 ≤ aBr hN lam sg i ∧ 0 ≤ bBr hN lam sg i

def SameShift : Prop := sg.detShift = lam.detShift

def d0 : ℤ := ∑ i, aBr hN lam sg i

def rSet (i : Fin n) : Finset ℤ :=
  Finset.Icc (lam.w (iS hN i)) (min (lam.w (iC hN i)) (lam.w (iS hN i) + d0 hN lam sg))

def cBr : ℤ :=
  ∏ i : Fin n, ∏ v ∈ (rSet hN lam sg i).erase (sg.w i), ∏ j : Fin n,
    ((v - ((i : ℤ) + 1)) - (sg.w j - ((j : ℤ) + 1)))

def nBr (lam : DomWeight N) (sg : DomWeight n) : ℤ := (∑ i, lam.w i) - ∑ i, sg.w i

end Numbers

section Proj

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

def gramB (sg : ι → DomWeight n) : Matrix (VVIdx sg) (VVIdx sg) K :=
  Matrix.of fun i j => fockB (bVVfun K sg i) (bVVfun K sg j)

open Classical in

def projVV (sg : ι → DomWeight n) : Pol K ι n →ₗ[K] VV K sg :=
  ∑ i : VVIdx sg, ∑ j : VVIdx sg,
    ((gramB (K := K) sg)⁻¹ i j) • (fockBL (bVVfun K sg j)).smulRight (bVV K sg i)

end Proj

section Coef

variable {K : Type} [Field K] {ι : Type} {N n : ℕ} (hN : N = n + 1)

def upVar (v : ι × Fin n × Fin n) : ι × Fin N × Fin N := (v.1, iC hN v.2.1, iC hN v.2.2)

theorem upVar_inj : Function.Injective (upVar (ι := ι) hN) := by
  intro v w h
  simp only [upVar, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Prod.ext (iC_inj hN h.2.1) (iC_inj hN h.2.2))

def IsTop (b : ι → Fin n → ℕ) (m : ι × Fin N × Fin N →₀ ℕ) : Prop :=
  (∀ τ s, m (τ, iL hN, iC hN s) = b τ s) ∧ ∀ τ a, m (τ, a, iL hN) = 0

open Classical in

def coefLast (b : ι → Fin n → ℕ) : Pol K ι N →ₗ[K] Pol K ι n :=
  (basisMonomials (ι × Fin N × Fin N) K).constr K fun m =>
    if IsTop hN b m then monomial (m.comapDomain (upVar hN) (upVar_inj hN).injOn) (1 : K) else 0

open Classical in
theorem coefLast_monomial (b : ι → Fin n → ℕ) (m : ι × Fin N × Fin N →₀ ℕ) :
    coefLast (K := K) hN b (monomial m 1) =
      if IsTop hN b m then monomial (m.comapDomain (upVar hN) (upVar_inj hN).injOn) (1 : K) else 0 := by
  have h : (basisMonomials (ι × Fin N × Fin N) K) m = monomial m 1 := by
    rw [coe_basisMonomials]
  rw [coefLast, ← h, Module.Basis.constr_basis]

end Coef

section Xi

variable (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)

def zMinor (i : Fin n) : MvPolynomial (Fin N × Fin N) K :=
  Formalism.GradedWeylDivisibility.initMinor K (s := i.val + 1)
    (fun p : Fin (i.val + 1) => if h : p.val < i.val then (⟨p.val, by have := i.2; omega⟩ : Fin N) else iL hN)
    (by have := i.2; omega)

def xiBr : MvPolynomial (Fin N × Fin N) K :=
  ∏ i : Fin n, Formalism.GradedWeylDivisibility.lpMinor K (i.val + 1) (by have := i.2; omega) (by have := i.2; omega) ^ (aBr hN lam sg i).toNat *
    zMinor K hN i ^ (bBr hN lam sg i).toNat

def kapBr : K := fockB (xiBr K hN lam sg) (xiBr K hN lam sg) / fockB (extremal K N lam) (extremal K N lam)

end Xi

section Map

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
  (lam : ι → DomWeight N) (sg : ι → DomWeight n)

def brConst (K : Type) [Field K] (lam : ι → DomWeight N) (sg : ι → DomWeight n) : K :=
  ∏ τ, ((cBr hN (lam τ) (sg τ) : ℤ) : K) * kapBr K hN (lam τ) (sg τ)

def bExp (τ : ι) (s : Fin n) : ℕ := (bBr hN (lam τ) (sg τ) s).toNat

def brStdP : Pol K ι N →ₗ[K] VV K sg := brConst hN K lam sg • (projVV sg ∘ₗ coefLast hN (bExp hN lam sg))

def brStd : VV K lam →ₗ[K] VV K sg := brStdP hN lam sg ∘ₗ (VV K lam).subtype

def brAt (t : ι → K) : VV K lam →ₗ[K] VV K sg := (∏ τ, t τ ^ (-nBr (lam τ) (sg τ))) • brStd hN lam sg

end Map

end Br

section Cast

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} (hN : N = n + 1)
  {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.tilH (pi : 𝓞 E) : DecoSet E n ∅ SG → DecoSet E N ST SG := by
  subst hN
  exact DecoSet.til pi

def extUH : UF E n →* UF E N := by
  subst hN
  exact extU

def extGH : GLG E n SG →* GLG E N SG := by
  subst hN
  exact extG

theorem DecoSet.tilH_smul (a : UF E n × GLG E n SG) (d : DecoSet E n ∅ SG) {pi : 𝓞 E}
    (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal) :
    DecoSet.tilH (ST := ST) hN pi (a • d) = (extUH hN a.1, extGH hN a.2) • DecoSet.tilH (ST := ST) hN pi d := by
  subst hN
  exact DecoSet.til_smul a d hT hG

def Deco.res (h : SG ⊆ SG') (d : Deco E n ST SG') : Deco E n ST SG where
  N := d.N
  f := d.f
  be w := d.be ⟨w.1, h w.2⟩

theorem Deco.Ok.res {d : Deco E n ST SG'} (hd : d.Ok) (h : SG ⊆ SG') : (d.res h).Ok where
  lat := hd.lat
  uni := hd.uni
  f_add := hd.f_add
  f_smul := hd.f_smul
  f_off := hd.f_off
  f_ne := hd.f_ne
  be_add w := hd.be_add ⟨w.1, h w.2⟩
  be_smul w := hd.be_smul ⟨w.1, h w.2⟩
  be_off w := hd.be_off ⟨w.1, h w.2⟩
  be_surj w := hd.be_surj ⟨w.1, h w.2⟩
  be_ker w := hd.be_ker ⟨w.1, h w.2⟩

def DecoSet.res (h : SG ⊆ SG') (d : DecoSet E n ST SG') : DecoSet E n ST SG := ⟨d.1.res h, d.2.res h⟩

end Cast

theorem N_m_succ (R : Ranks) : R.N R.m = (R.N R.m - 1) + 1 := by
  have := R.N_pos R.m
  omega

section Period

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def brC (u : Pr.Word) : VV X.K (W.lamTrue u R.m) →ₗ[X.K] VV X.K W.sgTrue :=
  Br.brAt (N_m_succ R) (W.lamTrue u R.m) W.sgTrue fun τ => X.emb τ (star ((Pr.piT u : 𝓞 X.E) : X.E))

variable (Pr R) in

abbrev RowPt : Type := DecoSet X.E (R.N R.m - 1) ∅ (rowSG Pr sel mu)

def tilQ (u : Pr.Word) : RowPt Pr R sel mu → DecoSet X.E (R.N R.m) (Pr.vT u) (rowSG Pr sel mu) :=
  DecoSet.tilH (N_m_succ R) (Pr.piT u)

open Classical in

def tilC (u : Pr.Word) : RowPt Pr R sel mu → DecoSet X.E (R.N R.m) (Pr.vT u) Pr.vGs :=
  fun d => (tilQ sel mu u d).res Finset.subset_union_left

def evzC (u : Pr.Word) : ColV W Ch u R.m →ₗ[X.K] (RowPt Pr R sel mu → VV X.K (W.lamTrue u R.m)) :=
  (LinearMap.funLeft X.K (VV X.K (W.lamTrue u R.m)) (tilC sel mu u)) ∘ₗ (ColV W Ch u R.m).subtype

def PtilFF (P : LevFam X.E X.K R.r Pr.vGs) (h : (mtildeGSD W Ch sel mu P).Ok) (u : Pr.Word) :
    (RowPt Pr R sel mu → VV X.K (W.lamTrue u R.m)) →ₗ[X.K] (RowPt Pr R sel mu → VV X.K W.sgTrue) →ₗ[X.K] X.K :=
  (mtildeGSD W Ch sel mu P).csOf h (mtildeGSD W Ch sel mu P).outSec fun d' =>
    (pairBK (K := X.K) W.sgTrue).compl₁₂ (brC W u ∘ₗ LinearMap.proj d') (LinearMap.proj d')

def PtilC (P : LevFam X.E X.K R.r Pr.vGs) (h : (mtildeGSD W Ch sel mu P).Ok) (u : Pr.Word) :
    ColV W Ch u R.m →ₗ[X.K] MtildeV W Ch sel mu P →ₗ[X.K] X.K :=
  (PtilFF W Ch sel mu P h u).compl₁₂ (evzC W Ch sel mu u) (Submodule.subtype _)

def evRho (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) :
    FormG (rowTy Ch sel mu P).inv →* Module.End X.K (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).V where
  toFun a := ((((rowTy Ch sel mu P).inv.chr a.2)⁻¹ : X.Kˣ) : X.K) •
    (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho (extUH (N_m_succ R) a.1)
  map_one' := by simp
  map_mul' a b := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_inv, Units.val_mul]
    rw [smul_mul_smul_comm]

open Classical in

@[reducible] def evGSD (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) : GSD X.K where
  G := FormG (rowTy Ch sel mu P).inv
  D := RowPt Pr R sel mu
  actD := formAct (rowTy Ch sel mu P).inv
  V := (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).V
  ιV := VVIdx (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).lam
  bV := (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).bV
  pair := (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).pair
  ρ := evRho W Ch sel mu P u
  Nab d := (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).Nab (tilQ sel mu u d)
  Del d := (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).Del (tilQ sel mu u d)

def PtilE (P : LevFam X.E X.K R.r Pr.vGs) (h : (mtildeGSD W Ch sel mu P).Ok) (u : Pr.Word) :
    (evGSD W Ch sel mu P u).EqFun →ₗ[X.K] MtildeV W Ch sel mu P →ₗ[X.K] X.K :=
  (PtilFF W Ch sel mu P h u).compl₁₂ (Submodule.subtype _) (Submodule.subtype _)

end Period

section Chains

variable {K : Type} [Field K] [NumberField K] [StarRing K]

abbrev KerFam (F : ℕ → GFam K) : Type := ∀ j, GFam.Mat (F j) (F (j + 1))

namespace KerFam

variable {F : ℕ → GFam K} (kk : KerFam F) (hF : ∀ j, (F j).Ok)

def step (j : ℕ) : (F j).Forms →ₗ[K] (F (j + 1)).Forms :=
  (kk j).opOf (hF j) fun b => ((F j).mem b).outSec

def colTo : ∀ j : ℕ, (F 0).Forms →ₗ[K] (F j).Forms
  | 0 => LinearMap.id
  | j + 1 => kk.step hF j ∘ₗ colTo j

end KerFam

structure Cpl (S : GSD K) where

  Yb : Type
  [actY : MulAction S.G Yb]

  ys : S.D → Set Yb
  fin : ∀ d, (ys d).Finite
  equiv : ∀ (g : S.G) (d : S.D) (y : Yb), g • y ∈ ys (g • d) ↔ y ∈ ys d

attribute [instance] Cpl.actY

def Cpl.Pts {S : GSD K} (Y : Cpl S) : Type := {p : S.D × Y.Yb // p.2 ∈ Y.ys p.1}

instance {S : GSD K} (Y : Cpl S) : MulAction S.G Y.Pts where
  smul g p := ⟨(g • p.1.1, g • p.1.2), (Y.equiv g p.1.1 p.1.2).2 p.2⟩
  one_smul _ := Subtype.ext (Prod.ext (one_smul _ _) (one_smul _ _))
  mul_smul _ _ _ := Subtype.ext (Prod.ext (mul_smul _ _ _) (mul_smul _ _ _))

structure CplKer (S₀ S S₁ : GSD K) (Y : Cpl S) where
  k1 : S₀.D → S.D → Y.Yb → (S₀.V →ₗ[K] S.V)
  k2 : S.D → Y.Yb → S₁.D → (S.V →ₗ[K] S₁.V)
  equiv1 : ∀ (g₀ : S₀.G) (g : S.G) (d₀ : S₀.D) (d : S.D) (y : Y.Yb),
    k1 (g₀ • d₀) (g • d) (g • y) = (S.ρ g) ∘ₗ (k1 d₀ d y) ∘ₗ (S₀.ρ g₀⁻¹)
  equiv2 : ∀ (g : S.G) (g₁ : S₁.G) (d : S.D) (y : Y.Yb) (d₁ : S₁.D),
    k2 (g • d) (g • y) (g₁ • d₁) = (S₁.ρ g₁) ∘ₗ (k2 d y d₁) ∘ₗ (S.ρ g⁻¹)

def CplKer.comp {S₀ S S₁ : GSD K} {Y : Cpl S} (A : CplKer S₀ S S₁ Y) (h : S.Ok) (s : S.Sec) : ClsKer S₀ S₁ where
  k d₀ d₁ :=
    letI := h.fintypeCl
    ∑ c : S.Cl, (((S.toCSDOf h s).wt c : K))⁻¹ •
      ∑ y ∈ (Y.fin (s.rep c)).toFinset, (A.k2 (s.rep c) y d₁) ∘ₗ (A.k1 d₀ (s.rep c) y)
  equiv g₀ g₁ d₀ d₁ := by
    let _ := h.fintypeCl
    have e1 : ∀ (d : S.D) (y : Y.Yb), A.k1 (g₀ • d₀) d y = (A.k1 d₀ d y) ∘ₗ (S₀.ρ g₀⁻¹) := by
      intro d y
      have := A.equiv1 g₀ 1 d₀ d y
      rw [one_smul, one_smul, map_one] at this
      rw [this]
      rfl
    have e2 : ∀ (d : S.D) (y : Y.Yb), A.k2 d y (g₁ • d₁) = (S₁.ρ g₁) ∘ₗ (A.k2 d y d₁) := by
      intro d y
      have := A.equiv2 1 g₁ d y d₁
      rw [one_smul, one_smul, inv_one, map_one] at this
      rw [this]
      rfl
    ext x
    simp only [e1, e2, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, map_smul]

def colCpl {F : ℕ → GFam K} (kk : KerFam F) (hF : ∀ j, (F j).Ok) (n : ℕ) {S S₁ : GSD K} {Y : Cpl S}
    (A : ∀ b : (F n).β, CplKer ((F n).mem b) S S₁ Y) (h : S.Ok) : (F 0).Forms →ₗ[K] S₁.EqFun :=
  (∑ b : (F n).β, (((A b).comp h S.outSec).opOf (hF n b) ((F n).mem b).outSec) ∘ₗ (LinearMap.proj b)) ∘ₗ kk.colTo hF n

end Chains

section Frames

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def stabL (M : Submodule (𝓞 E) (Sp E n)) : Subgroup (Sp E n ≃ₗ[E] Sp E n) where
  carrier := {c | ∀ x, c x ∈ M ↔ x ∈ M}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x => (ha (b x)).trans (hb x)
  inv_mem' := fun {a} ha x => by
    have h := ha (a⁻¹ x)
    rw [show a (a⁻¹ x) = x from LinearEquiv.apply_symm_apply a x] at h
    exact h.symm

def stdAt (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) (Sp E n) := localization₂ P.asIdeal (stdLat E n)

def GLint (P : HeightOneSpectrum (𝓞 E)) : Subgroup (Sp E n ≃ₗ[E] Sp E n) := stabL E n (stdAt E n P)

variable (ST SG Q : Finset (HeightOneSpectrum (𝓞 E)))

def DecoF : Type :=
  {p : DecoSet E n ST SG × (∀ P : Q, Sp E n ≃ₗ[E] Sp E n) //
    ∀ (P : Q) (x : Sp E n), p.2 P x ∈ p.1.1.at P.1 ↔ x ∈ stdAt E n P.1}

abbrev GLQ : Type := ∀ P : Q, ↥(GLint E n P.1)

variable {E n ST SG Q}

def DecoF.deco (p : DecoF E n ST SG Q) : DecoSet E n ST SG := p.1.1

def DecoF.fr (p : DecoF E n ST SG Q) (P : Q) : Sp E n ≃ₗ[E] Sp E n := p.1.2 P

variable (E n ST SG Q) in

def DecoF.base [NeZero n] : DecoF E n ST SG Q := ⟨(DecoSet.base E n ST SG, fun _ => 1), fun _ _ => Iff.rfl⟩

instance [NeZero n] : Nonempty (DecoF E n ST SG Q) := ⟨DecoF.base E n ST SG Q⟩

instance : MulAction (UF E n × GLG E n SG × GLQ E n Q) (DecoF E n ST SG Q) where
  smul a p := ⟨((a.1, a.2.1) • p.1.1, fun P => a.1.1 * p.1.2 P * ((a.2.2 P)⁻¹).1), fun P x => by
    have h1 : (((a.1, a.2.1) • p.1.1 : DecoSet E n ST SG)).1.at P.1 =
        localization₂ P.1.asIdeal (gmap a.1.1 p.1.1.1.N) := rfl
    rw [h1, mem_localization_gmap]
    show a.1.1.symm (a.1.1 (p.1.2 P (((a.2.2 P)⁻¹).1 x))) ∈ _ ↔ _
    rw [LinearEquiv.symm_apply_apply, p.2 P]
    exact ((a.2.2 P)⁻¹).2 x⟩
  one_smul p := by
    apply Subtype.ext
    apply Prod.ext
    · exact one_smul _ p.1.1
    · funext P
      show (1 : Sp E n ≃ₗ[E] Sp E n) * p.1.2 P * (((1 : GLQ E n Q) P)⁻¹).1 = p.1.2 P
      simp
  mul_smul a b p := by
    apply Subtype.ext
    apply Prod.ext
    · exact mul_smul (a.1, a.2.1) (b.1, b.2.1) p.1.1
    · funext P
      show (a.1.1 * b.1.1) * p.1.2 P * (((a.2.2 P * b.2.2 P))⁻¹).1 =
        a.1.1 * (b.1.1 * p.1.2 P * ((b.2.2 P)⁻¹).1) * ((a.2.2 P)⁻¹).1
      rw [mul_inv_rev]
      simp only [Subgroup.coe_mul, mul_assoc]

end Frames

structure LevI (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (n : ℕ) (P : HeightOneSpectrum (𝓞 E)) where
  H : Subgroup ↥(GLint E n P)
  lam : ↥H →* Kˣ

abbrev LevQFam (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (n : ℕ)
    (Q : Finset (HeightOneSpectrum (𝓞 E))) : Type := ∀ P : Q, LevI E K n P.1

namespace LevQFam

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))}
  (Θ : LevQFam E K n Q)

def grp : Subgroup (GLQ E n Q) := Subgroup.pi Set.univ fun P => (Θ P).H

def chr : ↥Θ.grp →* Kˣ := piChar (fun P => (Θ P).H) fun P => (Θ P).lam

variable (E K n Q) in

def top : LevQFam E K n Q := fun _ => ⟨⊤, 1⟩

end LevQFam

section FrmForms

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

abbrev FrmG (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) : Type := UF X.E n × ↥Λ.grp × ↥Θ.grp

def FrmG.incl (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) :
    FrmG Λ Θ →* UF X.E n × GLG X.E n SG × GLQ X.E n Q :=
  MonoidHom.prodMap (MonoidHom.id _) (MonoidHom.prodMap Λ.grp.subtype Θ.grp.subtype)

instance frmAct (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) :
    MulAction (FrmG Λ Θ) (DecoF X.E n ST SG Q) := MulAction.compHom _ (FrmG.incl Λ Θ)

def frmRho (C : CoefPk X n (DecoF X.E n ST SG Q)) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) :
    FrmG Λ Θ →* Module.End X.K C.V where
  toFun a := ((Λ.chr a.2.1 * Θ.chr a.2.2 : X.Kˣ) : X.K) • C.rho a.1
  map_one' := by simp
  map_mul' a b := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Units.val_mul]
    rw [smul_mul_smul_comm]
    congr 1
    ring

open Classical in

@[reducible] def frmGSD (C : CoefPk X n (DecoF X.E n ST SG Q)) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) :
    GSD X.K where
  G := FrmG Λ Θ
  D := DecoF X.E n ST SG Q
  actD := frmAct Λ Θ
  V := C.V
  ιV := VVIdx C.lam
  bV := C.bV
  pair := C.pair
  ρ := frmRho C Λ Θ
  Nab := C.Nab
  Del := C.Del

end FrmForms

namespace Loc

section Groups

variable (k : Type) [CommRing k] (n c : ℕ)

def atN {k : Type} [CommRing k] {N : ℕ} (v : Fin N → k) (i : ℕ) : k := if h : i < N then v ⟨i, h⟩ else 0

def eN (N i : ℕ) : Fin N → k := fun l => if l.1 = i then 1 else 0

def supp (N : ℕ) (s : Set ℕ) : Submodule k (Fin N → k) where
  carrier := {v | ∀ l : Fin N, l.1 ∉ s → v l = 0}
  add_mem' := fun {a b} ha hb l hl => by simp [ha l hl, hb l hl]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r a ha l hl => by simp [ha l hl]

def Ufl (i : ℕ) : Submodule k (Fin (n + c) → k) := supp k (n + c) {l | l < n + i}

def inX : (Fin n → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if h : l.1 < n then LinearMap.proj ⟨l.1, h⟩ else 0

def R1cond (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ i, ∀ v ∈ Ufl k n c i, r v ∈ Ufl k n c i) ∧ r (eN k (n + c) n) = eN k (n + c) n ∧
    ∀ i, r (eN k (n + c) (n + i)) - eN k (n + c) (n + i) ∈ Ufl k n c i

variable {k n c} in
theorem R1cond.mul {r s : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hs : R1cond k n c s) :
    R1cond k n c (r * s) := by
  refine ⟨fun i v hv => hr.1 i _ (hs.1 i v hv), ?_, fun i => ?_⟩
  · show r (s _) = _
    rw [hs.2.1, hr.2.1]
  · have h1 : (r * s) (eN k (n + c) (n + i)) - eN k (n + c) (n + i) =
        r (s (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) + (r (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) := by
      rw [map_sub]
      show r (s _) - _ = _
      abel
    rw [h1]
    exact add_mem (hr.1 i _ (hs.2.2 i)) (hr.2.2 i)

theorem R1cond_one : R1cond k n c 1 :=
  ⟨fun _ _ hv => hv, rfl, fun i => by
    show eN k (n + c) (n + i) - eN k (n + c) (n + i) ∈ _
    rw [sub_self]
    exact zero_mem _⟩

def R1 : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) where
  carrier := {r | R1cond k n c r ∧ R1cond k n c r⁻¹}
  one_mem' := ⟨R1cond_one k n c, by rw [inv_one]; exact R1cond_one k n c⟩
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, by rw [mul_inv_rev]; exact hb.2.mul ha.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

def fixX : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) where
  carrier := {r | ∀ x, r (inX k n c x) = inX k n c x}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb x => by
    show a (b _) = _
    rw [hb, ha]
  inv_mem' := fun {a} ha x => by
    have h := ha x
    show a.symm _ = _
    rw [LinearEquiv.symm_apply_eq, h]

def N1 : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) := R1 k n c ⊓ fixX k n c

variable {k n c}

def n1Arg (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : k :=
  ∑ i ∈ Finset.range (c - 1), atN (r (eN k (n + c) (n + i + 1))) (n + i)

def Cbe (J : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) (h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :=
  R1 k n c ⊓ J.comap (MulAut.conj h⁻¹).toMonoidHom

def prX (C : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) : Subgroup ((Fin n → k) ≃ₗ[k] (Fin n → k)) where
  carrier := {g | ∃ r ∈ C, ∀ x, r (inX k n c x) = inX k n c (g x)}
  one_mem' := ⟨1, C.one_mem, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨r, hr, h1⟩ ⟨s, hs, h2⟩
    refine ⟨r * s, C.mul_mem hr hs, fun x => ?_⟩
    show r (s _) = _
    rw [h2, h1]
    rfl
  inv_mem' := by
    rintro a ⟨r, hr, h1⟩
    refine ⟨r⁻¹, C.inv_mem hr, fun x => ?_⟩
    show r.symm _ = _
    rw [LinearEquiv.symm_apply_eq, h1]
    show _ = inX k n c (a (a.symm x))
    rw [LinearEquiv.apply_symm_apply]

def volN (K : Type) [Field K] (C N1O : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) : K :=
  ((N1O.relIndex (C ⊓ N1 k n c) : ℕ) : K) / (((C ⊓ N1 k n c).relIndex N1O : ℕ) : K)

end Groups

section Data

variable {k K : Type} [CommRing k] [Field K]

abbrev SF (k K : Type) [CommRing k] (a b : ℕ) : Type := ((Fin a → k) →ₗ[k] (Fin b → k)) → K

def om {a b : ℕ} (mu : k → K) (v : k → ℤ) (sq : K) (g₀ : (Fin a → k) ≃ₗ[k] (Fin a → k))
    (h : (Fin b → k) ≃ₗ[k] (Fin b → k)) (Φ : SF k K a b) : SF k K a b := fun x =>
  mu (LinearEquiv.det g₀ : kˣ) * (mu (LinearEquiv.det h : kˣ))⁻¹ * sq ^ (-(v (LinearEquiv.det g₀ : kˣ)) * b) *
    sq ^ (v (LinearEquiv.det h : kˣ) * a) * Φ (h.symm.toLinearMap ∘ₗ x ∘ₗ g₀.toLinearMap)

variable (n' c' n c : ℕ)

def IsFree (l s : ℕ) : Prop := n' ≤ s ∧ (s - n' = c ∨ (1 ≤ s - n' ∧ (l < n ∨ l - n < s - n')))

instance (l s : ℕ) : Decidable (IsFree n' n c l s) := by unfold IsFree; infer_instance

abbrev FC : Type := {p : Fin (n + c) × Fin (n' + c') // IsFree n' n c p.1.1 p.2.1}

variable {n' c' n c}

def xx1 (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : FC n' c' n c → k) : (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k) :=
  Matrix.toLin' (Matrix.of fun (l : Fin (n + c)) (s : Fin (n' + c')) =>
    if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
    else if hs : s.1 < n' then (if hl : l.1 < n then LinearMap.toMatrix' xj ⟨l.1, hl⟩ ⟨s.1, hs⟩ else 0)
    else if l.1 = n + (s.1 - n') then 1 else 0)

def chArg (x : (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k)) : k :=
  ∑ i ∈ Finset.range c, atN (x (eN k (n' + c') (n' + i + 1))) (n + i)

def E1 (psi : k → K) (vals : Finset k) (wt : K) (Φ : SF k K (n' + c') (n + c)) : SF k K n' n := fun xj =>
  wt ^ Fintype.card (FC n' c' n c) *
    ∑ t ∈ Fintype.piFinset fun _ : FC n' c' n c => vals, Φ (xx1 xj t) * psi (-chArg (xx1 xj t))

end Data

end Loc

section Theta

variable {E : Type} [Field E] [NumberField E] [StarRing E]

abbrev HomE (E : Type) [Field E] (a b : ℕ) : Type := Sp E a →ₗ[E] Sp E b

abbrev Frs (E : Type) [Field E] [NumberField E] (n : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E))) : Type :=
  ∀ _ : SB, Sp E n ≃ₗ[E] Sp E n

def homAt {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) :
    Submodule (𝓞 E) (HomE E a b) where
  carrier := {x | ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, x y ∈ localization₂ P.asIdeal N'}
  add_mem' := fun hx hx' P hP y hy => add_mem (hx P hP y hy) (hx' P hP y hy)
  zero_mem' := fun _ _ _ _ => zero_mem _
  smul_mem' := fun r _ hx P hP y hy => Submodule.smul_mem _ r (hx P hP y hy)

def divLat {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (c : ℕ) (M : Submodule (𝓞 E) H) : Submodule (𝓞 E) H :=
  M.comap ((c : 𝓞 E) • (LinearMap.id : H →ₗ[𝓞 E] H))

def mulLat {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (c : ℕ) (M : Submodule (𝓞 E) H) : Submodule (𝓞 E) H :=
  M.map ((c : 𝓞 E) • (LinearMap.id : H →ₗ[𝓞 E] H))

def latSum {H M : Type} [AddCommGroup H] [Module (𝓞 E) H] [AddCommMonoid M] (A B : Submodule (𝓞 E) H) (F : H → M) : M :=
  ∑ᶠ z : ↥A ⧸ B.comap A.subtype, F ((Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z : ↥A) : H)

abbrev ThDist (E K : Type) [Field E] [NumberField E] [Field K] (a b : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E)))
    (V V' : Type) [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] : Type :=
  Submodule (𝓞 E) (Sp E a) → Frs E a SB → Submodule (𝓞 E) (Sp E b) → Frs E b SB → ℕ → HomE E a b → (V →ₗ[K] V')

variable {K : Type} [Field K] {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def IsSdLat {n : ℕ} (N : Submodule (𝓞 E) (Sp E n)) : Prop := Submodule.IsLattice E N ∧ IsUnimodular (hStd E n) N

structure ThDist.Ok (th : ThDist E K a b SB V V') (Sall : Finset (HeightOneSpectrum (𝓞 E))) (D : ℕ)
    (rho : UF E a →* Module.End K V) (rho' : UF E b →* Module.End K V') (sS sT : SB → E → K) : Prop where

  cong : ∀ N fr N' fr' c x x', IsSdLat N → IsSdLat N' → x - x' ∈ mulLat c (homAt Sall N N') →
    th N fr N' fr' c x = th N fr N' fr' c x'

  add : ∀ N fr N' fr' c c' x, IsSdLat N → IsSdLat N' → 0 < c → 0 < c' → c * c' ∣ D → x ∈ divLat D (homAt Sall N N') →
    th N fr N' fr' c x = latSum (mulLat c (homAt Sall N N')) (mulLat (c * c') (homAt Sall N N')) fun y => th N fr N' fr' (c * c') (x + y)

  equiv : ∀ (γ : UF E a) (γ' : UF E b) N fr N' fr' c x, IsSdLat N → IsSdLat N' →
    th (gmap γ.1 N) (fun P => γ.1 * fr P) (gmap γ'.1 N') (fun P => γ'.1 * fr' P) c
        (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = (rho' γ') ∘ₗ (th N fr N' fr' c x) ∘ₗ (rho γ⁻¹)

  det : ∀ N fr N' fr' c x (κ : ∀ P : SB, ↥(GLint E a P.1)) (κ' : ∀ P : SB, ↥(GLint E b P.1)), IsSdLat N → IsSdLat N' →
    th N (fun P => fr P * (κ P).1) N' (fun P => fr' P * (κ' P).1) c x =
      (∏ P : SB, sS P (LinearEquiv.det (κ P).1 : Eˣ) * sT P (LinearEquiv.det (κ' P).1 : Eˣ)) • th N fr N' fr' c x

def kerOf (th : ThDist E K a b SB V V') (Sall : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (fr : Frs E a SB) (N' : Submodule (𝓞 E) (Sp E b)) (fr' : Frs E b SB)
    (Ξ : HomE E a b → K) : V →ₗ[K] V' :=
  latSum (divLat cA (homAt Sall N N')) (mulLat cB (homAt Sall N N')) fun x => Ξ x • th N fr N' fr' cB x

def inFr (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) : HomE E a b :=
  f'.symm.toLinearMap ∘ₗ x ∘ₗ f.toLinearMap

open Classical in

def phiT (K : Type) [Field K] {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (x : HomE E a b) : K :=
  if ∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y then 1 else 0

def redV {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) : Fin n → 𝓞 E ⧸ P.asIdeal := fun i => redP P (x i)

def Deco.liftFr {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E n ST SG) (w : SG) : Sp E n ≃ₗ[E] Sp E n :=
  Classical.epsilon fun f : Sp E n ≃ₗ[E] Sp E n =>
    (∀ x, f x ∈ d.at w.1 ↔ x ∈ stdAt E n w.1) ∧ ∀ x ∈ stdAt E n w.1, d.be w (f x) = redV w.1 x

end Theta

namespace LocE

open Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

def vP (a : E) : ℤ := Classical.epsilon fun z : ℤ => IsUnit (redP P (a / (q : E) ^ z))

variable {P} in
open Classical in

def unitV (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : K := if h : IsUnit (redP P a) then ((χ h.unit : Kˣ) : K) else 0

variable {P} in

def locChar (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : K := cq ^ vP P q a * unitV χ (a / (q : E) ^ vP P q a)

open Classical in

def valsQ (E : Type) [Field E] (q A B : ℕ) : Finset E :=
  (Finset.range (q ^ (A + B))).image fun i : ℕ => ((i : ℕ) : E) / (q : E) ^ A

def sclLat (N : ℕ) (e : ℕ → ℤ) : Submodule (𝓞 E) (Sp E N) :=
  (stdAt E N P).comap
    ((LinearMap.pi fun l : Fin N => ((q : E) ^ e l.1)⁻¹ • (LinearMap.proj l : Sp E N →ₗ[E] E)).restrictScalars (𝓞 E))

def fIdx (k₀ c n s : ℕ) : ℕ := if s < k₀ then s else if s < k₀ + c then n + (s - k₀) else s - c

def fPos (k₀ c n l : ℕ) : ℕ := if l < k₀ then l else if l < n then l + c else k₀ + (l - n)

def scE (n : ℕ) (ex : ℕ → ℕ) (l : ℕ) : ℤ := if l < n then 0 else (ex (l - n) : ℤ)

def lamY (n c : ℕ) (ex : ℕ → ℕ) : Submodule (𝓞 E) (Sp E (n + c)) := sclLat P q (n + c) (scE n ex)

def entB {N' N : ℕ} (k₀ c' n' c n : ℕ) (ex' ex : ℕ → ℕ) (x : HomE E N' N) (p p' : ℕ) : E :=
  atN (x (eN E N' (fIdx k₀ c' n' p'))) (fIdx k₀ c n p) * (q : E) ^ (scE n' ex' (fIdx k₀ c' n' p') - scE n ex (fIdx k₀ c n p))

section AtQ

variable (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

def parL (kj n c : ℕ) : Submodule (𝓞 E) (Sp E (n + c)) := sclLat P q (n + c) fun l => if kj ≤ l ∧ l < n then 1 else 0

def JQ (kj n c : ℕ) : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :=
  stabL E (n + c) (stdAt E (n + c) P) ⊓ stabL E (n + c) (parL P q kj n c)

variable {P}

def lamQB (kj n : ℕ) {N : ℕ} (h : HomE E N N) : K :=
  (unitV ξ (Matrix.det (Matrix.of fun s t : Fin (n - kj) => atN (h (eN E N (kj + t.1))) (kj + s.1))))⁻¹

open Classical in

def PhiQ (k₀ r c' n' c n : ℕ) : SF E K (n' + c') (n + c) := fun x =>
  if (∀ p p', p < n + c → p' < n' + c' → IntAt P (entB q k₀ c' n' c n 0 0 x p p')) ∧
      (∀ p p', r ≤ p → p < n + c → p' < r → IntAt P (entB q k₀ c' n' c n 0 0 x p p' / (q : E)))
  then unitV ξ (Matrix.det (Matrix.of fun s t : Fin r => entB q k₀ c' n' c n 0 0 x s.1 t.1)) else 0

end AtQ

section AtG

def flagU {N : ℕ} (M : ℕ → Submodule (𝓞 E) (Sp E N)) (e : ℕ → Sp E N) (r : ℕ) (st : Set ℕ) :
    Subgroup (Sp E N ≃ₗ[E] Sp E N) where
  carrier := {κ | (∀ s ∈ st, κ ∈ stabL E N (M s)) ∧ ∀ s < r, κ ∈ stabL E N (M s) ∧ κ (e s) - e s ∈ M s}
  one_mem' := ⟨fun _ _ => Subgroup.one_mem _, fun s _ => ⟨Subgroup.one_mem _, by
    show e s - e s ∈ M s
    rw [sub_self]
    exact zero_mem _⟩⟩
  mul_mem' := fun {a b} ha hb => ⟨fun s hs => Subgroup.mul_mem _ (ha.1 s hs) (hb.1 s hs), fun s hs =>
    ⟨Subgroup.mul_mem _ (ha.2 s hs).1 (hb.2 s hs).1, by
      have h1 : (a * b) (e s) - e s = a (b (e s) - e s) + (a (e s) - e s) := by
        rw [map_sub]
        show a (b _) - _ = _
        abel
      rw [h1]
      exact add_mem (((ha.2 s hs).1 _).2 (hb.2 s hs).2) (ha.2 s hs).2⟩⟩
  inv_mem' := fun {a} ha => ⟨fun s hs => Subgroup.inv_mem _ (ha.1 s hs), fun s hs =>
    ⟨Subgroup.inv_mem _ (ha.2 s hs).1, by
      have h1 : a⁻¹ (e s) - e s = -(a⁻¹ (a (e s) - e s)) := by
        rw [map_sub]
        show _ = -(a.symm (a (e s)) - _)
        rw [LinearEquiv.symm_apply_apply]
        abel
      rw [h1]
      exact neg_mem (((Subgroup.inv_mem _ (ha.2 s hs).1) _).2 (ha.2 s hs).2)⟩⟩

def flagG (k₀ n c s : ℕ) : Submodule (𝓞 E) (Sp E (n + c)) :=
  sclLat P q (n + c) fun l => scE n (fun i => i + 1) l + if s ≤ fPos k₀ c n l then 1 else 0

def bvecG (E : Type) [Field E] (q k₀ n c s : ℕ) : Sp E (n + c) :=
  ((q : E) ^ scE n (fun i => i + 1) (fIdx k₀ c n s)) • eN E (n + c) (fIdx k₀ c n s)

def JG (k₀ r t n c : ℕ) : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :=
  stabL E (n + c) (lamY P q n c fun i => i + 1) ⊓
    flagU (flagG P q k₀ n c) (bvecG E q k₀ n c) r {s | ∃ i, s = r + i * t}

def JGsharp (k₀ r t n c : ℕ) : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :=
  JG P q k₀ r t n c ⊓ flagU (fun _ => flagG P q k₀ n c 0) (fun _ => bvecG E q k₀ n c k₀) 1 ∅

def bd5 (k₀ rS s : ℕ) : ℕ := if s = rS + k₀ then rS else s

def flagS (k₀ rS n c s : ℕ) : Submodule (𝓞 E) (Sp E (n + c)) :=
  sclLat P q (n + c) fun l => scE n (fun i => i + 1) l + if bd5 k₀ rS s ≤ symIdx k₀ rS (fPos k₀ c n l) then 1 else 0

def bvecS (E : Type) [Field E] (q k₀ rS n c s : ℕ) : Sp E (n + c) := bvecG E q k₀ n c (symIdxInv k₀ rS s)

def JGsym (k₀ rS r t n c : ℕ) : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :=
  stabL E (n + c) (lamY P q n c fun i => i + 1) ⊓
    flagU (flagS P q k₀ rS n c) (bvecS E q k₀ rS n c) r {s | ∃ i, s = r + i * t}

variable {P} (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

def lamGv (r t j : ℕ) (M : ℕ → ℕ → E) : K :=
  ψ₀ (redP P (∑ i ∈ Finset.range (r - 1), M i (i + 1))) *
    ∏ i ∈ Finset.range j, unitV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1)))

def lamGB (k₀ r t j n c : ℕ) (h : HomE E (n + c) (n + c)) : K :=
  lamGv ψ₀ χ r t j (entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) h)

open Classical in

def PhiG (sharp : Bool) (k₀ r t j c' n' c n : ℕ) : SF E K (n' + c') (n + c) := fun x =>
  let M := entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x
  let a := r + (j - 1) * t
  if (∀ p p', p < n + c → p' < a → IntAt P (M p p')) ∧ (∀ p p', a ≤ p → p < n + c → p' < a → IntAt P (M p p' / (q : E))) ∧
      (∀ p', p' < r → redP P (M p' p') = 1 ∧ ∀ p, p' < p → p < a → redP P (M p p') = 0) ∧
      (∀ p p', r ≤ p' → p' < a → p < a → (p' - r) / t < (p - r) / t → redP P (M p p') = 0) ∧
      (sharp = true → ∀ p, p < n + c → redP P (M p k₀) = if p = k₀ then 1 else 0)
  then lamGv ψ₀ χ r t (j - 1) M * (unitV (χ (j - 1)) (Matrix.det (Matrix.of fun s s' : Fin a => M s.1 s'.1)))⁻¹ else 0

def lamGvS (k₀ r t j : ℕ) (M : ℕ → ℕ → E) : K :=
  ψ₀ (redP P (∑ i ∈ Finset.range (k₀ - 1), M i (i + 1) + ∑ i ∈ Finset.range (r - k₀ - 1), M (k₀ + i) (k₀ + i + 1))) *
    ∏ i ∈ Finset.range j, unitV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1)))

def lamGBS (k₀ r t j n c : ℕ) (h : HomE E (n + c) (n + c)) : K :=
  lamGvS ψ₀ χ k₀ r t j (entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) h)

open Classical in

def PhiGS (k₀ rS r t j c' n' c n : ℕ) : SF E K (n' + c') (n + c) := fun x =>
  let M := entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x
  let a := r + (j - 1) * t
  if (∀ p p', p < n + c → p' < a → IntAt P (M p p')) ∧ (∀ p p', a ≤ p → p < n + c → p' < a → IntAt P (M p p' / (q : E))) ∧
      (∀ p', p' < r → redP P (M p' p') = 1 ∧ ∀ p, p < a → p ≠ p' →
        (r ≤ p ∨ symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) → redP P (M p p') = 0) ∧
      (∀ p p', r ≤ p' → p' < a → p < a → (p' - r) / t < (p - r) / t → redP P (M p p') = 0)
  then lamGvS ψ₀ χ k₀ r t (j - 1) M * (unitV (χ (j - 1)) (Matrix.det (Matrix.of fun s s' : Fin a => M s.1 s'.1)))⁻¹ else 0

end AtG

end LocE

section ColChain

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def cOf (R : Ranks) (j : ℕ) : ℕ := R.m - 1 - j

def qOf {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : ℕ := Ideal.absNorm P.asIdeal

def epsSg : ℤ := -1

structure LocCst (X : Fields) (SB : Finset (HeightOneSpectrum (𝓞 X.E))) where

  psi : SB → X.E → X.K

  D : SB → ℕ

  sq : SB → X.K

  muq : ℕ → SB → X.K

  A : ℕ
  B : ℕ

  M : ℕ

  sharp : Bool

structure LocCst.Ok {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (c : LocCst X SB) : Prop where

  psi_add : ∀ (P : SB) (x y : X.E), IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * x) → IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * y) →
    c.psi P (x + y) = c.psi P x * c.psi P y

  psi_int : ∀ (P : SB) (x : X.E), IntAt P.1 x → c.psi P x = 1
  psi_ne : ∀ P : SB, c.psi P ((qOf P.1 : X.E)⁻¹) ≠ 1
  D_pos : ∀ P : SB, 1 ≤ c.D P
  sq_sq : ∀ P : SB, c.sq P ^ 2 = (qOf P.1 : X.K)
  M_pos : 1 ≤ c.M

  M_le_A : c.M ≤ c.A
  M_le_B : c.M ≤ c.B

  B_pos : 1 ≤ c.B

def LocCst.WeilTied {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (c : LocCst X SB) (σ₀ : X.K →+* ℂ) (xi0 : X.E) : Prop :=
  ∀ (P : SB) (a : X.E) (b : ℤ), IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * a) →
    IntAt P.1 (xi0 * a - (b : X.E) / (qOf P.1 : X.E) ^ c.D P) →
      σ₀ (c.psi P a) = Complex.exp (2 * Real.pi * Complex.I * b / (qOf P.1 : ℂ) ^ c.D P)

def XiUnitAt {X : Fields} (SB : Finset (HeightOneSpectrum (𝓞 X.E))) (xi0 : X.E) : Prop :=
  ∀ P : SB, IntAt P.1 xi0 ∧ redP P.1 xi0 ≠ 0

structure ChGlob (X : Fields) (m : ℕ) where

  σ₀ : X.K →+* ℂ

  xi0 : X.E

  mu0 : Fin m → Formalism.L2.Host.HChar X.E

def Chars.WeilTied {X : Fields} {Pr : Primes X} {m : ℕ} (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (xi0 : X.E) : Prop :=
  ∀ (w : {w // w ∈ Pr.vGs}) (c : 𝓞 X.E ⧸ w.1.asIdeal) (b : ℤ), redP w.1 xi0 * c = (b : 𝓞 X.E ⧸ w.1.asIdeal) →
    σ₀ (Ch.psi0 w c) = Complex.exp (2 * Real.pi * Complex.I * b / (qOf w.1 : ℂ))

section XiQ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

def IsQValC (ξ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) (k : Lˣ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), P.asIdeal.under (𝓞 F) = v.asIdeal →
  ∀ (y : (AfE F E)ˣ) (y₀ : RInt F E), (y₀ : AfE F E) = (y : AfE F E) → y ∈ suppAt E v →
    y₀ - toRInt F E ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ (P.asIdeal ^ 2).map (toRInt F E) →
    (∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀ - 1 ∈ P'.asIdeal.map (toRInt F E)) → ξ y = k

open Classical in

def qValC (ξ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) : Lˣ := if h : ∃ k, IsQValC ξ P k then h.choose else 1

end XiQ

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

open Classical in

def psi0P (P : HeightOneSpectrum (𝓞 X.E)) : AddChar (𝓞 X.E ⧸ P.asIdeal) X.K :=
  if h : P ∈ Pr.vGs then Ch.psi0 ⟨P, h⟩ else 1

open Classical in

def chiP (P : HeightOneSpectrum (𝓞 X.E)) : ℕ → (𝓞 X.E ⧸ P.asIdeal)ˣ →* X.Kˣ :=
  if h : P ∈ Pr.vGs then chiAt Ch ⟨P, h⟩ else fun _ => 1

abbrev AutY (X : Fields) (R : Ranks) (j : ℕ) : Type := Sp X.E (R.N j + cOf R j) ≃ₗ[X.E] Sp X.E (R.N j + cOf R j)

open Classical in

def Jat (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : Subgroup (AutY X R j) :=
  if P ∈ Pr.vGs then
    (if sharp then LocE.JGsym P (qOf P) R.k R.rS R.r R.t (R.N j) (cOf R j) else LocE.JG P (qOf P) R.k R.r R.t (R.N j) (cOf R j))
  else LocE.JQ P (qOf P) (R.k + j) (R.N j) (cOf R j)

open Classical in

def lamRow (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j)) : X.K :=
  if P ∈ Pr.vGs then
    (if sharp then LocE.lamGBS (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t j (R.N j) (cOf R j) h
      else LocE.lamGB (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t j (R.N j) (cOf R j) h)
  else LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P) (R.k + j) (R.N j) h

open Classical in

def lamYat (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : Submodule (𝓞 X.E) (Sp X.E (R.N j + cOf R j)) :=
  LocE.lamY P (qOf P) (R.N j) (cOf R j) (if P ∈ Pr.vGs then fun i => i + 1 else 0)

open Classical in

def PhiAt (sharp : Bool) (i : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : Loc.SF X.E X.K (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)) :=
  if P ∈ Pr.vGs then
    (if sharp then LocE.PhiGS (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.rS R.r R.t (i + 1) (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1))
      else LocE.PhiG (qOf P) (psi0P Ch P) (chiP Ch P) false R.k R.r R.t (i + 1) (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)))
  else LocE.PhiQ (qOf P) (resChar (mu : Chr X.F X.E X.K) P) R.k R.r (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1))

open Classical in

def muAt (i : ℕ) (P : rowSG Pr sel mu) : X.E → X.K :=
  LocE.locChar (qOf P.1) (cst.muq (i + 1) P)
    (if P.1 ∈ Pr.vGs then chiP Ch P.1 i else (resChar (mu : Chr X.F X.E X.K) P.1)⁻¹)

def omPhi (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (h : AutY X R (i + 1)) :
    Loc.SF X.E X.K (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)) :=
  Loc.om (muAt Ch sel mu cst i P) (LocE.vP P.1 (qOf P.1)) (cst.sq P) hal h (PhiAt Ch mu cst.sharp i P.1)

def E1at (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (h : AutY X R (i + 1)) : Loc.SF X.E X.K (R.N i) (R.N (i + 1)) :=
  Loc.E1 (cst.psi P) (LocE.valsQ X.E (qOf P.1) cst.A cst.B) (((qOf P.1 : X.K) ^ cst.B)⁻¹) (omPhi Ch sel mu cst i P hal h)

def XiAt (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (hbe : AutY X R (i + 1)) : Loc.SF X.E X.K (R.N i) (R.N (i + 1)) :=
  fun x => (Loc.volN X.K (Loc.Cbe (Jat (Pr := Pr) cst.sharp (i + 1) P.1) hbe)
    (Loc.N1 X.E (R.N (i + 1)) (cOf R (i + 1)) ⊓ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1)))⁻¹ * E1at Ch sel mu cst i P hal hbe x

structure ChIdx (X : Fields) (Pr : Primes X) (R : Ranks) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) where
  β : ℕ → Type
  [finβ : ∀ j, Fintype (β j)]
  [decβ : ∀ j, DecidableEq (β j)]

  h : ∀ j, β j → uSG Pr.vGs Q → AutY X R j

  levG : ∀ j, β j → LevFam X.E X.K (R.N j) Pr.vGs

  levQ : ∀ j, β j → LevQFam X.E X.K (R.N j) Q

attribute [instance] ChIdx.finβ ChIdx.decβ

end ColChain

section ColChain2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def SameDC (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h h' : AutY X R j) : Prop :=
  ∃ r ∈ Loc.R1 X.E (R.N j) (cOf R j), ∃ κ ∈ Jat (Pr := Pr) sharp j P, h' = r * h * κ

def prCat (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Subgroup (Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) :=
  Loc.prX (Loc.Cbe (Jat (Pr := Pr) sharp j P) h)

def chiInv (j : ℕ) (P : rowSG Pr sel mu) (h r : AutY X R j) : X.K :=
  (cst.psi P (Loc.n1Arg r))⁻¹ * lamRow Ch mu cst.sharp j P.1 ((h⁻¹ * r * h : AutY X R j)).toLinearMap

def atNL (E : Type) [Field E] (N i : ℕ) : Sp E N →ₗ[E] E := if h : i < N then LinearMap.proj ⟨i, h⟩ else 0

def joinCol {E : Type} [Field E] {n' c' n c : ℕ} (x₀ : HomE E n' n) (y' : Sp E n) : HomE E (n' + c') (n + c) :=
  Loc.inX E n c ∘ₗ (x₀ ∘ₗ LinearMap.funLeft E E (Fin.castAdd c') + (atNL E (n' + c') n').smulRight y')

def PsiAt (m2 : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R m2) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))) : X.K :=
  omPhi Ch sel mu cst m2 P hal 1 (joinCol x₀ y')

def FiniteSumNonzeroLargeDepth (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (h : AutY X R (i + 1)) : Prop :=
  ∃ A₀ B₀ : ℕ, ∀ A' B', A₀ ≤ A' → B₀ ≤ B' → E1at Ch sel mu { cst with A := A', B := B' } i P hal h ≠ 0

open Classical in

structure ChIdx.Ok (G : ChGlob X R.m) (m2 : ℕ) : Prop where
  hm : R.m = m2 + 2
  cst_ok : cst.Ok

  xiUnitAtPrime : XiUnitAt (rowSG Pr sel mu) G.xi0

  weil : cst.WeilTied G.σ₀ G.xi0

  muqQ : ∀ (i : ℕ) (h : i < R.m) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
    cst.muq (i + 1) P = (((Ch.muVal ⟨i, h⟩ P.1)⁻¹ * (qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K)

  muqG : ∀ (i : ℕ) (h : i < R.m) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ qu : X.Eˣ, (qu : X.E) = (qOf P.1 : X.E) →
    G.σ₀ (cst.muq (i + 1) P) =
      (((G.mu0 ⟨i, h⟩).locK P.1 qu : ℂˣ) : ℂ)⁻¹ * G.σ₀ ((((qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ)) : X.K)

  mu0G : ∀ (j : Fin R.m) (w : {w // w ∈ Pr.vGs}) (x : X.Eˣ) (y : 𝓞 X.E) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ), (x : X.E) = (y : X.E) →
    (c : 𝓞 X.E ⧸ w.1.asIdeal) = Ideal.Quotient.mk w.1.asIdeal y →
    (((G.mu0 j).locK w.1 x : ℂˣ) : ℂ) = G.σ₀ (((Ch.chi j w c)⁻¹ : X.Kˣ) : X.K)

  psi0 : ∀ (P : rowSG Pr sel mu) (a : X.E), P.1 ∈ Pr.vGs → IntAt P.1 a →
    cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)

  deep : ∀ A' B', cst.A ≤ A' → cst.B ≤ B' → ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu),
    E1at Ch sel mu { cst with A := A', B := B' } i P (L.h i al P) (L.h (i + 1) be P) =
      E1at Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P)

  zero_uniq : ∃ b : L.β 0, ∀ b', b' = b
  zero_h : ∀ b P, L.h 0 b P = 1
  zero_G : ∀ b, L.levG 0 b = colLev Ch 0
  zero_Q : ∀ b, L.levQ 0 b = LevQFam.top X.E X.K (R.N 0) _

  last_uniq : ∃ b : L.β (m2 + 1), ∀ b', b' = b
  last_h : ∀ b P, L.h (m2 + 1) b P = 1

  nonvan : ∀ i, i < m2 → ∀ (b : L.β (i + 1)) (P : rowSG Pr sel mu), ∃ al : L.β i, FiniteSumNonzeroLargeDepth Ch sel mu cst i P (L.h i al P) (L.h (i + 1) b P)

  inj : ∀ i, i < m2 → ∀ b b' : L.β (i + 1), (∀ P : rowSG Pr sel mu, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 (L.h (i + 1) b P) (L.h (i + 1) b' P)) → b = b'

  surj : ∀ i, i < m2 → ∀ hh : rowSG Pr sel mu → AutY X R (i + 1),
    (∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → hh P ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1)) →
    (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → (∀ x ∈ lamYat (Pr := Pr) (R := R) (i + 1) P.1, (hh P)⁻¹ x ∈ lamYat (Pr := Pr) (R := R) (i + 1) P.1 ∧ ((qOf P.1 : X.E) ^ (i + 1)) • (hh P) x ∈ lamYat (Pr := Pr) (R := R) (i + 1) P.1)) →
    (∀ P, ∃ al : L.β i, FiniteSumNonzeroLargeDepth Ch sel mu cst i P (L.h i al P) (hh P)) →
    ∃ b : L.β (i + 1), ∀ P, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 (L.h (i + 1) b P) (hh P)

  stabG : ∀ j (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P ∈ stabL X.E _ (lamYat (Pr := Pr) j P.1)

  depthG : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → cst.D P = 1
  depthQ : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P

  depthQ' : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * (R.m - 1) + 1 ≤ cst.D P

  boundQ : ∀ j (b : L.β j) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → (∀ x ∈ lamYat (Pr := Pr) (R := R) j P.1, (L.h j b P)⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P.1 ∧ ((qOf P.1 : X.E) ^ (j)) • (L.h j b P) x ∈ lamYat (Pr := Pr) (R := R) j P.1)

  psiSupp : ∀ (al : L.β m2) (P : rowSG Pr sel mu) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ y' ≠ 0 → ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M) * y' i)
  psiInv : ∀ (al : L.β m2) (P : rowSG Pr sel mu) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' z : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ * z i)) →
      PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ (y' + z) = PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ y'

  xiSupp : ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu) (x : HomE X.E (R.N i) (R.N (i + 1))),
    XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) x ≠ 0 → ∀ s l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * x (Pi.single s 1) l)
  xiInv : ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu) (x z : HomE X.E (R.N i) (R.N (i + 1))),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.B)⁻¹ * z (Pi.single s 1) l)) →
      XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) (x + z) = XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) x
  psiSuppX : ∀ (al : L.β m2) (P : rowSG Pr sel mu) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ y' ≠ 0 → ∀ s l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.A * x₀ (Pi.single s 1) l)
  psiInvX : ∀ (al : L.β m2) (P : rowSG Pr sel mu) (x₀ z : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.B)⁻¹ * z (Pi.single s 1) l)) →
      PsiAt Ch sel mu cst m2 P (L.h m2 al P) (x₀ + z) y' = PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ y'

  int : ∀ j (b : L.β j) (P : rowSG Pr sel mu), prCat (Pr := Pr) cst.sharp j P.1 (L.h j b P) ≤ GLint X.E (R.N j) P.1

  grpQ : ∀ j (b : L.β j) (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}),
    (L.levQ j b P).H = (prCat (Pr := Pr) cst.sharp j P.1 (L.h j b ⟨P.1, Finset.mem_union_right _ P.2⟩)).subgroupOf (GLint X.E (R.N j) P.1)
  chrQ : ∀ j (b : L.β j) (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (g : ↥(L.levQ j b P).H) (r : AutY X R j),
    r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b ⟨P.1, Finset.mem_union_right _ P.2⟩) →
    (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g.1.1 x)) →
    (((L.levQ j b P).lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j ⟨P.1, Finset.mem_union_right _ P.2⟩ (L.h j b ⟨P.1, Finset.mem_union_right _ P.2⟩) r

  grpG : ∀ j (b : L.β j) (w : {w // w ∈ Pr.vGs}) (hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)),
    hbar ∈ (L.levG j b w).H ↔ ∃ g ∈ prCat (Pr := Pr) cst.sharp j w.1 (L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩),
      ∀ x ∈ stdAt X.E (R.N j) w.1, redV w.1 (g x) = hbar.1.mulVec (redV w.1 x)
  chrG : ∀ j (b : L.β j) (w : {w // w ∈ Pr.vGs}) (hbar : ↥(L.levG j b w).H) (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (r : AutY X R j),
    r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j w.1) (L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩) →
    (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) →
    (∀ x ∈ stdAt X.E (R.N j) w.1, redV w.1 (g x) = hbar.1.1.mulVec (redV w.1 x)) →
    (((L.levG j b w).lam hbar : X.Kˣ) : X.K) = chiInv Ch sel mu cst j ⟨w.1, Finset.mem_union_left _ w.2⟩ (L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩) r

abbrev ChPt (u : Pr.Word) (j : ℕ) : Type := DecoF X.E (R.N j) (Pr.vT u) Pr.vGs (QE sel (mu : Chr X.F X.E X.K))

def colValF (u : Pr.Word) (j : ℕ) : CoefPk X (R.N j) (ChPt (R := R) sel mu u j) :=
  (colVal W u j (Pr.vT u) Pr.vGs).pull DecoF.deco

open Classical in

@[reducible] def chF (u : Pr.Word) (j : ℕ) : GFam X.K where
  β := L.β j
  V := (colValF W sel mu u j).V
  ιV := VVIdx (colValF W sel mu u j).lam
  bV := (colValF W sel mu u j).bV
  pair := (colValF W sel mu u j).pair
  G b := FrmG (L.levG j b) (L.levQ j b)
  D _ := ChPt (R := R) sel mu u j
  actD b := frmAct (L.levG j b) (L.levQ j b)
  ρ b := frmRho (colValF W sel mu u j) (L.levG j b) (L.levQ j b)
  Nab _ := (colValF W sel mu u j).Nab
  Del _ := (colValF W sel mu u j).Del

open Classical in

def frsF {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) : Frs X.E (R.N j) (rowSG Pr sel mu) := fun P =>
  if h : P.1 ∈ Pr.vGs then p.deco.1.liftFr ⟨P.1, h⟩ else p.fr ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩

def frsT (u : Pr.Word) (d : RowPt Pr R sel mu) : Frs X.E (R.N R.m) (rowSG Pr sel mu) := fun P => (tilQ sel mu u d).1.liftFr P

open Classical in

def Sall (u : Pr.Word) : Finset (HeightOneSpectrum (𝓞 X.E)) := Pr.vT u ∪ rowSG Pr sel mu

def cAof : ℕ := (∏ P : rowSG Pr sel mu, qOf P.1) ^ cst.A

def cBof (u : Pr.Word) : ℕ := Pr.T u * (∏ P : rowSG Pr sel mu, qOf P.1) ^ cst.B

def XiEntry {u : Pr.Word} (i : ℕ) (al : L.β i) (be : L.β (i + 1)) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  phiT X.K p.deco.1 p'.deco.1 x *
    ∏ P : rowSG Pr sel mu, XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) (inFr (frsF sel mu p P) (frsF sel mu p' P) x)

def locLat {E : Type} [Field E] [NumberField E] {n : ℕ} (SB : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n))
    (e : SB → ℤ) : Submodule (𝓞 E) (Sp E n) :=
  ⨅ P : SB, (localization₂ P.1.asIdeal N).comap
    ((((qOf P.1 : E) ^ e P)⁻¹ • (LinearMap.id : Sp E n →ₗ[E] Sp E n)).restrictScalars (𝓞 E))

open Classical in

def ybSet {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) : Set (Set (Sp X.E n)) :=
  {Y | ∃ y ∈ locLat (rowSG Pr sel mu) N (fun P => if P.1 ∈ Pr.vGs then -1 else -(cst.M : ℤ)),
    Y = {z | z - y ∈ locLat (rowSG Pr sel mu) N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}}

def repY {n : ℕ} (Y : Set (Sp X.E n)) : Sp X.E n := Classical.epsilon fun y => y ∈ Y

def XiCpl1 {u : Pr.Word} (m2 : ℕ) (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1))
    (Y : Set (Sp X.E (R.N (m2 + 1)))) (x : HomE X.E (R.N m2) (R.N (m2 + 1))) : X.K :=
  phiT X.K p₀.deco.1 p.deco.1 x *
    ∏ P : rowSG Pr sel mu, PsiAt Ch sel mu cst m2 P (L.h m2 al P) (inFr (frsF sel mu p₀ P) (frsF sel mu p P) x)
      ((frsF sel mu p P).symm (repY Y))

open Classical in

def PhiTop (sharp : Bool) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : Loc.SF X.E X.K (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0) :=
  if P ∈ Pr.vGs then
    (if sharp then LocE.PhiGS (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.rS R.r R.t R.m (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1)
      else LocE.PhiG (qOf P) (psi0P Ch P) (chiP Ch P) false R.k R.r R.t R.m (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1))
  else LocE.PhiQ (qOf P) (resChar (mu : Chr X.F X.E X.K) P) R.k R.r (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1)

open Classical in

def ftY {n : ℕ} (P : rowSG Pr sel mu) (η : Sp X.E n →ₗ[X.E] X.E) (y' : Sp X.E n) : X.K :=
  if P.1 ∈ Pr.vGs then
    (if ∀ i : Fin n, IntAt P.1 (η (Pi.single i 1)) then cst.psi P ((epsSg : X.E) * η y') else 0)
  else
    (if ∀ i : Fin n, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single i 1))
      then ((qOf P.1 : X.K) ^ (cst.M * n))⁻¹ * cst.psi P ((epsSg : X.E) * η y') else 0)

def prXp (E : Type) [Field E] (R : Ranks) : Sp E (R.N R.m) →ₗ[E] Sp E ((R.N R.m - 1) + 0) :=
  LinearMap.funLeft E E fun i : Fin ((R.N R.m - 1) + 0) => (⟨i.1, by have := i.2; omega⟩ : Fin (R.N R.m))

def XiCpl2 {u : Pr.Word} (m2 : ℕ) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu)
    (x : HomE X.E (R.N (m2 + 1)) (R.N R.m)) : X.K :=
  phiT X.K p.deco.1 (tilQ sel mu u d).1 x *
    ∏ P : rowSG Pr sel mu,
      PhiTop Ch mu cst.sharp m2 P.1 ((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap ∘ₗ
          LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
        ftY sel mu cst P ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap)
          ((frsF sel mu p P).symm (repY Y))

end ColChain2

section YbEquiv

variable {X : Fields} {Pr : Primes X}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem mem_locLat {E : Type} [Field E] [NumberField E] {n : ℕ} (SB : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Sp E n)) (e : SB → ℤ) (z : Sp E n) :
    z ∈ locLat SB N e ↔ ∀ P : SB, ((qOf P.1 : E) ^ e P)⁻¹ • z ∈ localization₂ P.1.asIdeal N := by
  simp only [locLat, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem mem_locLat_gmap {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (SB : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Sp E n)) (e : SB → ℤ) (γ : Sp E n ≃ₗ[E] Sp E n) (z : Sp E n) :
    z ∈ locLat SB (gmap γ N) e ↔ γ.symm z ∈ locLat SB N e := by
  rw [mem_locLat, mem_locLat]
  refine forall_congr' fun P => ?_
  rw [mem_localization_gmap, map_smul]

theorem ybSet_gmap {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (Y : Set (Sp X.E n)) :
    (fun v => γ v) '' Y ∈ ybSet sel mu cst (gmap γ N) ↔ Y ∈ ybSet sel mu cst N := by
  constructor
  · rintro ⟨y, hy, hY⟩
    refine ⟨γ.symm y, (mem_locLat_gmap _ _ _ _ _).1 hy, ?_⟩
    ext z
    have h1 : z ∈ Y ↔ γ z ∈ (fun v => γ v) '' Y :=
      ⟨fun h => ⟨z, h, rfl⟩, fun ⟨z', h', e⟩ => by rwa [← γ.injective e]⟩
    rw [h1, hY, Set.mem_ofPred_eq, Set.mem_ofPred_eq, mem_locLat_gmap, map_sub, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, hy, hY⟩
    refine ⟨γ y, (mem_locLat_gmap _ _ _ _ _).2 (by rwa [LinearEquiv.symm_apply_apply]), ?_⟩
    ext z
    rw [Set.mem_ofPred_eq, mem_locLat_gmap, map_sub, LinearEquiv.symm_apply_apply]
    constructor
    · rintro ⟨z', h', rfl⟩
      rw [hY] at h'
      simpa using h'
    · intro h
      refine ⟨γ.symm z, ?_, LinearEquiv.apply_symm_apply γ z⟩
      rw [hY]
      exact h

end YbEquiv

section ColChain3

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

abbrev midGSD (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) : GSD X.K := (chF W sel mu L u (m2 + 1)).mem b

structure YbHyp (u : Pr.Word) (m2 : ℕ) (_b : L.β (m2 + 1)) : Prop where
  fin : ∀ p : ChPt (R := R) sel mu u (m2 + 1), (ybSet sel mu cst p.deco.1.N).Finite

def ybCpl (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) : Cpl (midGSD W sel mu L u m2 b) where
  Yb := Set (Sp X.E (R.N (m2 + 1)))
  actY :=
    { smul := fun g Y => (fun v => g.1.1 v) '' Y
      one_smul := fun Y => Set.image_id Y
      mul_smul := fun g h Y => (Set.image_image (fun v => g.1.1 v) (fun v => h.1.1 v) Y).symm }
  ys p := ybSet sel mu cst p.deco.1.N
  fin := hY.fin
  equiv := fun g p Y => ybSet_gmap sel mu cst p.deco.1.N g.1.1 Y

structure ChKer (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) where
  kk : KerFam (chF W sel mu L u)
  cp : ∀ al : L.β m2, CplKer ((chF W sel mu L u m2).mem al) (midGSD W sel mu L u m2 b) (evGSD W Ch sel mu P u) (ybCpl W sel mu cst L u m2 b hY)

structure ChTh (u : Pr.Word) (m2 : ℕ) where
  th : ∀ i, ThDist X.E X.K (R.N i) (R.N (i + 1)) (rowSG Pr sel mu) (colValF W sel mu u i).V (colValF W sel mu u (i + 1)).V
  top : ThDist X.E X.K (R.N (m2 + 1)) (R.N R.m) (rowSG Pr sel mu) (colValF W sel mu u (m2 + 1)).V
    (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).V

open Classical in

def rhoS (i : ℕ) (P : rowSG Pr sel mu) : X.E → X.K :=
  LocE.unitV (if P.1 ∈ Pr.vGs then chiP Ch P.1 i else (resChar (mu : Chr X.F X.E X.K) P.1)⁻¹)

open Classical in

def rhoT (i : ℕ) (P : rowSG Pr sel mu) : X.E → X.K :=
  LocE.unitV (if P.1 ∈ Pr.vGs then (chiP Ch P.1 i)⁻¹ else resChar (mu : Chr X.F X.E X.K) P.1)

variable {W Ch sel mu cst L}

structure ChTh.Ok (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word} {m2 : ℕ} (T : ChTh W sel mu u m2) : Prop where
  th : ∀ i, i ≤ m2 → ThDist.Ok (T.th i) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (colValF W sel mu u i).rho
    (colValF W sel mu u (i + 1)).rho (rhoS Ch sel mu i) (rhoT Ch sel mu i)
  top : ThDist.Ok T.top (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (colValF W sel mu u (m2 + 1)).rho
    (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho (rhoS Ch sel mu (m2 + 1)) (rhoT Ch sel mu (m2 + 1))

structure ChKer.Shape {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)}
    {hY : YbHyp (R := R) sel mu cst L u m2 b} (A : ChKer W Ch sel mu cst L P u m2 b hY) (T : ChTh W sel mu u m2) : Prop where

  lev : (cst.sharp = false ∧ P = rP0 Ch) ∨ (cst.sharp = true ∧ P = rPsymF Ch)
  mat : ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)),
    (A.kk i al be).k p p' = kerOf (T.th i) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p)
      p'.deco.1.N (frsF sel mu p') (XiEntry Ch sel mu cst L i al be p p')
  cp1 : ∀ (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))),
    Y ∈ ybSet sel mu cst p.deco.1.N → (A.cp al).k1 p₀ p Y = kerOf (T.th m2) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p₀.deco.1.N (frsF sel mu p₀)
      p.deco.1.N (frsF sel mu p) (XiCpl1 Ch sel mu cst L m2 al p₀ p Y)
  cp2 : ∀ (al : L.β m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu),
    Y ∈ ybSet sel mu cst p.deco.1.N → (A.cp al).k2 p Y d = kerOf T.top (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p)
      (tilQ sel mu u d).1.N (frsT sel mu u d) (XiCpl2 Ch sel mu cst m2 p Y d)

def ChKer.colF {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)}
    {hY : YbHyp (R := R) sel mu cst L u m2 b} (A : ChKer W Ch sel mu cst L P u m2 b hY) (hF : ∀ j, (chF W sel mu L u j).Ok) :
    (chF W sel mu L u 0).Forms →ₗ[X.K] (evGSD W Ch sel mu P u).EqFun :=
  colCpl A.kk hF m2 A.cp (hF (m2 + 1) b)

end ColChain3

section Bt

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def BtOf (P : LevFam X.E X.K R.r Pr.vGs) (h : (mtildeGSD W Ch sel mu P).Ok) (Xg : Finset (G0 X.E Pr.vGs R.r → X.K))
    (u : Pr.Word) (col : MfV W Ch u →ₗ[X.K] (evGSD W Ch sel mu P u).EqFun) :
    MramV W Ch u →ₗ[X.K] ↥(V0X W Ch sel mu Xg P) →ₗ[X.K] X.K :=
  (PtilFF W Ch sel mu P h u).compl₁₂
    ((evGSD W Ch sel mu P u).EqFun.subtype ∘ₗ col ∘ₗ (MramV W Ch u).subtype)
    ((mtildeKGSD W Ch sel mu).EqFun.subtype ∘ₗ (V0X W Ch sel mu Xg P).subtype)

variable {W Ch sel mu}

def PerKillsU {P : LevFam X.E X.K R.r Pr.vGs} {Xg : Finset (G0 X.E Pr.vGs R.r → X.K)} {u : Pr.Word}
    (B : MramV W Ch u →ₗ[X.K] ↥(V0X W Ch sel mu Xg P) →ₗ[X.K] X.K) (U : Submodule X.K ↥(V0X W Ch sel mu Xg P)) : Prop :=
  ∀ φ, ∀ F ∈ U, B φ F = 0

def BkOf {P : LevFam X.E X.K R.r Pr.vGs} {Xg : Finset (G0 X.E Pr.vGs R.r → X.K)} {u : Pr.Word}
    (B : MramV W Ch u →ₗ[X.K] ↥(V0X W Ch sel mu Xg P) →ₗ[X.K] X.K) (U : Submodule X.K ↥(V0X W Ch sel mu Xg P))
    (hU : PerKillsU B U) : MramV W Ch u →ₗ[X.K] (↥(V0X W Ch sel mu Xg P) ⧸ U) →ₗ[X.K] X.K :=
  (U.liftQ B.flip fun F hF => by
    rw [LinearMap.mem_ker]
    ext φ
    exact hU φ F hF).flip

end Bt

section Nu

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

structure Serv (u : Pr.Word) where

  served : Finset ℕ

  yM : HeightOneSpectrum (𝓞 X.K) → Submodule (𝓞 X.K) (MfV W Ch u)

  tau : HeightOneSpectrum (𝓞 X.K) → ℕ

variable {W Ch}

structure Serv.Ok {u : Pr.Word} (Sv : Serv W Ch u) : Prop where
  prime : ∀ p ∈ Sv.served, p.Prime
  T_not : Pr.T u ∉ Sv.served
  le : ∀ w : HeightOneSpectrum (𝓞 X.K), prW w ∈ Sv.served → Sv.yM w ≤ MfL W Ch u
  ge : ∀ w : HeightOneSpectrum (𝓞 X.K), prW w ∈ Sv.served → ∃ c : ℕ,
    (MfL W Ch u).map (((prW w : 𝓞 X.K) ^ c) • (LinearMap.id : MfV W Ch u →ₗ[𝓞 X.K] MfV W Ch u)) ≤ Sv.yM w

def Serv.NP {u : Pr.Word} (Sv : Serv W Ch u) (w : HeightOneSpectrum (𝓞 X.K)) : Submodule (𝓞 X.K) (MramV W Ch u) :=
  (Sv.yM w ⊓ (MfL W Ch u).map (((prW w : 𝓞 X.K) ^ Sv.tau w) • (LinearMap.id : MfV W Ch u →ₗ[𝓞 X.K] MfV W Ch u))).comap
    ((MramV W Ch u).subtype.restrictScalars (𝓞 X.K))

open Classical in

def NuAt {u : Pr.Word} (Sv : Serv W Ch u) (w : HeightOneSpectrum (𝓞 X.K)) : Submodule (𝓞 X.K) (MramV W Ch u) :=
  if ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal then NlamG W Ch u w
  else if prW w ∈ Sv.served then Sv.NP w
  else MramL W Ch u

def NuC {u : Pr.Word} (Sv : Serv W Ch u) : Submodule (𝓞 X.K) (MramV W Ch u) :=
  ⨅ w : HeightOneSpectrum (𝓞 X.K), localization₂ w.asIdeal (NuAt Sv w)

end Nu

section NuPrime

variable {K : Type} [Field K] [NumberField K]

def toFinPl (w : HeightOneSpectrum (𝓞 K)) : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K := ⟨w.asIdeal, w.isMaximal⟩

def ofFinPl (w : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.1
  isPrime := w.2.isPrime
  ne_bot := fun h => by
    have h1 := w.2
    rw [h] at h1
    exact RingOfIntegers.not_isField K (Ring.isField_iff_maximal_bot.mpr h1)

def sgFloor (s : HeightOneSpectrum (𝓞 K) → ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℤ := ⌊(eW w : ℝ) * s w⌋

open Classical in

def sgFin (s : HeightOneSpectrum (𝓞 K) → ℝ) : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K →₀ ℤ :=
  if h : (Function.support fun w : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K => sgFloor s (ofFinPl w)).Finite
  then Finsupp.ofSupportFinite _ h else 0

def sgSumOf (m : ℕ) (gain F Eu : ℕ → HeightOneSpectrum (𝓞 K) → ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ j ∈ Finset.Icc 1 m, (gain j w + F j w) - ∑ j ∈ Finset.Icc 1 m, Eu j w

end NuPrime

def NuPrimeC {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m} {u : Pr.Word}
    (Sv : Serv W Ch u) (gain F Eu : ℕ → HeightOneSpectrum (𝓞 X.K) → ℝ) : Submodule (𝓞 X.K) (MramV W Ch u) :=
  Formalism.LFunctionChainParameters.slopeLatticeData.modLat (sgFin (sgSumOf R.m gain F Eu)) (NuC Sv)

section ColOp

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}

theorem LevQFam.top_chr {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}
    {Q : Finset (HeightOneSpectrum (𝓞 E))} (c : ↥(LevQFam.top E K n Q).grp) : (LevQFam.top E K n Q).chr c = 1 := by
  exact (piChar_apply (fun P => (LevQFam.top E K n Q P).H) (fun P => (LevQFam.top E K n Q P).lam) c).trans
    (Finset.prod_eq_one fun _ _ => rfl)

theorem start_mem (u : Pr.Word) (Λ : LevFam X.E X.K (R.N 0) Pr.vGs)
    (Θ : LevQFam X.E X.K (R.N 0) (QE sel (mu : Chr X.F X.E X.K))) (hΛ : Λ = colLev Ch 0) (hΘ : Θ = LevQFam.top X.E X.K (R.N 0) _)
    (φ : MfV W Ch u) :
    (fun p : ChPt (R := R) sel mu u 0 => (φ : (colGSD W Ch u 0).D → (colGSD W Ch u 0).V) p.deco) ∈
      (frmGSD (colValF W sel mu u 0) Λ Θ).EqFun := by
  subst hΛ hΘ
  intro g p
  have h1 := φ.2 (g.1, g.2.1) p.deco
  show (φ : (colGSD W Ch u 0).D → (colGSD W Ch u 0).V) ((g.1, g.2.1) • p.deco) = _
  rw [h1]
  have h2 : frmRho (colValF W sel mu u 0) (colLev Ch 0) (LevQFam.top X.E X.K (R.N 0) _) g =
      formRho (colVal W u 0 (Pr.vT u) Pr.vGs) (colLev Ch 0) (g.1, g.2.1) := by
    show ((((colLev Ch 0).chr g.2.1 * (LevQFam.top X.E X.K (R.N 0) _).chr g.2.2 : X.Kˣ)) : X.K) •
      (colValF W sel mu u 0).rho g.1 = _
    rw [LevQFam.top_chr, mul_one]
    rfl
  exact (LinearMap.congr_fun h2 _).symm

def startC {m2 : ℕ} {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2) (u : Pr.Word) : MfV W Ch u →ₗ[X.K] (chF W sel mu L u 0).Forms :=
  LinearMap.pi fun b =>
    { toFun := fun φ => ⟨_, start_mem u (L.levG 0 b) (L.levQ 0 b) (hL.zero_G b) (hL.zero_Q b) φ⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def colC {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := R) sel mu cst L u m2 b}
    (A : ChKer W Ch sel mu cst L P u m2 b hY) (hF : ∀ j, (chF W sel mu L u j).Ok) {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2) :
    MfV W Ch u →ₗ[X.K] (evGSD W Ch sel mu P u).EqFun :=
  A.colF hF ∘ₗ startC hL u

def BtC {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := R) sel mu cst L u m2 b}
    (A : ChKer W Ch sel mu cst L P u m2 b hY) (hF : ∀ j, (chF W sel mu L u j).Ok) {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2)
    (h : (mtildeGSD W Ch sel mu P).Ok) (Xg : Finset (G0 X.E Pr.vGs R.r → X.K)) (_hXg : ∀ χ ∈ Xg, IsAbsIrrChar χ)
    (_hS : Pr.T u ∈ S ∧ ∀ i, Pr.g i ∈ S) :
    MramV W Ch u →ₗ[X.K] ↥(V0X W Ch sel mu Xg P) →ₗ[X.K] X.K :=
  BtOf W Ch sel mu P h Xg u (colC A hF hL)

def BkC {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := R) sel mu cst L u m2 b}
    (A : ChKer W Ch sel mu cst L P u m2 b hY) (hF : ∀ j, (chF W sel mu L u j).Ok) {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2)
    (h : (mtildeGSD W Ch sel mu P).Ok) (Xg : Finset (G0 X.E Pr.vGs R.r → X.K)) (hXg : ∀ χ ∈ Xg, IsAbsIrrChar χ)
    (hS : Pr.T u ∈ S ∧ ∀ i, Pr.g i ∈ S) (U : Submodule X.K ↥(V0X W Ch sel mu Xg P))
    (hU : PerKillsU (BtC A hF hL h Xg hXg hS) U) : MramV W Ch u →ₗ[X.K] (↥(V0X W Ch sel mu Xg P) ⧸ U) →ₗ[X.K] X.K :=
  BkOf (BtC A hF hL h Xg hXg hS) U hU

end ColOp

section Names

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}

def Kop {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := R) sel mu cst L u m2 b}
    (A : ChKer W Ch sel mu cst L P u m2 b hY) (hF : ∀ j, (chF W sel mu L u j).Ok) (i : ℕ) :
    (chF W sel mu L u i).Forms →ₗ[X.K] (chF W sel mu L u (i + 1)).Forms :=
  A.kk.step hF i

def KopLast {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := R) sel mu cst L u m2 b}
    (A : ChKer W Ch sel mu cst L P u m2 b hY) (hF : ∀ j, (chF W sel mu L u j).Ok) (al : L.β m2) :
    ((chF W sel mu L u m2).mem al).EqFun →ₗ[X.K] (evGSD W Ch sel mu P u).EqFun :=
  ((A.cp al).comp (hF (m2 + 1) b) (midGSD W sel mu L u m2 b).outSec).opOf (hF m2 al) ((chF W sel mu L u m2).mem al).outSec

def PerInv (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    (mu : Tup X.F X.E X.K S) (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) : Prop :=
  ∀ (g : FormG (rowTy Ch sel mu P).inv) (x : VV X.K (W.lamTrue u R.m)) (y : VV X.K W.sgTrue),
    pairBK W.sgTrue (brC W u (evRho W Ch sel mu P u g x)) ((mtildeGSD W Ch sel mu P).ρ g y) = pairBK W.sgTrue (brC W u x) y

end Names

namespace Br

def BrEquiv (K : Type) [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) : Prop :=
  (∀ τ, SameShift (lam τ) (sg τ)) →
  ∀ (g : ι → GL (Fin n) K) (g' : ι → GL (Fin N) K),
    (∀ τ, (∀ a b : Fin n, (g' τ : Matrix _ _ K) (iC hN a) (iC hN b) = (g τ : Matrix _ _ K) a b) ∧
      (∀ a : Fin n, (g' τ : Matrix _ _ K) (iC hN a) (iL hN) = 0 ∧ (g' τ : Matrix _ _ K) (iL hN) (iC hN a) = 0) ∧
      (g' τ : Matrix _ _ K) (iL hN) (iL hN) = 1) →
    ∀ G : VV K lam, brStd hN lam sg (rhoK lam g' G) = rhoK sg g (brStd hN lam sg G)

def sumLat {K : Type} [Field K] [NumberField K] {N n : ℕ} (hN : N = n + 1) (M' : Submodule (𝓞 K) (Fin n → K)) (t : K) :
    Submodule (𝓞 K) (Fin N → K) where
  carrier := {x | (fun a : Fin n => x (iC hN a)) ∈ M' ∧ ∃ c : 𝓞 K, x (iL hN) = (c : K) * t}
  add_mem' := by
    rintro x y ⟨hx, c, hc⟩ ⟨hy, d, hd⟩
    exact ⟨M'.add_mem hx hy, c + d, by simp [hc, hd, add_mul]⟩
  zero_mem' := ⟨M'.zero_mem, 0, by simp⟩
  smul_mem' := by
    rintro r x ⟨hx, c, hc⟩
    refine ⟨M'.smul_mem r hx, r * c, ?_⟩
    simp only [Pi.smul_apply, hc, map_mul, Algebra.smul_def, mul_assoc]

def BrIntegral (K : Type) [Field K] [NumberField K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N)
    (sg : ι → DomWeight n) : Prop :=
  (∀ τ, Interlace hN (lam τ) (sg τ)) → (∀ τ, SameShift (lam τ) (sg τ)) →
  ∀ (M' : ι → Submodule (𝓞 K) (Fin n → K)) (t : ι → K), (∀ τ, t τ ≠ 0) →
    ∀ G ∈ delK lam fun τ => sumLat hN (M' τ) (t τ), brAt hN lam sg t G ∈ delK sg M'

end Br

end Formalism.L2.Col
