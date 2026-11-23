import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.LocalToGlobal.Columns.GSetLemmas
import Formalism.LocalToGlobal.Columns.PolyFn
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.Divisibility.Frames
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.ThDistC

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix

structure FOk {E K ι : Type} [Field E] [StarRing E] [Field K] [StarRing K] (emb : ι → E →+* K) (σ : K →+* ℂ) : Prop where
  conjE : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)
  emb_star : ∀ τ x, emb τ (star x) = star (emb τ x)
  sig_star : ∀ x, σ (star x) = starRingEnd ℂ (σ x)

structure GStep (E K : Type) [Field E] [NumberField E] [Field K] (n : ℕ) where

  β : Type
  [finβ : Fintype β]
  [decβ : DecidableEq β]

  G : β → Type
  [grpG : ∀ b, Group (G b)]

  D : β → Type
  [actD : ∀ b, MulAction (G b) (D b)]

  gam : ∀ b, G b →* GL (Fin n) E

  chr : ∀ b, G b →* Kˣ

  Lsh : ∀ b, D b → Submodule (𝓞 E) (Fin n → E)

  rp : ∀ b, MulAction.orbitRel.Quotient (G b) (D b) → D b
  rp_spec : ∀ b q, Quotient.mk (MulAction.orbitRel (G b) (D b)) (rp b q) = q

attribute [instance] GStep.finβ GStep.decβ GStep.grpG GStep.actD

section Fr

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) (n : ℕ)

abbrev Gr : ι → Matrix (Fin n) (Fin n) ℂ := gramC (1 : Matrix (Fin n) (Fin n) E) (embAt σ emb)

abbrev Fr : Type := Frames (Gr emb σ n)

def fr0 : Fr emb σ n := stdFrC (embAt σ emb)

variable {n}

def frMul (γ : GL (Fin n) E) (y : Fr emb σ n) : Fr emb σ n :=
  ⟨fun τ => (γ : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ) * y.1 τ, fun τ => by
    rw [det_mul]
    refine IsUnit.mul ?_ (y.2 τ)
    have h := (RingHom.map_det (embAt σ emb τ) (γ : Matrix (Fin n) (Fin n) E))
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    exact (Matrix.isUnit_iff_isUnit_det _ |>.1 γ.isUnit).map _⟩

theorem frMul_mul (γ δ : GL (Fin n) E) (y : Fr emb σ n) :
    frMul emb σ (γ * δ) y = frMul emb σ γ (frMul emb σ δ y) := by
  apply Subtype.ext
  funext τ
  simp [frMul, Matrix.map_mul, Matrix.mul_assoc]

theorem frMul_one (y : Fr emb σ n) : frMul emb σ 1 y = y := by
  apply Subtype.ext
  funext τ
  simp [frMul]

def frEquiv (γ : GL (Fin n) E) : Fr emb σ n ≃ Fr emb σ n where
  toFun := frMul emb σ γ
  invFun := frMul emb σ γ⁻¹
  left_inv y := by rw [← frMul_mul, inv_mul_cancel, frMul_one]
  right_inv y := by rw [← frMul_mul, mul_inv_cancel, frMul_one]

def trFr (γ : GL (Fin n) E) (c : Kˣ) : (Fr emb σ n → ℂ) ≃ₗ[ℂ] (Fr emb σ n → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ (frEquiv emb σ γ⁻¹)).trans (LinearEquiv.smulOfUnit (Units.map (σ : K →* ℂ) c))

theorem trFr_apply (γ : GL (Fin n) E) (c : Kˣ) (F : Fr emb σ n → ℂ) (y : Fr emb σ n) :
    trFr emb σ γ c F y = σ c * F (frMul emb σ γ⁻¹ y) := rfl

end Fr

namespace GStep

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

structure Ok (S : GStep E K n) : Prop where
  fin_orb : ∀ b, Finite (MulAction.orbitRel.Quotient (S.G b) (S.D b))
  fin_stab : ∀ b (d : S.D b), Finite (MulAction.stabilizer (S.G b) d)
  unit : ∀ b (g : S.G b), (S.gam b g : Matrix (Fin n) (Fin n) E)ᴴ * (S.gam b g : Matrix (Fin n) (Fin n) E) = 1
  root : ∀ b (g : S.G b), ∃ m : ℕ, 0 < m ∧ S.chr b g ^ m = 1
  lsh_smul : ∀ b (g : S.G b) (d : S.D b) (x : Fin n → E),
    (S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ S.Lsh b (g • d) ↔ x ∈ S.Lsh b d
  lsh_lat : ∀ b (d : S.D b), Submodule.IsLattice E (S.Lsh b d)
  stab_inj : ∀ b (g : S.G b) (d : S.D b), g • d = d → S.gam b g = 1 → g = 1

def Free (S : GStep E K n) : Prop := ∀ b (g : S.G b) (d : S.D b), g • d = d → g = 1

abbrev Cl : Type := Σ b, MulAction.orbitRel.Quotient (S.G b) (S.D b)

def rep (c : S.Cl) : S.D c.1 := S.rp c.1 c.2

@[reducible] def cl (b : S.β) (d : S.D b) : S.Cl := ⟨b, Quotient.mk _ d⟩

theorem exists_mv (b : S.β) (d : S.D b) : ∃ g : S.G b, g • S.rep (S.cl b d) = d := by
  have h : (MulAction.orbitRel (S.G b) (S.D b)).r d (S.rep (S.cl b d)) :=
    (MulAction.orbitRel (S.G b) (S.D b)).symm (Quotient.exact (S.rp_spec b (Quotient.mk _ d)))
  exact h

def mv (b : S.β) (d : S.D b) : S.G b := (S.exists_mv b d).choose

theorem mv_smul (b : S.β) (d : S.D b) : S.mv b d • S.rep (S.cl b d) = d := (S.exists_mv b d).choose_spec

abbrev Stab (c : S.Cl) : Type := MulAction.stabilizer (S.G c.1) (S.rep c)

def tr (b : S.β) (g : S.G b) : (Fr emb σ n → ℂ) ≃ₗ[ℂ] (Fr emb σ n → ℂ) := trFr emb σ (S.gam b g) (S.chr b g)

def trTo (b : S.β) (d : S.D b) : (Fr emb σ n → ℂ) ≃ₗ[ℂ] (Fr emb σ n → ℂ) := S.tr emb σ b (S.mv b d)

def rho (b : S.β) : S.G b →* Module.End K (VV K lam) where
  toFun g := ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, Units.val_mul]
    rw [smul_mul_smul_comm]

open Classical in

@[reducible] def fam : GFam K where
  β := S.β
  V := VV K lam
  ιV := VVIdx lam
  bV := bVV K lam
  pair := pairVr emb lam (1 : Matrix (Fin n) (Fin n) E)
  G := S.G
  D := S.D
  ρ := S.rho emb lam
  Nab b d := nabAtr emb lam (S.Lsh b d)
  Del b d := delAtr emb lam (S.Lsh b d)

def Fi : Submodule ℂ (S.Cl → Fr emb σ n → ℂ) where
  carrier := {φ | ∀ c, φ c ∈ ValC (Gr emb σ n) lam ∧ ∀ g : S.Stab c, S.tr emb σ c.1 g.1 (φ c) = φ c}
  add_mem' := by
    intro a b ha hb c
    exact ⟨Submodule.add_mem _ (ha c).1 (hb c).1, fun g => by rw [Pi.add_apply, map_add, (ha c).2 g, (hb c).2 g]⟩
  zero_mem' := fun c => ⟨Submodule.zero_mem _, fun g => map_zero _⟩
  smul_mem' := by
    intro r a ha c
    exact ⟨Submodule.smul_mem _ r (ha c).1, fun g => by rw [Pi.smul_apply, map_smul, (ha c).2 g]⟩

variable (h : (S.fam emb lam).Ok)

@[reducible] def csd : CSD K := (S.fam emb lam).toCSDOf h fun b => ⟨S.rp b, S.rp_spec b⟩

abbrev FormsK : Submodule K (S.Cl → VV K lam) := (S.csd emb lam h).Forms

instance formsModO : Module (𝓞 K) (S.FormsK emb lam h) :=
  (fun C : CSD K => (inferInstance : Module (𝓞 K) C.Forms)) (S.csd emb lam h)

instance formsTow : IsScalarTower (𝓞 K) K (S.FormsK emb lam h) :=
  (fun C : CSD K => (inferInstance : IsScalarTower (𝓞 K) K C.Forms)) (S.csd emb lam h)

def latOf (M : S.Cl → Submodule (𝓞 K) (VV K lam)) : Submodule (𝓞 K) (S.FormsK emb lam h) :=
  { carrier := {x | ∀ c, x.1 c ∈ M c}
    add_mem' := fun ha hb c => (M c).add_mem (ha c) (hb c)
    zero_mem' := fun c => (M c).zero_mem
    smul_mem' := fun r _ ha c => (M c).smul_mem r (ha c) }

@[reducible] def hlat : HLat K where
  V := S.FormsK emb lam h
  ι := Fin (S.csd emb lam h).dim
  b := (S.csd emb lam h).basis
  X := stdFrame (S.csd emb lam h).H
  L := S.latOf emb lam h fun c => delAtr emb lam (S.Lsh c.1 (S.rep c))

def embF : S.FormsK emb lam h →ₛₗ[σ] (S.Cl → Fr emb σ n → ℂ) where
  toFun x c := evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (x.1 c)
  map_add' x y := by funext c; exact map_add (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ) (x.1 c) (y.1 c)
  map_smul' r x := by funext c; exact LinearMap.map_smulₛₗ (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ) r (x.1 c)

end GStep

def ipVal {E K ι : Type} [Field E] [Field K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (lam : ι → DomWeight n) :
    (Fr emb σ n → ℂ) →ₗ⋆[ℂ] (Fr emb σ n → ℂ) →ₗ[ℂ] ℂ := ipFr (Gr emb σ n) lam (fr0 emb σ n)

def shW {N : ℕ} (lam : DomWeight N) (c : ℤ) : DomWeight N where
  w := fun i => lam.w i + c
  anti := by
    intro i j hij
    have h := lam.anti hij
    simp only
    omega

def lamT {R : Ranks} {ι : Type} (hc : ι → HCParam R) (j : ℕ) (τ : ι) : DomWeight (R.N j) :=
  shW (Examples₂.lamOf (hc τ) j) (-((j : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ)))

end GlobalTheory.Mem.Col2

section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix

abbrev Res {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Type := 𝓞 E ⧸ P.asIdeal

instance resField {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Field (Res P) :=
  haveI := P.isMaximal
  Ideal.Quotient.field P.asIdeal

structure TDat {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n)
    (ST : Finset (HeightOneSpectrum (𝓞 E))) where

  N : ∀ b, S.D b → Submodule (𝓞 E) (Fin n → E)

  f : ∀ b, S.D b → ∀ P : ST, (Fin n → E) → Res P.1

  dnN : ∀ b, S.D b → ST → Submodule (𝓞 E) (Fin n → E)

  ker : ∀ b, S.D b → ST → Submodule (𝓞 E) (Fin n → E)

  up : ∀ b, S.D b → ST → (Fin n → E) → S.D b

  dn : ∀ b, S.D b → ∀ P : ST, ((Fin n → E) → Res P.1) → S.D b

  dia : ∀ b, ∀ P : ST, (Res P.1)ˣ → S.D b → S.D b

structure TDat.Ok {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ) : Prop where
  N_lat : ∀ b d, Submodule.IsLattice E (A.N b d)
  dnN_lat : ∀ b d P, Submodule.IsLattice E (A.dnN b d P)
  ker_lat : ∀ b d P, Submodule.IsLattice E (A.ker b d P)
  f_add : ∀ b d P, ∀ x ∈ A.N b d, ∀ y ∈ A.N b d, A.f b d P (x + y) = A.f b d P x + A.f b d P y
  f_smul : ∀ b d (P : ST) (a : 𝓞 E), ∀ x ∈ A.N b d, A.f b d P (a • x) = Ideal.Quotient.mk P.1.asIdeal a * A.f b d P x
  f_ne : ∀ b d P, ∃ x ∈ A.N b d, A.f b d P x ≠ 0
  N_act : ∀ b (g : S.G b) d x, (S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ A.N b (g • d) ↔ x ∈ A.N b d
  f_act : ∀ b (g : S.G b) d P x, A.f b (g • d) P ((S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ x) = A.f b d P x
  te_mem : ∀ b d P, ∀ e ∈ A.N b d, A.f b d P e = 1 → (T : 𝓞 E) • e ∈ A.dnN b d P ∧ (T : 𝓞 E) • e ∉ P.1.asIdeal • A.dnN b d P
  dia_one : ∀ b P d, A.dia b P 1 d = d
  dia_mul : ∀ b P a a' d, A.dia b P (a * a') d = A.dia b P a (A.dia b P a' d)
  dia_act : ∀ b P a (g : S.G b) d, A.dia b P a (g • d) = g • A.dia b P a d
  dia_N : ∀ b P a d, A.N b (A.dia b P a d) = A.N b d
  dia_Lsh : ∀ b P a d, S.Lsh b (A.dia b P a d) = S.Lsh b d
  dia_f : ∀ b P a d x, A.f b (A.dia b P a d) P x = (a : Res P.1) * A.f b d P x

def TDat.deco {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (b : S.β) (d : S.D b) : Deco E n ST ∅ where
  N := A.N b d
  f := A.f b d
  be w := absurd w.2 (Finset.notMem_empty _)

structure TDat.Tied {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ) : Prop where
  ok : ∀ b d, (A.deco b d).Ok
  Lsh_eq : ∀ b d, S.Lsh b d = (A.deco b d).Lsh
  dnN_eq : ∀ b d P, A.dnN b d P = (A.deco b d).dnN P
  ker_eq : ∀ b d P, A.ker b d P = (A.deco b d).LshKer P
  up_deco : ∀ b d P, ∀ x ∈ A.N b d, A.f b d P x = 1 → A.deco b (A.up b d P x) = (A.deco b d).up P (T : 𝓞 E) x
  dn_deco : ∀ b d P g, ((A.deco b d).dn P g).Ok → A.deco b (A.dn b d P g) = (A.deco b d).dn P g
  up_act : ∀ b (γ : S.G b) d P, ∀ x ∈ A.N b d, A.f b d P x = 1 →
    A.up b (γ • d) P ((S.gam b γ : Matrix (Fin n) (Fin n) E) *ᵥ x) = γ • A.up b d P x
  dn_act : ∀ b (γ : S.G b) d P g, ((A.deco b d).dn P g).Ok →
    A.dn b (γ • d) P (fun y => g ((S.gam b γ⁻¹ : Matrix (Fin n) (Fin n) E) *ᵥ y)) = γ • A.dn b d P g
  up_congr : ∀ b d (P : ST) x x', x - x' ∈ P.1.asIdeal • A.N b d → A.up b d P x = A.up b d P x'
  dn_up : ∀ b d P, ∀ x ∈ A.N b d, A.f b d P x = 1 → A.dn b (A.up b d P x) P (A.f b d P) = d

namespace TDat

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST)

abbrev Red (M : Submodule (𝓞 E) (Fin n → E)) (P : HeightOneSpectrum (𝓞 E)) : Type :=
  M ⧸ (P.asIdeal • (⊤ : Submodule (𝓞 E) M))

abbrev lv (P : ST) (c : S.Cl) : Type := Red (A.N c.1 (S.rep c)) P.1

abbrev lk (P : ST) (c : S.Cl) : Type := Red (A.dnN c.1 (S.rep c) P) P.1

open Classical in

def fv (P : ST) (c : S.Cl) : Module.Dual (Res P.1) (A.lv P c) :=
  if h : ∃ φ : Module.Dual (Res P.1) (A.lv P c), ∀ x : A.N c.1 (S.rep c),
    φ (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x then h.choose else 0

open Classical in

def te (T : ℕ) (P : ST) (c : S.Cl) : A.lk P c :=
  if h : ∃ t : A.dnN c.1 (S.rep c) P, ∃ e ∈ A.N c.1 (S.rep c), A.f c.1 (S.rep c) P e = 1 ∧ (t : Fin n → E) = (T : 𝓞 E) • e
  then Submodule.Quotient.mk h.choose else 0

open Classical in

def extF (M : Submodule (𝓞 E) (Fin n → E)) (P : HeightOneSpectrum (𝓞 E)) (g : Module.Dual (Res P) (Red M P))
    (y : Fin n → E) : Res P :=
  if h : ∃ a : Res P, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ z : M, (z : Fin n → E) = s • y ∧
    g (Submodule.Quotient.mk z) = Ideal.Quotient.mk P.asIdeal s * a then h.choose else 0

def upPt (P : ST) (c : S.Cl) (x : A.lv P c) : S.D c.1 :=
  A.up c.1 (S.rep c) P ((Quotient.out x : A.N c.1 (S.rep c)) : Fin n → E)

def dnPt (P : ST) (c : S.Cl) (g : Module.Dual (Res P.1) (A.lk P c)) : S.D c.1 :=
  A.dn c.1 (S.rep c) P (extF _ P.1 g)

def diaPt (P : ST) (a : (Res P.1)ˣ) (c : S.Cl) : S.D c.1 := A.dia c.1 P a (S.rep c)

end TDat

section DGam

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def autO (N : Submodule (𝓞 E) (Sp E n)) : Subgroup (Sp E n ≃ₗ[E] Sp E n) := UF E n ⊓ autLat N

variable (E n) in

def autOrd : Set ℕ :=
  {a | ∃ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N ∧ Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) N ∧ a = Nat.card (autO N)}

def gamRanks (R : Ranks) : Finset ℕ := (Finset.Icc 1 R.m).image R.N ∪ {R.rankX', R.rankY (R.m - 1), R.nV}

variable (E) in

def gamOrd (R : Ranks) : Set ℕ := ⋃ n ∈ gamRanks R, autOrd E n

variable (E) in
open Classical in

def DGam (R : Ranks) : ℕ := if h : (gamOrd E R).Finite then h.toFinset.lcm id else 0

theorem autO_finite (hE : PosStar E) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) : Finite (autO N) :=
  Formalism.HermitianLatticesTheory.final_autFinite E (Sp E n) (hStd E n) hStd_isSymm (hStd_pos hE) N hN

theorem card_autO_gmap {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ UF E n) (N : Submodule (𝓞 E) (Sp E n)) :
    Nat.card (autO (Formalism.HermitianLatticesTheory.gmap g N)) = Nat.card (autO N) := by
  have h : autO (Formalism.HermitianLatticesTheory.gmap g N) = (autO N).map (MulAut.conj g).toMonoidHom := by
    ext γ
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    simp only [autO, Subgroup.mem_inf, mem_autLat]
    refine and_congr ?_ ?_
    · rw [Subgroup.mul_mem_cancel_right _ hg, Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ hg)]
    · rw [gmap_mul, gmap_mul]
      constructor
      · intro h
        rw [h, ← gmap_mul, inv_mul_cancel, gmap_one]
      · intro h
        have h2 := congrArg (Formalism.HermitianLatticesTheory.gmap g) h
        rwa [← gmap_mul, mul_inv_cancel, gmap_one] at h2
  rw [h]
  exact (Nat.card_congr ((autO N).equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).symm

theorem autOrd_finite (hE : PosStar E) (n : ℕ) : (autOrd E n).Finite := by
  obtain ⟨s, -, hs⟩ := unimod_finite hE n
  refine (s.finite_toSet.image fun N => Nat.card (autO N)).subset ?_
  rintro _ ⟨M, h1, h2, rfl⟩
  obtain ⟨N, hN, g, hg, rfl⟩ := hs M h1 h2
  exact ⟨N, hN, (card_autO_gmap hg N).symm⟩

theorem gamOrd_finite (hE : PosStar E) (R : Ranks) : (gamOrd E R).Finite :=
  (gamRanks R).finite_toSet.biUnion fun n _ => autOrd_finite hE n

theorem dvd_DGam (hE : PosStar E) (R : Ranks) (hn : n ∈ gamRanks R) {N : Submodule (𝓞 E) (Sp E n)}
    (h1 : Submodule.IsLattice E N) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) N) : Nat.card (autO N) ∣ DGam E R := by
  unfold DGam
  rw [dif_pos (gamOrd_finite hE R)]
  exact Finset.dvd_lcm (f := id) ((Set.Finite.mem_toFinset _).2 (Set.mem_biUnion hn ⟨N, h1, h2, rfl⟩))

theorem DGam_dvd (hE : PosStar E) (R : Ranks) {M : ℕ} (h : ∀ a ∈ gamOrd E R, a ∣ M) : DGam E R ∣ M := by
  unfold DGam
  rw [dif_pos (gamOrd_finite hE R)]
  exact Finset.lcm_dvd fun a ha => h a ((Set.Finite.mem_toFinset _).1 ha)

theorem DGam_pos (hE : PosStar E) (R : Ranks) : 0 < DGam E R := by
  apply Nat.pos_of_ne_zero
  unfold DGam
  rw [dif_pos (gamOrd_finite hE R), Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨a, ha, h0⟩
  obtain ⟨n, -, N, h1, -, rfl⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset _).1 ha)
  haveI := autO_finite hE h1
  exact Nat.card_pos.ne' h0

theorem N_mem_gamRanks (R : Ranks) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ R.m) : R.N j ∈ gamRanks R :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_Icc.2 ⟨h1, h2⟩))

theorem pred_mem_gamRanks (R : Ranks) : R.N R.m - 1 ∈ gamRanks R := by
  rw [rank_X'_eq]
  exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)

theorem nV_mem_gamRanks (R : Ranks) : R.nV ∈ gamRanks R := Finset.mem_union_right _ (by simp)

end DGam

structure ChainIn (E K ι : Type) [Field E] [NumberField E] [Field K] [Fintype ι] (R : Ranks) where
  S : ∀ i, GStep E K (R.N i)
  rho : ∀ i, (S i).Cl → ℂ
  rho' : ∀ i, (S (i + 1)).Cl → ℂ
  jet : ∀ i, (S i).Cl → (S (i + 1)).Cl → (Pol ℂ ι (R.N i) →ₗ[ℂ] Pol ℂ ι (R.N (i + 1)))

  DG : ℕ

structure ChainIn.Ok {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Fintype ι] {R : Ranks}
    (I : ChainIn E K ι R) : Prop where
  step : ∀ i, (I.S i).Ok
  rho_norm : ∀ i, i < R.m → ∀ c, ‖I.rho i c‖ = 1
  rho'_norm : ∀ i, i < R.m → ∀ c, ‖I.rho' i c‖ = 1
  DG_pos : 0 < I.DG
  dvd_DG : ∀ i, i ≤ R.m → ∀ c, Nat.card ((I.S i).Stab c) ∣ I.DG

theorem N_even (R : Ranks) (j : ℕ) : ∃ a : ℕ, R.N j = 2 * a := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  exact ⟨a + j * (c + 1), by unfold Ranks.N; rw [ha, hc]; ring⟩

theorem floor_sub_half {R : Ranks} (P : HCParam R) (i : Fin R.m) (j : ℕ) :
    ((⌊P.e i - (R.N j : ℚ) / 2⌋ : ℤ) : ℚ) = P.e i - (R.N j : ℚ) / 2 := by
  obtain ⟨z, hz⟩ := P.e_int i
  obtain ⟨a, ha⟩ := N_even R j
  have : P.e i - (R.N j : ℚ) / 2 = ((z - a : ℤ) : ℚ) := by rw [hz, ha]; push_cast; ring
  rw [this, Int.floor_intCast]

namespace ChainIn

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  (I : ChainIn E K ι R) (emb : ι → E →+* K) (σ : K →+* ℂ)

@[reducible] def clFin (h : I.Ok) (i : ℕ) : Fintype (I.S i).Cl :=
  haveI := (h.step i).fin_orb
  Fintype.ofFinite _

def unf (i : ℕ) (c : (I.S i).Cl) (c' : (I.S (i + 1)).Cl) : (Fr emb σ (R.N i) → ℂ) →ₗ[ℂ] (Fr emb σ (R.N (i + 1)) → ℂ) :=
  fnOf (Gr emb σ (R.N (i + 1))) 0 1 ∘ₗ I.jet i c c' ∘ₗ polOf (Gr emb σ (R.N i)) 0 (fr0 emb σ (R.N i))

@[reducible] def chain (h : I.Ok) (hc : ι → HCParam R) : ColumnChain R ι hc where
  cls i := (I.S i).Cl
  clsFin := I.clFin h
  stab i c := (I.S i).Stab c
  stabGrp _ _ := inferInstance
  stabFin i c := (h.step i).fin_stab c.1 _
  DGam := I.DG
  DGam_pos := h.DG_pos
  dvd_DGam := h.dvd_DG
  Y i := Fr emb σ (R.N i)
  de _ y τ := deFr y τ
  de_ne _ y τ := (y.2 τ).ne_zero
  rhoDet := I.rho
  rhoDet' := I.rho'
  rho_norm := h.rho_norm
  rho'_norm := h.rho'_norm
  unf := I.unf emb σ
  sSharp i τ := if hi : i < R.m then ⌊(hc τ).e ⟨i, hi⟩ - (R.N (i + 1) : ℚ) / 2⌋ else 0
  sSharp_eq i hi τ := by rw [dif_pos hi]; exact floor_sub_half _ _ _
  sDiv i τ := if hi : i < R.m then ⌊(hc τ).e ⟨i, hi⟩ - (R.N i : ℚ) / 2⌋ else 0
  sDiv_eq i hi τ := by rw [dif_pos hi]; exact floor_sub_half _ _ _

end ChainIn

def iniH {E : Type} {N n : ℕ} (hN : N = n + 1) (x : Fin N → E) : Fin n → E := fun i => x (Br.iC hN i)

structure PerIn {E K ι : Type} [Field E] [NumberField E] [Field K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) where
  S' : GStep E K (R.N R.m - 1)
  b0 : (I.S R.m).β
  til : ∀ b, S'.D b → (I.S R.m).D b0
  ext : ∀ b, S'.G b →* (I.S R.m).G b0

  sg : ι → DomWeight (R.N R.m - 1)

  tz : E

  H : ∀ b, Subgroup (S'.G b)

structure PerIn.Ok {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Fintype ι] {R : Ranks} {I : ChainIn E K ι R}
    (Q : PerIn I) : Prop where
  step : Q.S'.Ok
  til_smul : ∀ b (g : Q.S'.G b) d, Q.til b (g • d) = Q.ext b g • Q.til b d
  ext_inj : ∀ b, Function.Injective (Q.ext b)
  gam_ini : ∀ b (g : Q.S'.G b) (x : Fin (R.N R.m) → E),
    iniH (N_m_succ R) (((I.S R.m).gam Q.b0 (Q.ext b g) : Matrix (Fin (R.N R.m)) (Fin (R.N R.m)) E) *ᵥ x) =
      (Q.S'.gam b g : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) E) *ᵥ iniH (N_m_succ R) x
  gam_last : ∀ b (g : Q.S'.G b) (x : Fin (R.N R.m) → E),
    (((I.S R.m).gam Q.b0 (Q.ext b g) : Matrix (Fin (R.N R.m)) (Fin (R.N R.m)) E) *ᵥ x) (Br.iL (N_m_succ R)) =
      x (Br.iL (N_m_succ R))
  chr_ext : ∀ b (g : Q.S'.G b), (I.S R.m).chr Q.b0 (Q.ext b g) = Q.S'.chr b g
  tz_ne : Q.tz ≠ 0
  Lsh_til : ∀ b d (x : Fin (R.N R.m) → E), x ∈ (I.S R.m).Lsh Q.b0 (Q.til b d) ↔
    iniH (N_m_succ R) x ∈ Q.S'.Lsh b d ∧ Q.tz * x (Br.iL (N_m_succ R)) ∈ (1 : Submodule (𝓞 E) E)
  rep_til : ∀ b d, ∃ b' d', (I.S R.m).rep ((I.S R.m).cl Q.b0 (Q.til b d)) = Q.til b' d'
  H_idx : ∀ b, (Q.H b).FiniteIndex
  H_rat : ∀ b (g : Q.S'.G b), ∃ h ∈ Q.H b, Q.S'.gam b h = Q.S'.gam b g

namespace PerIn

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  {I : ChainIn E K ι R} (Q : PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ)

def sgT (τ : ι) : DomWeight (R.N R.m - 1) := shW (Q.sg τ) (-((R.m : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ)))

def br (hc : ι → HCParam R) : Pol ℂ ι (R.N R.m) →ₗ[ℂ] Pol ℂ ι (R.N R.m - 1) :=
  (∏ τ, embAt σ emb τ Q.tz ^ (-Br.nBr (lamT hc R.m τ) (Q.sgT τ))) •
    ((VV ℂ Q.sgT).subtype ∘ₗ Br.brStdP (N_m_succ R) (lamT hc R.m) Q.sgT)

def Mt : Submodule ℂ (∀ b, Q.S'.D b → Pol ℂ ι (R.N R.m - 1)) where
  carrier := {F | ∀ b d, F b d ∈ VV ℂ Q.sgT ∧ ∀ g ∈ Q.H b,
    F b (g • d) = (σ (Q.S'.chr b g : K))⁻¹ • rhoP Q.sgT (embGL (embAt σ emb) (Q.S'.gam b g)) (F b d)}
  add_mem' := by
    intro F G hF hG b d
    refine ⟨Submodule.add_mem _ (hF b d).1 (hG b d).1, fun g hg => ?_⟩
    simp only [Pi.add_apply]
    rw [(hF b d).2 g hg, (hG b d).2 g hg, map_add, smul_add]
  zero_mem' := fun b d => ⟨Submodule.zero_mem _, fun g _ => by simp⟩
  smul_mem' := by
    intro r F hF b d
    refine ⟨Submodule.smul_mem _ r (hF b d).1, fun g hg => ?_⟩
    simp only [Pi.smul_apply]
    rw [(hF b d).2 g hg, map_smul, smul_comm]

def rd : Q.Mt emb σ →ₗ[ℂ] (Q.S'.Cl → Pol ℂ ι (R.N R.m - 1)) where
  toFun F c := F.1 c.1 (Q.S'.rep c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[reducible] def clFin (h : Q.Ok) : Fintype Q.S'.Cl :=
  haveI := h.step.fin_orb
  Fintype.ofFinite _

def tilPt (c : Q.S'.Cl) : (I.S R.m).D Q.b0 := Q.til c.1 (Q.S'.rep c)

def tilC (c : Q.S'.Cl) : (I.S R.m).Cl := (I.S R.m).cl Q.b0 (Q.tilPt c)

def wt (c : Q.S'.Cl) : ℂ := ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ)⁻¹

@[reducible] def per (hI : I.Ok) (h : Q.Ok) (hc : ι → HCParam R) : PeriodMap R (I.chain emb σ hI hc) where
  Mt := Q.Mt emb σ
  Wz := Q.S'.Cl → Fr emb σ (R.N R.m) → ℂ
  evz := LinearMap.pi fun c => ((I.S R.m).trTo emb σ Q.b0 (Q.tilPt c)).toLinearMap ∘ₗ LinearMap.proj (Q.tilC c)
  Wrow := Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ
  lowerMap := LinearMap.pi fun c => fnOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) 1 ∘ₗ Q.br emb σ hc ∘ₗ
    polOf (Gr emb σ (R.N R.m)) (shiftOf (lamT hc R.m)) (fr0 emb σ (R.N R.m)) ∘ₗ LinearMap.proj c
  period := letI := Q.clFin h
    ∑ c : Q.S'.Cl, Q.wt c • (pairB (K := ℂ) Q.sgT).compl₁₂
      (polOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) (fr0 emb σ (R.N R.m - 1)) ∘ₗ LinearMap.proj c)
      (LinearMap.proj c ∘ₗ Q.rd emb σ)

def ipP (h : Q.Ok) : (Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) →ₗ⋆[ℂ] (Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) →ₗ[ℂ] ℂ :=
  letI := Q.clFin h
  ∑ c : Q.S'.Cl, Q.wt c • ((ipVal emb σ Q.sgT).comp (LinearMap.proj c)).compl₂ (LinearMap.proj c)

def stabMap (h : Q.Ok) (c : Q.S'.Cl) : Q.S'.Stab c →* (I.S R.m).Stab (Q.tilC c) where
  toFun g := ⟨((I.S R.m).mv Q.b0 (Q.tilPt c))⁻¹ * Q.ext c.1 g.1 * (I.S R.m).mv Q.b0 (Q.tilPt c), by
    have h1 := (I.S R.m).mv_smul Q.b0 (Q.tilPt c)
    have h2 : Q.ext c.1 g.1 • Q.tilPt c = Q.tilPt c := by
      unfold tilPt
      rw [← h.til_smul, g.2]
    show (((I.S R.m).mv Q.b0 (Q.tilPt c))⁻¹ * Q.ext c.1 g.1 * (I.S R.m).mv Q.b0 (Q.tilPt c)) •
      (I.S R.m).rep ((I.S R.m).cl Q.b0 (Q.tilPt c)) = (I.S R.m).rep ((I.S R.m).cl Q.b0 (Q.tilPt c))
    rw [mul_smul, mul_smul, h1, h2, inv_smul_eq_iff, h1]⟩
  map_one' := by
    apply Subtype.ext
    show ((I.S R.m).mv Q.b0 (Q.tilPt c))⁻¹ * Q.ext c.1 1 * (I.S R.m).mv Q.b0 (Q.tilPt c) = (1 : (I.S R.m).G Q.b0)
    simp
  map_mul' a b := by
    apply Subtype.ext
    show ((I.S R.m).mv Q.b0 (Q.tilPt c))⁻¹ * Q.ext c.1 (a.1 * b.1) * (I.S R.m).mv Q.b0 (Q.tilPt c) =
      (((I.S R.m).mv Q.b0 (Q.tilPt c))⁻¹ * Q.ext c.1 a.1 * (I.S R.m).mv Q.b0 (Q.tilPt c) *
      (((I.S R.m).mv Q.b0 (Q.tilPt c))⁻¹ * Q.ext c.1 b.1 * (I.S R.m).mv Q.b0 (Q.tilPt c)) : (I.S R.m).G Q.b0)
    simp [mul_assoc]

theorem stabMap_inj (h : Q.Ok) (c : Q.S'.Cl) : Function.Injective (Q.stabMap h c) := by
  intro a b hab
  have h1 : (((I.S R.m).mv Q.b0 (Q.tilPt c))⁻¹ * Q.ext c.1 a.1 * (I.S R.m).mv Q.b0 (Q.tilPt c) : (I.S R.m).G Q.b0) =
      ((I.S R.m).mv Q.b0 (Q.tilPt c))⁻¹ * Q.ext c.1 b.1 * (I.S R.m).mv Q.b0 (Q.tilPt c) := congrArg Subtype.val hab
  exact Subtype.ext (h.ext_inj _ (mul_left_cancel (mul_right_cancel h1)))

end PerIn

end GlobalTheory.Mem.Col2

end

section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix

structure AtIn {E K ι : Type} [Field E] [NumberField E] [Field K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) where
  T : ℕ
  ST : Finset (HeightOneSpectrum (𝓞 E))
  A : ∀ i, TDat (I.S i) ST
  psi : ∀ P : ST, AddChar (Res P.1) ℂ
  duStar : ℕ
  Dstar : ℝ
  GamP : ℝ

structure AtIn.Ok {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Fintype ι] {R : Ranks} {I : ChainIn E K ι R}
    (J : AtIn I) : Prop where
  T_prime : J.T.Prime
  card_ST : J.ST.card = R.f
  card_res : ∀ P : J.ST, Nat.card (Res P.1) = J.T
  lev : ∀ i, (J.A i).Ok J.T
  tied : ∀ i, (J.A i).Tied J.T
  psi_ne : ∀ P, J.psi P ≠ 1
  free0 : (I.S 0).Free
  duStar_pos : 0 < J.duStar
  Dstar_pos : 0 < J.Dstar
  one_lt_gammaP : 1 < J.GamP

namespace AtIn

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  {I : ChainIn E K ι R} (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ)

def dil (i : ℕ) (P : J.ST) (a : (Res P.1)ˣ) (c : (I.S i).Cl) : (I.S i).Cl := (I.S i).cl c.1 ((J.A i).diaPt P a c)

def dilT (i : ℕ) (P : J.ST) (a : (Res P.1)ˣ) (c : (I.S i).Cl) : (Fr emb σ (R.N i) → ℂ) ≃ₗ[ℂ] (Fr emb σ (R.N i) → ℂ) :=
  (I.S i).trTo emb σ c.1 ((J.A i).diaPt P a c)

def diaLin (P : J.ST) (a : (Res P.1)ˣ) : ((I.S 0).Cl → Fr emb σ (R.N 0) → ℂ) →ₗ[ℂ] ((I.S 0).Cl → Fr emb σ (R.N 0) → ℂ) :=
  LinearMap.pi fun c => (J.dilT emb σ 0 P a c).toLinearMap ∘ₗ LinearMap.proj (J.dil 0 P a c)

def LawDiaOne : Prop := ∀ P, J.diaLin emb σ P 1 = 1

def LawDiaMul : Prop := ∀ P a b, J.diaLin emb σ P (a * b) = J.diaLin emb σ P a * J.diaLin emb σ P b

def LawDiaStable (hc : ι → HCParam R) : Prop :=
  ∀ P a, ((I.S 0).Fi emb σ (lamT hc 0)).map (J.diaLin emb σ P a) ≤ (I.S 0).Fi emb σ (lamT hc 0)

structure Laws (hc : ι → HCParam R) : Prop where
  one : J.LawDiaOne emb σ
  mul : J.LawDiaMul emb σ
  fd : FiniteDimensional ℂ ((I.S 0).Fi emb σ (lamT hc 0))
  stable : J.LawDiaStable emb σ hc

@[reducible] def atT (hI : I.Ok) (h : J.Ok) (hc : ι → HCParam R) (l : J.Laws emb σ hc) : ColumnsAtT R (I.chain emb σ hI hc) where
  T := J.T
  T_prime := h.T_prime
  vT := J.ST
  vTFin := inferInstance
  card_vT := by rw [Fintype.card_coe]; exact h.card_ST
  Fv P := Res P.1
  FvField P := resField P.1
  FvFin P := @Fintype.ofFinite _ (Nat.finite_of_card_ne_zero (by rw [h.card_res P]; exact h.T_prime.ne_zero))
  FvDec P := Classical.decEq _
  card_Fv P := (@Nat.card_eq_fintype_card _ (_)).symm.trans (h.card_res P)
  psiT := J.psi
  psiT_ne := h.psi_ne
  rhoT P := { toFun := J.diaLin emb σ P, map_one' := l.one P, map_mul' := l.mul P }
  Mu0 := (I.S 0).Fi emb σ (lamT hc 0)
  Mu0_fd := l.fd
  Mu0_stable := l.stable
  duStar := J.duStar
  duStar_pos := h.duStar_pos
  Dstar := J.Dstar
  Dstar_pos := h.Dstar_pos
  GamP := J.GamP
  one_lt_gammaP := h.one_lt_gammaP

end AtIn

namespace GStep

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok)

def LawGood : Prop := (S.hlat emb lam h).Good

def LawBasis : Prop :=
  LinearIndependent ℂ (fun a => S.embF emb σ lam h ((S.hlat emb lam h).b a)) ∧
    Submodule.span ℂ (Set.range (fun a => S.embF emb σ lam h ((S.hlat emb lam h).b a))) = S.Fi emb σ lam

def LawNorm [Fintype S.Cl] : Prop := ∀ x : (S.hlat emb lam h).V,
  (Formalism.HermitianLatticesTheory.majAt (S.hlat emb lam h).b (S.hlat emb lam h).X (InfinitePlace.mk σ) x x).re =
    (∑ c : S.Cl, ((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹ * ipVal emb σ lam (S.embF emb σ lam h x c) (S.embF emb σ lam h x c)).re

end GStep

namespace TDat

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST)

set_option maxHeartbeats 1600000 in

structure Laws (T : ℕ) : Prop where
  lv_rank : ∀ P c, Module.finrank (Res P.1) (A.lv P c) = n
  lk_rank : ∀ P c, Module.finrank (Res P.1) (A.lk P c) = n
  fv_ne : ∀ P c, A.fv P c ≠ 0
  te_ne : ∀ P c, A.te T P c ≠ 0
  dil_one : ∀ P c, S.cl c.1 (A.diaPt P 1 c) = c
  dil_mul : ∀ P a b c, S.cl c.1 (A.diaPt P (a * b) c) = S.cl c.1 (A.diaPt P a (S.cl c.1 (A.diaPt P b c)))
  dil_fv : ∀ P a c, ∃ e : A.lv P (S.cl c.1 (A.diaPt P a c)) ≃ₗ[Res P.1] A.lv P c,
    ∀ x, A.fv P (S.cl c.1 (A.diaPt P a c)) x = (a : Res P.1) * A.fv P c (e x)
  dil_stab : ∀ P a c, Nat.card (S.Stab (S.cl c.1 (A.diaPt P a c))) = Nat.card (S.Stab c)

end TDat

structure PerIn.Over {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Fintype ι] {R : Ranks}
    {I : ChainIn E K ι R} (Q : PerIn I) (J : AtIn I) : Prop where
  norm_tz : star Q.tz * Q.tz = (J.T : E)
  N_til : ∀ b d (x : Fin (R.N R.m) → E), x ∈ (J.A R.m).N Q.b0 (Q.til b d) ↔
    iniH (N_m_succ R) x ∈ Q.S'.Lsh b d ∧ x (Br.iL (N_m_succ R)) ∈ (1 : Submodule (𝓞 E) E)
  f_til : ∀ b d (P : J.ST), ∀ x ∈ (J.A R.m).N Q.b0 (Q.til b d),
    (J.A R.m).f Q.b0 (Q.til b d) P x = redP P.1 (Q.tz * x (Br.iL (N_m_succ R)))

structure FmIn {E K ι : Type} [Field E] [NumberField E] [Field K] [Fintype ι] {R : Ranks} {I : ChainIn E K ι R}
    (J : AtIn I) (Pl : Rows.Places K) where
  tauOf : Pl.Pl → (J.ST ≃ ι)
  seenP : Pl.Pl → Bool
  beOn : ι → ℝ
  beOn_nonneg : ∀ τ, 0 ≤ beOn τ
  thFree : ∀ i, (K →+* ℂ) → (I.S i).Cl → (I.S (i + 1)).Cl → ℝ
  thFree_nonneg : ∀ i s c c', 0 ≤ thFree i s c c'

section Forms

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  {I : ChainIn E K ι R} (J : AtIn I) (Q : PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R)

def BLat (i : ℕ) (hF : ((I.S i).fam emb (lamT hc i)).Ok) (P : J.ST) : Submodule (𝓞 K) ((I.S i).hlat emb (lamT hc i) hF).V :=
  (I.S i).latOf emb (lamT hc i) hF fun c => delAtr emb (lamT hc i) ((J.A i).ker c.1 ((I.S i).rep c) P)

structure FmLaws (Pl : Rows.Places K) (hI : I.Ok) (hQ : Q.Ok) : Prop where
  fam : ∀ i, ((I.S i).fam emb (lamT hc i)).Ok
  famP : (Q.S'.fam emb Q.sgT).Ok
  lev : ∀ i, (J.A i).Laws J.T
  good : ∀ i, (I.S i).LawGood emb (lamT hc i) (fam i)
  basis : ∀ i, (I.S i).LawBasis emb σ (lamT hc i) (fam i)
  norm : ∀ i, letI := I.clFin hI i; (I.S i).LawNorm emb σ (lamT hc i) (fam i)
  goodP : Q.S'.LawGood emb Q.sgT famP
  basisP : Q.S'.LawBasis emb σ Q.sgT famP
  normP : letI := Q.clFin hQ; Q.S'.LawNorm emb σ Q.sgT famP
  dia_lat : ∀ P a x, x ∈ ((I.S 0).hlat emb (lamT hc 0) (fam 0)).L → ∃ y ∈ ((I.S 0).hlat emb (lamT hc 0) (fam 0)).L,
    (I.S 0).embF emb σ (lamT hc 0) (fam 0) y = J.diaLin emb σ P a ((I.S 0).embF emb σ (lamT hc 0) (fam 0) x)
  B_span : ∀ i (w : Pl.Pl) P, Submodule.span K
    (locW Pl w (BLat J emb hc i (fam i) P) : Set ((I.S i).hlat emb (lamT hc i) (fam i)).V) = ⊤

set_option maxHeartbeats 1600000 in

def forms {Pl : Rows.Places K} (Z : FmIn J Pl) (hI : I.Ok) (hJ : J.Ok) (hQ : Q.Ok) (l : J.Laws emb σ hc)
    (lf : FmLaws J Q emb σ hc Pl hI hQ) (_hT : Q.Over J) :
    MemberForms K σ Pl ι hc (I.chain emb σ hI hc) (J.atT emb σ hI hJ hc l) (Q.per emb σ hI hQ hc) where
  lv i P c := (J.A i).lv P c
  lvAcg _ _ _ := inferInstance
  lvMod _ _ _ := inferInstance
  lv_rank i := (lf.lev i).lv_rank
  fv i P c := (J.A i).fv P c
  fv_ne i := (lf.lev i).fv_ne
  up i P c x := (I.S i).cl c.1 ((J.A i).upPt P c x)
  upT i P c x := (I.S i).trTo emb σ c.1 ((J.A i).upPt P c x)
  lk i P c := (J.A i).lk P c
  lkAcg _ _ _ := inferInstance
  lkMod _ _ _ := inferInstance
  lk_rank i := (lf.lev i).lk_rank
  te i P c := (J.A i).te J.T P c
  te_ne i := (lf.lev i).te_ne
  dn i P c g := (I.S i).cl c.1 ((J.A i).dnPt P c g)
  dnT i P c g := (I.S i).trTo emb σ c.1 ((J.A i).dnPt P c g)
  dil := J.dil
  dilT := J.dilT emb σ
  dil_one i := (lf.lev i).dil_one
  dil_mul i := (lf.lev i).dil_mul
  dil_fv i P a c := by
    obtain ⟨e, he⟩ := (lf.lev i).dil_fv P a c
    exact ⟨e, LinearMap.ext he⟩
  dil_stab i := (lf.lev i).dil_stab
  rhoT_dil _ _ _ _ := rfl
  tauOf := Z.tauOf
  seenP := Z.seenP
  lam j τ := Examples₂.lamOf (hc τ) j
  lam_eq j hj τ i := Examples₂.lamOf_eq (hc τ) j hj i
  sg := Q.sg
  Fi i := (I.S i).Fi emb σ (lamT hc i)
  Fi_zero := rfl
  ipV i _ := ipVal emb σ (lamT hc i)
  lat i := (I.S i).hlat emb (lamT hc i) (lf.fam i)
  lat_good := lf.good
  emb i := (I.S i).embF emb σ (lamT hc i) (lf.fam i)
  emb_basis := lf.basis
  emb_norm := lf.norm
  rhoT_lat := lf.dia_lat
  Bw i w P := locW Pl w (BLat J emb hc i (lf.fam i) P)
  Bw_span := lf.B_span
  clsP := Q.S'.Cl
  clsPFin := Q.clFin hQ
  stabilizer₂ c := Q.S'.Stab c
  stabPGrp _ := inferInstance
  stabPFin c := hQ.step.fin_stab c.1 _
  til := Q.tilC
  stabMap := Q.stabMap hQ
  stabMap_inj := Q.stabMap_inj hQ
  evz_til φ ψ h := by
    funext c
    show (I.S R.m).trTo emb σ Q.b0 (Q.tilPt c) (φ (Q.tilC c)) = (I.S R.m).trTo emb σ Q.b0 (Q.tilPt c) (ψ (Q.tilC c))
    rw [h c]
  ptC := Q.S'.Fi emb σ Q.sgT
  ipP := Q.ipP emb σ hQ
  ptLat := Q.S'.hlat emb Q.sgT lf.famP
  ptLat_good := lf.goodP
  ptEmb := Q.S'.embF emb σ Q.sgT lf.famP
  ptEmb_basis := lf.basisP
  ptEmb_norm x := by
    refine (lf.normP x).trans ?_
    congr 1
    simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rfl
  beOn := Z.beOn
  beOn_nonneg := Z.beOn_nonneg
  thFree := Z.thFree
  thFree_nonneg := Z.thFree_nonneg

end Forms

end GlobalTheory.Mem.Col2

end

section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

section Steps

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

structure Ys (X : Fields) (n : ℕ) where
  ys : Submodule (𝓞 X.E) (Sp X.E n) → Set (Set (Sp X.E n))
  equiv : ∀ N (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) Y, (fun v => γ v) '' Y ∈ ys (Formalism.HermitianLatticesTheory.gmap γ N) ↔ Y ∈ ys N

def Ys.triv (X : Fields) (n : ℕ) : Ys X n where
  ys _ := {∅}
  equiv N γ Y := by simp

def Ys.Off (y : Ys X n) (P : HeightOneSpectrum (𝓞 X.E)) : Prop :=
  ∀ N N' : Submodule (𝓞 X.E) (Sp X.E n), (∀ w : HeightOneSpectrum (𝓞 X.E), w ≠ P → w ≠ conjPrime₂ P →
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N) → y.ys N' = y.ys N

variable (ST SG Q) in

def PtY (y : Ys X n) : Type := {p : DecoF X.E n ST SG Q × Set (Sp X.E n) // p.2 ∈ y.ys p.1.deco.1.N}

@[reducible] def ptYAct (y : Ys X n) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) :
    MulAction (FrmG Λ Θ) (PtY ST SG Q y) where
  smul g p := ⟨(FrmG.incl Λ Θ g • p.1.1, (fun v => g.1.1 v) '' p.1.2), (y.equiv p.1.1.deco.1.N g.1.1 p.1.2).2 p.2⟩
  one_smul p := Subtype.ext (Prod.ext (by
    show FrmG.incl Λ Θ 1 • p.1.1 = p.1.1
    rw [map_one, one_smul]) (Set.image_id p.1.2))
  mul_smul g h p := Subtype.ext (Prod.ext (by
    show FrmG.incl Λ Θ (g * h) • p.1.1 = FrmG.incl Λ Θ g • FrmG.incl Λ Θ h • p.1.1
    rw [map_mul, mul_smul]) (Set.image_image (fun v => g.1.1 v) (fun v => h.1.1 v) p.1.2).symm)

open Classical in

def prefRep {G D : Type} [Group G] [MulAction G D] (pref : D → Prop) (q : MulAction.orbitRel.Quotient G D) : D :=
  if h : ∃ p, Quotient.mk (MulAction.orbitRel G D) p = q ∧ pref p then h.choose else Quotient.out q

theorem prefRep_spec {G D : Type} [Group G] [MulAction G D] (pref : D → Prop) (q : MulAction.orbitRel.Quotient G D) :
    Quotient.mk (MulAction.orbitRel G D) (prefRep pref q) = q := by
  unfold prefRep
  split_ifs with h
  · exact h.choose_spec.1
  · exact Quotient.out_eq q

variable (ST) in

@[reducible] def stepY (y : Ys X n) (β : Type) [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG)
    (Θ : β → LevQFam X.E X.K n Q) (pref : DecoF X.E n ST SG Q → Prop) : GStep X.E X.K n where
  β := β
  G b := FrmG (Λ b) (Θ b)
  D _ := PtY ST SG Q y
  actD b := ptYAct y (Λ b) (Θ b)
  gam _ := (ufGL X.E n).comp (MonoidHom.fst _ _)
  chr b := ((Λ b).chr.comp ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _))) *
    ((Θ b).chr.comp ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _)))
  Lsh _ p := p.1.1.deco.1.Lsh
  rp b := @prefRep _ _ _ (ptYAct y (Λ b) (Θ b)) fun p => pref p.1.1
  rp_spec b := @prefRep_spec _ _ _ (ptYAct y (Λ b) (Θ b)) fun p => pref p.1.1

open Classical in

def PtY.mv {y : Ys X n} (p : PtY ST SG Q y) (d : DecoSet X.E n ST SG) : PtY ST SG Q y :=
  if h : (∀ (P : Q) (x : Sp X.E n), p.1.1.1.2 P x ∈ d.1.at P.1 ↔ x ∈ stdAt X.E n P.1) ∧ p.1.2 ∈ y.ys d.1.N
  then ⟨(⟨(d, p.1.1.1.2), h.1⟩, p.1.2), h.2⟩ else p

variable (ST) in

def tdatY (T : ℕ) (y : Ys X n) (β : Type) [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG)
    (Θ : β → LevQFam X.E X.K n Q) (pref : DecoF X.E n ST SG Q → Prop) : TDat (stepY ST y β Λ Θ pref) ST where
  N _ p := p.1.1.deco.1.N
  f _ p P := p.1.1.deco.1.f P
  dnN _ p P := p.1.1.deco.1.dnN P
  ker _ p P := p.1.1.deco.1.LshKer P
  up _ p P x := p.mv (p.1.1.deco.up P (T : 𝓞 X.E) x)
  dn _ p P g := p.mv (p.1.1.deco.dn P g)
  dia _ P a p := p.mv (DecoSet.dia1 P a p.1.1.deco)

end Steps

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

structure TopLev (X : Fields) (Pr : Primes X) (R : Ranks) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) where
  levG : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs
  levQ : ∀ j, LevQFam X.E X.K (R.N j) Q

  pref : ∀ u j, DecoF X.E (R.N j) (Pr.vT u) Pr.vGs Q → Prop

structure TopLev.Ok {X : Fields} {Pr : Primes X} {R : Ranks} {Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (Tp : TopLev X Pr R Q) : Prop where
  idx : ∀ j P, (Tp.levQ j P).H.FiniteIndex
  root : ∀ j P g, ∃ m : ℕ, 0 < m ∧ (Tp.levQ j P).lam g ^ m = 1
  levG_top : (Tp.levG R.m).grp ≤ (extGH (N_m_succ R)).range
  levQ_last : ∀ P, ∀ κ ∈ (Tp.levQ R.m P).H, ∀ x ∈ stdAt X.E (R.N R.m) P.1,
    redP P.1 (κ.1 x (Br.iL (N_m_succ R))) = redP P.1 (x (Br.iL (N_m_succ R)))
  levQ_ini : ∀ P, ∀ κ ∈ (Tp.levQ R.m P).H, ∀ i,
    redP P.1 (κ.1 (Pi.single (Br.iL (N_m_succ R)) 1) (Br.iC (N_m_succ R) i)) = 0
  pref_off : ∀ u j, j ≠ R.m → ∀ p, Tp.pref u j p
  pref_top : ∀ u p, Tp.pref u R.m p → ∃ d, p.deco = DecoSet.tilH (N_m_succ R) (Pr.piT u) d

variable (R) in
open Classical in

def ysAt (j : ℕ) : Ys X (R.N j) :=
  if j + 1 = R.m then ⟨ybSet sel mu cst, fun N γ Y => ybSet_gmap sel mu cst N γ Y⟩ else Ys.triv X _

def Idx (j : ℕ) : Type := {b : Option (L.β j) // b.isSome ↔ j < R.m}

instance (j : ℕ) : Fintype (Idx sel mu L j) := by unfold Idx; exact Fintype.ofFinite _
instance (j : ℕ) : DecidableEq (Idx sel mu L j) := Classical.decEq _

variable (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def levGAt (j : ℕ) (b : Idx sel mu L j) : LevFam X.E X.K (R.N j) Pr.vGs := b.1.elim (Tp.levG j) (L.levG j)

def levQAt (j : ℕ) (b : Idx sel mu L j) : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)) :=
  b.1.elim (Tp.levQ j) (L.levQ j)

@[reducible] def stepAt (u : Pr.Word) (j : ℕ) : GStep X.E X.K (R.N j) :=
  stepY (Pr.vT u) (ysAt R sel mu cst j) (Idx sel mu L j) (levGAt sel mu L Tp j) (levQAt sel mu L Tp j) (Tp.pref u j)

def tdatAt (u : Pr.Word) (j : ℕ) : TDat (stepAt sel mu cst L Tp u j) (Pr.vT u) :=
  tdatY (Pr.vT u) (Pr.T u) (ysAt R sel mu cst j) (Idx sel mu L j) (levGAt sel mu L Tp j) (levQAt sel mu L Tp j) (Tp.pref u j)

def chainAt (u : Pr.Word)
    (rho : ∀ i (b : Idx sel mu L i), (stepAt sel mu cst L Tp u i).D b → ℂ)
    (rho' : ∀ i (b : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u (i + 1)).D b → ℂ) (cD : X.Tau → ℂ)
    (Th : ∀ i (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u i).D b →
      (stepAt sel mu cst L Tp u (i + 1)).D b' → Formalism.L2.Ker.VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ) :
    ChainIn X.E X.K X.Tau R where
  S := stepAt sel mu cst L Tp u
  rho i c := rho i c.1 (GStep.rep _ c)
  rho' i c := rho' i c.1 (GStep.rep _ c)
  jet i c c' := Formalism.L2.Ker.jetMap (Formalism.L2.Ker.jetC cD (Th i c.1 c'.1 (GStep.rep _ c) (GStep.rep _ c'))) 0
  DG := DGam X.E R

end Chain

end GlobalTheory.Mem.Col2

end
