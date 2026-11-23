import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriMembership

variable {D : D7}

section Local

variable (D) in

abbrev Oh : Subring (Datum.EAf D) := Formalism.L2.Herm.intAf D.host.F D.host.E

def InI (I : Ideal (𝓞 D.host.E)) (z : Datum.EAf D) : Prop := ∃ h : z ∈ Oh D, (⟨z, h⟩ : Oh D) ∈ idS D.host.F I

def InIinv (I : Ideal (𝓞 D.host.E)) (z : Datum.EAf D) : Prop := ∀ a ∈ I, eToEAf D (a : D.host.E) * z ∈ Oh D

def absF (z : (AE D)ˣ) : ℝ :=
  Datum.volRel ((Oh D).toAddSubgroup.map (AddMonoidHom.mulLeft (toEAf D (z : AE D)))) (Oh D).toAddSubgroup

variable (e : AE D) (I : Ideal (𝓞 D.host.E)) (ν : (AE D)ˣ →* Circle)

def InHalf {p q : ℕ} (x : Matrix (Fin p) (Fin q) (Datum.EAf D)) : Prop := ∀ i j, toEAf D e * x i j = x i j

def AtE {n : ℕ} (g : GL (Fin n) (AE D)) : Prop := ∀ i j, e * (g.1 - 1) i j = (g.1 - 1) i j

def InK {n : ℕ} (g : GL (Fin n) (AE D)) : Prop := AtE e g ∧ ∀ i j, InI I (toEAf D ((g.1 - 1) i j))

def weight (d : ℕ) {n : ℕ} (g : GL (Fin n) (AE D)) : ℂ :=
  let z : (AE D)ˣ := Matrix.GeneralLinearGroup.det g
  (ν z : ℂ) * Complex.ofReal (Real.sqrt (absF z) ^ d)

variable {a a' d₁ d₂ : ℕ}

def IsZeta (Ψ : Matrix (Fin a') (Fin d₁) (Datum.EAf D) → Matrix (Fin a') (Fin d₂) (Datum.EAf D) → ℂ)
    (y₁ : Matrix (Fin a') (Fin d₁) (Datum.EAf D)) (y₂ : Matrix (Fin a') (Fin d₂) (Datum.EAf D)) (s : ℂ) : Prop :=
  ∃ Rp : Set (GL (Fin a') (AE D)), (∀ r ∈ Rp, AtE e r) ∧ (∀ g, AtE e g → ∃! r, r ∈ Rp ∧ InK e I (g * r⁻¹)) ∧
    HasSum (fun r : Rp => weight ν (d₁ + d₂) r.1 * Ψ (HMul.hMul (r.1.1.map (toEAf D)) y₁) (HMul.hMul (r.1.1.map (toEAf D)) y₂)) s

def IsPrim (x₁ : Matrix (Fin d₁) (Fin a) (Datum.EAf D)) (x₂ : Matrix (Fin d₂) (Fin a) (Datum.EAf D)) : Prop :=
  IsIntM x₁ ∧ (∀ i j, InIinv I (x₂ i j)) ∧
    ∃ (z₁ : Matrix (Fin a) (Fin d₁) (Datum.EAf D)) (z₂ : Matrix (Fin a) (Fin d₂) (Datum.EAf D)),
      IsIntM z₁ ∧ (∀ i j, InI I (z₂ i j)) ∧ z₁ * x₁ + z₂ * x₂ = toEAf D e • (1 : Matrix (Fin a) (Fin a) (Datum.EAf D))

def HasDepth (Ψ : Matrix (Fin a') (Fin d₁) (Datum.EAf D) → Matrix (Fin a') (Fin d₂) (Datum.EAf D) → ℂ) : Prop :=
  ∀ y₁ y₂, InHalf e y₁ → InHalf e y₂ →
    (Ψ y₁ y₂ ≠ 0 → (∀ i j, InIinv I (y₁ i j)) ∧ IsIntM y₂) ∧
    ∀ u₁ u₂, InHalf e u₁ → InHalf e u₂ → IsIntM u₁ → (∀ i j, InI I (u₂ i j)) → Ψ (y₁ + u₁) (y₂ + u₂) = Ψ y₁ y₂

variable (hd : a + a' = d₁ + d₂) (h : GL (Fin (d₁ + d₂)) (AE D))

def xTop : Matrix (Fin d₁) (Fin a) (Datum.EAf D) :=
  Matrix.of fun i p => toEAf D (e * (h⁻¹).1 (Fin.castAdd d₂ i) (Fin.cast hd (Fin.castAdd a' p)))

def xBot : Matrix (Fin d₂) (Fin a) (Datum.EAf D) :=
  Matrix.of fun i p => toEAf D (e * (h⁻¹).1 (Fin.natAdd d₁ i) (Fin.cast hd (Fin.castAdd a' p)))

def yLeft : Matrix (Fin a') (Fin d₁) (Datum.EAf D) :=
  Matrix.of fun q i => toEAf D (e * h.1 (Fin.cast hd (Fin.natAdd a q)) (Fin.castAdd d₂ i))

def yRight : Matrix (Fin a') (Fin d₂) (Datum.EAf D) :=
  Matrix.of fun q i => toEAf D (e * h.1 (Fin.cast hd (Fin.natAdd a q)) (Fin.natAdd d₁ i))

def LocFlip (n : ℕ) (Ψ : Matrix (Fin a') (Fin d₁) (Datum.EAf D) → Matrix (Fin a') (Fin d₂) (Datum.EAf D) → ℂ)
    (Φ : Matrix (Fin d₁) (Fin a) (Datum.EAf D) → Matrix (Fin d₂) (Fin a) (Datum.EAf D) → ℂ) : Prop :=
  ∃ hd : a + a' = d₁ + d₂, n ≠ 0 ∧ HasDepth e I Ψ ∧
    (∀ h, AtE e h → IsPrim e I (xTop e hd h) (xBot e hd h) →
      ∃ s, IsZeta e I ν Ψ (yLeft e hd h) (yRight e hd h) s ∧
        Φ (xTop e hd h) (xBot e hd h) = weight ν (d₁ + d₂) h * ((n : ℂ)⁻¹ * s)) ∧
    ∀ x₁ x₂, InHalf e x₁ → InHalf e x₂ → ¬ IsPrim e I x₁ x₂ → Φ x₁ x₂ = 0

end Local

section Models

variable (ψ : AddChar (AF D.host.F) ℂ)

open Classical in

def IsDatOwn (ε : Bool) (S T : Node D) (e : AE D) (f₀ : WO S.V T.V → ℂ)
    (φ : Matrix (Fin T.V.rank) (Fin S.V.rank) (Datum.EAf D) → ℂ) (f : WO S.V T.V → ℂ) : Prop :=
  IsSBHalf e (latO (sgn ε S.V) T.V S.Λ T.Λ fun _ => True)
      (fun x : WO S.V T.V => if IsHalf e x then φ (frMapO S.V T.V S.β T.β x) else 0) ∧
    IsThetaAt ψ (symplO (sgn ε S.V) T.V) (heisO ψ (sgn ε S.V) T.V) e (latO (sgn ε S.V) T.V S.Λ T.Λ fun _ => True) 1 f₀
      (fun x : WO S.V T.V => if IsHalf e x then φ (frMapO S.V T.V S.β T.β x) else 0) f

open Classical in

def IsDatDual (S T : Node D) (e : AE D) (f₀ : WO S.V T.V → ℂ)
    (φ : Matrix (Fin S.V.rank) (Fin T.V.rank) (Datum.EAf D) → ℂ) (f : WO S.V T.V → ℂ) : Prop :=
  IsSBHalf (cA D e) (latO S.V T.V S.Λ T.Λ fun _ => True)
      (fun x : WO S.V T.V => if IsHalf (cA D e) x then φ (frMapAdj S.V T.V S.β T.β x) else 0) ∧
    IsThetaAt ψ (symplO S.V T.V) (heisO ψ S.V T.V) (cA D e) (latO S.V T.V S.Λ T.Λ fun _ => True) 1 f₀
      (fun x : WO S.V T.V => if IsHalf (cA D e) x then φ (frMapAdj S.V T.V S.β T.β x) else 0) f

end Models

section Grid

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)

abbrev DX (i j : ℕ) : Type := WO (G.V (i + 1) j).V (G.V i j).V → ℂ

abbrev DT (i j : ℕ) : Type := WO (G.V i j).V (G.V i (j + 1)).V → ℂ

open Classical in

def places (t : T) : Finset (Pl D.host.E) := G.toPlaceDat.W R.Pg ∪ R.Q t

open Classical in

def depth (t : T) : Ideal (𝓞 D.host.E) := G.lvl R * ∏ w ∈ R.Q t \ G.toPlaceDat.W R.Pg, w.asIdeal

def nu (t : T) (i j : ℕ) : (AE D)ˣ →* Circle := R.toLevCh.mu t (j + 1) / G.chi (D.R.m - i)

def levIdx (t : T) : ℕ → ℕ → ℕ
  | i, 0 => ((G.V i 0).princ (depth G t)).relIndex ((G.V i 0).princ (G.lvl R))
  | 0, j + 1 => ((nodeY R (j + 1)).princ (depth G t)).relIndex
      (lev D.sp.cm (Yc D (j + 1)).gram (R.βY (j + 1)) (R.datYt t (j + 1) R.triv))
  | i + 1, j + 1 => ((G.V (i + 1) (j + 1)).princ (depth G t)).relIndex ((G.V (i + 1) (j + 1)).princ ⊤)

def SqFlip (t : T) (i j : ℕ) {nb na : ℕ} (b : Fin nb → DT G i j × DX G i j) (a : Fin na → DX G i (j + 1) × DT G (i + 1) j) : Prop :=
  ∃ e, IsIdemSum e (places G t) ∧ ∃ (β₁ : Fin nb → _) (β₂ : Fin nb → _) (α₁ : Fin na → _) (α₂ : Fin na → _),
    (∀ k, IsDatDual R.ψ (G.V i j) (G.V i (j + 1)) e (G.th t i j).vac (β₁ k) (b k).1) ∧
    (∀ k, IsDatOwn R.ψ true (G.V (i + 1) j) (G.V i j) e (G.X i j).vac (β₂ k) (b k).2) ∧
    (∀ k, IsDatOwn R.ψ true (G.V (i + 1) (j + 1)) (G.V i (j + 1)) e (G.X i (j + 1)).vac (α₁ k) (a k).1) ∧
    (∀ k, IsDatDual R.ψ (G.V (i + 1) j) (G.V (i + 1) (j + 1)) e (G.th t (i + 1) j).vac (α₂ k) (a k).2) ∧
    LocFlip e (depth G t) (nu G t i j) (levIdx G t i j) (fun y₁ y₂ => ∑ k, β₁ k y₁ * β₂ k y₂) fun x₁ x₂ => ∑ k, α₁ k x₁ * α₂ k x₂

def IsSqConst (c : T → ℕ → ℕ → ℂ) : Prop :=
  ∀ t i j, i < D.R.m → j < D.R.m → c t i j ≠ 0 ∧
    ∀ (nb na : ℕ) (b : Fin nb → DT G i j × DX G i j) (a : Fin na → DX G i (j + 1) × DT G (i + 1) j), SqFlip G t i j b a →
      ∑ k, G.ioT t (i + 1) j (a k).2 ∘ₗ G.ioX t i (j + 1) (a k).1 = c t i j • ∑ k, G.ioX t i j (b k).2 ∘ₗ G.ioT t i j (b k).1

variable (D) in

def cTot (c : T → ℕ → ℕ → ℂ) (t : T) : ℂ := ∏ i ∈ Finset.range D.R.m, ∏ j ∈ Finset.range D.R.m, c t i j

structure Pt where

  X : ∀ i j, WO (G.V (i + 1) j).V (G.V i j).V

  th : ∀ i j, WO (G.V i j).V (G.V i (j + 1)).V

variable {G} in

def Pt.AgreeOff (i j : ℕ) (p q : Pt G) : Prop :=
  (∀ i' j', ¬ (i' = i ∧ (j' = j ∨ j' = j + 1)) → p.X i' j' = q.X i' j') ∧
    ∀ i' j', ¬ (j' = j ∧ (i' = i ∨ i' = i + 1)) → p.th i' j' = q.th i' j'

def StepFlip (t : T) (i j : ℕ) (τ τ' : Pt G → ℂ) : Prop :=
  ∀ p : Pt G, ∃ (nb na : ℕ) (b : Fin nb → DT G i j × DX G i j) (a : Fin na → DX G i (j + 1) × DT G (i + 1) j),
    SqFlip G t i j b a ∧ ∀ q : Pt G, Pt.AgreeOff i j p q →
      τ q = ∑ k, (b k).1 (q.th i j) * (b k).2 (q.X i j) ∧ τ' q = ∑ k, (a k).1 (q.X i (j + 1)) * (a k).2 (q.th (i + 1) j)

def givenFin (t : T) (Φ : G.Data R) (p : Pt G) : ℂ :=
  (∏ j ∈ Finset.range D.R.m, datum0 R t j (p.th 0 j)) * ∏ i ∈ Finset.range D.R.m, G.datum Φ i (p.X i 0)

abbrev OppFin : Type := (∀ i, DX G i D.R.m) × ∀ j, DT G D.R.m j

def oppFin {n : ℕ} (Tf : Fin n → OppFin G) (p : Pt G) : ℂ :=
  ∑ k, (∏ i ∈ Finset.range D.R.m, (Tf k).1 i (p.X i D.R.m)) * ∏ j ∈ Finset.range D.R.m, (Tf k).2 j (p.th D.R.m j)

def IsFlipped (t : T) (Φ : G.Data R) {n : ℕ} (Tf : Fin n → OppFin G) : Prop :=
  (∀ k i, i < D.R.m → IsFinVec R.ψ R.θ true (G.V (i + 1) D.R.m) (G.V i D.R.m) ((Tf k).1 i)) ∧
  (∀ k j, j < D.R.m → IsFinVec R.ψ R.θ false (G.V D.R.m j) (G.V D.R.m (j + 1)) ((Tf k).2 j)) ∧
  ∃ τ : ℕ → Pt G → ℂ, τ 0 = givenFin G t Φ ∧ τ (D.R.m * D.R.m) = oppFin G Tf ∧
    ∀ s, s < D.R.m * D.R.m → StepFlip G t (s / D.R.m) (s % D.R.m) (τ s) (τ (s + 1))

def rowVec (t : T) (i : ℕ) (P : ∀ j, Pol (G.V i j) (G.V i (j + 1))) (n : ℕ) : SmT (G.V i n).M →ₗ[ℂ] SmT (G.V i 0).M :=
  Nat.rec (motive := fun n => SmT (G.V i n).M →ₗ[ℂ] SmT (G.V i 0).M) LinearMap.id (fun n L => L ∘ₗ (G.th t i n).It (P n)) n

def colVec (j : ℕ) (P : ∀ i, Pol (G.V (i + 1) j) (G.V i j)) (n : ℕ) : SmT (G.V 0 j).M →ₗ[ℂ] SmT (G.V n j).M :=
  Nat.rec (motive := fun n => SmT (G.V 0 j).M →ₗ[ℂ] SmT (G.V n j).M) LinearMap.id (fun n L => (G.X n j).It (P n) ∘ₗ L) n

abbrev GivenInf : Type := (∀ j, Pol (G.V 0 j) (G.V 0 (j + 1))) × ∀ i, Pol (G.V (i + 1) 0) (G.V i 0)

abbrev OppInf : Type := (∀ i, Pol (G.V (i + 1) D.R.m) (G.V i D.R.m)) × ∀ j, Pol (G.V D.R.m j) (G.V D.R.m (j + 1))

def thDn (t : T) (x : (R.HX t).H) : G.CV 0 0 :=
  ⟨R.thDn t x, (nodeY R 0).multT_le_cusp R.θ _ _ (Lift.thetaDn (R.CC t) (R.ioY t) (D.R.m - 1) (R.ioX t _)).2⟩

def IsForm (t : T) (x : (R.HX t).H) (F : G.CV 0 D.R.m) : Prop :=
  F.1 = Node.castMaps (nodeX_eq_chainVertexAtRowZero_top R) (R.cX.toMap R.prX ((R.HX t).e x))

def givenVal (t : T) (Φ : G.Data R) {n : ℕ} (T₀ : Fin n → GivenInf G) (x : (R.HX t).H) (v : SmT (G.V 0 D.R.m).M) :
    GA D (G.V D.R.m 0).V → ℂ :=
  ∑ l, (G.chiLift Φ D.R.m (thDn G t x)).1 (colVec G 0 (T₀ l).2 D.R.m (rowVec G t 0 (T₀ l).1 D.R.m v))

def oppVal (t : T) {n n' : ℕ} (Tinf : Fin n → OppInf G) (Tf : Fin n' → OppFin G) (F : G.CV 0 D.R.m) (v : SmT (G.V 0 D.R.m).M) :
    GA D (G.V D.R.m 0).V → ℂ :=
  ∑ l, ∑ k, (G.rowLift t D.R.m (Tf k).2 D.R.m (G.colLift t D.R.m (Tf k).1 D.R.m F)).1
    (rowVec G t D.R.m (Tinf l).2 D.R.m (colVec G D.R.m (Tinf l).1 D.R.m v))

def FormulaFor (c : T → ℕ → ℕ → ℂ) : Prop :=
  ∀ (n₀ : ℕ) (T₀ : Fin n₀ → GivenInf G), ∃ (n : ℕ) (Tinf : Fin n → OppInf G),
    ∀ (t : T) (Φ : G.Data R), ∃ (n' : ℕ) (Tf : Fin n' → OppFin G), IsFlipped G t Φ Tf ∧
      ∀ x : (R.HX t).H, ∃ F, IsForm G t x F ∧ ∀ v, givenVal G t Φ T₀ x v = (cTot D c t)⁻¹ • oppVal G t Tinf Tf F v

def FlipOn : Prop := AllSome (IsSqConst G) (FormulaFor G)

def Standing : Prop :=
  11 ≤ D.host.splitBound ∧
    ∀ t, ∀ w ∈ places G t, ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal

end Grid

def FlipAt (D : D7) : Prop :=
  ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (G : GridDat R),
    R.Char F → G.Is → Standing G → FlipOn G

def Flip : Prop := ∀ D : D7, FlipAt D

section Basic₂

theorem absF_one : absF (1 : (AE D)ˣ) = 1 := by
  have h : (Oh D).toAddSubgroup.map (AddMonoidHom.mulLeft (toEAf D ((1 : (AE D)ˣ) : AE D))) = (Oh D).toAddSubgroup := by
    ext x; simp
  unfold absF Datum.volRel
  rw [h, inf_idem, AddSubgroup.addSubgroupOf_self]
  have : Nat.card ((Oh D).toAddSubgroup ⧸ (⊤ : AddSubgroup (Oh D).toAddSubgroup)) = 1 := AddSubgroup.index_top
  rw [this]; simp

theorem sum_divisible_eq_sum_mul {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (e : A) {p q : ℕ} (u v : Fin p → A) (u' v' : Fin q → A)
    (h : ∑ i, u i * v i + ∑ i, u' i * v' i = 0) : ∑ i, φ (e * u i) * φ (e * v i) + ∑ i, φ (e * u' i) * φ (e * v' i) = 0 := by
  have h2 := congrArg (fun z => φ (e * e * z)) h
  simp only [mul_zero, map_zero, mul_add, Finset.mul_sum, map_add, map_sum] at h2
  rw [← h2]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> rw [← map_mul] <;> congr 1 <;> ring

theorem rowBlocks_mul_colBlocks (e : AE D) {a a' d₁ d₂ : ℕ} (hd : a + a' = d₁ + d₂) (h : GL (Fin (d₁ + d₂)) (AE D)) :
    yLeft e hd h * xTop e hd h + yRight e hd h * xBot e hd h = 0 := by
  ext q p
  have h1 : (h.1 * (h⁻¹).1) (Fin.cast hd (Fin.natAdd a q)) (Fin.cast hd (Fin.castAdd a' p)) = 0 := by
    rw [Units.mul_inv, Matrix.one_apply_ne]
    intro H
    have := congrArg Fin.val H
    simp at this
    omega
  rw [Matrix.mul_apply, Fin.sum_univ_add] at h1
  exact sum_divisible_eq_sum_mul (toEAf D) e _ _ _ _ h1

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridDat R}

theorem cTot_ne_zero {c : T → ℕ → ℕ → ℂ} (h : IsSqConst G c) (t : T) : cTot D c t ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i hi => Finset.prod_ne_zero_iff.2 fun j hj =>
    (h t i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)).1

theorem rowVec_tuple (t t' : T) (i : ℕ) (P : ∀ j, Pol (G.V i j) (G.V i (j + 1))) (n : ℕ) : rowVec G t i P n = rowVec G t' i P n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show rowVec G t i P n ∘ₗ _ = rowVec G t' i P n ∘ₗ _
    rw [ih, G.th_It t t']

theorem colLift_succ_int (h : G.IsLifts) (t : T) {j n : ℕ} (hj : j ≤ D.R.m) (hn : n < D.R.m) (f : ∀ i, DX G i j)
    (hf : IsFinVec R.ψ R.θ true (G.V (n + 1) j) (G.V n j) (f n)) (P : ∀ i, Pol (G.V (i + 1) j) (G.V i j)) (F : G.CV 0 j)
    (v : SmT (G.V 0 j).M) :
    (G.colLift t j f (n + 1) F).1 (colVec G j P (n + 1) v) =
      (G.X n j).int (G.meas t n j) (fock R.ψ R.θ true (G.V (n + 1) j) (G.V n j) (f n) (P n))
        ((G.colLift t j f n F).1 (colVec G j P n v)) :=
  ((h.X t n j hn hj _ hf).int_eq _ _ _).symm

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriMembership

end
