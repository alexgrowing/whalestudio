import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Twist

variable {Γ O : Type} [Group Γ] [CommRing O] {n : ℕ}

def twGL (r : Γ →* GL (Fin n) O) (χ : Γ →* Oˣ) : Γ →* GL (Fin n) O where
  toFun g := Units.map (Matrix.scalar (Fin n) : O →+* Matrix (Fin n) (Fin n) O).toMonoidHom (χ g) * r g
  map_one' := by simp
  map_mul' g h := by
    apply Units.ext
    simp only [map_mul, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [mul_assoc, mul_assoc, ← mul_assoc (Matrix.scalar (Fin n) _) (r g : Matrix (Fin n) (Fin n) O),
      (Matrix.scalar_commute _ (fun _ => Commute.all _ _) (r g : Matrix (Fin n) (Fin n) O)).eq, mul_assoc]

def charGL (χ : Γ →* Oˣ) : Γ →* GL (Fin 1) O := twGL 1 χ

theorem twGL_val (r : Γ →* GL (Fin n) O) (χ : Γ →* Oˣ) (g : Γ) :
    ((twGL r χ g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) =
      ((χ g : Oˣ) : O) • (r g : Matrix (Fin n) (Fin n) O) := by
  change Matrix.scalar (Fin n) ((χ g : Oˣ) : O) * (r g : Matrix (Fin n) (Fin n) O) = _
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

end Twist

def sg (b : Bool) : ℚ := if b then 1 else -1

def lam {n : ℕ} (a : Fin n → ℤ) (s : Fin n) : ℚ := (a s : ℚ) + (((n : ℚ) - 1) / 2 - ((s : ℕ) : ℚ))

def wtJump {n : ℕ} (a : Fin n → ℤ) (b : Bool) (s : Fin n) : ℚ := ((n : ℚ) - 1) / 2 - sg b * lam a s

def IsRunWeight {n : ℕ} (p t : ℕ) (a : Fin n → ℤ) : Prop :=
  Antitone a ∧
  (∀ s s' : Fin n, p ≤ (s : ℕ) → (s : ℕ) < p + t → p ≤ (s' : ℕ) → (s' : ℕ) < p + t → a s = a s') ∧
  (∀ s s' : Fin n, (s : ℕ) < p → p ≤ (s' : ℕ) → a s' < a s) ∧
  (∀ s s' : Fin n, (s : ℕ) < p + t → p + t ≤ (s' : ℕ) → a s' < a s)

def sigPar {R : Ranks} (P : HCParam R) : Multiset ℚ :=
  Finset.univ.val.map P.v + Finset.univ.val.map fun i => -P.b i

def runPar (t : ℕ) (e : ℚ) : Multiset ℚ :=
  (Finset.Icc 1 t).val.map fun c : ℕ => -e + ((t : ℚ) - 1) / 2 - ((c : ℚ) - 1)

def fullPar {R : Ranks} (P : HCParam R) (j : Fin R.m) : Multiset ℚ := sigPar P + runPar R.t (P.e j)

section Dict

variable (D : D7)

def embAt (ρ : D.what₂.Tau) (b : Bool) : D.host.E →+* ℂ :=
  if b then D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)
  else (D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)).comp
    (D.host.conj : D.host.E →+* D.host.E)

def jF (i : D.nd.Loc) : Fin D.R.m := ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def ctr (i : D.nd.Loc) (ρ : D.what₂.Tau) : ℚ := (D.hc ρ).e (jF D i)

abbrev Emb (i : D.nd.Loc) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Type :=
  Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw

def cplx (i : D.nd.Loc) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (τ : Emb D i w hw) : D.host.E →+* ℂ :=
  (D.naut.iotaQC i).toRingHom.comp
    ((D.nbr i w hw).LL.1.val.toRingHom.comp (τ.toRingHom.comp (Br.cEw D.nbr i w hw)))

def JumpsAre (i : D.nd.Loc) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) {m : ℕ}
    (r : GE D.nd →* GL (Fin m) (D.nd.O i)) (τ : Emb D i w hw) (J : Multiset ℚ) : Prop :=
  (∀ y ∈ J, ∃ z : ℤ, y = (z : ℚ)) ∧
  ∀ z : ℤ, Br.jumpMult D.loc D.nbr i w hw r τ z = (J.count (z : ℚ) : ℤ)

def IsWeight (i : D.nd.Loc) (a : D.what₂.Tau → Fin D.R.nV → ℤ) : Prop :=
  ∀ ρ, IsRunWeight (D.R.sigW (D.nd.j i)).1 D.R.t (a ρ) ∧
    ∀ b, D.naut.infWt i (embAt D ρ b) =
      Finset.univ.val.map fun s => ((sg b * lam (a ρ) s : ℚ) : ℂ)

def ParamTie : Prop :=
  ∀ i ρ b, D.naut.infWt i (embAt D ρ b) =
    (fullPar (D.hc ρ) (jF D i)).map fun y => ((sg b * (y - 1 / 2) : ℚ) : ℂ)

def CharTie : Prop :=
  (∀ i ρ b, D.naut.infG (D.naut.muC i) (embAt D ρ b) = {((-(sg b * ctr D i ρ) : ℚ) : ℂ)}) ∧
  ∀ ρ b, D.naut.infG D.naut.etaTinv (embAt D ρ b) = {((-(sg b / 2) : ℚ) : ℂ)}

def WeightsAt (i : D.nd.Loc) (a : D.what₂.Tau → Fin D.R.nV → ℤ) (x : D.nd.X i)
    (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Prop :=
  ∀ (τ : Emb D i w hw) (ρ : D.what₂.Tau) (b : Bool), cplx D i w hw τ = embAt D ρ b →
    JumpsAre D i w hw r τ (Finset.univ.val.map (wtJump (a ρ) b)) ∧
    ({z : ℤ | Br.IsJumpW D.loc D.nbr i w hw r τ z}.ncard = D.R.nV ∧
      ∀ z : ℤ, Br.jumpMult D.loc D.nbr i w hw r τ z ≤ 1) ∧
    ∃ w₁ : ℤ,
      (∀ y : ℚ, (∃ s : Fin D.R.nV, (D.R.sigW (D.nd.j i)).1 ≤ (s : ℕ) ∧
          (s : ℕ) < (D.R.sigW (D.nd.j i)).1 + D.R.t ∧ y = wtJump (a ρ) b s) ↔
        ∃ z : ℤ, w₁ ≤ z ∧ z < w₁ + D.R.t ∧ y = (z : ℚ)) ∧
      ¬ Br.IsJumpW D.loc D.nbr i w hw r τ (w₁ - 1) ∧
      ¬ Br.IsJumpW D.loc D.nbr i w hw r τ (w₁ + D.R.t) ∧
      (x ∈ D.nd.Z i → ∀ z : ℤ,
        (∃ c, 1 ≤ c ∧ c ≤ D.R.t ∧ Br.IsJumpW D.loc D.nbr i w hw (charGL (D.nd.chi i c)) τ z) ↔
          (w₁ ≤ z ∧ z < w₁ + D.R.t))

def Crys_at : Prop :=
  ∀ (i : D.nd.Loc), (∀ k, D.nd.l i ≠ D.host.g k) →
  ∀ a, IsWeight D i a →
  ∀ (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
  ∀ (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.IsCrysW D.loc D.nbr i w hw r ∧ WeightsAt D i a x r w hw

def TypePrime_at : Prop :=
  ∀ (i : D.nd.Loc), (∃ k, D.nd.l i = D.host.g k) →
  ∀ a, IsWeight D i a →
  ∀ (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
  ∀ (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.IsdRW D.loc D.nbr i w hw r ∧ WeightsAt D i a x r w hw ∧
    ∀ P : D.naut.AV i, D.naut.ptV i P = some x →
      (Br.IsPotCrysW D.loc D.nbr i w hw r ↔ D.naut.mono0 (D.naut.locV i P w))

def Twisted_at : Prop :=
  ParamTie D → CharTie D →
  ∀ (i : D.nd.Loc) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (τ : Emb D i w hw) (ρ : D.what₂.Tau) (b : Bool), cplx D i w hw τ = embAt D ρ b →
    (∀ c, 1 ≤ c → c ≤ D.R.t → JumpsAre D i w hw (charGL (D.nd.chi i c)) τ
      {sg b * (ctr D i ρ + 1 / 2) + ((D.R.nV : ℚ) - 1) / 2 - ((D.R.t : ℚ) - 1) / 2 + ((c : ℚ) - 1)}) ∧
    ∀ (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
      JumpsAre D i w hw (twGL r (D.nd.chi i 1)⁻¹) τ
        ((fullPar (D.hc ρ) (jF D i)).map fun y => ((D.R.t : ℚ) - 1) / 2 - sg b * (y + ctr D i ρ)) ∧
      JumpsAre D i w hw (twGL r (D.nd.chi i 1)⁻¹) τ
        ((Finset.range D.R.t).val.map (fun c : ℕ => (c : ℚ)) +
          (sigPar (D.hc ρ)).map fun y => ((D.R.t : ℚ) - 1) / 2 - sg b * (y + ctr D i ρ)) ∧
      ∀ (s : Fin (D.R.k - 1)) (z : ℤ),
        (z : ℚ) = ((D.R.t : ℚ) - 1) / 2 - sg b * ((D.hc ρ).v s + ctr D i ρ) →
        (b = true → z < 0) ∧ (b = false → (D.R.t : ℤ) - 1 < z)

def Explicit_at : Prop :=
  ParamTie D →
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
  ∀ (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.IsdRW D.loc D.nbr i w hw r ∧
    ∀ (τ : Emb D i w hw) (ρ : D.what₂.Tau),
      (cplx D i w hw τ = embAt D ρ true →
        JumpsAre D i w hw r τ
          ((fullPar (D.hc ρ) (jF D i)).map fun p => ((D.R.nV : ℚ) - 1) / 2 + 1 / 2 - p) ∧
        (CharTie D → x ∈ D.nd.Z i → ∀ c, 1 ≤ c → c ≤ D.R.t → JumpsAre D i w hw (charGL (D.nd.chi i c)) τ
          {ctr D i ρ + 1 / 2 + (D.R.r : ℚ) / 2 + ((c : ℚ) - 1)})) ∧
      (cplx D i w hw τ = embAt D ρ false →
        JumpsAre D i w hw r τ
          ((fullPar (D.hc ρ) (jF D i)).map fun p => ((D.R.nV : ℚ) - 1) / 2 - 1 / 2 + p))

def PlaceTypeCondition : Prop := Crys_at D ∧ TypePrime_at D ∧ Twisted_at D ∧ Explicit_at D

end Dict

def AtF (S : D7 → Prop) {eps : ℝ} (Fm : FamP eps) : Prop := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, S (Fm.D x i)

def CrysF {eps : ℝ} (Fm : FamP eps) : Prop := AtF Crys_at Fm

def TypePrimeF {eps : ℝ} (Fm : FamP eps) : Prop := AtF TypePrime_at Fm

def RowF {eps : ℝ} (Fm : FamP eps) : Prop := AtF PlaceTypeCondition Fm

def CrysClosed (C : FamClass) : Prop := Closed C fun Fm _ => CrysF Fm

def TypePrimeClosed (C : FamClass) : Prop := Closed C fun Fm _ => TypePrimeF Fm

def RowClosed (C : FamClass) : Prop := Closed C fun Fm _ => RowF Fm

example : IsRunWeight (n := 4) 1 2 ![2, 0, 0, -1] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s s'; revert s s'; decide
  all_goals decide

example : ¬ IsRunWeight (n := 4) 1 2 ![2, 0, 0, 0] := by
  intro h
  exact absurd (h.2.2.2 1 3 (by decide) (by decide)) (by decide)

end GlobalTheory.IndefiniteRowSideFullHecke.PrimeTypeWeightPartitions

end
