import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.abelian₂ Formalism.L2.LamCM
open ReciprocityTheory.ChartRestriction.G.FD (Data DataX Frame LamBasis fdeg)

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeLetterSources

section Letters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E} {l : Level H}
  {c : Coeff l} {nΨ n' : ℕ}

abbrev FinalTheorems (o : LamObj c nΨ n') : Type := (Fin o.xΨ.P.g × Fin nΨ) ⊕ (Fin o.x'.P.g × Fin n')

def FinalTheorems.chr {o : LamObj c nΨ n'} : FinalTheorems o → (E →+* ℂ)
  | .inl s => (o.τΨ s.1).1
  | .inr s => (o.τ' s.1).1

def FinalTheorems.copy {o : LamObj c nΨ n'} : FinalTheorems o → ℕ
  | .inl s => s.2
  | .inr s => s.2

def FinalTheorems.line {o : LamObj c nΨ n'} : FinalTheorems o → MLine o.K₁
  | .inl s => o.ℓΨ s.1
  | .inr s => o.ℓ' s.1

def FinalTheorems.img {o : LamObj c nΨ n'} : FinalTheorems o → (Sp (DualNumber o.K₁) ⟶ o.B.A.left)
  | .inl s => (o.xΨ.v s.1).left ≫ o.φΨg ≫ (o.φΨ s.2).left
  | .inr s => (o.x'.v s.1).left ≫ o.φ'g ≫ (o.φ' s.2).left

structure LamLetters (o : LamObj c nΨ n') : Type where
  m : (E →+* ℂ) → ℕ
  e : (Σ τ : E →+* ℂ, Fin (m τ)) ≃ Fin o.xB.P.g
  src : Fin o.xB.P.g → FinalTheorems o
  U : Matrix (Fin o.xB.P.g) (Fin o.xB.P.g) o.K₁
  ℓ : Fin o.xB.P.g → MLine o.K₁

variable {o : LamObj c nΨ n'}

def LamLetters.IsLetter (L : LamLetters o) (k : Fin o.xB.P.g) (w : epsR o.K₁ ⟶ o.xB.P.A) : Prop :=
  w.left ≫ o.φB = (L.src k).img

def LamLetters.IsEvident (L : LamLetters o) : Prop :=
  Function.Bijective L.src ∧
  (∀ (τ : E →+* ℂ) (i : Fin (L.m τ)), (L.src (L.e ⟨τ, i⟩)).chr = τ ∧ (L.src (L.e ⟨τ, i⟩)).copy = (i : ℕ)) ∧
  ∀ k, L.ℓ k = (L.src k).line

def LamLetters.IsGood (L : LamLetters o) : Prop :=
  L.IsEvident ∧ ∀ k, ∃ w : epsR o.K₁ ⟶ o.xB.P.A, L.IsLetter k w ∧ IsLieComb (L.U k) o.xB.v w

open Classical in

def blockSize (H : Host E) (nΨ n' : ℕ) (τ : E →+* ℂ) : ℕ := if τ (H.rt : E) = H.rt0 then nΨ else n'

open Classical in

def srcAt (o : LamObj c nΨ n') (p : Σ τ : E →+* ℂ, Fin (blockSize H nΨ n' τ)) : FinalTheorems o :=
  if h : p.1 (H.rt : E) = H.rt0 then .inl (o.τΨ.symm ⟨p.1, h⟩, p.2.cast (if_pos h))
  else .inr (o.τ'.symm ⟨p.1, h⟩, p.2.cast (if_neg h))

theorem srcAt_spec (o : LamObj c nΨ n') (p : Σ τ : E →+* ℂ, Fin (blockSize H nΨ n' τ)) :
    (srcAt o p).chr = p.1 ∧ (srcAt o p).copy = (p.2 : ℕ) := by
  unfold srcAt
  split_ifs with h <;> exact ⟨by simp [FinalTheorems.chr], rfl⟩

theorem srcAt_bijective (o : LamObj c nΨ n') : Function.Bijective (srcAt o) := by
  constructor
  · rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
    have h1 := srcAt_spec o ⟨τ, i⟩
    have h2 := srcAt_spec o ⟨τ', i'⟩
    rw [h] at h1
    obtain rfl : τ = τ' := h1.1.symm.trans h2.1
    obtain rfl : i = i' := Fin.ext (h1.2.symm.trans h2.2)
    rfl
  · rintro (⟨a, j⟩ | ⟨a, j⟩)
    · have h := (o.τΨ a).2
      refine ⟨⟨(o.τΨ a).1, j.cast (if_pos h).symm⟩, ?_⟩
      unfold srcAt
      rw [dif_pos h]
      simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
      rfl
    · have h := (o.τ' a).2
      refine ⟨⟨(o.τ' a).1, j.cast (if_neg h).symm⟩, ?_⟩
      unfold srcAt
      rw [dif_neg h]
      simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
      rfl

theorem exists_isEvident (o : LamObj c nΨ n') {f : ℕ} (h₁ : o.xΨ.P.g = f) (h₂ : o.x'.P.g = f)
    (h₃ : o.xB.P.g = f * (nΨ + n')) (U : Matrix (Fin o.xB.P.g) (Fin o.xB.P.g) o.K₁) :
    ∃ L : LamLetters o, L.m = blockSize H nΨ n' ∧ L.U = U ∧ L.IsEvident := by
  let b := Equiv.ofBijective _ (srcAt_bijective o)
  let d : FinalTheorems o ≃ Fin o.xB.P.g := Fintype.equivFinOfCardEq (by simp [h₁, h₂, h₃, mul_add])
  refine ⟨⟨blockSize H nΨ n', b.trans d, d.symm, U, fun k => (d.symm k).line⟩, rfl, rfl, d.symm.bijective,
    fun τ i => ?_, fun _ => rfl⟩
  have := srcAt_spec o ⟨τ, i⟩
  simpa [b] using this

end Letters

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

abbrev CMObj (Dw : Datum H) (c : Coeff l) : Type 1 :=
  letI := H.starRing
  LamObj c Dw.p Dw.q

def IsTie (o : CMObj Dw c) (y : letI := H.starRing; FrPt Xo c o.K₁)
    (eY : letI := H.starRing; o.xB.P.A.left ⟶ Xo.univ.t.G.left) : Prop :=
  letI := H.starRing
  IsGrpPullback o.xB.P.A Xo.univ.t.G y.x eY ∧
  (∀ a : 𝓞 E, ∃ α : o.xB.P.A ⟶ o.xB.P.A,
    α.left ≫ o.φB = o.φB ≫ (o.oa.act a).left ∧ α.left ≫ eY = eY ≫ (Xo.univ.t.act.act a).left) ∧
  ∃ (he : eSec o.xB.P.A ≫ eY = y.x ≫ eSec Xo.univ.t.G)
    (w : LB.Iso o.xB.P.L (Xo.univ.t.PP.L.pull eY)) (s₁ : LB.Sec (Xo.univ.t.PP.L.pull eY))
    (g : o.xB.P.A.left ⟶ Gx y.x),
    w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec o.xB.P.A) (fun _ => 1)) o.xB.rig
      (rigPullOf eY y.x he Xo.univ.t.PP.L Xo.univ.t.PP.rig) ∧
    IsoMaps w o.xB.th s₁ ∧
    g ≫ gxFst y.x = eY ∧ g ≫ gxSnd y.x = o.xB.P.A.hom ∧
    ∀ j, ∃ h : (Xo.univ.t.PP.L.pull eY).U j ≤ g ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit),
      s₁.f j = (g.appLE _ _ h).hom (y.s.f (fun _ => j PUnit.unit))

def LamPtClauses {σ₀ : c.F →+* ℂ} {r : ℕ} (Un : Unf Xo c σ₀ r) (k : Un.Comp) (x₀ : (Un.X k).dom) (La : ℝ)
    (o : CMObj Dw c) (L : letI := H.starRing; LamLetters o) (σ₁ : letI := H.starRing; o.K₁ →+* ℂ)
    (y : letI := H.starRing; FrPt Xo c o.K₁) (eY : letI := H.starRing; o.xB.P.A.left ⟶ Xo.univ.t.G.left) : Prop :=
  letI := H.starRing
  LamObjGood o (fdeg E) La ∧ L.IsGood ∧ (∀ τ, L.m τ ≤ r) ∧
  σ₁.comp (algebraMap c.F o.K₁) = σ₀ ∧
  IsTie o y eY ∧
  (∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), ∃ (i' : Fin (L.m τ)) (w : epsR o.K₁ ⟶ o.xB.P.A),
    (i' : ℕ) = (i : ℕ) ∧ L.IsLetter (L.e ⟨τ, i'⟩) w ∧ w.left ≫ eY = y.u τ i) ∧
  spMap (show o.K₁ →+* CAt σ₀ from σ₁) ≫ y.x = (Un.un k x₀).x

def frameOf {r : ℕ} (Xx : DataX E r) {X : Data E r} (hX : Xx.toData = X) (x : Frame X.Ψ r) : Frame Xx.Ψ r :=
  cast (congrArg (fun Y : Data E r => Frame Y.Ψ r) hX.symm) x

theorem frameOf_rfl {r : ℕ} (Xx : DataX E r) (x : Frame Xx.Ψ r) : frameOf Xx rfl x = x := rfl

end Point

def LamPtAt {D : Formalism.BasicNotions.D7} (T : Core D) (j : ℕ) (σ₀ : T.Q.c.F →+* ℂ) : Prop :=
  ∀ (k : (T.U j σ₀).Comp) (Xx : DataX D.host.E D.R.r) (hX : Xx.toData = (T.U j σ₀).X k),
    Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} →
    ∀ (x₀ : ((T.U j σ₀).X k).dom) (lam : Fin D.R.r → Fin D.R.r → D.host.E) (La : ℝ),
      LamBasis Xx La (frameOf Xx hX x₀.1) lam →
      letI := T.Q.H.starRing
      ∃ (o : CMObj (T.Q.Dw j) T.Q.c) (L : LamLetters o) (σ₁ : o.K₁ →+* ℂ) (y : FrPt (T.Q.Xo j) T.Q.c o.K₁)
        (eY : o.xB.P.A.left ⟶ (T.Q.Xo j).univ.t.G.left),
        LamPtClauses (T.U j σ₀) k x₀ La o L σ₁ y eY

def LamPtSt {D : Formalism.BasicNotions.D7} (T : Core D) (j : ℕ) : Prop :=
  LawsCore T → InR D j → LamPtAt T j T.σ₀

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeLetterSources
