import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsB

noncomputable section

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting Matrix

namespace Formalism.L2.SG.Pf.NormSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LeviOntoSPf

variable {D : D7}

def fixV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : Set (VA X.B.I) :=
  Set.range (fun a => incl X.B.I (X.eR a)) ∪ Set.range (fun a => incl X.B.I (X.fR a)) ∪
    {X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)}

variable {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) (u : D.what₂.Word)

def KappaOnto : Prop :=
  ∀ s : Iof TR, ∃ κ : X.B.I.Gf, κ ∈ X.B.I.Kset ∧ (∀ y ∈ fixV X u, X.B.I.fmat κ *ᵥ y = y) ∧ levi TR κ = s

variable (X)

def IsDualFrame (η : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (b d : Fin D.R.k → VA X.B.I) : Prop :=
  η ∈ IntAf X.B.I.F X.B.I.E ∧ η * η = η ∧ η * X.ew = η ∧ ZMod' X.B.I X.B.g (X.ew - η) ∧
    (∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      η * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = η) ∧
    (∀ i, b i ∈ X.B.I.Lf ∧ d i ∈ X.B.I.Lf ∧ η • b i = b i ∧ sigA X.B.I η • d i = d i) ∧
    (∀ y ∈ fixV X u, ∀ i, hA X.B.I y (b i) = 0 ∧ hA X.B.I y (d i) = 0) ∧
    (∀ i j, hA X.B.I (d i) (b j) = if i = j then η else 0) ∧
    ∀ i j, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (b j) - if i = j then X.ew else 0) ∧
      ZMod' X.B.I X.B.g (hA X.B.I (d i) (X.bw j) - if i = j then X.ew else 0)

def DualFrame : Prop := ∃ η b d, IsDualFrame X u η b d

def SIdem : Prop :=
  ∃ ε ∈ IntAf X.B.I.F X.B.I.E, ε * ε = ε ∧ sigA X.B.I ε = ε ∧ ZMod' X.B.I X.B.g (1 - ε) ∧
    ∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      ε * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = ε

def FrameOfS : Prop := SIdem X → DualFrame X u

variable {X}

def LeviElt : Prop :=
  ∀ η b d, IsDualFrame X u η b d → ∀ C C' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
    (∀ i j, C i j ∈ IntAf X.B.I.F X.B.I.E ∧ C' i j ∈ IntAf X.B.I.F X.B.I.E) →
    η • (C * C') = η • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _) →
    η • (C' * C) = η • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _) →
    ∃ κ : X.B.I.Gf, κ ∈ X.B.I.Kset ∧ (∀ y ∈ fixV X u, X.B.I.fmat κ *ᵥ y = y) ∧
      ∀ v, leviM TR κ v = C.map (resT TR v)

def MatLift : Prop :=
  ∀ η : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F, η ∈ IntAf X.B.I.F X.B.I.E → η * η = η → η * X.ew = η →
    ZMod' X.B.I X.B.g (X.ew - η) →
    (∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      η * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = η) →
    ∀ s : Iof TR, ∃ C C' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
      (∀ i j, C i j ∈ IntAf X.B.I.F X.B.I.E ∧ C' i j ∈ IntAf X.B.I.F X.B.I.E) ∧
      η • (C * C') = η • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _) ∧
      η • (C' * C) = η • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _) ∧
      ∀ v, C.map (resT TR v) = ((s v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v))

theorem kappaOnto_of (hF : DualFrame X u) (hE : LeviElt TR u) (hL : MatLift TR) : KappaOnto TR u := by
  intro s
  obtain ⟨η, b, d, hfr⟩ := hF
  obtain ⟨C, C', hint, hCC, hC'C, hres⟩ :=
    hL η hfr.1 hfr.2.1 hfr.2.2.1 hfr.2.2.2.1 hfr.2.2.2.2.1 s
  obtain ⟨κ, hκK, hfix, hlev⟩ := hE η b d hfr C C' hint hCC hC'C
  refine ⟨κ, hκK, hfix, ?_⟩
  funext v
  have hM : leviM TR κ v = ((s v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) := by
    rw [hlev, hres]
  have hu : IsUnit (leviM TR κ v).det := by
    rw [hM]
    exact Matrix.isUnits_det_units (s v)
  simp only [levi, dif_pos hu]
  exact Units.ext hM

theorem LeviOntoS_xu_inv_fix (y : Fin X.B.I.n → X.B.I.E)
    (hy : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I y = incl X.B.I y) :
    X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I y = incl X.B.I y := by
  have e : X.B.I.fmat (X.xu u)⁻¹ * X.B.I.fmat (X.xu u) = 1 := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  calc X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I y
      = X.B.I.fmat (X.xu u)⁻¹ *ᵥ (X.B.I.fmat (X.xu u) *ᵥ incl X.B.I y) := by rw [hy]
    _ = incl X.B.I y := by rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]

theorem LeviOntoS_conj_mem (κ : X.B.I.Gf) (hfix : ∀ y ∈ fixV X u, X.B.I.fmat κ *ᵥ y = y) :
    X.xu u * κ * (X.xu u)⁻¹ ∈ Hfin X u := by
  have hmul : ∀ a b : X.B.I.Gf, X.B.I.fmat (a * b) = X.B.I.fmat a * X.B.I.fmat b := by
    intro a b
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have hinv : X.B.I.fmat (X.xu u) * X.B.I.fmat (X.xu u)⁻¹ = 1 := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have he : ∀ a, X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) :=
    fun a => (X.xu_fix u a).1
  have hf : ∀ a, X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) :=
    fun a => (X.xu_fix u a).2
  show ∀ y ∈ fixSet X u, X.B.I.fmat (X.xu u * κ * (X.xu u)⁻¹) *ᵥ incl X.B.I y = incl X.B.I y
  intro y hy
  rw [hmul, hmul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz
  · rw [LeviOntoS_xu_inv_fix u _ (he a), hfix (incl X.B.I (X.eR a)) (Or.inl (Or.inl ⟨a, rfl⟩)), he a]
  · rw [LeviOntoS_xu_inv_fix u _ (hf a), hfix (incl X.B.I (X.fR a)) (Or.inl (Or.inr ⟨a, rfl⟩)), hf a]
  · rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [hfix (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) (Or.inr rfl), Matrix.mulVec_mulVec, hinv,
      Matrix.one_mulVec]

theorem LeviOntoS_K_inv {κ : X.B.I.Gf} (hκ : κ ∈ X.B.I.Kset) : κ⁻¹ ∈ X.B.I.Kset := by
  exact Subgroup.inv_mem (Formalism.UG.stabGL X.B.I.Lf) hκ

variable {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)

theorem leviOntoS_of (hK : KappaOnto TR u) : LeviOntoS TR cs := by
  intro q s
  obtain ⟨κ, hκK, hfix, hlev⟩ := hK s
  have e1 : colDS (cs.h (cs.base q.1))
      (cs.h (cs.base q.1) * ⟨X.xu u * κ * (X.xu u)⁻¹, LeviOntoS_conj_mem u κ hfix⟩) = κ := by
    simp only [colDS, Subgroup.coe_mul, Subgroup.coe_mk]
    group
  have e2 : colDS (cs.h (cs.base q.1) * ⟨X.xu u * κ * (X.xu u)⁻¹, LeviOntoS_conj_mem u κ hfix⟩)
      (cs.h (cs.base q.1)) = κ⁻¹ := by
    simp only [colDS, Subgroup.coe_mul, Subgroup.coe_mk]
    group
  refine ⟨cs.h (cs.base q.1) * ⟨X.xu u * κ * (X.xu u)⁻¹, LeviOntoS_conj_mem u κ hfix⟩, ?_, ?_, ?_⟩
  · rw [e1]
    exact hκK
  · rw [e2]
    exact LeviOntoS_K_inv hκK
  · rw [e1]
    exact hlev

theorem leviOntoS_of_steps (hS : SIdem X) (hFS : FrameOfS X u) (hE : LeviElt TR u) (hL : MatLift TR) : LeviOntoS TR cs :=
  leviOntoS_of (TR := TR) (u := u) (cs := cs) (kappaOnto_of (TR := TR) (u := u) (hFS hS) hE hL)

end LeviOntoSPf

end Formalism.L2.SG.Pf.NormSteps
