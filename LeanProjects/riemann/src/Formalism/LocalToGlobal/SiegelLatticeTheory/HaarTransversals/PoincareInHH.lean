import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ColsDim
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

namespace Formalism.L2.SG.PoincareInHH

section Stab

variable (I : Formalism.MainNotions.S.AutInst)

def HinfS (S : Set (Fin I.n → I.E)) : Subgroup I.Ginf where
  carrier := {s | ∀ v, ∀ x ∈ S, uMat (s v) *ᵥ rv I v x = rv I v x}
  one_mem' := by
    intro v x _
    simp [uMat]
  mul_mem' := by
    intro s t hs ht v x hx
    have e1 : uMat ((s * t) v) = uMat (s v) * uMat (t v) := by simp [uMat]
    rw [e1, ← Matrix.mulVec_mulVec, ht v x hx, hs v x hx]
  inv_mem' := by
    intro s hs v x hx
    have e1 : uMat (s⁻¹ v) * uMat (s v) = 1 := by simp [uMat]
    calc uMat (s⁻¹ v) *ᵥ rv I v x = uMat (s⁻¹ v) *ᵥ (uMat (s v) *ᵥ rv I v x) := by rw [hs v x hx]
      _ = rv I v x := by rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]

def HfinS (S : Set (Fin I.n → I.E)) : Subgroup I.Gf where
  carrier := {x | ∀ y ∈ S, I.fmat x *ᵥ incl I y = incl I y}
  one_mem' := by
    intro y _
    simp [AutInst.fmat]
  mul_mem' := by
    intro a b ha hb y hy
    have e1 : I.fmat (a * b) = I.fmat a * I.fmat b := by simp [AutInst.fmat]
    rw [e1, ← Matrix.mulVec_mulVec, hb y hy, ha y hy]
  inv_mem' := by
    intro a ha y hy
    have e1 : I.fmat a⁻¹ * I.fmat a = 1 := by simp [AutInst.fmat]
    calc I.fmat a⁻¹ *ᵥ incl I y = I.fmat a⁻¹ *ᵥ (I.fmat a *ᵥ incl I y) := by rw [ha y hy]
      _ = incl I y := by rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]

def Sfin {r : ℕ} (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Set I.Gf :=
  {x | (∀ a : Fin r, (I.fmat x - 1) *ᵥ incl I (e a) ∈
        Submodule.span (I.E ⊗[I.F] Af I.F) ((fun b => incl I (e b)) '' {b | b.1 < a.1})) ∧
    (I.fmat x - 1) *ᵥ incl I z ∈ Submodule.span (I.E ⊗[I.F] Af I.F) (Set.range fun b => incl I (e b))}

end Stab

namespace PoincareSetting

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def fixSet : Set (Fin X.B.I.n → X.B.I.E) := Set.range X.eR ∪ Set.range X.fR ∪ {X.zR u}

abbrev Hinf : Subgroup X.B.I.Ginf := HinfS X.B.I (fixSet X u)
abbrev Hfin : Subgroup X.B.I.Gf := HfinS X.B.I (fixSet X u)

def Gam : Subgroup X.B.I.GA := Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ⊓ (Hinf X u).prod (Hfin X u)

def iotaI : Gam X u →* Hinf X u :=
  MonoidHom.codRestrict ((MonoidHom.fst _ _).comp (Gam X u).subtype) (Hinf X u)
    (fun γ => (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).1)

def iotaF : Gam X u →* Hfin X u :=
  MonoidHom.codRestrict ((MonoidHom.snd _ _).comp (Gam X u).subtype) (Hfin X u)
    (fun γ => (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).2)

theorem hinf_le_sinf (s : X.B.I.Ginf) (hs : s ∈ Hinf X u) : s ∈ X.SinfU u := by
  have hs' : ∀ v, ∀ x ∈ fixSet X u, uMat (s v) *ᵥ rv X.B.I v x = rv X.B.I v x := hs
  simp only [HidaSetting.SinfU, Sinf, Set.mem_setOf_eq]
  intro v
  constructor
  · intro a
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hs' v _ (Or.inl (Or.inl ⟨a, rfl⟩)), sub_self]
    exact Submodule.zero_mem _
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, hs' v _ (Or.inr rfl), sub_self]
    exact Submodule.zero_mem _

def piRep : Representation ℂ (Hinf X u) (X.Vpi u) where
  toFun h := (X.piU u (h : X.B.I.Ginf)).toLinearMap
  map_one' := by
    have h1 := (X.piU_rep u).1
    ext ξ
    simp [h1]
  map_mul' := by
    intro a b
    have hm := (X.piU_rep u).2.1 _ (hinf_le_sinf X u _ a.2) _ (hinf_le_sinf X u _ b.2)
    ext ξ
    simp [hm]

def Ku (hK : X.LevelSubgroupCharacter) : Subgroup (Hfin X u) where
  carrier := {h | (X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u ∈ X.K2}
  one_mem' := by
    show (X.xu u)⁻¹ * ((1 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.K2
    simpa using hK.1
  mul_mem' := by
    intro a b ha hb
    show (X.xu u)⁻¹ * ((a * b : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.K2
    have := hK.2.1 _ ha _ hb
    simpa [mul_assoc] using this
  inv_mem' := by
    intro a ha
    show (X.xu u)⁻¹ * ((a⁻¹ : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.K2
    have := hK.2.2.1 _ ha
    simpa [mul_assoc] using this

theorem chi2_apply_one (hK : X.LevelSubgroupCharacter) : X.chi2 1 = 1 := by
  have h1 := hK.2.2.2.1 1 hK.1 1 hK.1
  have hn := hK.2.2.2.2 1 hK.1
  rw [one_mul] at h1
  have h0 : X.chi2 1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  exact mul_left_cancel₀ h0 (h1.symm.trans (mul_one _).symm)

def psiK (hK : X.LevelSubgroupCharacter) : Ku X u hK →* ℂˣ where
  toFun h := Units.mk0 (X.chi2 ((X.xu u)⁻¹ * ((h : Hfin X u) : X.B.I.Gf) * X.xu u)) (by
    intro h0
    have hn := hK.2.2.2.2 _ h.2
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn)
  map_one' := by
    ext
    simpa using chi2_apply_one X hK
  map_mul' := by
    intro a b
    ext
    have := hK.2.2.2.1 _ a.2 _ b.2
    simp only [Units.val_mk0, Units.val_mul]
    rw [← this]
    congr 1
    simp [mul_assoc]

def Cu (hK : X.LevelSubgroupCharacter) : Submodule ℂ (X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) :=
  Formalism.L2.SG.ColsDim.Cols ℂ (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) (piRep X u)

def SfinU : Set X.B.I.Gf := Sfin X.B.I X.eR (X.zR u)

def Srat : Subgroup X.B.I.GA :=
  Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ⊓ Subgroup.closure {y | y.1 ∈ X.SinfU u ∧ y.2 ∈ SfinU X u}

def SGroup : Prop :=
  ((Subgroup.closure {y : X.B.I.GA | y.1 ∈ X.SinfU u ∧ y.2 ∈ SfinU X u} : Subgroup X.B.I.GA) :
    Set X.B.I.GA) = {y | y.1 ∈ X.SinfU u ∧ y.2 ∈ SfinU X u}

def IsDec (y : X.B.I.Gf) (n : X.B.I.Gf) (h : Hfin X u) (k : X.B.I.Gf) : Prop :=
  n ∈ X.NfinU u ∧ k ∈ X.K2 ∧ y = n * (h : X.B.I.Gf) * X.xu u * k

def phVal (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (yinf : X.B.I.Ginf) (n : X.B.I.Gf) (h : Hfin X u)
    (k : X.B.I.Gf) : ℂ :=
  X.psiFinU u n * X.chi2 k * (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u yinf) (1, h)

def Ph (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (y : X.B.I.GA) : ℂ :=
  if hd : ∃ n h k, IsDec X u y.2 n h k then
    phVal X u hK T y.1 hd.choose hd.choose_spec.choose hd.choose_spec.choose_spec.choose
  else 0

def PhWellDef (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (T : Cu X u hK) (yinf : X.B.I.Ginf) (yf n n' k k' : X.B.I.Gf) (h h' : Hfin X u),
    IsDec X u yf n h k → IsDec X u yf n' h' k' → phVal X u hK T yinf n h k = phVal X u hK T yinf n' h' k'

def PhProps (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ T : Cu X u hK, Measurable (Ph X u hK T) ∧
    (∀ γ ∈ Srat X u, ∀ y, Ph X u hK T (γ * y) = Ph X u hK T y) ∧
    (∀ y, ∀ κ ∈ X.K2, Ph X u hK T (y * (1, κ)) = X.chi2 κ * Ph X u hK T y) ∧
    ∀ y, Integrable (fun z => X.ph z * Ph X u hK T (y * (z, 1))) (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
      ∫ z, X.ph z * Ph X u hK T (y * (z, 1)) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = Ph X u hK T y

def Pser (hK : X.LevelSubgroupCharacter) (Dt : Set X.B.I.GA) (T : Cu X u hK) (x : X.B.I.GA) : ℂ :=
  Formalism.L2.SG.PoincareSeriesSquareIntegrable.poinc Dt (Ph X u hK T) x

def IsReps (Dt : Set X.B.I.GA) : Prop :=
  Formalism.L2.SG.FoldBound.IsRightTransversal (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (Srat X u) Dt

def PuFun (hK : X.LevelSubgroupCharacter) (Dt : Set X.B.I.GA) (T : Cu X u hK) : X.B.I.L2 X.B.μf X.B.fund :=
  if hm : MemLp (Pser X u hK Dt T) 2 ((X.B.I.muA X.B.μf).restrict X.B.fund) then hm.toLp _ else 0

def IFinite (hK : X.LevelSubgroupCharacter) : Prop :=
  (∃ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf)) ∧
  ∀ (T : Cu X u hK) (Ω : Set X.B.I.GA), IsCompact Ω → ∀ Fs : Set X.B.I.GA,
    IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) →
      Formalism.L2.SG.PoincareSeriesSquareIntegrable.multiplicityLIntegral (X.B.I.muA X.B.μf) (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) Ω Fs (Ph X u hK T) < ⊤

def InHH (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (T : Cu X u hK) (Dt : Set X.B.I.GA), IsReps X u Dt →
    (∀ x, Summable fun δ : Dt => ‖Ph X u hK T ((δ : X.B.I.GA) * x)‖) ∧
    (∀ Dt', IsReps X u Dt' → Pser X u hK Dt' T = Pser X u hK Dt T) ∧
    MemLp (Pser X u hK Dt T) 2 ((X.B.I.muA X.B.μf).restrict X.B.fund) ∧
    X.B.Re (X.Rph (PuFun X u hK Dt T)) = PuFun X u hK Dt T

def PuLinear (hK : X.LevelSubgroupCharacter) (Dt : Set X.B.I.GA) : Prop :=
  IsReps X u Dt → InHH X u hK →
  (∀ T T' : Cu X u hK, PuFun X u hK Dt (T + T') = PuFun X u hK Dt T + PuFun X u hK Dt T') ∧
    ∀ (c : ℂ) (T : Cu X u hK), PuFun X u hK Dt (c • T) = c • PuFun X u hK Dt T

abbrev HHX : Submodule ℂ (X.B.I.L2 X.B.μf X.B.fund) := Formalism.L2.SG.RowsDef.HHB X.B X.Rph

def Pu (hK : X.LevelSubgroupCharacter) (Dt : Set X.B.I.GA) (hD : IsReps X u Dt) (hin : InHH X u hK)
    (hlin : PuLinear X u hK Dt) : Cu X u hK →ₗ[ℂ] HHX X where
  toFun T := ⟨PuFun X u hK Dt T, by
    refine ⟨PuFun X u hK Dt T, ?_⟩
    exact (hin T Dt hD).2.2.2⟩
  map_add' T T' := by
    ext1
    exact (hlin hD hin).1 T T'
  map_smul' c T := by
    ext1
    exact (hlin hD hin).2 c T

theorem one_mem_level_subgroup : (1 : X.B.I.Gf) ∈ X.K2 := by
  have h1 : X.B.I.fmat 1 = 1 := by simp [AutInst.fmat]
  simp only [HidaSetting.K2, K2set, K2cong, InMod, Set.mem_setOf_eq, h1, sub_self, Matrix.zero_mulVec,
    Submodule.zero_mem, implies_true, and_true]
  first
  | simp [AutInst.Kset]
  | exact (Formalism.UG.stabGL X.B.I.Lf).one_mem

def frameOrthogonalLattice : Set (VA X.B.I) :=
  {y | y ∈ X.B.I.Lf ∧ ∀ a, hA X.B.I (incl X.B.I (X.eR a)) y = 0 ∧ hA X.B.I (incl X.B.I (X.fR a)) y = 0 ∧
    hA X.B.I (incl X.B.I (X.zR u)) y = 0}

def IsLevelTwoCongruentAt (x : X.B.I.Gf) : Prop :=
  (∀ a : Fin D.R.rS, ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      InMod X.B.I X.B.g (X.e0 '' {b | b.1 < a.1}) ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.I.fmat x - 1) *ᵥ X.e0 a))) ∧
    (∃ c : ℕ, Nat.Coprime c X.B.g ∧
      InMod X.B.I X.B.g (Set.range X.e0) ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.I.fmat x - 1) *ᵥ X.z0))) ∧
    ∀ i : Fin D.R.k, ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      InMod X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1})
        ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.I.fmat x - 1) *ᵥ X.bw i))

def HaarTransversal : Set (Hfin X u) :=
  {h | (∀ y ∈ frameOrthogonalLattice X u, X.B.I.fmat (h : X.B.I.Gf) *ᵥ y ∈ frameOrthogonalLattice X u ∧
      X.B.I.fmat ((h : X.B.I.Gf)⁻¹) *ᵥ y ∈ frameOrthogonalLattice X u) ∧
    IsLevelTwoCongruentAt X ((X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u)}

def K0 : Subgroup (Hfin X u) := Subgroup.closure (HaarTransversal X u)

def ColsLink (hK : X.LevelSubgroupCharacter) : Prop :=
  Ku X u hK ≤ K0 X u ∧ Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (K0 X u) ∧
    Finite (Formalism.L2.SG.ColsDim.Classes (iotaF X u) (Ku X u hK))

def c0 (volN volH : ℝ) : ℝ := volN * volH / (Module.finrank ℂ (X.Vpi u) : ℝ)

def NOinf : Set X.B.I.Ginf :=
  {s | ∃ γ ∈ X.B.I.GFset, γ.1 = s ∧ γ.1 ∈ X.NinfU u ∧ γ.2 ∈ X.NfinU u ∧ (X.xu u)⁻¹ * γ.2 * X.xu u ∈ X.K2}

def c0X (FdN : Set X.B.I.Ginf) : ℝ :=
  X.volK2 * (X.muN u FdN).toReal * (X.muH u Set.univ).toReal / (Module.finrank ℂ (X.Vpi u) : ℝ)

def Kform (u' : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (Dt Dt' : Set X.B.I.GA) (FdN FdN' : Set X.B.I.Ginf) (T : Cu X u hK)
    (T' : Cu X u' hK) : ℂ :=
  ((Real.sqrt (c0X X u FdN * c0X X u' FdN'))⁻¹ : ℝ) *
    ⟪PuFun X u hK Dt T, PuFun X u' hK Dt' T'⟫_ℂ

end PoincareSetting

end Formalism.L2.SG.PoincareInHH
