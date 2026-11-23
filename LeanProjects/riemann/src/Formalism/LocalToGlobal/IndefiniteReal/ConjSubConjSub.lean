import Formalism.LocalToGlobal.IndefiniteReal.CongNormal
import Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace
import Formalism.LocalToGlobal.Columns.MtRowRep

noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Conj

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def conjSub (U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) where
  carrier := {f | (fun g => star (f g)) ∈ U}
  zero_mem' := by
    show (fun g => star ((0 : Formalism.AUTREP.GAf L n → ℂ) g)) ∈ U
    have : (fun g => star ((0 : Formalism.AUTREP.GAf L n → ℂ) g)) = 0 := by
      funext g
      simp
    rw [this]
    exact U.zero_mem
  add_mem' := by
    intro f f' hf hf'
    show (fun g => star ((f + f') g)) ∈ U
    have : (fun g => star ((f + f') g)) = (fun g => star (f g)) + (fun g => star (f' g)) := by
      funext g
      simp
    rw [this]
    exact U.add_mem hf hf'
  smul_mem' := by
    intro a f hf
    show (fun g => star ((a • f) g)) ∈ U
    have : (fun g => star ((a • f) g)) = star a • (fun g => star (f g)) := by
      funext g
      simp [mul_comm]
    rw [this]
    exact U.smul_mem _ hf

theorem mem_conjSub {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} {f : Formalism.AUTREP.GAf L n → ℂ} :
    f ∈ conjSub U ↔ (fun g => star (f g)) ∈ U := Iff.rfl

theorem conjSub_conjSub (U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) : conjSub (conjSub U) = U := by
  ext f
  have hf : (fun g => star (star (f g))) = f := by
    funext g
    simp
  show (fun g => star (star (f g))) ∈ U ↔ f ∈ U
  rw [hf]

theorem conjSub_mono {U U' : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (h : U ≤ U') : conjSub U ≤ conjSub U' :=
  fun _ hf => h hf

theorem conjSub_bot : conjSub (⊥ : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) = ⊥ := by
  ext f
  rw [mem_conjSub, Submodule.mem_bot, Submodule.mem_bot]
  constructor
  · intro h
    funext g
    have := congrFun h g
    simpa using this
  · intro h
    subst h
    funext g
    simp

theorem conj_rt (h : Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) :
    (fun g => star (Formalism.L2.NG.rt L n h f g)) = Formalism.L2.NG.rt L n h (fun g => star (f g)) := rfl

theorem conjSub_stable {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (hU : ∀ h, ∀ f ∈ U, Formalism.L2.NG.rt L n h f ∈ U) :
    ∀ h, ∀ f ∈ conjSub U, Formalism.L2.NG.rt L n h f ∈ conjSub U := by
  intro h f hf
  rw [mem_conjSub] at hf ⊢
  rw [conj_rt]
  exact hU h _ hf

def FinTyp.conjT (π : Formalism.L2.NG.FinTyp L n) : Formalism.L2.NG.FinTyp L n where
  S := conjSub π.S
  stable := conjSub_stable π.stable
  smooth := by
    intro f hf
    obtain ⟨N, hN, hfix⟩ := π.smooth _ hf
    refine ⟨N, hN, fun κ hκ => ?_⟩
    funext g
    have := congrFun (hfix κ hκ) g
    rw [← conj_rt] at this
    simp only at this
    exact star_injective this
  ne := by
    intro h
    apply π.ne
    rw [← conjSub_conjSub π.S, h, conjSub_bot]
  irr := by
    intro S' hle hst
    rcases π.irr (conjSub S') (by rw [← conjSub_conjSub π.S]; exact conjSub_mono hle) (conjSub_stable hst) with h | h
    · left
      rw [← conjSub_conjSub S', h, conjSub_bot]
    · right
      rw [← conjSub_conjSub S', h]

theorem conjT_S (π : Formalism.L2.NG.FinTyp L n) : (FinTyp.conjT π).S = conjSub π.S := rfl

end Conj

section Act

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostI (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

def rtA (k : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := rTr V k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def actM (P : RowPsi V n) (M : Mult.DSModel V Sp) : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ (Mult.MMap M) where
  toFun h := Mult.postOn M (rtA (P.ψ h))
  map_one' := by
    apply LinearMap.ext
    intro T
    apply MultilinearMap.ext
    intro v
    funext g
    simp [Mult.postOn_apply, rtA, rTr]
  map_mul' a b := by
    apply LinearMap.ext
    intro T
    apply MultilinearMap.ext
    intro v
    funext g
    simp only [map_mul, Module.End.mul_apply, Mult.postOn_apply]
    show T v (g * (P.ψ a * P.ψ b)) = T v (g * P.ψ a * P.ψ b)
    rw [mul_assoc]

theorem actM_apply (P : RowPsi V n) (M : Mult.DSModel V Sp) (h : Formalism.AUTREP.GAf D.host.E n) (T : Mult.MMap M) (v : M.Vec)
    (g : GA D V) : actM P M h T v g = T v (g * P.ψ h) := rfl

def levN (P : RowPsi V n) (N : ℕ) : Set (GA D V) := P.ψ '' {κ | Formalism.L2.NG.Cong D.host.E n N κ}

def Minf (P : RowPsi V n) (M : Mult.DSModel V Sp) : Submodule ℂ (Mult.MMap M) :=
  ⨆ N : ℕ, Mult.Mult θ M (levN P (N + 1)) (fun _ => 1)

def isotIn {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A)
    (π : Formalism.L2.NG.FinTyp D.host.E n) : Submodule ℂ A :=
  ⨆ (Φ : π.S →ₗ[ℂ] A) (_ : IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C), LinearMap.range Φ

def isotL (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (π : Formalism.L2.NG.FinTyp D.host.E n) : Submodule ℂ (Mult.MMap M) :=
  Mult.goodPart θ M J χ e ⊓ isotIn (actM P M) (Minf θ P M) π

def isotE (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (π : Formalism.L2.NG.FinTyp D.host.E n) : Submodule ℂ (Mult.MMap M) :=
  isotL θ P M J χ e (FinTyp.conjT π)

def OccRows (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ)
    (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) : Set (Formalism.L2.NG.FinTyp D.host.E n) :=
  {π | ∃ b, isotE θ P M (J b) (χ b) (e b) π ≠ ⊥}

abbrev FTR (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ)
    (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) : Type :=
  Formalism.L2.Col.FinTypCls (OccRows θ P M J χ e)

def rowRepR {P : RowPsi V n} {M : Mult.DSModel V Sp} {J : Bool → Set (GA D V)} {χ : Bool → GA D V → ℂ}
    {e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} (σ : FTR θ P M J χ e) : Formalism.L2.NG.FinTyp D.host.E n :=
  Formalism.L2.Col.finTypRep _ σ

theorem rowRepR_occ {P : RowPsi V n} {M : Mult.DSModel V Sp} {J : Bool → Set (GA D V)} {χ : Bool → GA D V → ℂ}
    {e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} (σ : FTR θ P M J χ e) : rowRepR θ σ ∈ OccRows θ P M J χ e :=
  Formalism.L2.Col.finTypRep_mem _ σ

theorem rowRepR_inj {P : RowPsi V n} {M : Mult.DSModel V Sp} {J : Bool → Set (GA D V)} {χ : Bool → GA D V → ℂ}
    {e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} (σ σ' : FTR θ P M J χ e)
    (h : (rowRepR θ σ).Iso (rowRepR θ σ')) : σ = σ' :=
  Formalism.L2.Col.finTypRep_inj h

def IsEigOf (P : RowPsi V n) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (π : Formalism.L2.NG.FinTyp D.host.E n) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Prop :=
  (∃ x ∈ π.S, x ≠ 0 ∧ IsTypeVec (P.ψ ⁻¹' J) (fun κ => χ (P.ψ κ)) x) ∧
  (∀ Pr d R, Mult.Hecke₂ V J χ Sb Pr d R → ∀ x ∈ π.S, IsTypeVec (P.ψ ⁻¹' J) (fun κ => χ (P.ψ κ)) x →
    Hecke₃ P R x = c Pr d • x) ∧
  ∀ Pr d, (¬ ∃ R, Mult.Hecke₂ V J χ Sb Pr d R) → c Pr d = 0

open Classical in

def cOfT (P : RowPsi V n) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (π : Formalism.L2.NG.FinTyp D.host.E n) : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ :=
  if h : ∃ c, IsEigOf P J χ Sb π c then h.choose else 0

structure IsIsomFin {Y W : Formalism.BasicNotions.TH.HSp D} (ι : ↥(GfC Y) →* ↥(GfC W)) : Prop where
  bij : Function.Bijective ι
  conj : ∃ (X : Matrix (Fin W.rank) (Fin Y.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (X' : Matrix (Fin Y.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), X * X' = 1 ∧ X' * X = 1 ∧
      ∀ g : GfC Y, finMat D.sp.cm.sig W.gram ((ι g : GfC W) : GA D W) = X * finMat D.sp.cm.sig Y.gram (g : GA D Y) * X'
  lat : ∀ g : GfC Y, ((g : GA D Y) ∈ KsphC Y ∅ ↔ ((ι g : GfC W) : GA D W) ∈ KsphC W ∅)

def FrameMatch {Y W : Formalism.BasicNotions.TH.HSp D} (PY : RowPsi Y n) (PW : RowPsi W n) (ι : ↥(GfC Y) →* ↥(GfC W)) : Prop :=
  ∃ k : Formalism.AUTREP.GAf D.host.E n, ∀ h, PW.ψ (k⁻¹ * h * k) = ((ι ⟨PY.ψ h, PY.into h⟩ : GfC W) : GA D W)

end Act

end Formalism.IndefR.principalLevelFrame
