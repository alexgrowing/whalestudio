import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DeRham
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DifferentiableAtOm

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

variable (E a) in

def HV : Submodule ℝ (Lie E a) where
  carrier := {x | IsSelfAdjoint (Matrix.of x)}
  add_mem' h h' := IsSelfAdjoint.add h h'
  zero_mem' := IsSelfAdjoint.zero (Matrix (Fin a) (Fin a) (Cinf E))
  smul_mem' c x h := (Herm E a).smul_mem c (x := Matrix.of x) h

def hv : Herm E a ≃ₗ[ℝ] HV E a where
  toFun X := ⟨toL X.1, X.2⟩
  invFun x := ⟨Matrix.of x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [NumberField E] in
theorem hv_val (X : Herm E a) : Matrix.of (hv X).1 = X.1 := rfl

variable (E a) in

def hOne : HV E a := hv ⟨1, IsSelfAdjoint.one _⟩

omit [NumberField E] in
theorem hOne_val : Matrix.of (hOne E a).1 = 1 := rfl

def sand : GL (Fin a) (Cinf E) →* (HV E a →L[ℝ] HV E a) where
  toFun g := LinearMap.toContinuousLinearMap
    { toFun := fun p => ⟨toL (g.val * Matrix.of p.1 * star g.val), IsSelfAdjoint.conjugate p.2 g.val⟩
      map_add' := fun p p' => Subtype.ext (by
        change g.val * (Matrix.of p.1 + Matrix.of p'.1) * star g.val =
          g.val * Matrix.of p.1 * star g.val + g.val * Matrix.of p'.1 * star g.val
        rw [mul_add, add_mul])
      map_smul' := fun c p => Subtype.ext (by
        change g.val * (c • Matrix.of p.1) * star g.val = c • (g.val * Matrix.of p.1 * star g.val)
        rw [mul_smul_comm, smul_mul_assoc]) }
  map_one' := ContinuousLinearMap.ext fun p => Subtype.ext (by
    change (1 : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of p.1 * star 1 = Matrix.of p.1
    simp)
  map_mul' g h := ContinuousLinearMap.ext fun p => Subtype.ext (by
    change (g.val * h.val) * Matrix.of p.1 * star (g.val * h.val) =
      g.val * (h.val * Matrix.of p.1 * star h.val) * star g.val
    simp only [star_mul, mul_assoc])

theorem sand_val (g : GL (Fin a) (Cinf E)) (p : HV E a) :
    Matrix.of (sand g p).1 = g.val * Matrix.of p.1 * star g.val := rfl

variable (E a) in

def cone : Set (HV E a) := {p | ∃ g : GL (Fin a) (Cinf E), sand g (hOne E a) = p}

theorem hOne_mem_cone : hOne E a ∈ cone E a := ⟨1, by rw [map_one]; rfl⟩

theorem sand_mem_cone (g : GL (Fin a) (Cinf E)) {p : HV E a} (hp : p ∈ cone E a) : sand g p ∈ cone E a := by
  obtain ⟨h, rfl⟩ := hp
  exact ⟨g * h, by rw [map_mul]; rfl⟩

variable [IsTotallyComplex E]

def ev {d : ℕ} : Sm E a ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] (GA E a → Fin d → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun φ v g => φ.1 g • v) (fun φ ψ v => by ext g i; simp [add_mul])
    (fun c φ v => by ext g i; simp [mul_assoc]) (fun φ v w => by ext g i; simp [mul_add])
    (fun c φ v => by ext g i; simp [mul_left_comm]))

@[simp] theorem ev_tmul {d : ℕ} (φ : Sm E a) (v : Fin d → ℂ) (g : GA E a) : ev (φ ⊗ₜ[ℂ] v) g = φ.1 g • v := rfl

def geo (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) :
    Geo (⊤ : Subgroup (GL (Fin a) E)) (HV E a) (GL (Fin a) (Af E) ⧸ U) Ξ.d where
  ρ := sand.comp (((GeneralLinearGroup.map (pInf E)).comp (ratGL E a)).comp (Subgroup.subtype ⊤))
  σ := (MulAction.toPermHom (GL (Fin a) (Af E)) _).comp
    ((GeneralLinearGroup.map (algebraMap E (Af E))).comp (Subgroup.subtype ⊤))
  ξ := (ratC Ξ).comp (Subgroup.subtype ⊤)
  Y := cone E a
  isOpen := ho
  maps _ _ hp := sand_mem_cone _ hp

section

variable (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)

theorem geo_Y : (geo ho U Ξ).Y = cone E a := rfl

theorem geo_ρ (γ : (⊤ : Subgroup (GL (Fin a) E))) :
    (geo ho U Ξ).ρ γ = sand (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1)) := rfl

theorem geo_σ (γ : (⊤ : Subgroup (GL (Fin a) E))) (s : GL (Fin a) (Af E) ⧸ U) :
    (geo ho U Ξ).σ γ s = GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 • s := rfl

theorem geo_ξ (γ : (⊤ : Subgroup (GL (Fin a) E))) :
    (geo ho U Ξ).ξ γ = Ξ.mat (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1)) := rfl

theorem geo_lev : (geo ho U Ξ).lev = levelRep ⊤ U (ratC Ξ) := by
  ext γ f s i
  rw [Geo.lev_apply, geo_σ]
  simp only [Subgroup.coe_inv, map_inv]
  rfl

def Corr {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)))
    (w : (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ)) : Prop :=
  ∀ (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (X : Fin q → Herm E a),
    w (x : GL (Fin a) (Af E) ⧸ U) (sand g (hOne E a)) (fun i => (2 : ℝ) • sand g (hv (X i))) =
      Ξ.mat g *ᵥ ev (ω X) (infGL E a g * finGL E a x)

end

def LeftInv {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Prop := ∀ γ g, ev m (ratGL E a γ * g) = ev m g

def RightInv (U : Subgroup (GL (Fin a) (Af E))) {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Prop :=
  ∀ u ∈ U, ∀ g, ev m (g * finGL E a u) = ev m g

end UpperTheory.V.Lit.Dr
