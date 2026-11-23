import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide

noncomputable section

namespace GlobalTheory.LKCount

def LeftCosets {Γ G : Type} [Group Γ] [Group G] (_ι : Γ →* G) (K : Subgroup G) : Type := G ⧸ K

namespace LeftCosets

variable {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (K : Subgroup G)

instance : MulAction Γ (LeftCosets ι K) := MulAction.compHom (G ⧸ K) ι

def mk (x : G) : LeftCosets ι K := ((x : G ⧸ K) : G ⧸ K)

def rep (y : LeftCosets ι K) : G := Quotient.out (y : G ⧸ K)

variable {ι K}

theorem mk_rep (y : LeftCosets ι K) : mk ι K (rep ι K y) = y :=
  QuotientGroup.out_eq' (s := K) (y : G ⧸ K)

theorem mk_eq_mk {x y : G} : mk ι K x = mk ι K y ↔ x⁻¹ * y ∈ K :=
  QuotientGroup.eq

theorem smul_mk (η : Γ) (x : G) : η • mk ι K x = mk ι K (ι η * x) := rfl

theorem rep_mk (x : G) : ∃ k ∈ K, rep ι K (mk ι K x) = x * k := by
  have h : mk ι K x = mk ι K (rep ι K (mk ι K x)) := (mk_rep _).symm
  rw [mk_eq_mk] at h
  exact ⟨_, h, by group⟩

theorem mem_map_conj {x g : G} : g ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * g * x ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [mul_assoc] using hk
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem stabilizer_mk (x : G) :
    MulAction.stabilizer Γ (mk ι K x) = (K.map (MulAut.conj x).toMonoidHom).comap ι := by
  ext η
  rw [MulAction.mem_stabilizer_iff, smul_mk, mk_eq_mk, Subgroup.mem_comap, mem_map_conj]
  constructor
  · intro h
    have := K.inv_mem h
    simpa [mul_assoc] using this
  · intro h
    have := K.inv_mem h
    simpa [mul_assoc] using this

end LeftCosets

section Terms

variable {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂]

theorem stab_eq_stabilizer (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (x : G₁ × G₂) :
    stab ι₁ ι₂ K₁ K₂ x = MulAction.stabilizer Γ (LeftCosets.mk (ι₁.prod ι₂) (K₁.prod K₂) x) := by
  rw [LeftCosets.stabilizer_mk]
  ext η
  simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, LeftCosets.mem_map_conj, Subgroup.mem_prod,
    MonoidHom.prod_apply, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]

def cosetTerm (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (y : LeftCosets (ι₁.prod ι₂) (K₁.prod K₂)) (γ : Γ) : ℂ :=
  term ι₁ ι₂ θ δ f₁ φ (LeftCosets.rep _ _ y) γ

end Terms

end GlobalTheory.LKCount
