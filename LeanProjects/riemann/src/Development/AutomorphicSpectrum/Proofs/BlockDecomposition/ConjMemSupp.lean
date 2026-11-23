import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.StrongApproxSub

section Group

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

abbrev mt (g : HA (AF F) σ J) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))

theorem mt_mul (g h : HA (AF F) σ J) : mt (g * h) = mt g * mt h := rfl

theorem mt_one : mt (1 : HA (AF F) σ J) = 1 := rfl

theorem mt_inv_mul (g : HA (AF F) σ J) : mt g⁻¹ * mt g = 1 := by
  rw [← mt_mul, inv_mul_cancel, mt_one]

theorem mt_mul_inv (g : HA (AF F) σ J) : mt g * mt g⁻¹ = 1 := by
  rw [← mt_mul, mul_inv_cancel, mt_one]

theorem smul_eq_iff (c : AF F ⊗[F] E) (X : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :
    (∀ i j, c * X i j = X i j) ↔ c • X = X := by
  constructor
  · intro h
    ext i j
    simpa using h i j
  · intro h i j
    simpa using congrFun (congrFun h i) j

theorem mem_SUSupp {ε : AF F} {g : HA (AF F) σ J} :
    g ∈ SUSupp σ J ε ↔
      g ∈ SUAdelic σ J ∧ algebraMap (AF F) (AF F ⊗[F] E) ε • (mt g - 1) = mt g - 1 :=
  and_congr_right fun _ => smul_eq_iff _ _

def suppGroup (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (ε : AF F) :
    Subgroup (HA (AF F) σ J) where
  carrier := SUSupp σ J ε
  mul_mem' := by
    intro g h hg hh
    obtain ⟨hg1, hg2⟩ := mem_SUSupp.1 hg
    obtain ⟨hh1, hh2⟩ := mem_SUSupp.1 hh
    refine mem_SUSupp.2 ⟨mul_mem hg1 hh1, ?_⟩
    have e : mt (g * h) - 1 = (mt g - 1) * (mt h - 1) + (mt g - 1) + (mt h - 1) := by
      rw [mt_mul]; noncomm_ring
    rw [e, smul_add, smul_add, ← Matrix.smul_mul, hg2, hh2]
  one_mem' := mem_SUSupp.2 ⟨one_mem _, by rw [mt_one, sub_self, smul_zero]⟩
  inv_mem' := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := mem_SUSupp.1 hg
    refine mem_SUSupp.2 ⟨inv_mem hg1, ?_⟩
    have e : mt g⁻¹ - 1 = -(mt g⁻¹ * (mt g - 1)) := by
      rw [Matrix.mul_sub, mt_inv_mul, Matrix.mul_one]; abel
    rw [e, smul_neg, ← Matrix.mul_smul, hg2]

theorem conj_mem_supp {ε : AF F} {γ h : HA (AF F) σ J} (hγ : γ ∈ SUAdelic σ J)
    (hh : h ∈ SUSupp σ J ε) : γ * h * γ⁻¹ ∈ SUSupp σ J ε := by
  obtain ⟨hh1, hh2⟩ := mem_SUSupp.1 hh
  refine mem_SUSupp.2 ⟨mul_mem (mul_mem hγ hh1) (inv_mem hγ), ?_⟩
  have e : mt (γ * h * γ⁻¹) - 1 = mt γ * (mt h - 1) * mt γ⁻¹ := by
    rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hh2]

def ratSupp (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (ε : AF F) :
    Subgroup (HA (AF F) σ J) where
  carrier := SASet σ J ε
  mul_mem' := by
    rintro _ _ ⟨γ, hγ, h, hh, rfl⟩ ⟨γ', hγ', h', hh', rfl⟩
    have hc : γ'⁻¹ * h * γ' ∈ SUSupp σ J ε := by
      have := conj_mem_supp (inv_mem (inf_le_left (a := SUAdelic σ J) hγ')) hh
      rwa [inv_inv] at this
    refine ⟨γ * γ', mul_mem hγ hγ', γ'⁻¹ * h * γ' * h', (suppGroup σ J ε).mul_mem hc hh', ?_⟩
    group
  one_mem' := ⟨1, one_mem _, 1, (suppGroup σ J ε).one_mem, by simp⟩
  inv_mem' := by
    rintro _ ⟨γ, hγ, h, hh, rfl⟩
    refine ⟨γ⁻¹, inv_mem hγ, γ * h⁻¹ * γ⁻¹,
      conj_mem_supp (inf_le_left (a := SUAdelic σ J) hγ) ((suppGroup σ J ε).inv_mem hh), ?_⟩
    group

end Group

theorem topGroup {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : IsTopologicalGroup (HA (AF F) σ J) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))

theorem propSub : Sa2.PropSub := by
  intro F E _ _ _ _ _ σ M J ε
  haveI := topGroup σ J
  exact ⟨(ratSupp σ J ε).topologicalClosure, rfl⟩

end GlobalTheory.CompanionTheory.StrongApproxSub

end
