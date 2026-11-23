import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpFrame.GLInhab

variable (l : ℕ) [Fact l.Prime] (N : ℕ)

def glFrame : Frame l Unit N where
  O := ℤ_[l]
  emb := (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom
  G := GL (Fin N) ℤ_[l]
  Γ := ⊥
  K := ⊤
  kap := MonoidHom.pi fun _ => (⊤ : Subgroup (GL (Fin N) ℤ_[l])).subtype
  chi := 1
  I := Unit
  tr := fun _ => {1}
  cst := fun _ => 1

theorem one_mem_dualWeyl :
    (1 : MvPolynomial (Fin N × Fin N) (PadicAlgCl l)) ∈ Formalism.GradedWeylDivisibility.dualWeyl (PadicAlgCl l) N N (res N (fun _ : ℕ => 0)) := by
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · have h0 : res N (fun _ : ℕ => 0) = 0 := rfl
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule, h0]
    exact MvPolynomial.isWeightedHomogeneous_one (R := PadicAlgCl l) (Formalism.GradedWeylDivisibility.colW N N)
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro a b _
    simp

def oneVec : NablaT (PadicAlgCl l) N (fun (_ : Unit) (_ : ℕ) => 0) :=
  PiTensorProduct.tprod (PadicAlgCl l) fun _ => ⟨1, one_mem_dualWeyl l N⟩

theorem oneVec_ne_zero : oneVec l N ≠ 0 := by
  intro h
  have h2 := congrArg (PiTensorProduct.subsingletonEquiv (R := PadicAlgCl l)
    (s := fun _ : Unit => Formalism.GradedWeylDivisibility.dualWeyl (PadicAlgCl l) N N (res N (fun _ : ℕ => 0))) ()) h
  rw [oneVec, PiTensorProduct.subsingletonEquiv_apply_tprod, map_zero] at h2
  exact one_ne_zero (congrArg Subtype.val h2)

theorem grp_oneVec (g : Unit → GL (Fin N) (PadicAlgCl l)) :
    grp (PadicAlgCl l) N (fun (_ : Unit) (_ : ℕ) => 0) g (oneVec l N) = oneVec l N := by
  simp only [grp, Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep, oneVec, MonoidHom.coe_comp, Function.comp_apply]
  rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
  congr 1
  funext τ
  apply Subtype.ext
  simp [Formalism.UG.dualWeylRep_apply]

theorem ok : (glFrame l N).Ok := by
  refine ⟨⟨?_, ⊥, inferInstance, ?_⟩, ⟨{1}, fun g => ⟨1, Subgroup.one_mem _, 1, Finset.mem_singleton_self _, g, Subgroup.mem_top g, by simp⟩⟩,
    fun g => ?_, fun i κ => ⟨Equiv.refl _, fun s => ⟨κ, ?_, rfl, rfl⟩⟩, fun i j => ⟨Equiv.prodComm _ _, fun x => ?_⟩⟩
  · intro x y h
    exact Subtype.val_injective ((algebraMap ℚ_[l] (PadicAlgCl l)).injective h)
  · ext x
    simp only [Set.mem_range, Set.mem_setOf_eq, IntermediateField.mem_bot]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨⟨((show ℤ_[l] from y) : ℚ_[l]), rfl⟩, ?_⟩
      show ‖algebraMap ℚ_[l] (PadicAlgCl l) ((show ℤ_[l] from y) : ℚ_[l])‖ ≤ 1
      rw [norm_algebraMap']
      exact (show ℤ_[l] from y).2
    · rintro ⟨⟨y, rfl⟩, hy⟩
      rw [norm_algebraMap'] at hy
      exact ⟨(⟨y, hy⟩ : ℤ_[l]), rfl⟩
  · have hu : Nat.card {γ : (glFrame l N).Γ // g⁻¹ * (γ : (glFrame l N).G) * g ∈ (glFrame l N).K} = 1 := by
      refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => Subtype.ext (Subsingleton.elim (α := (⊥ : Subgroup (GL (Fin N) ℤ_[l]))) _ _)⟩,
        ⟨⟨1, Subgroup.mem_top _⟩⟩⟩
    refine ⟨Nat.finite_of_card_ne_zero (by rw [hu]; exact one_ne_zero), ?_⟩
    rw [hu]
    exact fun h => (Fact.out : l.Prime).ne_one (Nat.dvd_one.1 h)
  · have hs : (s : (glFrame l N).G) = 1 := Finset.mem_singleton.1 s.2
    show (κ : (glFrame l N).G) * s = s * κ
    rw [hs, mul_one, one_mul]
  · have h1 : ∀ (k : Unit) (t : (glFrame l N).tr k), (t : (glFrame l N).G) = 1 := fun k t => Finset.mem_singleton.1 t.2
    have he : ((((Equiv.prodComm _ _ x).1 : (glFrame l N).G) * (Equiv.prodComm _ _ x).2)⁻¹ * ((x.1 : (glFrame l N).G) * x.2)) = 1 := by
      rw [h1 _ (Equiv.prodComm _ _ x).1, h1 _ (Equiv.prodComm _ _ x).2, h1 _ x.1, h1 _ x.2]; simp
    rw [he]
    exact ⟨Subgroup.mem_top _, rfl, rfl⟩

end GlobalTheory.ExpFrame.GLInhab

namespace GlobalTheory.ExpFrame

end GlobalTheory.ExpFrame
