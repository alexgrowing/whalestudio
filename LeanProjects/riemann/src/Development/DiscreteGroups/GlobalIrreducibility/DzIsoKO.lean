import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.ExistsOfMemKOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.StepData

namespace DiscreteGroups.sglob.DzIso

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

theorem exists_int_lift {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ_[g]) (h : ∀ a b, ‖M a b‖ ≤ 1) :
    ∃ A : Matrix (Fin n) (Fin n) ℤ_[g], (algebraMap ℤ_[g] ℚ_[g]).mapMatrix A = M :=
  ⟨fun a b => ⟨M a b, h a b⟩, by ext a b; rfl⟩

theorem mapMatrix_int_injective {n : ℕ} :
    Function.Injective ((algebraMap ℤ_[g] ℚ_[g]).mapMatrix : Matrix (Fin n) (Fin n) ℤ_[g] → _) :=
  fun _ _ h => Matrix.ext fun a b => PadicInt.ext (congrFun (congrFun h a) b)

include hi

theorem mem_integer_iff (x : ℚ_[g]) : i x ∈ 𝒪[w.adicCompletion E] ↔ ‖x‖ ≤ 1 :=
  (Valuation.mem_integer_iff _ _).trans (valuation_le_iff i hi x)

theorem map_inc_mem_KO {n : ℕ} (k : GL (Fin n) ℤ_[g]) :
    Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) ∈ KO (w.adicCompletion E) (Fin n) := by
  rw [mem_KO]
  refine ⟨fun a b => (mem_integer_iff i hi _).2 (k.val a b).2, fun a b => ?_⟩
  rw [← map_inv, ← map_inv]
  exact (mem_integer_iff i hi _).2 ((k⁻¹).val a b).2

theorem exists_of_mem_KO {n : ℕ} {m : GL (Fin n) (w.adicCompletion E)} (hm : m ∈ KO (w.adicCompletion E) (Fin n)) :
    ∃ k : GL (Fin n) ℤ_[g], Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) = m := by
  obtain ⟨h1, h2⟩ := mem_KO.1 hm
  have hint : ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E), IntM M →
      ∀ a b, ‖i.symm.toRingHom.mapMatrix M a b‖ ≤ 1 := by
    intro M hM a b
    rw [← norm_le_iff i hi]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    exact (val_le_iff _).1 ((Valuation.mem_integer_iff _ _).1 (hM a b))
  obtain ⟨A, hA⟩ := exists_int_lift _ (hint _ h1)
  obtain ⟨B, hB⟩ := exists_int_lift _ (hint _ h2)
  have hAB : A * B = 1 := mapMatrix_int_injective (by rw [map_mul, hA, hB, ← map_mul, Units.mul_inv, map_one, map_one])
  have hBA : B * A = 1 := mapMatrix_int_injective (by rw [map_mul, hA, hB, ← map_mul, Units.inv_mul, map_one, map_one])
  refine ⟨⟨A, B, hAB, hBA⟩, Units.ext (Matrix.ext fun a b => ?_)⟩
  change i ((algebraMap ℤ_[g] ℚ_[g]).mapMatrix A a b) = m.val a b
  rw [hA]
  simp

theorem map_inc_range (n : ℕ) :
    (inc g n).range.map (Matrix.GeneralLinearGroup.map i.toRingHom) = KO (w.adicCompletion E) (Fin n) := by
  ext m
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact map_inc_mem_KO i hi k
  · intro hm
    obtain ⟨k, rfl⟩ := exists_of_mem_KO i hi hm
    exact ⟨_, ⟨k, rfl⟩, rfl⟩

def toKO (n : ℕ) : GL (Fin n) ℤ_[g] →* KO (w.adicCompletion E) (Fin n) :=
  ((Matrix.GeneralLinearGroup.map i.toRingHom).comp (inc g n)).codRestrict _ fun k => map_inc_mem_KO i hi k

theorem coe_toKO (n : ℕ) (k : GL (Fin n) ℤ_[g]) :
    ((toKO i hi n k : KO (w.adicCompletion E) (Fin n)) : GL (Fin n) (w.adicCompletion E)) =
      Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) := rfl

theorem toKO_injective (n : ℕ) : Function.Injective (toKO i hi n) := by
  intro k k' h
  have h' := congrArg (fun x : KO (w.adicCompletion E) (Fin n) =>
    ((x : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) h
  refine Units.ext (Matrix.ext fun a b => PadicInt.ext (i.injective ?_))
  exact congrFun (congrFun h' a) b

theorem toKO_surjective (n : ℕ) : Function.Surjective (toKO i hi n) := by
  intro m
  obtain ⟨k, hk⟩ := exists_of_mem_KO i hi m.2
  exact ⟨k, Subtype.ext hk⟩

def equivKO (n : ℕ) : GL (Fin n) ℤ_[g] ≃* KO (w.adicCompletion E) (Fin n) :=
  MulEquiv.ofBijective (toKO i hi n) ⟨toKO_injective i hi n, toKO_surjective i hi n⟩

def redKO (n : ℕ) : KO (w.adicCompletion E) (Fin n) →* Gn g n :=
  (red g n).comp (equivKO i hi n).symm.toMonoidHom

theorem redKO_toKO (n : ℕ) (k : GL (Fin n) ℤ_[g]) : redKO i hi n (toKO i hi n k) = red g n k := by
  show red g n ((equivKO i hi n).symm (equivKO i hi n k)) = red g n k
  rw [MulEquiv.symm_apply_apply]

theorem redKO_surjective (n : ℕ) : Function.Surjective (redKO i hi n) :=
  (GlobalTheory.GLp.Model.red_surjective n).comp (equivKO i hi n).symm.surjective

theorem ker_redKO (n : ℕ) :
    (redKO i hi n).ker = (KOne (w.adicCompletion E) (Fin n)).subgroupOf (KO (w.adicCompletion E) (Fin n)) := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨k, rfl⟩ := toKO_surjective i hi n m
  rw [redKO_toKO, coe_toKO]
  constructor
  · intro hk
    exact map_mem_KOne i hi k hk
  · intro hm
    obtain ⟨k', hk', he⟩ := exists_of_mem_KOne i hi hm
    have : k' = k := toKO_injective i hi n (Subtype.ext he)
    rw [← this]
    exact hk'

end DiscreteGroups.sglob.DzIso
