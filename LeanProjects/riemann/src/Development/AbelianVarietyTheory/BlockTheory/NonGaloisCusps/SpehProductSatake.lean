import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivLocProdTriv

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions

namespace GlobalTheory.IndefiniteRowSideFullHecke.SpehProductSatake

def infString (d : ℕ) (A : Multiset ℂ) : Multiset ℂ :=
  A.bind fun x => (Multiset.range d).map fun j : ℕ => x + (((d : ℂ) - 1) / 2 - (j : ℂ))

def satString (q d : ℕ) (B : Multiset ℂˣ) : Multiset ℂ :=
  B.bind fun β => (Multiset.range d).map fun j : ℕ => (β : ℂ) * (q : ℂ) ^ (((d : ℂ) - 1) / 2 - (j : ℂ))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n c : ℕ}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

def IsSpehProductAt (π : Submodule ℂ (UA E n → ℂ)) {a : Fin c → ℕ} (P : ∀ i, CG E (a i)) (d : Fin c → ℕ)
    (h : ∑ i, a i * d i = n) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ (σ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E)))
    (S : ∀ i, SmIrr (GL (Fin (a i * d i)) (w.adicCompletion E))),
    (∀ i, (P i).IsLoc w (Quotient.mk _ (σ i))) ∧
    (∀ i, GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (σ i).ρ (σ i).smooth (σ i).irred) (d i) (S i).ρ) ∧
    IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w S)

def IsSatStringAt (π : Submodule ℂ (UA E n → ℂ)) {a : Fin c → ℕ} (P : ∀ i, CG E (a i)) (d : Fin c → ℕ)
    (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ B : Fin c → Multiset ℂˣ, (∀ i, (P i).HasSat w (B i)) ∧
    ∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
      ∀ β : Fin (n / 2) → ℂˣ, HasSatAt π w s ϖ q β →
        ∑ i, satString (Ideal.absNorm w.asIdeal) (d i) (B i) = (GlobalTheory.LGrp.bcParam n β).map Units.val

def IsInfStringAt (π : Submodule ℂ (UA E n → ℂ)) {a : Fin c → ℕ} (P : ∀ i, CG E (a i)) (d : Fin c → ℕ)
    (τ : E →+* ℂ) : Prop :=
  ∃ A : Fin c → Multiset ℂ, (∀ i, (P i).HasInfChar τ (A i)) ∧
    ∀ lam : DomWeight n, HasWeightAt π τ lam → ∑ i, infString (d i) (A i) = infOfWeight lam

def IsSpehBaseChange (π : Submodule ℂ (UA E n → ℂ)) {a : Fin c → ℕ} (P : ∀ i, CG E (a i)) (d : Fin c → ℕ)
    (h : ∑ i, a i * d i = n) : Prop :=
  (∀ i, 1 ≤ a i) ∧ (∀ i, 1 ≤ d i) ∧
  (Function.Injective fun i => (((⟨a i, P i⟩ : Σ b, CG E b), d i) : (Σ b, CG E b) × ℕ)) ∧
  (∀ i, (P i).IsUnitary) ∧ (∀ i, (P i).IsCsd) ∧
  (∀ w, IsSplitAt w → IsSpehProductAt π P d h w) ∧
  (∀ w, ¬ IsSplitAt w → IsUnramU π w → IsSatStringAt π P d w) ∧
  ∀ τ, IsInfStringAt π P d τ

def SpehBaseChange : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
      ∃ (c : ℕ) (a d : Fin c → ℕ) (P : ∀ i, CG E (a i)) (h : ∑ i, a i * d i = n), IsSpehBaseChange π P d h

theorem infString_one (A : Multiset ℂ) : infString 1 A = A := by
  simpa [infString] using Multiset.bind_singleton A id

theorem satString_one (q : ℕ) (B : Multiset ℂˣ) : satString q 1 B = B.map Units.val := by
  simp [satString, Multiset.bind_singleton]

theorem infString_zero (n : ℕ) :
    infString n {0} = Finset.univ.val.map fun k : Fin n => ((n : ℂ) - 1) / 2 - (k : ℕ) := by
  rw [infString, Multiset.singleton_bind, Fin.univ_val_map, List.ofFn_eq_map, ← Multiset.coe_range, Multiset.map_coe,
    ← List.map_coe_finRange_eq_range, List.map_map]
  simp [Function.comp_def]

theorem satString_two (q : ℕ) (hq : (q : ℂ) ≠ 0) :
    satString (q ^ 2) 2 {1} = (GlobalTheory.LGrp.bcParam 2 fun _ => Units.mk0 (q : ℂ) hq).map Units.val := by
  have h1 : (((q ^ 2 : ℕ) : ℂ)) ^ ((2 : ℂ)⁻¹) = q := by
    have := Complex.natCast_cpow_natCast_mul q 2 ((2 : ℂ)⁻¹)
    push_cast at this ⊢
    rw [← this]; simp
  have e1 : (((2 : ℕ) : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ) = (2 : ℂ)⁻¹ := by norm_num
  have e2 : (((2 : ℕ) : ℂ) - 1) / 2 - ((1 : ℕ) : ℂ) = -(2 : ℂ)⁻¹ := by norm_num
  have r : Multiset.range 2 = 0 ::ₘ {1} := by decide
  rw [satString, Multiset.singleton_bind, r, Multiset.map_cons, Multiset.map_singleton, e1, e2, Complex.cpow_neg, h1]
  simp [GlobalTheory.LGrp.bcParam]

theorem isSatStringAt_one (π : Submodule ℂ (UA E 1 → ℂ)) (w : HeightOneSpectrum (𝓞 E)) :
    IsSatStringAt π (a := fun _ : Fin 1 => 1) (fun _ => CG.ofChar 1) (fun _ => 1) w := by
  refine ⟨fun _ => {1}, fun _ => ?_, fun s ϖ q _ _ β _ => ?_⟩
  · exact CG.hasSat_ofChar (χ := 1) (w := w) fun _ _ => rfl
  · simp [satString_one, GlobalTheory.LGrp.bcParam]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem isSpehBaseChange_const_one :
    IsSpehBaseChange (Submodule.span ℂ {(fun _ => 1 : UA E 1 → ℂ)}) (a := fun _ : Fin 1 => 1) (fun _ => CG.ofChar 1)
      (fun _ => 1) (by simp) := by
  refine ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ _ _ => Subsingleton.elim _ _,
    fun _ => CG.isUnitary_ofChar fun _ => by simp,
    fun _ => ?_,
    fun w _ => ⟨fun _ => SmIrr.triv _, fun _ => SmIrr.triv _, fun _ => ?_, fun _ => ?_, ?_⟩,
    fun w _ _ => isSatStringAt_one _ w,
    fun τ => ⟨fun _ => {0}, fun _ => by simpa [CG.expo_one] using CG.hasInfChar_ofChar (1 : Formalism.L2.Host.HChar E) τ,
      fun lam h => by simp [infString_one, infOfWeight, weight_eq_zero_of_const τ lam h]⟩⟩
  · rw [CG.ofChar, CuspSub.twist_one]
    exact (cuspSub_iff (CuspSub.triv E (le_refl 1))).1.1 isCsdGL_const
  · have h : (CuspSub.triv E (le_refl 1)).IsLocComp w (SmIrr.triv _) :=
      ⟨LinearMap.toSpanSingleton ℂ _ ⟨oneFn E 1, Submodule.mem_span_singleton_self _⟩,
        fun h => oneFn_ne_zero ((one_smul ℂ _).symm.trans (congrArg Subtype.val (LinearMap.congr_fun h (1 : ℂ)))),
        fun _ _ => rfl⟩
    rw [CG.ofChar, CuspSub.twist_one]
    exact h
  · obtain ⟨hd, hc⟩ := GlobalTheory.LocGL.isSpeh_one (GlobalTheory.LocGL.IrrGL.of (SmIrr.triv (GL (Fin 1) (w.adicCompletion E))).ρ
      (SmIrr.triv _).smooth (SmIrr.triv _).irred)
    exact ⟨hd, hc.of_equiv (GlobalTheory.LocGL.IrrGL.equivOf _ _ _).symm (.refl _)⟩
  · obtain ⟨φ⟩ := nonempty_equiv_locProd_triv (Fin.sum_univ_one fun _ => 1) w
    exact isCompAlong_const _ _ φ

end GlobalTheory.IndefiniteRowSideFullHecke.SpehProductSatake

end
