import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnimodOneGenus
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralHeckeForms

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable (D : D7)

theorem ddS_ne_zero : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  exact Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot

theorem aaI_ne_zero (a : Fin D.R.rS) : aaI D a ≠ 0 := by
  unfold aaI
  exact zpow_ne_zero _ (ddS_ne_zero D)

theorem int_mul_of_ne {b : 𝓞 D.host.E} (hb : b ≠ 0) : ∃ k : ℕ, k ≠ 0 ∧ ∃ c : 𝓞 D.host.E, (k : 𝓞 D.host.E) = b * c := by
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
    exact ⟨c, by rw [← hc, mul_comm]⟩

theorem coe_nat_O (k : ℕ) : (((k : 𝓞 D.host.E)) : D.host.E) = (k : D.host.E) := by
  simp

theorem fi_nat_mul {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} (hI : I ≠ 0) (x : D.host.E) :
    ∃ k : ℕ, k ≠ 0 ∧ (k : D.host.E) * x ∈ I := by
  obtain ⟨y, hyI, hy0⟩ : ∃ y ∈ I, y ≠ 0 := by
    by_contra h
    push Not at h
    apply hI
    ext z
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨h z, fun hz => hz ▸ fi_zero D I⟩
  obtain ⟨a0, b0, hb0, rfl⟩ := IsFractionRing.div_surjective (𝓞 D.host.E) y
  have hb0' : algebraMap (𝓞 D.host.E) D.host.E b0 ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]
    exact nonZeroDivisors.ne_zero hb0
  have ha0I : algebraMap (𝓞 D.host.E) D.host.E a0 ∈ I := by
    have := fi_mul D b0 hyI
    have e : (b0 : D.host.E) * (algebraMap (𝓞 D.host.E) D.host.E a0 / algebraMap (𝓞 D.host.E) D.host.E b0) =
        algebraMap (𝓞 D.host.E) D.host.E a0 := by
      rw [show (b0 : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b0 from rfl, mul_div_cancel₀ _ hb0']
    rwa [e] at this
  have ha00 : a0 ≠ 0 := by
    rintro rfl
    simp at hy0
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 D.host.E) x
  have hbne : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap (𝓞 D.host.E) D.host.E b ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]
    exact hbne
  obtain ⟨k, hk, c, hc⟩ := int_mul_of_ne D hbne
  obtain ⟨k0, hk0, c0, hc0⟩ := int_mul_of_ne D ha00
  refine ⟨k0 * k, mul_ne_zero hk0 hk, ?_⟩
  have hcE : (k : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b * algebraMap (𝓞 D.host.E) D.host.E c := by
    rw [← map_mul, ← hc]; simp
  have hc0E : (k0 : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E a0 * algebraMap (𝓞 D.host.E) D.host.E c0 := by
    rw [← map_mul, ← hc0]; simp
  have e : ((k0 * k : ℕ) : D.host.E) * (algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E b) =
      ((c0 * c * a : 𝓞 D.host.E) : D.host.E) * algebraMap (𝓞 D.host.E) D.host.E a0 := by
    rw [Nat.cast_mul, hcE, hc0E]
    show _ = algebraMap (𝓞 D.host.E) D.host.E (c0 * c * a) * _
    rw [map_mul, map_mul]
    field_simp
  rw [e]
  exact fi_mul D _ ha0I

variable {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (f : Fin D.R.rS → (VS D).V)

theorem M_nat_smul (M : Submodule (𝓞 D.host.E) (WbQ D F0)) (hsp : Submodule.span D.host.E (M : Set (WbQ D F0)) = ⊤)
    (m : WbQ D F0) : ∃ k : ℕ, k ≠ 0 ∧ (k : 𝓞 D.host.E) • m ∈ M := by
  first | exact UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul .. | (apply UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (apply @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (apply @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 M hsp m | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 M hsp | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 M | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D

theorem vPr_perp (hf : PartnerOK D F0 f) (v : (VS D).V) : vPr D F0 f v ∈ perpS (VS D) F0.X := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    simp [vPr, hf.1]
  | zero => simp
  | add y w _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

def vPrLin : (VS D).V →ₗ[D.host.E] (VS D).V where
  toFun := vPr D F0 f
  map_add' := vPr_add D F0 f
  map_smul' := vPr_smul D F0 f

def coordL (hf : PartnerOK D F0 f) :
    (VS D).V →ₗ[D.host.E] (Fin D.R.rS → D.host.E) × (WbQ D F0) × (Fin D.R.rS → D.host.E) :=
  LinearMap.prod (LinearMap.pi fun a => ((VS D).hT (f a)).comp (vPrLin D F0 f))
    (LinearMap.prod ((nX D F0).mkQ.comp (LinearMap.codRestrict _ (vPrLin D F0 f) (vPr_perp D F0 f hf)))
      (LinearMap.pi fun a => (VS D).hT (F0.e a)))

theorem coordL_apply (hf : PartnerOK D F0 f) (v : (VS D).V) :
    coordL D F0 f hf v = ((fun a => (VS D).hT (f a) (vPr D F0 f v)),
      (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) : WbQ D F0),
      (fun a => (VS D).hT (F0.e a) v)) := rfl

theorem coordL_injective (hf : PartnerOK D F0 f) : Function.Injective (coordL D F0 f hf) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  rw [coordL_apply] at hv
  simp only [Prod.mk_eq_zero] at hv
  obtain ⟨h1, h2, h3⟩ := hv
  have hb : ∀ a, (VS D).hT (F0.e a) v = 0 := fun a => congrFun h3 a
  have hvv : vPr D F0 f v = v := by simp [vPr, hb]
  have hX : v ∈ F0.X := by
    rw [Submodule.Quotient.mk_eq_zero] at h2
    have : vPr D F0 f v ∈ F0.X := h2
    rwa [hvv] at this
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun D.host.E |>.1 hX
  have ha : ∀ a, (VS D).hT (f a) v = 0 := fun a => by
    have := congrFun h1 a
    rwa [hvv] at this
  have hc0 : ∀ a, c a = 0 := by
    intro a
    have h := ha a
    rw [← hc, map_sum] at h
    have e : ∀ b, (VS D).hT (f a) (c b • F0.e b) = c b * (if b = a then 1 else 0) := by
      intro b
      rw [map_smul, smul_eq_mul, ← (VS D).herm.eq (F0.e b) (f a), hf.1 b a]
      split_ifs <;> simp
    simp only [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  rw [← hc]
  simp [hc0]

theorem fi_bound (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    ∃ d : D.host.E, ∀ x ∈ I, ∃ o : 𝓞 D.host.E, x = (o : D.host.E) * d := by
  obtain ⟨d, hdS, hd⟩ := I.isFractional
  refine ⟨(algebraMap (𝓞 D.host.E) D.host.E d)⁻¹, fun x hx => ?_⟩
  obtain ⟨o, ho⟩ := hd x hx
  have hd0 : algebraMap (𝓞 D.host.E) D.host.E d ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]
    exact nonZeroDivisors.ne_zero hdS
  refine ⟨o, ?_⟩
  rw [Algebra.smul_def] at ho
  show x = algebraMap (𝓞 D.host.E) D.host.E o * _
  rw [ho]
  field_simp

theorem pi_mem_span {x : Fin D.R.rS → D.host.E} {d : Fin D.R.rS → D.host.E}
    (h : ∀ a, ∃ o : 𝓞 D.host.E, x a = (o : D.host.E) * d a) :
    x ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => (Pi.single a (d a) : Fin D.R.rS → D.host.E)) := by
  choose o ho using h
  have e : x = ∑ a, o a • (Pi.single a (d a) : Fin D.R.rS → D.host.E) := by
    ext b
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    simp [ho b]
    rfl
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem lamC_fg (hf : PartnerOK D F0 f) (M : Submodule (𝓞 D.host.E) (WbQ D F0)) (hM : M.FG) :
    (lamC D F0 f M).FG := by
  choose dα hdα using fun a => fi_bound D (aaI D a)
  choose dβ hdβ using fun a => fi_bound D (aaI D a)⁻¹
  let P : Submodule (𝓞 D.host.E) ((Fin D.R.rS → D.host.E) × (WbQ D F0) × (Fin D.R.rS → D.host.E)) :=
    (Submodule.span (𝓞 D.host.E) (Set.range fun a => (Pi.single a (dα a) : Fin D.R.rS → D.host.E))).prod
      (M.prod (Submodule.span (𝓞 D.host.E) (Set.range fun a =>
        (Pi.single a (star (dβ a)) : Fin D.R.rS → D.host.E))))
  have hPfg : P.FG := Submodule.FG.prod (Submodule.fg_span (Set.finite_range _))
    (Submodule.FG.prod hM (Submodule.fg_span (Set.finite_range _)))
  have hle : (lamC D F0 f M).map ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E)) ≤ P := by
    rintro _ ⟨v, ⟨h1, ⟨w, hw, hwM⟩, h3⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · exact pi_mem_span D (fun a => hdα a _ (h3 a))
    · have e : (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) = w := Subtype.ext hw.symm
      show (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) : WbQ D F0) ∈ M
      rw [e]; exact hwM
    · refine pi_mem_span D (fun a => ?_)
      obtain ⟨o, ho⟩ := hdβ a _ (h1 a)
      obtain ⟨o', ho'⟩ := star_int D o
      refine ⟨o', ?_⟩
      show (VS D).hT (F0.e a) v = _
      rw [ho', ← star_mul, mul_comm, ← ho, star_star]
  exact Submodule.fg_of_fg_map_injective ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E)) (coordL_injective D F0 f hf)
    (Submodule.FG.of_le (S := (lamC D F0 f M).map ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E))) hPfg hle)

theorem lamC_span (hf : PartnerOK D F0 f) (M : Submodule (𝓞 D.host.E) (WbQ D F0))
    (hsp : Submodule.span D.host.E (M : Set (WbQ D F0)) = ⊤) :
    Submodule.span D.host.E (lamC D F0 f M : Set (VS D).V) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  choose kα hkα hα using fun a => fi_nat_mul D (aaI_ne_zero D a) ((VS D).hT (f a) (vPr D F0 f v))
  choose kβ hkβ hβ using fun a => fi_nat_mul D (inv_ne_zero (aaI_ne_zero D a)) (star ((VS D).hT (F0.e a) v))
  obtain ⟨kM, hkM, hM⟩ := M_nat_smul D F0 M hsp
    (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X))
  set K : ℕ := (∏ a, kα a) * kM * ∏ a, kβ a with hK
  have hK0 : K ≠ 0 := by
    rw [hK]
    refine mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun a _ => hkα a) hkM)
      (Finset.prod_ne_zero_iff.2 fun a _ => hkβ a)
  have hdvd : ∀ {k : ℕ} {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} {x : D.host.E},
      k ∣ K → (k : D.host.E) * x ∈ I → (K : D.host.E) * x ∈ I := by
    rintro k I x ⟨m, hm⟩ hx
    rw [hm, Nat.cast_mul, mul_comm (k : D.host.E) (m : D.host.E), mul_assoc]
    have := fi_mul D (m : 𝓞 D.host.E) hx
    simpa using this
  have hmem : (K : 𝓞 D.host.E) • v ∈ lamC D F0 f M := by
    have hs : (K : 𝓞 D.host.E) • v = (K : D.host.E) • v := by
      rw [← algebraMap_smul D.host.E (K : 𝓞 D.host.E) v, map_natCast]
    rw [hs]
    refine ⟨fun a => ?_, ⟨(K : 𝓞 D.host.E) • ⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩, ?_, ?_⟩, fun a => ?_⟩
    · rw [map_smul, smul_eq_mul, star_mul, star_natCast, mul_comm]
      exact hdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ a) |>.trans (dvd_mul_left _ _)) (hβ a)
    · rw [vPr_smul]
      show (K : 𝓞 D.host.E) • vPr D F0 f v = _
      rw [← algebraMap_smul D.host.E (K : 𝓞 D.host.E), map_natCast]
    · rw [Submodule.Quotient.mk_smul]
      obtain ⟨m, hm⟩ : kM ∣ K := by
        rw [hK]; exact (dvd_mul_left _ _).mul_right _
      rw [hm, Nat.cast_mul, mul_comm, mul_smul]
      exact M.smul_mem _ hM
    · rw [vPr_smul, map_smul, smul_eq_mul]
      exact hdvd ((Finset.dvd_prod_of_mem _ (Finset.mem_univ a)).mul_right _ |>.mul_right _) (hα a)
  have hK' : (K : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hK0
  have e : v = (K : D.host.E)⁻¹ • ((K : 𝓞 D.host.E) • v) := by
    rw [← algebraMap_smul D.host.E (K : 𝓞 D.host.E) v, map_natCast, smul_smul, inv_mul_cancel₀ hK', one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem lattice_integral : LamLattice := by
  intro D u F0 f M hf hM
  exact ⟨lamC_fg D F0 f hf M hM.1.fg, lamC_span D F0 f hf M hM.1.span_eq_top⟩

end Lat

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
