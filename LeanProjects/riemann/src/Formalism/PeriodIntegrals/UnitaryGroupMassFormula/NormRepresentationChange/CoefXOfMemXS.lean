import Mathlib
import Formalism.PeriodIntegrals.PairValDefs
import Formalism.PeriodIntegrals.NormRepChange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NlamFrameMem

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem coefX_add (F : FlagG S r T) {v w : S.V} (hv : v ∈ F.X) (hw : w ∈ F.X) (a : Fin r) :
    F.coefX (v + w) a = F.coefX v a + F.coefX w a := by
  have hv' : v ∈ Submodule.span E (Set.range F.e) := hv
  have hw' : w ∈ Submodule.span E (Set.range F.e) := hw
  have hvw' : v + w ∈ Submodule.span E (Set.range F.e) := Submodule.add_mem _ hv' hw'
  simp only [Formalism.MainNotions.S.FlagG.coefX, dif_pos hv', dif_pos hw', dif_pos hvw']
  rw [show (⟨v + w, hvw'⟩ : Submodule.span E (Set.range F.e)) = ⟨v, hv'⟩ + ⟨w, hw'⟩ from rfl, map_add,
    Finsupp.add_apply]

theorem coefX_smul (F : FlagG S r T) {v : S.V} (hv : v ∈ F.X) (c : E) (a : Fin r) :
    F.coefX (c • v) a = c * F.coefX v a := by
  have hv' : v ∈ Submodule.span E (Set.range F.e) := hv
  have hcv' : c • v ∈ Submodule.span E (Set.range F.e) := Submodule.smul_mem _ c hv'
  simp only [Formalism.MainNotions.S.FlagG.coefX, dif_pos hv', dif_pos hcv']
  rw [show (⟨c • v, hcv'⟩ : Submodule.span E (Set.range F.e)) = c • ⟨v, hv'⟩ from rfl, map_smul,
    Finsupp.smul_apply, smul_eq_mul]

theorem coefX_smul_e (F : FlagG S r T) (c : E) (a' a : Fin r) :
    F.coefX (c • F.e a') a = if a' = a then c else 0 := by
  have he : F.e a' ∈ Submodule.span E (Set.range F.e) := Submodule.subset_span ⟨a', rfl⟩
  have hce : c • F.e a' ∈ Submodule.span E (Set.range F.e) := Submodule.smul_mem _ c he
  simp only [Formalism.MainNotions.S.FlagG.coefX, dif_pos hce]
  rw [show (⟨c • F.e a', hce⟩ : Submodule.span E (Set.range F.e)) = c • ⟨F.e a', he⟩ from rfl, map_smul,
    F.e_indep.repr_eq_single a' ⟨F.e a', he⟩ rfl, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem coefX_e (F : FlagG S r T) (a' a : Fin r) : F.coefX (F.e a') a = if a' = a then 1 else 0 := by
  simpa using coefX_smul_e F 1 a' a

theorem coefX_zero (F : FlagG S r T) (a : Fin r) : F.coefX 0 a = 0 := by
  have h0 : (0 : S.V) ∈ Submodule.span E (Set.range F.e) := Submodule.zero_mem _
  simp only [Formalism.MainNotions.S.FlagG.coefX, dif_pos h0]
  rw [show (⟨0, h0⟩ : Submodule.span E (Set.range F.e)) = 0 from rfl, map_zero, Finsupp.zero_apply]

theorem e_mem_X (F : FlagG S r T) (a : Fin r) : F.e a ∈ F.X := by
  exact Submodule.subset_span ⟨a, rfl⟩

theorem nlam_mem {Λ : Submodule (𝓞 E) S.V} {G : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ G)
    {v : S.V} (hv : v ∈ Λ) : n v ∈ Λ := by
  obtain ⟨⟨-, hmap⟩, -, -⟩ := hn
  rw [← hmap]
  exact Submodule.mem_map_of_mem hv

theorem nlam_X {Λ : Submodule (𝓞 E) S.V} {G : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ G)
    {v : S.V} (hv : v ∈ G.fl.X) : n v ∈ G.fl.X := by
  obtain ⟨-, hflag, -⟩ := hn
  have h1 : v ∈ Xflag G (r + 1) := by
    show v ∈ G.fl.Xa (r + 1)
    refine Submodule.span_mono ?_ hv
    rintro _ ⟨i, rfl⟩
    exact ⟨i, show i.1 < r + 1 by have := i.2; omega, rfl⟩
  have h2 := hflag r v h1
  have h3 : n v - v ∈ G.fl.X := by
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩
  have h4 := G.fl.X.add_mem h3 hv
  rwa [sub_add_cancel] at h4

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fi_zero {D : D7} (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : (0 : D.host.E) ∈ I := by
  exact (I : Submodule (𝓞 D.host.E) D.host.E).zero_mem

theorem fi_add {D : D7} (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) {x y : D.host.E}
    (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by
  exact (I : Submodule (𝓞 D.host.E) D.host.E).add_mem hx hy

theorem fi_smul {D : D7} (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (o : 𝓞 D.host.E)
    {x : D.host.E} (hx : x ∈ I) : o • x ∈ I := by
  exact (I : Submodule (𝓞 D.host.E) D.host.E).smul_mem o hx

abbrev aaI (D : D7) (a : Fin D.R.rS) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))

theorem coefX_of_mem_XS (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {v : (VS D).V}
    (hv : v ∈ XS D F0) : v ∈ F0.X ∧ ∀ a, F0.coefX v a ∈ aaI D a := by
  unfold XS at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, x, hx, rfl⟩ := hy
    refine ⟨F0.X.smul_mem x (e_mem_X F0 a), fun b => ?_⟩
    rw [coefX_smul_e]
    split_ifs with h
    · subst h
      exact hx
    · exact fi_zero _
  | zero => exact ⟨F0.X.zero_mem, fun a => by rw [coefX_zero]; exact fi_zero _⟩
  | add y z _ _ hy hz =>
    refine ⟨F0.X.add_mem hy.1 hz.1, fun a => ?_⟩
    rw [coefX_add F0 hy.1 hz.1]
    exact fi_add _ (hy.2 a) (hz.2 a)
  | smul o y _ hy =>
    have e : o • y = (o : D.host.E) • y := (algebraMap_smul D.host.E o y).symm
    refine ⟨by rw [e]; exact F0.X.smul_mem _ hy.1, fun a => ?_⟩
    rw [e, coefX_smul F0 hy.1]
    exact fi_smul _ o (hy.2 a)

theorem ddS_ne_zero (D : D7) : ddS D ≠ 0 := by
  unfold ddS
  have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    first
    | exact FaithfulSMul.algebraMap_injective _ _
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective hinj]
  exact differentIdeal_ne_bot

theorem frac_lemma (D : D7) (c : D.host.E) (m : ℤ) (h : ∀ x ∈ ddS D ^ m, x * c ∈ ddS D ^ (m - 1)) :
    ∀ δ ∈ ddS D, ∃ o : 𝓞 D.host.E, (o : D.host.E) = c * δ := by
  intro δ hδ
  have hne := ddS_ne_zero D
  have hsplit : ddS D = ddS D ^ m * ddS D ^ (1 - m) := by
    rw [← zpow_add₀ hne, show m + (1 - m) = 1 by ring, zpow_one]
  have h1 : ddS D ^ (m - 1) * ddS D ^ (1 - m) = 1 := by
    rw [← zpow_add₀ hne, show m - 1 + (1 - m) = 0 by ring, zpow_zero]
  rw [hsplit] at hδ
  have hc : c * δ ∈ ddS D ^ (m - 1) * ddS D ^ (1 - m) := by
    refine FractionalIdeal.mul_induction_on hδ ?_ ?_
    · intro x hx y hy
      have e : c * (x * y) = (x * c) * y := by ring
      rw [e]
      exact FractionalIdeal.mul_mem_mul (h x hx) hy
    · intro x y hx hy
      rw [mul_add]
      exact ((ddS D ^ (m - 1) * ddS D ^ (1 - m) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E).add_mem hx hy
  rw [h1] at hc
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).mp hc
  exact ⟨o, ho⟩

end PI.NRCW
