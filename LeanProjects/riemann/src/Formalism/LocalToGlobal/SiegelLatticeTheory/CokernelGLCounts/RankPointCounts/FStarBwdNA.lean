import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.XLeOrthXplus
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

def SD (Λ : Submodule (𝓞 E) S.V) : Prop := ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (S.hT y x)

theorem hsw (x y : S.V) : S.hT y x = star (S.hT x y) := PI.ScalarPairDr.W.hT_swap S x y

theorem hT_smulL (a : E) (x v : S.V) : S.hT (a • x) v = star a * S.hT x v := by
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem oSmul (o : 𝓞 E) (x : S.V) : o • x = (o : E) • x := (algebraMap_smul E o x).symm

theorem coe_ne_zero {d : 𝓞 E} (hd : d ≠ 0) : (d : E) ≠ 0 := by
  intro h; apply hd; exact RingOfIntegers.coe_eq_zero_iff.1 h

theorem isInt_star {a : E} (h : IsIntegral ℤ a) : IsIntegral ℤ (star a) := by
  have h2 := h.map ((starRingEnd E : E →+* E).toIntAlgHom)
  exact h2

theorem intO {a : E} (h : IsIntegral ℤ a) : ∃ o : 𝓞 E, (o : E) = a := ⟨⟨a, h⟩, rfl⟩

theorem isInt_coe (o : 𝓞 E) : IsIntegral ℤ (o : E) := RingOfIntegers.isIntegral_coe o

variable {S}

theorem int_smul_mem {Λ : Submodule (𝓞 E) S.V} {c : E} (hc : IsIntegral ℤ c) {x : S.V} (hx : x ∈ Λ) :
    c • x ∈ Λ := by
  obtain ⟨o, rfl⟩ := intO hc
  rw [← oSmul]
  exact Λ.smul_mem o hx

theorem sd_int {Λ : Submodule (𝓞 E) S.V} (h : SD S Λ) {x y : S.V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    IsIntegral ℤ (S.hT y x) := (h x).1 hx y hy

variable (S)

theorem riesz (F : S.V →ₗ[E] E) : ∃ w, ∀ v, S.hT w v = F v := by
  classical
  let b := S.frame
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis S.hT S.nondeg b
  refine ⟨∑ j, star (F (b j)) • bs j, fun v => ?_⟩
  have key : S.hT (∑ j, star (F (b j)) • bs j) = F := by
    apply b.ext
    intro i
    rw [map_sum, LinearMap.sum_apply]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [hsw S (b i) (bs i), hbs i i]; simp
    · intro j _ hj
      rw [hsw S (b i) (bs j), hbs i j, if_neg (Ne.symm hj)]; simp
    · simp
  rw [key]

theorem mem_of_orth_orth (X : Submodule E S.V) {w : S.V} (hw : ∀ u ∈ orth S X, S.hT w u = 0) : w ∈ X := by
  have hle : X ≤ orth S (orth S X) := fun x hx => (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun u hu => by
    rw [hsw S x u, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 hu x hx, star_zero]
  have h1 := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S X
  have h2 := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (orth S X)
  have heq : X = orth S (orth S X) := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  rw [heq]
  exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun u hu => by rw [hsw S w u, hw u hu, star_zero]

theorem proj_quot (P : Submodule (𝓞 E) S.V) (hP : P.FG) (Z : Submodule E S.V) :
    Module.Projective (𝓞 E) (P ⧸ (Z.restrictScalars (𝓞 E)).comap P.subtype) := by
  set K := (Z.restrictScalars (𝓞 E)).comap P.subtype with hK
  have : Module.Finite (𝓞 E) P := Module.Finite.iff_fg.2 hP
  have htor : Submodule.torsion (𝓞 E) (P ⧸ K) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff q).1 hq
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [Submonoid.smul_def, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at ha
    have ha0 : ((a : 𝓞 E) : E) ≠ 0 := coe_ne_zero (nonZeroDivisors.coe_ne_zero a)
    have h1 : ((a : 𝓞 E) : E) • (x : S.V) ∈ Z := by
      have := ha
      simp only [hK, Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_smul,
        Submodule.restrictScalars_mem] at this
      rwa [oSmul] at this
    have h2 := Z.smul_mem ((a : 𝓞 E) : E)⁻¹ h1
    rw [smul_smul, inv_mul_cancel₀ ha0, one_smul] at h2
    simpa [hK] using h2
  have : Module.Flat (𝓞 E) (P ⧸ K) := (IsDedekindDomain.flat_iff_torsion_eq_bot).2 htor
  have : Module.FinitePresentation (𝓞 E) (P ⧸ K) := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem glift (P Q : Submodule (𝓞 E) S.V) (hP : P.FG) (Y Z : Submodule E S.V)
    (hPZ : ∀ x ∈ P, x ∈ Z → x ∈ Q) (hs : ∀ x ∈ P, ∃ y ∈ Q, y - x ∈ Y) :
    ∃ δ : P →ₗ[𝓞 E] S.V, (∀ x, δ x ∈ Y) ∧ (∀ x : P, (x : S.V) ∈ Z → δ x = 0) ∧
      (∀ x : P, (x : S.V) + δ x ∈ Q) := by
  classical
  set K := (Z.restrictScalars (𝓞 E)).comap P.subtype with hK
  have := proj_quot S P hP Z
  let dif : (P × Q) →ₗ[𝓞 E] S.V := Q.subtype ∘ₗ LinearMap.snd _ _ _ - P.subtype ∘ₗ LinearMap.fst _ _ _
  let R : Submodule (𝓞 E) (P × Q) := (Y.restrictScalars (𝓞 E)).comap dif
  let g : R →ₗ[𝓞 E] (P ⧸ K) := K.mkQ ∘ₗ LinearMap.fst _ _ _ ∘ₗ R.subtype
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    obtain ⟨y, hyQ, hy⟩ := hs x x.2
    refine ⟨⟨(x, ⟨y, hyQ⟩), ?_⟩, rfl⟩
    simpa [R, dif] using hy
  obtain ⟨s, hs'⟩ := Module.projective_lifting_property g LinearMap.id hg
  refine ⟨dif ∘ₗ R.subtype ∘ₗ s ∘ₗ K.mkQ, fun x => ?_, fun x hx => ?_, fun x => ?_⟩
  · exact (s (K.mkQ x)).2
  · have : K.mkQ x = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simpa [hK] using hx
    simp [this]
  · have hgt : g (s (K.mkQ x)) = K.mkQ x := LinearMap.congr_fun hs' (K.mkQ x)
    set t := s (K.mkQ x) with ht
    have h1 : x - (t : P × Q).1 ∈ K := by
      have h0 : K.mkQ (x - (t : P × Q).1) = 0 := by
        have : K.mkQ ((t : P × Q).1) = K.mkQ x := hgt
        rw [map_sub, this, sub_self]
      exact (Submodule.Quotient.mk_eq_zero K).1 h0
    have h2 : ((x : S.V) - ((t : P × Q).1 : S.V)) ∈ Q := by
      refine hPZ _ (P.sub_mem x.2 (t : P × Q).1.2) ?_
      simpa [hK] using h1
    have h3 : (x : S.V) + (dif ∘ₗ R.subtype ∘ₗ s ∘ₗ K.mkQ) x =
        ((t : P × Q).2 : S.V) + ((x : S.V) - ((t : P × Q).1 : S.V)) := by
      simp only [LinearMap.coe_comp, Function.comp_apply, ← ht, dif, LinearMap.sub_apply,
        Submodule.coe_subtype, LinearMap.snd_apply, LinearMap.fst_apply]
      abel
    rw [h3]
    exact Q.add_mem (t : P × Q).2.2 h2

theorem retract (P : Submodule (𝓞 E) S.V) (hP : P.FG) (Z : Submodule E S.V) :
    ∃ π : P →ₗ[𝓞 E] S.V, (∀ x, π x ∈ P ∧ π x ∈ Z) ∧ ∀ x : P, (x : S.V) ∈ Z → π x = x := by
  classical
  set K := (Z.restrictScalars (𝓞 E)).comap P.subtype with hK
  have := proj_quot S P hP Z
  obtain ⟨s, hs'⟩ := Module.projective_lifting_property K.mkQ LinearMap.id K.mkQ_surjective
  refine ⟨P.subtype ∘ₗ (LinearMap.id - s ∘ₗ K.mkQ), fun x => ⟨?_, ?_⟩, fun x hx => ?_⟩
  · exact (x - s (K.mkQ x)).2
  · have h1 : x - s (K.mkQ x) ∈ K := by
      have h0 : K.mkQ (x - s (K.mkQ x)) = 0 := by
        have : K.mkQ (s (K.mkQ x)) = K.mkQ x := LinearMap.congr_fun hs' (K.mkQ x)
        rw [map_sub, this, sub_self]
      exact (Submodule.Quotient.mk_eq_zero K).1 h0
    simpa [hK] using h1
  · have : K.mkQ x = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simpa [hK] using hx
    simp [this]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA
