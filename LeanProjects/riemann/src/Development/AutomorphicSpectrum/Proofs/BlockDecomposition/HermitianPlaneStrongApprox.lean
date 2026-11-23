import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

section Places

variable (F : Type) [Field F] [NumberField F]

abbrev Pl : Type := InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)

variable {F}

def Kp : Pl F → Type
  | .inl w => w.Completion
  | .inr v => v.adicCompletion F

instance (u : Pl F) : Field (Kp u) :=
  match u with
  | .inl w => inferInstanceAs (Field w.Completion)
  | .inr v => inferInstanceAs (Field (v.adicCompletion F))

instance (u : Pl F) : Algebra F (Kp u) :=
  match u with
  | .inl w => inferInstanceAs (Algebra F w.Completion)
  | .inr v => inferInstanceAs (Algebra F (v.adicCompletion F))

instance (u : Pl F) : TopologicalSpace (Kp u) :=
  match u with
  | .inl w => inferInstanceAs (TopologicalSpace w.Completion)
  | .inr v => inferInstanceAs (TopologicalSpace (v.adicCompletion F))

def proj : (u : Pl F) → AF F →ₐ[F] Kp u
  | .inl w => (Pi.evalAlgHom F (fun w : InfinitePlace F => w.Completion) w).comp (fstA F)
  | .inr v => (evalV F v).comp (sndA F)

open Classical in

def inc : (u : Pl F) → Kp u → AF F
  | .inl w => fun y => pairA F (Pi.single w y) 0
  | .inr v => fun y => pairA F 0 (singleV F v y)

instance (u : Pl F) : IsTopologicalRing (Kp u) :=
  match u with
  | .inl w => inferInstanceAs (IsTopologicalRing w.Completion)
  | .inr v => inferInstanceAs (IsTopologicalRing (v.adicCompletion F))

instance (u : Pl F) : T2Space (Kp u) :=
  match u with
  | .inl w => inferInstanceAs (T2Space w.Completion)
  | .inr v => inferInstanceAs (T2Space (v.adicCompletion F))

instance (u : Pl F) : IsTopologicalDivisionRing (Kp u) :=
  match u with
  | .inl w => inferInstanceAs (IsTopologicalDivisionRing w.Completion)
  | .inr v => inferInstanceAs (IsTopologicalDivisionRing (v.adicCompletion F))

theorem continuous_inc (u : Pl F) : Continuous (inc u) := by
  classical
  cases u with
  | inl w =>
    exact (continuous_single w).prodMk continuous_const
  | inr v =>
    have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
      Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
    let f : Fv F v → RestrictedProduct (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
        (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (Filter.principal {v}ᶜ) :=
      fun a => ⟨Pi.single v a, fun u hu => by
        rw [Set.mem_setOf_eq, Pi.single_eq_of_ne hu]; exact zero_mem _⟩
    have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
    have h2 : Continuous (singleV F v) := by
      refine ((RestrictedProduct.continuous_inclusion hS).comp hf).congr fun a => ?_
      refine Subtype.ext (funext fun u => ?_)
      by_cases h : u = v
      · subst h
        exact (Pi.single_eq_same u a).trans (StrongApprox.evalV_single_same u a).symm
      · exact (Pi.single_eq_of_ne h a).trans (StrongApprox.evalV_single_ne h a).symm
    exact continuous_const.prodMk h2

theorem proj_inc_same (u : Pl F) (y : Kp u) : proj u (inc u y) = y := by
  classical
  cases u with
  | inl w => exact Pi.single_eq_same w y
  | inr v => exact Pi.single_eq_same v y

theorem proj_inc_ne {u u' : Pl F} (h : u' ≠ u) (y : Kp u) : proj u' (inc u y) = 0 := by
  classical
  cases u with
  | inl w =>
    cases u' with
    | inl w' => exact Pi.single_eq_of_ne (fun h' => h (congrArg Sum.inl h')) y
    | inr v' => rfl
  | inr v =>
    cases u' with
    | inl w' => rfl
    | inr v' => exact Pi.single_eq_of_ne (fun h' => h (congrArg Sum.inr h')) y

theorem adele_ext {a b : AF F} (h : ∀ u : Pl F, proj u a = proj u b) : a = b := by
  exact Prod.ext (funext fun w => h (Sum.inl w)) (Subtype.ext (funext fun v => h (Sum.inr v)))

end Places

section Quat

variable {F : Type} [Field F]

abbrev Q (d β : F) (R : Type) [CommRing R] [Algebra F R] : Type :=
  ℍ[R, algebraMap F R d, 0, algebraMap F R β]

variable {d β : F} {R : Type} [CommRing R] [Algebra F R]

def qn (x : Q d β R) : R :=
  x.re ^ 2 - algebraMap F R d * x.imI ^ 2 - algebraMap F R β * x.imJ ^ 2 +
    algebraMap F R d * algebraMap F R β * x.imK ^ 2

def qtr (x : Q d β R) : R := 2 * x.re

def qmap {R' : Type} [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') : Q d β R →+* Q d β R' where
  toFun x := ⟨f x.re, f x.imI, f x.imJ, f x.imK⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

def rat : Q d β F →+* Q d β R := qmap (Algebra.ofId F R)

section Top

variable [TopologicalSpace R]

instance qTop : TopologicalSpace (Q d β R) :=
  TopologicalSpace.induced (QuaternionAlgebra.equivProd _ _ _) inferInstance

def qHomeo : Q d β R ≃ₜ R × R × R × R :=
  (QuaternionAlgebra.equivProd _ _ _).toHomeomorphOfIsInducing ⟨rfl⟩

theorem continuous_re : Continuous fun x : Q d β R => x.re := by
  have h := continuous_induced_dom
    (f := (QuaternionAlgebra.equivProd (algebraMap F R d) 0 (algebraMap F R β) : Q d β R → R × R × R × R))
    (t := inferInstance)
  exact h.fst
theorem continuous_imI : Continuous fun x : Q d β R => x.imI := by
  have h := continuous_induced_dom
    (f := (QuaternionAlgebra.equivProd (algebraMap F R d) 0 (algebraMap F R β) : Q d β R → R × R × R × R))
    (t := inferInstance)
  exact h.snd.fst
theorem continuous_imJ : Continuous fun x : Q d β R => x.imJ := by
  have h := continuous_induced_dom
    (f := (QuaternionAlgebra.equivProd (algebraMap F R d) 0 (algebraMap F R β) : Q d β R → R × R × R × R))
    (t := inferInstance)
  exact h.snd.snd.fst
theorem continuous_imK : Continuous fun x : Q d β R => x.imK := by
  have h := continuous_induced_dom
    (f := (QuaternionAlgebra.equivProd (algebraMap F R d) 0 (algebraMap F R β) : Q d β R → R × R × R × R))
    (t := inferInstance)
  exact h.snd.snd.snd

theorem continuous_q_iff {X : Type*} [TopologicalSpace X] {f : X → Q d β R} :
    Continuous f ↔ Continuous (fun x => (f x).re) ∧ Continuous (fun x => (f x).imI) ∧
      Continuous (fun x => (f x).imJ) ∧ Continuous (fun x => (f x).imK) := by
  constructor
  · intro hf
    exact ⟨continuous_re.comp hf, continuous_imI.comp hf, continuous_imJ.comp hf, continuous_imK.comp hf⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact continuous_induced_rng.2 (h1.prodMk (h2.prodMk (h3.prodMk h4)))

instance [IsTopologicalRing R] : IsTopologicalRing (Q d β R) where
  continuous_add := by
    rw [continuous_q_iff]
    simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add, QuaternionAlgebra.imK_add]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · first
      | exact (continuous_re.comp continuous_fst).add (continuous_re.comp continuous_snd)
      | exact (continuous_imI.comp continuous_fst).add (continuous_imI.comp continuous_snd)
      | exact (continuous_imJ.comp continuous_fst).add (continuous_imJ.comp continuous_snd)
      | exact (continuous_imK.comp continuous_fst).add (continuous_imK.comp continuous_snd)
  continuous_mul := by
    have a1 := (continuous_re (d := d) (β := β) (R := R)).comp (continuous_fst (X := Q d β R) (Y := Q d β R))
    have a2 := (continuous_imI (d := d) (β := β) (R := R)).comp (continuous_fst (X := Q d β R) (Y := Q d β R))
    have a3 := (continuous_imJ (d := d) (β := β) (R := R)).comp (continuous_fst (X := Q d β R) (Y := Q d β R))
    have a4 := (continuous_imK (d := d) (β := β) (R := R)).comp (continuous_fst (X := Q d β R) (Y := Q d β R))
    have b1 := (continuous_re (d := d) (β := β) (R := R)).comp (continuous_snd (X := Q d β R) (Y := Q d β R))
    have b2 := (continuous_imI (d := d) (β := β) (R := R)).comp (continuous_snd (X := Q d β R) (Y := Q d β R))
    have b3 := (continuous_imJ (d := d) (β := β) (R := R)).comp (continuous_snd (X := Q d β R) (Y := Q d β R))
    have b4 := (continuous_imK (d := d) (β := β) (R := R)).comp (continuous_snd (X := Q d β R) (Y := Q d β R))
    simp only [Function.comp_def] at a1 a2 a3 a4 b1 b2 b3 b4
    rw [continuous_q_iff]
    simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> fun_prop
  continuous_neg := by
    rw [continuous_q_iff]
    simp only [QuaternionAlgebra.re_neg, QuaternionAlgebra.imI_neg, QuaternionAlgebra.imJ_neg, QuaternionAlgebra.imK_neg]
    exact ⟨continuous_re.neg, continuous_imI.neg, continuous_imJ.neg, continuous_imK.neg⟩

end Top

end Quat

section QuatAlg

variable {F : Type} [Field F] {d β : F} {R : Type} [CommRing R] [Algebra F R]

theorem qn_mul (x y : Q d β R) : qn (x * y) = qn x * qn y := by
  simp only [qn, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]
  ring

theorem qn_one : qn (1 : Q d β R) = 1 := by simp [qn]

theorem qn_star (x : Q d β R) : qn (star x) = qn x := by
  simp only [qn, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star]
  ring

theorem mul_star_eq (x : Q d β R) : x * star x = algebraMap R (Q d β R) (qn x) := by
  ext <;> simp only [QuaternionAlgebra.algebraMap_eq, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, qn] <;> ring

theorem star_mul_eq (x : Q d β R) : star x * x = algebraMap R (Q d β R) (qn x) := by
  ext <;> simp only [QuaternionAlgebra.algebraMap_eq, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, qn] <;> ring

theorem qn_qmap {R' : Type} [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') (x : Q d β R) :
    qn (qmap f x) = f (qn x) := by
  simp [qn, qmap]

end QuatAlg

section Adelic

variable {F : Type} [Field F] [NumberField F] {d β : F}

def Ov (v : HeightOneSpectrum (𝓞 F)) : Set (Kp (Sum.inr v : Pl F)) :=
  (v.adicCompletionIntegers F : Set (v.adicCompletion F))

def IntQ (v : HeightOneSpectrum (𝓞 F)) (x : Q d β (Kp (Sum.inr v : Pl F))) : Prop :=
  x.re ∈ Ov v ∧ x.imI ∈ Ov v ∧ x.imJ ∈ Ov v ∧ x.imK ∈ Ov v

def SuppAt (d β : F) (T : Set (Pl F)) : Set (Q d β (AF F)) :=
  {g | qn g = 1 ∧ ∀ u, u ∉ T → qmap (proj u) g = 1}

def SAQ (d β : F) (s : Pl F) : Set (Q d β (AF F)) :=
  {x | ∃ γ : Q d β F, qn γ = 1 ∧ ∃ h ∈ SuppAt d β {s}, x = rat γ * h}

def QSA (d β : F) (s : Pl F) : Prop :=
  ∀ T : Finset (Pl F), SuppAt d β (T : Set (Pl F)) ⊆ closure (SAQ d β s)

end Adelic

section Two

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def J2 (E : Type) [Field E] [Algebra F E] (β : F) : Matrix (Fin 2) (Fin 2) E :=
  !![1, 0; 0, -algebraMap F E β]

def HermitianPlaneStrongApprox (σ : E →ₐ[F] E) (β : F) : Prop :=
  ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε →
    ¬ IsCompact (SUSupp σ (J2 E β) ε) →
    ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (δ : AF F), IsPlacesIdem T₁ T₂ δ →
      SUSupp σ (J2 E β) δ ⊆ closure (Sa2.SASet σ (J2 E β) ε)

end Two

end GlobalTheory.CompanionTheory.PlaneSA
