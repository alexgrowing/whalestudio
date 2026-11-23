import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.SmoothKZ

open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

set_option linter.unusedSectionVars false

theorem mem_of_hasDerivAt {X : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W]
    {c : ℝ → X → ℂ} (hc : ∀ t, c t ∈ W) {d : X → ℂ}
    (hd : ∀ x, HasDerivAt (fun t => c t x) (d x) 0) : d ∈ W := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_eval_eq_zero W

  have key : ∀ y : X, ∃ w ∈ W, ∀ x ∈ insert y S, w x = d x := by
    intro y
    let T : Finset X := insert y S
    let ev : (X → ℂ) →ₗ[ℂ] (T → ℂ) :=
      { toFun := fun f x => f x
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hR : IsClosed ((W.map ev : Submodule ℂ _) : Set (T → ℂ)) :=
      Submodule.closed_of_finiteDimensional _
    have hder : HasDerivAt (fun t => ev (c t)) (ev d) 0 :=
      hasDerivAt_pi.2 fun x => hd x
    have hlim := hasDerivAt_iff_tendsto_slope.1 hder
    have hmem : ev d ∈ W.map ev := by
      refine hR.mem_of_tendsto hlim (Eventually.of_forall fun t => ?_)
      rw [slope_def_module]
      exact Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ ⟨_, hc t, rfl⟩ ⟨_, hc 0, rfl⟩)
    obtain ⟨w, hw, hwd⟩ := hmem
    exact ⟨w, hw, fun x hx => congrFun hwd ⟨x, hx⟩⟩
  rcases isEmpty_or_nonempty X with hX | ⟨⟨y₀⟩⟩
  · have : d = 0 := funext fun x => (IsEmpty.false x).elim
    rw [this]
    exact W.zero_mem
  choose w hwW hwd using key
  have huniq : ∀ y, w y = w y₀ := by
    intro y
    have := hS _ (W.sub_mem (hwW y) (hwW y₀)) fun x hx => by
      rw [Pi.sub_apply, hwd y x (Finset.mem_insert_of_mem hx), hwd y₀ x (Finset.mem_insert_of_mem hx),
        sub_self]
    exact sub_eq_zero.1 this
  have : d = w y₀ := funext fun y => by
    rw [← huniq y, hwd y y (Finset.mem_insert_self y S)]
  rw [this]
  exact hwW y₀

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open Reduction

theorem smoothKZ_le_archSmooth : smoothKZ K n ≤ archSmooth K n := fun _ hφ => hφ.isSmooth.1

def toArchSmooth : smoothKZ K n →ₗ[ℂ] archSmooth K n := Submodule.inclusion smoothKZ_le_archSmooth

@[simp] theorem coe_toArchSmooth (φ : smoothKZ K n) :
    ((toArchSmooth φ : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) = φ := rfl

variable (K n) in

def uActionKZ : UEnv K n →ₐ[ℝ] Module.End ℂ (smoothKZ K n) where
  toFun u := LinearMap.codRestrict (smoothKZ K n)
    ((archSmooth K n).subtype ∘ₗ uAction u ∘ₗ toArchSmooth) fun φ => φ.2.uAction u
  map_one' := LinearMap.ext fun φ => Subtype.ext (by
    show ((uAction 1 (toArchSmooth φ) : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) = φ
    rw [map_one]; rfl)
  map_mul' u v := LinearMap.ext fun φ => Subtype.ext (by
    show ((uAction (u * v) (toArchSmooth φ) : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) =
      ((uAction u (uAction v (toArchSmooth φ)) : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ)
    rw [map_mul]; rfl)
  map_zero' := LinearMap.ext fun φ => Subtype.ext (by
    show ((uAction 0 (toArchSmooth φ) : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) = 0
    rw [map_zero]; rfl)
  map_add' u v := LinearMap.ext fun φ => Subtype.ext (by
    show ((uAction (u + v) (toArchSmooth φ) : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) = _
    rw [map_add]; rfl)
  commutes' r := LinearMap.ext fun φ => Subtype.ext (by
    show ((uAction (algebraMap ℝ (UEnv K n) r) (toArchSmooth φ) : archSmooth K n) :
      AdelicGLn.AdelicGL K n → ℂ) = _
    rw [AlgHom.commutes]; rfl)

@[simp] theorem coe_uActionKZ (u : UEnv K n) (φ : smoothKZ K n) :
    ((uActionKZ K n u φ : smoothKZ K n) : AdelicGLn.AdelicGL K n → ℂ) =
      ((uAction u (toArchSmooth φ) : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) := rfl

variable (K n) in

def finRepKZ : Representation ℂ (AdelicGLn.FiniteAdelicGL K n) (smoothKZ K n) where
  toFun h := (rightTranslateL (finEmb K n h)).restrict fun _ hφ => hφ.rightTranslate_finEmb h
  map_one' := LinearMap.ext fun φ => Subtype.ext (funext fun g => by
    simp [GroundTheory.Automorphic.rightTranslate])
  map_mul' h₁ h₂ := LinearMap.ext fun φ => Subtype.ext (funext fun g => by
    show (φ : AdelicGLn.AdelicGL K n → ℂ) (g * finEmb K n (h₁ * h₂)) =
      (φ : AdelicGLn.AdelicGL K n → ℂ) (g * finEmb K n h₁ * finEmb K n h₂)
    rw [map_mul, mul_assoc])

variable (K n) in

def archCompactRepKZ : Representation ℂ (archCompact K n) (smoothKZ K n) where
  toFun k := (rightTranslateL (infEmb K n k)).restrict fun _ hφ => hφ.rightTranslate_infEmb k.2
  map_one' := LinearMap.ext fun φ => Subtype.ext (funext fun g => by
    simp [GroundTheory.Automorphic.rightTranslate])
  map_mul' k₁ k₂ := LinearMap.ext fun φ => Subtype.ext (funext fun g => by
    show (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n ((k₁ * k₂ : archCompact K n) : archGroup K n)) =
      (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n k₁ * infEmb K n k₂)
    rw [Subgroup.coe_mul, map_mul, mul_assoc])

@[simp] theorem coe_finRepKZ (h : AdelicGLn.FiniteAdelicGL K n) (φ : smoothKZ K n) :
    ((finRepKZ K n h φ : smoothKZ K n) : AdelicGLn.AdelicGL K n → ℂ) =
      rightTranslate (finEmb K n h) (φ : AdelicGLn.AdelicGL K n → ℂ) := rfl

@[simp] theorem coe_archCompactRepKZ (k : archCompact K n) (φ : smoothKZ K n) :
    ((archCompactRepKZ K n k φ : smoothKZ K n) : AdelicGLn.AdelicGL K n → ℂ) =
      rightTranslate (infEmb K n k) (φ : AdelicGLn.AdelicGL K n → ℂ) := rfl

theorem uActionKZ_finRepKZ (u : UEnv K n) (h : AdelicGLn.FiniteAdelicGL K n) (φ : smoothKZ K n) :
    uActionKZ K n u (finRepKZ K n h φ) = finRepKZ K n h (uActionKZ K n u φ) := by
  apply Subtype.ext
  have := congrArg Subtype.val (uAction_rtFin u h (toArchSmooth φ))
  exact this

theorem archCompactRepKZ_uActionKZ (k : archCompact K n) (u : UEnv K n) (φ : smoothKZ K n) :
    archCompactRepKZ K n k (uActionKZ K n u φ) =
      uActionKZ K n ((isExpLieAlgebra K n).AdU (k : archGroup K n) u) (archCompactRepKZ K n k φ) := by
  apply Subtype.ext
  have := congrArg Subtype.val (uAction_rtInf ((isExpLieAlgebra K n).AdU (k : archGroup K n) u)
    (k : archGroup K n) (toArchSmooth φ))
  rw [IsExpLieAlgebra.AdU_inv_apply] at this
  exact this.symm

theorem archCompactRepKZ_finRepKZ (k : archCompact K n) (h : AdelicGLn.FiniteAdelicGL K n)
    (φ : smoothKZ K n) :
    archCompactRepKZ K n k (finRepKZ K n h φ) = finRepKZ K n h (archCompactRepKZ K n k φ) := by
  apply Subtype.ext
  funext g
  simp only [coe_finRepKZ, coe_archCompactRepKZ, GroundTheory.Automorphic.rightTranslate, mul_assoc,
    infEmb_mul_finEmb_comm]

theorem exists_linearMap_eval_eq (W : Submodule ℂ (smoothKZ K n)) [FiniteDimensional ℂ W]
    (φ : Module.Dual ℂ (smoothKZ K n)) :
    ∃ (S : Finset (AdelicGLn.AdelicGL K n)) (ψ : (S → ℂ) →ₗ[ℂ] ℂ),
      ∀ w ∈ W, φ w = ψ (fun x => (w : AdelicGLn.AdelicGL K n → ℂ) x) := by
  classical
  set Wf := W.map (smoothKZ K n).subtype
  obtain ⟨S, hS⟩ := exists_finset_eval_eq_zero Wf
  let ev : W →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun w x => ((w : smoothKZ K n) : AdelicGLn.AdelicGL K n → ℂ) x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have h0 := hS _ ⟨(w : smoothKZ K n), w.2, rfl⟩ fun x hx => congrFun hw ⟨x, hx⟩
    exact Subtype.ext (Subtype.ext h0)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (K := ℂ) (V := W) (V' := S → ℂ) ev hker
  refine ⟨S, φ ∘ₗ W.subtype ∘ₗ g, fun w hw => ?_⟩
  have : g (ev ⟨w, hw⟩) = ⟨w, hw⟩ := by rw [← LinearMap.comp_apply, hg, LinearMap.id_apply]
  show φ w = φ (W.subtype (g (ev ⟨w, hw⟩)))
  rw [this]
  rfl

theorem continuous_archSlice {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsArchSmooth φ)
    (g : AdelicGLn.AdelicGL K n) : Continuous (archSlice φ g) := by
  letI := (isExpLieAlgebra K n).chartedSpace
  exact (hφ g).continuous

theorem finiteDimensional_span_archCompactRepKZ (v : smoothKZ K n) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : archCompact K n => archCompactRepKZ K n k v)) := by
  set Wf := Submodule.span ℂ (range fun k : (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
    rightTranslate (k : AdelicGLn.AdelicGL K n) (v : AdelicGLn.AdelicGL K n → ℂ))
  have : FiniteDimensional ℂ Wf := v.2.isKFinite
  set W := Submodule.span ℂ (range fun k : archCompact K n => archCompactRepKZ K n k v)
  have hW : ∀ w : W, ((w : smoothKZ K n) : AdelicGLn.AdelicGL K n → ℂ) ∈ Wf := by
    rintro ⟨w, hw⟩
    refine Submodule.span_induction
      (p := fun w _ => ((w : smoothKZ K n) : AdelicGLn.AdelicGL K n → ℂ) ∈ Wf) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨⟨infEmb K n k, k.2⟩, rfl⟩
    · exact Wf.zero_mem
    · intro x y _ _ hx hy
      exact Wf.add_mem hx hy
    · intro c x _ hx
      exact Wf.smul_mem c hx
  refine FiniteDimensional.of_injective
    (((smoothKZ K n).subtype ∘ₗ W.subtype).codRestrict Wf hW) ?_
  intro x y hxy
  have := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext this)

theorem hasContinuousCoeff_archCompactRepKZ :
    Representation.HasContinuousCoeff (archCompactRepKZ K n) := by
  intro φ v
  have := finiteDimensional_span_archCompactRepKZ v
  obtain ⟨S, ψ, hψ⟩ := exists_linearMap_eval_eq
    (Submodule.span ℂ (range fun k : archCompact K n => archCompactRepKZ K n k v)) φ
  have e : (fun k : archCompact K n => φ (archCompactRepKZ K n k v)) =
      fun k : archCompact K n =>
        ψ (fun x : S => archSlice (v : AdelicGLn.AdelicGL K n → ℂ) x (k : archGroup K n)) :=
    funext fun k => hψ _ (Submodule.subset_span ⟨k, rfl⟩)
  rw [e]
  refine (LinearMap.continuous_of_finiteDimensional ψ).comp (continuous_pi fun x => ?_)
  exact (continuous_archSlice v.2.isSmooth.1 x).comp continuous_subtype_val

theorem hasDerivAt_uActionKZ_ι (X : archLie K n) (v : smoothKZ K n) (x : AdelicGLn.AdelicGL K n) :
    HasDerivAt (fun t : ℝ => (v : AdelicGLn.AdelicGL K n → ℂ)
        (x * infEmb K n ((isExpLieAlgebra K n).expG (t • X))))
      (((uActionKZ K n (UniversalEnvelopingAlgebra.ι ℝ ((isExpLieAlgebra K n).toLie X)) v :
        smoothKZ K n) : AdelicGLn.AdelicGL K n → ℂ) x) 0 := by
  have h := (isExpLieAlgebra K n).hasDerivAt_rightDeriv (v.2.isSmooth.1 x) X 1
  simp only [one_mul] at h
  rw [coe_uActionKZ, uAction_ι_apply]
  exact h

theorem hasDerivAt_archCompactRepKZ (X : archLie K n)
    (hX : ∀ t : ℝ, (isExpLieAlgebra K n).expG (t • X) ∈ archCompact K n)
    (φ : Module.Dual ℂ (smoothKZ K n)) (v : smoothKZ K n) :
    HasDerivAt (fun t : ℝ => φ (archCompactRepKZ K n ⟨(isExpLieAlgebra K n).expG (t • X), hX t⟩ v))
      (φ (uActionKZ K n (UniversalEnvelopingAlgebra.ι ℝ ((isExpLieAlgebra K n).toLie X)) v)) 0 := by
  set W := Submodule.span ℂ (range fun k : archCompact K n => archCompactRepKZ K n k v)
  have : FiniteDimensional ℂ W := finiteDimensional_span_archCompactRepKZ v
  set Xv := uActionKZ K n (UniversalEnvelopingAlgebra.ι ℝ ((isExpLieAlgebra K n).toLie X)) v
  have hmem : Xv ∈ W := by
    have hf : ((Xv : smoothKZ K n) : AdelicGLn.AdelicGL K n → ℂ) ∈ W.map (smoothKZ K n).subtype :=
      mem_of_hasDerivAt (W.map (smoothKZ K n).subtype)
        (c := fun t => ((archCompactRepKZ K n ⟨(isExpLieAlgebra K n).expG (t • X), hX t⟩ v :
          smoothKZ K n) : AdelicGLn.AdelicGL K n → ℂ))
        (fun t => ⟨_, Submodule.subset_span ⟨_, rfl⟩, rfl⟩)
        (hasDerivAt_uActionKZ_ι X v)
    obtain ⟨w, hw, e⟩ := hf
    rwa [show w = Xv from Subtype.ext e] at hw
  obtain ⟨S, ψ, hψ⟩ := exists_linearMap_eval_eq W φ
  have hpi : HasDerivAt (fun t : ℝ => fun x : S => (v : AdelicGLn.AdelicGL K n → ℂ)
      (x * infEmb K n ((isExpLieAlgebra K n).expG (t • X))))
      (fun x : S => ((Xv : smoothKZ K n) : AdelicGLn.AdelicGL K n → ℂ) x) 0 :=
    hasDerivAt_pi.2 fun x => hasDerivAt_uActionKZ_ι X v x
  have hcomp := ((LinearMap.toContinuousLinearMap ψ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hpi
  have e1 : ((LinearMap.toContinuousLinearMap ψ).restrictScalars ℝ)
      (fun x : S => ((Xv : smoothKZ K n) : AdelicGLn.AdelicGL K n → ℂ) x) = φ Xv := by
    rw [hψ _ hmem]
    rfl
  rw [e1] at hcomp
  refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  exact hψ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem archCompactRepKZ_uActionKZ_ι (k : archCompact K n) (X : archLie K n) (v : smoothKZ K n) :
    archCompactRepKZ K n k
        (uActionKZ K n (UniversalEnvelopingAlgebra.ι ℝ ((isExpLieAlgebra K n).toLie X)) v) =
      uActionKZ K n (UniversalEnvelopingAlgebra.ι ℝ ((isExpLieAlgebra K n).toLie
        ((isExpLieAlgebra K n).Ad (k : archGroup K n) X))) (archCompactRepKZ K n k v) := by
  rw [archCompactRepKZ_uActionKZ, IsExpLieAlgebra.AdU_ι]
  rfl

section GK

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K n) in

def gkModule : (isExpLieAlgebra K n).GKModule (archCompact K n) (smoothKZ K n) where
  ρ :=
    { toFun := fun X => uActionKZ K n (UniversalEnvelopingAlgebra.ι ℝ X)
      map_add' := fun X Y => by rw [map_add, map_add]
      map_smul' := fun r X => by rw [map_smul, map_smul]; rfl
      map_lie' := fun {X Y} => by
        rw [LieHom.map_lie, Ring.lie_def, Ring.lie_def, map_sub, map_mul, map_mul] }
  σ := archCompactRepKZ K n
  locallyFinite v := finiteDimensional_span_archCompactRepKZ v
  hasContinuousCoeff := hasContinuousCoeff_archCompactRepKZ
  hasDerivAt_coeff X hX φ v := hasDerivAt_archCompactRepKZ X hX φ v
  map_ρ k X v := archCompactRepKZ_uActionKZ_ι k X v

@[simp] theorem gkModule_ρ_apply (X : (isExpLieAlgebra K n).lieSubalgebra) (v : smoothKZ K n) :
    (gkModule K n).ρ X v = uActionKZ K n (UniversalEnvelopingAlgebra.ι ℝ X) v := rfl

@[simp] theorem gkModule_σ_apply (k : archCompact K n) (v : smoothKZ K n) :
    (gkModule K n).σ k v = archCompactRepKZ K n k v := rfl

theorem gkModule_ρ_finRepKZ (X : (isExpLieAlgebra K n).lieSubalgebra)
    (h : AdelicGLn.FiniteAdelicGL K n) (v : smoothKZ K n) :
    (gkModule K n).ρ X (finRepKZ K n h v) = finRepKZ K n h ((gkModule K n).ρ X v) :=
  uActionKZ_finRepKZ _ h v

theorem gkModule_σ_finRepKZ (k : archCompact K n) (h : AdelicGLn.FiniteAdelicGL K n)
    (v : smoothKZ K n) :
    (gkModule K n).σ k (finRepKZ K n h v) = finRepKZ K n h ((gkModule K n).σ k v) :=
  archCompactRepKZ_finRepKZ k h v

end GK

end AutomorphicForm

end

end GroundTheory.Automorphic
