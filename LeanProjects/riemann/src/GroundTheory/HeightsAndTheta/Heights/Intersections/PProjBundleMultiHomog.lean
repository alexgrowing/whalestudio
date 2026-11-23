import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StProjBundleMultiHomog
import GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleMultiHomogSpan
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Weights

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def zDegInl : (K → ℕ) →+ (K ⊕ Unit → ℤ) :=
  AddMonoidHom.mk' (fun a x => Sum.elim (fun k => (a k : ℤ)) (fun _ => 0) x) (by
    intro a b
    funext x
    cases x <;> simp)

def zDeg : (K ⊕ Unit → ℕ) →+ (K ⊕ Unit → ℤ) := AddMonoidHom.compLeft (Nat.castAddMonoidHom ℤ) _

omit [Fintype K] [DecidableEq K] in
theorem zDeg_injective : Function.Injective (zDeg (K := K)) := fun a b h =>
  funext fun x => by
    have := congrFun h x
    simpa [zDeg] using this

variable (ι) {S : Type} [Fintype S] (γ : S → K → ℕ)

def genericWeight : S ⊕ (Σ k, ι k) → (K ⊕ Unit → ℤ)
  | .inl s => Pi.single (Sum.inr ()) 1 - zDegInl (γ s)
  | .inr p => zDegInl (NumbersDVR.blockWeight ι p)

variable {ι} {N1 : ℕ}

def genericSubstitution (V : S → Fin N1 → MRing ι) : (Σ x, PBlk ι N1 x) → MvPolynomial (S ⊕ (Σ k, ι k)) ℤ
  | ⟨.inl k, i⟩ => X (.inr ⟨k, i⟩)
  | ⟨.inr _, j⟩ => ∑ s, rename Sum.inr (V s j) * X (.inl s)

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem genericSubstitution_isWeightedHomogeneous (V : S → Fin N1 → MRing ι)
    (hV : ∀ s j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (V s j) (γ s))
    (v : Σ x, PBlk ι N1 x) :
    IsWeightedHomogeneous (genericWeight ι γ) (genericSubstitution V v) (zDeg (NumbersDVR.blockWeight (PBlk ι N1) v)) := by
  rcases v with ⟨k | u, i⟩
  · convert isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inr ⟨k, i⟩) using 1
    · rfl
    · funext x
      cases x <;> simp [genericWeight, zDegInl, zDeg, NumbersDVR.blockWeight, Pi.single_apply]
  · have hdeg : zDeg (NumbersDVR.blockWeight (PBlk ι N1) ⟨Sum.inr u, i⟩) = Pi.single (Sum.inr ()) 1 := by
      funext x
      cases x <;> simp [zDeg, NumbersDVR.blockWeight]
    rw [hdeg]
    change Fin N1 at i
    refine IsWeightedHomogeneous.sum _ _ _ fun s _ => ?_
    have hren : IsWeightedHomogeneous (genericWeight ι γ) (rename Sum.inr (V s i) : MvPolynomial (S ⊕ _) ℤ)
        (zDegInl (γ s)) := by
      rw [rename_eq_aeval]
      refine isWeightedHomogeneous_aeval_of_weights (w := fun p => zDegInl (NumbersDVR.blockWeight ι p))
        (e := X ∘ Sum.inr)
        (fun p => isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inr p)) ?_
      intro d hd
      rw [NumbersDVR.weight_comp_addMonoidHom, hV s i hd]
    convert hren.mul (isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inl s)) using 1
    show _ = zDegInl (γ s) + (Pi.single (Sum.inr ()) 1 - zDegInl (γ s))
    abel

end Weights

section Kernel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {S : Type} [Fintype S]

def genericEvaluation (P : Ideal (MRing ι)) : MvPolynomial (S ⊕ (Σ k, ι k)) ℤ →+* MvPolynomial S (FnField P) :=
  (map (toFn P)).comp (sumAlgEquiv ℤ S (Σ k, ι k)).toAlgHom.toRingHom

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S] in
theorem sumAlgEquiv_rename_inr (f : MRing ι) :
    sumAlgEquiv ℤ S (Σ k, ι k) (rename Sum.inr f) = C f := by
  have := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr ℤ S (Σ k, ι k)) f
  simpa [algebraMap_eq] using this

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S] in
theorem genericEvaluation_rename_inr (P : Ideal (MRing ι)) (f : MRing ι) :
    genericEvaluation (S := S) P (rename Sum.inr f) = C (toFn P f) := by
  simp [genericEvaluation, sumAlgEquiv_rename_inr]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem genMap_eq_comp [DecidableEq K] (P : Ideal (MRing ι)) {N1 : ℕ} (V : S → Fin N1 → MRing ι) :
    genMap P (fun s j => toFn P (V s j)) = (genericEvaluation P).comp (aeval (genericSubstitution V)).toRingHom := by
  refine MvPolynomial.ringHom_ext (fun z => by simp) ?_
  rintro ⟨k | u, i⟩
  · simp [genMap, genericSubstitution, genericEvaluation, genPt, toFn]
  · change Fin N1 at i
    simp only [genMap, genericSubstitution, RingHom.coe_comp, Function.comp_apply, eval₂Hom_X', AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, aeval_X, map_sum, map_mul, genericEvaluation_rename_inr]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [genericEvaluation]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S] in

theorem ker_genericEvaluation_le (P : Ideal (MRing ι)) :
    RingHom.ker (genericEvaluation (S := S) P) ≤ Ideal.map (rename Sum.inr) P := by
  intro f hf
  set e := sumAlgEquiv ℤ S (Σ k, ι k)
  have hg : e f ∈ Ideal.map (C : MRing ι →+* MvPolynomial S (MRing ι)) P := by
    rw [← ker_toFn P, ← MvPolynomial.ker_map]
    exact hf
  have hre : ∀ x : MRing ι, e.symm (C x) = rename Sum.inr x := by
    intro x
    rw [AlgEquiv.symm_apply_eq]
    exact (sumAlgEquiv_rename_inr x).symm
  have h1 : Ideal.map e.symm (Ideal.map (C : MRing ι →+* MvPolynomial S (MRing ι)) P) ≤
      Ideal.map (rename Sum.inr) P := by
    rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap, hre]
    exact Ideal.mem_map_of_mem _ hx
  simpa using h1 (Ideal.mem_map_of_mem e.symm hg)

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S] in

theorem map_le_ker_genericEvaluation (P : Ideal (MRing ι)) :
    Ideal.map (rename Sum.inr) P ≤ RingHom.ker (genericEvaluation (S := S) P) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker, genericEvaluation_rename_inr]
  have h0 : toFn P x = 0 := by rw [← RingHom.mem_ker, ker_toFn]; exact hx
  rw [h0, map_zero]

theorem component_mem_ker_genMap [DecidableEq K] (P : Ideal (MRing ι)) (G : Set (MRing ι))
    (hG : ∀ f ∈ G, ∃ a, IsMultiHomog f a) (hPG : P = Ideal.span G) {N1 : ℕ}
    (V : S → Fin N1 → MRing ι) (γ : S → K → ℕ)
    (hV : ∀ s j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (V s j) (γ s))
    {f : MRing (PBlk ι N1)} (hf : f ∈ RingHom.ker (genMap P fun s j => toFn P (V s j)))
    (b : K ⊕ Unit → ℕ) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight (PBlk ι N1)) b f ∈
      RingHom.ker (genMap P fun s j => toFn P (V s j)) := by
  classical
  rw [genMap_eq_comp] at hf ⊢
  rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker] at hf ⊢
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf ⊢
  have hJ := ker_genericEvaluation_le P hf
  have hGw : ∀ g ∈ G, ∃ a, IsWeightedHomogeneous (fun p => zDegInl (NumbersDVR.blockWeight ι p)) g a := by
    intro g hg
    obtain ⟨a, ha⟩ := hG g hg
    refine ⟨zDegInl a, fun d hd => ?_⟩
    rw [NumbersDVR.weight_comp_addMonoidHom, ((Bridge.isMultiHomog_iff g a).mpr ha) hd]
  rw [hPG, rename_eq_aeval] at hJ
  have hc := weightedHomogeneousComponent_mem_map_aeval (ω := genericWeight ι γ) (e := X ∘ Sum.inr)
    (fun p => isWeightedHomogeneous_X ℤ (genericWeight ι γ) (Sum.inr p)) G hGw hJ (zDeg b)
  rw [← rename_eq_aeval, ← hPG] at hc
  rw [← aeval_weightedHomogeneousComponent_of_weights
      (fun v => zDeg (NumbersDVR.blockWeight (PBlk ι N1) v)) (genericWeight ι γ) (genericSubstitution V)
      (genericSubstitution_isWeightedHomogeneous γ V hV), NumbersDVR.weightedHomogeneousComponent_comp_addMonoidHom zDeg zDeg_injective]
    at hc
  exact map_le_ker_genericEvaluation P hc

end Kernel

theorem ProjBundleMultiHomog.proof : ProjBundleMultiHomog.Statement := by
  intro K _ ι _ N1 t n P d c m B hP hQ hB
  classical
  obtain ⟨-, ⟨hPp, hPh, -⟩, -, -⟩ := hP
  have := hPp
  have hPc := (Bridge.isMultiHomogIdeal_iff P).mpr hPh
  obtain ⟨S, _, V, γ, hV, hVker, hBspan⟩ := exists_homog_span P hPc c m
    (fun r j => (Bridge.isMultiHomog_iff _ _).mpr (hQ.1 r j)) B
    (fun a => by rw [← hB.2]; exact Submodule.subset_span ⟨a, rfl⟩)
  have hker : projBundleIdeal P B = RingHom.ker (genMap P fun s j => toFn P (V s j)) :=
    le_antisymm (ker_genMap_le P B _ fun s => by rw [hB.2]; exact hVker s)
      (ker_genMap_le P _ B hBspan)
  rw [hker]
  obtain ⟨G, hG, hPG⟩ := hPh
  exact (Bridge.isMultiHomogIdeal_iff _).mp fun f hf b => component_mem_ker_genMap P G hG hPG V γ hV hf b

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
