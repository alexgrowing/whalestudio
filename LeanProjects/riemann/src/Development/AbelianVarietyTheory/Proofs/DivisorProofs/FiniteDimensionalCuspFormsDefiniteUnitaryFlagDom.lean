import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import ReciprocityTheory.SemistableReduction.LatAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteFrameLeadingMinorsSignStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameSectionSliceEqPolyDivDetPowStatement

set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.DefiniteFin

theorem finiteDimensional_span_of_slices (ι : Type) [Fintype ι] [DecidableEq ι] (A : ι → Type) (D : ∀ i, Set (A i))
    (W : ∀ i, Submodule ℂ (A i → ℂ)) (hW : ∀ i, FiniteDimensional ℂ (W i)) (Dom : Set (∀ i, A i))
    (hDom : Dom = Set.univ.pi D) (S : Set ((∀ i, A i) → ℂ))
    (hS : ∀ g ∈ S, ∀ x ∈ Dom, ∀ i, ∃ w ∈ W i, ∀ t ∈ D i, g (Function.update x i t) = w t) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun g : (∀ i, A i) → ℂ => fun x : Dom => g x) '' S)) := by
  subst hDom
  have hT : ∀ i, ∃ T : Set (A i), T ⊆ D i ∧ T.Finite ∧
      ∀ w ∈ W i, (∀ t ∈ T, w t = 0) → ∀ t ∈ D i, w t = 0 := by
    intro i
    let ev : A i → Module.Dual ℂ (W i) := fun t =>
      (LinearMap.proj t : (A i → ℂ) →ₗ[ℂ] ℂ).comp (W i).subtype
    obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent ℂ (ev '' D i)
    have hbfin : b.Finite := hli.setFinite
    obtain ⟨T, hTD, hTfin, hTb⟩ := Set.exists_subset_image_finite_and.1 ⟨b, hb, hbfin, rfl⟩
    refine ⟨T, hTD, hTfin, fun w hw h0 t ht => ?_⟩
    have hmem : ev t ∈ Submodule.span ℂ b := by
      rw [hspan]; exact Submodule.subset_span ⟨t, ht, rfl⟩
    have hall : ∀ φ ∈ Submodule.span ℂ b, φ ⟨w, hw⟩ = 0 := by
      intro φ hφ
      induction hφ using Submodule.span_induction with
      | mem φ hφ =>
        rw [hTb] at hφ
        obtain ⟨s, hs, rfl⟩ := hφ
        exact h0 s hs
      | zero => rfl
      | add φ ψ _ _ h1 h2 => simp [h1, h2]
      | smul c φ _ h => simp [h]
    exact hall _ hmem
  choose T hTD hTfin hTz using hT
  let G : Set (∀ i, A i) := Set.univ.pi T
  have hGfin : G.Finite := Set.Finite.pi (fun i => hTfin i)
  have hGD : G ⊆ Set.univ.pi D := Set.pi_mono (fun i _ => hTD i)
  let V : Submodule ℂ ((∀ i, A i) → ℂ) :=
    { carrier := {g | ∀ x ∈ Set.univ.pi D, ∀ i, ∃ w ∈ W i, ∀ t ∈ D i, g (Function.update x i t) = w t}
      add_mem' := by
        intro f g hf hg x hx i
        obtain ⟨w, hw, hfw⟩ := hf x hx i
        obtain ⟨w', hw', hgw⟩ := hg x hx i
        exact ⟨w + w', (W i).add_mem hw hw', fun t ht => by simp [hfw t ht, hgw t ht]⟩
      zero_mem' := by
        intro x hx i
        exact ⟨0, (W i).zero_mem, fun t ht => by simp⟩
      smul_mem' := by
        intro c f hf x hx i
        obtain ⟨w, hw, hfw⟩ := hf x hx i
        exact ⟨c • w, (W i).smul_mem c hw, fun t ht => by simp [hfw t ht]⟩ }
  have key : ∀ g ∈ V, (∀ x ∈ G, g x = 0) → ∀ x ∈ Set.univ.pi D, g x = 0 := by
    intro g hg h0
    have hs : ∀ s : Finset ι, ∀ x ∈ Set.univ.pi D, (∀ i ∉ s, x i ∈ T i) → g x = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro x _ hx; exact h0 x (fun i _ => hx i (Finset.notMem_empty i))
      | insert j s hj ih =>
        intro x hx hxT
        obtain ⟨w, hw, hgw⟩ := hg x hx j
        have hwT : ∀ t ∈ T j, w t = 0 := by
          intro t ht
          rw [← hgw t (hTD j ht)]
          apply ih
          · intro i _
            by_cases h : i = j
            · subst h; simpa using hTD i ht
            · simpa [h] using hx i trivial
          · intro i hi
            by_cases h : i = j
            · subst h; simpa using ht
            · simpa [h] using hxT i (by simp [h, hi])
        have h1 := hTz j w hw hwT (x j) (hx j trivial)
        rw [← h1, ← hgw (x j) (hx j trivial), Function.update_eq_self]
    intro x hx
    exact hs Finset.univ x hx (fun i hi => absurd (Finset.mem_univ i) hi)
  let resD : ((∀ i, A i) → ℂ) →ₗ[ℂ] (Set.univ.pi D → ℂ) := LinearMap.funLeft ℂ ℂ Subtype.val
  let resG : (Set.univ.pi D → ℂ) →ₗ[ℂ] (G → ℂ) := LinearMap.funLeft ℂ ℂ (Set.inclusion hGD)
  have hsub : Submodule.span ℂ ((fun g : (∀ i, A i) → ℂ => fun x : Set.univ.pi D => g x) '' S) ≤
      V.map resD := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hS g hg, rfl⟩
  haveI : Finite G := hGfin.to_subtype
  have hinj : Function.Injective (resG.domRestrict (V.map resD)) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨φ, g, hg, rfl⟩ hφ
    rw [LinearMap.mem_ker] at hφ
    rw [Submodule.mem_bot]
    ext ⟨x, hx⟩
    have hz : ∀ y ∈ G, g y = 0 := by
      intro y hy
      have := congrFun (show resG (resD g) = 0 from hφ) ⟨y, hy⟩
      exact this
    exact key g hg hz x hx
  haveI : FiniteDimensional ℂ (V.map resD) := Module.Finite.of_injective _ hinj
  exact Submodule.finiteDimensional_of_le hsub

theorem finiteDimensional_cusp_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 0 ∨ X.p0 = r) → ∀ la : Wt X.Ψ r,
      FiniteDimensional ℂ (Submodule.span ℂ ((fun f : Frame X.Ψ r → ℂ => fun x : X.dom => f x) '' X.SS la)) := by
  intro E _ _ _ r X hp la
  classical
  have hdom : ∀ x : Frame X.Ψ r, x ∈ X.dom ↔ ∀ τ, (mat x τ).det ≠ 0 := by
    intro x
    constructor
    · intro hx τ; exact (hx τ).1
    · intro hx τ; exact ⟨hx τ, GlobalTheory.T.re_dmin_sign_pos_of_definite E r X hp x τ (hx τ)⟩
  set N : ℕ := ∑ τ, ∑ i, (la τ i).natAbs with hN
  have hNle : ∀ τ i, 0 ≤ la τ i + N := by
    intro τ i
    have h1 : (la τ i).natAbs ≤ N := by
      calc (la τ i).natAbs ≤ ∑ i, (la τ i).natAbs :=
            Finset.single_le_sum (f := fun i => (la τ i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        _ ≤ N := Finset.single_le_sum (f := fun τ => ∑ i, (la τ i).natAbs) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ τ)
    omega
  let d : X.Ψ → ℕ := fun τ => ∑ i, (la τ i + N).toNat
  let ev : MvPolynomial (Fin r × Fin r) ℂ →ₗ[ℂ] ((Fin r → Fin r → ℂ) → ℂ) :=
    { toFun := fun F y => MvPolynomial.eval (fun ij => y ij.1 ij.2) F * ((Matrix.of y).det)⁻¹ ^ N
      map_add' := by intro F G; funext y; simp [add_mul]
      map_smul' := by intro c F; funext y; simp [mul_assoc] }
  let W : X.Ψ → Submodule ℂ ((Fin r → Fin r → ℂ) → ℂ) :=
    fun τ => (MvPolynomial.restrictTotalDegree (Fin r × Fin r) ℂ (d τ)).map ev
  have hW : ∀ τ, FiniteDimensional ℂ (W τ) := fun τ => inferInstance
  refine finiteDimensional_span_of_slices X.Ψ (fun _ => Fin r → Fin r → ℂ) (fun _ => {y | (Matrix.of y).det ≠ 0})
    W hW X.dom ?_ (X.SS la) ?_
  · ext x
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
    exact hdom x
  · intro g hg x hx τ
    obtain ⟨F, hF, hFy⟩ := GlobalTheory.T.frameSection_slice_eq_poly_div_det_pow E r X hdom la N hNle g hg.1.1 x hx τ
    refine ⟨ev F, ⟨F, ?_, rfl⟩, fun t ht => hFy t ht⟩
    rw [SetLike.mem_coe, MvPolynomial.mem_restrictTotalDegree]
    exact hF.totalDegree_le

end GlobalTheory.DefiniteFin

end
