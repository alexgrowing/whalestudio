import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ContrSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameEx
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T : W →ₗ[ℂ] W) (i : Fin d)
    (x : W ⊗[ℂ] (Fin d → ℂ)) : cmp i (T.rTensor _ x) = T (cmp i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v => simp

private noncomputable def coords {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (q : ℕ)
    {n : ℕ} (e : Fin n → Herm E a) : Co Ξ q →ₗ[ℂ] ((Fin q → Fin n) × Fin Ξ.d → Sm E a) where
  toFun ω p := cmp p.2 (ω fun j => e (p.1 j))
  map_add' α β := funext fun p => map_add (Bor.cmp p.2) _ _
  map_smul' c α := funext fun p => map_smul (Bor.cmp p.2) c _

private theorem coords_inj {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (q : ℕ)
    {n : ℕ} {e : Fin n → Herm E a} (he : IsFrame e) : Function.Injective (coords Ξ q e) := by
  intro α β h
  have hs : Submodule.span ℝ (Set.range e) = ⊤ := by
    refine eq_top_iff.2 fun X _ => ?_
    rw [he X]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  apply AlternatingMap.coe_multilinearMap_injective
  refine MultilinearMap.ext_of_span_eq_top (g := fun _ => e) (fun _ => hs) fun I => ?_
  change α (fun j => e (I j)) = β (fun j => e (I j))
  rw [← sum_cmp (α _), ← sum_cmp (β _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := congrFun h (I, i)
  exact congrArg (· ⊗ₜ[ℂ] _) this

theorem UpperTheory.V.Cj.H.harmFin :
    UpperTheory.V.Cj.H.HarmFin := by
  intro E _ _ _ a Ξ r m q U hU
  obtain ⟨n, e, he⟩ := frameEx E a
  obtain ⟨W, _, _, _, ρ, hρ, hk⟩ := kType E a Ξ q
  have hF := formsFiniteGL E a U hU W ρ hρ fun t u => ((m t).map (u + ·)).prod
  set F := Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms U ρ fun t u => ((m t).map (u + ·)).prod) with hFd
  have hle : ∀ ω ∈ Submodule.span ℂ {ω : Co Ξ q | IsH r m ω ∧ ∀ u ∈ U, trans u ω = ω}, ∀ p, coords Ξ q e ω p ∈ F := by
    intro ω hω p
    induction hω using Submodule.span_induction with
    | zero => rw [map_zero]; exact F.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact F.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact F.smul_mem c hx
    | mem ω hω =>
      obtain ⟨h, hu⟩ := hω
      obtain ⟨U', -, -, hl⟩ := h.lev
      refine Submodule.subset_span ⟨(h.aut _ _).1, fun k hk' => ?_, fun g => ?_, (h.aut _ _).2⟩
      · have h1 := congrArg (fun η : Co Ξ q => cmp p.2 (η fun j => e (p.1 j))) (hu k hk')
        exact (cmp_rT _ _ _).symm.trans h1
      · obtain ⟨T, w, hT, hw⟩ := hk ω hl.equiv (fun j => e (p.1 j)) p.2
        have := GlobalTheory.Published.AutFinGL.type_of_map ρ T hT w g
        rw [hw] at this
        exact this
  refine FiniteDimensional.of_injective (V₂ := (Fin q → Fin n) × Fin Ξ.d → F)
    (LinearMap.pi fun p => ((LinearMap.proj p ∘ₗ coords Ξ q e) ∘ₗ Submodule.subtype _).codRestrict F fun ω => hle ω.1 ω.2 p)
    fun α β h => Subtype.ext (coords_inj Ξ q he (funext fun p => ?_))
  exact congrArg Subtype.val (congrFun h p)
