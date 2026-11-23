import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSub
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFETranslateFeTranslate

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstFam

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange

theorem pullOver_injective_of_dominant {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' : Scheme.{0}}
    {π : Y ⟶ Spec (CommRingCat.of R)} (L : LB X) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} (ε : K → ℤ)
    {π' : Y' ⟶ Spec (CommRingCat.of R')} {g : R →+* R'} {p : Y' ⟶ Y}
    (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom g)) {φ' : K → (Y' ⟶ X)} (hφ : ∀ k, φ' k = p ≫ φ k)
    [IsSchemeTheoreticallyDominant p] [QuasiCompact p] : Function.Injective (pullOver L ε hp hφ) := by
  intro s t h
  refine SecOver.ext _ _ fun i => p.app_injective _ (fn_ext fun y hy => ?_)
  have e := congrArg (fun q : SecOver π' (LB.LinComb L φ' ε) => gs (𝟙 _) y _ (LB.Sec.f q i)) h
  have hy' : (𝟙 Y' : _ ⟶ _) y ∈ LB.wchart L φ' i := (wchart_eq hφ i).ge hy
  exact (gs_pull _ _ y _ hy _).trans ((gs_pullFn _ _ _ _ y hy').symm.trans (e.trans
    ((gs_pullFn _ _ _ _ y hy').trans (gs_pull _ _ y _ hy _).symm)))

section

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) {j n : ℕ}

theorem expandsAt_smul (a : R)
    {σ : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))}
    {f : ∀ χ, SecBMod D.toPre j χ} (h : U.ExpandsAt n j σ f) :
    U.ExpandsAt n j (a • σ : SecOver G.hom _) (a • f : ∀ χ, SecBMod D.toPre j χ) :=
  expandsAt_secIsMul R I D A G U n j a σ _ f _ (fun _ => rfl) (fun _ _ => rfl) h

theorem expandsAt_zero
    {σ : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))}
    {f : ∀ χ, SecBMod D.toPre j χ} (h : U.ExpandsAt n j σ f) :
    U.ExpandsAt n j (0 : SecOver G.hom _) (0 : ∀ χ, SecBMod D.toPre j χ) := by
  have e₁ : (0 : R) • σ = 0 := zero_smul R σ
  have e₂ : (0 : R) • f = 0 := zero_smul R f
  exact e₁ ▸ e₂ ▸ expandsAt_smul U (0 : R) h

theorem expandsAt_add
    {σ τ : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))}
    {f g : ∀ χ, SecBMod D.toPre j χ} (h : U.ExpandsAt n j σ f) (h' : U.ExpandsAt n j τ g) :
    U.ExpandsAt n j (σ + τ : SecOver G.hom _) (f + g : ∀ χ, SecBMod D.toPre j χ) := by
  refine expandsAt_sub R I D A G U n j σ ((-1 : R) • τ : SecOver G.hom _) _ f
    ((-1 : R) • g : ∀ χ, SecBMod D.toPre j χ) _ (fun i => ?_) (fun α i => ?_) h (expandsAt_smul U (-1) h')
  · show chartLin G.hom _ i (σ + τ) = chartLin G.hom _ i σ - chartLin G.hom _ i ((-1 : R) • τ)
    rw [← map_sub, neg_one_smul, sub_neg_eq_add]
  · show chartLin D.toPre.P.A.hom _ i (f α + g α) =
      chartLin D.toPre.P.A.hom _ i (f α) - chartLin D.toPre.P.A.hom _ i ((-1 : R) • g α)
    rw [← map_sub, neg_one_smul, sub_neg_eq_add]

end

theorem exists_smul_mem_span_of_expandsAt {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : Unif I D A G) {j : ℕ} (hj : 1 ≤ j) {Idx : Type} (Φ : Idx → Fam D.toPre (FractionRing R) j)
    (hΦ : Submodule.span (FractionRing R) (Set.range Φ) = ⊤) (r : Idx → R) (hr : ∀ i, r i ≠ 0)
    (σ : Idx → SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ))))
    (f : Idx → ∀ χ, SecBMod D.toPre j χ)
    (hf : ∀ i χ, resF D.toPre (FractionRing R) j χ (f i χ) =
      toF (R := R) (FractionRing R) (r i) • famComp D.toPre (FractionRing R) j χ (Φ i))
    (hE : ∀ i n, U.toUnifPre.ExpandsAt n j (σ i) (f i))
    (s : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))) :
    ∃ t : R, t ≠ 0 ∧ t • s ∈ Submodule.span R (Set.range σ) := by
  have hsm := U.smooth
  have hinj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have : IsDominant (jK R) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R)) :=
    .of_isPullback (IsPullback.of_hasPullback G.hom (jK R)).flip
  have hp : pullback.fst G.hom (jK R) ≫ G.hom =
      pullback.snd G.hom (jK R) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := pullback.condition
  have hφ : ∀ k : Fin 1, (fun _ : Fin 1 => pullback.fst G.hom (jK R)) k =
      pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k := fun _ => (Category.comp_id _).symm
  have hρ := pullOver_injective_of_dominant U.LG.L (fun _ : Fin 1 => (j : ℤ)) hp hφ
  set ρ := pullOver U.LG.L (fun _ : Fin 1 => (j : ℤ)) hp hφ with hρdef
  have hS := fun s₁ s₂ c => secScal_iff hp hφ (ε := fun _ : Fin 1 => (j : ℤ)) U.LG.isLB s₁ s₂
    (pullback.snd G.hom (jK R) ≫ jK R) (algebraMap R (FractionRing R)) rfl c
  have toF_eq : ∀ x : R, toF (R := R) (FractionRing R) x = algebraMap R (FractionRing R) x := fun _ => rfl
  obtain ⟨Φ₀, hΦ₀, -⟩ := (U.expand j hj).1 (ρ s)
  obtain ⟨-, -, σ₀, f₀, -, -, h₀⟩ := id hΦ₀
  have key : ∀ Ψ ∈ Submodule.span (FractionRing R) (Set.range Φ), ∃ t : R, t ≠ 0 ∧
      ∃ σ' ∈ Submodule.span R (Set.range σ), ∃ f' : ∀ χ, SecBMod D.toPre j χ,
        (∀ χ, resF D.toPre (FractionRing R) j χ (f' χ) =
          toF (R := R) (FractionRing R) t • famComp D.toPre (FractionRing R) j χ Ψ) ∧
        ∀ n, U.toUnifPre.ExpandsAt n j σ' f' := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨r i, hr i, σ i, Submodule.subset_span ⟨i, rfl⟩, f i, hf i, hE i⟩
    | zero =>
      refine ⟨1, one_ne_zero, 0, zero_mem _, 0, fun χ => by simp, fun n => ?_⟩
      exact expandsAt_zero U.toUnifPre (σ := σ₀) (f := f₀) (h₀ n)
    | add x y _ _ hx hy =>
      obtain ⟨t₁, ht₁, σ₁, m₁, f₁, e₁, E₁⟩ := hx
      obtain ⟨t₂, ht₂, σ₂, m₂, f₂, e₂, E₂⟩ := hy
      refine ⟨t₁ * t₂, mul_ne_zero ht₁ ht₂, t₂ • σ₁ + t₁ • σ₂,
        add_mem (Submodule.smul_mem _ _ m₁) (Submodule.smul_mem _ _ m₂), t₂ • f₁ + t₁ • f₂, fun χ => ?_,
        fun n => expandsAt_add _ (expandsAt_smul _ _ (E₁ n)) (expandsAt_smul _ _ (E₂ n))⟩
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, map_add, map_smulₛₗ, map_smulₛₗ, e₁, e₂, map_add, map_mul,
        smul_add, smul_smul, smul_smul, mul_comm]
    | smul a x _ hx =>
      obtain ⟨t, ht, σ₁, m₁, f₁, e₁, E₁⟩ := hx
      obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := R) a
      have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
      have hv' : algebraMap R (FractionRing R) v ≠ 0 := fun h => hv0 (hinj (h.trans (map_zero _).symm))
      refine ⟨t * v, mul_ne_zero ht hv0, u • σ₁, Submodule.smul_mem _ _ m₁, u • f₁, fun χ => ?_,
        fun n => expandsAt_smul _ _ (E₁ n)⟩
      rw [Pi.smul_apply, map_smulₛₗ, e₁, map_smul, smul_smul, smul_smul, map_mul, toF_eq, toF_eq, toF_eq]
      congr 1
      field_simp
  obtain ⟨t, ht, σ', m, f', e, E⟩ := key Φ₀ (hΦ ▸ Submodule.mem_top)
  have ht' : algebraMap R (FractionRing R) t ≠ 0 := fun h => ht (hinj (h.trans (map_zero _).symm))
  have hX : U.toUnifPre.Expands j ((algebraMap R (FractionRing R) t)⁻¹ • ρ σ' : SecOver _ _) Φ₀ :=
    ⟨t, ht, σ', f', (hS _ _ _).2 (by rw [smul_inv_smul₀ ht']),
      fun χ => (secScal_iff_resF D.toPre (FractionRing R) _ _ _).2 (e χ), E⟩
  have hu : ((algebraMap R (FractionRing R) t)⁻¹ • ρ σ' : SecOver _ _) = ρ s :=
    ((U.expand j hj).2 Φ₀).unique hX hΦ₀
  refine ⟨t, ht, ?_⟩
  have : t • s = σ' := hρ (by rw [map_smulₛₗ, ← hu, smul_inv_smul₀ ht'])
  rwa [this]

end GlobalTheory.ConstFam
