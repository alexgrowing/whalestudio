import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrSetlift
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpGlift
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpGco
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LcMatrix
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.BorelProjectionIsTwoCocycle
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCocv
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ValSubOneMap

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ep_hasobs :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ (ρ : NRep F 3 R) (B : Box F 3 R) (π : F.V → Fin 3 → ZMod 2), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → B.Gr σ π → ∀ h : (B.bar O).Ev π, ∀ j, HasObsG O σ j (coneH2 F.loc (h.ad j) ((B.bar O).bp j)) := by
  intro l _ k _ _ F C₀ hF O _ _ _ _ h2 R _ _ _ σ hσ ρ B π hU hOf hCont hGood hGr h j
  intro C' _ _ _ p σ' hp hker hσ' hpσ
  obtain ⟨a⟩ := pr_setlift hF O C' R p B hp hker hCont
  obtain ⟨D, hD⟩ := ep_glift O h2 C' R p σ' σ hσ' hpσ B π hGr a
  have hco : ∀ u : ↥(formp σ' (RingHom.ker p) j),
      (∀ x : F.Γ × F.Γ, (D.co u).1 x ∈ adp (ResidueField O) j) ∧
        ∀ (v : F.V) (s : F.Gv v), (D.co u).2 v s ∈ adp (ResidueField O) j :=
    fun u => ep_gco O C' R p σ' B π D hD j u u.2
  have hom := pr_omk hF O C' R p B D hker
  let Ψ : ↥(formp σ' (RingHom.ker p) j) →ₗ[ResidueField O]
      ((F.Γ × F.Γ → ↥(adp (ResidueField O) j)) × ((v : F.V) → F.Gv v → ↥(adp (ResidueField O) j))) :=
    { toFun := fun u => (fun x => ⟨(D.co u).1 x, (hco u).1 x⟩, fun v s => ⟨(D.co u).2 v s, (hco u).2 v s⟩)
      map_add' := by
        intro u w
        refine Prod.ext (funext fun x => Subtype.ext ?_) (funext fun v => funext fun s => Subtype.ext ?_) <;>
          simp [map_add]
      map_smul' := by
        intro c u
        refine Prod.ext (funext fun x => Subtype.ext ?_) (funext fun v => funext fun s => Subtype.ext ?_) <;>
          simp [map_smul] }
  have hmem : ∀ u, Ψ u ∈ continuousCocycles2 F.loc (h.ad j) ((Box.bar O B).bp j) := by
    intro u
    have k1 : Subtype.val ∘ (Ψ u).1 = (fun M : Matrix (Fin 3) (Fin 3) C' =>
        M.map (evK (RingHom.ker p) (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O))) ∘ D.om := rfl
    have k2 : ∀ v, Subtype.val ∘ (Ψ u).2 v = (fun M : Matrix (Fin 3) (Fin 3) C' =>
        M.map (evK (RingHom.ker p) (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O))) ∘ D.a v := fun v => rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      rw [k1]
      exact hom.2.2.1.comp _
    · intro v
      refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
      rw [k2 v]
      exact (hom.2.2.2 v).comp _
    · intro s t r
      apply Subtype.ext
      exact borelProjection_isTwoCocycle hF O C' R p B D (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) hker s t r
    · intro v s t
      exact pr_cocv hF O C' R p B D (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) hker v s t
  refine ⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _ Ψ hmem), ?_⟩
  intro u hu C'' _ _ _ q p'' hcomp hq hy
  refine pr_obs hF O R ρ B hU hOf hCont hGood C' p D (u : ↥(RingHom.ker p) →ₗ[O] ResidueField O) hker ?_
    C'' q p'' hcomp hq hy
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu
  obtain ⟨β, Y, hβ, h1, h3⟩ := hu
  refine ⟨fun g => (β g : Matrix (Fin 3) (Fin 3) (ResidueField O)),
    fun v => (Y v : Matrix (Fin 3) (Fin 3) (ResidueField O)), hβ.comp _, ?_, ?_⟩
  · funext x
    exact congrArg (fun f => (f x : Matrix (Fin 3) (Fin 3) (ResidueField O))) h1
  · intro v s
    exact h3 v s
