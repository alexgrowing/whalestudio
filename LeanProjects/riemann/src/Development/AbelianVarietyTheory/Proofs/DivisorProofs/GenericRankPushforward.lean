import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open GlobalTheory.VB

namespace GlobalTheory.VB

theorem genRank_pushforward_of_generic : ∀ (T T' : Scheme.{0}) [IsIntegral T] [IsIntegral T']
    (ρ : T' ⟶ T) (h : ρ (genericPoint T') ⤳ genericPoint T),
    (∀ V : T'.Opens, genericPoint T' ∈ V → ∃ U : T.Opens, genericPoint T ∈ U ∧ ρ ⁻¹ᵁ U ≤ V) →
    ∀ F : T'.Modules, genRank ((Scheme.Modules.pushforward ρ).obj F) =
      (letI := (T.presheaf.stalkSpecializes h ≫ ρ.stalkMap (genericPoint T')).hom.toAlgebra;
        Module.finrank T.functionField T'.functionField) * genRank F := by
  intro T T' _ _ ρ h H F
  let G := (Scheme.Modules.pushforward ρ).obj F
  let φ := T.presheaf.stalkSpecializes h ≫ ρ.stalkMap (genericPoint T')
  letI : Algebra T.functionField T'.functionField := φ.hom.toAlgebra
  letI : Module T.functionField (genStalk F) :=
    Module.compHom _ (algebraMap T.functionField T'.functionField)
  haveI : IsScalarTower T.functionField T'.functionField (genStalk F) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let Ψ : (G.presheaf.stalk (genericPoint T) :) →+ (F.presheaf.stalk (genericPoint T') :) :=
    (G.presheaf.stalkSpecializes h ≫ F.presheaf.stalkPushforward _ ρ.base (genericPoint T')).hom
  have hΨ (U : T.Opens) (hU : genericPoint T ∈ U) (s : Γ(G, U)) :
      Ψ (G.presheaf.germ U _ hU s) =
        F.presheaf.germ (ρ ⁻¹ᵁ U) (genericPoint T') (h.mem_open U.isOpen hU) s := by
    have e := TopCat.Presheaf.germ_stalkSpecializes G.presheaf (U := U) hU h
    have e' := TopCat.Presheaf.stalkPushforward_germ _ ρ.base F.presheaf U (genericPoint T')
      (h.mem_open U.isOpen hU)
    calc Ψ (G.presheaf.germ U _ hU s) = ((G.presheaf.germ U _ hU ≫ G.presheaf.stalkSpecializes h) ≫
          F.presheaf.stalkPushforward _ ρ.base _).hom s := rfl
      _ = (G.presheaf.germ U _ (h.mem_open U.isOpen hU) ≫
          F.presheaf.stalkPushforward _ ρ.base _).hom s := by rw [e]
      _ = _ := congr($(e').hom s)

  have hsurj : Function.Surjective Ψ := by
    intro t
    obtain ⟨V, hV, s, rfl⟩ := F.presheaf.germ_exist t
    obtain ⟨U, hU, hle⟩ := H V hV
    refine ⟨G.presheaf.germ U _ hU (F.presheaf.map (homOfLE hle).op s), ?_⟩
    refine (hΨ U hU _).trans ?_
    exact TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hle) _ _ s
  have hinj : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).2 fun m hm => ?_
    obtain ⟨U, hU, s, rfl⟩ := G.presheaf.germ_exist m
    have hm' : F.presheaf.germ (ρ ⁻¹ᵁ U) _ (h.mem_open U.isOpen hU) s =
        F.presheaf.germ (ρ ⁻¹ᵁ U) _ (h.mem_open U.isOpen hU) 0 :=
      (hΨ U hU s).symm.trans (hm.trans (map_zero _).symm)
    obtain ⟨W, hW, i₁, i₂, e⟩ := F.presheaf.germ_eq _ _ _ _ _ hm'
    obtain ⟨U', hU', hle⟩ := H W hW
    have hU'' : genericPoint T ∈ U ⊓ U' := ⟨hU, hU'⟩
    have hle' : ρ ⁻¹ᵁ (U ⊓ U') ≤ W := fun x hx => hle hx.2
    have h0 : G.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op s = 0 := by
      change F.presheaf.map (homOfLE (fun x hx => hx.1 : ρ ⁻¹ᵁ (U ⊓ U') ≤ ρ ⁻¹ᵁ U)).op s = 0
      have := congr(F.presheaf.map (homOfLE hle').op $e)
      rw [map_zero, map_zero] at this
      rw [show (homOfLE _ : ρ ⁻¹ᵁ (U ⊓ U') ⟶ ρ ⁻¹ᵁ U) = homOfLE hle' ≫ i₁ from rfl, op_comp,
        F.presheaf.map_comp]
      exact this
    rw [← TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (inf_le_left : U ⊓ U' ≤ U)) _ hU'', h0,
      map_zero]
  have hsmul (a : T.functionField) (m : genStalk G) : Ψ (a • m) = φ.hom a • Ψ m := by
    obtain ⟨U₁, hU₁, r, rfl⟩ := T.presheaf.germ_exist a
    obtain ⟨U₂, hU₂, s, rfl⟩ := G.presheaf.germ_exist m
    have hU : genericPoint T ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
    rw [← TopCat.Presheaf.germ_res_apply T.presheaf (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) _ hU,
      ← TopCat.Presheaf.germ_res_apply G.presheaf (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) _ hU]
    generalize T.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op r = r'
    generalize G.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op s = s'
    rw [← GlobalTheory.QCoh.germ_smul G, hΨ, hΨ]
    refine (GlobalTheory.QCoh.germ_smul F (U := ρ ⁻¹ᵁ (U₁ ⊓ U₂)) _ _ (ρ.app _ r') s').trans ?_
    congr 1
    have e₁ := TopCat.Presheaf.germ_stalkSpecializes T.presheaf hU h
    have e₂ := Scheme.Hom.germ_stalkMap ρ (U₁ ⊓ U₂) (genericPoint T') (h.mem_open (U₁ ⊓ U₂).isOpen hU)
    calc T'.presheaf.germ _ _ _ (ρ.app _ r') =
          (T.presheaf.germ (U₁ ⊓ U₂) _ (h.mem_open (U₁ ⊓ U₂).isOpen hU) ≫ ρ.stalkMap _).hom r' :=
          congr($(e₂).hom r').symm
      _ = ((T.presheaf.germ (U₁ ⊓ U₂) _ hU ≫ T.presheaf.stalkSpecializes h) ≫ ρ.stalkMap _).hom r' := by
          rw [e₁]
      _ = _ := rfl
  let e : genStalk G ≃ₗ[T.functionField] genStalk F :=
    { AddEquiv.ofBijective Ψ ⟨hinj, hsurj⟩ with map_smul' := hsmul }
  show Module.finrank T.functionField (genStalk G) =
    Module.finrank T.functionField T'.functionField * Module.finrank T'.functionField (genStalk F)
  rw [e.finrank_eq, Module.finrank_mul_finrank]

end GlobalTheory.VB
