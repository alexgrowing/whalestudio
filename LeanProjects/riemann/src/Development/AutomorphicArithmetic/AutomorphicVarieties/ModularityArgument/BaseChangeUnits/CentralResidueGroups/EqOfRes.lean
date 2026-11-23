import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SignNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.TwCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ResTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc

private theorem eq_of_res {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] (φ : Γ' →* Γ) (ε : Γ →* kˣ)
    (h1 : ∀ s, ε s = 1 ↔ s ∈ φ.range) (h2 : ∀ s, ε s = 1 ∨ ε s = -1) (t : Γ) (ht : ε t ≠ 1) (a b : Γ →* kˣ)
    (hab : a.comp φ = b.comp φ) (hc : a t = b t) : a = b := by
  have h0 : ∀ s, ε s = 1 → a s = b s := fun s hs => by
    obtain ⟨x, rfl⟩ := (h1 s).1 hs
    exact DFunLike.congr_fun hab x
  refine MonoidHom.ext fun s => ?_
  rcases h2 s with hs | hs
  · exact h0 s hs
  · have e := h0 (t⁻¹ * s) (by simp [hs, (h2 t).resolve_left ht])
    rw [map_mul, map_mul, map_inv, map_inv, hc] at e
    exact mul_left_cancel e

open Classical in
private theorem card_bad {Γ Γ' k I : Type} [Group Γ] [Group Γ'] [Field k] [Fintype I] {n : ℕ} (φ : Γ' →* Γ) (ε : Γ →* kˣ)
    (h1 : ∀ s, ε s = 1 ↔ s ∈ φ.range) (h2 : ∀ s, ε s = 1 ∨ ε s = -1) (h3 : ε ≠ 1) (δ : I → Γ →* kˣ)
    (hi : Function.Injective δ) (hδ : ∀ i s, δ i s = 1 ∨ δ i s = -1) (r : Γ' →* GL (Fin n) k) (hr : IsIrr r) :
    (Finset.univ.filter fun i => RepIso r (tw r ((δ i).comp φ))).card ≤ 2 * n ^ 2 := by
  obtain ⟨t, ht⟩ : ∃ t, ε t ≠ 1 := by
    by_contra h
    exact h3 (MonoidHom.ext fun s => by_contra fun hs => h ⟨s, hs⟩)
  have key : ∀ c : kˣ,
      ((Finset.univ.filter fun i => RepIso r (tw r ((δ i).comp φ))).filter fun i => δ i t = c).card ≤ n ^ 2 := by
    intro c
    rw [← Finset.card_image_of_injOn (f := fun i => (δ i).comp φ)]
    · refine Br.twCard _ _ n r hr _ fun d hd => ?_
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hd
      exact (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).2
    · intro i hi' j hj hij
      exact hi (eq_of_res φ ε h1 h2 t ht _ _ hij
        ((Finset.mem_filter.1 hi').2.trans (Finset.mem_filter.1 hj).2.symm))
  refine le_trans (Finset.card_le_card (t := _ ∪ _) ?_) ((Finset.card_union_le _ _).trans
    ((add_le_add (key 1) (key (-1))).trans (two_mul _).ge))
  intro i hi
  exact Finset.mem_union.2 ((hδ i t).imp (fun h => Finset.mem_filter.2 ⟨hi, h⟩) fun h => Finset.mem_filter.2 ⟨hi, h⟩)

private theorem irr_inf {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ} (φ : Γ' →* Γ)
    (H : Subgroup Γ) (δ : Γ →* kˣ) (h1 : ∀ s, δ s = 1 ↔ s ∈ H) (h2 : ∀ s, δ s = 1 ∨ δ s = -1) (r : Γ →* GL (Fin n) k)
    (hr : IsIrr (r.comp φ)) (hn : ¬ RepIso (r.comp φ) (tw (r.comp φ) (δ.comp φ))) :
    IsIrr (r.comp (φ.range ⊓ H).subtype) := by
  have h := (Br.resTwo _ _ k n (δ.comp φ).ker.subtype (δ.comp φ) (fun s => by rw [Subgroup.range_subtype]; rfl)
    (fun s => h2 _) (r.comp φ)).1 hr hn
  refine ⟨h.1, fun _ _ _ => trivial, fun W hW hst => h.2.2 W hW fun s v hv => ?_⟩
  exact hst ⟨φ s, ⟨s, rfl⟩, (h1 _).1 s.2⟩ v hv

theorem UpperTheory.V.Z.Bc.third :
    Third := by
  intro K K' Ω _ _ _ _ _ _ _ _ _ _ _ _ _ hK hK' l _ n r hr hr'
  classical
  obtain ⟨K₀, _, _, _, hK2, hKc⟩ := Br.quadFam (4 * n ^ 2 + 1)
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let emb : ∀ i, K₀ i →ₐ[ℚ] Ω := fun i => IsAlgClosed.lift
  letI alg : ∀ i, Algebra (K₀ i) Ω := fun i => (emb i).toRingHom.toAlgebra
  haveI tow : ∀ i, IsScalarTower ℚ (K₀ i) Ω := fun i =>
    IsScalarTower.of_algebraMap_eq fun x => ((emb i).commutes x).symm
  haveI clo : ∀ i, IsAlgClosure (K₀ i) Ω := fun i => ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : IsAlgClosure K' Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  choose δ _ _ hδ _ using fun i => UpperTheory.exists_quadratic_sign_character ℚ (K₀ i) Ω l (hK2 _)
  have hδi : Function.Injective δ := fun i j hij => by
    by_contra hne
    refine Br.signNe (K₀ i) (K₀ j) Ω (hK2 _) (hKc _ _ hne) (Subgroup.ext fun s => ?_)
    rw [← (hδ i).1, ← (hδ j).1, hij]
  obtain ⟨ε, -, e0, he, -⟩ := UpperTheory.exists_quadratic_sign_character ℚ K Ω l hK
  obtain ⟨ε', -, e0', he', -⟩ := UpperTheory.exists_quadratic_sign_character ℚ K' Ω l hK'
  have c1 := card_bad (resG ℚ K Ω) ε he.1 he.2 e0 δ hδi (fun i => (hδ i).2) _ hr
  have c2 := card_bad (resG ℚ K' Ω) ε' he'.1 he'.2 e0' δ hδi (fun i => (hδ i).2) _ hr'
  have c3 := (Finset.card_union_le _ _).trans (add_le_add c1 c2)
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := Finset.univ)
    (c3.trans_lt (by rw [Finset.card_univ, Fintype.card_fin]; omega))
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hi
  exact ⟨K₀ i, inferInstance, inferInstance, inferInstance, alg i, tow i, hK2 i,
    irr_inf _ _ (δ i) (hδ i).1 (hδ i).2 r hr hi.1, irr_inf _ _ (δ i) (hδ i).1 (hδ i).2 r hr' hi.2⟩
