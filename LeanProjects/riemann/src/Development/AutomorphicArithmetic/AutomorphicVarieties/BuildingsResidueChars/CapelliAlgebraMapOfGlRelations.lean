import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.HasUnivOfStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CenterTensorProductLeSupMapCenter

open UpperTheory.V.Af.CuspFin

private theorem glRel_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) : Formalism.REAL.GlRel (fun a b => f (X a b)) := by
  intro i j k l
  have := congrArg f (h i j k l)
  simpa [apply_ite f] using this

private theorem comm_LR {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (a : A) (b : B) :
    Commute ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorProduct ℂ A B) a)
      ((Algebra.TensorProduct.includeRight : B →ₐ[ℂ] TensorProduct ℂ A B) b) := by
  simp [Commute, SemiconjBy]

private theorem map_cap {ι κ A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : ι → Fin n → Fin n → A) (F : κ → Fin n → Fin n → B) (e : ι → κ)
    (h : ∀ v, F (e v) = fun i j => f (E v i j)) : (capAlg E).map f ≤ capAlg F := by
  unfold capAlg
  rw [AlgHom.map_adjoin]
  refine Algebra.adjoin_mono ?_
  rintro _ ⟨_, ⟨v, u, rfl⟩, rfl⟩
  exact ⟨e v, u, by rw [map_qdet, h]⟩

private theorem map_gen {ι κ A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : ι → Fin n → Fin n → A) (F : κ → Fin n → Fin n → B) (e : ι → κ)
    (hg : Algebra.adjoin ℂ {z | ∃ v i j, z = E v i j} = ⊤)
    (h : ∀ v, F (e v) = fun i j => f (E v i j)) (a : A) :
    f a ∈ Algebra.adjoin ℂ {z | ∃ v i j, z = F v i j} := by
  have : (Algebra.adjoin ℂ {z | ∃ v i j, z = E v i j}).map f ≤ Algebra.adjoin ℂ {z | ∃ v i j, z = F v i j} := by
    rw [AlgHom.map_adjoin]
    refine Algebra.adjoin_mono ?_
    rintro _ ⟨_, ⟨v, i, j, rfl⟩, rfl⟩
    exact ⟨e v, i, j, by rw [h]⟩
  exact this ⟨a, by rw [hg]; trivial, rfl⟩

theorem UpperTheory.capelliAlgebra_map_of_glRelations :
    ∀ (n : ℕ) (ι κ : Type), UpperTheory.V.Af.CuspFin.HasUniv ι n → UpperTheory.V.Af.CuspFin.HasUniv κ n → UpperTheory.V.Af.CuspFin.HasUniv (ι ⊕ κ) n := by
  rintro n ι κ ⟨A, _, _, E, hE⟩ ⟨B, _, _, F, hF⟩
  let L : A →ₐ[ℂ] TensorProduct ℂ A B := Algebra.TensorProduct.includeLeft
  let R : B →ₐ[ℂ] TensorProduct ℂ A B := Algebra.TensorProduct.includeRight
  let G : ι ⊕ κ → Fin n → Fin n → TensorProduct ℂ A B :=
    Sum.elim (fun v i j => L (E v i j)) (fun v i j => R (F v i j))
  refine ⟨TensorProduct ℂ A B, inferInstance, inferInstance, G, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rintro (v | v)
    · exact glRel_map L (hE.rel.1 v)
    · exact glRel_map R (hF.rel.1 v)
  · rintro (v | v) (w | w) hvw i j k l
    · exact (hE.rel.2 v w (fun h => hvw (congrArg _ h)) i j k l).map L
    · exact comm_LR _ _
    · exact (comm_LR _ _).symm
    · exact (hF.rel.2 v w (fun h => hvw (congrArg _ h)) i j k l).map R
  · refine eq_top_iff.2 fun z hz => ?_
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul a b =>
      have : a ⊗ₜ[ℂ] b = L a * R b := by simp [L, R]
      rw [this]
      exact mul_mem (map_gen L E G Sum.inl hE.gen (fun _ => rfl) a) (map_gen R F G Sum.inr hF.gen (fun _ => rfl) b)
    | add x y hx hy => exact add_mem hx hy
  · intro C _ _ H hH
    obtain ⟨f, hf⟩ := hE.univ C (fun v => H (Sum.inl v))
      ⟨fun v => hH.1 _, fun v w hvw => hH.2 _ _ fun h => hvw (Sum.inl_injective h)⟩
    obtain ⟨g, hg⟩ := hF.univ C (fun v => H (Sum.inr v))
      ⟨fun v => hH.1 _, fun v w hvw => hH.2 _ _ fun h => hvw (Sum.inr_injective h)⟩
    have hc : ∀ a b, Commute (f a) (g b) := by
      intro a b
      have ha := map_gen f E (fun v => H (Sum.inl v)) id hE.gen (fun v => by funext i j; simp [hf]) a
      have hb := map_gen g F (fun v => H (Sum.inr v)) id hF.gen (fun v => by funext i j; simp [hg]) b
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb ?_
      rintro _ ⟨w, k, l, rfl⟩
      refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha ?_).symm
      rintro _ ⟨v, i, j, rfl⟩
      exact hH.2 _ _ Sum.inr_ne_inl _ _ _ _
    refine ⟨Algebra.TensorProduct.lift f g hc, ?_⟩
    rintro (v | v) i j
    · simp [G, L, hf]
    · simp [G, R, hg]
  · refine (UpperTheory.center_tensorProduct_le_sup_map_center A B).trans (sup_le ?_ ?_)
    · exact (Subalgebra.map_mono hE.centre).trans (map_cap L E G Sum.inl fun _ => rfl)
    · exact (Subalgebra.map_mono hF.centre).trans (map_cap R F G Sum.inr fun _ => rfl)
