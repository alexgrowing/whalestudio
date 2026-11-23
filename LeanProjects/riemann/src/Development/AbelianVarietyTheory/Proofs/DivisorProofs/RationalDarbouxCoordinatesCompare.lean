import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

theorem sumElim_weylM_map {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ] {R : Type} [CommRing R]
    [Algebra F R] (a b a' b' : κ → R) :
    Sum.elim a b ⬝ᵥ ((weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R)) *ᵥ Sum.elim a' b' =
      a ⬝ᵥ b' - a' ⬝ᵥ b := by
  simp only [weylM, Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec]
  simp [Matrix.map_neg, Matrix.neg_mulVec, dotProduct_comm b a', sub_eq_add_neg]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in

theorem darboux_change_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (c₁ c₂ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d)),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₁.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₂.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ G : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F,
      GlobalTheory.SympChange.IsSymp G ∧ ∀ w, c₂.e w = GlobalTheory.SympChange.spAct G (c₁.e w) := by
  intro F E _ _ _ _ _ σ n d JX JW c₁ c₂ h₁ h₂
  classical
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  have hAinj : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective _ _

  have honto : ∀ y z : Fin n × Fin d → F, ∃ x : Matrix (Fin n) (Fin d) E,
      c₁.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
    intro y z
    let I : Matrix (Fin n) (Fin d) E →ₗ[F] Matrix (Fin n) (Fin d) (AE F E) :=
      (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).toLinearMap.mapMatrix
    let L : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
      (c₁.e.toLinearMap.restrictScalars F).comp I
    have hL : ∀ x, L x = c₁.e (incM F x) := fun x => rfl
    let r : (Fin n × Fin d → F) →ₗ[F] (Fin n × Fin d → AF F) :=
      LinearMap.pi fun i => (Algebra.linearMap F (AF F)).comp (LinearMap.proj i)
    let R : ((Fin n × Fin d → F) × (Fin n × Fin d → F)) →ₗ[F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
      LinearMap.prodMap r r
    have hR : ∀ y z, R (y, z) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) :=
      fun _ _ => rfl
    have hrinj : Function.Injective r := fun a b h => funext fun i => hAinj (congrFun h i)
    have hRinj : Function.Injective R := fun a b h =>
      Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))
    have hIinj : Function.Injective I := fun a b h => Matrix.ext fun i j =>
      Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)
    have hLinj : Function.Injective L := c₁.e.injective.comp hIinj
    have hle : LinearMap.range L ≤ LinearMap.range R := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y', z', h⟩ := h₁ x
      exact ⟨(y', z'), by rw [hR, hL, h]⟩
    have hdim : Fintype.card (Fin n) * Fintype.card (Fin d) * Module.finrank F E =
        Fintype.card (Fin n × Fin d) + Fintype.card (Fin n × Fin d) := by
      have h1 := c₁.e.finrank_eq
      rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h1
      exact h1
    have hfin : Module.finrank F (LinearMap.range L) = Module.finrank F (LinearMap.range R) := by
      rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix,
        Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hdim]
    have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
    obtain ⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L := heq ▸ ⟨(y, z), rfl⟩
    exact ⟨x, by rw [← hL, hx, hR]⟩

  let g : ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) ≃ₗ[AF F]
      ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) := c₁.e.symm.trans c₂.e
  have hgrat : ∀ y z : Fin n × Fin d → F, ∃ y' z' : Fin n × Fin d → F,
      g (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) =
        (fun i => algebraMap F (AF F) (y' i), fun i => algebraMap F (AF F) (z' i)) := by
    intro y z
    obtain ⟨x, hx⟩ := honto y z
    obtain ⟨y', z', h⟩ := h₂ x
    exact ⟨y', z', by rw [← hx]; simp only [g, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, h]⟩
  let S := LinearEquiv.sumArrowLequivProdArrow (Fin n × Fin d) (Fin n × Fin d) (AF F) (AF F)
  let φ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) →ₗ[AF F] ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) :=
    (S.symm.toLinearMap.comp g.toLinearMap).comp S.toLinearMap
  have hφ : ∀ s, φ s = S.symm (g (S s)) := fun s => rfl
  have hent : ∀ i j, ∃ c : F, LinearMap.toMatrix' φ i j = algebraMap F (AF F) c := by
    intro i j
    rw [LinearMap.toMatrix'_apply]
    obtain ⟨y', z', h⟩ := hgrat (fun k => (Pi.single j (1 : F) : _ → F) (Sum.inl k))
      (fun k => (Pi.single j (1 : F) : _ → F) (Sum.inr k))
    have hS : S (Pi.single j 1) = (fun k => algebraMap F (AF F) ((Pi.single j (1 : F) : _ → F) (Sum.inl k)),
        fun k => algebraMap F (AF F) ((Pi.single j (1 : F) : _ → F) (Sum.inr k))) := by
      ext k <;> simp [S, Pi.single_apply, apply_ite]
    refine ⟨Sum.elim y' z' i, ?_⟩
    rw [hφ, hS, h]
    cases i <;> simp [S]
  obtain ⟨G, hG⟩ : ∃ G : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F,
      ∀ i j, LinearMap.toMatrix' φ i j = algebraMap F (AF F) (G i j) :=
    ⟨Matrix.of fun i j => (hent i j).choose, fun i j => (hent i j).choose_spec⟩
  have hGm : G.map (algebraMap F (AF F)) = LinearMap.toMatrix' φ := Matrix.ext fun i j => (hG i j).symm
  have hact : ∀ u, g u = spAct G u := by
    intro u
    have h1 : spAct G u = S (LinearMap.toMatrix' φ *ᵥ S.symm u) := by
      rw [← hGm]; rfl
    rw [h1, LinearMap.toMatrix'_mulVec, hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

  have hstd : ∀ u u' : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F),
      S.symm u ⬝ᵥ (weylM.map (algebraMap F (AF F))) *ᵥ S.symm u' = u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2 := by
    intro u u'
    obtain ⟨a, b⟩ := u
    obtain ⟨a', b'⟩ := u'
    have hs : ∀ p q : Fin n × Fin d → AF F, S.symm (p, q) = Sum.elim p q := fun p q => funext fun k => by
      cases k <;> simp [S]
    rw [hs, hs]
    exact sumElim_weylM_map a b a' b'
  have hkeep : ∀ u u' : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F),
      (g u).1 ⬝ᵥ (g u').2 - (g u').1 ⬝ᵥ (g u).2 = u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2 := by
    intro u u'
    have e2 := c₂.form (c₁.e.symm u) (c₁.e.symm u')
    have e1 := c₁.form (c₁.e.symm u) (c₁.e.symm u')
    simp only [LinearEquiv.apply_symm_apply] at e1
    simp only [g, LinearEquiv.trans_apply]
    rw [← e2, e1]
  refine ⟨G, ?_, fun w => ?_⟩
  · unfold IsSymp
    refine Matrix.map_injective hAinj ?_
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hGm]
    ext i j
    have key : ∀ s s' : (Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F,
        s ⬝ᵥ ((LinearMap.toMatrix' φ)ᵀ * weylM.map (algebraMap F (AF F)) * LinearMap.toMatrix' φ) *ᵥ s' =
          s ⬝ᵥ (weylM.map (algebraMap F (AF F))) *ᵥ s' := by
      intro s s'
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
        LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hφ, hφ, hstd, hkeep,
        ← hstd, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    have := key (Pi.single i 1) (Pi.single j 1)
    simpa [single_dotProduct, Matrix.mulVec_single_one] using this
  · have := hact (c₁.e w)
    simpa [g] using this

end GlobalTheory.SympChange
