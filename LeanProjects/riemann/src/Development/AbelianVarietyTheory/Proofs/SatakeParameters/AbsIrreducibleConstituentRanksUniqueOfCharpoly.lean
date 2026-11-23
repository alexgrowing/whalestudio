import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation

noncomputable section

namespace GlobalTheory.SSRank

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial

structure FRep (K Γ : Type) [Field K] [Group Γ] where
  V : Type
  [acg : AddCommGroup V]
  [mod : Module K V]
  [fd : FiniteDimensional K V]
  ρ : Representation K Γ V

attribute [instance] FRep.acg FRep.mod FRep.fd

section Main

variable {K : Type} [Field K] {Γ : Type} [Group Γ]

section BN

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def matRep {n : ℕ} (b : Module.Basis (Fin n) K V) (ρ : Representation K Γ V) : Γ →* GL (Fin n) K :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp ρ.toHomUnits

theorem matRep_coe {n : ℕ} (b : Module.Basis (Fin n) K V) (ρ : Representation K Γ V) (g : Γ) :
    ((matRep b ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = LinearMap.toMatrix b b (ρ g) := by
  ext i j
  simp [matRep, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]

theorem matRep_mulVec {n : ℕ} (b : Module.Basis (Fin n) K V) (ρ : Representation K Γ V) (g : Γ) (v : V) :
    ((matRep b ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec (b.equivFun v) = b.equivFun (ρ g v) := by
  rw [matRep_coe]
  simpa [Module.Basis.equivFun_apply] using LinearMap.toMatrix_mulVec_repr b b (ρ g) v

theorem charpoly_matRep {n : ℕ} (b : Module.Basis (Fin n) K V) (ρ : Representation K Γ V) (g : Γ) :
    ((matRep b ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly = (ρ g).charpoly := by
  rw [matRep_coe, LinearMap.charpoly_toMatrix]

theorem isSSRep_matRep {n : ℕ} (b : Module.Basis (Fin n) K V) (ρ : Representation K Γ V)
    (h : ρ.IsSemisimpleRepresentation) : IsSSRep (matRep b ρ) := by
  haveI := h
  intro W hW
  let e := b.equivFun
  let S : Subrepresentation ρ := ⟨W.comap (e : V →ₗ[K] Fin n → K), fun g v hv => by
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
    rw [← matRep_mulVec]
    exact hW g _ hv⟩
  obtain ⟨C, hC⟩ := exists_isCompl S
  refine ⟨C.toSubmodule.map (e : V →ₗ[K] Fin n → K), ?_, ?_⟩
  · intro g w hw
    obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hw
    refine Submodule.mem_map.2 ⟨ρ g c, C.apply_mem_toSubmodule g hc, ?_⟩
    simp only [LinearEquiv.coe_coe]
    rw [matRep_mulVec]
  · have h1 : IsCompl S.toSubmodule C.toSubmodule :=
      ⟨disjoint_iff.2 (congrArg Subrepresentation.toSubmodule hC.inf_eq_bot),
        codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule hC.sup_eq_top)⟩
    have h2 := (Submodule.orderIsoMapComap e).isCompl_iff.1 h1
    have h3 : (Submodule.orderIsoMapComap e) S.toSubmodule = W := by
      show Submodule.map (e : V →ₗ[K] Fin n → K) (W.comap (e : V →ₗ[K] Fin n → K)) = W
      exact Submodule.map_comap_eq_of_surjective e.surjective W
    rw [h3] at h2
    exact h2

theorem bn_gen {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K Γ V) (σ : Representation K Γ W)
    (hρ : IsSemisimpleModule (MonoidAlgebra K Γ) ρ.asModule)
    (hσ : IsSemisimpleModule (MonoidAlgebra K Γ) σ.asModule)
    (hc : ∀ g, (ρ g).charpoly = (σ g).charpoly) :
    ∃ e : V ≃ₗ[K] W, ∀ g, (e : V →ₗ[K] W) ∘ₗ ρ g = σ g ∘ₗ (e : V →ₗ[K] W) := by
  have hn : Module.finrank K V = Module.finrank K W := by
    have := congrArg natDegree (hc 1)
    rwa [LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree] at this
  let bV : Module.Basis (Fin (Module.finrank K W)) K V := Module.finBasisOfFinrankEq K V hn
  let bW : Module.Basis (Fin (Module.finrank K W)) K W := Module.finBasisOfFinrankEq K W rfl
  obtain ⟨Pm, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix (matRep bV ρ) (matRep bW σ)
    (isSSRep_matRep bV ρ ((Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).2 hρ))
    (isSSRep_matRep bW σ ((Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).2 hσ))
    (fun g => by rw [charpoly_matRep, charpoly_matRep, hc])
  let e0 : (Fin (Module.finrank K W) → K) ≃ₗ[K] (Fin (Module.finrank K W) → K) :=
    Matrix.toLin'OfInv (M := ((Pm : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K)) (M' := ((Pm⁻¹ : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K))
      Pm.mul_inv Pm.inv_mul
  refine ⟨bV.equivFun ≪≫ₗ e0 ≪≫ₗ bW.equivFun.symm, fun g => LinearMap.ext fun x => ?_⟩
  have hg : ((Pm⁻¹ : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) * ((matRep bV ρ g : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) =
      ((matRep bW σ g : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) * ((Pm⁻¹ : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) := by
    rw [hP g]
    simp only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have key : bW.equivFun (σ g (bW.equivFun.symm (e0 (bV.equivFun x)))) =
      bW.equivFun (bW.equivFun.symm (e0 (bV.equivFun (ρ g x)))) := by
    rw [← matRep_mulVec, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, ← matRep_mulVec]
    have he0 : ∀ y, e0 y = ((Pm⁻¹ : GL (Fin (Module.finrank K W)) K) : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).mulVec y := fun y => Matrix.toLin'_apply _ _
    rw [he0, he0, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]
  simpa using (bW.equivFun.injective key).symm

end BN

def sumRep (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) : FRep K Γ :=
  L.rec { V := Fin 0 → K, ρ := 1 } fun p _ r => { V := (Fin p.1 → K) × r.V, ρ := (glRep p.2).prod r.ρ }

def cpL (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (g : Γ) : K[X] :=
  (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod

theorem cpL_nil (g : Γ) : cpL ([] : List (Σ m : ℕ, Γ →* GL (Fin m) K)) g = 1 := rfl

theorem cpL_cons (p : Σ m : ℕ, Γ →* GL (Fin m) K) (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (g : Γ) :
    cpL (p :: L) g = ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly * cpL L g := by
  simp [cpL]

theorem cpL_perm {L L' : List (Σ m : ℕ, Γ →* GL (Fin m) K)} (h : L.Perm L') (g : Γ) :
    cpL L g = cpL L' g :=
  (h.map _).prod_eq

theorem glRep_app {m : ℕ} (ρ : Γ →* GL (Fin m) K) (g : Γ) (v : Fin m → K) :
    glRep ρ g v = ((ρ g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).mulVec v := by
  rw [Formalism.MainNotions.SumRepresentations.glRep_apply, Matrix.toLin'_apply]

theorem charpoly_fin_zero (f : Module.End K (Fin 0 → K)) : f.charpoly = 1 := by
  rw [← LinearMap.charpoly_toMatrix f (Pi.basisFun K (Fin 0))]
  exact eq_one_of_monic_natDegree_zero (Matrix.charpoly_monic _)
    (by rw [Matrix.charpoly_natDegree_eq_dim]; simp)

theorem cp_sumRep : ∀ (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (g : Γ),
    ((sumRep L).ρ g).charpoly = cpL L g
  | [], g => charpoly_fin_zero _
  | p :: L, g => by
    rw [cpL_cons, ← cp_sumRep L g]
    show (((glRep p.2) g).prodMap ((sumRep L).ρ g)).charpoly = _
    rw [LinearMap.charpoly_prodMap]
    congr 1
    exact Matrix.charpoly_toLin' _

theorem cpL_deg : ∀ (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (g : Γ),
    (cpL L g).Monic ∧ (cpL L g).natDegree = (L.map Sigma.fst).sum
  | [], g => ⟨monic_one, by simp [cpL]⟩
  | p :: L, g => by
    have ih := cpL_deg L g
    rw [cpL_cons]
    refine ⟨(Matrix.charpoly_monic _).mul ih.1, ?_⟩
    rw [(Matrix.charpoly_monic _).natDegree_mul ih.1, ih.2, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
    simp

theorem asAlg_prod {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K Γ V) (σ : Representation K Γ W) (r : MonoidAlgebra K Γ) (x : V × W) :
    (ρ.prod σ).asAlgebraHom r x = (ρ.asAlgebraHom r x.1, σ.asAlgebraHom r x.2) := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of,
      Representation.asAlgebraHom_of]
    rfl
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, Prod.mk_add_mk]
  | smul c a ha => simp only [map_smul, LinearMap.smul_apply, ha, Prod.smul_mk]

def prodEquiv {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K Γ V) (σ : Representation K Γ W) :
    (ρ.prod σ).asModule ≃ₗ[MonoidAlgebra K Γ] ρ.asModule × σ.asModule where
  toFun x := (show V × W from x)
  invFun x := (show V × W from x)
  map_add' _ _ := rfl
  map_smul' r x := by
    change (ρ.prod σ).asAlgebraHom r (show V × W from x) =
      (ρ.asAlgebraHom r (show V × W from x).1, σ.asAlgebraHom r (show V × W from x).2)
    exact asAlg_prod ρ σ r _
  left_inv _ := rfl
  right_inv _ := rfl

theorem ss_prod {R M N : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsSemisimpleModule R M] [IsSemisimpleModule R N] : IsSemisimpleModule R (M × N) := by
  have h : IsSemisimpleModule R ↥(LinearMap.range (LinearMap.inl R M N) ⊔
      LinearMap.range (LinearMap.inr R M N)) :=
    IsSemisimpleModule.sup (IsSemisimpleModule.range _) (IsSemisimpleModule.range _)
  rw [LinearMap.sup_range_inl_inr] at h
  exact IsSemisimpleModule.congr (Submodule.topEquiv (R := R) (M := M × N)).symm

theorem simple_of_irr {m : ℕ} (ρ : Γ →* GL (Fin m) K) (h : IsIrrSub ρ ⊤) :
    IsSimpleModule (MonoidAlgebra K Γ) (glRep ρ).asModule := by
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => h.1 ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · exact (congrArg Subrepresentation.toSubmodule hbt).symm
  · rcases h.2.2 W.toSubmodule le_top (fun g v hv => by
        rw [← glRep_app]; exact W.apply_mem_toSubmodule g hv) with h0 | h0
    · exact Or.inl (Subrepresentation.toSubmodule_injective h0)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h0)

theorem ss_sumRep : ∀ (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)), (∀ p ∈ L, IsIrrSub p.2 ⊤) →
    IsSemisimpleModule (MonoidAlgebra K Γ) (sumRep L).ρ.asModule
  | [], _ => by
    have : Subsingleton (sumRep ([] : List (Σ m : ℕ, Γ →* GL (Fin m) K))).ρ.asModule :=
      inferInstanceAs (Subsingleton (Fin 0 → K))
    exact IsSemisimpleModule.of_sSup_simples_eq_top (Subsingleton.elim _ _)
  | p :: L, hL => by
    have := simple_of_irr p.2 (hL p (by simp))
    have := ss_sumRep L (fun r hr => hL r (by simp [hr]))
    have := ss_prod (R := MonoidAlgebra K Γ) (M := (glRep p.2).asModule) (N := (sumRep L).ρ.asModule)
    exact IsSemisimpleModule.congr (prodEquiv (glRep p.2) (sumRep L).ρ)

theorem exists_summand (p : Σ m : ℕ, Γ →* GL (Fin m) K) (hp : IsIrrSub p.2 ⊤) :
    ∀ (L' : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (F : (Fin p.1 → K) →ₗ[K] (sumRep L').V),
      Function.Injective F → (∀ g v, F (glRep p.2 g v) = (sumRep L').ρ g (F v)) →
      ∃ q ∈ L', ∃ φ : (Fin p.1 → K) →ₗ[K] (Fin q.1 → K), Function.Injective φ ∧
        ∀ g v, φ (glRep p.2 g v) = glRep q.2 g (φ v) := by
  intro L'
  induction L' with
  | nil =>
    intro F hF _
    exfalso
    have : Subsingleton (sumRep ([] : List (Σ m : ℕ, Γ →* GL (Fin m) K))).V :=
      inferInstanceAs (Subsingleton (Fin 0 → K))
    have hex := (Submodule.ne_bot_iff _).1 hp.1
    exact hex.elim fun v hv => hv.2 (hF (Subsingleton.elim _ _))
  | cons q L'' ih =>
    intro F hF hint
    let F1 : (Fin p.1 → K) →ₗ[K] (Fin q.1 → K) := LinearMap.fst K _ _ ∘ₗ F
    let F2 : (Fin p.1 → K) →ₗ[K] (sumRep L'').V := LinearMap.snd K _ _ ∘ₗ F
    have h1 : ∀ g v, F1 (glRep p.2 g v) = glRep q.2 g (F1 v) := fun g v =>
      congrArg Prod.fst (hint g v)
    have h2 : ∀ g v, F2 (glRep p.2 g v) = (sumRep L'').ρ g (F2 v) := fun g v =>
      congrArg Prod.snd (hint g v)
    have hinv : IsInv p.2 (LinearMap.ker F1) := by
      intro g v hv
      rw [LinearMap.mem_ker] at hv ⊢
      rw [← glRep_app, h1, hv, map_zero]
    rcases hp.2.2 (LinearMap.ker F1) le_top hinv with hk | hk
    · exact ⟨q, by simp, F1, LinearMap.ker_eq_bot.1 hk, h1⟩
    · have hz : ∀ v, F1 v = 0 := fun v => LinearMap.mem_ker.1 (hk ▸ Submodule.mem_top)
      have hF2 : Function.Injective F2 := fun v w hvw =>
        hF (Prod.ext ((hz v).trans (hz w).symm) hvw)
      have hr := ih F2 hF2 h2
      exact hr.elim fun r hr => ⟨r, by simp [hr.1], hr.2⟩

theorem iso_of_inj (p q : Σ m : ℕ, Γ →* GL (Fin m) K) (hp : IsIrrSub p.2 ⊤) (hq : IsIrrSub q.2 ⊤)
    (φ : (Fin p.1 → K) →ₗ[K] (Fin q.1 → K)) (hφ : Function.Injective φ)
    (hint : ∀ g v, φ (glRep p.2 g v) = glRep q.2 g (φ v)) :
    p.1 = q.1 ∧ ∀ g, ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly =
      ((q.2 g : GL _ _) : Matrix (Fin q.1) (Fin q.1) K).charpoly := by
  have hinv : IsInv q.2 (LinearMap.range φ) := by
    intro g v hv
    rw [← glRep_app]
    rcases LinearMap.mem_range.1 hv with ⟨w, hw⟩
    rw [← hw, ← hint]
    exact LinearMap.mem_range_self _ _
  have hne : LinearMap.range φ ≠ ⊥ := by
    intro h0
    have hex := (Submodule.ne_bot_iff _).1 hp.1
    refine hex.elim fun v hv => hv.2 (hφ ?_)
    have hm : φ v ∈ LinearMap.range φ := LinearMap.mem_range_self _ _
    rw [h0, Submodule.mem_bot] at hm
    rw [hm, map_zero]
  rcases hq.2.2 _ le_top hinv with h0 | htop
  · exact absurd h0 hne
  have hsurj : Function.Surjective φ := LinearMap.range_eq_top.1 htop
  let e := LinearEquiv.ofBijective φ ⟨hφ, hsurj⟩
  refine ⟨?_, fun g => ?_⟩
  · simpa using e.finrank_eq
  · have key : ∀ w, e (glRep p.2 g w) = glRep q.2 g (e w) := by
      intro w
      simp only [e]
      exact hint g w
    have hc : e.conj (glRep p.2 g) = glRep q.2 g := by
      refine LinearMap.ext fun v => ?_
      rw [LinearEquiv.conj_apply_apply, key, LinearEquiv.apply_symm_apply]
    have hcp := LinearEquiv.charpoly_conj e (glRep p.2 g)
    rw [hc] at hcp
    rw [← Matrix.charpoly_toLin', ← Matrix.charpoly_toLin']
    exact hcp.symm

theorem main : ∀ (L L' : List (Σ m : ℕ, Γ →* GL (Fin m) K)),
    (∀ p ∈ L, 1 ≤ p.1 ∧ IsIrrSub p.2 ⊤) → (∀ p ∈ L', 1 ≤ p.1 ∧ IsIrrSub p.2 ⊤) →
    (∀ g, cpL L g = cpL L' g) → (L.map Sigma.fst).Perm (L'.map Sigma.fst)
  | [], [], _, _, _ => List.Perm.refl _
  | [], q :: t, _, hL', h => by
    exfalso
    have h1 := (cpL_deg (q :: t) 1).2
    rw [← h 1, cpL_nil, natDegree_one] at h1
    have hq := (hL' q (by simp)).1
    simp only [List.map_cons, List.sum_cons] at h1
    omega
  | p :: L, L', hL, hL', h => by
    have hp := hL p (by simp)
    have hss := ss_sumRep (p :: L) (fun r hr => (hL r hr).2)
    have hss' := ss_sumRep L' (fun r hr => (hL' r hr).2)
    have hcp : ∀ g, ((sumRep (p :: L)).ρ g).charpoly = ((sumRep L').ρ g).charpoly := fun g => by
      rw [cp_sumRep, cp_sumRep, h g]
    have hBN := bn_gen (sumRep (p :: L)).ρ (sumRep L').ρ hss hss' hcp
    refine hBN.elim fun e he => ?_
    let F : (Fin p.1 → K) →ₗ[K] (sumRep L').V :=
      e.toLinearMap ∘ₗ LinearMap.inl K (Fin p.1 → K) (sumRep L).V
    have hF : Function.Injective F := e.injective.comp LinearMap.inl_injective
    have hint : ∀ g v, F (glRep p.2 g v) = (sumRep L').ρ g (F v) := by
      intro g v
      have h0 : (sumRep (p :: L)).ρ g ((v, 0) : (Fin p.1 → K) × (sumRep L).V) =
          ((glRep p.2 g v, 0) : (Fin p.1 → K) × (sumRep L).V) := by
        show ((glRep p.2 g).prodMap ((sumRep L).ρ g)) (v, 0) = _
        rw [LinearMap.prodMap_apply, map_zero]
      have h3 := LinearMap.congr_fun (he g) ((v, 0) : (Fin p.1 → K) × (sumRep L).V)
      change e ((sumRep (p :: L)).ρ g (v, 0)) = (sumRep L').ρ g (e (v, 0)) at h3
      exact (congrArg (fun x => e x) h0).symm.trans h3
    have hS := exists_summand p hp.2 L' F hF hint
    refine hS.elim fun q hq => ?_
    refine hq.2.elim fun φ hφ => ?_
    have hI := iso_of_inj p q hp.2 (hL' q hq.1).2 φ hφ.1 hφ.2
    have hsplit := List.append_of_mem hq.1
    refine hsplit.elim fun s hs => hs.elim fun t hst => ?_
    subst hst
    have hperm : (s ++ q :: t).Perm (q :: (s ++ t)) := List.perm_middle
    have hcut : ∀ g, cpL L g = cpL (s ++ t) g := by
      intro g
      have h1 := h g
      rw [cpL_cons, cpL_perm hperm, cpL_cons, hI.2 g] at h1
      exact mul_left_cancel₀ (Matrix.charpoly_monic _).ne_zero h1
    have ih := main L (s ++ t) (fun r hr => hL r (by simp [hr]))
      (fun r hr => hL' r (by simp only [List.mem_append, List.mem_cons] at hr ⊢; tauto)) hcut
    have h4 : ((p :: L).map Sigma.fst).Perm ((q :: (s ++ t)).map Sigma.fst) := by
      simp only [List.map_cons]
      rw [hI.1]
      exact ih.cons _
    exact h4.trans (hperm.symm.map _)

end Main

section Closure

variable {k : Type} [Field k] {Γ : Type} [Group Γ]

theorem span_image_top (m : ℕ) :
    Submodule.span (AlgebraicClosure k)
      ((fun v : Fin m → k => (algebraMap k (AlgebraicClosure k)) ∘ v) '' (⊤ : Submodule k (Fin m → k))) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun (AlgebraicClosure k) (Fin m)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  refine ⟨Pi.single i 1, Submodule.mem_top, ?_⟩
  funext j
  by_cases hj : j = i <;> simp [hj]

def liftL (L : List (Σ m : ℕ, Γ →* GL (Fin m) k)) : List (Σ m : ℕ, Γ →* GL (Fin m) (AlgebraicClosure k)) :=
  L.map fun p => ⟨p.1, mapRep (algebraMap k (AlgebraicClosure k)) p.2⟩

theorem cpL_liftL : ∀ (L : List (Σ m : ℕ, Γ →* GL (Fin m) k)) (g : Γ),
    cpL (liftL L) g = (cpL L g).map (algebraMap k (AlgebraicClosure k))
  | [], g => by simp [liftL, cpL]
  | p :: L, g => by
    have ih := cpL_liftL L g
    simp only [liftL, List.map_cons] at ih ⊢
    rw [cpL_cons, cpL_cons, ih, Polynomial.map_mul, ← Matrix.charpoly_map]
    rfl

theorem fst_liftL (L : List (Σ m : ℕ, Γ →* GL (Fin m) k)) :
    (liftL L).map Sigma.fst = L.map Sigma.fst := by
  rw [liftL, List.map_map]
  rfl

theorem irr_liftL (L : List (Σ m : ℕ, Γ →* GL (Fin m) k)) (hL : ∀ p ∈ L, 1 ≤ p.1 ∧ AbsIrrSub p.2 ⊤) :
    ∀ p ∈ liftL L, 1 ≤ p.1 ∧ IsIrrSub p.2 ⊤ := by
  intro p hp
  rw [liftL, List.mem_map] at hp
  refine hp.elim fun a ha => ?_
  rw [← ha.2]
  refine ⟨(hL a ha.1).1, ?_⟩
  have h := (hL a ha.1).2
  unfold AbsIrrSub at h
  rw [span_image_top] at h
  exact h

end Closure

theorem ssRankUnique_holds : GlobalTheory.StringRepresentationDecomposition.SSRankUnique := by
  intro k _ Γ _ L L' hL hL' h
  have hP := main (liftL L) (liftL L') (irr_liftL L hL) (irr_liftL L' hL') (fun g => by
    rw [cpL_liftL, cpL_liftL]
    exact congrArg _ (h g))
  rw [fst_liftL, fst_liftL] at hP
  exact Multiset.coe_eq_coe.2 hP

end GlobalTheory.SSRank
