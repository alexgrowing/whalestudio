import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent

namespace GlobalTheory.WeilDeligne.InertiaSplit

variable {l : ℕ} [Fact l.Prime]

theorem toEndC_coord (ι : Qbar l ≃+* ℂ) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n (Qbar l)) (v : n → Qbar l) :
    toEndC ι M (fun k => ι (v k)) = fun i => ι ((M.mulVec v) i) := by
  funext i
  rw [toEndC_apply, Matrix.toLin'_apply]
  exact (RingHom.map_mulVec ι.toRingHom M v i).symm

theorem mem_of_exp (ι : Qbar l ≃+* ℂ) {n : Type} [Fintype n] [DecidableEq n]
    (S : Submodule ℂ (n → ℂ)) {M : Matrix n n (Qbar l)} (hM : IsNilpotent M)
    (hS : ∀ v ∈ S, toEndC ι M v ∈ S) : ∀ v ∈ S, toEndC ι (exp M) v ∈ S := by
  obtain ⟨k, hk⟩ := hM
  intro v hv
  rw [exp_eq_sum hk, map_sum, LinearMap.sum_apply]
  refine S.sum_mem fun i hi => ?_
  clear hi
  rw [map_rat_smul, LinearMap.smul_apply, map_pow]
  refine S.smul_of_tower_mem _ ?_
  induction i with
  | zero => simpa using hv
  | succ i ih => rw [pow_succ', Module.End.mul_apply]; exact hS _ ih

theorem exp_apply_of_eq_zero (ι : Qbar l ≃+* ℂ) {n : Type} [Fintype n] [DecidableEq n]
    {M : Matrix n n (Qbar l)} (hM : IsNilpotent M) {v : n → ℂ} (hv : toEndC ι M v = 0) :
    toEndC ι (exp M) v = v := by
  obtain ⟨k, hk⟩ := hM
  rw [exp_eq_sum (k := k + 1) (pow_eq_zero_of_le (Nat.le_succ k) hk), Finset.sum_range_succ', map_add,
    map_sum, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_eq_zero]
  · simp
  · intro i _
    rw [map_rat_smul, LinearMap.smul_apply, map_pow, _root_.pow_succ, Module.End.mul_apply, hv, map_zero,
      smul_zero]

theorem eq_algebraMap_of_charpoly {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {x : Module.End ℂ V} (hs : x.IsSemisimple) {z : ℂ}
    (hc : x.charpoly = (X - C z) ^ finrank ℂ V) : x = algebraMap ℂ (Module.End ℂ V) z := by
  have h0 := LinearMap.aeval_self_charpoly x
  rw [hc, map_pow, map_sub, aeval_X, aeval_C] at h0
  have hs' : (x - algebraMap ℂ (Module.End ℂ V) z).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hs
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs')

def pull (ι : Qbar l ≃+* ℂ) {a n m : ℕ} (f : (Fin a → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ)) :
    (Fin a → Qbar l) ≃ₗ[Qbar l] (Fin n → Qbar l) × (Fin m → Qbar l) where
  toFun v := (fun j => ι.symm ((f (fun k => ι (v k))).1 j), fun j => ι.symm ((f (fun k => ι (v k))).2 j))
  invFun y := fun k => ι.symm (f.symm (fun j => ι (y.1 j), fun j => ι (y.2 j)) k)
  map_add' v v' := by
    have e : (fun k => ι ((v + v') k)) = (fun k => ι (v k)) + fun k => ι (v' k) := by
      funext k; simp
    simp only [e, map_add]
    ext j <;> simp
  map_smul' c v := by
    have e : (fun k => ι ((c • v) k)) = ι c • fun k => ι (v k) := by funext k; simp
    simp only [e, map_smul]
    ext j <;> simp
  left_inv v := by
    funext k; simp
  right_inv y := by
    ext j <;> simp

theorem pull_apply (ι : Qbar l ≃+* ℂ) {a n m : ℕ} (f : (Fin a → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ))
    (v : Fin a → Qbar l) :
    pull ι f v = (fun j => ι.symm ((f (fun k => ι (v k))).1 j),
      fun j => ι.symm ((f (fun k => ι (v k))).2 j)) := rfl

theorem pull_fst_eq_zero (ι : Qbar l ≃+* ℂ) {a n m : ℕ} (f : (Fin a → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ))
    (v : Fin a → Qbar l) : (pull ι f v).1 = 0 ↔ (f (fun k => ι (v k))).1 = 0 := by
  rw [pull_apply]
  constructor
  · intro e; funext j; simpa using congrFun e j
  · intro e; funext j; simp [e]

theorem pull_snd_eq_zero (ι : Qbar l ≃+* ℂ) {a n m : ℕ} (f : (Fin a → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ))
    (v : Fin a → Qbar l) : (pull ι f v).2 = 0 ↔ (f (fun k => ι (v k))).2 = 0 := by
  rw [pull_apply]
  constructor
  · intro e; funext j; simpa using congrFun e j
  · intro e; funext j; simp [e]

end GlobalTheory.WeilDeligne.InertiaSplit

namespace GlobalTheory.WeilDeligne.InertiaSplit

variable {l : ℕ} [Fact l.Prime]
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem split_away (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (r : G E Ω →* GL (Fin a) (Qbar l))
    (hr : Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)))
    (x y : WD h) (hxy : wdOf h hl ι r = x.lpSum y) :
    ∃ U U' : Submodule (Qbar l) (Fin a → Qbar l), IsCompl U U' ∧ finrank (Qbar l) U = x.lpDim ∧
      finrank (Qbar l) U' = y.lpDim ∧
      (∀ σ ∈ Ine (F := E) A,
        (∀ v ∈ U, ((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).mulVec v ∈ U) ∧
        (∀ v ∈ U', ((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).mulVec v ∈ U')) ∧
      (y.mono0 → ∀ σ ∈ Ine (F := E) A, ∀ c : Qbar l, y.inePol σ = (X - C (ι c)) ^ y.lpDim →
        ∀ v ∈ U', ((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).mulVec v = c • v) := by
  induction x using WD.ind with | hP n b => ?_
  induction y using WD.ind with | hP m c => ?_
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hr
  obtain ⟨z, hz, e⟩ := hN.wdOf_spec hl ht (deg_frob (h := h)) ι
  rw [e, WD.lpSum_mk, WD.mk_eq_mk] at hxy
  obtain ⟨f, hfρ, hfN⟩ := hxy

  have hin : ∀ σ (hσ : σ ∈ Ine (F := E) A) (u : Fin a → ℂ),
      toEndC ι ((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) u =
        z.ρ (ineIncl h ⟨σ, hσ⟩) (toEndC ι (exp (tval (tameL h hl) ⟨σ, hσ⟩ • N)) u) := by
    intro σ hσ u
    have hm : ((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) =
        wdMat (tameL h hl) (deg_frob (h := h)) r N (ineIncl h ⟨σ, hσ⟩) *
          exp (tval (tameL h hl) ⟨σ, hσ⟩ • N) := by
      rw [wdMat_ineIncl, mul_assoc, ← exp_add_smul hN.1, neg_add_cancel, zero_smul,
        IsNilpotent.exp_zero, mul_one]
    rw [hm, map_mul, Module.End.mul_apply, ← hN.rep_apply hl ht deg_frob ι,
      ← hz.ρ_ineIncl (hN.isSmooth_rep hl ht deg_frob ι)]

  have stρ2 : ∀ g u, (f u).2 = 0 → (f (z.ρ g u)).2 = 0 := fun g u hu => by
    rw [hfρ]; simp [hu]
  have stρ1 : ∀ g u, (f u).1 = 0 → (f (z.ρ g u)).1 = 0 := fun g u hu => by
    rw [hfρ]; simp [hu]
  have stN2 : ∀ u, (f u).2 = 0 → (f (z.N u)).2 = 0 := fun u hu => by
    rw [hfN]; simp [hu]
  have stN1 : ∀ u, (f u).1 = 0 → (f (z.N u)).1 = 0 := fun u hu => by
    rw [hfN]; simp [hu]
  have ste2 : ∀ (s : Qbar l) u, (f u).2 = 0 → (f (toEndC ι (exp (s • N)) u)).2 = 0 := by
    intro s u hu
    have := mem_of_exp ι (LinearMap.ker ((LinearMap.snd ℂ (Fin n → ℂ) (Fin m → ℂ)).comp
      (f : (Fin a → ℂ) →ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ)))) (hN.1.smul s) (fun v hv => by
        simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply,
          LinearEquiv.coe_coe] at hv ⊢
        rw [toEndC_smul, LinearMap.smul_apply, ← hz.1, map_smul, Prod.smul_snd, stN2 v hv, smul_zero])
      u (by simpa using hu)
    simpa using this
  have ste1 : ∀ (s : Qbar l) u, (f u).1 = 0 → (f (toEndC ι (exp (s • N)) u)).1 = 0 := by
    intro s u hu
    have := mem_of_exp ι (LinearMap.ker ((LinearMap.fst ℂ (Fin n → ℂ) (Fin m → ℂ)).comp
      (f : (Fin a → ℂ) →ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ)))) (hN.1.smul s) (fun v hv => by
        simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply,
          LinearEquiv.coe_coe] at hv ⊢
        rw [toEndC_smul, LinearMap.smul_apply, ← hz.1, map_smul, Prod.smul_fst, stN1 v hv, smul_zero])
      u (by simpa using hu)
    simpa using this

  have hC : IsCompl (LinearMap.ker (LinearMap.snd (Qbar l) (Fin n → Qbar l) (Fin m → Qbar l)))
      (LinearMap.ker (LinearMap.fst (Qbar l) (Fin n → Qbar l) (Fin m → Qbar l))) := by
    rw [← LinearMap.range_inl, ← LinearMap.range_inr]
    exact LinearMap.isCompl_range_inl_inr
  have hC' := (Submodule.orderIsoMapComap (pull ι f).symm).isCompl hC
  simp only [Submodule.orderIsoMapComap_apply] at hC'
  have memU : ∀ v : Fin a → Qbar l, v ∈ (LinearMap.ker (LinearMap.snd (Qbar l) (Fin n → Qbar l) (Fin m → Qbar l))).map
      ((pull ι f).symm : (Fin n → Qbar l) × (Fin m → Qbar l) →ₗ[Qbar l] (Fin a → Qbar l)) ↔ (f (fun k => ι (v k))).2 = 0 := fun v => by
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, LinearMap.mem_ker, LinearMap.snd_apply,
      pull_snd_eq_zero]
  have memU' : ∀ v : Fin a → Qbar l, v ∈ (LinearMap.ker (LinearMap.fst (Qbar l) (Fin n → Qbar l) (Fin m → Qbar l))).map
      ((pull ι f).symm : (Fin n → Qbar l) × (Fin m → Qbar l) →ₗ[Qbar l] (Fin a → Qbar l)) ↔ (f (fun k => ι (v k))).1 = 0 := fun v => by
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, LinearMap.mem_ker, LinearMap.fst_apply,
      pull_fst_eq_zero]
  refine ⟨_, _, hC', ?_, ?_, fun σ hσ => ⟨fun v hv => ?_, fun v hv => ?_⟩, ?_⟩
  · rw [WD.lpDim_mk, Module.finrank_fin_fun, LinearEquiv.finrank_map_eq, ← LinearMap.range_inl,
      LinearMap.finrank_range_of_inj LinearMap.inl_injective, Module.finrank_fin_fun]
  · rw [WD.lpDim_mk, Module.finrank_fin_fun, LinearEquiv.finrank_map_eq, ← LinearMap.range_inr,
      LinearMap.finrank_range_of_inj LinearMap.inr_injective, Module.finrank_fin_fun]
  · rw [memU] at hv ⊢
    rw [← toEndC_coord, hin σ hσ]
    exact stρ2 _ _ (ste2 _ _ hv)
  · rw [memU'] at hv ⊢
    rw [← toEndC_coord, hin σ hσ]
    exact stρ1 _ _ (ste1 _ _ hv)
  · intro hm σ hσ c0 hc v hv
    rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at hm
    rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.lpDim_mk] at hc
    have hsc := eq_algebraMap_of_charpoly (c.semisimple _) hc
    rw [memU'] at hv
    set u : Fin a → ℂ := fun k => ι (v k) with hu
    have hNu : z.N u = 0 := by
      rw [← f.map_eq_zero_iff, hfN]
      ext j <;> simp [hv, hm]
    suffices H : (fun i => ι ((((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).mulVec v) i)) =
        fun i => ι ((c0 • v) i) by
      funext i; exact ι.injective (congrFun H i)
    have hcu : (fun i => ι ((c0 • v) i)) = ι c0 • u := by funext i; simp [hu]
    rw [← toEndC_coord, hin σ hσ, exp_apply_of_eq_zero ι (hN.1.smul _)
      (by rw [toEndC_smul, LinearMap.smul_apply, ← hz.1, hNu, smul_zero]), hcu]
    apply f.injective
    rw [hfρ, map_smul]
    refine Prod.ext ?_ ?_
    · rw [WDRep.sum_ρ, LinearMap.prodMap_apply, Prod.smul_fst, hv, map_zero, smul_zero]
    · rw [WDRep.sum_ρ, LinearMap.prodMap_apply, Prod.smul_snd, hsc, Module.algebraMap_end_apply]

end GlobalTheory.WeilDeligne.InertiaSplit

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.WeilDeligne.InertiaSplit.decomp_away : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ i : D.nd.Loc, (∀ a (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → ∀ p q : D.naut.LP w, D.naut.wdOf i ρ w = D.naut.lpSum p q → ∃ U U' : Submodule (Qbar (D.nd.l i)) (Fin a → Qbar (D.nd.l i)), IsCompl U U' ∧ Module.finrank (Qbar (D.nd.l i)) U = D.naut.lpDim p ∧ Module.finrank (Qbar (D.nd.l i)) U' = D.naut.lpDim q ∧ (∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), (∀ v ∈ U, ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))).mulVec v ∈ U) ∧ (∀ v ∈ U', ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))).mulVec v ∈ U')) ∧ (D.naut.mono0 q → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), ∀ c : Qbar (D.nd.l i), D.naut.inePol q σ = (X - C (D.naut.iotaQC i c)) ^ D.naut.lpDim q → ∀ v ∈ U', ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))).mulVec v = c • v)) := by
  intro _ hL D P i a ρ hρ w hw p q hpq
  have hw' : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hw
  have e1 := congrArg (P.T.e w) hpq
  rw [(P.wdOf i a ρ w).1, P.wd.away _ _ ρ w hw', P.T.sum] at e1
  obtain ⟨U, U', hC, h1, h2, h3, h4⟩ :=
    GlobalTheory.WeilDeligne.InertiaSplit.split_away hw' (D.naut.iotaQC i) ρ hρ _ _ e1
  refine ⟨U, U', hC, by rw [h1, P.T.dim], by rw [h2, P.T.dim], h3,
    fun hm σ hσ c hc => h4 ((P.T.mono0 w q).1 hm) σ hσ c ?_⟩
  rw [← P.T.inePol w q σ hσ, hc, P.T.dim]
