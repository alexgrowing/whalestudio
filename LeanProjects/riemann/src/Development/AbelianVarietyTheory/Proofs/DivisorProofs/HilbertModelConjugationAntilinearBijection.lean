import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRepresentativeSobolevBoundStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntilinear

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjHilb

theorem nonempty_antilinear {H H' Y : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']
    (ev : H → Y → ℂ) (ev' : H' → Y → ℂ)
    (ha : ∀ a b g, ev (a + b) g = ev a g + ev b g) (hs : ∀ (z : ℂ) a g, ev (z • a) g = z * ev a g)
    (ha' : ∀ a b g, ev' (a + b) g = ev' a g + ev' b g) (hs' : ∀ (z : ℂ) a g, ev' (z • a) g = z * ev' a g)
    (hinj : Function.Injective ev) (hinj' : Function.Injective ev')
    (hx : ∀ y, ∃ x, ∀ g, ev' x g = starRingEnd ℂ (ev y g)) (hy : ∀ x, ∃ y, ∀ g, ev y g = starRingEnd ℂ (ev' x g)) :
    Nonempty (H' ≃ₗ⋆[ℂ] H) := by
  choose x hx using hx
  choose y hy using hy
  exact ⟨{ toFun := y
           invFun := x
           map_add' := fun a b => hinj (funext fun g => by rw [ha, hy, hy, hy, ha', map_add])
           map_smul' := fun z a => hinj (funext fun g => by rw [hs, hy, hy, hs', map_mul])
           left_inv := fun a => hinj' (funext fun g => by rw [hx, hy, Complex.conj_conj])
           right_inv := fun a => hinj (funext fun g => by rw [hy, hx, Complex.conj_conj]) }⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_conj_value (R : RealDat D A Ks) (hm : R.models_HW) (i : Fin D.R.m) (σ σ' : D.what₂.LL →+* ℂ)
    (c : ∀ τ, (R.MW i σ).H τ ≃ₗᵢ⋆[ℂ] (R.MW i σ').H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ), ∀ w, c τ ((R.MW i σ).rep τ g w) = (R.MW i σ').rep τ g (c τ w))
    (v : (R.MW i σ).Vec) (v' : (R.MW i σ').Vec) (hv : ∀ τ, (v' τ : (R.MW i σ').H τ) = c τ (v τ)) (y : (R.HW i σ').H) :
    ∃ x : (R.HW i σ).H, ∀ g, evAt R i σ v x g = starRingEnd ℂ (evAt R i σ' v' y g) := by
  obtain ⟨-, hmul⟩ := GlobalTheory.ConjMult.conj_mult R.θ (R.MW i σ') (R.MW i σ) c hc
  have hχ : (fun k => star (levChi _ (R.βW i) (R.datWp i R.triv) k)) = levChi _ (R.βW i) (R.datWp i R.triv) := by
    funext k
    rw [GlobalTheory.ConjEval.levChi_principal, star_one]
  have h1 : (R.HW i σ').e y ∈ R.Wall i σ' := (hm i _).2.1 ▸ LinearMap.mem_range_self _ y
  obtain ⟨T', hT', h2⟩ := hmul _ _ _ h1
  rw [hχ] at hT'
  obtain ⟨x, rfl⟩ : T' ∈ LinearMap.range (R.HW i σ).e := (hm i σ).2.1.symm ▸ hT'
  exact ⟨x, h2 v _ hv⟩

theorem evAt_inj (R : RealDat D A Ks) (hm : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec)
    (hv : IsUnitV v) : Function.Injective (evAt R i σ v) :=
  GlobalTheory.EvalInj.evAt_injective_of_ne R hm i σ v fun τ h => by
    have := hv τ
    rw [h, norm_zero] at this
    exact zero_ne_one this

theorem conj_hilbert : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → (∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → Nonempty ((R.HW i σ).H ≃ₗ⋆[ℂ] (R.HW i ((starRingEnd ℂ).comp σ)).H)) ∧ (JEvExists T R κ v₀ → JEvBar T R κ) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hM ht
  have hm := hM.HW
  have hadd : ∀ i (σ' : D.what₂.LL →+* ℂ) (u : (R.MW i σ').Vec) a b g,
      evAt R i σ' u (a + b) g = evAt R i σ' u a g + evAt R i σ' u b g := fun i σ' u a b g => by
    simp [evAt]
  have hsmul : ∀ i (σ' : D.what₂.LL →+* ℂ) (u : (R.MW i σ').Vec) (z : ℂ) a g,
      evAt R i σ' u (z • a) g = z * evAt R i σ' u a g := fun i σ' u z a g => by
    simp [evAt]
  have key : ∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → ∃ v : (R.MW i σ).Vec, IsUnitV v ∧
      (∀ y, ∃ x, ∀ g, evAt R i σ v x g = starRingEnd ℂ (evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) y g)) ∧
      ∀ x, ∃ y, ∀ g, evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) y g = starRingEnd ℂ (evAt R i σ v x g) := by
    intro i σ hσ
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_antiunitary_intertwiner_conjugateEmbedding_models D G Pl0 T0 A T R κ v₀ hM ht i σ hσ
    obtain ⟨hsm, -⟩ := GlobalTheory.ConjMult.conj_mult R.θ (R.MW i ((starRingEnd ℂ).comp σ)) (R.MW i σ) c hc
    let v : (R.MW i σ).Vec := fun τ => ⟨(c τ).symm (v₀ i ((starRingEnd ℂ).comp σ) τ), (hsm τ _).2 (by
      rw [LinearIsometryEquiv.apply_symm_apply]; exact (v₀ i ((starRingEnd ℂ).comp σ) τ).2)⟩
    refine ⟨v, fun τ => ((c τ).symm.norm_map _).trans ((ht.hv₀ i _).norm R τ),
      exists_conj_value R hm i σ _ c hc v _ fun τ => ((c τ).apply_symm_apply _).symm,
      exists_conj_value R hm i _ σ (fun τ => (c τ).symm) (fun τ g hg w => (c τ).injective ?_) _ v fun τ => rfl⟩
    rw [hc τ g hg, (c τ).apply_symm_apply, (c τ).apply_symm_apply]
  refine ⟨fun i σ hσ => ?_, fun hJ i σ hσ hV => ?_⟩
  · obtain ⟨v, hv, hx, hy⟩ := key i σ hσ
    exact nonempty_antilinear _ _ (hadd _ _ _) (hsmul _ _ _) (hadd _ _ _) (hsmul _ _ _)
      (evAt_inj R hm i _ _ fun τ => (ht.hv₀ i _).norm R τ) (evAt_inj R hm i σ v hv) hx hy
  · obtain ⟨v, hv, hx, -⟩ := key i σ hσ
    exact ⟨v, hv, GlobalTheory.ConjEval.evEx_conj (res T σ) _ _ (hadd _ _ _) (hsmul _ _ _) (hadd _ _ _) (hsmul _ _ _)
      (evAt_inj R hm i σ v hv) hx _ (hJ i ((starRingEnd ℂ).comp σ) (good_resC T hσ) hV)⟩

end GlobalTheory.ConjHilb
