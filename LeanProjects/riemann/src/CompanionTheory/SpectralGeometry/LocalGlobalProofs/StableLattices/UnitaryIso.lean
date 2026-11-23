import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckUIso

open CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk dsigW)

section Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H H' : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup H'] [NormedSpace ℂ H']
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)} {σ' : Mat n → (H' →L[ℂ] H')}

theorem isSm_map (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x)) {v : H} (hv : IsSm G σ v) :
    IsSm G σ' (e v) :=
  (SmOn.clm hv (e.restrictScalars ℝ)).congr fun g hg => (he g hg v).symm

theorem ds_map (h : RepOn G σ) (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x)) {X : Mat n}
    (hX : ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v) : ds σ' X (e v) = e (ds σ X v) := by
  have h1 := (e.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hv.differentiableAt h hX).hasDerivAt
  have h2 : (fun t => σ' (ex X t) (e v)) = (e.restrictScalars ℝ) ∘ fun t => σ (ex X t) v := by
    ext t; exact (he _ (hX t) v).symm
  unfold ds
  rw [h2, h1.deriv]; rfl

theorem dsW_map (h : RepOn G σ) (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x))
    {v : H} (hv : IsSm G σ v) : ∀ {W : List (Mat n)}, LieW G W → dsW σ' W (e v) = e (dsW σ W v)
  | [], _ => rfl
  | X :: W, hW => by
    have hW' : LieW G W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    rw [dsW_cons, dsW_cons, dsW_map h e he hv hW',
      ds_map h e he (hW X List.mem_cons_self) (hv.dsW h hW')]

end Gen

variable {k r : ℕ}

def res (U U' : URep k r) (e : U.R.H →L[ℂ] U'.R.H) (he : ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) :
    U.R.smSub →ₗ[ℂ] U'.R.smSub :=
  (e : U.R.H →ₗ[ℂ] U'.R.H).restrict fun v hv => isSm_map (G := GG k r) e he (v := v) hv

theorem res_coe (U U' : URep k r) (e : U.R.H →L[ℂ] U'.R.H)
    (he : ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) (v : U.R.smSub) :
    (res U U' e he v : U'.R.H) = e v := rfl

theorem isHom_res (F : FRep k r) (U U' : URep k r) (e : U.R.H →L[ℂ] U'.R.H)
    (he : ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) (hn : ∀ x, ‖e x‖ = ‖x‖) :
    IsHom (F, U) (F, U') (dOp F.ι (res U U' e he)) where
  cont W hW := by
    refine ⟨1, [W], by simpa using hW, fun x => le_of_eq ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul, sn]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [dsigW_eq', dsigW_eq']
    change ‖dsW U'.R.σ W (e (x c : U.R.H))‖ = _
    rw [dsW_map U.repOn e he (v := (x c : U.R.H)) (x c).2 (fun X hX t => ex_mem_of_lie (hW X hX) t), hn]
  equiv g hg := by
    have h1 : res U U' e he ∘ₗ U.sig g = U'.sig g ∘ₗ res U U' e he := by
      ext v
      simp only [LinearMap.comp_apply, res_coe, URep.sig_coe _ hg, he g hg]
    refine LinearMap.ext fun x => funext fun c => ?_
    have h2 : ∀ d, res U U' e he (U.sig g (x d)) = U'.sig g (res U U' e he (x d)) :=
      fun d => LinearMap.congr_fun h1 (x d)
    simp [CompanionTheory.Zuck.act, mAct, dOp, h2]

theorem uIso : UIso := by
  rintro k r F U U' ⟨e, he⟩
  have he' : ∀ g ∈ GG k r, ∀ x, e.symm (U'.R.σ g x) = U.R.σ g (e.symm x) := fun g hg x => by
    apply e.injective
    rw [he g hg, e.apply_symm_apply, e.apply_symm_apply]
  refine ⟨dOp F.ι (res U U' (e.toContinuousLinearEquiv : U.R.H →L[ℂ] U'.R.H) he),
    dOp F.ι (res U' U (e.symm.toContinuousLinearEquiv : U'.R.H →L[ℂ] U.R.H) he'),
    isHom_res F U U' _ he e.norm_map, isHom_res F U' U _ he' e.symm.norm_map, ?_, ?_⟩
  · exact LinearMap.ext fun x => funext fun c => Subtype.ext (e.symm_apply_apply _)
  · exact LinearMap.ext fun x => funext fun c => Subtype.ext (e.apply_symm_apply _)

end GlobalTheory.CompanionTheory.ZuckUIso

end
