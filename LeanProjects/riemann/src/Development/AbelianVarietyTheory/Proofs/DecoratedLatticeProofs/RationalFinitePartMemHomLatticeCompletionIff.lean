import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.RatLat

open GlobalTheory.LatVac

variable {D : D7}

theorem eq_of_parts {m n : ℕ} {u u' : Formalism.IndefR.Datum.Mx D m n} (h1 : u.map (infPart D) = u'.map (infPart D))
    (h2 : u.map (finPart D) = u'.map (finPart D)) : u = u' := by
  ext i j
  rw [← sub_eq_zero]
  apply eq_zero_of_parts
  · rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j
  · rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h2 i) j

theorem finTens_mem_iff {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finTens 1 M ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      M ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
  refine ⟨fun h => ?_, finTens_mem_latO (one_mem_intAf _)⟩
  refine (GlobalTheory.T.rationalHermitianRankOneLattice_selfDual D S T ΛS ΛT hS hT (GlobalTheory.T.exists_dual_family_selfDual_hermitianSpace D S ΛS hS) _).2 fun ℓ hℓ => ?_
  have h1 := char_sympl_eq_one hψ hS hT h (finTens_mem_latO (one_mem_intAf _) hℓ)
  rw [symplO_finTens, one_mul, one_mul] at h1
  exact (char_rat hψ _).1 h1

theorem genMap_mulVec (S T : HSp D) (a : D.host.E) (s y : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    genMap S T a s t *ᵥ y = a • (∑ i, ∑ j, star (s i) * S.gram i j * y j) • t := by
  funext i
  simp only [genMap, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mem_latRat_iff_perO {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : IsSelfDualC S ΛS) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    M ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) ↔
      Matrix.toLin' M ∈ perO (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      refine Submodule.subset_span ⟨a, ha, Matrix.toLin' (genMap S T 1 s t), fun y hy => ?_, ?_⟩
      · obtain ⟨b, hb⟩ := (hS.2 y).1 hy s hs
        rw [Matrix.toLin'_apply, genMap_mulVec, one_smul, ← hb]
        exact ΛT.smul_mem b ht
      · refine LinearMap.ext fun y => ?_
        rw [LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, genMap_mulVec, genMap_mulVec, one_smul]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  · intro h
    obtain ⟨n, s, s', hs, hd⟩ := GlobalTheory.T.exists_dual_family_selfDual_hermitianSpace D S ΛS hS
    have key : ∀ z ∈ perO (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) ΛS ΛT,
        LinearMap.toMatrix' z ∈ latRat S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨r, hr, x, hx, rfl⟩ := hw
        have e : LinearMap.toMatrix' (r • x) = ∑ k, genMap S T r (s' k) (x (s k)) := by
          refine Matrix.ext fun i j => ?_
          have e1 : (Pi.single j 1 : Fin S.rank → D.host.E) = ∑ k, (∑ l, star (s' k l) * S.gram l j) • s k := by
            funext c
            rw [Finset.sum_apply, Pi.single_apply, ← hd c j]
            exact Finset.sum_congr rfl fun k _ => mul_comm (s k c) _
          have e2 : LinearMap.toMatrix' (r • x) i j = r * x (Pi.single j 1) i := by
            rw [LinearMap.toMatrix'_apply]
            first
              | rfl
              | (congr 3; funext c; simp [Pi.single_apply])
          rw [e2, e1, map_sum, Matrix.sum_apply, Finset.sum_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [LinearMap.map_smul]
          change r * ((∑ l, star (s' k l) * S.gram l j) * x (s k) i) = r * x (s k) i * ∑ l, star (s' k l) * S.gram l j
          ring
        refine e ▸ AddSubgroup.sum_mem _ fun k _ => ?_
        exact AddSubgroup.subset_closure ⟨r, hr, _, (hs k).2, _, hx _ (hs k).1, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul c x _ hx =>
        have e : LinearMap.toMatrix' (c • x) = (c : D.host.E) • LinearMap.toMatrix' x := by
          rw [← map_smul]; rfl
        rw [e]
        exact smul_mem_latRat c hx
    have := key _ h
    rwa [LinearMap.toMatrix'_toLin'] at this

theorem AA_eq (h : D.host.ccK = ⊤) : D.host.AA = D.host.AA0 := by
  rw [Host.AA, Host.ccE, h, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]

theorem finOf_mem_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) N N', (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → (v ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) ↔ toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T a b hS hT δ sc hP ΛS ΛT N N' h1 h2 hΛS hΛT γ v hv
  subst hS hT
  have e1 : N = ΛS := (SetLike.coe_injective h1).symm
  have e2 : N' = ΛT := (SetLike.coe_injective h2).symm
  have : v = finTens 1 γ :=
    eq_of_parts (hv.1.trans (Matrix.ext fun i j => (infPart_pair _ _).symm)) (hv.2.trans rfl)
  rw [← h1, ← h2, this, finTens_mem_iff hP.std hΛS hΛT, mem_latRat_iff_perO ΛT hΛS, AA_eq hP.cc, e1, e2]
  rfl

end GlobalTheory.AdForm.RatLat

end
