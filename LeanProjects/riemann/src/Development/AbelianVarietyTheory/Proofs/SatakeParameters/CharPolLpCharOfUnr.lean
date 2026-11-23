import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq

noncomputable section

namespace GlobalTheory.SplitRead.BlockParam

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
open GlobalTheory.WeilDeligne (WD Weil ineIncl)

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem charpoly_smul_one {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (c : ℂ) :
    (c • (1 : Module.End ℂ V)).charpoly = (X - C c) ^ Module.finrank ℂ V := by
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, LinearMap.toMatrix_one,
    Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  simp

theorem charPol_lpChar_of_unr (a χ : WD h) (ha : a.unr) (σ : Ine (F := E) B) (c : ℂ)
    (hc : χ.charPol (ineIncl h σ) = X - C c) :
    (a.lpChar χ).charPol (ineIncl h σ) = (X - C c) ^ a.lpDim := by
  have hd : χ.lpDim = 1 := by rw [← WD.charPol_natDegree χ (ineIncl h σ), hc, natDegree_X_sub_C]
  induction a using WD.ind with
  | hP n a =>
  induction χ using WD.ind with
  | hP m b =>
    rw [WD.unr_mk] at ha
    rw [WD.lpDim_mk] at hd
    rw [WD.charPol_mk] at hc
    have h3 := LinearMap.aeval_self_charpoly (b.ρ (ineIncl h σ))
    rw [hc, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h3
    rw [WD.lpChar_mk, WD.charPol_mk, WD.lpDim_mk, GlobalTheory.WeilDeligne.WDRep.tensor_ρ, ha.2, h3,
      TensorProduct.map_smul_right, TensorProduct.map_one, charpoly_smul_one, Module.finrank_tensorProduct, hd,
      mul_one]

theorem irreducible_twist {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ Γ V}
    (hρ : ρ.IsIrreducible) (χ : Γ →* ℂˣ) : (twist ρ χ).IsIrreducible :=
  OrderIso.isSimpleOrder_iff (α := Subrepresentation (twist ρ χ)) (β := Subrepresentation ρ)
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
        simpa [smul_smul] using this⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl } |>.2 hρ

def detIrr (n : ℕ) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Irr k n where
  V := ℂ
  π := detRep (Fin n) χ
  smooth := (isSmooth_ofChar_iff _).2 hχ.detChar
  irr := isIrreducible_ofChar _

def twistIrr {n : ℕ} (π : Irr k n) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Irr k n where
  V := π.V
  π := twist π.π (detChar (Fin n) χ)
  smooth := isSmooth_twist π.smooth hχ.detChar
  irr := irreducible_twist π.irr _

theorem charPol_unr_twist {rc : ∀ n, Irr k n → WD h} (hrc : RecLaws rc) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ)
    (σ : Ine (F := E) B) (c : ℂ) (hc : (rc 1 (detIrr 1 χ hχ)).charPol (ineIncl h σ) = X - C c)
    (n : ℕ) (π : Irr k n) (hn : n = 1) (α : ℂˣ)
    (e : Nonempty (π.π.Equiv (detRep (Fin n) (χ * unrChar k α)))) :
    (rc n π).charPol (ineIncl h σ) = X - C c := by
  subst hn
  let u : Irr k 1 := detIrr 1 (unrChar k α) (isSmoothChar_of_isUnram (isUnram_unrChar k α))
  have he : detRep (Fin 1) (χ * unrChar k α) = twist u.π (detChar (Fin 1) χ) := by
    show _ = twist (detRep (Fin 1) (unrChar k α)) (detChar (Fin 1) χ)
    unfold detRep ofChar
    rw [twist_twist]
    rfl
  have h1 := hrc.twist 1 χ (detIrr 1 χ hχ) u π ⟨.refl _⟩ (he ▸ e)
  rw [h1, charPol_lpChar_of_unr _ _ ((hrc.sph 1 u).2 (isSpherical_detRep (isUnram_unrChar k α))) σ c hc,
    hrc.dim, pow_one]

theorem split_local {rc : ∀ n, Irr k n → WD h} (hB : BlockSplit k) (hrc : RecLaws rc) (hs : RecSupp rc)
    {r t : ℕ} {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (ht : IsTame χ) (π : Irr k (r + t)) (v : π.V) (hv : v ≠ 0)
    (hvb : IsBlockVec χ π.π v) (c : Ine (F := E) B → ℂ)
    (hc : ∀ σ, (rc 1 (detIrr 1 χ hχ)).charPol (ineIncl h σ) = X - C (c σ)) (γ : Ine (F := E) B)
    (hm : ((rc _ π).charPol (ineIncl h γ)).rootMultiplicity (c γ) ≤ t) :
    ∃ a b : WD h, rc _ π = a.lpSum b ∧ a.lpDim = r ∧ b.lpDim = t ∧ b.mono0 ∧
      ∀ σ, b.charPol (ineIncl h σ) = (X - C (c σ)) ^ t := by
  classical
  rcases hB r t χ π v hχ ht hv hvb with ⟨π₁, π₂, hsph, e⟩ | ⟨s, d, σ, hsupp, hcard⟩
  · have h1 := hrc.twist t χ (detIrr 1 χ hχ) π₂ (twistIrr π₂ χ hχ) ⟨.refl _⟩ ⟨.refl _⟩
    have hu := (hrc.sph t π₂).2 hsph
    refine ⟨rc r π₁, rc t (twistIrr π₂ χ hχ), hrc.prod r t π₁ _ π e, hrc.dim _ _, hrc.dim _ _, ?_, fun σ => ?_⟩
    · rw [h1, WD.monomial_char_iff _ _ (hrc.dim _ _)]
      exact WD.unr_mono0 _ hu
    · rw [h1, charPol_lpChar_of_unr _ _ hu σ _ (hc σ), hrc.dim]
  · exfalso
    set U := {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))} with hU
    have hdvd : (X - C (c γ)) ^ U.toFinset.card ∣ (rc _ π).charPol (ineIncl h γ) := by
      rw [hs _ s π d σ hsupp, ← Finset.prod_const]
      refine dvd_trans (dvd_of_eq (Finset.prod_congr rfl fun a ha => ?_))
        (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ U.toFinset))
      obtain ⟨h1, α, e⟩ := Set.mem_toFinset.1 ha
      exact (charPol_unr_twist hrc hχ γ _ (hc γ) _ _ h1 α e).symm
    have := (le_rootMultiplicity_iff (WD.charPol_monic _ _).ne_zero).2 hdvd
    rw [Set.ncard_eq_toFinset_card'] at hcard
    omega

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem split_param : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A) (S : Reading T) (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w), BlockSplitAll H.E → Laws S → SuppLaws S → TypeBlock S i w hw → (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))) → ∀ P : A.AV i, (A.inePol (A.locV i P w) (N.gam0 i w)).rootMultiplicity (iotaO N A i (chi1 N i (N.gam0 i w))) ≤ R.t → ∃ a b : A.LP w, A.locV i P w = A.lpSum a b ∧ A.lpDim a = R.r ∧ A.lpDim b = R.t ∧ A.mono0 b ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol b σ = (X - C (iotaO N A i (chi1 N i σ))) ^ R.t := by
  intro R H what₂ N A T S i w hw hB hL hS hT hchi P hm
  obtain ⟨v, hv, hvb⟩ := hT.2 P
  have hμ := (S i w hw).mu_ok.1
  rw [T.inePol w _ _ (N.locNd_chebotarevPlace_mem i w), (S i w hw).locV, WD.inePol_of_mem_Ine _ (N.locNd_chebotarevPlace_mem i w)] at hm
  obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := split_local (hB w) (hL i w hw) (hS i w hw) hμ hT.1 _ v hv hvb
    (fun σ => iotaO N A i (chi1 N i σ.1)) (fun σ => by
      rw [← hchi σ.1 σ.2, T.inePol w _ _ σ.2, (S i w hw).locMu (detIrr 1 _ hμ) ⟨.refl _⟩,
        WD.inePol_of_mem_Ine _ σ.2]) ⟨_, N.locNd_chebotarevPlace_mem i w⟩ hm
  obtain ⟨a, rfl⟩ := (T.e w).surjective a
  obtain ⟨b, rfl⟩ := (T.e w).surjective b
  refine ⟨a, b, (T.e w).injective ?_, ?_, ?_, (T.mono0 w b).2 h4, fun σ hσ => ?_⟩
  · rw [(S i w hw).locV, h1, T.sum]
  · rw [← T.dim, h2]
  · rw [← T.dim, h3]
  · rw [T.inePol w _ _ hσ, WD.inePol_of_mem_Ine _ hσ, h5]

end GlobalTheory.SplitRead.BlockParam
