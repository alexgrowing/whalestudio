import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermSecRestrictGlobalAlgebraMap
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HodgeCoh

section Alg
open GlobalTheory.CechDR

theorem mem_closure_smul_ιMulti_D (k B : Type) [CommRing k] [CommRing B] [Algebra k B] (z : DR k B) :
    z ∈ AddSubgroup.closure {w : DR k B | ∃ (q : ℕ) (c : B) (v : Fin q → B),
      w = c • ExteriorAlgebra.ιMulti B q (fun i => D k B (v i))} := by
  set A := AddSubgroup.closure {w : DR k B | ∃ (q : ℕ) (c : B) (v : Fin q → B),
      w = c • ExteriorAlgebra.ιMulti B q (fun i => D k B (v i))} with hA
  have hsmul : ∀ (b : B) (a : DR k B), a ∈ A → b • a ∈ A := by
    intro b a ha
    induction ha using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨q, c, v, rfl⟩ := hw
      exact AddSubgroup.subset_closure ⟨q, b * c, v, by rw [smul_smul]⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  have key : ∀ z : DR k B, ∀ a ∈ A, z * a ∈ A := by
    intro z
    induction z using indDR with
    | h b => intro a ha; rw [← Algebra.smul_def]; exact hsmul b a ha
    | hd b =>
      intro a ha
      induction ha using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨q, c, v, rfl⟩ := hw
        refine AddSubgroup.subset_closure ⟨q + 1, c, Fin.cons b v, ?_⟩
        rw [mul_smul_comm, ExteriorAlgebra.ιMulti_succ_apply]
        simp [Matrix.vecTail, Function.comp_def]
      | zero => rw [mul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
      | neg x _ hx => rw [mul_neg]; exact neg_mem hx
    | hm x y hx hy => intro a ha; rw [mul_assoc]; exact hx _ (hy a ha)
    | ha x y hx hy => intro a ha; rw [add_mul]; exact add_mem (hx a ha) (hy a ha)
  have h1 : (1 : DR k B) ∈ A :=
    AddSubgroup.subset_closure ⟨0, 1, Fin.elim0, by rw [ExteriorAlgebra.ιMulti_zero_apply, one_smul]⟩
  simpa using key z 1 h1

variable {R R' R'' B B' B'' : Type} [CommRing R] [CommRing B] [Algebra R B]
  [CommRing R'] [CommRing B'] [Algebra R' B'] [CommRing R''] [CommRing B''] [Algebra R'' B'']

theorem SemiHom.mDR_ιMulti_D {σ : R →+* R'} {α : B →+* B'} (h : SemiHom σ α) (q : ℕ) (v : Fin q → B) :
    h.mDR (ExteriorAlgebra.ιMulti B q fun i => D R B (v i)) =
      ExteriorAlgebra.ιMulti B' q fun i => D R' B' (α (v i)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  congr 1
  funext i
  simp only [Function.comp_apply]
  exact (SemiHom.mDR_ι h _).trans (congrArg ι1 (SemiHom.m1_D h _))

theorem SemiHom.mDR_mDR {σ : R →+* R'} {α : B →+* B'} {τ : R' →+* R''} {β : B' →+* B''}
    {ρ : R →+* R''} {γ : B →+* B''} (h : SemiHom σ α) (h' : SemiHom τ β) (h'' : SemiHom ρ γ)
    (e : ∀ b, β (α b) = γ b) (x : DR R B) : h'.mDR (h.mDR x) = h''.mDR x := by
  induction x using indDR with
  | h b => simp [e]
  | hd b => simp [e]
  | hm x y hx hy => simp only [map_mul, hx, hy]
  | ha x y hx hy => simp only [map_add, hx, hy]

theorem isDRMap_mDR {k K K' : Type} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
    [Algebra k B] {g : B →+* K} {γ : B →+* K'} (hg : SemiHom (RingHom.id k) g)
    (hγ : SemiHom (RingHom.id k) γ) {ψ : K →ₐ[k] K'} {φ : DR k K →ₗ[k] DR k K'}
    (hφ : IsDRMap k ψ φ) (e : ∀ b, ψ (g b) = γ b) (z : DR k B) : φ (hg.mDR z) = hγ.mDR z := by
  induction mem_closure_smul_ιMulti_D k B z using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨q, c, v, rfl⟩ := hw
    rw [SemiHom.mDR_smul, SemiHom.mDR_ιMulti_D, hφ q (g c) (fun i => g (v i)), SemiHom.mDR_smul,
      SemiHom.mDR_ιMulti_D]
    simp only [e]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add]
  | neg x _ hx => rw [map_neg, map_neg, hx, map_neg]

end Alg

theorem formGermI_res_mapOver : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (p : Z ⟶ Sp ℂ) (p' : Z' ⟶ Sp ℂ),
    letI := algΓ p; letI := algΓ p'
    ∀ [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Z'.functionField] (hinst : inst = ffAlg p)
      (hinst' : inst' = ffAlg p') (f : Z' ⟶ Z) (hf : f ≫ p = p') (ψ : Z.functionField →ₐ[ℂ] Z'.functionField)
      (φ : DR ℂ Z.functionField →ₗ[ℂ] DR ℂ Z'.functionField), IsDRMap ℂ ψ φ →
      (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Z' ∈ f ⁻¹ᵁ V) (g : Γ(Z, V)),
        ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) =
          (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') hV').hom (f.app V g)) →
      ∀ (j : ℕ) (V : Z.Opens) (V' : Z'.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
        (hη : genericPoint Z ∈ V) (hη' : genericPoint Z' ∈ V') (h : V' ≤ f ⁻¹ᵁ V)
        (y : sectionsOn (Omega p j) V),
        formGermI p' j hV' hη' hinst' (sectionsOn.res ℂ (Omega p' j) h
          (sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf j) V y)) =
          φ (formGermI p j hV hη hinst y) := by
  intro Z Z' _ _ p p' inst inst' hinst hinst' f hf ψ φ hφ hψ j V V' hV hV' hη hη' h y
  subst hinst hinst'
  letI := algΓ p; letI := algΓ p'
  set x := (toOmEquiv p j hV).symm (sectionsOn.toΓ _ _ y) with hx
  have hy : sectionsOn.toΓ _ _ y = toOm p j V x := by
    exact (LinearEquiv.apply_symm_apply (toOmEquiv p j hV) _).symm
  have hz : sectionsOn.toΓ _ _ (sectionsOn.res ℂ (Omega p' j) h
      (sectionsOn.mapOver (appTop_algebraMap hf) (omegaPull hf j) V y)) =
      toOm p' j V' (formRes p' h j (formPull hf V j x)) := by
    have h2 : (omegaPull hf j).app V (toOm p j V x) = toOm p' j (f ⁻¹ᵁ V) (formPull hf V j x) :=
      omegaPull_toOmega hf j V x
    rw [sectionsOn.toΓ_res, sectionsOn.toΓ_mapOver, hy, h2, res_toOm]
  letI := ffAlg p; letI := ffAlg p'
  rw [formGermI_ffAlg, formGermI_ffAlg]
  simp only [formGerm, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hz, ← toOmEquiv_apply p' j hV', LinearEquiv.symm_apply_apply, ← hx]
  have hγ : SemiHom (RingHom.id ℂ) ((germSec p' (h hη')).comp (appSec p p' f V)) :=
    fun r b ↦ (semiHom_appSec hf V).comp (semiHom_germSec p' (h hη')) r b
  rw [isDRMap_mDR (semiHom_germSec p hη) hγ hφ (fun b ↦ hψ V hη (h hη') b)]
  change (semiHom_germSec p' hη').mDR ((SemiHom.of_algHom (Sec.res p' h)).mDR
    ((semiHom_appSec hf V).mDR (x : DR ℂ (Sec p V)))) = _
  rw [SemiHom.mDR_mDR (semiHom_appSec hf V) (SemiHom.of_algHom (Sec.res p' h))
    ((semiHom_appSec hf V).comp (SemiHom.of_algHom (Sec.res p' h))) (fun _ ↦ rfl)]
  refine SemiHom.mDR_mDR _ (semiHom_germSec p' hη') hγ (fun b ↦ ?_) _
  change (Z'.presheaf.germ V' (genericPoint Z') hη').hom
      ((Z'.presheaf.map (homOfLE h).op).hom ((f.app V).hom b)) =
    (Z'.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Z') (h hη')).hom ((f.app V).hom b)
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]

end GlobalTheory.HodgeCoh
