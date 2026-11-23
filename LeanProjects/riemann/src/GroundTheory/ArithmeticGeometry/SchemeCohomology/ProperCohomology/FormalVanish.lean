import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver reesCechModule

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] (F : X.Modules)

def transMap (n : ℕ) : (c : ℕ) → idealPow I F (n + c + 1) ⟶ idealPow I F (n + 1)
  | 0 => 𝟙 _
  | c + 1 => idealPowSucc I F (n + c + 1) ≫ transMap n c

lemma transMap_ι (n : ℕ) : ∀ c, transMap I F n c ≫ idealPowι I F (n + 1) = idealPowι I F (n + c + 1)
  | 0 => Category.id_comp _
  | c + 1 => by
    rw [transMap, Category.assoc, transMap_ι n c, idealPowSucc_ι]
    rfl

variable {F} [F.IsQuasicoherent] (hF : IsCoherent F)

lemma coeff_mem_pow_of_le (r : reesAlgebra I) {n i : ℕ} (h : n ≤ i) :
    (r : Polynomial A).coeff i ∈ I ^ n :=
  Ideal.pow_le_pow_right h ((mem_reesAlgebra_iff I _).1 r.2 i)

lemma transMap_reesDeg_smul {V : X.Opens} (hV : IsAffineOpen V) (n d : ℕ) (r : reesAlgebra I)
    (s : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) (hs : ∀ j, d < j → reesCoef I hF hV j s = 0) :
    (transMap I F n (d + 1)).app V (reesDeg I hF hV (n + (d + 1) + 1) (reesInr I V r • s)) =
      ∑ j : Fin (d + 1), (idealPowOfMem I F ((r : Polynomial A).coeff (n + (d + 1) + 1 - j))
        (coeff_mem_pow_of_le I r (by omega))).app V (reesCoef I hF hV j s) := by
  apply idealPowι_app_injective I (n + 1)
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, transMap_ι, idealPowι_reesDeg,
    reesCoef_reesInr_smul, map_sum]
  simp_rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, idealPowOfMem_ι]
  rw [← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k l => (r : Polynomial A).coeff l • reesCoef I hF hV k s)]
  rw [Fin.sum_univ_eq_sum_range (fun j => (smulHom F (algebraMap A Γ(X, ⊤)
    ((r : Polynomial A).coeff (n + (d + 1) + 1 - j)))).app V (reesCoef I hF hV j s)) (d + 1)]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    rw [hs k (by omega), map_zero]

variable {ι : Type u} (𝔘 : ι → X.Opens)
  (hU : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a))) [Finite ι] (p : ℕ)

set_option maxHeartbeats 4000000 in
include hF hU in

theorem exists_transMap_eq_zero [IsProper (X ↘ Spec (.of A))] (hUtop : iSup 𝔘 = ⊤) :
    ∃ c, ∀ n (y : cechH (modulesAb (idealPow I F (n + c + 1))).obj 𝔘 p),
      cechHMap 𝔘 (modulesAbMap (idealPowι I F (n + c + 1))).hom p y = 0 →
        cechHMap 𝔘 (modulesAbMap (transMap I F n c)).hom p y = 0 := by
  classical
  have := finite_reesCech I 𝔘 p hF hUtop hU
  have hnoeth : IsNoetherian (reesAlgebra I) (cechH (reesPre I F) 𝔘 p) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  obtain ⟨S, hS⟩ := hnoeth.noetherian (LinearMap.ker (reesΦ I hF 𝔘 hU p))
  choose σ hσ Nb hcls hNb using fun g => exists_cls_coef_eq_zero I hF 𝔘 hU p g
  obtain ⟨d, hd⟩ : ∃ d, d = S.sup Nb := ⟨_, rfl⟩
  refine ⟨d + 1, fun n y hy => ?_⟩
  have hκ : (reesIncFam I hF 𝔘 hU (n + (d + 1) + 1)).cechH p y ∈
      LinearMap.ker (reesΦ I hF 𝔘 hU p) := by
    rw [LinearMap.mem_ker]
    apply PolynomialModule.ext
    ext k
    rw [reesΦ_coeff, reesCoefFam_reesIncFam]
    split_ifs with h
    · subst h
      exact hy
    · rfl
  rw [← hS, Submodule.mem_span_finset] at hκ
  obtain ⟨f, -, hf⟩ := hκ
  have hy' : y = (reesDegFam I hF 𝔘 hU (n + (d + 1) + 1)).cechH p (∑ g ∈ S, f g • g) := by
    rw [hf, reesDegFam_reesIncFam]
  rw [hy', map_sum, map_sum]
  refine Finset.sum_eq_zero fun g hg => ?_
  have hgker : reesΦ I hF 𝔘 hU p g = 0 :=
    LinearMap.mem_ker.1 (hS ▸ Submodule.subset_span hg)
  have hgd : Nb g ≤ d := hd ▸ Finset.le_sup (f := Nb) hg
  have key : ∀ r : reesAlgebra I, cechHMap 𝔘 (modulesAbMap (transMap I F n (d + 1))).hom p
      ((reesDegFam I hF 𝔘 hU (n + (d + 1) + 1)).cechH p (r • g)) = 0 := by
    intro r
    rw [← hcls g]
    change cechHMap 𝔘 (modulesAbMap (transMap I F n (d + 1))).hom p
      ((reesDegFam I hF 𝔘 hU (n + (d + 1) + 1)).cechH p
        (cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p (cls (σ g) (hσ g)))) = 0
    rw [cechHMap_cls, CechFamily.cechH_cls, cechHMap_cls]
    have hterm : ∀ j : Fin (d + 1), cechHMap 𝔘 (modulesAbMap (idealPowOfMem I F (k := n + 1)
        ((r : Polynomial A).coeff (n + (d + 1) + 1 - j)) (coeff_mem_pow_of_le I r (by omega)))).hom p
        ((reesCoefFam I hF 𝔘 hU j).cechH p (cls (σ g) (hσ g))) = 0 := by
      intro j
      rw [hcls g, ← reesΦ_coeff, hgker, PolynomialModule.coeff_zero, Finsupp.zero_apply, map_zero]
    refine Eq.trans ?_ (Finset.sum_eq_zero (s := Finset.univ) fun j _ => hterm j)
    simp_rw [CechFamily.cechH_cls, cechHMap_cls]
    rw [← cls_sum]
    · refine cls_congr 𝔘 (funext fun t => ?_) _ _
      rw [Finset.sum_apply]
      exact transMap_reesDeg_smul I hF (isAffineOpen_inter 𝔘 hU t) n d r (σ g t)
        (fun j hj => hNb g j (by omega) t)
    · rw [map_sum]
      exact Finset.sum_eq_zero fun j _ => by
        rw [← push_d, ← CechFamily.cochain_d, hσ g, map_zero, map_zero]
  exact key (f g)

end

end GroundTheory.Arith.SchemeCoh
