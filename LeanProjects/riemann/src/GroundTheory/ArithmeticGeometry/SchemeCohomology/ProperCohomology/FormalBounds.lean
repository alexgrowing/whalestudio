import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalCechSmul
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalAlgebra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver reesCechModule

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules} [F.IsQuasicoherent] (hF : IsCoherent F)
  {ι : Type u} (𝔘 : ι → X.Opens)
  (hU : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a))) [Finite ι] (p : ℕ)

def reesBound (x : cechH (reesPre I F) 𝔘 p) : ℕ :=
  Classical.choose (reesCoefFam_eq_zero_of_lt I hF 𝔘 hU p x)

lemma reesCoefFam_eq_zero_of_bound_lt (x : cechH (reesPre I F) 𝔘 p) {n : ℕ}
    (hn : reesBound I hF 𝔘 hU p x < n) : (reesCoefFam I hF 𝔘 hU n).cechH p x = 0 :=
  Classical.choose_spec (reesCoefFam_eq_zero_of_lt I hF 𝔘 hU p x) n hn

def reesCoefPoly (x : cechH (reesPre I F) 𝔘 p) :
    PolynomialModule A (cechH (modulesAb F).obj 𝔘 p) :=
  PolynomialModule.ofCoeff A (Finsupp.onFinset (Finset.range (reesBound I hF 𝔘 hU p x + 1))
    (fun n => (reesCoefFam I hF 𝔘 hU n).cechH p x) (fun n hn => by
      rw [Finset.mem_range]
      by_contra h
      exact hn (reesCoefFam_eq_zero_of_bound_lt I hF 𝔘 hU p x (by omega))))

lemma reesCoefPoly_coeff (x : cechH (reesPre I F) 𝔘 p) (n : ℕ) :
    (reesCoefPoly I hF 𝔘 hU p x).coeff n = (reesCoefFam I hF 𝔘 hU n).cechH p x :=
  rfl

def reesΦ : cechH (reesPre I F) 𝔘 p →ₗ[reesAlgebra I]
    PolynomialModule A (cechH (modulesAb F).obj 𝔘 p) where
  toFun := reesCoefPoly I hF 𝔘 hU p
  map_add' x y := by
    apply PolynomialModule.ext
    ext n
    simp only [reesCoefPoly_coeff, PolynomialModule.coeff_add, Finsupp.add_apply, map_add]
  map_smul' r x := by
    apply PolynomialModule.ext
    ext N
    rw [reesCoefPoly_coeff, RingHom.id_apply]
    change (reesCoefFam I hF 𝔘 hU N).cechH p (cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p x) =
      ((r : Polynomial A) • reesCoefPoly I hF 𝔘 hU p x).coeff N
    rw [reesCoefFam_reesMul, PolynomialModule.smul_apply]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [reesCoefPoly_coeff]

lemma reesΦ_coeff (x : cechH (reesPre I F) 𝔘 p) (n : ℕ) :
    (reesΦ I hF 𝔘 hU p x).coeff n = (reesCoefFam I hF 𝔘 hU n).cechH p x :=
  reesCoefPoly_coeff I hF 𝔘 hU p x n

def cechK (n : ℕ) : Submodule A (cechH (modulesAb F).obj 𝔘 p) :=
  LinearMap.range (cechH.linearMap 𝔘 A (idealPowι I F n) p)

omit [F.IsQuasicoherent] [Finite ι] in
lemma smul_cechK_le (n : ℕ) : I • cechK I 𝔘 p (F := F) n ≤ cechK I 𝔘 p (n + 1) := by
  refine Submodule.smul_le.2 fun a ha y hy => ?_
  obtain ⟨z, rfl⟩ := hy
  have ha1 : a ∈ I ^ 1 := by rwa [pow_one]
  refine ⟨cechH.linearMap 𝔘 A (idealPowMul I F a ha1) p z, ?_⟩
  have h := congrArg (fun f => f.hom) (show modulesAbMap (idealPowMul I F a ha1) ≫
      modulesAbMap (idealPowι I F (n + 1)) =
      modulesAbMap (idealPowι I F n) ≫ smulAbRingHom F (algebraMap A Γ(X, ⊤) a) by
    rw [← modulesAbMap_comp, idealPowMul_ι, modulesAbMap_comp]
    rfl)
  change cechHMap 𝔘 (modulesAbMap (idealPowι I F (n + 1))).hom p
      (cechHMap 𝔘 (modulesAbMap (idealPowMul I F a ha1)).hom p z) =
    cechHMap 𝔘 (smulAbRingHom F (algebraMap A Γ(X, ⊤) a)).hom p
      (cechHMap 𝔘 (modulesAbMap (idealPowι I F n)).hom p z)
  rw [← cechHMap_comp, ← cechHMap_comp]
  exact congrArg (fun f => cechHMap 𝔘 f p z) h

lemma range_reesΦ :
    LinearMap.range (reesΦ I hF 𝔘 hU p) = reesFiltration I (smul_cechK_le I 𝔘 p (F := F)) := by
  ext P
  constructor
  · rintro ⟨x, rfl⟩ n
    change (reesΦ I hF 𝔘 hU p x).coeff n ∈ cechK I 𝔘 p n
    rw [reesΦ_coeff, reesCoefFam_cechH]
    exact ⟨_, rfl⟩
  · intro hP
    choose y hy using fun n => (hP n : P.coeff n ∈ cechK I 𝔘 p n)
    refine ⟨∑ n ∈ P.coeff.support, (reesIncFam I hF 𝔘 hU n).cechH p (y n), ?_⟩
    apply PolynomialModule.ext
    ext k
    rw [reesΦ_coeff, map_sum]
    simp_rw [reesCoefFam_reesIncFam]
    rw [Finset.sum_ite_eq']
    split_ifs with hk
    · exact hy k
    · exact (Finsupp.notMem_support_iff.1 hk).symm

include hF hU in

theorem exists_cechK_eq_pow_smul [IsProper (X ↘ Spec (.of A))] (hUtop : iSup 𝔘 = ⊤) :
    ∃ c, ∀ n, cechK I 𝔘 p (F := F) (n + c) = I ^ n • cechK I 𝔘 p c := by
  refine exists_eq_pow_smul_of_fg I (smul_cechK_le I 𝔘 p) ?_
  rw [← range_reesΦ I hF 𝔘 hU p]
  have := finite_reesCech I 𝔘 p hF hUtop hU
  rw [LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

end

end GroundTheory.Arith.SchemeCoh
