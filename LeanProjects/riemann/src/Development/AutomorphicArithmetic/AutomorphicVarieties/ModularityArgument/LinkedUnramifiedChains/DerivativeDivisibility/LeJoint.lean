import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CmpPrime
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.BaseChange

open Polynomial TensorProduct

namespace UpperTheory.V.J

section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

private lemma ev_uniq (f : Module.End K V) {μ ν : K} {v : V} (hv : v ≠ 0)
    (h1 : v ∈ f.maxGenEigenspace μ) (h2 : v ∈ f.maxGenEigenspace ν) : μ = ν := by
  by_contra hne
  have hd := Module.End.disjoint_genEigenspace f hne ⊤ ⊤
  exact hv ((Submodule.disjoint_def.1 hd) v h1 h2)

private theorem ev_add_lemma {X Y : Module.End K V} (hc : Commute X Y) {v : V} {k l : ℕ}
    (hk : (X ^ k) v = 0) (hl : (Y ^ l) v = 0) : ((X + Y) ^ (k + l)) v = 0 := by
  rw [hc.add_pow, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro m _
  have hXY : (X ^ m * Y ^ (k + l - m)) v = 0 := by
    by_cases hmk : k ≤ m
    · rw [(hc.pow_pow m (k + l - m)).eq, Module.End.mul_apply, ← pow_sub_mul_pow X hmk,
        Module.End.mul_apply, hk, map_zero, map_zero]
    · rw [show k + l - m = (k + l - m - l) + l by omega, pow_add, Module.End.mul_apply,
        Module.End.mul_apply, hl, map_zero, map_zero]
  rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, hXY, smul_zero]

private lemma ev_add {f g : Module.End K V} (h : Commute f g) {μ ν : K} {v : V}
    (h1 : v ∈ f.maxGenEigenspace μ) (h2 : v ∈ g.maxGenEigenspace ν) :
    v ∈ (f + g).maxGenEigenspace (μ + ν) := by
  rw [Module.End.mem_maxGenEigenspace] at h1 h2 ⊢
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  have hs1 : ∀ (c : K) (T : Module.End K V), Commute (c • (1 : Module.End K V)) T := fun c T => by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact Algebra.commute_algebraMap_left c T
  have hc : Commute (f - μ • 1) (g - ν • 1) := (h.sub_right (hs1 ν f).symm).sub_left (hs1 μ _)
  refine ⟨k + l, ?_⟩
  have hsplit : f + g - (μ + ν) • (1 : Module.End K V) = (f - μ • 1) + (g - ν • 1) := by
    rw [add_smul]
    abel
  rw [hsplit]
  exact ev_add_lemma hc hk hl

private lemma ev_mul {f g : Module.End K V} (h : Commute f g) {μ ν : K} {v : V}
    (h1 : v ∈ f.maxGenEigenspace μ) (h2 : v ∈ g.maxGenEigenspace ν) :
    v ∈ (f * g).maxGenEigenspace (μ * ν) := by
  rw [Module.End.mem_maxGenEigenspace] at h1 h2 ⊢
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  have hs1 : ∀ (c : K) (T : Module.End K V), Commute (c • (1 : Module.End K V)) T := fun c T => by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact Algebra.commute_algebraMap_left c T
  have hag : Commute (f - μ • 1) g := h.sub_left (hs1 μ g)
  have hab : Commute (f - μ • 1) (g - ν • 1) := (h.sub_right (hs1 ν f).symm).sub_left (hs1 μ _)
  have hgb : Commute g (g - ν • 1) := (Commute.refl g).sub_right (hs1 ν g).symm
  have hc : Commute ((f - μ • 1) * g) (μ • (g - ν • 1)) := (hab.mul_left hgb).smul_right μ
  have hsplit : f * g - (μ * ν) • (1 : Module.End K V) = (f - μ • 1) * g + μ • (g - ν • 1) := by
    simp only [sub_mul, smul_sub, smul_mul_assoc, one_mul, smul_smul]
    abel
  refine ⟨k + l, ?_⟩
  rw [hsplit]
  refine ev_add_lemma hc ?_ ?_
  · rw [hag.mul_pow, (hag.pow_pow k k).eq, Module.End.mul_apply, hk, map_zero]
  · rw [_root_.smul_pow, LinearMap.smul_apply, hl, smul_zero]

private lemma ev_scal (c : K) (v : V) : v ∈ (c • (1 : Module.End K V)).maxGenEigenspace c :=
  (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by simp⟩

private lemma le_joint {ι : Type} [FiniteDimensional K V] [IsAlgClosed K] (f : ι → Module.End K V)
    (hc : ∀ i j, Commute (f i) (f j)) (x : ι → K) (t : ι)
    (h : ∀ (χ : ι → K) (v : V), v ≠ 0 → (∀ i, v ∈ (f i).maxGenEigenspace (χ i)) → χ t = x t → χ = x) :
    (f t).maxGenEigenspace (x t) ≤ ⨅ i, (f i).maxGenEigenspace (x i) := by
  classical
  have hmap : ∀ j, Set.MapsTo (f j) ((f t).maxGenEigenspace (x t)) ((f t).maxGenEigenspace (x t)) :=
    fun j => Module.End.mapsTo_maxGenEigenspace_of_comm (hc t j) (x t)
  have lift : ∀ (j : ι) (μ : K) (w : (f t).maxGenEigenspace (x t)),
      w ∈ Module.End.maxGenEigenspace ((f j).restrict (hmap j)) μ → (w : V) ∈ (f j).maxGenEigenspace μ := by
    intro j μ w hw
    have e := Module.End.genEigenspace_restrict (f j) ((f t).maxGenEigenspace (x t)) ⊤ μ (hmap j)
    have hw' : w ∈ Submodule.comap ((f t).maxGenEigenspace (x t)).subtype (((f j).genEigenspace μ) ⊤) := e ▸ hw
    exact hw'
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo
    (fun j => (f j).restrict (hmap j))
    (fun i j φ => Module.End.mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo (f i) (f j) (hmap i) (hmap j)
      (Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ))
    (fun i => Module.End.iSup_maxGenEigenspace_eq_top _)
  have hbot : ∀ χ : ι → K, χ ≠ x →
      ⨅ j, Module.End.maxGenEigenspace ((f j).restrict (hmap j)) (χ j) = ⊥ := by
    intro χ hχ
    by_contra hne
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hne
    rw [Submodule.mem_iInf] at hw
    have hv0 : (w : V) ≠ 0 := fun h0 => hw0 (Subtype.ext h0)
    have hall : ∀ j, (w : V) ∈ (f j).maxGenEigenspace (χ j) := fun j => lift j (χ j) w (hw j)
    have hχt : χ t = x t := ev_uniq (f t) hv0 (hall t) w.2
    exact hχ (h χ w hv0 hall hχt)
  have heq : ⨅ j, Module.End.maxGenEigenspace ((f j).restrict (hmap j)) (x j) = ⊤ := by
    rw [eq_top_iff, ← htop]
    apply iSup_le
    intro χ
    by_cases hχ : χ = x
    · rw [hχ]
    · rw [hbot χ hχ]
      exact bot_le
  intro v hv
  rw [Submodule.mem_iInf]
  intro j
  have hw : (⟨v, hv⟩ : (f t).maxGenEigenspace (x t)) ∈
      ⨅ j, Module.End.maxGenEigenspace ((f j).restrict (hmap j)) (x j) := by
    rw [heq]
    exact Submodule.mem_top
  rw [Submodule.mem_iInf] at hw
  exact lift j (x j) ⟨v, hv⟩ (hw j)

end

end UpperTheory.V.J

theorem UpperTheory.V.J.muGe :
    UpperTheory.V.J.MuGe := by
  intro O Λ B K _ _ _ _ _ _ _ _ _ lam J M _ _ _ _ _ h x t hsep
  letI : Algebra Λ K := (x.comp lam).toAlgebra
  have actAdd : ∀ a b : B, actL lam M h.hs (a + b) = actL lam M h.hs a + actL lam M h.hs b :=
    fun a b => LinearMap.ext fun m => add_smul a b m
  have actMul : ∀ a b : B, actL lam M h.hs (a * b) = actL lam M h.hs a * actL lam M h.hs b :=
    fun a b => LinearMap.ext fun m => mul_smul a b m
  have Jrad : J ≤ (Module.annihilator B M).radical := by
    intro y hy
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro p ⟨hap, hp⟩
    exact ((h.supp p hp).1 hap) hy
  let F : B → Module.End K (K ⊗[Λ] M) := fun a => LinearMap.baseChange K (actL lam M h.hs a)
  have Fadd : ∀ a b, F (a + b) = F a + F b := fun a b => by
    simp only [F, actAdd, LinearMap.baseChange_add]
  have Fmul : ∀ a b, F (a * b) = F a * F b := fun a b => by
    simp only [F, actMul, LinearMap.baseChange_mul]
  have Fcomm : ∀ a b, Commute (F a) (F b) := fun a b => by
    show F a * F b = F b * F a
    rw [← Fmul, ← Fmul, mul_comm]
  have Flam : ∀ l : Λ, F (lam l) = (x (lam l)) • (1 : Module.End K (K ⊗[Λ] M)) := fun l => by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k m =>
      show k ⊗ₜ[Λ] (lam l • m) = x (lam l) • (k ⊗ₜ[Λ] m)
      rw [← h.hs, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
      rfl
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  have Fann : ∀ a ∈ Module.annihilator B M, F a = 0 := fun a ha => by
    have h0 : actL lam M h.hs a = 0 := LinearMap.ext fun m => (Module.mem_annihilator.1 ha) m
    simp only [F, h0, LinearMap.baseChange_zero]
  have key : rootMultiplicity (x t) (Polynomial.map (↑(x.comp lam) : Λ →+* K)
      (LinearMap.charpoly (actL lam M h.hs t))) = Module.finrank K ((F t).maxGenEigenspace (x t)) := by
    rw [LinearMap.finrank_maxGenEigenspace_eq, LinearMap.charpoly_baseChange]
    rfl
  refine (le_of_eq key).trans ?_
  show _ ≤ Module.finrank K ↥(⨅ a, (F a).maxGenEigenspace (x a))
  apply Submodule.finrank_mono
  refine le_joint F (fun a b => Fcomm a b) x t ?_
  intro χ v hv hall hχt
  have uniq : ∀ a μ, v ∈ (F a).maxGenEigenspace μ → μ = χ a := fun a μ hμ => ev_uniq (F a) hv hμ (hall a)
  have χlam : ∀ l, χ (lam l) = x (lam l) := fun l => (uniq _ _ (by rw [Flam]; exact ev_scal _ v)).symm
  let x' : B →ₐ[O] K :=
    { toFun := χ
      map_one' := by
        have e := χlam 1
        rwa [map_one, map_one] at e
      map_mul' := fun a b =>
        (uniq (a * b) (χ a * χ b) (by rw [Fmul]; exact ev_mul (Fcomm a b) (hall a) (hall b))).symm
      map_zero' := by
        have e := χlam 0
        rwa [map_zero, map_zero] at e
      map_add' := fun a b =>
        (uniq (a + b) (χ a + χ b) (by rw [Fadd]; exact ev_add (Fcomm a b) (hall a) (hall b))).symm
      commutes' := fun c => by
        show χ (algebraMap O B c) = algebraMap O K c
        rw [← lam.commutes c, χlam, lam.commutes c, x.commutes c] }
  have hJ : J ≤ RingHom.ker x' := by
    intro j hj
    rw [RingHom.mem_ker]
    obtain ⟨n, hn⟩ := Jrad hj
    have h0 : χ (j ^ n) = 0 := by
      refine (uniq (j ^ n) 0 ?_).symm
      rw [Fann _ hn]
      have e := ev_scal (0 : K) v
      rwa [zero_smul] at e
    have h1 : x' (j ^ n) = 0 := h0
    rw [map_pow] at h1
    exact (pow_eq_zero_iff'.mp h1).1
  have hx := hsep x' hJ (AlgHom.ext fun l => χlam l) hχt
  funext a
  exact DFunLike.congr_fun hx a
