import Mathlib
import Formalism.HermitianLattices.StatementLat
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic

noncomputable section

namespace Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem genusBasic_gmap_one (L : Submodule R V) : gmap (1 : V ≃ₗ[K] V) L = L := by
  ext x
  rw [isomAct_mem_gmap]
  first
  | rfl
  | simp
  | exact Iff.rfl

theorem genusBasic_gmap_mul (g₁ g₂ : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap (g₂ * g₁) L = gmap g₂ (gmap g₁ L) := by
  ext x
  simp only [isomAct_mem_gmap]
  rfl

theorem genusBasic_gmap_inv (g : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap g⁻¹ (gmap g L) = L := by
  first
  | exact isomAct_gmap_symm g L
  | (ext x; simp only [isomAct_mem_gmap]; simp)

theorem genusBasic_mem_one_mul (x : K) (hx : x ∈ (1 : Submodule R K)) (r : R) :
    algebraMap R K r * x ∈ (1 : Submodule R K) := by
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ r hx

theorem genusBasic_hsmul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (v w : V) :
    h v (r • w) = algebraMap R K r * h v w := by
  rw [← algebraMap_smul K r w, map_smul, smul_eq_mul]

theorem genusBasic_hsmul_left (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (v w : V) :
    h (r • v) w = algebraMap R K (locBasic_sigma hinj hstar r) * h v w := by
  rw [← algebraMap_smul K r v, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    locBasic_sigma_spec, starRingEnd_apply]

theorem genusBasic_sigma_mem (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (p : Ideal R) (s : R) (hs : s ∈ hcompl (K := K) p) :
    locBasic_sigma hinj hstar s ∈ hcompl (K := K) p := by
  unfold hcompl at hs ⊢
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨hx1, hx2⟩ := hx
    refine Submonoid.subset_closure (Set.mem_setOf.2 ⟨hx2 _ (locBasic_sigma_spec hinj hstar x), fun t ht => ?_⟩)
    have e : t = x := hinj (by rw [ht, locBasic_sigma_spec, star_star])
    rw [e]
    exact hx1
  | one => rw [map_one]; exact Submonoid.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Submonoid.mul_mem _ hx hy

theorem genusBasic_hS (p : Ideal R) (hp : p.IsMaximal) (s : R) (hs : s ∈ hcompl (K := K) p) :
    s ∉ p := by
  haveI := hp.isPrime
  exact locBasic_hcompl_not_mem p s hs

theorem genusBasic_lg {W : Type*} [AddCommGroup W] [Module R W] (L : Submodule R W) (x : W)
    (hx : ∀ p : Ideal R, p.IsMaximal → x ∈ loc (K := K) p L) : x ∈ L := locBasic_lg (fun p => hcompl (K := K) p) (fun p hp s hs => genusBasic_hS p hp s hs) L x hx

theorem genusBasic_common (S : Submonoid R) (s : Finset V) (f : V → K)
    (hf : ∀ v ∈ s, ∃ u ∈ S, algebraMap R K u * f v ∈ (1 : Submodule R K)) :
    ∃ u ∈ S, ∀ v ∈ s, algebraMap R K u * f v ∈ (1 : Submodule R K) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, S.one_mem, fun v hv => by simp at hv⟩
  | @insert a s ha ih =>
    obtain ⟨u, hu, hus⟩ := ih (fun v hv => hf v (Finset.mem_insert_of_mem hv))
    obtain ⟨w, hw, hwa⟩ := hf a (Finset.mem_insert_self a s)
    refine ⟨u * w, S.mul_mem hu hw, fun v hv => ?_⟩
    rcases Finset.mem_insert.1 hv with rfl | hv
    · rw [map_mul, mul_assoc]
      exact genusBasic_mem_one_mul _ hwa u
    · rw [map_mul, mul_comm (algebraMap R K u), mul_assoc]
      exact genusBasic_mem_one_mul _ (hus v hv) w

theorem genusBasic_loc_dual (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) (hL : L.FG) (z : V)
    (hz : ∀ v ∈ L, h v z ∈ loc (K := K) p (1 : Submodule R K)) :
    z ∈ loc (K := K) p (dual h L) := by
  obtain ⟨gens, rfl⟩ := hL
  have hgen : ∀ v ∈ gens, ∃ u ∈ hcompl (K := K) p,
      algebraMap R K u * h v z ∈ (1 : Submodule R K) := by
    intro v hv
    obtain ⟨s, hs, hsv⟩ := locBasic_mem_locS.1 (hz v (Submodule.subset_span hv))
    exact ⟨s, hs, by rw [← Algebra.smul_def]; exact hsv⟩
  obtain ⟨u, hu, hall⟩ := genusBasic_common (hcompl (K := K) p) gens (fun v => h v z) hgen
  refine locBasic_mem_locS.2 ⟨u, hu, ?_⟩
  rw [dualBasic_mem_dual]
  intro y hy
  rw [genusBasic_hsmul_right]
  induction hy using Submodule.span_induction with
  | mem x hx => exact hall x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply, mul_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [genusBasic_hsmul_left hinj hstar, mul_left_comm]
    exact genusBasic_mem_one_mul _ hx _

theorem genusBasic_symm (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V)
    (hLM : SameGenus h L M) : SameGenus h M L := by
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  exact ⟨g⁻¹, (isom h).inv_mem hg, by rw [← hgL, genusBasic_gmap_inv]⟩

theorem genusBasic_int (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) (hLM : SameGenus h L M)
    (hL : IsIntegralLat h L) : IsIntegralLat h M := by
  intro x hx y hy
  apply genusBasic_lg (K := K) (1 : Submodule R K) (h x y)
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  have hx' : x ∈ gmap g (loc (K := K) p L) := by
    rw [hgL]
    exact locBasic_le_locS _ _ hx
  have hy' : y ∈ gmap g (loc (K := K) p L) := by
    rw [hgL]
    exact locBasic_le_locS _ _ hy
  rw [isomAct_mem_gmap] at hx' hy'
  obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.1 hx'
  obtain ⟨t, ht, hty⟩ := locBasic_mem_locS.1 hy'
  have hiso : h (g.symm x) (g.symm y) = h x y := by
    have e := hg (g.symm x) (g.symm y)
    simpa using e.symm
  refine locBasic_mem_locS.2 ⟨locBasic_sigma hinj hstar s * t,
    Submonoid.mul_mem _ (genusBasic_sigma_mem hinj hstar p s hs) ht, ?_⟩
  have h1 := hL _ hsx _ hty
  rw [genusBasic_hsmul_left hinj hstar, genusBasic_hsmul_right, hiso] at h1
  rw [Algebra.smul_def, map_mul]
  convert h1 using 1
  ring

theorem genusBasic_dual_le (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) (hLfg : L.FG) (hLM : SameGenus h L M)
    (hL : IsUnimodular h L) : dual h M ≤ M := by
  intro z hz
  rw [dualBasic_mem_dual] at hz
  apply genusBasic_lg (K := K) M z
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  rw [← hgL, isomAct_mem_gmap]
  have hmem : g.symm z ∈ loc (K := K) p (dual h L) := by
    apply genusBasic_loc_dual hinj hstar h p L hLfg
    intro v hv
    have hgv : g v ∈ loc (K := K) p M := by
      rw [← hgL, isomAct_mem_gmap, LinearEquiv.symm_apply_apply]
      exact locBasic_le_locS _ _ hv
    obtain ⟨s, hs, hsv⟩ := locBasic_mem_locS.1 hgv
    have h1 := hz _ hsv
    rw [genusBasic_hsmul_left hinj hstar] at h1
    have hiso : h (g v) z = h v (g.symm z) := by
      have e := hg v (g.symm z)
      simpa using e
    refine locBasic_mem_locS.2 ⟨locBasic_sigma hinj hstar s,
      genusBasic_sigma_mem hinj hstar p s hs, ?_⟩
    rw [Algebra.smul_def, ← hiso]
    exact h1
  rwa [show dual h L = L from hL] at hmem

end SlopeTestRemainingChoices

theorem genusBasic : GenusBasic := by
  intro R K V _ _ _ _ _ _ _ _ _ _ h _ hstar
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hint_of : ∀ L : Submodule R V, IsUnimodular h L → IsIntegralLat h L := by
    intro L hL x hx y hy
    have hy' : y ∈ dual h L := by
      rw [show dual h L = L from hL]
      exact hy
    exact (dualBasic_mem_dual h L y).1 hy' x hx
  have hle_dual : ∀ L : Submodule R V, IsIntegralLat h L → L ≤ dual h L := by
    intro L hL y hy
    exact (dualBasic_mem_dual h L y).2 fun x hx => hL x hx y hy
  refine ⟨⟨fun L p hp => ⟨1, (isom h).one_mem, by rw [genusBasic_gmap_one]⟩,
    fun {L M} hLM => genusBasic_symm h L M hLM, fun {L M N} h1 h2 p hp => ?_⟩, ?_, ?_⟩
  · obtain ⟨g₁, hg₁, e₁⟩ := h1 p hp
    obtain ⟨g₂, hg₂, e₂⟩ := h2 p hp
    exact ⟨g₂ * g₁, (isom h).mul_mem hg₂ hg₁, by rw [genusBasic_gmap_mul, e₁, e₂]⟩
  · intro L g hg p hp
    refine ⟨g, hg, ?_⟩
    ext x
    simp only [loc, isomAct_mem_gmap, locBasic_mem_locS, isomAct_smul]
  · intro L M hL hM hLM
    have hML := genusBasic_symm h L M hLM
    refine ⟨⟨fun hU => ?_, fun hU => ?_⟩,
      ⟨genusBasic_int hinj hstar h L M hLM, genusBasic_int hinj hstar h M L hML⟩⟩
    · exact le_antisymm (genusBasic_dual_le hinj hstar h L M hL hLM hU)
        (hle_dual M (genusBasic_int hinj hstar h L M hLM (hint_of L hU)))
    · exact le_antisymm (genusBasic_dual_le hinj hstar h M L hM hML hU)
        (hle_dual L (genusBasic_int hinj hstar h M L hML (hint_of M hU)))

end Formalism.HermitianLatticesTheory
