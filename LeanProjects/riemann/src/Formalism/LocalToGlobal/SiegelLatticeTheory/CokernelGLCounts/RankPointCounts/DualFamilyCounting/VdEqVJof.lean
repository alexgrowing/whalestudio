import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CuspDecayShortRowColumn
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SupEqTopOfMemHcompl
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.StarAlgebraMap

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G1

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem vd_eq_vJof (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsMaximal)
    (b : Fin (finrank K (⊤ : Submodule K V)) → V) (a : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F)
    (hJ : Cnt.IsJordanIn h ⊤ L 𝔭 b a) : vd h L 𝔭 = Cnt.vJof 𝔭 a := by
  classical
  obtain ⟨P, hP, hPc⟩ := exists_over (K := K) 𝔭 h𝔭
  haveI := h𝔭.isPrime
  have e : Fin (finrank K (⊤ : Submodule K V)) ≃ Fin (finrank K V) := finCongr (finrank_top K V)
  have hmap : ∀ x : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap F K (x : F) := fun x => by
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]
  have hA0 : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hJ.2.2.2.2 i
  have horth : ∀ i j, i ≠ j → h (b (e.symm i)) (b (e.symm j)) = 0 :=
    fun i j hij => hJ.2.2.1 _ _ fun h' => hij (e.symm.injective h')
  have hrange : Set.range (fun j => b (e.symm j)) = Set.range b := e.symm.surjective.range_comp b

  have hgb : (U0.gram h fun j => b (e.symm j)).det =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (∏ i, a i)) := by
    rw [gram_det_orth horth]
    have hp : ∏ j, h (b (e.symm j)) (b (e.symm j)) = ∏ i, h (b i) (b i) :=
      Fintype.prod_equiv e.symm _ _ fun _ => rfl
    rw [hp, map_prod, map_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [hJ.2.2.2.1 i, hmap]
  have key : ∀ m : ℕ, discrIdeal h L ≤ extP K 𝔭 ^ m ↔ m ≤ vF 𝔭 (∏ i, a i) := by
    intro m
    constructor
    · intro hle
      have ht : ∀ i, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • b i ∈ L := fun i => by
        have hb : b i ∈ locF 𝔭 L := by
          rw [← hJ.2.1]
          exact LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩)
        exact (LocalSpans.mem_locF 𝔭 L (b i)).1 hb
      choose t ht1 ht2 using ht
      have ht0 : ∀ i, t i ≠ 0 := fun i h0 => ht1 i (h0 ▸ 𝔭.zero_mem)
      have hT0 : (∏ i, t i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ht0 i
      have hvT : vF 𝔭 (∏ i, t i) = 0 := by
        rw [vF_prod h𝔭 Finset.univ t ht0]
        exact Finset.sum_eq_zero fun i _ => vF_of_notMem h𝔭 (ht1 i)
      have hst : ∀ u : F, star (algebraMap F K u) = algebraMap F K u := fun u => (hF _).2 ⟨u, rfl⟩
      have hx : (U0.gram h fun j => algebraMap F K (t (e.symm j) : F) • b (e.symm j)).det =
          algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) ((∏ i, t i) * (∏ i, t i) * ∏ i, a i)) := by
        rw [gram_det_smul_orth horth]
        have hp1 : ∏ j, star (algebraMap F K (t (e.symm j) : F)) * algebraMap F K (t (e.symm j) : F) =
            ∏ i, algebraMap F K (t i : F) * algebraMap F K (t i : F) :=
          Fintype.prod_equiv e.symm _ _ fun j => by rw [hst]
        have hp2 : ∏ j, h (b (e.symm j)) (b (e.symm j)) = ∏ i, h (b i) (b i) :=
          Fintype.prod_equiv e.symm _ _ fun _ => rfl
        rw [hp1, hp2, map_mul, map_mul, map_mul, map_mul, map_prod, map_prod, map_prod, map_prod,
          Finset.prod_mul_distrib]
        simp only [hmap, hJ.2.2.2.1]
      have hxL : ∀ j, algebraMap F K (t (e.symm j) : F) • b (e.symm j) ∈ L := fun j => by
        rw [← hmap, algebraMap_smul]
        exact ht2 _
      have hmem : algebraMap (𝓞 F) (𝓞 K) ((∏ i, t i) * (∏ i, t i) * ∏ i, a i) ∈ discrIdeal h L :=
        Ideal.subset_span ⟨_, hxL, hx.symm⟩
      have h2 := hle hmem
      have h3 : (∏ i, t i) * (∏ i, t i) * ∏ i, a i ∈ 𝔭 ^ m := by
        rw [← MeanB.comap_extP_pow (K := K) 𝔭 m]
        exact h2
      rw [mem_pow_iff h𝔭 (mul_ne_zero (mul_ne_zero hT0 hT0) hA0), vF_mul h𝔭 (mul_ne_zero hT0 hT0) hA0,
        vF_mul h𝔭 hT0 hT0, hvT] at h3
      simpa using h3
    · intro hv
      unfold discrIdeal
      rw [Ideal.span_le]
      rintro z ⟨x, hxL, hz⟩
      have hx' : ∀ i, x i ∈ spanS (locRing P) fun j => b (e.symm j) := fun i => by
        have hxi : x i ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range fun j => b (e.symm j))) := by
          rw [hrange, hJ.2.1]
          exact LocF.le_locF 𝔭 L (hxL i)
        rw [← hPc] at hxi
        exact (mem_locF_span_iff hK hF hP _ (x i)).1 hxi
      obtain ⟨c, hc, hdet⟩ := gram_det_of_le (h := h) (isHermSemilocal_locRing hK hP) hx'
      obtain ⟨r, s, hs, hcr⟩ := (mem_locR_iff hP.isPrime c).1 hc
      have hsne := algebraMap_ne_zero_of_mem_hcompl hP.isPrime hs
      have hsz : s * z = r * algebraMap (𝓞 F) (𝓞 K) (∏ i, a i) := by
        apply IsFractionRing.injective (𝓞 K) K
        rw [map_mul, map_mul, hz]
        change _ * (U0.gram h x).det = _
        rw [hdet, hgb, hcr]
        field_simp
      have hAm : algebraMap (𝓞 F) (𝓞 K) (∏ i, a i) ∈ extP K 𝔭 ^ m := by
        rw [extP, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ ((mem_pow_iff h𝔭 hA0 m).2 hv)
      have hcop := OrthogonalBases.sup_eq_top_of_mem_hcompl hK hF hP hs
      rw [hPc] at hcop
      exact mem_pow_of_coprime hcop m (hsz ▸ Ideal.mul_mem_left _ r hAm)
  have hv : Cnt.vJof 𝔭 a = vF 𝔭 (∏ i, a i) := (vF_prod h𝔭 Finset.univ a hJ.2.2.2.2).symm
  rw [hv]
  unfold vd
  simp_rw [key]
  exact csSup_Iic

end Formalism.L2.SG.Pf.G1
