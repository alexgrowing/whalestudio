import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlphaDiscriminantHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSplittingExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscEquiv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountExtP
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical

noncomputable section
namespace GlobalTheory.MaxLatExpo

theorem main : ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V], IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → ∀ P ∈ badP h M, ∀ (b : Fin (Module.finrank K (⊤ : Submodule K V)) → V) (a : Fin (Module.finrank K (⊤ : Submodule K V)) → 𝓞 F), IsJordanIn h ⊤ M (P.comap (algebraMap (𝓞 F) (𝓞 K))) b a → ∃ i, vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a i) = 1 ∧ ∀ j, j ≠ i → vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a j) = 0 := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd M hM P hPb b a hJ
  have hP : P.IsMaximal := hPb.1
  have hp : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hpp := hp.isPrime
  have hl : ∀ L : Submodule (𝓞 K) V, locF (P.comap (algebraMap (𝓞 F) (𝓞 K))) L = loc (K := K) P L :=
    fun L => locF_eq_loc hK hF hP L
  obtain ⟨-, -, -, hloc⟩ := GlobalTheory.MaxLatStruct.main K V h hK hs (UnimodularLocalization.nondegenerate hd) M hM
  obtain ⟨hconj, -, -, x, hxM, ⟨a0, ha0x, ha0P, ha0P2⟩, hstr⟩ := hloc P hPb
  have hext : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = P := ThirdPropositionSlot.map_comap_eq_of_inert hK hF hP hconj
  obtain ⟨hbX, hspan, horth, hdiag, ha⟩ := hJ
  have hL : IsLatIn (⊤ : Submodule K V) M := ⟨hM.1.1.fg, hM.1.1.span_eq_top⟩
  have hdI : dualIn h ⊤ M = dual h M := by
    ext z; simp [dualIn]
  set p := P.comap (algebraMap (𝓞 F) (𝓞 K)) with hpdef
  set S := HU.SP K p with hSdef
  have hB : ∀ z, z ∈ locF p M ↔ ∀ i, h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := fun z => by
    exact (Formalism.L2.SG.Pf.G2.mem_B_iff hbX hspan horth hdiag ha hpp hL z).trans ⟨fun h => h.2, fun h => ⟨Submodule.mem_top, h⟩⟩
  have hA : ∀ z, z ∈ locF p (dual h M) ↔ ∀ i, h (b i) z ∈ S := fun z => by
    rw [← hdI]; exact (Formalism.L2.SG.Pf.G2.mem_locF_dualIn_iff hbX hspan horth hdiag ha hF hp hL z).trans ⟨fun h => h.2, fun h => ⟨Submodule.mem_top, h⟩⟩
  have hR : ∀ c, c ∈ locR (K := K) P → c ∈ S := fun c hc => HU.mem_SP_iff_locF.2 (by rw [locF_eq_loc hK hF hP (1 : Submodule (𝓞 K) K)]; exact hc)

  obtain ⟨a0', ha0'⟩ : a0 ∈ Set.range (algebraMap (𝓞 F) (𝓞 K)) := by
    refine (conjO_eq_iff_mem_range hF a0).1 (RingOfIntegers.ext ?_)
    rw [conjO_coe]
    change star ((a0 : K)) = (a0 : K)
    rw [ha0x]; exact hs.eq x x
  have ha0ne : a0' ≠ 0 := by
    rintro rfl
    apply ha0P2
    rw [← ha0', map_zero]; exact Submodule.zero_mem _
  have hv0 : vF p a0' = 1 := by
    have h1 := localValuationFiltration.mem_pow_vF hp ha0ne
    have h2 := localValuationFiltration.notMem_pow_vF hp ha0ne
    have hin : a0' ∈ p := by rw [hpdef, Ideal.mem_comap, ha0']; exact ha0P
    rcases Nat.lt_or_ge (vF p a0') 2 with hlt | hge
    · interval_cases hv : vF p a0'
      · rw [zero_add, pow_one] at h2; exact absurd hin h2
      · rfl
    · exfalso
      apply ha0P2
      have := localizedQuotients.ι_mem_pow (K := K) (Ideal.pow_le_pow_right hge h1)
      rwa [hext, ha0'] at this
  have hd0 : h x x = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0') := by rw [ha0', ← ha0x]
  have hdne : h x x ≠ 0 := by rw [hd0]; exact Formalism.L2.SG.Pf.G2.jK_ι_ne_zero ha0ne
  have hα : ∀ i, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ≠ 0 := fun i => Formalism.L2.SG.Pf.G2.jK_ι_ne_zero (ha i)
  have hy : ∀ k i, h (b k) ((algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))⁻¹ • b i) = if k = i then 1 else 0 := by
    intro k i
    rw [LinearMap.map_smul, smul_eq_mul]
    split_ifs with hki
    · subst hki; rw [hdiag]; exact inv_mul_cancel₀ (hα k)
    · rw [horth k i hki, mul_zero]
  have hyA : ∀ i, (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)))⁻¹ • b i ∈ loc (K := K) P (dual h M) := by
    intro i
    rw [← hl, hA]
    intro k
    rw [hy]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  choose c hc hcM using fun i => hstr _ (hyA i)
  have hcS : ∀ i, c i ∈ S := fun i => hR _ (hc i)
  have hE : ∀ i k, ((if k = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b k) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a k)) ∈ S := by
    intro i k
    have h1 := hcM i
    rw [← hl] at h1
    have := (hB _).1 h1 k
    rwa [map_sub, hy, LinearMap.map_smul, smul_eq_mul] at this
  have hξ : ∀ k, h (b k) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a k)) ∈ S :=
    (hB x).1 (LocF.le_locF p M hxM)
  have hdS : h x x ∈ S := by rw [hd0]; exact HU.jK_mem_SP _

  have hle1 : ∀ i, vF p (a i) ≤ 1 := by
    intro i
    by_contra hgt
    push_neg at hgt
    have h1 : h x x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := by
      have e : h x x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) =
          h x x * (((if i = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b i) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) + c i * (h (b i) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
        rw [if_pos rfl]; field_simp; ring
      rw [e]
      exact S.add_mem (S.mul_mem hdS (hE i i)) (S.mul_mem (hcS i) (hξ i))
    have h1' : algebraMap (𝓞 K) K a0 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := by
      rw [show algebraMap (𝓞 K) K a0 = h x x from ha0x]; exact h1
    have h2 := (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha i) a0).1 h1'
    rw [hext] at h2
    exact ha0P2 (Ideal.pow_le_pow_right hgt h2)
  have huniq : ∀ i j, i ≠ j → vF p (a j) = 1 → 1 ≤ vF p (a i) → False := by
    intro i j hij hj hi
    have hci : c i / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ S := by
      have e : c i / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) = c i * (((if j = j then (1 : K) else 0) - c j * (h x x)⁻¹ * h (b j) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)))
          - c j * (((if j = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b j) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j))) := by
        rw [if_pos rfl, if_neg (fun e => hij e.symm)]; ring
      rw [e]
      exact S.sub_mem (S.mul_mem (hcS i) (hE j j)) (S.mul_mem (hcS j) (hE i j))
    obtain ⟨t, ht, w, hw⟩ := HU.mem_SP.1 (hcS i)
    have hw1 : algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ S := by
      rw [hw, mul_div_assoc]; exact S.mul_mem (HU.jK_mem_SP _) hci
    have hwP : w ∈ P := by
      have := (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha j) w).1 hw1
      rwa [hj, pow_one, hext] at this
    have hw2 : algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0') ∈ S :=
      (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp ha0ne w).2 (by rw [hv0, pow_one, hext]; exact hwP)
    have htne : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := Formalism.L2.SG.Pf.G2.jK_ι_ne_zero (Formalism.L2.SG.Pf.G2.ne_zero_of_notMem ht)
    have htinv : (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ ∈ S := HU.mem_SP.2 ⟨t, ht, 1, by rw [map_one, mul_inv_cancel₀ htne]⟩
    have hcd : c i * (h x x)⁻¹ ∈ S := by
      have e : c i * (h x x)⁻¹ = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ * (algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a0')) := by
        rw [hw, ← hd0]; field_simp
      rw [e]; exact S.mul_mem htinv hw2
    have h1 : algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := by
      have e : algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) = ((if i = i then (1 : K) else 0) - c i * (h x x)⁻¹ * h (b i) x) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))
          + (c i * (h x x)⁻¹) * (h (b i) x / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
        rw [if_pos rfl, map_one]; ring
      rw [e]; exact S.add_mem (hE i i) (S.mul_mem hcd (hξ i))
    have h2 := (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha i) 1).1 h1
    rw [hext] at h2
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (Ideal.pow_le_self (by omega) h2))
  have hex : ∃ i, vF p (a i) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hPb.2
    have hinv : ∀ i, algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) ∈ S := fun i =>
      (Formalism.L2.SG.Pf.G2.div_mem_SP_iff hp (ha i) 1).2 (by rw [hcon i, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)
    have heq : loc (K := K) P (dual h M) = loc (K := K) P M := by
      rw [← hl, ← hl]
      ext z
      rw [hA, hB]
      constructor
      · intro hz i
        have e : h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) = h (b i) z * (algebraMap (𝓞 K) K 1 / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
          rw [map_one]; ring
        rw [e]; exact S.mul_mem (hz i) (hinv i)
      · intro hz i
        have e : h (b i) z = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) * (h (b i) z / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i))) := by
          field_simp [hα i]
        rw [e]; exact S.mul_mem (HU.jK_mem_SP _) (hz i)
    obtain ⟨σ, hσ⟩ := GlobalTheory.MaxLatStruct.star_int (K := K)
    have hinj := IsFractionRing.injective (𝓞 K) K
    have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
      fun r => ⟨σ r, hσ r⟩
    unfold IsUnimodularAt
    rw [locDual_dualAt_loc h hinj hstar, ← le_antisymm (locDual_loc_dual_le h P M)
      (locDual_dualAt_le h hstar P M hM.1.1.fg)]
    exact heq
  obtain ⟨i, hi⟩ := hex
  have hi1 : vF p (a i) = 1 := le_antisymm (hle1 i) (Nat.one_le_iff_ne_zero.2 hi)
  refine ⟨i, hi1, fun j hji => ?_⟩
  by_contra hj
  exact huniq j i hji hi1 (Nat.one_le_iff_ne_zero.2 hj)

end GlobalTheory.MaxLatExpo
