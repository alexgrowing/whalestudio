import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {H : LB M.Z} {d : H.ι → Ω}
  {J : Type} {σ : J → H.Sec} {t : J → Ω}

theorem mem_nonzeroLocus_iff_div (hH : H.IsLB) (hd : M.GenTriv H d) (hv : ∀ j, M.HasVal d (σ j) (t j))
    (hg : ∀ l, ∀ z ∈ H.U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ M.O z) (i : J) (z : M.Z) :
    z ∈ Out.nonzeroLocus (σ i) ↔ M.Div t i z := by
  constructor
  · intro hz
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    have hzl : z ∈ H.U l := M.Z.basicOpen_le _ hl
    obtain ⟨h0, h1⟩ := (isUnit_O_iff _).1 ((isUnit_valF_iff hzl _).2 hl)
    have e := hv i l ⟨z, hzl⟩
    dsimp only at h0 h1
    rw [e] at h0 h1
    have hi : t i ≠ 0 := fun h => h0 (by rw [h, zero_div])
    refine ⟨hi, fun j => ?_⟩
    have h2 := valF_mem_O hzl ((σ j).f l)
    rw [hv j l ⟨z, hzl⟩] at h2
    have h3 := mul_mem h2 h1
    have hdl := hd.ne l
    have e' : t j / d l * (t i / d l)⁻¹ = t j / t i := by field_simp
    rwa [e'] at h3
  · intro hz
    have hc : z ∈ ⨆ l, H.U l := by rw [hH.cover]; trivial
    obtain ⟨l, hzl⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    obtain ⟨i', hi', h1⟩ := hg l z hzl
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨l, (isUnit_valF_iff hzl _).1 ((isUnit_O_iff _).2 ?_)⟩
    dsimp only
    rw [hv i l ⟨z, hzl⟩]
    refine ⟨div_ne_zero hz.1 (hd.ne l), ?_⟩
    have h3 := mul_mem h1 (hz.2 i')
    have hi := hz.1
    have e' : d l / t i' * (t i' / t i) = (t i / d l)⁻¹ := by field_simp
    rwa [e'] at h3

theorem immBy_of_div : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z) (d : H.ι → Ω) (J : Type) (σ : J → H.Sec) (t : J → Ω) (k : Type) [CommRing k] (p : M.Z ⟶ Sp k) (ψ : k →+* Ω), H.IsLB → M.GenTriv H d → (∀ j, M.HasVal d (σ j) (t j)) → (∀ l, ∀ z ∈ H.U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ M.O z) → M.pt ≫ p = spMap ψ → (∀ i, t i ≠ 0 → ∃ U : M.Z.Opens, IsAffineOpen U ∧ (U : Set M.Z) = {z | M.Div t i z} ∧ ∀ x ∈ M.ringOn U, x ∈ Subring.closure (Set.range ψ ∪ Set.range fun j => t j / t i)) → ImmBy p H σ Set.univ := by
  intro o Ω _ _ _ M H d J σ t k _ p ψ hH hd hv hg hp hU
  have key := mem_nonzeroLocus_iff_div hH hd hv hg
  refine ⟨top_unique fun z _ => ?_, fun i _ => ?_⟩
  · have hc : z ∈ ⨆ l, H.U l := by rw [hH.cover]; trivial
    obtain ⟨l, hzl⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    obtain ⟨i, hi, h1⟩ := hg l z hzl
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨trivial, (key i z).2 ⟨hi, fun j => ?_⟩⟩⟩
    have h2 := valF_mem_O hzl ((σ j).f l)
    rw [hv j l ⟨z, hzl⟩] at h2
    have h3 := mul_mem h2 h1
    have hdl := hd.ne l
    have e' : t j / d l * (d l / t i) = t j / t i := by field_simp
    rwa [e'] at h3
  · have hempty : ∀ V : M.Z.Opens, ¬ (V : Set M.Z).Nonempty → Subsingleton Γ(M.Z, V) := fun V hV => by
      have : V = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hV)
      subst this
      infer_instance
    have key' := key i
    generalize Out.nonzeroLocus (σ i) = W at key' ⊢
    by_cases hi : t i = 0
    · have hW : W = ⊥ := eq_bot_iff.2 fun z hz => (((key' z).1 hz).1 hi).elim
      subst hW
      refine ⟨isAffineOpen_bot _, fun _ => 0, fun j l => ?_,
        top_unique fun f _ => Subsingleton.elim 0 f ▸ zero_mem _⟩
      have := hempty (⊥ ⊓ H.U l) (fun ⟨z, hz⟩ => hz.1)
      exact Subsingleton.elim _ _
    · obtain ⟨U, hUa, hUe, hR⟩ := hU i hi
      have hWU : W = U := SetLike.ext fun z => (key' z).trans (Set.ext_iff.1 hUe z).symm
      subst hWU
      have hne : (W : Set M.Z).Nonempty := ⟨_, (key' _).2 (div_genericPoint hi)⟩
      have hr : ∀ j, ∃ f : Γ(M.Z, W), valF M.pt W f = t j / t i := fun j =>
        (mem_ringOn_iff_exists hne).1 (mem_ringOn.2 fun z hz => ((key' z).1 hz).2 j)
      choose r hr using hr
      refine ⟨hUa, r, fun j l => ?_, ?_⟩
      · by_cases hl : ((W ⊓ H.U l : M.Z.Opens) : Set M.Z).Nonempty
        · have hl' : (H.U l : Set M.Z).Nonempty := hl.mono fun z hz => hz.2
          apply M.res_injective _ hl
          rw [map_mul, res_apply, res_apply, res_apply, M.valF_resG _ hl, M.valF_resG _ hl, M.valF_resG _ hl,
            hv j l hl', hv i l hl', hr]
          have hdl := hd.ne l
          field_simp
        · have := hempty _ hl
          exact Subsingleton.elim _ _
      · refine top_unique fun f _ => ?_
        have h1 := hR _ ((mem_ringOn_iff_exists hne).2 ⟨f, rfl⟩)
        have e : (Set.range ψ ∪ Set.range fun j => t j / t i) =
            M.res W hne '' (Set.range (constFn p W) ∪ Set.range r) := by
          rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]
          congr 2
          · funext a
            exact ((M.res_apply W hne _).trans
              (valR_constFn_of_over p ψ M.pt hp W (M.top_le_preimage_pt hne) a)).symm
          · funext j
            exact ((M.res_apply W hne _).trans (hr j)).symm
        rw [e, ← RingHom.map_closure] at h1
        obtain ⟨g, hg1, hg2⟩ := h1
        have : g = f := M.res_injective W hne (hg2.trans (M.res_apply W hne f).symm)
        exact this ▸ hg1

end GlobalTheory.ZH.RatModel
