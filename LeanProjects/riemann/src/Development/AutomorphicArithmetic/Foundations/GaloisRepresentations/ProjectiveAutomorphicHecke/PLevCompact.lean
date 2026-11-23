import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pLevCompact_of :
    UpperTheory.Gal.CertificateRingHomMap.IntCompact → UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.LevOpen → UpperTheory.Gal.CertificateRingHomMap.LevCompact := by
  intro hC hI hL hO E _ _ _ n Up w₀ hw₀ S Kw hS
  obtain ⟨-, hAp, -, -, -, -⟩ := hL E n w₀ hw₀
  have hclosed : IsClosed (lev S Kw : Set (GUf E n)) :=
    Subgroup.isClosed_of_isOpen _ (hO E n S Kw hS.opn)
  have hK₁ := hC E n
  have hJ := hS.cpt w₀ hS.mem
  have hKo := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w₀ n).1
  obtain ⟨F, -, hF⟩ := hJ.elim_nhds_subcover
    (fun a => {y : GLw n w₀ | a⁻¹ * y ∈ GlobalTheory.LFun.KGL w₀ n}) (fun a _ => by
      refine IsOpen.mem_nhds (hKo.preimage (continuous_const.mul continuous_id)) ?_
      simp [Subgroup.one_mem])
  have hcov : IsCompact (⋃ a ∈ F, (fun x : GUf E n => loc hw₀ a * x) ''
      (lev (E := E) (n := n) ∅ (fun _ => ⊤) : Set (GUf E n))) :=
    F.isCompact_biUnion fun a _ => hK₁.image (continuous_const.mul continuous_id)
  refine hcov.of_isClosed_subset hclosed fun k hk => ?_
  obtain ⟨hsim, hmem, hoff⟩ := mem_lev.1 hk
  obtain ⟨a, haF, ha⟩ := Set.mem_iUnion₂.1 (hF (hmem w₀ hS.mem))
  have ha' : a⁻¹ * comp w₀ k ∈ GlobalTheory.LFun.KGL w₀ n := ha
  have hsim' : sim ((loc hw₀ a)⁻¹ * k) ∈ ZU := by simpa using hsim
  have hw : comp w₀ ((loc hw₀ a)⁻¹ * k) ∈ GlobalTheory.LFun.KGL w₀ n := by simpa using ha'
  have hint : ∀ u : Plc E, u ≠ w₀ → u ≠ cj w₀ → comp u k ∈ GlobalTheory.LFun.KGL u n := by
    intro u h1 h2
    have hcc : cj (cj u) = u := GlobalTheory.SplitPts.conjSrc_conjSrc_cm u
    by_cases hu : u ∈ S
    · exact hS.le u hu h1 (hmem u hu)
    by_cases hc : cj u ∈ S
    · have hne : cj u ≠ w₀ := fun h => h2 (by rw [← h, hcc])
      have := hI E n k (cj u) hsim (hS.le _ hc hne (hmem _ hc))
      rwa [hcc] at this
    · exact hoff u hu hc
  have hk' : (loc hw₀ a)⁻¹ * k ∈ lev (E := E) (n := n) ∅ (fun _ => ⊤) := by
    refine mem_lev.2 ⟨hsim', by simp, fun u _ _ => ?_⟩
    by_cases h1 : u = w₀
    · subst h1; exact hw
    by_cases h2 : u = cj w₀
    · subst h2; exact hI E n _ w₀ hsim' hw
    · have happ : GlobalTheory.Cong.Apart u w₀ := (hAp u).2 ⟨h1, h2⟩
      have : comp u ((loc hw₀ a)⁻¹ * k) = comp u k := by
        rw [map_mul, map_inv, comp_loc_of_apart hw₀ happ, inv_one, one_mul]
      rw [this]
      exact hint u h1 h2
  exact Set.mem_iUnion₂.2 ⟨a, haF, _, hk', by simp⟩
