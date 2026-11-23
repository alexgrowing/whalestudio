import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsEigenLift
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Kcompact
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DeRhamEllipticIdentity

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

theorem exists_fixed_sum {K S : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [AddCommGroup S] [Module ℂ S] (ω : K →* Module.End ℂ S) (f₀ : S)
    (hU : ∃ U ∈ 𝓝 (1 : K), ∀ k ∈ U, ω k f₀ = f₀) :
    ∃ (m : ℕ) (k : Fin (m + 1) → K), ∀ g, ω g (∑ i, ω (k i) f₀) = ∑ i, ω (k i) f₀ :=
  _root_.UpperTheory.Reformulated.B.InvariantSumOfTranslates.main ω f₀ hU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
  {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}

theorem IsLocRep.mulX (L : IsLocRep M ψ om v ω ρ) {g g' : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v))
    (hg' : g' ∈ UAt σ X (evFin F v)) {φ} (hφ : φ ∈ SB _) : ω (g * g', 1) φ = ω (g, 1) (ω (g', 1) φ) := by
  simpa using L.mul g hg 1 (one_mem_UAt W v) g' hg' 1 (one_mem_UAt W v) φ hφ

def IsLocRep.onKX (L : IsLocRep M ψ om v ω ρ) : KSub σ X v →* Module.End ℂ (SB (Fin n × Fin d → Fv F v)) where
  toFun k := (ω (k.1, 1)).restrict fun φ hφ => L.pres k.1 k.2.1 1 (one_mem_UAt W v) φ hφ
  map_one' := LinearMap.ext fun φ => Subtype.ext (L.one φ φ.2)
  map_mul' a b := LinearMap.ext fun φ => Subtype.ext ((IsLocRep.mulX L) a.2.1 b.2.1 φ.2)

theorem IsLocRep.onKX_apply (L : IsLocRep M ψ om v ω ρ) (k : KSub σ X v) (φ : SB (Fin n × Fin d → Fv F v)) :
    ((IsLocRep.onKX L) k φ).1 = ω (k.1, 1) φ.1 := rfl

theorem IsLocRep.onK_apply (L : IsLocRep M ψ om v ω ρ) (k : KSub σ W v) (φ : SB (Fin n × Fin d → Fv F v)) :
    (L.onK k φ).1 = ω (1, k.1) φ.1 := rfl

theorem IsLocRep.sub_mem_aug (L : IsLocRep M ψ om v ω ρ) {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) {φ}
    (hφ : φ ∈ SB _) : ω (g, 1) φ - φ ∈ augAt om v :=
  Submodule.subset_span ⟨g, hg, φ, hφ, _, L.pres g hg 1 (one_mem_UAt W v) φ hφ,
    (L.acts g hg 1 (one_mem_UAt W v) φ hφ _).2 rfl, rfl⟩

theorem IsLocRep.smoothX (L : IsLocRep M ψ om v ω ρ) {ψ' : AddChar (AF F) ℂ} {χX χW : Chr F E}
    (hw : M.IsWeil ψ' χX χW om) :
    ∀ φ ∈ SB _, ∃ U ∈ 𝓝 (1 : UA σ X.J), ∀ g ∈ U, g ∈ UAt σ X (evFin F v) → ω (g, 1) φ = φ := by
  intro φ hφ
  have hs := IsUWeilPair.isUSplitting hw
  obtain ⟨r₀, x₀, h₀, h₁⟩ := PositivityTheory.ThKH.Locrep.exists_base (Fin n × Fin d) v
  let loc : UA σ X.J → Module.End ℂ (Fn F n d v) := fun g =>
    PositivityTheory.ThKH.Locrep.res v x₀ ∘ₗ om (g, 1) ∘ₗ PositivityTheory.ThKH.Locrep.tensL v r₀
  have key : ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB _, loc g φ = ω (g, 1) φ := fun g hg φ hφ =>
    (PositivityTheory.ThKH.Locrep.eq_of_acts v h₁ (h₀ φ hφ) ((L.acts g hg 1 (one_mem_UAt W v) φ hφ _).2 rfl)).symm
  obtain ⟨K, hK1, hK2, hK3, hK4⟩ := PositivityTheory.ThKH.Locrep.exists_small_subgroups σ X v
  obtain ⟨m, hm⟩ := PositivityTheory.ThKH.Locrep.smooth_of_weak (SB _) K hK1 hK2 loc
    (fun g hg φ hφ => by
      rw [key g (hK3 0 hg) φ hφ]; exact L.pres g (hK3 0 hg) 1 (one_mem_UAt W v) φ hφ)
    (fun φ hφ => by rw [key 1 (one_mem_UAt X v) φ hφ]; exact L.one φ hφ)
    (fun g hg g' hg' φ hφ => by
      rw [key _ (mul_mem_UAt (hK3 0 hg) (hK3 0 hg')) φ hφ, key g' (hK3 0 hg') φ hφ,
        key g (hK3 0 hg) _ (L.pres g' (hK3 0 hg') 1 (one_mem_UAt W v) φ hφ)]
      exact (IsLocRep.mulX L) (hK3 0 hg) (hK3 0 hg') hφ)
    (fun l φ hφ => (hs.cont _ (PositivityTheory.ThKH.Locrep.res_adm v x₀ l) _ (h₀ φ hφ).2).comp
      (continuous_id.prodMk continuous_const)) φ hφ
  obtain ⟨U, hU, hUK⟩ := hK4 m
  exact ⟨U, hU, fun g hg hv => by rw [← key g hv φ hφ]; exact hm g (hUK g hg hv)⟩

theorem IsLocRep.span_vac (L : IsLocRep M ψ om v ω ρ) (hs : M.vac v ∈ SB _) {z}
    (hz : z ∈ Submodule.span ℂ {z | ∃ g ∈ UAt σ X (evFin F v), z = ω (g, 1) (M.vac v)}) :
    ∃ c : ℂ, z - c • M.vac v ∈ augAt om v := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, hg, rfl⟩ := hy
    exact ⟨1, by rw [one_smul]; exact (IsLocRep.sub_mem_aug L) hg hs⟩
  | zero => exact ⟨0, by rw [zero_smul, sub_zero]; exact Submodule.zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨c, hc⟩ := hy
    obtain ⟨c', hc'⟩ := hz
    refine ⟨c + c', ?_⟩
    have e : y + z - (c + c') • M.vac v = (y - c • M.vac v) + (z - c' • M.vac v) := by rw [add_smul]; abel
    rw [e]
    exact add_mem hc hc'
  | smul a y _ hy =>
    obtain ⟨c, hc⟩ := hy
    refine ⟨a * c, ?_⟩
    have e : a • y - (a * c) • M.vac v = a • (y - c • M.vac v) := by rw [smul_sub, smul_smul]
    rw [e]
    exact Submodule.smul_mem _ _ hc

theorem isVacSph_of (L : IsLocRep M ψ om v ω ρ) (H : IsHowe M v ω) (hKX : IsCompact (KAt σ X v))
    (hKW : IsCompact (KAt σ W v)) (hs : M.vac v ∈ SB _)
    (smX : ∀ φ ∈ SB _, ∃ U ∈ 𝓝 (1 : UA σ X.J), ∀ g ∈ U, g ∈ UAt σ X (evFin F v) → ω (g, 1) φ = φ) :
    IsVacSph M om v ω := by
  classical
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  haveI : IsTopologicalGroup (GL (Fin n) (AE F E)) := inferInstance
  haveI : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  haveI : IsTopologicalGroup (UA σ X.J) := inferInstance
  haveI : IsTopologicalGroup (UA σ W.J) := inferInstance
  haveI : IsTopologicalGroup (KSub σ X v) := inferInstance
  haveI : IsTopologicalGroup (KSub σ W v) := inferInstance
  haveI : CompactSpace (KSub σ X v) := isCompact_iff_compactSpace.1 hKX
  haveI : CompactSpace (KSub σ W v) := isCompact_iff_compactSpace.1 hKW
  refine ⟨H.fixW, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨U, hU, hU'⟩ := smX φ hφ
    obtain ⟨m, k, hk⟩ := exists_fixed_sum (IsLocRep.onKX L) ⟨φ, hφ⟩
      ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt hU, fun k hk => Subtype.ext (hU' k.1 hk k.2.1)⟩
    set f := ∑ i, ω ((k i).1, 1) φ with hf
    have hfS : f ∈ SB _ := sum_mem fun i _ => L.pres _ (k i).2.1 1 (one_mem_UAt W v) φ hφ
    have hfix : ∀ g ∈ KAt σ X v, ω (g, 1) f = f := fun g hg => by
      have := congrArg Subtype.val (hk ⟨g, hg⟩)
      simpa only [(IsLocRep.onKX_apply L), Submodule.coe_sum] using this
    have hgen := H.genW f hfS hfix
    have haug : ((m + 1 : ℕ) : ℂ) • φ - f ∈ augAt om v := by
      have e : ((m + 1 : ℕ) : ℂ) • φ - f = ∑ i : Fin (m + 1), -(ω ((k i).1, 1) φ - φ) := by
        rw [hf, Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Nat.cast_smul_eq_nsmul ℂ, neg_sub]
      rw [e]
      exact sum_mem fun i _ => neg_mem ((IsLocRep.sub_mem_aug L) (k i).2.1 hφ)
    have hc : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)
    refine Submodule.mem_sup.2 ⟨_, Submodule.smul_mem _ (((m + 1 : ℕ) : ℂ)⁻¹) haug, _,
      Submodule.smul_mem _ (((m + 1 : ℕ) : ℂ)⁻¹) hgen, ?_⟩
    rw [← smul_add, sub_add_cancel, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · obtain ⟨U, hU, hU'⟩ := L.smooth φ hφ
    obtain ⟨m, k, hk⟩ := exists_fixed_sum L.onK ⟨φ, hφ⟩
      ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt hU, fun k hk => Subtype.ext (hU' k.1 hk k.2.1)⟩
    set f := ∑ i, ω (1, (k i).1) φ with hf
    have hfS : f ∈ SB _ := sum_mem fun i _ => L.pres 1 (one_mem_UAt X v) _ (k i).2.1 φ hφ
    have hfix : ∀ g ∈ KAt σ W v, ω (1, g) f = f := fun g hg => by
      have := congrArg Subtype.val (hk ⟨g, hg⟩)
      simpa only [(IsLocRep.onK_apply L), Submodule.coe_sum] using this
    obtain ⟨c, hc⟩ := (IsLocRep.span_vac L) hs (H.genX f hfS hfix)
    exact ⟨m, fun i => (k i).1, c, fun i => (k i).2, hc⟩

theorem vacInert (h : HoweInert) : VacInert := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v he
  obtain ⟨p, p'⟩ := h F E σ B a a' G X om om' hT v he
  exact ⟨fun ω ρ L => isVacSph_of L (p ω ρ L) (isCompact_KAt G.V hT.geo.hV.lat v) (isCompact_KAt G.W hT.geo.hW.lat v)
      (hT.geo.hM.vac v).1 ((IsLocRep.smoothX L) hT.weil),
    fun ω ρ L => isVacSph_of L (p' ω ρ L) (isCompact_KAt G.V' hT.geo.hV'.lat v) (isCompact_KAt G.W hT.geo.hW.lat v)
      (hT.geo.hM'.vac v).1 ((IsLocRep.smoothX L) hT.weil')⟩

end PositivityTheory.Sph

end
