import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PullPieces
import GroundTheory.AutomorphicForms.WhittakerLSpace
import GroundTheory.AutomorphicForms.WhittakerDistribution

noncomputable section

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker Set Topology

namespace PositivityTheory.RgUd.TP.Desc.Restr.Ppull2B

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n N q : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {Z' : Subalgebra k (Matrix (Fin N) (Fin N) k)}
  {φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin N) (Fin N) k} {e : (Fin n → k) ≃+ (Fin N → k)}

def Φ (φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin N) (Fin N) k) (e : (Fin n → k) ≃+ (Fin N → k)) (p : Sp k n) : Sp k N :=
  (φ p.1, e p.2)

def eH (hd : PhiData q Z Z' φ e) : (Fin n → k) ≃ₜ (Fin N → k) :=
  { toEquiv := e.toEquiv, continuous_toFun := hd.econt, continuous_invFun := hd.econt' }

theorem isClosedEmbedding_Φ (hd : PhiData q Z Z' φ e) : IsClosedEmbedding (Φ φ e) :=
  hd.emb.prodMap (eH hd).isClosedEmbedding

theorem comp_mem (hd : PhiData q Z Z' φ e) {f : Sp k N → ℂ} (hf : f ∈ locallyConstantCompactSupport (Sp k N) ℂ ℂ) :
    f ∘ Φ φ e ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ := by
  obtain ⟨h1, h2⟩ := hf
  exact ⟨h1.comp_continuous (isClosedEmbedding_Φ hd).continuous,
    h2.comp_isClosedEmbedding (isClosedEmbedding_Φ hd)⟩

theorem inv_val (hd : PhiData q Z Z' φ e) {g : GL (Fin n) k} {g' : GL (Fin N) k} (h : φ g.val = g'.val) :
    φ g⁻¹.val = g'⁻¹.val := by
  calc φ g⁻¹.val = φ g⁻¹.val * (g'.val * g'⁻¹.val) := by simp
    _ = φ (g⁻¹.val * g.val) * g'⁻¹.val := by rw [map_mul, h, mul_assoc]
    _ = g'⁻¹.val := by simp

theorem act_Φ (hd : PhiData q Z Z' φ e) {g : GL (Fin n) k} {g' : GL (Fin N) k} (h : φ g.val = g'.val) (p : Sp k n) :
    act g' (Φ φ e p) = Φ φ e (act g p) := by
  simp only [act, Φ, map_mul, hd.intertw, h, inv_val hd h]

private theorem exists_compact_clopen_between {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] {K U : Set Y} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V : Set Y, IsClopen V ∧ IsCompact V ∧ K ⊆ V ∧ V ⊆ U := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  have hb := loc_compact_Haus_tot_disc_of_zero_dim (H := Y)
  have hx : ∀ x : K, ∃ V : Set Y, IsClopen V ∧ (x : Y) ∈ V ∧ V ⊆ interior L := fun x =>
    hb.mem_nhds_iff.1 (isOpen_interior.mem_nhds (hKL x.2))
  choose V hV using hx
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover V (fun x => (hV x).1.isOpen)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hV ⟨x, hx⟩).2.1⟩)
  have hcl : IsClopen (⋃ i ∈ I, V i) := I.finite_toSet.isClopen_biUnion (fun i _ => (hV i).1)
  refine ⟨⋃ i ∈ I, V i, hcl, ?_, hI, ?_⟩
  · exact hL.of_isClosed_subset hcl.isClosed
      (iUnion₂_subset fun i _ => (hV i).2.2.trans interior_subset)
  · exact iUnion₂_subset fun i _ => (hV i).2.2.trans (interior_subset.trans hLU)

private theorem exists_compact_clopen_preimage_Phi_eq (hd : PhiData q Z Z' φ e) {A : Set (Sp k n)} (hA : IsClopen A)
    (hAc : IsCompact A) (hAO : A ⊆ {p | p.2 ≠ 0}) :
    ∃ B : Set (Sp k N), IsClopen B ∧ IsCompact B ∧ B ⊆ {p | p.2 ≠ 0} ∧ Φ φ e ⁻¹' B = A := by
  haveI := totallyDisconnectedSpace_localField (F := k)
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin N → Fin N → k))
  have hE := isClosedEmbedding_Φ hd
  have hO : IsOpen ({p : Sp k N | p.2 ≠ 0} ∩ (Φ φ e '' Aᶜ)ᶜ) :=
    (isOpen_ne_fun continuous_snd continuous_const).inter
      (hE.isClosedMap _ hA.isOpen.isClosed_compl).isOpen_compl
  have hKO : Φ φ e '' A ⊆ {p : Sp k N | p.2 ≠ 0} ∩ (Φ φ e '' Aᶜ)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · show e x.2 ≠ 0
      intro h0
      exact hAO hx ((map_eq_zero_iff e e.injective).1 h0)
    · rintro ⟨y, hy, hyx⟩
      exact hy (hE.injective hyx ▸ hx)
  obtain ⟨V, hV, hVc, hKV, hVO⟩ :=
    exists_compact_clopen_between (Y := Sp k N) (hAc.image hE.continuous) hO hKO
  refine ⟨V, hV, hVc, fun p hp => (hVO hp).1, ?_⟩
  ext x
  constructor
  · intro hx
    by_contra hxA
    exact (hVO hx).2 ⟨x, hxA, rfl⟩
  · intro hx
    exact hKV ⟨x, hx, rfl⟩

private theorem exists_supportedIn_comp_Phi_eq (hd : PhiData q Z Z' φ e) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn {p : Sp k n | p.2 ≠ 0}) :
    ∃ h ∈ supportedIn {p : Sp k N | p.2 ≠ 0}, h ∘ Φ φ e = f := by
  obtain ⟨⟨hlc, hcs⟩, hsupp⟩ := hf
  have hK := hcs.isCompact
  have key : ∀ c : ℂ, c ≠ 0 → ∃ B : Set (Sp k N), IsClopen B ∧ IsCompact B ∧
      B ⊆ {p | p.2 ≠ 0} ∧ Φ φ e ⁻¹' B = f ⁻¹' {c} := by
    intro c hc
    have hcl : IsClopen (f ⁻¹' {c}) := hlc.isClopen_fiber c
    have hsub : f ⁻¹' {c} ⊆ Function.support f := fun x hx => by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      simp [Function.mem_support, hx, hc]
    exact exists_compact_clopen_preimage_Phi_eq hd hcl
      (hK.of_isClosed_subset hcl.isClosed (hsub.trans (subset_tsupport f))) (hsub.trans hsupp)
  choose! B hB using key
  have hfin : (Set.range f).Finite := by
    haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hK
    have hc : Continuous (fun x : tsupport f => (x : Sp k n)) := continuous_subtype_val
    have h1 := (hlc.comp_continuous hc).range_finite
    refine (h1.insert 0).subset ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : f x = 0
    · exact Or.inl hx
    · exact Or.inr ⟨⟨x, subset_tsupport f hx⟩, rfl⟩
  set S := hfin.toFinset.filter (· ≠ 0) with hS
  refine ⟨∑ c ∈ S, c • (B c).indicator (fun _ => (1 : ℂ)), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
    obtain ⟨hBc, hBk, hBO, -⟩ := hB c hc0
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro s
      have := Set.indicator_const_preimage (B c) s (1 : ℂ)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h | h | h | h <;> rw [h]
      exacts [isOpen_univ, hBc.isOpen, hBc.isClosed.isOpen_compl, isOpen_empty]
    · exact HasCompactSupport.intro hBk fun x hx => Set.indicator_of_notMem hx _
    · exact Set.support_indicator_subset.trans hBO
  · funext x
    simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hterm : ∀ c ∈ S, c * (B c).indicator (fun _ => (1 : ℂ)) (Φ φ e x) =
        if f x = c then c else 0 := by
      intro c hc
      have hpre := (hB c (Finset.mem_filter.1 hc).2).2.2.2
      by_cases hx : f x = c
      · have hm : Φ φ e x ∈ B c := by
          show x ∈ Φ φ e ⁻¹' B c
          rw [hpre]
          exact hx
        simp [Set.indicator_of_mem hm, hx]
      · have hm : Φ φ e x ∉ B c := by
          show x ∉ Φ φ e ⁻¹' B c
          rw [hpre]
          exact hx
        simp [Set.indicator_of_notMem hm, hx]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hne
      exact h (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨x, rfl⟩, Ne.symm hne⟩)

theorem fibVan_pull (hd : PhiData q Z Z' φ e) (F : Set (Matrix (Fin n) (Fin n) k))
    (F' : Set (Matrix (Fin N) (Fin N) k)) (hF : ∀ x ∈ F, φ x ∈ F') (h' : FibVan Z' F') : FibVan Z F := by
  intro ξ hS hI
  let ξ' : (Sp k N → ℂ) →ₗ[ℂ] ℂ := ξ.comp (LinearMap.funLeft ℂ ℂ (Φ φ e))
  have hmem : ∀ g ∈ supportedIn (univ : Set (Sp k N)),
      g ∘ Φ φ e ∈ supportedIn (univ : Set (Sp k n)) := by
    intro g hg
    obtain ⟨hg1, -⟩ := hg
    exact ⟨comp_mem hd hg1, subset_univ _⟩
  have hS' : Supp ξ' (F' ×ˢ univ) := by
    intro g hg hz
    show ξ (g ∘ Φ φ e) = 0
    refine hS _ (hmem g hg) ?_
    rintro p ⟨hp, -⟩
    exact hz _ ⟨hF _ hp, mem_univ _⟩
  have hI' : PositivityTheory.RgUd.T.Inv Z' ξ' := by
    intro g' hg' g hg
    obtain ⟨g0, hg0, hφ⟩ := (hd.gz g').1 hg'
    show ξ ((fun p => g (act g' p)) ∘ Φ φ e) = ξ (g ∘ Φ φ e)
    have hfun : ((fun p => g (act g' p)) ∘ Φ φ e) = fun p => (g ∘ Φ φ e) (act g0 p) := by
      funext p
      simp only [Function.comp_apply, act_Φ hd hφ]
    rw [hfun]
    exact hI g0 hg0 _ (hmem g hg)
  have hK := h' ξ' hS' hI'
  intro f hf
  obtain ⟨h, hh, rfl⟩ := exists_supportedIn_comp_Phi_eq hd hf
  exact hK h hh

end PositivityTheory.RgUd.TP.Desc.Restr.Ppull2B
