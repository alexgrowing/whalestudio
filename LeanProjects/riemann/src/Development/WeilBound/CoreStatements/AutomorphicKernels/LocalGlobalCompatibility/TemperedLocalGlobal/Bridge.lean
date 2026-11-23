import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.TemperednessTransfer
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst
open PositivityTheory.Pf1.CLGD.DescRes

open scoped Topology commutatorElement

namespace PositivityTheory.Pf1.CLGD.Bridge

section Groups

variable {G : Type*} [Group G]

theorem conj_mem_of_commutator_le {U V : Subgroup G} (hUV : U ≤ V) (hc : ⁅V, V⁆ ≤ U) {g n : G}
    (hg : g ∈ V) (hn : n ∈ U) : g * n * g⁻¹ ∈ U := by
  have h1 : ⁅g, n⁆ ∈ U := hc (Subgroup.commutator_mem_commutator hg (hUV hn))
  have e : g * n * g⁻¹ = ⁅g, n⁆ * n := by
    rw [commutatorElement_def]; group
  rw [e]
  exact U.mul_mem h1 hn

theorem normal_subgroupOf {U W V : Subgroup G} (hUW : U ≤ W) (hWV : W ≤ V) (hc : ⁅V, V⁆ ≤ U) :
    (U.subgroupOf W).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := conj_mem_of_commutator_le (hUW.trans hWV) hc (hWV g.2) hn
  simpa using this

theorem exists_mid {U V : Subgroup G} (hUV : U ≤ V) (hc : ⁅V, V⁆ ≤ U) (hn0 : U.relIndex V ≠ 0) {p : ℕ}
    (hp : p.Prime) (hpn : p ∣ U.relIndex V) :
    ∃ W : Subgroup G, U ≤ W ∧ W ≤ V ∧ U.relIndex W = p ∧ W.relIndex V * p = U.relIndex V := by
  have : Fact p.Prime := ⟨hp⟩
  have hN : (U.subgroupOf V).Normal := normal_subgroupOf hUV le_rfl hc
  have : (U.subgroupOf V).FiniteIndex := ⟨hn0⟩
  have hcard : Nat.card (↥V ⧸ U.subgroupOf V) = U.relIndex V := (Subgroup.index_eq_card _).symm
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥V ⧸ U.subgroupOf V) p (hcard ▸ hpn)
  set W' : Subgroup ↥V := (Subgroup.zpowers q).comap (QuotientGroup.mk' (U.subgroupOf V)) with hW'
  have hUW : U ≤ W'.map V.subtype := by
    intro u hu
    refine ⟨⟨u, hUV hu⟩, ?_, rfl⟩
    show QuotientGroup.mk' (U.subgroupOf V) ⟨u, hUV hu⟩ ∈ Subgroup.zpowers q
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr ((Subgroup.mem_subgroupOf).mpr hu)]
    exact Subgroup.one_mem _
  refine ⟨W'.map V.subtype, hUW, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have hidx : (W'.map V.subtype).relIndex V = (Subgroup.zpowers q).index := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective V.subtype_injective,
        hW', Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have h1 : (Subgroup.zpowers q).index * p = U.relIndex V := by
      rw [← hq, ← Nat.card_zpowers, Subgroup.index_mul_card, hcard]
    have h2 := Subgroup.relIndex_mul_relIndex U (W'.map V.subtype) V hUW (Subgroup.map_subtype_le _)
    rw [hidx] at h2
    have hm : (Subgroup.zpowers q).index ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h1; exact hn0 h1.symm
    have : U.relIndex (W'.map V.subtype) * (Subgroup.zpowers q).index = p * (Subgroup.zpowers q).index := by
      rw [h2, ← h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hm) this
  · rw [Subgroup.relIndex, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective V.subtype_injective,
      hW', Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _), ← hq, ← Nat.card_zpowers,
      Subgroup.index_mul_card, hcard]

end Groups

section Chains

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

omit [IsAlgClosure E Ω] in

theorem smoothSub_mono {U V : Subgroup (Weil h)} (hU : K.SmoothSub U) (hUV : U ≤ V) : K.SmoothSub V := by
  obtain ⟨O, hO, hs⟩ := hU
  exact ⟨O, hO, fun σ h0 h1 => hUV (hs σ h0 h1)⟩

theorem smoothSub_of_isOpen {U : Subgroup (Weil h)}
    (hU : IsOpen {s : ↥(Ine (F := E) A) | ineIncl h s ∈ U}) : K.SmoothSub U := by
  have h1 : {s : ↥(Ine (F := E) A) | ineIncl h s ∈ U} ∈ 𝓝 (1 : ↥(Ine (F := E) A)) :=
    hU.mem_nhds (by simp)
  obtain ⟨u, hu, hsub⟩ := (mem_nhds_subtype (Ine (F := E) A : Set (G E Ω)) 1 _).mp h1
  obtain ⟨L, hL, hLu⟩ := (krullTopology_mem_nhds_one_iff E Ω u).mp hu
  refine ⟨L.fixingSubgroup, L.fixingSubgroup_isOpen, fun σ hσ hO => ?_⟩
  have hI : (σ : G E Ω) ∈ Ine (F := E) A := deg_eq_zero_iff.mp hσ
  have h2 : (⟨(σ : G E Ω), hI⟩ : ↥(Ine (F := E) A)) ∈ {s : ↥(Ine (F := E) A) | ineIncl h s ∈ U} :=
    hsub (hLu hO)
  have e : ineIncl h (⟨(σ : G E Ω), hI⟩ : ↥(Ine (F := E) A)) = σ := Subtype.ext rfl
  simp only [Set.mem_ofPred_eq, e] at h2
  exact h2

omit [IsAlgClosure E Ω] in

theorem chain_of_le (n : ℕ) : ∀ U V : Subgroup (Weil h), K.Chain h V → U ≤ V → ⁅V, V⁆ ≤ U →
    U.relIndex V = n → n ≠ 0 → K.SmoothSub U → K.Chain h U := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U V hV hUV hc hn hn0 hs
  rcases eq_or_ne n 1 with rfl | hn1
  · rwa [le_antisymm hUV (Subgroup.relIndex_eq_one.mp hn)]
  · have hp : n.minFac.Prime := Nat.minFac_prime hn1
    obtain ⟨W, hUW, hWV, hUWp, hWVn⟩ :=
      exists_mid hUV hc (hn ▸ hn0) hp (hn ▸ Nat.minFac_dvd n)
    have hlt : W.relIndex V < n := by
      rw [← hn] at hn0 ⊢
      rw [← hWVn]
      have hpos : 0 < W.relIndex V := by
        rcases Nat.eq_zero_or_pos (W.relIndex V) with h0 | h0
        · rw [h0, zero_mul] at hWVn; exact absurd hWVn.symm hn0
        · exact h0
      have := hp.two_le
      nlinarith
    have hW : K.Chain h W := ih _ hlt W V hV hWV (hc.trans hUW) rfl
      (by intro h0; rw [h0, zero_mul] at hWVn; exact (hn ▸ hn0) hWVn.symm) (smoothSub_mono hs hUW)
    exact K.Chain.step hW hUW (normal_subgroupOf hUW hWV hc) (hUWp ▸ hp) hs

theorem chain_of_sub {U : Subgroup (Weil h)} (hU : LocalGlobalAboveLAlt.Sub U) : K.Chain h U := by
  induction hU with
  | top => exact K.Chain.top
  | step _ hUV hc hi ho ih => exact chain_of_le _ _ _ ih hUV hc rfl hi (smoothSub_of_isOpen ho)

end Chains

section Res

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
  (h : IsPlaceOver A w) (h' : IsPlaceOver A w')

theorem mono0_res (x : WD h) : (WD.res h h' x).mono0 ↔ x.mono0 := by
  induction x using WD.ind with
  | hP n a => rw [WD.res_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff, resRep_N]

theorem charPol_res (x : WD h) (σ : ↥(Weil h')) : (WD.res h h' x).charPol σ = x.charPol (resW h h' σ) := by
  induction x using WD.ind with
  | hP n a => rw [WD.res_mk, WD.charPol_mk, WD.charPol_mk, resRep_ρ]

end Res

theorem lpDim_rc {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {a : ℕ}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) :
    (rc (algNorm σ)).lpDim = a := by
  obtain ⟨_, _, _, _, L⟩ := hrc
  exact L.dim _

theorem iwahori_compatibility_of_chains (H : K.Main) : LocalGlobalAboveLAlt.IwahoriBaseChange := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π hc hr r wt HT hG P AI hT w hw A hA O _ _ _ Bw hj σ hσ rc hrc
  have hx : (wdAt P ι Bw hA hj (r.comp (Dec (F := E) A).subtype)).lpDim = a :=
    GlobalTheory.PstLaws.lpDim_wdAt _ _ _ _ _ _
  have hy := lpDim_rc hrc σ
  refine ⟨hx.trans hy.symm, fun U hU htriv => ?_⟩
  obtain ⟨X, w', h', hrange, heq⟩ := H E Ω l ι a (by omega) π hc hr r wt HT hG P AI hT w hw A hA O Bw hj σ hσ rc hrc
    U (chain_of_sub hU) (fun t ht h0 => by have := htriv t ht h0; unfold LocalGlobalAboveLAlt.Triv at this; rwa [hy] at this)
  refine ⟨?_, fun g hg => ?_⟩
  · rw [← mono0_res hA h', heq, mono0_res hA h']
  · rw [← hrange] at hg
    obtain ⟨g', rfl⟩ := hg
    rw [← charPol_res hA h', heq, charPol_res hA h']

theorem temperedness_of_restriction (H : K.Main) (hE : LocalGlobalAboveLAlt.ExSub) (hR : LocalGlobalAboveLAlt.TempRes) : LocalGlobalAboveLAlt.TemperednessTransfer := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π hc hr r wt HT hG P AI hT w hw A hA O _ _ _ Bw hj σ hσ rc hrc s hs
  obtain ⟨U, hU, -, htriv⟩ := hE E Ω A w hA (rc (algNorm σ))
  have hy := lpDim_rc hrc σ
  obtain ⟨X, w', h', -, heq⟩ := H E Ω l ι a (by omega) π hc hr r wt HT hG P AI hT w hw A hA O Bw hj σ hσ rc hrc
    U (chain_of_sub hU) (fun t ht h0 => by have := htriv t ht h0; unfold LocalGlobalAboveLAlt.Triv at this; rwa [hy] at this)
  have h1 := (hR E X.M Ω A w w' hA h' (rc (algNorm σ)) s).mpr hs
  rw [← heq] at h1
  exact (hR E X.M Ω A w w' hA h' _ s).mp h1

end PositivityTheory.Pf1.CLGD.Bridge
