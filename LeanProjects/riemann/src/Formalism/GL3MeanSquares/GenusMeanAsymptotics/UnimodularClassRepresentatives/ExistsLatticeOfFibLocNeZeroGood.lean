import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LamGEqOneOfOrtho
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic

open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.UnimodularLocalization

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem nondegenerate (hd : IsTotPosDef h) : h.Nondegenerate := by
  have hne : ∀ v : V, v ≠ 0 → h v v ≠ 0 := by
    intro v hv e
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd v hv φ
    rw [e, map_zero] at this
    exact lt_irrefl _ this
  constructor
  · intro x hx
    by_contra h0
    exact hne x h0 (hx x)
  · intro x hx
    by_contra h0
    exact hne x h0 (hx x)

theorem loc_eq_loc_adjoin_cut (S : VecSplit h h') {P : Ideal (𝓞 K)} (hP : P.IsPrime)
    {B : Submodule (𝓞 K) V} (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B)
    (hx : S.x₀ ∈ Formalism.HermitianLatticesTheory.loc (K := K) P B)
    (hn' : (h S.x₀ S.x₀)⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P) :
    Formalism.HermitianLatticesTheory.loc (K := K) P B = Formalism.HermitianLatticesTheory.loc (K := K) P (S.adjoin (S.cut B)) := by
  obtain ⟨hloc, -⟩ := Formalism.HermitianLatticesTheory.locBasic (𝓞 K) K V Formalism.HermitianLatticesTheory.genusCovol_hinj
  have hidem : Formalism.HermitianLatticesTheory.loc (K := K) P (Formalism.HermitianLatticesTheory.loc (K := K) P B) = Formalism.HermitianLatticesTheory.loc (K := K) P B :=
    (hloc P hP B B).2.2.1
  apply le_antisymm
  · intro b hb
    obtain ⟨c, a, rfl⟩ := S.cover b
    have hc : c ∈ Formalism.HermitianLatticesTheory.locR (K := K) P := by
      have h1 := LocalizedFibreSets.form_mem_locR hBi P hx hb
      rw [S.h_x₀_comb] at h1
      have := mul_mem_locR P h1 hn'
      rwa [mul_assoc, mul_inv_cancel₀ S.hx₀, mul_one] at this
    rw [S.comb_mem_loc_adjoin_iff]
    refine ⟨hc, ?_⟩
    have h2 : S.ι a ∈ Formalism.HermitianLatticesTheory.loc (K := K) P B := by
      have h3 := Submodule.sub_mem _ hb (LocalizedFibreSets.smul_mem_of_loc_eq hidem hc hx)
      rwa [add_sub_cancel_left] at h3
    obtain ⟨s, hs', h4⟩ := h2
    refine ⟨s, hs', ?_⟩
    rw [VecSplit.mem_cut_iff, LinearMap.map_smul_of_tower]
    exact h4
  · rw [← hidem]
    apply (hloc P hP _ _).2.1
    unfold VecSplit.adjoin
    refine sup_le ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hx
    · rw [Submodule.map_le_iff_le_comap]
      intro a ha
      exact (hloc P hP B B).1 ha

theorem unimod_of_unimod_adjoin (hs : h.IsSymm) (S : VecSplit h h') {p : Ideal (𝓞 K)}
    {L' : Submodule (𝓞 K) V'} (hU : Formalism.HermitianLatticesTheory.IsUnimodularAt h p (S.adjoin L')) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h' p L' := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodularAt at hU ⊢
  ext a
  have h1 := LocalizedFibreSets.comb_mem_dualAt_iff hs S p L' 0 a
  rw [hU, S.comb_mem_loc_adjoin_iff, zero_mul] at h1
  constructor
  · intro ha
    exact (h1.mpr ⟨Submodule.zero_mem _, ha⟩).2
  · intro ha
    exact (h1.mp ⟨Submodule.zero_mem _, ha⟩).2

theorem isIntegralLat_cut (S : VecSplit h h') {B : Submodule (𝓞 K) V}
    (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B) : Formalism.HermitianLatticesTheory.IsIntegralLat h' (S.cut B) := by
  intro x hx y hy
  rw [← S.isom]
  exact hBi _ hx _ hy

theorem algebraMap_smul_K (t : 𝓞 F) (c : K) :
    algebraMap (𝓞 F) (𝓞 K) t • c = algebraMap F K (t : F) * c := by
  rw [Algebra.smul_def]
  rfl

theorem locR_eq_locF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) :
    Formalism.HermitianLatticesTheory.locR (K := K) P =
      locF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (1 : Submodule (𝓞 K) K) :=
  (locF_eq_loc hK hF hP (1 : Submodule (𝓞 K) K)).symm

theorem inv_mem_locF_one {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn0 : n ≠ 0)
    (hn : n ∉ 𝔭) : (algebraMap F K (n : F))⁻¹ ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  rw [LocF.mem_locF_iff h𝔭.isPrime]
  refine ⟨n, hn, ?_⟩
  rw [algebraMap_smul_K, mul_inv_cancel₀]
  · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  · rw [map_ne_zero]
    exact fun e => hn0 (RingOfIntegers.ext e)

theorem vd_cut_eq_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {B : Submodule (𝓞 K) V}
    (hB : Submodule.IsLattice K B) (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvB : vd h B 𝔭 = 0) (hvn : vF 𝔭 n = 0) (hx : S.x₀ ∈ locF 𝔭 B) :
    vd h' (S.cut B) 𝔭 = 0 := by
  obtain ⟨P, hP, rfl⟩ := LocalizedFibreSets.exists_max_over (K := K) h𝔭
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact S.hx₀ (by rw [hn]; simp)
  rw [← isUnimodularAt_iff_vd hK hF hs hd hB hBi hP] at hvB
  rw [← isUnimodularAt_iff_vd hK hF (S.isSymm hs) (S.isTotPosDef hd) (StabilizerLattices.isLattice_cut S hB)
    (isIntegralLat_cut S hBi) hP]
  apply unimod_of_unimod_adjoin hs S
  rw [locF_eq_loc hK hF hP] at hx
  have hn' : (h S.x₀ S.x₀)⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P := by
    rw [locR_eq_locF hK hF hP, hn]
    exact inv_mem_locF_one h𝔭 hn0 (LocalizedFibreSets.notMem_of_vF_zero h𝔭 hn0 hvn)
  rwa [← isUnimodularAt_of_loc_eq P (loc_eq_loc_adjoin_cut S hP.isPrime hBi hx hn')]

theorem exists_unimod_through (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {P : Ideal (𝓞 K)}
    (hP : P.IsPrime) (hU : Formalism.HermitianLatticesTheory.IsUnimodularAt h P L) {x₀ : V}
    (hx : h x₀ x₀ ∈ (1 : Submodule (𝓞 K) K)) :
    ∃ B : Submodule (𝓞 K) V, Submodule.IsLattice K B ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h B ∧
      Formalism.HermitianLatticesTheory.IsUnimodularAt h P B ∧ x₀ ∈ B := by
  obtain ⟨hanti, hbi, hsup, hint, -⟩ := Formalism.HermitianLatticesTheory.dualBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  have DL := Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs (nondegenerate hd) Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨hloc, -⟩ := Formalism.HermitianLatticesTheory.locBasic (𝓞 K) K V Formalism.HermitianLatticesTheory.genusCovol_hinj
  set X : Submodule (𝓞 K) V := Submodule.span (𝓞 K) {x₀} with hX
  have hxX : x₀ ∈ X := Submodule.mem_span_singleton_self x₀
  have hXX : X ≤ Formalism.HermitianLatticesTheory.dual h X := by
    intro y hy
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_dual]
    intro z hz
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [LocalizedFibreSets.form_smul_smul]
    exact Submodule.smul_mem _ _ hx
  have hLd : L ≤ Formalism.HermitianLatticesTheory.dual h L := (hint L).mp hLi
  set B : Submodule (𝓞 K) V := (L ⊓ Formalism.HermitianLatticesTheory.dual h X) ⊔ X with hB
  have hBfg : B.FG := (hL.fg.of_le inf_le_left).sup (Submodule.fg_span_singleton x₀)
  have hBl : Submodule.IsLattice K B := by
    refine ⟨hBfg, ?_⟩
    rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
    intro v hv
    obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (h x₀ v)
    have hb0 : algebraMap (𝓞 K) K b ≠ 0 := by
      rw [map_ne_zero_iff _ Formalism.HermitianLatticesTheory.genusCovol_hinj]
      exact nonZeroDivisors.ne_zero hb
    have h1 : b • v ∈ B := by
      apply Submodule.mem_sup_left
      refine ⟨L.smul_mem b hv, ?_⟩
      change b • v ∈ Formalism.HermitianLatticesTheory.dual h X
      rw [Formalism.HermitianLatticesTheory.isomAct_mem_dual]
      intro z hz
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
      rw [LocalizedFibreSets.form_smul_smul, mul_smul]
      apply Submodule.smul_mem
      rw [← e, Algebra.smul_def, mul_div_cancel₀ _ hb0]
      exact Submodule.mem_one.mpr ⟨a, rfl⟩
    have h2 : (algebraMap (𝓞 K) K b)⁻¹ • (b • v) ∈ Submodule.span K (B : Set V) :=
      Submodule.smul_mem _ _ (Submodule.subset_span h1)
    rwa [← algebraMap_smul K b v, smul_smul, inv_mul_cancel₀ hb0, one_smul] at h2
  have lat2 : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.dual h L ⊔ X) := by
    refine ⟨(DL L hL).1.fg.sup (Submodule.fg_span_singleton x₀), ?_⟩
    rw [eq_top_iff, ← (DL L hL).1.span_eq_top]
    exact Submodule.span_mono (show Formalism.HermitianLatticesTheory.dual h L ≤ Formalism.HermitianLatticesTheory.dual h L ⊔ X from le_sup_left)
  have e1 : L ⊓ Formalism.HermitianLatticesTheory.dual h X = Formalism.HermitianLatticesTheory.dual h (Formalism.HermitianLatticesTheory.dual h L ⊔ X) := by
    rw [hsup, (DL L hL).2.1]
  have e2 : Formalism.HermitianLatticesTheory.dual h (L ⊓ Formalism.HermitianLatticesTheory.dual h X) = Formalism.HermitianLatticesTheory.dual h L ⊔ X := by
    rw [e1, (DL _ lat2).2.1]
  have e3 : Formalism.HermitianLatticesTheory.dual h B = (Formalism.HermitianLatticesTheory.dual h L ⊔ X) ⊓ Formalism.HermitianLatticesTheory.dual h X := by
    rw [hB, hsup, e2]
  refine ⟨B, hBl, ?_, ?_, Submodule.mem_sup_right hxX⟩
  · rw [hint, e3]
    refine sup_le (le_inf (inf_le_left.trans (hLd.trans le_sup_left)) inf_le_right)
      (le_inf le_sup_right hXX)
  · have LDB := (Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range B hBfg).1 P hP
    have LDL := (Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range L hL.fg).1 P hP
    have e4 : Formalism.HermitianLatticesTheory.loc (K := K) P (Formalism.HermitianLatticesTheory.dual h L) = Formalism.HermitianLatticesTheory.loc (K := K) P L := by
      rw [LDL.1, ← LDL.2]
      exact hU
    unfold Formalism.HermitianLatticesTheory.IsUnimodularAt
    rw [LDB.2, ← LDB.1, e3, (hloc P hP _ _).2.2.2.1, (hloc P hP _ _).2.2.2.2, e4, hB,
      (hloc P hP _ _).2.2.2.2, (hloc P hP _ _).2.2.2.1, sup_comm, sup_inf_assoc_of_le, sup_comm]
    exact (hloc P hP _ _).2.1 hXX

theorem vd_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : vd h (Formalism.HermitianLatticesTheory.gmap g L) 𝔭 = vd h L 𝔭 := by
  have e : discrIdeal h (Formalism.HermitianLatticesTheory.gmap g L) = discrIdeal h L := by
    unfold discrIdeal
    congr 1
    ext z
    constructor
    · rintro ⟨x, hx, e⟩
      refine ⟨fun i => g.symm (x i), fun i => (Formalism.HermitianLatticesTheory.isomAct_mem_gmap g L _).mp (hx i), ?_⟩
      rw [e]
      congr 1
      ext i j
      exact (SplitBAux.isom_apply (SplitBAux.symm_mem_isom hg) _ _).symm
    · rintro ⟨x, hx, e⟩
      refine ⟨fun i => g (x i), fun i => StabilizerLattices.apply_mem_gmap g (hx i), ?_⟩
      rw [e]
      congr 1
      ext i j
      exact (SplitBAux.isom_apply hg _ _).symm
  unfold vd
  rw [e]

theorem isIntegralLat_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : Formalism.HermitianLatticesTheory.IsIntegralLat h (Formalism.HermitianLatticesTheory.gmap g L) :=
  ((Formalism.HermitianLatticesTheory.isomAct (𝓞 K) K V h g hg L).2.2.1).mpr hLi

theorem exists_of_fibLoc_ne_zero (S : VecSplit h h') {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    {T : Submodule (𝓞 K) V'} (hT : fibLoc S L 𝔭 T ≠ 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, S.x₀ ∈ locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g L) ∧
      locF 𝔭 (S.cut (Formalism.HermitianLatticesTheory.gmap g L)) = locF 𝔭 T := by
  have hne : Nonempty {Λ : Submodule (𝓞 K) V // locF 𝔭 Λ = Λ ∧
      (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = Λ) ∧ S.x₀ ∈ Λ ∧
      S.cut Λ = locF 𝔭 T} := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hT Nat.card_of_isEmpty
  obtain ⟨Λ, -, ⟨g, hg, rfl⟩, hx, hc⟩ := hne
  rw [LocalizedFibreSets.gmap_locF] at hx hc
  exact ⟨g, hg, hx, by rw [← LocalizedFibreSets.cut_locF, hc]⟩

theorem fibLoc_locF (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (T : Submodule (𝓞 K) V') : fibLoc S L 𝔭 (locF 𝔭 T) = fibLoc S L 𝔭 T := by
  unfold fibLoc
  rw [LocF.locF_idem]

theorem fibLoc_congr (S : VecSplit h h') (L : Submodule (𝓞 K) V) {𝔭 : Ideal (𝓞 F)}
    {T T' : Submodule (𝓞 K) V'} (e : locF 𝔭 T = locF 𝔭 T') :
    fibLoc S L 𝔭 T = fibLoc S L 𝔭 T' := by
  rw [← fibLoc_locF S L 𝔭 T, e, fibLoc_locF]

theorem localFactor_localField (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    lamP h (locF 𝔭 L) 𝔭 = lamP h L 𝔭 := by
  have e : alphaL h (locF 𝔭 L) 𝔭 = alphaL h L 𝔭 := by
    unfold alphaL
    congr 1
    ext k
    rw [akCount_locF hF h L 𝔭 h𝔭]
  unfold lamP
  rw [vd_locF hK hF hs hd hL hLi h𝔭, e]

theorem exists_lattice_of_fibLoc_ne_zero (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    {T : Submodule (𝓞 K) V'} (hT : fibLoc S L 𝔭 T ≠ 0) :
    ∃ C : Submodule (𝓞 K) V', Submodule.IsLattice K C ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h' C ∧
      locF 𝔭 C = locF 𝔭 T := by
  obtain ⟨g, hg, -, e⟩ := exists_of_fibLoc_ne_zero S hT
  exact ⟨_, StabilizerLattices.isLattice_cut S (LocalizedFibreSets.isLattice_gmap g hL),
    isIntegralLat_cut S (isIntegralLat_gmap hg hLi), e⟩

theorem exists_lattice_of_fibLoc_ne_zero_good (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0)
    {T : Submodule (𝓞 K) V'} (hT : fibLoc S L 𝔭 T ≠ 0) :
    ∃ C : Submodule (𝓞 K) V', Submodule.IsLattice K C ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h' C ∧
      vd h' C 𝔭 = 0 ∧ locF 𝔭 C = locF 𝔭 T := by
  obtain ⟨g, hg, hx, e⟩ := exists_of_fibLoc_ne_zero S hT
  exact ⟨_, StabilizerLattices.isLattice_cut S (LocalizedFibreSets.isLattice_gmap g hL),
    isIntegralLat_cut S (isIntegralLat_gmap hg hLi),
    vd_cut_eq_zero hK hF hs hd S (LocalizedFibreSets.isLattice_gmap g hL) (isIntegralLat_gmap hg hLi) h𝔭 hn
      (by rw [vd_gmap hg, hvL]) hvn hx, e⟩

theorem exists_unimod_lattice_good (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0) :
    ∃ C : Submodule (𝓞 K) V', Submodule.IsLattice K C ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h' C ∧
      vd h' C 𝔭 = 0 := by
  obtain ⟨P, hP, rfl⟩ := LocalizedFibreSets.exists_max_over (K := K) h𝔭
  have hU := (isUnimodularAt_iff_vd hK hF hs hd hL hLi hP).mpr hvL
  have hx : h S.x₀ S.x₀ ∈ (1 : Submodule (𝓞 K) K) := by
    rw [hn]
    exact Submodule.mem_one.mpr ⟨algebraMap (𝓞 F) (𝓞 K) n, rfl⟩
  obtain ⟨B, hB, hBi, hBU, hxB⟩ := exists_unimod_through hs hd hL hLi hP.isPrime hU hx
  exact ⟨_, StabilizerLattices.isLattice_cut S hB, isIntegralLat_cut S hBi,
    vd_cut_eq_zero hK hF hs hd S hB hBi h𝔭 hn
      ((isUnimodularAt_iff_vd hK hF hs hd hB hBi hP).mp hBU) hvn (LocF.le_locF _ _ hxB)⟩

end Formalism.HermitianLattices.Ext.L3.UnimodularLocalization
