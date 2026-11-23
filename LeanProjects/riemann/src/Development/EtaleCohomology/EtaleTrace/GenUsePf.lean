import Development.EtaleCohomology.EtaleTrace.LCoverCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

lemma genUse_generic_mem {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (x : X) (hx : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

lemma genUse_ne {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) {N : ℕ} (ι : X ⟶ PN k N)
    (v : Fin (N + 1) → X.functionField) (hG : Gen p ι v) (n : ℕ) (hn : 0 < n) (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f.IsHomogeneous n) (x : X) (hx : x ∈ ι ⁻¹ᵁ Proj.basicOpen _ f) : eval₂ (kHom p) v f ≠ 0 :=
  ((hG n hn f ((mem_homogeneousSubmodule _ _).mpr hf)).1).mp (genUse_generic_mem _ x hx)

def GenUseLoc : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → ∀ (n : ℕ), 0 < n → ∀ f : MvPolynomial (Fin (N + 1)) k,
  f.IsHomogeneous n → ∀ x : X, x ∈ ι ⁻¹ᵁ Proj.basicOpen _ f →
  ∀ g : MvPolynomial (Fin (N + 1)) k, g.IsHomogeneous n → eval₂ (kHom p) v g / eval₂ (kHom p) v f ∈ loc X x

def GenUseBack : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → ∀ (n : ℕ), 0 < n → ∀ f : MvPolynomial (Fin (N + 1)) k,
  f.IsHomogeneous n → ∀ x : X, eval₂ (kHom p) v f ≠ 0 →
  (∀ g : MvPolynomial (Fin (N + 1)) k, g.IsHomogeneous n → eval₂ (kHom p) v g / eval₂ (kHom p) v f ∈ loc X x) →
  x ∈ ι ⁻¹ᵁ Proj.basicOpen _ f

def GenUseRangeTo : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → ∀ z : X.functionField, z ∈ (ι.stalkMap (genericPoint X)).hom.range →
  ∃ (n : ℕ) (f g : MvPolynomial (Fin (N + 1)) k), f.IsHomogeneous n ∧ g.IsHomogeneous n ∧
    eval₂ (kHom p) v f ≠ 0 ∧ z = eval₂ (kHom p) v g / eval₂ (kHom p) v f

def GenUseRangeOf : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → ∀ (n : ℕ) (f g : MvPolynomial (Fin (N + 1)) k), f.IsHomogeneous n →
  g.IsHomogeneous n → eval₂ (kHom p) v f ≠ 0 →
  eval₂ (kHom p) v g / eval₂ (kHom p) v f ∈ (ι.stalkMap (genericPoint X)).hom.range

theorem genUseLoc : GenUseLoc := by
  intro k _ X _ p N ι v hG n hn f hf x hx g hg
  have hne := genUse_ne p ι v hG n hn f hf x hx
  have hη := genUse_generic_mem _ x hx
  have hg' : g ∈ homogeneousSubmodule (Fin (N + 1)) k (1 • n) := by
    rw [one_smul]; exact (mem_homogeneousSubmodule _ _).mpr hg
  have key := (hG n hn f ((mem_homogeneousSubmodule _ _).mpr hf)).2 1 g hg' hη
  have : Nonempty (ι ⁻¹ᵁ Proj.basicOpen _ f) := ⟨⟨x, hx⟩⟩
  refine ⟨X.presheaf.germ _ x hx (ι.app _ (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ ((mem_homogeneousSubmodule _ _).mpr hf) 1 g hg'))), ?_⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, eq_div_iff hne]
  rw [pow_one] at key
  exact key

theorem genUseRangeOf_pos {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
    (v : Fin (N + 1) → X.functionField) (hG : Gen p ι v) (n : ℕ) (hn : 0 < n) (f g : MvPolynomial (Fin (N + 1)) k)
    (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n) (hne : eval₂ (kHom p) v f ≠ 0) :
    eval₂ (kHom p) v g / eval₂ (kHom p) v f ∈ (ι.stalkMap (genericPoint X)).hom.range := by
  have hη := ((hG n hn f ((mem_homogeneousSubmodule _ _).mpr hf)).1).mpr hne
  have hg' : g ∈ homogeneousSubmodule (Fin (N + 1)) k (1 • n) := by
    rw [one_smul]; exact (mem_homogeneousSubmodule _ _).mpr hg
  have key := (hG n hn f ((mem_homogeneousSubmodule _ _).mpr hf)).2 1 g hg' hη
  rw [pow_one] at key
  refine ⟨(PN k N).presheaf.germ _ (ι (genericPoint X)) hη (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ ((mem_homogeneousSubmodule _ _).mpr hf) 1 g hg')), ?_⟩
  rw [eq_div_iff hne, ← key]
  erw [Scheme.Hom.germ_stalkMap_apply]

def GenUseNZ : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → ∃ i, v i ≠ 0

theorem genUseNZ : GenUseNZ := by
  intro k _ X _ p N ι v hG
  have hcov : ⨆ i, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top'
    · exact fun i => ⟨1, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i)⟩
    · rw [eq_top_iff]
      rintro a -
      induction a using MvPolynomial.induction_on with
      | C c =>
        have : (C c : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 0 :=
          (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ c)
        exact Subalgebra.algebraMap_mem _ (⟨_, this⟩ : homogeneousSubmodule (Fin (N + 1)) k 0)
      | add a b ha hb => exact Subalgebra.add_mem _ ha hb
      | mul_X a i ha => exact Subalgebra.mul_mem _ ha (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hm : ι (genericPoint X) ∈ (⊤ : (PN k N).Opens) := trivial
  rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, hi⟩ := hm
  refine ⟨i, ?_⟩
  have := ((hG 1 one_pos (MvPolynomial.X i) ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i))).1).mp hi
  simpa using this

theorem genUseRangeOf_of (hZ : GenUseNZ) : GenUseRangeOf := by
  intro k _ X _ p N ι v hG n f g hf hg hne
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨i, hi⟩ := hZ k p N ι v hG
    have h1 : (MvPolynomial.X i * f).IsHomogeneous 1 := by simpa using (isHomogeneous_X k i).mul hf
    have h2 : (MvPolynomial.X i * g).IsHomogeneous 1 := by simpa using (isHomogeneous_X k i).mul hg
    have hne' : eval₂ (kHom p) v (MvPolynomial.X i * f) ≠ 0 := by simp [hi, hne]
    have := genUseRangeOf_pos p N ι v hG 1 one_pos _ _ h1 h2 hne'
    simpa [eval₂_mul, eval₂_X, mul_div_mul_left _ _ hi] using this
  · exact genUseRangeOf_pos p N ι v hG n hn f g hf hg hne

theorem genUseRangeTo : GenUseRangeTo := by
  intro k _ X _ p N ι v hG z hz
  obtain ⟨t, rfl⟩ := hz
  obtain ⟨U, hU, s, rfl⟩ := (PN k N).presheaf.exists_germ_eq t
  obtain ⟨_, ⟨h, rfl⟩, hhη, hhU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Proj.isBasis_basicOpen _)) hU
  have hle : ∀ j, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (GradedRing.proj _ j h) ≤
      Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) h := fun j => by
    rw [Proj.basicOpen_eq_iSup_proj _ h]; exact le_iSup (fun i => Proj.basicOpen _ (GradedRing.proj _ i h)) j
  rw [Proj.basicOpen_eq_iSup_proj, TopologicalSpace.Opens.mem_iSup] at hhη
  obtain ⟨j, hj⟩ := hhη
  obtain ⟨i, hi⟩ := genUseNZ k p N ι v hG
  have hXi : ι (genericPoint X) ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) :=
    ((hG 1 one_pos _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i))).1).mpr (by simpa using hi)
  have hpj : GradedRing.proj (homogeneousSubmodule (Fin (N + 1)) k) j h ∈ homogeneousSubmodule (Fin (N + 1)) k j := by
    rw [GradedRing.proj_apply]; exact SetLike.coe_mem _
  have hfm : MvPolynomial.X i * GradedRing.proj (homogeneousSubmodule (Fin (N + 1)) k) j h ∈
      homogeneousSubmodule (Fin (N + 1)) k (j + 1) := by
    have := (isHomogeneous_X k i).mul ((mem_homogeneousSubmodule _ _).mp hpj)
    exact (mem_homogeneousSubmodule _ _).mpr (by rwa [Nat.add_comm 1 j] at this)
  set f := MvPolynomial.X i * GradedRing.proj (homogeneousSubmodule (Fin (N + 1)) k) j h with hfdef
  have hfη : ι (genericPoint X) ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) f := by
    rw [hfdef, Proj.basicOpen_mul]; exact ⟨hXi, hj⟩
  have hfU : Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) f ≤ U := by
    rw [hfdef, Proj.basicOpen_mul]; exact inf_le_right.trans ((hle j).trans hhU)
  have hfne := ((hG (j + 1) (Nat.succ_pos j) f hfm).1).mp hfη
  rw [← (PN k N).presheaf.germ_res_apply (homOfLE hfU) _ hfη s]
  obtain ⟨a, ha⟩ : ∃ a, Proj.awayToSection _ f a = (PN k N).presheaf.map (homOfLE hfU).op s :=
    ⟨(Proj.basicOpenIsoAway _ f hfm (Nat.succ_pos j)).inv ((PN k N).presheaf.map (homOfLE hfU).op s), by
      rw [← Proj.basicOpenIsoAway_hom _ f hfm (Nat.succ_pos j)]; simp⟩
  obtain ⟨m, g, hg, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hfm a
  have key := (hG (j + 1) (Nat.succ_pos j) f hfm).2 m g hg hfη
  refine ⟨m • (j + 1), f ^ m, g, ?_, (mem_homogeneousSubmodule _ _).mp hg, by rw [eval₂_pow]; exact pow_ne_zero _ hfne, ?_⟩
  · rw [smul_eq_mul, mul_comm]; exact ((mem_homogeneousSubmodule _ _).mp hfm).pow m
  rw [← ha]
  erw [Scheme.Hom.germ_stalkMap_apply]
  rw [eval₂_pow, eq_div_iff (pow_ne_zero _ hfne)]
  exact key

theorem GenUse_of (hB : GenUseBack) : GenUse := by
  have hT := genUseRangeTo
  have hL := genUseLoc
  have hO := genUseRangeOf_of genUseNZ
  intro k _ X _ p N ι v hG
  refine ⟨fun n hn f hf x => ⟨fun hx => ⟨genUse_ne p ι v hG n hn f hf x hx, hL k p N ι v hG n hn f hf x hx⟩,
    fun h => hB k p N ι v hG n hn f hf x h.1 h.2⟩, fun z => ⟨hT k p N ι v hG z, ?_⟩⟩
  rintro ⟨n, f, g, hf, hg, hne, rfl⟩
  exact hO k p N ι v hG n f g hf hg hne

end LateralTheory.EtaleTrace.Cov
