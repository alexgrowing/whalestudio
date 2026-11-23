import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSchemeGrpObjOfMonoFactorStatement
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SubRepPull
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsFiniteEtaleRepresentingClopenSubschemes
import Development.AutomorphicArithmetic.CommutativeAlgebra.ClopenCondOfIsClosedSubgroupLocus
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLiftOfClosedSubgroupLocus
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClosedLocusOfTorsionAbelianScheme

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace UpperTheory.SubRep

private theorem range_pre {S : Scheme.{0}} {T' Z Z' : Over S} (m : T' ⟶ Z) (r : Z ⟶ Z') (U : Z'.left.Opens) :
    Set.range m.left ⊆ (r.left ⁻¹ᵁ U : Z.left.Opens) ↔ Set.range (m ≫ r).left ⊆ U := by
  rw [Over.comp_left]
  simp only [Set.range_subset_iff]
  rfl

private theorem opens_le {S : Scheme.{0}} {X G : Over S} {O O' : (X ⊗ G).left.Opens}
    (h : ∀ (T' : Over S) (t : T' ⟶ X) (a : T' ⟶ G),
      Set.range (lift t a).left ⊆ O → Set.range (lift t a).left ⊆ O') : O ≤ O' := by
  intro x hx
  have h' := h (Over.mk (O.ι ≫ (X ⊗ G).hom)) (Over.homMk O.ι ≫ fst X G) (Over.homMk O.ι ≫ snd X G)
  rw [lift_comp_fst_snd] at h'
  exact h' (by exact (Scheme.Opens.range_ι O).le) (by exact (Scheme.Opens.range_ι O).ge hx)

private theorem opens_ext {S : Scheme.{0}} {X G : Over S} {O O' : (X ⊗ G).left.Opens}
    (h : ∀ (T' : Over S) (t : T' ⟶ X) (a : T' ⟶ G),
      Set.range (lift t a).left ⊆ O ↔ Set.range (lift t a).left ⊆ O') : O = O' :=
  le_antisymm (opens_le fun T' t a => (h T' t a).1) (opens_le fun T' t a => (h T' t a).2)

private theorem core {S : Scheme.{0}} [IsLocallyNoetherian S] (A G : Over S) [GrpObj A] [IsCommMonObj A]
    [GrpObj G] (inc : G ⟶ A) (hm : Mono inc) (hh : IsMonHom inc) [IsFinite G.hom] [Etale G.hom] (k : ℕ)
    (hu : IsUnit (k : Γ(S, ⊤)))
    (htor : ∀ (T' : Over S) (a : T' ⟶ A), a ^ k = 1 → ∃ b : T' ⟶ G, b ≫ inc = a)
    (hk : ∀ (T' : Over S) (b : T' ⟶ G), (b ≫ inc) ^ k = 1) :
    ∃ (Y : Over S), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (A₀ : Over Y.left) [GrpObj A₀] [IsCommMonObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (H : Over Y.left) (_ : GrpObj H) (i : H ⟶ A₀), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Etale H.hom ∧ i ^ k = 1 ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] (f : A₁ ⟶ B₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsMonHom f → (∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ f = 1 → g ^ k = 1) → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ f = 1 ↔ ∃ h : T'.left ⟶ H.left, h ≫ H.hom = T'.hom ≫ y ∧ h ≫ i.left ≫ φ₀ = g.left ≫ φ₁ := by
  haveI := hm
  haveI := hh
  obtain ⟨Y₀, U, hY₀f, hY₀e, hU, hrep⟩ := UpperTheory.Cb.exists_finite_etale_representing_clopen_subschemes S G inferInstance inferInstance
  obtain ⟨U₁, hU₁, hP⟩ := UpperTheory.clopenCond_of_isClosed_subgroupLocus G Y₀ U hU
  haveI := hY₀f
  haveI := hY₀e
  obtain ⟨Y, i₀, hYf, hYe, hi₀, hsub⟩ := GlobalTheory.LevCover.exists_sub U₁ hU₁
  haveI := hi₀
  obtain ⟨U₂, hU₂def⟩ : ∃ U₂ : (Y ⊗ G).left.Opens, U₂ = (i₀ ▷ G).left ⁻¹ᵁ U := ⟨_, rfl⟩
  have hU₂ : IsClosed (U₂ : Set (Y ⊗ G).left) := by
    rw [hU₂def]
    exact IsClosed.preimage (i₀ ▷ G).left.continuous hU
  have hlift : ∀ {T' : Over S} (t : T' ⟶ Y) (a : T' ⟶ G),
      Set.range (lift t a).left ⊆ ↑U₂ ↔ Set.range (lift (t ≫ i₀) a).left ⊆ ↑U := by
    intro T' t a
    rw [hU₂def, range_pre, lift_whiskerRight]
  have hcond : ∀ (T' : Over S) (t : T' ⟶ Y),
      Set.range (lift t (1 : T' ⟶ G)).left ⊆ ↑U₂ ∧
      ∀ (a b : T' ⟶ G), Set.range (lift t a).left ⊆ ↑U₂ → Set.range (lift t b).left ⊆ ↑U₂ →
        Set.range (lift t (a * b⁻¹)).left ⊆ ↑U₂ := by
    intro T' t
    have hp := (hP T' (t ≫ i₀)).2 ((hsub T' (t ≫ i₀)).2 ⟨t, rfl⟩) T' (𝟙 T')
    simp only [Category.id_comp] at hp
    simp only [hlift]
    exact hp
  refine ⟨Y, hYf, hYe, ?_⟩
  intro A₀ _ _ φ₀ hpb
  obtain ⟨H, instH, j, hjm, hjmono, hHf, hHe, hj⟩ :=
    UpperTheory.exists_lift_of_closed_subgroup_locus Y A G inc U₂ hm hh hU₂ hcond A₀ φ₀ hpb
  obtain ⟨aj, haj1, -⟩ :=
    (hj (Over.mk (H.hom ≫ Y.hom)) (Over.homMk H.hom) j).1 ⟨𝟙 _, Category.id_comp _⟩
  have PW : ∀ (T' : Over S) (z : T' ⟶ Y) (a : T' ⟶ G), Set.range (lift z a).left ⊆ ↑U₂ ↔
      ∃ h : T'.left ⟶ H.left, h ≫ H.hom = z.left ∧ h ≫ j.left ≫ φ₀ = a.left ≫ inc.left := by
    intro T' z a
    obtain ⟨gA, hgA, -⟩ := UpperTheory.SubRep.pull_existsUnique hpb T' z.left (Over.w z) (a ≫ inc)
    rw [Over.comp_left] at hgA
    have H1 := hj T' z gA
    constructor
    · intro hr
      obtain ⟨hh', hhj⟩ := H1.2 ⟨a, hgA.symm, hr⟩
      refine ⟨hh'.left, Over.w hh', ?_⟩
      rw [← hgA, ← hhj, Over.comp_left, Category.assoc]
    · rintro ⟨h, hH, hφ⟩
      obtain ⟨a', ha', hr⟩ := H1.1 ⟨Over.homMk h hH, UpperTheory.SubRep.pull_ext hpb
        (by
          rw [Over.comp_left]
          show (h ≫ j.left) ≫ φ₀ = gA.left ≫ φ₀
          rw [Category.assoc, hφ, hgA])⟩
      have e : a' = a := by
        have e' : a' ≫ inc = a ≫ inc := by
          ext
          rw [Over.comp_left, Over.comp_left, ha', hgA]
        exact (cancel_mono inc).1 e'
      rw [← e]
      exact hr
  refine ⟨H, instH, j, hjm, hjmono, hHf, hHe, ?_, ?_⟩
  · apply UpperTheory.SubRep.pull_ext hpb
    have e1 := UpperTheory.SubRep.pull_pow hpb (Over.mk (H.hom ≫ Y.hom)) H.hom rfl (g := j)
      (a := aj ≫ inc) (by rw [Over.comp_left, haj1]) k
    have e2 := UpperTheory.SubRep.pull_one hpb (Over.mk (H.hom ≫ Y.hom)) H.hom rfl
    refine e1.trans ?_
    rw [hk]
    exact e2.symm
  · intro T x A₁ _ _ φ₁ B₁ _ f hpb1 hB hf hker
    haveI := hf
    have huT : IsUnit ((k : ℕ) : Γ(T, ⊤)) := by
      have h2 := hu.map (Scheme.Hom.appTop x).hom
      rwa [map_natCast] at h2
    obtain ⟨V, hV, hVp⟩ := UpperTheory.exists_closed_locus_of_torsion_abelianScheme x A G inc k hk huT A₁ φ₁ B₁ f hpb1 hB hf
    obtain ⟨y₀, hy₀, hy₀u⟩ := hrep (Over.mk x) V hV
    have PW2 : ∀ (y₁' : Over.mk x ⟶ Y) (T' : Over S) (t : T' ⟶ Over.mk x) (a : T' ⟶ G),
        Set.range (lift t a).left ⊆ ↑(((y₁' ≫ i₀) ▷ G).left ⁻¹ᵁ U) ↔
          ∃ h : T'.left ⟶ H.left, h ≫ H.hom = t.left ≫ y₁'.left ∧
            h ≫ j.left ≫ φ₀ = a.left ≫ inc.left := by
      intro y₁' T' t a
      rw [range_pre, lift_whiskerRight, ← Category.assoc, ← hlift, PW, Over.comp_left]
    have hwt : ∀ {T' : Over S} (t : T' ⟶ Over.mk x), t.left ≫ x = T'.hom := fun t => Over.w t
    have hyU : ∀ (T' : Over S) (t : T' ⟶ Over.mk x) (a : T' ⟶ G),
        Set.range (lift (t ≫ y₀) a).left ⊆ ↑U ↔ Set.range (lift t a).left ⊆ ↑V := by
      intro T' t a
      rw [← hy₀, range_pre, lift_whiskerRight]
    have hPy : ∀ (T' : Over S) (t : T' ⟶ Over.mk x),
        Set.range (lift (t ≫ y₀) (1 : T' ⟶ G)).left ⊆ ↑U ∧
        ∀ (a b : T' ⟶ G), Set.range (lift (t ≫ y₀) a).left ⊆ ↑U →
          Set.range (lift (t ≫ y₀) b).left ⊆ ↑U → Set.range (lift (t ≫ y₀) (a * b⁻¹)).left ⊆ ↑U := by
      intro T' t
      simp only [hyU]
      refine ⟨?_, ?_⟩
      · rw [← hVp T' t 1 1 ?_]
        · exact MonObj.one_comp f
        · rw [UpperTheory.SubRep.pull_one hpb1 T' t.left (hwt t), ← Over.comp_left, MonObj.one_comp inc]
      · intro a b ha hb
        obtain ⟨ga, hga0, -⟩ := UpperTheory.SubRep.pull_existsUnique hpb1 T' t.left (hwt t) (a ≫ inc)
        obtain ⟨gb, hgb0, -⟩ := UpperTheory.SubRep.pull_existsUnique hpb1 T' t.left (hwt t) (b ≫ inc)
        have hga : ga.left ≫ φ₁ = a.left ≫ inc.left := by rw [hga0, Over.comp_left]
        have hgb : gb.left ≫ φ₁ = b.left ≫ inc.left := by rw [hgb0, Over.comp_left]
        have hga' := (hVp T' t a ga hga).2 ha
        have hgb' := (hVp T' t b gb hgb).2 hb
        rw [← hVp T' t (a * b⁻¹) (ga * gb⁻¹) ?_]
        · rw [MonObj.mul_comp, GrpObj.inv_comp, hga', hgb', inv_one, _root_.mul_one]
        · rw [UpperTheory.SubRep.pull_mul hpb1 T' t.left (hwt t) hga0
            (UpperTheory.SubRep.pull_inv hpb1 T' t.left (hwt t) hgb0), ← Over.comp_left,
            MonObj.mul_comp, GrpObj.inv_comp]
    obtain ⟨y₁, hy₁⟩ := (hsub (Over.mk x) y₀).1 ((hP (Over.mk x) y₀).1 hPy)
    have hy₁x : y₁.left ≫ Y.hom = x := Over.w y₁
    refine ⟨y₁.left, ⟨hy₁x, ?_⟩, ?_⟩
    · intro T' g
      have hpre : ((y₁ ≫ i₀) ▷ G).left ⁻¹ᵁ U = V := by rw [hy₁, hy₀]
      have chain : ∀ a : Over.mk (T'.hom ≫ x) ⟶ G, g.left ≫ φ₁ = a.left ≫ inc.left →
          (g ≫ f = 1 ↔ ∃ h : T'.left ⟶ H.left, h ≫ H.hom = T'.hom ≫ y₁.left ∧
            h ≫ j.left ≫ φ₀ = g.left ≫ φ₁) := by
        intro a ha
        rw [ha]
        exact (hVp (Over.mk (T'.hom ≫ x)) (Over.homMk T'.hom) a g ha).trans
          (by rw [← hpre]; exact PW2 y₁ (Over.mk (T'.hom ≫ x)) (Over.homMk T'.hom) a)
      constructor
      · intro hg1
        have htk : g ^ k = 1 := hker T' g hg1
        have w : (g.left ≫ φ₁) ≫ A.hom = (Over.mk (T'.hom ≫ x)).hom := by
          rw [Category.assoc, hpb1.1.w, ← Category.assoc, Over.w g]
          rfl
        have ha₁k : (Over.homMk (g.left ≫ φ₁) w : Over.mk (T'.hom ≫ x) ⟶ A) ^ k = 1 := by
          ext
          have e1 := UpperTheory.SubRep.pull_pow hpb1 (Over.mk (T'.hom ≫ x)) T'.hom rfl (g := g)
            (a := Over.homMk (g.left ≫ φ₁) w) rfl k
          have e2 := UpperTheory.SubRep.pull_one hpb1 (Over.mk (T'.hom ≫ x)) T'.hom rfl
          refine e1.symm.trans ?_
          rw [htk]
          exact e2
        obtain ⟨b, hb⟩ := htor _ _ ha₁k
        have hb' : g.left ≫ φ₁ = b.left ≫ inc.left := by
          rw [← Over.comp_left, hb]
          rfl
        exact (chain b hb').1 hg1
      · rintro ⟨h, hH, hφ⟩
        have w : (h ≫ aj.left) ≫ G.hom = (Over.mk (T'.hom ≫ x)).hom := by
          rw [Category.assoc, Over.w aj]
          show h ≫ H.hom ≫ Y.hom = T'.hom ≫ x
          rw [← Category.assoc, hH, Category.assoc, hy₁x]
        have ha : g.left ≫ φ₁ = (Over.homMk (h ≫ aj.left) w : Over.mk (T'.hom ≫ x) ⟶ G).left ≫ inc.left := by
          rw [← hφ]
          show h ≫ j.left ≫ φ₀ = (h ≫ aj.left) ≫ inc.left
          rw [Category.assoc, haj1]
        exact (chain _ ha).2 ⟨h, hH, hφ⟩
    · rintro y' ⟨hy'x, hQ⟩
      have hpre' : ((Over.homMk y' hy'x ≫ i₀ : Over.mk x ⟶ Y₀) ▷ G).left ⁻¹ᵁ U = V := by
        apply opens_ext
        intro T' t a
        rw [PW2 (Over.homMk y' hy'x) T' t a]
        obtain ⟨ga, hga0, -⟩ := UpperTheory.SubRep.pull_existsUnique hpb1 T' t.left (hwt t) (a ≫ inc)
        have hga : ga.left ≫ φ₁ = a.left ≫ inc.left := by rw [hga0, Over.comp_left]
        rw [← hVp T' t a ga hga, hQ (Over.mk t.left) ga, hga]
        rfl
      have e1 : (Over.homMk y' hy'x : Over.mk x ⟶ Y) ≫ i₀ = y₀ := hy₀u _ hpre'
      have e2 : (Over.homMk y' hy'x : Over.mk x ⟶ Y) = y₁ := by
        rw [← cancel_mono i₀, e1, hy₁]
      rw [← e2]
      rfl

end UpperTheory.SubRep

theorem UpperTheory.Cb.exists_finite_etale_trivializing_torsion_abelianScheme :
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → ∃ (Y : Over S), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (A₀ : Over Y.left) [GrpObj A₀] [IsCommMonObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (H : Over Y.left) (_ : GrpObj H) (i : H ⟶ A₀), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Etale H.hom ∧ i ^ k = 1 ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] (f : A₁ ⟶ B₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsMonHom f → (∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ f = 1 → g ^ k = 1) → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ f = 1 ↔ ∃ h : T'.left ⟶ H.left, h ≫ H.hom = T'.hom ≫ y ∧ h ≫ i.left ≫ φ₀ = g.left ≫ φ₁ := by
  intro S _ A _ _ k hA hk0 hu
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A hu
  have hpow : ∀ (T' : Over S) (b : T' ⟶ torsion A k), (b ≫ torsion.ι A k) ^ k = 1 := by
    intro T' b
    rw [← comp_pow, GlobalTheory.LatticeTorsion.torsionι_pow_eq_one]
    simp
  have hmono : Mono (torsion.ι A k) := by
    constructor
    intro Z g h e
    exact (GlobalTheory.LatticeTorsion.existsUnique_torsion A k (g ≫ torsion.ι A k) (hpow _ g)).unique rfl e.symm
  have hmul : ∃ m, m ≫ torsion.ι A k = (torsion.ι A k ⊗ₘ torsion.ι A k) ≫ μ := by
    refine (GlobalTheory.LatticeTorsion.existsUnique_torsion A k _ ?_).exists
    have e : (torsion.ι A k ⊗ₘ torsion.ι A k) ≫ μ
        = fst _ _ ≫ torsion.ι A k * snd _ _ ≫ torsion.ι A k := by
      rw [Hom.mul_def]
      simp
    rw [e, mul_pow, hpow, hpow]
    simp
  have hone : ∃ e, e ≫ torsion.ι A k = η := by
    refine (GlobalTheory.LatticeTorsion.existsUnique_torsion A k _ ?_).exists
    have e : (η : 𝟙_ (Over S) ⟶ A) = 1 := by
      rw [Hom.one_def]
      simp
    rw [e, one_pow]
  have hinv : ∃ v, v ≫ torsion.ι A k = torsion.ι A k ≫ ι := by
    refine (GlobalTheory.LatticeTorsion.existsUnique_torsion A k _ ?_).exists
    rw [← Hom.inv_def, inv_pow, GlobalTheory.LatticeTorsion.torsionι_pow_eq_one, inv_one]
  obtain ⟨inst, hmon⟩ := GlobalTheory.T.exists_grpObj_isMonHom_of_mono_factor S A (torsion A k) (torsion.ι A k) hmono hmul hone hinv
  haveI := hfin
  haveI := het
  exact UpperTheory.SubRep.core A (torsion A k) (torsion.ι A k) hmono hmon k hu
    (fun T' a ha => (GlobalTheory.LatticeTorsion.existsUnique_torsion A k a ha).exists)
    (fun T' b => hpow T' b)
