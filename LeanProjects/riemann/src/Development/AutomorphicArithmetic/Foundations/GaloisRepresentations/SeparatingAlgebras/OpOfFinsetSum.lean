import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem opOf_finset_sum {Γ V ι : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V)
    (f : Γ →₀ ℂ) (I : Finset ι) (u : ι → V) : opOf ρ f (∑ i ∈ I, u i) = ∑ i ∈ I, opOf ρ f (u i) := by
  unfold opOf
  simp only [Finsupp.sum, map_sum, Finset.smul_sum]
  exact Finset.sum_comm

private theorem finite_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B : Subgroup G}
    (hA : IsCompact (A : Set G)) (hB : IsOpen (B : Set G)) : Finite (A ⧸ B.subgroupOf A) := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.1 hA
  have ho : IsOpen ((B.subgroupOf A : Subgroup A) : Set A) := hB.preimage continuous_subtype_val
  exact Subgroup.quotient_finite_of_isOpen _ ho

private theorem bound_arith {M s ε c t : ℝ} (hM : 0 ≤ M) (hs : 0 ≤ s) (hε : 0 < ε) (hc : 0 ≤ c) (ht : t ≤ ε / (M * s + 1)) :
    M * (s * c) * t ≤ ε * c := by
  have hd : 0 < M * s + 1 := by positivity
  have h1 : M * s * t ≤ ε := by
    have hMs : 0 ≤ M * s := by positivity
    calc M * s * t ≤ M * s * (ε / (M * s + 1)) := mul_le_mul_of_nonneg_left ht hMs
      _ = ε * (M * s / (M * s + 1)) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left ((div_le_one hd).2 (by linarith)) hε.le
      _ = ε := mul_one ε
  calc M * (s * c) * t = (M * s * t) * c := by ring
    _ ≤ ε * c := mul_le_mul_of_nonneg_right h1 hc

theorem UpperTheory.Gal.Gen.count_pf :
    UpperTheory.Gal.Gen.CountCore → UpperTheory.Gal.Gen.Cover → UpperTheory.Gal.Gen.Sep → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.Count := by
  intro hCore hCover hSep hPart E _ _ _ a w₀ hs K hK J hJ W B hB ε hε
  obtain ⟨M, hM0, hM⟩ := hCore E a W
  obtain ⟨S, hS⟩ := hCover E a w₀ hs K hK J hJ
  have hδ : 0 < ε / (M * (S.card : ℝ) + 1) := by positivity
  obtain ⟨h, h1, h2, h3, h4⟩ := hB _ hδ
  obtain ⟨n₀, hn₀⟩ := hSep E a w₀ hs K hK J hJ S h.support h1 h2
  refine ⟨n₀, fun n hn => ?_⟩
  haveI : Finite (J 0 ⧸ (J n).subgroupOf (J 0)) := finite_quot (hJ.compact 0) (hJ.isOpen n)
  letI : Fintype (J 0 ⧸ (J n).subgroupOf (J 0)) := Fintype.ofFinite _
  obtain ⟨r, hr, hcov⟩ := hS n
  have hsep : Separates (lev K w₀ (J n)) (fun y : S × (J 0 ⧸ (J n).subgroupOf (J 0)) => y.1.1 * r y.2) h.support :=
    fun y g hg g' hg' γ hγ x hx c hc e =>
      hn₀ n hn (y.1, ⟨r y.2, hr y.2⟩) g hg g' hg' γ hγ x hx c hc e
  have hfix : ∀ f ∈ part W (lev K w₀ (J n)) B, ∀ v, opOf (RU E a) h (f.1 v) = f.1 v := by
    intro f hf v
    obtain ⟨I, F, hF, rfl⟩ := (hPart E a W (lev K w₀ (J n)) B).2.2.2.2 f hf
    have e : (∑ π ∈ I, F π : algForms W).1 v = ∑ π ∈ I, (F π).1 v := by
      simp [Submodule.coe_sum, LinearMap.sum_apply]
    rw [e, opOf_finset_sum]
    refine Finset.sum_congr rfl fun π hπ => ?_
    obtain ⟨hP, hfin, hfx, -⟩ := hF π hπ
    refine h4 π.V π.isAut hP _ (AutSub.mem_finPart.1 hfin v) fun x hx => funext fun g => ?_
    rw [RU_apply]
    exact hfx x ((le_sup_left : K ≤ lev K w₀ (J n)) hx) v g
  obtain ⟨hfd, hle⟩ := hM (lev K w₀ (J n)) _ _ hcov h hsep (part W (lev K w₀ (J n)) B)
    (hPart E a W (lev K w₀ (J n)) B).2.1 hfix
  refine ⟨hfd, hle.trans ?_⟩
  have hcard : (Fintype.card (S × (J 0 ⧸ (J n).subgroupOf (J 0))) : ℝ) =
      (S.card : ℝ) * (Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_coe, Nat.card_eq_fintype_card]
    push_cast
    rfl
  rw [hcard]
  exact bound_arith hM0 (Nat.cast_nonneg _) hε (Nat.cast_nonneg _) h3
