import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactSpaceDefiniteUnitaryInfinitePoints
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem eq_one_of_fin_inf {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {x : UA E a}
    (hf : x ∈ finU E a) (hi : x ∈ infU E a) : x = 1 := by
  have h1 : Matrix.GeneralLinearGroup.map (pInf E) x.1 = 1 := hf
  have h2 : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hi
  exact Subtype.ext (ga_ext (by rw [h1]; simp) (by rw [h2]; simp))

private theorem cLoc_of_inf {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
    (w : HeightOneSpectrum (𝓞 E)) {x : UA E a} (hx : x ∈ infU E a) : cLoc w x = 1 := by
  have h2 : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
  have e : cLoc w x = Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) x.1) := by
    ext i j
    rfl
  rw [e, h2, map_one]

private theorem conj_form {G : Type} [Group G] {s j g g' γ x c : G} (hj : j * g' = g' * j) (hj2 : j * g = g * j)
    (hxg : g * x = x * g) (hxj : j * x = x * j) (h : s * j * g' = γ * (s * j * g) * x * c) :
    γ = s * g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ * s⁻¹ := by
  have h0 : γ * (s * j * g) = s * j * g' * c⁻¹ * x⁻¹ := by
    rw [h]; group
  have h1 : γ = s * j * g' * c⁻¹ * x⁻¹ * (s * j * g)⁻¹ := eq_mul_inv_of_mul_eq h0
  have hc : Commute x (g⁻¹ * j⁻¹) :=
    (Commute.inv_right (show Commute x g from hxg.symm)).mul_right (Commute.inv_right (show Commute x j from hxj.symm))
  have hq : x⁻¹ * (g⁻¹ * j⁻¹) = g⁻¹ * j⁻¹ * x⁻¹ := (hc.inv_left).eq
  have hq2 : g⁻¹ * j⁻¹ = j⁻¹ * g⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hj2]
  calc γ = s * (j * g') * c⁻¹ * (x⁻¹ * (g⁻¹ * j⁻¹)) * s⁻¹ := by rw [h1]; group
    _ = s * (g' * j) * c⁻¹ * (j⁻¹ * g⁻¹ * x⁻¹) * s⁻¹ := by rw [hj, hq, hq2]
    _ = s * g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ * s⁻¹ := by group

theorem UpperTheory.Gal.Gen.sep_pf :
    UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.LocComm → UpperTheory.Gal.Gen.RatFin → UpperTheory.Gal.Gen.Sep := by
  intro hLev hComm hRat E _ _ _ a w₀ hs K hK J hJ S T hT hinj
  classical
  haveI := GlobalTheory.InfUCompact.compactSpace_infU E a
  have hI : IsCompact (infU E a : Set (UA E a)) := isCompact_iff_compactSpace.2 inferInstance
  obtain ⟨hL0, hmem0, -, -, -, -⟩ := hLev E a w₀ hs K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  have hC0 : IsCompact (lev K w₀ (J 0) : Set (UA E a)) := hL0.compact

  let P : UA E a × UA E a × UA E a × UA E a × UA E a → UA E a :=
    fun q => q.1 * q.2.2.1 * q.2.2.2.1 * q.2.1⁻¹ * q.2.2.2.2 * q.1⁻¹
  let D : Set (UA E a × UA E a × UA E a × UA E a × UA E a) :=
    (S : Set (UA E a)) ×ˢ (T : Set (UA E a)) ×ˢ (T : Set (UA E a)) ×ˢ
      (lev K w₀ (J 0) : Set (UA E a)) ×ˢ (infU E a : Set (UA E a))
  have hD : IsCompact D :=
    S.finite_toSet.isCompact.prod (T.finite_toSet.isCompact.prod (T.finite_toSet.isCompact.prod (hC0.prod hI)))
  have hP : Continuous P := by
    simp only [P]
    fun_prop
  have hR : (P '' D ∩ (ratU E a : Set (UA E a))).Finite := (hRat E a).1 _ (hD.image hP)

  let Y : UA E a × UA E a → GL (Fin a) (w₀.adicCompletion E) := fun q => cLoc w₀ (q.1⁻¹ * q.2 * q.1)
  let F : Set (GL (Fin a) (w₀.adicCompletion E)) :=
    Y '' ((S : Set (UA E a)) ×ˢ ((P '' D ∩ (ratU E a : Set (UA E a))) \ {1}))
  have hF : F.Finite := (S.finite_toSet.prod (hR.subset Set.diff_subset)).image _
  have hne : ∀ y ∈ F, y ≠ 1 := by
    rintro _ ⟨⟨s, γ⟩, ⟨-, ⟨-, hγ⟩, hγ1⟩, rfl⟩ e
    refine hγ1 ((hRat E a).2 w₀ γ hγ ?_)
    simp only [Y, map_mul, map_inv] at e
    have := congrArg (fun t => cLoc w₀ s * t * (cLoc w₀ s)⁻¹) e
    simpa [mul_assoc] using this
  have ev : ∀ y ∈ F, ∀ᶠ n in Filter.atTop, y ∉ J n := by
    intro y hy
    obtain ⟨n, hn⟩ := hJ.small {y}ᶜ (isOpen_compl_singleton.mem_nhds (by simpa using (hne y hy).symm))
    filter_upwards [Filter.eventually_ge_atTop n] with m hm hym
    exact hn (hJ.anti hm hym) rfl
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 ((Set.Finite.eventually_all hF).2 ev)
  refine ⟨n₀, fun n hn y g hg g' hg' γ hγ x hx c hc h => ?_⟩
  obtain ⟨⟨s, hsS⟩, ⟨j, hjL, hjJ⟩⟩ := y
  simp only at h
  obtain ⟨hLn, -, hcl, hck, -, hmono⟩ := hLev E a w₀ hs K hK (J n) (hJ.isOpen n) (hJ.compact n)
  have hcJ : cLoc w₀ c ∈ J n := hcl c hc
  have hcC0 : c ∈ lev K w₀ (J 0) := hmono (J 0) c hc (hJ.anti (Nat.zero_le n) hcJ)
  have hjC0 : j ∈ lev K w₀ (J 0) := (hmem0 j).2 ⟨1, K.one_mem, j, hjL, hjJ, (one_mul j).symm⟩
  have hgF : g ∈ finU E a := (hT g hg).1
  have hgF' : g' ∈ finU E a := (hT g' hg').1
  have hcF : c ∈ finU E a := hLn.fin hc
  have hjF : j ∈ finU E a := (Subgroup.mem_inf.1 hjL).1
  have hg1 : cLoc w₀ g = 1 := (hT g hg).2 w₀ (not_apart_self w₀)
  have hg1' : cLoc w₀ g' = 1 := (hT g' hg').2 w₀ (not_apart_self w₀)
  have hx1 : cLoc w₀ x = 1 := cLoc_of_inf w₀ hx
  have hγeq : γ = s * g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ * s⁻¹ :=
    conj_form (hComm E a w₀ j g' hjL (hT g' hg').2) (hComm E a w₀ j g hjL (hT g hg).2)
      (fin_mul_inf hgF hx) (fin_mul_inf hjF hx) h
  have hcloc : cLoc w₀ (s⁻¹ * γ * s) = cLoc w₀ j * (cLoc w₀ c)⁻¹ * (cLoc w₀ j)⁻¹ := by
    have e : s⁻¹ * γ * s = g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ := by
      rw [hγeq]; group
    rw [e]
    simp only [map_mul, map_inv, hg1, hg1', hx1, inv_one, one_mul, mul_one]
  have hin : cLoc w₀ (s⁻¹ * γ * s) ∈ J n := by
    rw [hcloc]
    exact hJ.normal n _ hjJ _ (inv_mem hcJ)
  have hγ1 : γ = 1 := by
    by_contra hne'
    have hγZ : γ ∈ P '' D :=
      ⟨(s, g, g', j * c⁻¹ * j⁻¹, x⁻¹),
        ⟨hsS, hg, hg', mul_mem (mul_mem hjC0 (inv_mem hcC0)) (inv_mem hjC0), inv_mem hx⟩, hγeq.symm⟩
    exact hn₀ n hn _ ⟨(s, γ), ⟨hsS, ⟨hγZ, hγ⟩, hne'⟩, rfl⟩ hin
  subst hγ1
  have h2 : g' = g * x * c := by
    have : s * j * g' = s * j * (g * x * c) := by
      rw [h]; group
    exact mul_left_cancel this
  have hxF : x ∈ finU E a := by
    have e : x = g⁻¹ * g' * c⁻¹ := by
      rw [h2]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hgF) hgF') (inv_mem hcF)
  have hxe : x = 1 := eq_one_of_fin_inf hxF hx
  subst hxe
  have h3 : g⁻¹ * g' = c := by
    rw [h2]; group
  have hcK : c ∈ K := hck c hc (by
    rw [← h3, map_mul, map_inv, hg1, hg1', inv_one, one_mul])
  exact hinj g hg g' hg' (h3 ▸ hcK)
