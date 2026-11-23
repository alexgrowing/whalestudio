import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinCoordsArithVar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsJoinModelDominatesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNormalisationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalIsoOfIntegrallyClosedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsCompatibleAlongMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreRefineLineBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGenericFibreOfSnc
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalOfTranscendenceDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralOverLocalizationScaled
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegrallyClosedQuotientOfMemMinimalPrimes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeModel

section Normal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem exists_div_of_tie {κ : Type} {x : κ → Ω} (ht : CoordTie ℤ ξ x) {c : κ} {q : Cpt ξ} (hc : InChart ξ x c q)
    (a : Ω) : ∃ u ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ v ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), v ≠ 0 ∧ a = u / v := by
  have hg : InChart ξ x c (TieArith.genCpt ξ) :=
    ⟨hc.1, fun c' => (RegAtMono.regAt_mono X Ω ξ q (TieArith.genCpt ξ) q.2).1 (hc.2 c')⟩
  obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ _ ht c (TieArith.genCpt ξ) hg a).1
    (TieArith.mem_regAt_genCpt ξ ht.gen a)
  exact ⟨s * a, hsa, s, hs, hu.1, by field_simp [hu.1]⟩

variable [CharZero Ω]

theorem exists_trdeg_eq {κ : Type} [Finite κ] {x : κ → Ω} (ht : CoordTie ℤ ξ x) :
    ∃ d : ℕ, Algebra.trdeg ℤ Ω = d := by
  obtain ⟨c, hc⟩ := ht.cover (TieArith.genCpt ξ)
  set s : Set Ω := Set.range fun j => x j / x c with hs
  haveI : Algebra.IsAlgebraic (Algebra.adjoin ℤ s) Ω := by
    refine ⟨fun a => ?_⟩
    obtain ⟨u, hu, v, hv, hv0, rfl⟩ := exists_div_of_tie ht hc a
    have h1 : IsAlgebraic (Algebra.adjoin ℤ s) u := isAlgebraic_algebraMap (⟨u, hu⟩ : Algebra.adjoin ℤ s)
    have h2 : IsAlgebraic (Algebra.adjoin ℤ s) v := isAlgebraic_algebraMap (⟨v, hv⟩ : Algebra.adjoin ℤ s)
    rw [div_eq_mul_inv]
    exact h1.mul h2.inv
  obtain ⟨t, hts, hb⟩ := exists_isTranscendenceBasis_subset (R := ℤ) s
  have hfin : t.Finite := (Set.finite_range _).subset hts
  haveI := hfin.to_subtype
  haveI := Fintype.ofFinite t
  exact ⟨Fintype.card t, by rw [← hb.cardinalMk_eq_trdeg, Cardinal.mk_fintype]⟩

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem mem_regAt_of_isIntegral (ht : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hs : SmoothGenericFibreM y) (q : Cpt ξ) (hq : q ∈ genFib ξ) (a : Ω)
    (ha : IsIntegral (regAt ξ q) a) : a ∈ regAt ξ q := by
  classical
  obtain ⟨c, hc⟩ := ht.cover q
  have hne : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc.1) k (Finset.mem_univ k)
  set A : Subalgebra ℚ Ω := Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) with hA
  haveI : Algebra.Smooth ℚ A := hs c hne
  let R : Subalgebra ℚ Ω :=
    { (regAt ξ q) with
      algebraMap_mem' := fun r => by
        have e : algebraMap ℚ Ω r = (r.num : Ω) * ((r.den : ℕ) : Ω)⁻¹ := by
          rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
        rw [e]
        exact mul_mem (intCast_mem _ _) (hq r.den r.den_pos).2.2 }
  have hAR : ∀ b ∈ A, b ∈ regAt ξ q := by
    have : A ≤ R := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨⟨k, j⟩, rfl⟩
      exact Lat.block_ratio_mem hc k j
    exact fun b hb => this hb
  have hBA : ∀ b ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩), b ∈ A := by
    intro b hb
    have : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤ A.restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨j, rfl⟩
      show (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩ ∈ A
      rw [← Finset.prod_div_distrib]
      exact prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
    exact this hb
  have hfr : ∀ r ∈ regAt ξ q, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ regAt ξ q ∧ r = u / v := by
    intro r hr
    obtain ⟨s, hsB, hsu, hsr⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ _ ht c q hc r).1 hr
    refine ⟨s * r, hBA _ hsr, s, hBA _ hsB, hsu.1, hsu.2.2, ?_⟩
    field_simp [hsu.1]
  obtain ⟨v, hvA, hv0, hvR, hint⟩ :=
    GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral A (regAt ξ q) hAR hfr a ha
  haveI : IsFractionRing A Ω := IsFractionRing.of_field A Ω fun z => by
    obtain ⟨u, hu, w, hw, -, rfl⟩ := exists_div_of_tie ht hc z
    exact ⟨⟨u, hBA u hu⟩, ⟨w, hBA w hw⟩, rfl⟩
  haveI : IsIntegrallyClosed A := by
    have h1 : IsIntegrallyClosed (A ⧸ (⊥ : Ideal A)) :=
      GlobalTheory.isIntegrallyClosed_quotient_minimalPrime_of_smooth ℚ A ⊥ (by
        rw [IsDomain.minimalPrimes_eq_singleton_bot]; rfl)
    exact IsIntegrallyClosed.of_equiv (RingEquiv.quotientBot A)
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have e : a = b * v⁻¹ := by
    have : (b : Ω) = v * a := hb
    rw [this]; field_simp [hv0]
  rw [e]
  exact mul_mem (hAR _ b.2) hvR

end Normal

section Blocks

variable {K : Type} {κ : Type} (J : K → Type)

def joinEquiv : ((k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => κ) k) ≃ ((k : K) → J k) × κ where
  toFun c := (fun k => c (.inl k), c (.inr ()))
  invFun t := fun k => match k with
    | .inl k => t.1 k
    | .inr () => t.2
  left_inv c := by funext k; rcases k with k | _ <;> rfl
  right_inv t := rfl

variable {J} [Fintype K] {Ω : Type} [Field Ω]

theorem segre_joinVec (x : (Σ k, J k) → Ω) (v : (Σ _ : Unit, κ) → Ω)
    (c : (k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => κ) k) :
    ∏ k, Cmp.joinVec x v ⟨k, c k⟩ = (∏ k, x ⟨k, (joinEquiv J c).1 k⟩) * v ⟨(), (joinEquiv J c).2⟩ := by
  rw [Fintype.prod_sum_type]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  rfl

theorem tie_joinVec {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {o : Type} [CommRing o] [Algebra o Ω]
    (x : (Σ k, J k) → Ω) (v : (Σ _ : Unit, κ) → Ω)
    (h : CoordTie o ξ (fun q : ((k : K) → J k) × κ => (∏ k, x ⟨k, q.1 k⟩) * v ⟨(), q.2⟩)) :
    CoordTie o ξ (fun c : (k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => κ) k => ∏ k, Cmp.joinVec x v ⟨k, c k⟩) := by
  have e : (fun c : (k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => κ) k => ∏ k, Cmp.joinVec x v ⟨k, c k⟩) =
      fun c => (fun q : ((k : K) → J k) × κ => (∏ k, x ⟨k, q.1 k⟩) * v ⟨(), q.2⟩) (joinEquiv J c) :=
    funext fun c => segre_joinVec x v c
  rw [e]
  exact ExtraBlocks.coordTie_equiv (joinEquiv J) h

end Blocks

end GlobalTheory.CompanionTheory.Ar.ChangeModel

namespace GlobalTheory.CompanionTheory.Ar.ChangeModel

theorem dominates_comp {X₁ X₂ X₃ : Scheme.{0}} {Ω₁ Ω₂ Ω₃ : Type} [Field Ω₁] [Field Ω₂] [Field Ω₃]
    {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂} {ξ₃ : Spec (CommRingCat.of Ω₃) ⟶ X₃}
    {f : X₂ ⟶ X₁} {g : X₃ ⟶ X₂} {i : Ω₁ →+* Ω₂} {j : Ω₂ →+* Ω₃}
    (hf : GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ f i) (hg : GlobalTheory.CompanionTheory.Ar.Dominates ξ₃ ξ₂ g j) :
    GlobalTheory.CompanionTheory.Ar.Dominates ξ₃ ξ₁ (g ≫ f) (j.comp i) := by
  unfold GlobalTheory.CompanionTheory.Ar.Dominates at *
  rw [← Category.assoc, hg, Category.assoc, hf, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem closure_eq_top_of_basis {Ω₁ Ω : Type} [Field Ω₁] [Field Ω] (i : Ω₁ →+* Ω)
    (hfin : letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) :
    ∃ (n : ℕ) (w : Option (Fin n) → Ω), w none ≠ 0 ∧
      Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) = ⊤ := by
  letI := i.toAlgebra
  haveI := hfin
  let b := Module.finBasis Ω₁ Ω
  refine ⟨_, fun l => l.elim 1 b, one_ne_zero, ?_⟩
  rw [eq_top_iff]
  intro a _
  rw [← b.sum_repr a]
  refine sum_mem fun j _ => ?_
  rw [Algebra.smul_def]
  refine mul_mem (Subfield.subset_closure (Or.inl ⟨_, rfl⟩)) (Subfield.subset_closure (Or.inr ⟨some j, none, ?_⟩))
  simp

theorem exists_normal_model : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] [CharZero Ω] (i : Ω₁ →+* Ω) (y : (Σ k, J k) → Ω₁) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω₁) ⟶ X), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (M : PModel ℤ (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩)) (h : M.X ⟶ X), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = i (y ⟨k, a⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates M.ξ ξ h i ∧ Flat.NormalCpt M.ξ ∧ SmoothGenericFibreM y' := by
  intro hRes K _ J _ Ω₁ Ω _ _ _ i y X ξ hfin hall htie
  classical

  let M₀ : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) :=
    { X := X, ξ := ξ, s := specZIsTerminal.from X, hover := specZIsTerminal.hom_ext _ _, all := hall, tie := htie }

  obtain ⟨n, w, hw0, hclo⟩ := closure_eq_top_of_basis i hfin
  obtain ⟨M₁, f₁, hf₁⟩ := GlobalTheory.T.exists_join_model_dominates ℤ Ω₁ _ _ M₀ Ω i (Option (Fin n)) w (fun a => by simp) ⟨none, hw0⟩ hclo
  let y₁ : (Σ k, Cmp.joinIdx J (fun _ : Unit => Option (Fin n)) k) → Ω :=
    Cmp.joinVec (fun p => i (y p)) (fun p : Σ _ : Unit, Option (Fin n) => w p.2)
  have ht₁ : CoordTie ℤ M₁.ξ (fun c' : (k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => Option (Fin n)) k =>
      ∏ k, y₁ ⟨k, c' k⟩) := by
    refine tie_joinVec _ _ ?_
    have e : (fun q : ((k : K) → J k) × Option (Fin n) => (∏ k, i (y ⟨k, q.1 k⟩)) * w q.2) =
        joinCo i (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) w := by
      funext q
      simp [joinCo, map_prod]
    show CoordTie ℤ M₁.ξ (fun q : ((k : K) → J k) × Option (Fin n) => (∏ k, i (y ⟨k, q.1 k⟩)) * w q.2)
    rw [e]
    exact M₁.tie

  obtain ⟨d, hd⟩ := exists_trdeg_eq ht₁
  obtain ⟨-, hAr⟩ := GlobalTheory.CompanionTheory.Ar.coordTie_birational_isArithVar M₁.X Ω M₁.ξ (K ⊕ Unit) _ y₁ d ht₁ hd
  obtain ⟨m, y₂, Jb, ⟨l₀, hl₀⟩, -, -, -, hsnc, -⟩ := SncRes.exists_snc_model hRes (K ⊕ Unit) _ Ω y₁ d 1 0 hAr
    (by intro a ha k; simp [MvPolynomial.support_one] at ha; simp [ha])
    (by
      intro h
      have : mConeMap y₁ 1 = 0 := h
      simp at this)

  let M₁' : PModel ℤ (fun c' : (k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => Option (Fin n)) k => ∏ k, y₁ ⟨k, c' k⟩) :=
    { X := M₁.X, ξ := M₁.ξ, s := M₁.s, hover := M₁.hover, all := M₁.all, tie := ht₁ }
  have hclo₂ : Subfield.closure (Set.range (RingHom.id Ω) ∪ {a | ∃ l l', a = y₂ ⟨(), l⟩ / y₂ ⟨(), l'⟩}) = ⊤ := by
    rw [eq_top_iff]
    intro a _
    exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  obtain ⟨M₂, f₂, hf₂⟩ := GlobalTheory.T.exists_join_model_dominates ℤ Ω _ _ M₁' Ω (RingHom.id Ω) (Fin m) (fun l => y₂ ⟨(), l⟩)
    (fun a => rfl) ⟨l₀, hl₀⟩ hclo₂
  let z := Cmp.joinVec y₁ y₂
  have ht₂ : CoordTie ℤ M₂.ξ (fun c' : (k : (K ⊕ Unit) ⊕ Unit) → Cmp.joinIdx (Cmp.joinIdx J (fun _ : Unit => Option (Fin n))) (fun _ : Unit => Fin m) k =>
      ∏ k, z ⟨k, c' k⟩) := tie_joinVec _ _ M₂.tie
  have hsm : SmoothGenericFibreM z := GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel _ _ Ω z d Jb hsnc
  let M₂' : PModel ℤ (fun c' : (k : (K ⊕ Unit) ⊕ Unit) → Cmp.joinIdx (Cmp.joinIdx J (fun _ : Unit => Option (Fin n))) (fun _ : Unit => Fin m) k => ∏ k, z ⟨k, c' k⟩) :=
    { X := M₂.X, ξ := M₂.ξ, s := M₂.s, hover := M₂.hover, all := M₂.all, tie := ht₂ }

  obtain ⟨κ₃, _, y₃, M₃, f₃, hf₃, hN, -, hNorm⟩ := GlobalTheory.T.exists_normal_dominating_model ℤ Ω _ _ M₂' Ω
  have hf₃' : GlobalTheory.CompanionTheory.Ar.Dominates M₃.ξ M₂.ξ f₃ (RingHom.id Ω) := hf₃
  have hchart : ∀ p : Cpt M₃.ξ, ∃ c₀, InChart M₃.ξ
      (fun c' : (k : (K ⊕ Unit) ⊕ Unit) → Cmp.joinIdx (Cmp.joinIdx J (fun _ : Unit => Option (Fin n))) (fun _ : Unit => Fin m) k => ∏ k, z ⟨k, c' k⟩) c₀ p := by
    intro p
    obtain ⟨h, hreg, -⟩ := RegAtDom.regAt_dominates M₂.X Ω M₂.ξ M₃.X Ω M₃.ξ f₃ _ hf₃' p
    obtain ⟨c, hc⟩ := ht₂.cover ⟨f₃ p.1, h⟩
    exact ⟨c, hc.1, fun c' => hreg _ (hc.2 c')⟩

  obtain ⟨K', _, J', _, y', bk, bx, -, hinj, heq, ht', -⟩ := ExtraBlocks.exists_blocks_of_lines ℤ Ω _ y₃ M₃ _ _ z Empty
    (fun a => a.elim) hchart (fun a => a.elim)
  have hsm' : SmoothGenericFibreM y' :=
    GlobalTheory.T.smoothGenericFibre_of_dominates Ω _ _ z K' J' y' M₂.X M₃.X M₂.ξ M₃.ξ f₃ M₂.all M₃.all ht₂ ht' hf₃' hsm fun q hq =>
      GlobalTheory.T.normal_iso_of_integrally_closed M₂.X Ω M₂.ξ M₃.X M₃.ξ f₃ q (hNorm q) (mem_regAt_of_isIntegral ht₂ hsm q hq)
  refine ⟨K', inferInstance, J', inferInstance, y', fun k => bk (.inl (.inl k)), fun k => bx (.inl (.inl k)),
    { X := M₃.X, ξ := M₃.ξ, s := M₃.s, hover := M₃.hover, all := M₃.all, tie := ht' },
    f₃ ≫ f₂ ≫ f₁, fun a b e => ?_, fun k a => heq (.inl (.inl k)) a, ?_, hN, hsm'⟩
  · simpa using hinj e
  · have h1 := dominates_comp (dominates_comp hf₁ hf₂) hf₃'
    exact h1

end GlobalTheory.CompanionTheory.Ar.ChangeModel
