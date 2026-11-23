import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsArithVarEffCartier
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

namespace GlobalTheory.BlowArith

theorem exists_isArithVar_effCartier_isIso (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (D : ℕ) (hX : IsArithVar p D) (J : X.IdealSheafData)
    (hJ : genericPoint X ∉ J.support) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X), IsArithVar (ρ ≫ p) D ∧
      ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap ρ) ∧
      ∀ V : X.Opens, (∀ x ∈ V, x ∉ J.support) → IsIso (ρ ∣_ V) := by
  have := hX.isNoetherianRing
  obtain ⟨Y, b, hb, hproj, hiso⟩ := ProjBlowup.exists_blowup p hX.isProjOver J
  let V : X.Opens := J.support.compl
  have hbV : IsIso (b ∣_ V) := hiso V fun _ hx => hx
  have : Nonempty V.toScheme := ⟨⟨genericPoint X, hJ⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : Nonempty (b ⁻¹ᵁ V).toScheme := ⟨inv (b ∣_ V) (Classical.arbitrary _)⟩
  have : IsIntegral (b ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (b ∣_ V)
  have hU : (J.comap b).support.compl = b ⁻¹ᵁ V := by
    ext y
    exact not_congr (ProjBlowup.mem_support_comap J b y)
  have hdom : IsSchemeTheoreticallyDominant (b ⁻¹ᵁ V).ι :=
    hU ▸ ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier Y _ hb.1
  have : IsNoetherian Y := isNoetherian_of_isProjOver hproj
  have : IsIntegral Y := by
    have : IsReduced Y := IsSchemeTheoreticallyDominant.isReduced (b ⁻¹ᵁ V).ι
    have h := ((IrreducibleSpace.isIrreducible_univ (b ⁻¹ᵁ V).toScheme).image _
      (b ⁻¹ᵁ V).ι.continuous.continuousOn).closure
    rw [Set.image_univ, (b ⁻¹ᵁ V).ι.denseRange.closure_range] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : (b ⁻¹ᵁ V).ι ≫ b = b ∣_ V ≫ V.ι := (morphismRestrict_ι b V).symm
  have hoi : IsOpenImmersion ((b ⁻¹ᵁ V).ι ≫ b) := by rw [hfac]; infer_instance
  have hg : (b ⁻¹ᵁ V).ι (genericPoint _) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgen : b (genericPoint Y) = genericPoint X := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  have hdeg : b.residueDegree (genericPoint Y) ≠ 0 := by
    intro h0
    have h1 := CurveDegreesCompare.residueDegree_comp (b ⁻¹ᵁ V).ι b (genericPoint _)
    rw [CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hflat : Flat ((b ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [flat_int_iff_charZero]
    have := hX.charZero
    have : IsDominant b := ⟨by
      rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← genericPoint_closure]
      exact closure_mono (Set.singleton_subset_iff.2 ⟨_, hgen⟩)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant b
    have hinj' : Function.Injective b.appTop := Scheme.Hom.app_injective b ⊤
    exact charZero_of_injective_ringHom (f := b.appTop.hom) hinj'
  exact ⟨Y, b, ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat,
    DimCover.topologicalKrullDim_eq k X Y p (b ≫ p) D hX hproj hflat b rfl hgen hdeg⟩, hb.1, hiso⟩

end GlobalTheory.BlowArith

namespace GlobalTheory.ArLieBase

theorem exists_blowup_principalises : ∀ (F : Type) [Field F] [NumberField F] (G T : Scheme.{0}) (s : G ⟶ Sp F) (S : Set G) (d : ℕ) (ι : G ⟶ T) (X W : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ G) (ρ : X ⟶ T), IsPre s S d ι q jB πB ρ → ∀ (n : ℕ) (U : Fin n → X.Opens) (m : Fin n → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)) (N : Fin n → ℕ), (∀ j, IsAffineOpen (U j)) → (∀ j, N j ≠ 0) → (∀ j, (N j : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical) → ∃ (X' W' : Scheme.{0}) (b : X' ⟶ X) (jB' : W' ⟶ X') (πB' : W' ⟶ G), IsPre s S d ι (b ≫ q) jB' πB' (b ≫ ρ) ∧ ∀ (Y : Scheme.{0}) (ν : Y ⟶ X') (w : Y) (j : Fin n), (ν ≫ b) w ∈ U j → ∃ (V : Y.Opens) (hV : V ≤ (ν ≫ b) ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧ ∃ k, ∀ k', ((ν ≫ b).appLE (U j) V hV).hom (A j k) ∣ ((ν ≫ b).appLE (U j) V hV).hom (A j k') := by
  intro F _ _ G T s S d ι X W q jB πB ρ h n U m A N hU hN hA
  have hX := h.1
  have := hX.isIntegral
  have := hX.isLocallyNoetherian
  have hc := hX.charZero
  set p : ℕ := ∏ j, N j with hpdef
  have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hN j
  have hpA : ∀ j, (p : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical := by
    intro j
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ j)
    rw [hpdef, hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hA j)
  obtain ⟨J, hJp, hJE⟩ := GlobalTheory.Principalise.exists_idealSheaf_principalises X p n U m A hU hpA
  have hgen : genericPoint X ∈ X.basicOpen (p : Γ(X, ⊤)) := by
    have hne : (p : Γ(X, ⊤)) ≠ 0 := Nat.cast_ne_zero.2 hp0
    have hb : X.basicOpen (p : Γ(X, ⊤)) ≠ ⊥ := fun h0 => hne ((basicOpen_eq_bot_iff _).1 h0)
    have : Nonempty (X.basicOpen (p : Γ(X, ⊤))) := by
      by_contra h1
      apply hb
      rw [eq_bot_iff]
      intro x hx
      exact (h1 ⟨⟨x, hx⟩⟩).elim
    exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen (p : Γ(X, ⊤))).isOpen).mpr
      (by simpa using this)
  have hJg : genericPoint X ∉ J.support := fun hx => hJp _ hx hgen
  obtain ⟨X', b, hX', hE, hiso⟩ := GlobalTheory.BlowArith.exists_isArithVar_effCartier_isIso (𝓞 F) X q d hX J hJg
  let V : X.Opens := J.support.compl
  have hbV : IsIso (b ∣_ V) := hiso V fun _ hx => hx
  have huF : IsUnit ((p : ℕ) : Γ(Sp F, ⊤)) := by
    have := (IsUnit.mk0 (p : F) (Nat.cast_ne_zero.2 hp0)).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    simpa using this
  have huW : IsUnit ((p : ℕ) : Γ(W, ⊤)) := by
    let φ : Γ(Sp F, ⊤) →+* Γ(W, ⊤) := ((πB ≫ s).app ⊤).hom
    have := huF.map φ
    rwa [map_natCast φ] at this
  have hrange : Set.range jB ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hw : w ∈ jB ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤)) := by
      simp only [Scheme.preimage_basicOpen, map_natCast]
      exact (Scheme.basicOpen_of_isUnit W huW).ge (show w ∈ (⊤ : W.Opens) from trivial)
    exact fun hx => hJp _ hx hw
  let jV : W ⟶ V.toScheme := IsOpenImmersion.lift V.ι jB hrange
  have hjV : jV ≫ V.ι = jB := IsOpenImmersion.lift_fac _ _ _
  let jB' : W ⟶ X' := jV ≫ inv (b ∣_ V) ≫ (b ⁻¹ᵁ V).ι
  have hjB' : jB' ≫ b = jB := by
    simp only [jB', Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hjV]
  have hsq : IsPullback jB' (𝟙 W) b jB := by
    have h1 : IsPullback (jV ≫ inv (b ∣_ V)) (𝟙 W) (b ∣_ V) jV :=
      IsPullback.of_vert_isIso ⟨by simp⟩
    have h2 := h1.paste_horiz (isPullback_morphismRestrict b V).flip
    simpa [jB', Category.assoc, hjV] using h2
  have hpb : IsPullback jB' (πB ≫ s) (b ≫ q) (spMap (algebraMap (𝓞 F) F)) := by
    simpa using hsq.paste_vert h.2.1
  refine ⟨X', W, b, jB', πB, ⟨hX', hpb, h.2.2.1, h.2.2.2.1, ?_⟩, ?_⟩
  · rw [← Category.assoc, hjB']
    exact h.2.2.2.2
  · intro Y ν w j hw
    exact hJE X' Y b ν hE w j hw

end GlobalTheory.ArLieBase
