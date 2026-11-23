import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagConcatenationExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactPairChernRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoDivisorClassIsoInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairMorphismCompatibilityStatement

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Concat

theorem gen_coker {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Z : GlobalTheory.Vert.Model O} {F E F' E' : Z.X.Modules} (ι : F ⟶ E) (ι' : F' ⟶ E')
    (γ : Z.GenIso F F') (φ : Z.GenIso E E')
    (h : γ.hom ≫ Z.genRes.map ι' = Z.genRes.map ι ≫ φ.hom) :
    ∃ χ : Z.GenIso (cokernel ι) (cokernel ι'),
      Z.genRes.map (cokernel.π ι) ≫ χ.hom = φ.hom ≫ Z.genRes.map (cokernel.π ι') :=
  ⟨PreservesCokernel.iso Z.genRes ι ≪≫ cokernel.mapIso _ _ γ φ h.symm ≪≫
    (PreservesCokernel.iso Z.genRes ι').symm, by simp⟩

open GlobalTheory.Vert.Model in

theorem exists_flagPair_ck_add : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (Z : GlobalTheory.Vert.Model O) (E₁ E₂ E₃ E₁' E₂' E₃' : Z.X.Modules) (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (a' : E₁' ⟶ E₂') (b' : E₂' ⟶ E₃') (h : a ≫ b = 0) (h' : a' ≫ b' = 0), (ShortComplex.mk a b h).ShortExact → (ShortComplex.mk a' b' h').ShortExact → ∀ (ψ₁ : E₁' ⟶ E₁) (ψ₂ : E₂' ⟶ E₂) (ψ₃ : E₃' ⟶ E₃), ψ₁ ≫ a = a' ≫ ψ₂ → ψ₂ ≫ b = b' ≫ ψ₃ → ∀ (φ₁ : Z.GenIso E₁ E₁') (φ₂ : Z.GenIso E₂ E₂') (φ₃ : Z.GenIso E₃ E₃'), φ₁.inv = Z.genRes.map ψ₁ → φ₂.inv = Z.genRes.map ψ₂ → φ₃.inv = Z.genRes.map ψ₃ → ∀ (r₁ r₂ r₃ : ℕ), r₂ = r₁ + r₃ → ∀ (F₁ : GlobalTheory.Vert.Model.FlagPair φ₁ r₁) (F₃ : GlobalTheory.Vert.Model.FlagPair φ₃ r₃), ∃ F₂ : GlobalTheory.Vert.Model.FlagPair φ₂ r₂, ∀ (k : ℕ) (Q : PicSym Z.X), ck (F₂.toFPair p) k Q = ck (F₁.toFPair p) k Q + ck (F₃.toFPair p) k Q := by
  intro O _ _ _ p _ _ _ Z E₁ E₂ E₃ E₁' E₂' E₃' a b a' b' h h' hS hS' ψ₁ ψ₂ ψ₃ h₁₂ h₂₃ φ₁ φ₂ φ₃
    hφ₁ hφ₂ hφ₃ r₁ r₂ r₃ hr F₁ F₃
  subst hr
  have ca : Z.genRes.map a ≫ φ₂.hom = φ₁.hom ≫ Z.genRes.map a' := by
    rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv, hφ₁, hφ₂, ← Functor.map_comp,
      ← Functor.map_comp, h₁₂]
  have cb : Z.genRes.map b ≫ φ₃.hom = φ₂.hom ≫ Z.genRes.map b' := by
    rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv, hφ₂, hφ₃, ← Functor.map_comp,
      ← Functor.map_comp, h₂₃]
  have key : ∀ i, (F₁.gen i).hom ≫ Z.genRes.map (F₁.fl'.ι i ≫ a') =
      Z.genRes.map (F₁.fl.ι i ≫ a) ≫ φ₂.hom := by
    intro i
    rw [Functor.map_comp, Functor.map_comp, reassoc_of% (F₁.gen_ι i), Category.assoc, ca]
  obtain ⟨fl₂, P1, P2, P3, P4⟩ := GlobalTheory.T.flag_concatenation_extension Z.X E₁ E₂ E₃ a b h hS r₁ r₃ F₁.fl F₃.fl
  obtain ⟨fl₂', Q1, Q2, Q3, Q4⟩ := GlobalTheory.T.flag_concatenation_extension Z.X E₁' E₂' E₃' a' b' h' hS' r₁ r₃ F₁.fl' F₃.fl'
  have hgen : ∀ k, ∃ γ : Z.GenIso (fl₂.F k) (fl₂'.F k),
      γ.hom ≫ Z.genRes.map (fl₂'.ι k) = Z.genRes.map (fl₂.ι k) ≫ φ₂.hom := by
    intro k
    by_cases hk : (k : ℕ) ≤ r₁
    · obtain ⟨e, he⟩ := P1 k ⟨k, by omega⟩ rfl
      obtain ⟨e', he'⟩ := Q1 k ⟨k, by omega⟩ rfl
      refine ⟨Z.genRes.mapIso e ≪≫ F₁.gen _ ≪≫ Z.genRes.mapIso e'.symm, ?_⟩
      rw [he, he']
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
      rw [← Functor.map_comp, Iso.inv_hom_id_assoc, key, ← Category.assoc, ← Functor.map_comp]
    · have hj : (k : ℕ) - r₁ < r₃ + 1 := by omega
      obtain ⟨hz, hSk⟩ := P2 k ⟨(k : ℕ) - r₁, hj⟩ (by simp; omega)
      obtain ⟨hz', hSk'⟩ := Q2 k ⟨(k : ℕ) - r₁, hj⟩ (by simp; omega)
      obtain ⟨χ, hχ⟩ := gen_coker _ _ (F₃.gen ⟨(k : ℕ) - r₁, hj⟩) φ₃ (F₃.gen_ι _)
      haveI := (fl₂.isVB k).isQuasicoherent
      haveI := (fl₂'.isVB k).isQuasicoherent
      haveI := fl₂.isVB_self.isQuasicoherent
      haveI := fl₂'.isVB_self.isQuasicoherent
      exact GlobalTheory.T.short_exact_pair_chern_relation O Z _ _ _ _ _ _ _ _ hz _ _ hz' hSk hSk' _ _ (F₃.fl.isVB_cokernel _)
        (F₃.fl'.isVB_cokernel _) φ₂ χ (by
          rw [Functor.map_comp, Functor.map_comp, Category.assoc, hχ, ← Category.assoc, cb,
            Category.assoc])
  choose gen hgen using hgen
  let F₂ : FlagPair φ₂ (r₁ + r₃) := ⟨fl₂, fl₂', gen, hgen⟩
  refine ⟨F₂, fun k Q => ?_⟩
  have A1 : ∀ i : Fin r₁, (F₂.toFPair p).x (Fin.castAdd r₃ i) = (F₁.toFPair p).x i ∧
      (F₂.toFPair p).x' (Fin.castAdd r₃ i) = (F₁.toFPair p).x' i ∧
      (F₂.toFPair p).Dv (Fin.castAdd r₃ i) = (F₁.toFPair p).Dv i := by
    intro i
    obtain ⟨e, u, he, hu⟩ := P3 (Fin.castAdd r₃ i) i rfl
    obtain ⟨e', u', he', hu'⟩ := Q3 (Fin.castAdd r₃ i) i rfl
    refine GlobalTheory.T.flag_pair_morphism_compatibility O p Z _ _ _ _ φ₂ φ₁ _ _ F₂ F₁ _ i e.hom e'.hom u u' ?_ hu hu'
    have hm : Mono (Z.genRes.map (F₁.fl'.ι i.succ ≫ a')) := by
      rw [show F₁.fl'.ι i.succ ≫ a' = e'.inv ≫ fl₂'.ι _ by rw [he', Iso.inv_hom_id_assoc],
        Functor.map_comp]
      infer_instance
    rw [← cancel_mono (Z.genRes.map (F₁.fl'.ι i.succ ≫ a'))]
    have L : (Z.genRes.map e.hom ≫ (F₁.gen i.succ).hom) ≫ Z.genRes.map (F₁.fl'.ι i.succ ≫ a') =
        Z.genRes.map (fl₂.ι (Fin.castAdd r₃ i).succ) ≫ φ₂.hom := by
      rw [Category.assoc, key, he, ← Category.assoc, ← Functor.map_comp]
    have R : (gen (Fin.castAdd r₃ i).succ).hom ≫ Z.genRes.map e'.hom ≫
        Z.genRes.map (F₁.fl'.ι i.succ ≫ a') =
        Z.genRes.map (fl₂.ι (Fin.castAdd r₃ i).succ) ≫ φ₂.hom := by
      rw [← Functor.map_comp, ← he']
      exact hgen _
    exact L.trans (R.symm.trans (Category.assoc _ _ _).symm)
  have A3 : ∀ j : Fin r₃, (F₂.toFPair p).x (Fin.natAdd r₁ j) = (F₃.toFPair p).x j ∧
      (F₂.toFPair p).x' (Fin.natAdd r₁ j) = (F₃.toFPair p).x' j ∧
      (F₂.toFPair p).Dv (Fin.natAdd r₁ j) = (F₃.toFPair p).Dv j := by
    intro j
    obtain ⟨m, u, hm, hu⟩ := P4 (Fin.natAdd r₁ j) j rfl
    obtain ⟨m', u', hm', hu'⟩ := Q4 (Fin.natAdd r₁ j) j rfl
    refine GlobalTheory.T.flag_pair_morphism_compatibility O p Z _ _ _ _ φ₂ φ₃ _ _ F₂ F₃ _ j m m' u u' ?_ hu hu'
    rw [← cancel_mono (Z.genRes.map (F₃.fl'.ι j.succ))]
    have L : (Z.genRes.map m ≫ (F₃.gen j.succ).hom) ≫ Z.genRes.map (F₃.fl'.ι j.succ) =
        (Z.genRes.map (fl₂.ι (Fin.natAdd r₁ j).succ) ≫ φ₂.hom) ≫ Z.genRes.map b' := by
      rw [Category.assoc, F₃.gen_ι, ← Category.assoc, ← Functor.map_comp, hm, Functor.map_comp,
        Category.assoc, cb, Category.assoc]
    have R : (gen (Fin.natAdd r₁ j).succ).hom ≫ Z.genRes.map m' ≫ Z.genRes.map (F₃.fl'.ι j.succ) =
        (Z.genRes.map (fl₂.ι (Fin.natAdd r₁ j).succ) ≫ φ₂.hom) ≫ Z.genRes.map b' := by
      rw [← Functor.map_comp, hm', Functor.map_comp, ← Category.assoc]
      exact congrArg (· ≫ Z.genRes.map b') (hgen _)
    exact L.trans (R.symm.trans (Category.assoc _ _ _).symm)
  simp only [ck, Fin.sum_univ_add, fun i => (A1 i).1, fun i => (A1 i).2.1, fun i => (A1 i).2.2,
    fun j => (A3 j).1, fun j => (A3 j).2.1, fun j => (A3 j).2.2]

end GlobalTheory.Concat
