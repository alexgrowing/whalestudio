import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionChainLatticeEntriesAgreeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIteratedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharacterClosedFormStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedLevelPatternToFramePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedLevelPatternOfFramePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelCharacterByResidueCharacterStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.PhiAgreeProof

theorem places_iff_pattern : ∀ (F : Type) [Zero F] [One F] (κ ρ s τ j : ℕ) (R : ℕ → ℕ → F),
    (∀ (a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) ↔
    ((∀ p', p' < κ + s + 1 → R p' p' = 1 ∧ ∀ p, p < κ + s + 1 + j * τ → p ≠ p' →
        (κ + s + 1 ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + s + 1 ≤ p' → p' < κ + s + 1 + j * τ → p < κ + s + 1 + j * τ →
        (p' - (κ + s + 1)) / τ < (p - (κ + s + 1)) / τ → R p p' = 0)) := by
  intro F _ _ κ ρ s τ j R
  exact ⟨GlobalTheory.T.iteratedLevelPattern_to_framePlaces F κ ρ s τ j R, GlobalTheory.T.iteratedLevelPattern_of_framePlaces F κ ρ s τ j R⟩

theorem symmetricLevelCharacter_rationalPoint_eq_residue : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + s + 1 → p' < κ + s + 1 → IntAt P (M p p')) → ∀ (g : S.P.J), (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) a) (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) b))) → ((S.P.lam g : ℂˣ) : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := GlobalTheory.T.symLevel_character_by_residueCharacter

theorem zPos_equiv : ∀ (κ l τ j : ℕ), ∃ eqv : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ), ∀ a, (eqv a : ℕ) = zPos a := by
  intro κ l τ j
  refine ⟨(Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv, ?_⟩
  rintro ((a | a) | ⟨i, u⟩)
  · simp [zPos]
  · simp [zPos]
  · simp [zPos, finProdFinEquiv]; ring

section SlopeTestRemainingChoices
variable {E : Type} [Field E] [NumberField E]

theorem intAt_one' (P : HeightOneSpectrum (𝓞 E)) : IntAt P (1 : E) := by
  simpa using IntAt.coe P 1

theorem intAt_zero' (P : HeightOneSpectrum (𝓞 E)) : IntAt P (0 : E) := by
  simpa using IntAt.coe P 0

theorem intAt_sub' {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    IntAt P (a - b) := by
  have h1 : IntAt P (-1 : E) := by simpa using IntAt.coe P (-1)
  rw [sub_eq_add_neg, neg_eq_neg_one_mul]
  exact ha.add (h1.mul hb)

theorem redP_eq_iff' {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    redP P (a - b) = 0 ↔ redP P a = redP P b := by
  have e : redP P a = redP P (a - b) + redP P b := by
    rw [← reduction_add (intAt_sub' ha hb) hb, sub_add_cancel]
  rw [e]; constructor
  · intro h; rw [h, zero_add]
  · intro h; simpa using h

theorem reduction_one' (P : HeightOneSpectrum (𝓞 E)) : redP P (1 : E) = 1 := by
  simpa using reduction_coe P 1

theorem redP_zero' (P : HeightOneSpectrum (𝓞 E)) : redP P (0 : E) = 0 := by
  simpa using reduction_coe P 0

theorem intAt_natCast' (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) : IntAt P (q : E) := by
  simpa using IntAt.coe P (q : 𝓞 E)

end SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_KO_of_det {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n k} (hA : IntM A)
    (hd : valuation k A.det = 1) : ∃ g ∈ KO k n, g.val = A := by
  have h0 : A.det ≠ 0 := by intro h; rw [h, map_zero] at hd; exact zero_ne_one hd
  refine exists_mem_KO_of_mul hA (A' := A⁻¹) ?_ (by rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h0), sub_self]; exact maxM_zero)
  let A₀ : Matrix n n 𝒪[k] := fun i j => ⟨A i j, hA i j⟩
  have hA₀ : (algebraMap 𝒪[k] k).mapMatrix A₀ = A := by ext i j; rfl
  intro i j
  rw [Matrix.inv_def, ← hA₀, ← RingHom.map_adjugate, Matrix.smul_apply, smul_eq_mul]
  refine mul_mem ?_ (by simp [RingHom.mapMatrix_apply]; exact (A₀.adjugate i j).2)
  rw [Ring.inverse_eq_inv', Valuation.mem_integer_iff, map_inv₀, hA₀, hd, inv_one]

theorem det_zPos {E : Type} [CommRing E] (ι : E →+* k) (κ l τ j : ℕ) (M : ℕ → ℕ → E) :
    (Matrix.of fun a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j => ι (M (zPos a) (zPos b))).det =
      ι (Matrix.of fun p p' : Fin (κ + l + j * τ) => M p p').det := by
  obtain ⟨eqv, he⟩ := zPos_equiv κ l τ j
  rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self eqv]
  congr 1
  ext a b
  simp [he]

theorem zPos_ixSucc_inl {κ l τ j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) :
    zPos (ixSucc (Fin κ ⊕ Fin l) (Fin τ) j (Sum.inl a)) = zPos a := by
  rcases a with (a | a) | ⟨i, u⟩ <;> rfl

theorem det_mem_of_intM {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n k} (hA : IntM A) :
    A.det ∈ 𝒪[k] := by
  let A₀ : Matrix n n 𝒪[k] := fun i j => ⟨A i j, hA i j⟩
  have hA₀ : (algebraMap 𝒪[k] k).mapMatrix A₀ = A := by ext i j; rfl
  rw [← hA₀, ← RingHom.map_det]
  exact (A₀.det).2

theorem phiAgree : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → PhiAgree P q ι σ₀ ψ₀ χ S := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT
  intro τ j c h n' c' n c₂ hn' hn hc' hc₂ e' e ho' ho x
  have hent := GlobalTheory.T.completionChain_lattice_entries_agree E K k P q ι σ₀ ψ₀ χ s κ S hT τ j c h n' c' n c₂ hn' hn hc' hc₂ e' e ho' ho x
  subst c' c₂
  obtain ⟨hres1, hres2, hres3, hq0, -, -, -, -⟩ := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι S.ϖ hT.compl S.unif
  have hint : ∀ a : E, ι a ∈ 𝒪[k] ↔ IntAt P a := hT.compl.int
  have hNc : n + c = κ + s + 1 + j * τ + τ := by subst hn; rw [← h]; ring
  set M := LocE.entB q κ (c + 1) n' c n (fun i => i + 1) (fun i => i + 1) x with hM
  set G : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k :=
    Matrix.of fun a b => ι (M (zPos a) (zPos b)) with hG
  set Y : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j ⊕ Fin τ) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k :=
    (Matrix.of fun (a : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (j + 1)) (b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) => ι (M (zPos a) (zPos b))).submatrix
      (ixSucc _ _ j) id with hY
  have hL : (S.T (Fin τ)).Phi j c h (toLoc ι e e' x) =
      (S.P.iter (Fin τ) S.μ S.tame j).Phi (Fin τ) (S.μ (j + 1)) Y := by
    show (S.P.iter (Fin τ) S.μ S.tame j).Phi (Fin τ) (S.μ (j + 1))
      (((typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) (j + 1) c (by omega))).coords
        (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) j (c + 1) (by omega))) (toLoc ι e e' x)).submatrix (ixSucc _ _ j) id) = _
    congr 2
    ext a b
    exact hent a b
  have hY1 : Y.toRows₁ = G := by
    ext a b; simp only [hY, hG, Matrix.toRows₁, Matrix.submatrix_apply, Matrix.of_apply, id, zPos_ixSucc_inl]
  have hY2 : ∀ u b, Y.toRows₂ u b = ι (M (κ + s + 1 + j * τ + u.val) (zPos b)) := by
    intro u b; rfl
  rw [hL]
  unfold LocE.PhiGS
  dsimp only
  rw [show j + 1 - 1 = j by omega]
  rw [← hM]
  have hzb : ∀ a : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j, zPos a < κ + s + 1 + j * τ := fun a => by
    obtain ⟨eqv, he⟩ := zPos_equiv κ (s + 1) τ j; rw [← he]; exact (eqv a).2
  have hzs : ∀ p, p < κ + s + 1 + j * τ → ∃ a : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j, zPos a = p := fun p hp => by
    obtain ⟨eqv, he⟩ := zPos_equiv κ (s + 1) τ j; exact ⟨eqv.symm ⟨p, hp⟩, by rw [← he]; simp⟩
  have hdetG : G.det = ι (Matrix.of fun p p' : Fin (κ + s + 1 + j * τ) => M p p').det := det_zPos ι κ (s + 1) τ j M
  have hpat := GlobalTheory.T.symmetricLevelChain_pattern_iterated k s κ S (Fin τ) j
  have htr : (∀ a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j, IntAt P (M (zPos a) (zPos b))) → ∀ a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j,
      (valuation k (G a b - (1 : Matrix _ _ k) a b) < 1 ↔ redP P (M (zPos a) (zPos b)) = if a = b then 1 else 0) := by
    intro hI a b
    have hI1 : IntAt P (if a = b then (1 : E) else 0) := by split_ifs; exacts [intAt_one' P, intAt_zero' P]
    have e1 : G a b - (1 : Matrix _ _ k) a b = ι (M (zPos a) (zPos b) - if a = b then 1 else 0) := by
      simp only [hG, Matrix.of_apply, Matrix.one_apply, map_sub]; split_ifs <;> simp
    rw [e1, hres2 _ (intAt_sub' (hI a b) hI1), redP_eq_iff' (hI a b) hI1]
    split_ifs <;> simp [reduction_one', redP_zero']
  split_ifs with hcond
  · obtain ⟨c1, c2, c3, c4⟩ := hcond
    have hI : ∀ a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j, IntAt P (M (zPos a) (zPos b)) := fun a b => c1 _ _ (by have := hzb a; omega) (hzb b)
    have hGint : IntM G := fun a b => (hint _).2 (hI a b)
    have hmax : MaxM Y.toRows₂ := fun u b => by
      rw [hY2, hres1]; exact c2 _ _ (by omega) (by have := u.2; omega) (hzb b)
    have hpatG : ∀ a b, ¬ FreeIx S.ρ a b → valuation k (G a b - (1 : Matrix _ _ k) a b) < 1 := by
      intro a b hab
      rw [htr hI]
      exact ((places_iff_pattern (𝓞 E ⧸ P.asIdeal) κ S.ρ s τ j (fun p p' => redP P (M p p'))).2 ⟨c3, c4⟩) a b hab
    have hIdet : IntAt P (Matrix.of fun p p' : Fin (κ + s + 1 + j * τ) => M p p').det :=
      (hint _).1 (hdetG ▸ det_mem_of_intM hGint)
    by_cases hu : IsUnit (redP P (Matrix.of fun p p' : Fin (κ + s + 1 + j * τ) => M p p').det)
    · obtain ⟨g, hgKO, hgv⟩ := exists_KO_of_det hGint (by rw [hdetG]; exact (hres3 _ hIdet).2 hu)
      have hgJ : g ∈ (S.P.iter (Fin τ) S.μ S.tame j).J :=
        (hpat g).2 ⟨hgKO, fun a b hab => by rw [hgv]; exact hpatG a b hab⟩
      rw [TypeDatum.Phi_of_mem _ _ ⟨g, hgJ⟩ (by rw [hY1]; exact hgv) hmax]
      obtain ⟨g₀, D, hg₀, hD, hlam⟩ := GlobalTheory.T.iteratedDepthOneLevel_character_closed_form k (Fin κ ⊕ Fin (s + 1)) (Fin τ) S.P S.μ S.tame j ⟨g, hgJ⟩
      rw [hlam]
      have hl0 := symmetricLevelCharacter_rationalPoint_eq_residue E K k P q ι σ₀ ψ₀ χ s κ S hT M (fun p p' hp hp' => c1 p p' (by omega) (by omega)) g₀ (by
        rw [hg₀]; ext a b
        rcases a with a | a <;> rcases b with b | b <;> simp [hgv, hG, zPos, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos])
      have hDi : ∀ i : Fin j, ((S.μ (i.val + 1) (Matrix.GeneralLinearGroup.det (D i)) : ℂˣ) : ℂ) =
          σ₀ (LocE.unitV (χ i) (Matrix.of fun u u' : Fin τ =>
            M (κ + s + 1 + i.val * τ + u.val) (κ + s + 1 + i.val * τ + u'.val)).det) := by
        intro i
        have hDv : (D i).val = ι.mapMatrix (Matrix.of fun u u' : Fin τ =>
            M (κ + s + 1 + i.val * τ + u.val) (κ + s + 1 + i.val * τ + u'.val)) := by
          rw [(hD i).2]; ext u u'
          simp only [Ix.diagonalBlockOfMatrix, Matrix.submatrix_apply, hgv, hG, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
          rfl
        have hdv : ((Matrix.GeneralLinearGroup.det (D i) : kˣ) : k) = ι (Matrix.of fun u u' : Fin τ =>
            M (κ + s + 1 + i.val * τ + u.val) (κ + s + 1 + i.val * τ + u'.val)).det := by
          rw [Matrix.GeneralLinearGroup.val_det_apply, hDv, RingHom.map_det]
        have hv1 := valuation_det_of_mem_KO (hD i).1
        rw [hdv] at hv1
        have hIi : IntAt P (Matrix.of fun u u' : Fin τ =>
            M (κ + s + 1 + i.val * τ + u.val) (κ + s + 1 + i.val * τ + u'.val)).det :=
          (hint _).1 (by rw [Valuation.mem_integer_iff, hv1])
        exact hT.chi i _ _ hIi ((hres3 _ hIi).1 hv1) hdv
      have hdg : ((Matrix.GeneralLinearGroup.det g : kˣ) : k) =
          ι (Matrix.of fun p p' : Fin (κ + s + 1 + j * τ) => M p p').det := by
        rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, hdetG]
      have hmu := hT.chi j _ _ hIdet hu hdg
      unfold LocE.lamGvS
      simp only [Units.val_mul, Units.coe_prod, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_prod]
      rw [hl0, hmu, ← Fin.prod_univ_eq_prod_range]
      congr 2
      exact Finset.prod_congr rfl fun i _ => hDi i
    · have h0 : LocE.unitV (χ j) (Matrix.of fun p p' : Fin (κ + s + 1 + j * τ) => M p p').det = 0 := by
        unfold LocE.unitV; rw [dif_neg hu]
      rw [h0, _root_.inv_zero, mul_zero, map_zero]
      by_contra hne
      obtain ⟨⟨g, hgJ, hgv⟩, -⟩ := (TypeDatum.Phi_ne_zero_iff _ _).1 hne
      rw [hY1] at hgv
      have hv := valuation_det_of_mem_KO ((S.P.iter (Fin τ) S.μ S.tame j).le_KO hgJ)
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, hdetG] at hv
      exact hu ((hres3 _ hIdet).1 hv)
  · rw [map_zero]
    by_contra hne
    obtain ⟨⟨g, hgJ, hgv⟩, hmax⟩ := (TypeDatum.Phi_ne_zero_iff _ _).1 hne
    rw [hY1] at hgv
    obtain ⟨hgKO, hgpat⟩ := (hpat g).1 hgJ
    have hGint : IntM G := hgv ▸ intM_of_mem_KO hgKO
    have hI : ∀ a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j, IntAt P (M (zPos a) (zPos b)) := fun a b => (hint _).1 (hGint a b)
    have hbot : ∀ (u : Fin τ) (b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), IntAt P (M (κ + s + 1 + j * τ + u.val) (zPos b) / q) :=
      fun u b => (hres1 _).1 (by rw [← hY2]; exact hmax u b)
    apply hcond
    refine ⟨?_, ?_, ?_⟩
    · intro p p' hp hp'
      obtain ⟨b, rfl⟩ := hzs p' hp'
      by_cases hpa : p < κ + s + 1 + j * τ
      · obtain ⟨a, rfl⟩ := hzs p hpa; exact hI a b
      · obtain ⟨u, hu⟩ : ∃ u : Fin τ, p = κ + s + 1 + j * τ + u.val :=
          ⟨⟨p - (κ + s + 1 + j * τ), by omega⟩, by simp only; omega⟩
        subst hu
        have := (hbot u b).mul (intAt_natCast' P q)
        rwa [div_mul_cancel₀ _ hq0] at this
    · intro p p' hp hp2 hp'
      obtain ⟨b, rfl⟩ := hzs p' hp'
      obtain ⟨u, hu⟩ : ∃ u : Fin τ, p = κ + s + 1 + j * τ + u.val :=
        ⟨⟨p - (κ + s + 1 + j * τ), by omega⟩, by simp only; omega⟩
      subst hu; exact hbot u b
    · exact (places_iff_pattern (𝓞 E ⧸ P.asIdeal) κ S.ρ s τ j (fun p p' => redP P (M p p'))).1
        (fun a b hab => (htr hI a b).1 (by have := hgpat a b hab; rwa [hgv] at this))

end GlobalTheory.SymBridge.PhiAgreeProof
