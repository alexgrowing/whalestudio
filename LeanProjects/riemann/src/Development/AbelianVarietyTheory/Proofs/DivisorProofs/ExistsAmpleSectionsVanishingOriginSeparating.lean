import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RelAmpleSep

theorem mem_iff_of_gen {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {κ : Type} (r : κ → R) (c : κ → A)
    (I : Ideal R) (hI : ∀ j, r j - φ (c j) ∈ I) (p : MvPolynomial κ A) :
    MvPolynomial.eval₂Hom φ r p ∈ I ↔ φ (MvPolynomial.eval c p) ∈ I := by
  have hr : (Ideal.Quotient.mk I) ∘ r = ((Ideal.Quotient.mk I).comp φ) ∘ c := by
    funext j; exact Ideal.Quotient.eq.2 (hI j)
  have e : Ideal.Quotient.mk I (MvPolynomial.eval₂Hom φ r p) = Ideal.Quotient.mk I (φ (MvPolynomial.eval c p)) := by
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, hr, MvPolynomial.eval,
      MvPolynomial.coe_eval₂Hom, ← RingHom.comp_apply, MvPolynomial.eval₂_comp_left]
    rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem (I := I), e]

theorem ideal_eq_of_gen {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {κ : Type} (r : κ → R) (c : κ → A)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom φ r)) (P Q : Ideal R)
    (hP : ∀ j, r j - φ (c j) ∈ P) (hQ : ∀ j, r j - φ (c j) ∈ Q) (hPQ : ∀ x, φ x ∈ P ↔ φ x ∈ Q) : P = Q := by
  ext a
  obtain ⟨p, rfl⟩ := hs a
  rw [mem_iff_of_gen φ r c P hP, mem_iff_of_gen φ r c Q hQ]
  exact hPQ _

theorem mem_basicOpen_iff_prime {Y : Scheme.{0}} {D : Y.Opens} (hD : IsAffineOpen D) {y : Y} (hy : y ∈ D)
    (a : Γ(Y, D)) : y ∈ Y.basicOpen a ↔ a ∉ (hD.primeIdealOf ⟨y, hy⟩).asIdeal := by
  have h := hD.fromSpec_primeIdealOf ⟨y, hy⟩
  have h2 : hD.primeIdealOf ⟨y, hy⟩ ∈ hD.fromSpec ⁻¹ᵁ Y.basicOpen a ↔ y ∈ Y.basicOpen a := by
    show hD.fromSpec (hD.primeIdealOf ⟨y, hy⟩) ∈ Y.basicOpen a ↔ y ∈ Y.basicOpen a
    rw [h]
  rw [← h2, hD.fromSpec_preimage_basicOpen]
  rfl

variable {K : Type} [Field K]

theorem one_left_comp_hom (B : AbVar K) : (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left ≫ B.X.hom = 𝟙 _ := Over.w _

theorem sp_pt_eq (a b : Sp K) : a = b := by
  have h : ∀ p : PrimeSpectrum K, p.asIdeal = ⊥ := fun p => Ideal.eq_bot_of_prime _
  exact PrimeSpectrum.ext ((h a).trans (h b).symm)

theorem top_le_preimage_unit (B : AbVar K) : (⊤ : (Over.mk (𝟙 (Sp K))).left.Opens) ≤
    (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left ⁻¹ᵁ (B.X.hom ⁻¹ᵁ ⊤) := fun _ _ => trivial

def unitU (B : AbVar K) : (⊤ : (Sp K).Opens).toScheme ⟶ (B.X.hom ⁻¹ᵁ ⊤).toScheme :=
  (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left.resLE (B.X.hom ⁻¹ᵁ ⊤) (⊤ : (Over.mk (𝟙 (Sp K))).left.Opens)
    (top_le_preimage_unit B)

theorem unitU_comp (B : AbVar K) : unitU B ≫ (B.X.hom ∣_ ⊤) = 𝟙 _ := by
  rw [← cancel_mono (⊤ : (Sp K).Opens).ι, Category.assoc, morphismRestrict_ι, unitU,
    Scheme.Hom.resLE_comp_ι_assoc, one_left_comp_hom, Category.comp_id, Category.id_comp]

theorem unitU_ι (B : AbVar K) (t : (⊤ : (Sp K).Opens).toScheme) :
    (B.X.hom ⁻¹ᵁ ⊤).ι (unitU B t) = B.origin := by
  rw [← Scheme.Hom.comp_apply, unitU, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply, AbVar.origin]
  exact congrArg _ (sp_pt_eq _ _)

theorem topU_pt_eq (a b : (⊤ : (Sp K).Opens).toScheme) : a = b := Subtype.ext (sp_pt_eq _ _)

theorem isUnit_sub_mul_of_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {a b : R} (c : R) (ha : IsUnit a)
    (hb : ¬ IsUnit b) : IsUnit (a - c * b) := by
  by_contra h
  have hb' : b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hb
  have h' : a - c * b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h
  have h'' := Ideal.add_mem _ h' (Ideal.mul_mem_left _ c hb')
  rw [sub_add_cancel] at h''
  exact (IsLocalRing.mem_maximalIdeal _).1 h'' ha

theorem gs_secSubScale {Y : Scheme.{0}} {P : LB Y} (a b : P.Sec) (c : Γ(Y, ⊤)) (y : Y) (k : P.ι) (hk : y ∈ P.U k) :
    gs (𝟙 Y) y _ ((DVR.SecOps.secAdd a (DVR.SecOps.secNeg (DVR.SecOps.secScale c b))).f k) =
      gs (𝟙 Y) y _ (a.f k) - gs (𝟙 Y) y ⊤ c * gs (𝟙 Y) y _ (b.f k) := by
  have e : (DVR.SecOps.secAdd a (DVR.SecOps.secNeg (DVR.SecOps.secScale c b))).f k =
      a.f k - Out.resTop _ c * b.f k := by
    simp only [DVR.SecOps.secAdd, DVR.SecOps.secNeg, DVR.SecOps.secScale, sub_eq_add_neg]
  rw [e, LBGerm.gs_sub _ y _ hk, gs_mul _ y _ hk, Out.resTop, gs_res _ y _ hk]

theorem exists_sep_of_chart {Y T : Scheme.{0}} (π : Y ⟶ T) (u : T ⟶ Y) (hu : u ≫ π = 𝟙 T) (hT : ∀ a b : T, a = b)
    {P : LB Y} (hP : P.IsLB) {n : ℕ} (s : Fin n → P.Sec) (hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (i : Fin n) (hD : IsAffineOpen (Out.nonzeroLocus (s i)))
    (r : Fin n → Γ(Y, Out.nonzeroLocus (s i)))
    (hr : ∀ j k, (Y.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ P.U k ≤ P.U k)).op).hom ((s j).f k) =
            (Y.presheaf.map (homOfLE (inf_le_left :
              Out.nonzeroLocus (s i) ⊓ P.U k ≤ Out.nonzeroLocus (s i))).op).hom (r j) *
            (Y.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ P.U k ≤ P.U k)).op).hom ((s i).f k))
    (hs : Function.Surjective (MvPolynomial.eval₂Hom (π.appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom r))
    (t₀ : T) (hi : u t₀ ∈ Out.nonzeroLocus (s i)) :
    ∃ t : Fin n → P.Sec, (∀ j, u t₀ ∉ Out.nonzeroLocus (t j)) ∧
      ∀ y, y ≠ u t₀ → ∃ j, y ∈ Out.nonzeroLocus (t j) := by
  classical
  have hTle : ⊤ ≤ u ⁻¹ᵁ Out.nonzeroLocus (s i) := fun t _ => by rw [hT t t₀]; exact hi
  let c : Fin n → Γ(T, ⊤) := fun j => (u.appLE (Out.nonzeroLocus (s i)) ⊤ hTle).hom (r j)
  let φ := (π.appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom
  have hc : ∀ (y : Y) (x : Γ(T, ⊤)), gs (𝟙 Y) y ⊤ (π.appTop.hom x) = gs π y ⊤ x := fun y x =>
    (gs_pull (𝟙 Y) π y ⊤ trivial x).trans (by rw [Category.id_comp])
  have hφ : ∀ y ∈ Out.nonzeroLocus (s i), ∀ x, gs (𝟙 Y) y _ (φ x) = gs π y ⊤ x := fun y hy x =>
    (gs_appLE π ⊤ _ le_top (𝟙 Y) y hy x).trans (by rw [Category.id_comp])
  have hrel : ∀ j k y, y ∈ Out.nonzeroLocus (s i) → y ∈ P.U k →
      gs (𝟙 Y) y _ ((s j).f k) = gs (𝟙 Y) y _ (r j) * gs (𝟙 Y) y _ ((s i).f k) := by
    intro j k y hyD hk
    have hm : y ∈ Out.nonzeroLocus (s i) ⊓ P.U k := ⟨hyD, hk⟩
    have e := congrArg (gs (𝟙 Y) y (Out.nonzeroLocus (s i) ⊓ P.U k)) (hr j k)
    rwa [gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
  have hkey : ∀ y ∈ Out.nonzeroLocus (s i), ∀ j k, y ∈ P.U k →
      gs (𝟙 Y) y _ ((DVR.SecOps.secAdd (s j) (DVR.SecOps.secNeg
        (DVR.SecOps.secScale (π.appTop.hom (c j)) (s i)))).f k) =
        gs (𝟙 Y) y _ (r j - φ (c j)) * gs (𝟙 Y) y _ ((s i).f k) := by
    intro y hy j k hk
    rw [gs_secSubScale _ _ _ y k hk, hrel j k y hy hk, hc, LBGerm.gs_sub _ y _ hy, hφ y hy]
    ring
  have hiff : ∀ y ∈ Out.nonzeroLocus (s i), ∀ j,
      y ∈ Out.nonzeroLocus (DVR.SecOps.secAdd (s j) (DVR.SecOps.secNeg
        (DVR.SecOps.secScale (π.appTop.hom (c j)) (s i)))) ↔ y ∈ Y.basicOpen (r j - φ (c j)) := by
    intro y hy j
    obtain ⟨k, hk⟩ := exists_chart hP y
    rw [GlobalTheory.mem_nonzeroLocus_iff_isUnit _ hk, hkey y hy j k hk, IsUnit.mul_iff,
      ← GlobalTheory.mem_nonzeroLocus_iff_isUnit (s i) hk, LBGerm.isUnit_gs_iff (𝟙 Y) y _ hy]
    exact and_iff_left hy
  have h0 : ∀ j, u t₀ ∉ Y.basicOpen (r j - φ (c j)) := by
    intro j h
    have hu1 := (LBGerm.isUnit_gs_iff u t₀ _ hi _).2 h
    have e1 : gs u t₀ _ (r j) = gs (𝟙 T) t₀ ⊤ (c j) :=
      ((gs_appLE u _ ⊤ hTle (𝟙 T) t₀ trivial (r j)).trans (by rw [Category.id_comp])).symm
    have e2 : gs u t₀ _ (φ (c j)) = gs (𝟙 T) t₀ ⊤ (c j) :=
      (gs_appLE π ⊤ _ le_top u t₀ hi (c j)).trans (by rw [hu])
    rw [LBGerm.gs_sub u t₀ _ hi, e1, e2, sub_self] at hu1
    exact not_isUnit_zero hu1
  refine ⟨fun j => DVR.SecOps.secAdd (s j) (DVR.SecOps.secNeg (DVR.SecOps.secScale (π.appTop.hom (c j)) (s i))),
    fun j h => h0 j ((hiff _ hi j).1 h), fun y hy => ?_⟩
  by_cases hyD : y ∈ Out.nonzeroLocus (s i)
  · by_contra hno
    push_neg at hno
    have hPy : ∀ j, r j - φ (c j) ∈ (hD.primeIdealOf ⟨y, hyD⟩).asIdeal := fun j => by
      by_contra h
      exact hno j ((hiff y hyD j).2 ((mem_basicOpen_iff_prime hD hyD _).2 h))
    have hQ : ∀ j, r j - φ (c j) ∈ (hD.primeIdealOf ⟨u t₀, hi⟩).asIdeal := fun j => by
      by_contra h
      exact h0 j ((mem_basicOpen_iff_prime hD hi _).2 h)
    have hb : ∀ z ∈ Out.nonzeroLocus (s i), ∀ x, z ∈ Y.basicOpen (φ x) ↔ π z ∈ T.basicOpen x := fun z hz x =>
      (LBGerm.isUnit_gs_iff (𝟙 Y) z _ hz (φ x)).symm.trans (by rw [hφ z hz]; exact LBGerm.isUnit_gs_iff π z ⊤ trivial x)
    have hPQ : ∀ x, φ x ∈ (hD.primeIdealOf ⟨y, hyD⟩).asIdeal ↔ φ x ∈ (hD.primeIdealOf ⟨u t₀, hi⟩).asIdeal := by
      intro x
      rw [← not_iff_not, ← mem_basicOpen_iff_prime hD hyD, ← mem_basicOpen_iff_prime hD hi, hb y hyD, hb _ hi,
        hT (π y) (π (u t₀))]
    have hE := ideal_eq_of_gen φ r c hs _ _ hPy hQ hPQ
    have e1 := hD.fromSpec_primeIdealOf ⟨y, hyD⟩
    have e2 := hD.fromSpec_primeIdealOf ⟨u t₀, hi⟩
    rw [PrimeSpectrum.ext hE] at e1
    exact hy (e1.symm.trans e2)
  · have hy' : y ∈ (⨆ i, Out.nonzeroLocus (s i)) := by rw [hcov]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
    obtain ⟨k, hk⟩ := exists_chart hP y
    refine ⟨j, ?_⟩
    rw [GlobalTheory.mem_nonzeroLocus_iff_isUnit _ hk, gs_secSubScale _ _ _ y k hk]
    exact isUnit_sub_mul_of_not_isUnit _ ((GlobalTheory.mem_nonzeroLocus_iff_isUnit (s j) hk).1 hj)
      fun h => hyD ((GlobalTheory.mem_nonzeroLocus_iff_isUnit (s i) hk).2 h)

theorem exists_sec_sep_origin : ∀ (K : Type) [Field K] (B : AbVar K) (L : LB B.X.left), L.IsLB →
    Out.RelAmple B.X L → ∃ N : ℕ, 1 ≤ N ∧ ∃ (M : ℕ) (t : Fin M → LB.Sec (Out.powOver B.X L ⊤ N)),
      (∀ j y, (B.X.hom ⁻¹ᵁ ⊤).ι y = B.origin → y ∉ Out.nonzeroLocus (t j)) ∧
      ∀ y, (B.X.hom ⁻¹ᵁ ⊤).ι y ≠ B.origin → ∃ j, y ∈ Out.nonzeroLocus (t j) := by
  intro K _ B L hL hA
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA ⊤ (isAffineOpen_top _)
  obtain ⟨t₀⟩ : Nonempty (⊤ : (Sp K).Opens).toScheme := ⟨⟨IsLocalRing.closedPoint K, trivial⟩⟩
  have hmem : unitU B t₀ ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  obtain ⟨hD, r, hr, hsurj⟩ := hs i
  obtain ⟨t, h1, h2⟩ := exists_sep_of_chart (B.X.hom ∣_ ⊤) (unitU B) (unitU_comp B) topU_pt_eq
    (LB.isLB_linComb hL _ _) s hcov i hD r hr hsurj t₀ hi
  have hinj : ∀ y, (B.X.hom ⁻¹ᵁ ⊤).ι y = B.origin → y = unitU B t₀ := fun y hy =>
    Subtype.ext ((Scheme.Opens.ι_apply _ _).symm.trans
      (hy.trans ((unitU_ι B t₀).symm.trans (Scheme.Opens.ι_apply _ _))))
  exact ⟨N, hN, M + 1, t, fun j y hy => hinj y hy ▸ h1 j, fun y hy => h2 y fun h => hy (h ▸ unitU_ι B t₀)⟩

end GlobalTheory.RelAmpleSep
