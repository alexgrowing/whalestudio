import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.ThetaAmple

theorem opens_le_of_points {Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] {U V : Y.Opens}
    (h : ∀ x : Sp ℂ ⟶ Y, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V := by
  intro y hy
  by_contra hV
  obtain ⟨x, hx, hZ⟩ := ComplexPoints.exists_point_mem (K := ℂ) p (Z := (U : Set Y) ∩ (V : Set Y)ᶜ)
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨y, hy, hV⟩
  exact (hZ _).2 ((top_le_preimage_iff_mem x V).1 (h x hx ((top_le_preimage_iff_mem x U).2 (hZ _).1)))

theorem top_le_preimage_iSup {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {κ : Type} (U : κ → Y.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (⨆ k, U k) ↔ ∃ k, ⊤ ≤ x ⁻¹ᵁ U k := by
  simp only [top_le_preimage_iff_mem]
  exact TopologicalSpace.Opens.mem_iSup

theorem top_le_preimage_wchart {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) {N : ℕ} (j : Fin N → L.ι) (x : Sp ℂ ⟶ Y) :
    ⊤ ≤ x ⁻¹ᵁ (LB.LinComb L (K := Fin N) (fun _ => φ) (fun _ => 1)).U j ↔ ∀ k, ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U (j k) := by
  simp only [top_le_preimage_iff_mem]
  exact Set.mem_iInter

theorem valAt'_linComb_g {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) {N : ℕ} (j j' : Fin N → L.ι) (x : Sp ℂ ⟶ Y)
    (h : ⊤ ≤ x ⁻¹ᵁ ((LB.LinComb L (K := Fin N) (fun _ => φ) (fun _ => 1)).U j ⊓
      (LB.LinComb L (K := Fin N) (fun _ => φ) (fun _ => 1)).U j')) :
    valAt' x _ ((LB.LinComb L (K := Fin N) (fun _ => φ) (fun _ => 1)).g j j').val =
      ∏ k, valAt' (x ≫ φ) _ (L.g (j k) (j' k)).val := by
  refine (valAt'_units_prod x h _ _).trans (Finset.prod_congr rfl fun k _ => ?_)
  rw [zpow_one]
  exact (valAt'_map x _ _ h).trans (valAt'_comp x φ (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val)

theorem relAmple_of_top {X : Over (Sp ℂ)} {L : LB X.left}
    (h : ∃ N : ℕ, 1 ≤ N ∧ ∃ M : ℕ, ∃ s : Fin (M + 1) → LB.Sec (Out.powOver X L ⊤ N),
      (⨆ i, Out.nonzeroLocus (s i) = ⊤) ∧
      ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧
        ∃ r : Fin (M + 1) → Γ((X.hom ⁻¹ᵁ ⊤).toScheme, Out.nonzeroLocus (s i)),
          (∀ j k, ((X.hom ⁻¹ᵁ ⊤).toScheme.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ (Out.powOver X L ⊤ N).U k ≤ (Out.powOver X L ⊤ N).U k)).op).hom
                ((s j).f k) =
            ((X.hom ⁻¹ᵁ ⊤).toScheme.presheaf.map (homOfLE (inf_le_left :
              Out.nonzeroLocus (s i) ⊓ (Out.powOver X L ⊤ N).U k ≤ Out.nonzeroLocus (s i))).op).hom (r j) *
            ((X.hom ⁻¹ᵁ ⊤).toScheme.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ (Out.powOver X L ⊤ N).U k ≤ (Out.powOver X L ⊤ N).U k)).op).hom
                ((s i).f k)) ∧
          Function.Surjective (MvPolynomial.eval₂Hom
            ((X.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom r)) : Out.RelAmple X L := by
  intro U hU
  by_cases hne : (default : PrimeSpectrum ℂ) ∈ U
  · have : U = ⊤ := top_le_iff.1 fun p _ => by
      rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) p default]
    subst this
    exact h
  · have he : IsEmpty (X.hom ⁻¹ᵁ U).toScheme := ⟨fun y => hne (by
      have := y.2
      rwa [← Subsingleton.elim (α := PrimeSpectrum ℂ) (X.hom y.1) default])⟩
    have hb : ∀ V : (X.hom ⁻¹ᵁ U).toScheme.Opens, V = ⊥ := fun V => le_bot_iff.1 fun y _ => he.elim y
    have hs : ∀ V : (X.hom ⁻¹ᵁ U).toScheme.Opens, Subsingleton Γ((X.hom ⁻¹ᵁ U).toScheme, V) := fun V => by
      rw [hb V]; infer_instance
    refine ⟨1, le_rfl, 0, fun _ => ⟨fun _ => 0, fun _ _ => Subsingleton.elim _ _⟩, (hb _).trans (hb _).symm,
      fun i => ⟨by rw [hb (Out.nonzeroLocus _)]; exact isAffineOpen_bot _, fun _ => 0,
        fun _ _ => Subsingleton.elim _ _, fun d => ⟨0, Subsingleton.elim _ _⟩⟩⟩

theorem relAmple_of_values
    (hext : ∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens)
      (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U →
        valAt' x.left U f = valAt' x.left U f') → f = f')
    {X : Over (Sp ℂ)} [IsReduced X.left] [LocallyOfFiniteType X.hom] {L : LB X.left} (hL : L.IsLB)
    {Z κ : Type} [Fintype κ] [Nonempty κ] (ex : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (hex : Function.Surjective ex)
    (fr : L.ι → Z → ℂ) (fr_ne : ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i → fr i z ≠ 0)
    (fr_compat : ∀ i j z, ⊤ ≤ (ex z).left ⁻¹ᵁ (L.U i ⊓ L.U j) →
      fr i z = valAt' (ex z).left (L.U i ⊓ L.U j) (L.g i j).val * fr j z)
    (f : κ → Z → ℂ) {N : ℕ} (hN : 1 ≤ N)
    (hsec : ∀ c (j : Fin N → L.ι), ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z,
      (∀ k, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U (j k)) →
        ⊤ ≤ (ex z).left ⁻¹ᵁ U ∧ valAt' (ex z).left U φ = f c z * ∏ k, fr (j k) z)
    (D : κ → X.left.Opens) (hcov : ⨆ c, D c = ⊤) (haff : ∀ c, IsAffineOpen (D c))
    (hD : ∀ c z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ f c z ≠ 0) (r : ∀ c, κ → Γ(X.left, D c))
    (hr : ∀ c c' z, f c z ≠ 0 → valAt' (ex z).left (D c) (r c c') = f c' z / f c z)
    (hgen : ∀ c (t : Γ(X.left, D c)), ∃ F : MvPolynomial κ ℂ, t = MvPolynomial.eval₂
      (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) (r c) F) :
    Out.RelAmple X L := by
  apply relAmple_of_top
  obtain ⟨M, ⟨e⟩⟩ : ∃ M : ℕ, Nonempty (Fin (M + 1) ≃ κ) :=
    ⟨Fintype.card κ - 1, ⟨(finCongr (Nat.sub_add_cancel Fintype.card_pos)).trans (Fintype.equivFin κ).symm⟩⟩
  let ψ : (X.hom ⁻¹ᵁ ⊤).toScheme ⟶ X.left := (X.hom ⁻¹ᵁ ⊤).ι
  have hiso : IsIso ψ := inferInstanceAs (IsIso X.left.topIso.hom)
  have hpt : ∀ x : Sp ℂ ⟶ (X.hom ⁻¹ᵁ ⊤).toScheme, x ≫ ψ ≫ X.hom = 𝟙 _ → ∃ z, x ≫ ψ = (ex z).left := by
    intro x hx
    obtain ⟨z, hz⟩ := hex (Over.homMk (x ≫ ψ) ((Category.assoc _ _ _).trans hx))
    exact ⟨z, by rw [hz]; rfl⟩
  have ext : ∀ (U : (X.hom ⁻¹ᵁ ⊤).toScheme.Opens) (a b : Γ((X.hom ⁻¹ᵁ ⊤).toScheme, U)),
      (∀ (x : Sp ℂ ⟶ (X.hom ⁻¹ᵁ ⊤).toScheme) z, x ≫ ψ = (ex z).left → ⊤ ≤ x ⁻¹ᵁ U →
        valAt' x U a = valAt' x U b) → a = b := by
    intro U a b h
    refine hext (Over.mk (ψ ≫ X.hom)) (inferInstanceAs (IsReduced (X.hom ⁻¹ᵁ ⊤).toScheme))
      (inferInstanceAs (LocallyOfFiniteType (ψ ≫ X.hom))) U a b fun x hx => ?_
    obtain ⟨z, hz⟩ := hpt x.left (Over.w x)
    exact h x.left z hz hx
  have le : ∀ (U V : (X.hom ⁻¹ᵁ ⊤).toScheme.Opens),
      (∀ (x : Sp ℂ ⟶ (X.hom ⁻¹ᵁ ⊤).toScheme) z, x ≫ ψ = (ex z).left → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) → U ≤ V := by
    intro U V h
    refine opens_le_of_points (ψ ≫ X.hom) fun x hx => ?_
    obtain ⟨z, hz⟩ := hpt x hx
    exact h x z hz
  have hch : ∀ (x : Sp ℂ ⟶ (X.hom ⁻¹ᵁ ⊤).toScheme) z, x ≫ ψ = (ex z).left → ∀ j : Fin N → L.ι,
      (⊤ ≤ x ⁻¹ᵁ (Out.powOver X L ⊤ N).U j ↔ ∀ k, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U (j k)) := by
    intro x z hz j
    rw [← hz]
    exact top_le_preimage_wchart L ψ j x
  choose U φ hφ using hsec
  have hU : ∀ c j, (Out.powOver X L ⊤ N).U j ≤ ψ ⁻¹ᵁ U c j := fun c j => le _ _ fun x z hz hx => by
    rw [← top_le_preimage_comp, hz]
    exact (hφ c j z ((hch x z hz j).1 hx)).1
  have hv : ∀ c j (x : Sp ℂ ⟶ (X.hom ⁻¹ᵁ ⊤).toScheme) z, x ≫ ψ = (ex z).left →
      ⊤ ≤ x ⁻¹ᵁ (Out.powOver X L ⊤ N).U j →
      valAt' x _ ((ψ.appLE _ _ (hU c j)).hom (φ c j)) = f c z * ∏ k, fr (j k) z := fun c j x z hz hx => by
    rw [valAt'_appLE x ψ _ _ _ _ hx, hz]
    exact (hφ c j z ((hch x z hz j).1 hx)).2
  let s : κ → LB.Sec (Out.powOver X L ⊤ N) := fun c =>
    ⟨fun j => (ψ.appLE _ _ (hU c j)).hom (φ c j), fun j j' => ext _ _ _ fun x z hz hx => by
      have hx' := (top_le_preimage_inf x _ _).1 hx
      rw [valAt'_mul, valAt'_map x _ _ hx, valAt'_map x _ _ hx, hv c j x z hz hx'.1, hv c j' x z hz hx'.2]
      refine Eq.trans ?_ (congrArg (· * _) (valAt'_linComb_g L ψ j j' x hx).symm)
      rw [hz, mul_left_comm, ← Finset.prod_mul_distrib]
      refine congrArg _ (Finset.prod_congr rfl fun k _ => fr_compat _ _ z ?_)
      exact (top_le_preimage_inf _ _ _).2 ⟨(hch x z hz j).1 hx'.1 k, (hch x z hz j').1 hx'.2 k⟩⟩
  have hnz : ∀ c (x : Sp ℂ ⟶ (X.hom ⁻¹ᵁ ⊤).toScheme) z, x ≫ ψ = (ex z).left →
      (⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus (s c) ↔ f c z ≠ 0) := by
    intro c x z hz
    refine (top_le_preimage_iSup x _).trans ⟨fun ⟨j, hj⟩ => ?_, fun h => ?_⟩
    · have h1 := (top_le_preimage_basicOpen_iff x _ _).1 hj
      have h2 := hv c j x z hz (top_le_preimage_of_valAt'_ne_zero x h1)
      exact left_ne_zero_of_mul (h2 ▸ h1)
    · obtain ⟨i, hi⟩ := (top_le_preimage_iSup (ex z).left L.U).1 (by rw [hL.cover]; exact le_top)
      refine ⟨fun _ => i, (top_le_preimage_basicOpen_iff x _ _).2 ?_⟩
      refine (hv c (fun _ => i) x z hz ((hch x z hz _).2 fun _ => hi)).trans_ne ?_
      exact mul_ne_zero h (Finset.prod_ne_zero_iff.2 fun _ _ => fr_ne i z hi)
  have loc : ∀ c, Out.nonzeroLocus (s c) = ψ ⁻¹ᵁ D c := fun c => by
    refine le_antisymm (le _ _ fun x z hz hx => ?_) (le _ _ fun x z hz hx => ?_)
    · rw [← top_le_preimage_comp, hz]
      exact (hD c z).2 ((hnz c x z hz).1 hx)
    · rw [← top_le_preimage_comp, hz] at hx
      exact (hnz c x z hz).2 ((hD c z).1 hx)
  refine ⟨N, hN, M, fun i => s (e i), ?_, fun i => ⟨?_, fun j => (ψ.appLE _ _ (loc (e i)).le).hom (r (e i) (e j)),
    fun j k => ext _ _ _ fun x z hz hx => ?_, ?_⟩⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 (show ψ y ∈ ⨆ c, D c by rw [hcov]; trivial)
    obtain ⟨i, rfl⟩ := e.surjective c
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hc⟩
  · rw [loc]; exact (haff _).preimage ψ
  · have hx' := (top_le_preimage_inf x _ _).1 hx
    have h0 := (hnz _ x z hz).1 hx'.1
    rw [valAt'_mul, valAt'_map x _ _ hx, valAt'_map x _ _ hx, valAt'_map x _ _ hx, valAt'_appLE x ψ _ _ _ _ hx'.1, hz,
      hr _ _ z h0]
    refine (hv _ k x z hz hx'.2).trans (Eq.trans ?_ (congrArg (_ * ·) (hv _ k x z hz hx'.2).symm))
    field_simp
  · have hap : IsIso (ψ.appLE _ _ (loc (e i)).le) := by
      have key : ∀ V (h : V = ψ ⁻¹ᵁ D (e i)), IsIso (ψ.appLE _ V h.le) := by
        rintro _ rfl
        rw [Scheme.Hom.appLE_eq_app]
        infer_instance
      exact key _ (loc _)
    let θ : CommRingCat.of ℂ ⟶ Γ((⊤ : (Sp ℂ).Opens).toScheme, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (⊤ : (Sp ℂ).Opens).ι.appLE ⊤ ⊤ le_top
    have hc : (ψ.appLE _ _ (loc (e i)).le).hom.comp (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) =
        ((X.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s (e i))) le_top).hom.comp θ.hom := by
      have e₁ := Scheme.Hom.appLE_comp_appLE ψ X.hom ⊤ (D (e i)) _ le_top (loc (e i)).le
      have e₂ := Scheme.Hom.appLE_comp_appLE (X.hom ∣_ ⊤) (⊤ : (Sp ℂ).Opens).ι ⊤ ⊤
        (Out.nonzeroLocus (s (e i))) le_top le_top
      have e₃ : ∀ (a b : (X.hom ⁻¹ᵁ ⊤).toScheme ⟶ Sp ℂ), a = b →
          a.appLE ⊤ (Out.nonzeroLocus (s (e i))) le_top = b.appLE ⊤ (Out.nonzeroLocus (s (e i))) le_top := by
        rintro _ _ rfl; rfl
      have e₄ := e₁.trans ((e₃ _ _ (morphismRestrict_ι X.hom ⊤).symm).trans e₂.symm)
      ext a
      exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) e₄
    intro d
    obtain ⟨d, rfl⟩ := (ConcreteCategory.bijective_of_isIso (ψ.appLE _ _ (loc (e i)).le)).2 d
    obtain ⟨F, rfl⟩ := hgen _ d
    refine ⟨MvPolynomial.map θ.hom (MvPolynomial.rename e.symm F), ?_⟩
    rw [MvPolynomial.eval₂Hom_map_hom, ← hc, MvPolynomial.eval₂Hom_rename]
    refine Eq.trans ?_ (MvPolynomial.map_eval₂Hom _ (r (e i)) (ψ.appLE _ _ (loc (e i)).le).hom F).symm
    congr 2
    funext c
    simp

theorem two_mul_dot_int {g : ℕ} {a : Fin g → ℝ} (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (n : Fin g → ℤ) :
    ∃ k : ℤ, 2 * (ofRealVec a ⬝ᵥ ofIntVec n) = k := by
  have : ∀ i, ∃ k : ℤ, 2 * (a i : ℂ) = k := fun i => by
    rcases ha i with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose k hk using this
  refine ⟨∑ i, k i * n i, ?_⟩
  simp only [dotProduct, ofRealVec, ofIntVec, Finset.mul_sum, Int.cast_sum, Int.cast_mul, ← hk, _root_.mul_assoc]

theorem eC_nat_mul' (N : ℕ) (x : ℂ) : eC (N * x) = eC x ^ N := by
  rw [eC, eC, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem autFactor_pow_even {g : ℕ} {a b : Fin g → ℝ} (ha : ∀ i, a i = 0 ∨ a i = 1 / 2)
    (hb : ∀ i, b i = 0 ∨ b i = 1 / 2) (τ : Matrix (Fin g) (Fin g) ℂ) (n n' : Fin g → ℤ) (z : Fin g → ℂ) {N : ℕ}
    (hN : Even N) : autFactor a b τ n n' z ^ N =
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) := by
  obtain ⟨m, rfl⟩ := hN
  obtain ⟨k, hk⟩ := two_mul_dot_int ha n'
  obtain ⟨l, hl⟩ := two_mul_dot_int hb n
  rw [autFactor, mul_pow, ← eC_nat_mul', ← eC_nat_mul']
  have : ((m + m : ℕ) : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec n' - ofRealVec b ⬝ᵥ ofIntVec n) = ((m * (k - l) : ℤ) : ℂ) := by
    push_cast
    rw [← hk, ← hl]
    ring
  rw [this, eC_int, _root_.one_mul]
  congr 1
  ring

theorem level_add {N : ℕ} (w : ℂ) :
    eC (-((N * (N + 1) : ℕ) : ℂ) * w) = eC (-(N : ℂ) * w) * eC (-(N : ℂ) * w) ^ N := by
  rw [← pow_succ', ← eC_nat_mul']
  congr 1
  push_cast
  ring

theorem prod_level {N : ℕ} (w t t' : ℂ) (h h' : Fin N → ℂ) (ht : t' = eC (-(N : ℂ) * w) * t)
    (hh : ∀ k, h' k = eC (-(N : ℂ) * w) * h k) :
    t' * ∏ k, h' k = eC (-((N * (N + 1) : ℕ) : ℂ) * w) * (t * ∏ k, h k) := by
  simp only [ht, hh, level_add, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem prod_level' {N : ℕ} (w α : ℂ) (F F' : Fin N → ℂ) (hα : α ^ N = eC (-(N : ℂ) * w))
    (hF : ∀ k, F' k = α * eC (-(N : ℂ) * w) * F k) :
    ∏ k, F' k = eC (-((N * (N + 1) : ℕ) : ℂ) * w) * ∏ k, F k := by
  simp only [hF, hα, level_add, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem relAmple_thetaBundle : (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧ (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g → ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠ 0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → Even N → ∀ [GrpObj X], (∀ z w, ex (z + w) = ex z * ex w) → ∀ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∀ (L : LB X.left) (u : HolUnif X L g), L.IsLB → (u.ex = ex ∧ (∀ z, z ∈ u.Λ ↔ z ∈ periodLattice τ) ∧ (∀ (n n' : Fin g → ℤ) i z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i → u.fr i z = autFactor a b τ n n' z * u.fr i (z + τ *ᵥ ofIntVec n + ofIntVec n')) ∧ (∀ i, ∃ h F : (Fin g → ℂ) → ℂ, (Differentiable ℂ h ∧ ∀ (n n' : Fin g → ℤ) z, h (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * h z) ∧ Differentiable ℂ F ∧ (∀ (n n' : Fin g → ℤ) z, F (z + τ *ᵥ ofIntVec n + ofIntVec n') = autFactor a b τ n n' z * eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F z) ∧ ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ L.U i ↔ h z ≠ 0 ∧ F z ≠ 0) ∧ u.fr i z = h z / F z)) → Out.RelAmple X L) := by
  rintro hext hth g τ hτ N hN X ex D ⟨hint, hprop, hex, _, _, hD, hcov⟩ hquot heven _ _ a b ha hb L u hL
    ⟨hu, _, _, hfr⟩
  subst hu
  have hN₁ : 1 ≤ N := le_trans (by decide) hN
  have : Nonempty (Fin N) := ⟨⟨0, hN₁⟩⟩
  choose h F hh hFd hF hz using hfr
  choose haff _ hDz r hr hgen using hD
  have hth' := (hth g τ hτ N hN₁).1
  clear hth
  obtain ⟨f, hf⟩ : ∃ f : (Fin g → Fin N) → (Fin g → ℂ) → ℂ, ∀ c z,
      theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) = f c z := ⟨_, fun _ _ => rfl⟩
  simp only [hf] at hth' hDz hr
  refine relAmple_of_values hext hL u.ex hex u.fr u.fr_ne u.fr_compat
    f hN₁
    (fun c j => ?_) D hcov haff hDz r hr hgen
  obtain ⟨hd, hq⟩ := hth' c
  have hp : ∀ G : Fin N → (Fin g → ℂ) → ℂ, (∀ k, Differentiable ℂ (G k)) →
      Differentiable ℂ fun z => ∏ k, G k z := fun G hG => by fun_prop
  obtain ⟨U, φ, hφ⟩ := hquot (N + 1)
    (fun z => f c z * ∏ k, h (j k) z)
    (fun z => ∏ k, F (j k) z)
    ⟨Differentiable.fun_mul hd (hp _ fun k => (hh (j k)).1), fun n n' z =>
      prod_level _ _ _ _ _ (hq n n' z) fun k => (hh (j k)).2 n n' z⟩
    ⟨hp _ fun k => hFd (j k), fun n n' z =>
      prod_level' _ _ _ _ (autFactor_pow_even ha hb τ n n' z heven) fun k => hF (j k) n n' z⟩
  refine ⟨U, φ, fun z hj => ?_⟩
  have hne : ∏ k, F (j k) z ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => ((hz (j k) z).1.1 (hj k)).2
  refine ⟨(hφ z).1.2 hne, ((hφ z).2 hne).trans ?_⟩
  rw [Finset.prod_congr rfl fun k _ => (hz (j k) z).2, Finset.prod_div_distrib, mul_div_assoc]

end GlobalTheory.ThetaAmple
