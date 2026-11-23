import Development.EtaleCohomology.EtaleTrace.GenInPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov.GenInPf

variable {k : Type} [Field k] {N : ℕ}

def pg {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN k N) (U : (PN k N).Opens)
    (hU : genericPoint X ∈ ι ⁻¹ᵁ U) : Γ(PN k N, U) →+* X.functionField :=
  (ι.app U ≫ X.presheaf.germ _ (genericPoint X) hU).hom

theorem pg_apply {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN k N) (U : (PN k N).Opens)
    (hU : genericPoint X ∈ ι ⁻¹ᵁ U) (s : Γ(PN k N, U)) :
    pg ι U hU s = X.presheaf.germ _ (genericPoint X) hU (ι.app U s) := rfl

theorem pg_res {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN k N) {U V : (PN k N).Opens} (hVU : V ≤ U)
    (hV : genericPoint X ∈ ι ⁻¹ᵁ V) (hU : genericPoint X ∈ ι ⁻¹ᵁ U) (s : Γ(PN k N, U)) :
    pg ι V hV ((PN k N).presheaf.map (homOfLE hVU).op s) = pg ι U hU s := by
  show (((PN k N).presheaf.map (homOfLE hVU).op ≫ ι.app V) ≫ X.presheaf.germ _ _ hV).hom s = _
  rw [Scheme.Hom.naturality, Category.assoc, TopCat.Presheaf.germ_res]
  rfl

theorem away_eq {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN k N) {n : ℕ}
    (f : MvPolynomial (Fin (N + 1)) k) (hf : f ∈ A k N n) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) f)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • n)) :
    away ι f hf h m g hg = pg ι _ h (Proj.awayToSection _ f (Away.mk _ hf m g hg)) := rfl

theorem away_identity (x f g : MvPolynomial (Fin (N + 1)) k) {n m : ℕ} (hx : x ∈ A k N 1) (hf : f ∈ A k N n)
    (hg : g ∈ A k N (m • n)) (hf' : f ∈ A k N (n • 1)) (hg' : g ∈ A k N ((m * n) • 1)) :
    awayMap (A k N) hx (show x * f = f * x from mul_comm _ _) (Away.mk _ hf m g hg) *
      awayMap (A k N) hf (show x * f = x * f from rfl) (Away.mk _ hx n f hf') ^ m =
      awayMap (A k N) hf (show x * f = x * f from rfl) (Away.mk _ hx (m * n) g hg') := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, awayMap_mk,
    Away.val_mk, Localization.mk_pow, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, OneMemClass.coe_one, one_mul]
  ring

theorem away_self_pow (x : MvPolynomial (Fin (N + 1)) k) (hx : x ∈ A k N 1) (n : ℕ)
    (h : x ^ n ∈ A k N (n • 1)) : Away.mk (A k N) hx n (x ^ n) h = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_one]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

theorem away_self_pow' (x : MvPolynomial (Fin (N + 1)) k) (hx : x ∈ A k N 1) {m n : ℕ} (hmn : m = n)
    (h : x ^ n ∈ A k N (m • 1)) : Away.mk (A k N) hx m (x ^ n) h = 1 := by
  subst hmn; exact away_self_pow x hx m h

theorem key {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN k N) (i : Fin (N + 1))
    (hi : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) {n : ℕ}
    (f : MvPolynomial (Fin (N + 1)) k) (hf : f ∈ A k N n) (hfη : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) f)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • n))
    (hf' : f ∈ A k N (n • 1)) (hg' : g ∈ A k N ((m * n) • 1)) :
    away ι f hf hfη m g hg * away ι (MvPolynomial.X i) (X_mem k N i) hi n f hf' ^ m =
      away ι (MvPolynomial.X i) (X_mem k N i) hi (m * n) g hg' := by
  have hF : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i * f) := by
    rw [Proj.basicOpen_mul]; exact ⟨hi, hfη⟩
  have e1 : ∀ y, pg ι _ hF (Proj.awayToSection _ (MvPolynomial.X i * f)
      (awayMap (A k N) hf (show MvPolynomial.X i * f = MvPolynomial.X i * f from rfl) y)) =
      pg ι _ hi (Proj.awayToSection _ (MvPolynomial.X i) y) := fun y => by
    have := congr($(Proj.awayMap_awayToSection (A k N) hf
      (show MvPolynomial.X i * f = MvPolynomial.X i * f from rfl)) y)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    erw [this]
    exact pg_res ι _ hF hi _
  have e2 : ∀ y, pg ι _ hF (Proj.awayToSection _ (MvPolynomial.X i * f)
      (awayMap (A k N) (X_mem k N i) (show MvPolynomial.X i * f = f * MvPolynomial.X i from mul_comm _ _) y)) =
      pg ι _ hfη (Proj.awayToSection _ f y) := fun y => by
    have := congr($(Proj.awayMap_awayToSection (A k N) (X_mem k N i)
      (show MvPolynomial.X i * f = f * MvPolynomial.X i from mul_comm _ _)) y)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    erw [this]
    exact pg_res ι _ hF hfη _
  rw [away_eq, away_eq, away_eq, ← e2, ← e1, ← e1, ← map_pow, ← map_mul, ← away_identity _ _ _ _ hf hg hf' hg',
    map_mul, map_pow]
  simp only [map_mul, map_pow]

theorem basicOpen_le (i : Fin (N + 1)) {n : ℕ} (hn : 0 < n) (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ A k N n) (hf' : f ∈ A k N (n • 1)) :
    (PN k N).basicOpen (Proj.awayToSection (A k N) (MvPolynomial.X i) (Away.mk _ (X_mem k N i) n f hf')) ≤
      Proj.basicOpen (A k N) f := by
  intro y hy
  have hyU : y ∈ Proj.basicOpen (A k N) (MvPolynomial.X i) := (PN k N).basicOpen_le _ hy
  let y' : (Proj.basicOpen (A k N) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)).toScheme := ⟨y, hyU⟩
  have h1 : y' ∈ (Proj.basicOpen (A k N) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)).ι ⁻¹ᵁ
      (PN k N).basicOpen (Proj.awayToSection (A k N) (MvPolynomial.X i) (Away.mk _ (X_mem k N i) n f hf')) := hy
  rw [← Scheme.Opens.toSpecΓ_preimage_basicOpen, ← SpecMap_preimage_basicOpen] at h1
  have ht : Away.isLocalizationElem (X_mem k N i) hf = Away.mk _ (X_mem k N i) n f hf' := by
    apply val_injective; simp [Away.val_mk]
  have h2 : y' ∈ Proj.basicOpenToSpec (A k N) (MvPolynomial.X i) ⁻¹ᵁ
      PrimeSpectrum.basicOpen (Away.isLocalizationElem (X_mem k N i) hf) := by
    rw [ht]; exact h1
  rw [← Proj.awayι_preimage_basicOpen (A k N) (X_mem k N i) one_pos hf hn, ← Scheme.Hom.comp_preimage,
    ← Proj.basicOpenIsoSpec_inv_ι _ _ (X_mem k N i) one_pos, ← Proj.basicOpenIsoSpec_hom _ _ (X_mem k N i) one_pos,
    Iso.hom_inv_id_assoc] at h2
  exact h2

theorem GenOfAway_of : GenOfAway := by
  intro k _ X _ p N ι hp i h hE n hn f hf
  have hf' : f ∈ A k N (n • 1) := by simpa using hf
  have hfv : away ι (MvPolynomial.X i) (X_mem k N i) h n f hf' = eval₂ (kHom p) (coordAt ι i h) f := hE n f hf'
  refine ⟨⟨fun hfη => ?_, fun hne => ?_⟩, fun m g hg hfη => ?_⟩
  · have hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ^ n ∈ A k N (1 • n) := by
      simpa using SetLike.pow_mem_graded n (X_mem k N i)
    have hx' : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ^ n ∈ A k N ((1 * n) • 1) := by
      simpa using SetLike.pow_mem_graded n (X_mem k N i)
    have h1 : away ι (MvPolynomial.X i) (X_mem k N i) h (1 * n) _ hx' = 1 := by
      rw [away_eq, away_self_pow' _ _ (one_mul n), map_one, map_one]
    have := key ι i h f hf hfη 1 _ hx hf' hx'
    rw [h1, hfv] at this
    intro h0
    rw [h0] at this
    simp at this
  · have hu : IsUnit (X.presheaf.germ _ (genericPoint X) h
        (ι.app _ (Proj.awayToSection _ (MvPolynomial.X i) (Away.mk _ (X_mem k N i) n f hf')))) := by
      rw [← hfv] at hne; exact isUnit_iff_ne_zero.mpr hne
    rw [← Scheme.mem_basicOpen, ← Scheme.preimage_basicOpen] at hu
    exact basicOpen_le i hn f hf hf' hu
  · have hg' : g ∈ A k N ((m * n) • 1) := by simpa using hg
    have := key ι i h f hf hfη m g hg hf' hg'
    rw [hfv, hE (m * n) g hg'] at this
    exact this

end LateralTheory.EtaleTrace.Cov.GenInPf
