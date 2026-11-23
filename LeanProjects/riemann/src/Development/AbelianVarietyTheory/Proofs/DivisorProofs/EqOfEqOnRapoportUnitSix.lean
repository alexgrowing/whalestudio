import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AgreeOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularRuleExtOfLevelTwelveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAffineDeterminantGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenLocalFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantGeneratorRuleBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatNormalFibersOpenExtensionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult

theorem eq_zero_of_forall_away {R : Type} [CommRing R] (d : R)
    (h : ∀ p : PrimeSpectrum R, ∃ f : R, f ∉ p.asIdeal ∧ algebraMap R (Localization.Away f) d = 0) : d = 0 := by
  set I : Submodule R R := (Submodule.span R {d}).annihilator
  by_cases hI : I = ⊤
  · have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    simpa using (Submodule.mem_annihilator_span_singleton d 1).1 h1
  · obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨f, hf, hfd⟩ := h ⟨m, hm.isPrime⟩
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f)] at hfd
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := hfd
    have : f ^ n ∈ I := (Submodule.mem_annihilator_span_singleton d _).2 (by simpa [smul_eq_mul] using hn)
    exact (hf (hm.isPrime.mem_of_pow_mem n (hle this))).elim

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem Rule.agreeOn_of_isRapoport {R₀ : Type} [CommRing R₀] {k : ℕ} (s t : Rule (unitObj 𝔠 6) R₀ k)
    (hst : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : IsUnit ((6 : ℕ) : R)), X.IsRapoport →
      ∀ δ : X.DetGen, s.val R X h δ = t.val R X h δ)
    {A : Type} [CommRing A] (Y : Obj F 𝔠 (Sp A)) (hY : Y.IsRapoport) : s.AgreeOn t Y :=
  fun B _ _ σ Y' _ hY' h δ ↦ hst B Y' h (hY'.isRapoport σ hY) δ

theorem isRapoport_of_le_rapLocus {M : Scheme.{0}} (U : Obj F 𝔠 M) (V : M.Opens) (hV : (V : Set M) = U.rapLocus)
    (W : M.Opens) (hW : IsAffineOpen W) (hle : W ≤ V) (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left)
    (hY : Y.IsPullBy U hW.fromSpec φ) : Y.IsRapoport := by
  rw [Obj.isRapoport_iff]
  refine Set.eq_univ_of_forall fun x K _ t hx Z ψ hZ ↦ ?_
  have hmem : hW.fromSpec x ∈ U.rapLocus := by
    rw [← hV]; apply hle; show hW.fromSpec x ∈ (W : Set M); rw [← hW.range_fromSpec]; exact ⟨x, rfl⟩
  refine hmem K (t ≫ hW.fromSpec) ?_ Z (ψ ≫ φ) (hZ.comp hY)
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, rfl⟩

theorem isUnit_six_of_away {M : Scheme.{0}} (sM : M ⟶ Sp (Localization.Away (12 : ℤ))) (W : M.Opens) :
    IsUnit ((6 : ℕ) : Γ(M, W)) := by
  have h12 : IsUnit (algebraMap ℤ (Localization.Away (12 : ℤ)) 12) := IsLocalization.Away.algebraMap_isUnit _
  have h6 : IsUnit ((6 : ℕ) : Localization.Away (12 : ℤ)) := by
    have : algebraMap ℤ (Localization.Away (12 : ℤ)) 12 = ((6 : ℕ) : Localization.Away (12 : ℤ)) * 2 := by
      simp; norm_num
    rw [this] at h12
    exact isUnit_of_mul_isUnit_left h12
  let g : Localization.Away (12 : ℤ) →+* Γ(M, W) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (12 : ℤ)))).inv ≫ sM.appTop ≫
      M.presheaf.map (homOfLE le_top).op).hom
  have := h6.map g
  rwa [map_natCast] at this

end GlobalTheory.RealMult

namespace GlobalTheory.RealMult

theorem Rule.eq_of_eq_on_rapoport_unit_six : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
  (R₀ : Type) [CommRing R₀] (k : ℕ) (s t : Rule (unitObj 𝔠 6) R₀ k),
  (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : IsUnit ((6 : ℕ) : R)), X.IsRapoport →
    ∀ δ : X.DetGen, s.val R X h δ = t.val R X h δ) → s = t := by
  intro hDP F _ _ _ 𝔠 R₀ _ k s t hst
  obtain ⟨M, sM, U, αU, hfine, -, -, -, hflat, -, ⟨V, hV, -, -, hcod⟩, hnorm, -⟩ := hDP F 𝔠 12 (by norm_num)
  have hchart : ∀ (W : M.Opens) (hW : IsAffineOpen W) (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left),
      Y.IsPullBy U hW.fromSpec φ → Nonempty Y.DetGen → s.AgreeOn t Y := by
    intro W hW Y φ hY hgen
    exact GlobalTheory.T.determinant_generator_rule_base_change F 𝔠 R₀ k s t Γ(M, W) Y hgen
      (GlobalTheory.T.flat_normal_fibers_open_extension F 𝔠 R₀ k s t 12 M sM U V hflat hnorm hcod W hW
        (fun W' hW' hle Y' φ' hY' ↦ Rule.agreeOn_of_isRapoport s t hst Y'
          (isRapoport_of_le_rapLocus U V hV W' hW' (hle.trans inf_le_right) Y' φ' hY')) Y φ hY)
      (isUnit_six_of_away sM W)
  apply GlobalTheory.T.modular_rule_ext_of_level_twelve F 𝔠 R₀ k s t
  intro R _ _ X h6 ⟨α⟩ δ
  have h6' : IsUnit (6 : R) := by exact_mod_cast h6
  have h2 : IsUnit (2 : R) := isUnit_of_mul_isUnit_left (y := (3 : R)) (by norm_num; exact h6')
  have h12 : IsUnit ((Int.castRingHom R) 12) := by
    have : (Int.castRingHom R) 12 = 6 * 2 := by simp; norm_num
    rw [this]; exact h6'.mul h2
  let τ : Localization.Away (12 : ℤ) →+* R := IsLocalization.Away.lift (12 : ℤ) h12
  obtain ⟨b, -, φ, hφ, -⟩ := (hfine (Sp R) (spMap τ) X α).exists
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_away
  intro p
  obtain ⟨W, hW, hy, Y, ψ, hY, hgen⟩ := GlobalTheory.T.local_affine_determinant_generator F 𝔠 M U (b p)
  obtain ⟨f, g, hp, hg⟩ := GlobalTheory.T.affine_open_local_factorization M W hW R b p hy
  obtain ⟨Xf, φf, hXf⟩ := Obj.exists_isPullBy X (spMap (algebraMap R (Localization.Away f)))
  obtain ⟨δf, hδf, -⟩ := hXf.existsUnique_detGen _ δ
  have hXfU := hXf.comp hφ
  rw [← hg] at hXfU
  obtain ⟨χ, hχ, -⟩ := hXfU.cancel hY
  have h6f : IsUnit ((6 : ℕ) : Localization.Away f) := by
    have := h6.map (algebraMap R (Localization.Away f))
    rwa [map_natCast] at this
  refine ⟨f, hp, ?_⟩
  have e1 := s.baseChange R (Localization.Away f) (IsScalarTower.toAlgHom R₀ R _) X h6 Xf h6f φf δ δf hXf hδf
  have e2 := t.baseChange R (Localization.Away f) (IsScalarTower.toAlgHom R₀ R _) X h6 Xf h6f φf δ δf hXf hδf
  simp only [IsScalarTower.coe_toAlgHom'] at e1 e2
  rw [map_sub, ← e1, ← e2]
  exact sub_eq_zero.2 (hchart W hW Y ψ hY hgen _ g Xf χ hχ h6f δf)
end GlobalTheory.RealMult
