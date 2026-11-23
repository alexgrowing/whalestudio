import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RTensorEqZeroOfRestrictAffineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefSpecMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSectionOfCoefficientSpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantGeneratorLocallyExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientSpecRestrictionCompatibleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.QUniq

theorem eq_of_loc_two_three (R : Type) [CommRing R] (x y : R)
    (h2 : algebraMap R (Localization.Away (2 : R)) x = algebraMap R (Localization.Away (2 : R)) y)
    (h3 : algebraMap R (Localization.Away (3 : R)) x = algebraMap R (Localization.Away (3 : R)) y) : x = y := by
  rw [← sub_eq_zero]
  rw [← sub_eq_zero, ← map_sub] at h2 h3
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (2 : R)) _ _).1 h2
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (3 : R)) _ _).1 h3
  have hc : IsCoprime ((2 : R) ^ n) ((3 : R) ^ m) := by
    have : IsCoprime (2 : R) 3 := ⟨-1, 1, by norm_num⟩
    exact this.pow
  obtain ⟨a, b, hab⟩ := hc
  simp only at hn hm
  calc x - y = (a * 2 ^ n + b * 3 ^ m) * (x - y) := by rw [hab, _root_.one_mul]
    _ = a * (2 ^ n * (x - y)) + b * (3 ^ m * (x - y)) := by ring
    _ = 0 := by rw [hn, hm]; ring

theorem eq_of_loc_away (R : Type) [CommRing R] (f : PrimeSpectrum R → R) (hf : ∀ p, f p ∉ p.asIdeal)
    (x y : R) (h : ∀ p, algebraMap R (Localization.Away (f p)) x = algebraMap R (Localization.Away (f p)) y) :
    x = y := by
  rw [← sub_eq_zero]
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R (x - y))
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hI
    let p : PrimeSpectrum R := ⟨q, hq.isPrime⟩
    have hp := h p
    rw [← sub_eq_zero, ← map_sub] at hp
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f p)) _ _).1 hp
    have hmem : f p ^ n ∈ I := by
      simp only [I, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul]
      exact hn
    exact hf p (hq.isPrime.mem_of_pow_mem n (hIq hmem))
  have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem isRapoport_of_range_subset {M : Scheme.{0}} (U : Obj F 𝔠 M) {A : Type} [CommRing A] (c : Sp A ⟶ M)
    (X : Obj F 𝔠 (Sp A)) (φ : X.A.left ⟶ U.A.left) (hX : X.IsPullBy U c φ) (hr : Set.range c ⊆ U.rapLocus) :
    X.IsRapoport := by
  rw [Obj.isRapoport_iff]
  refine Set.eq_univ_of_forall fun s ↦ ?_
  intro K _ t hs Y ψ hY
  obtain ⟨p, rfl⟩ := hs
  exact hr ⟨t p, rfl⟩ K (t ≫ c) ⟨p, rfl⟩ Y (ψ ≫ φ) (hY.comp hX)

theorem agreeAt_on_model : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (N : ℕ) (M : Scheme.{0})
    (sM : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (V : M.Opens), (V : Set M) = U.rapLocus → Flat sM →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback sM t)) →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback sM t)),
      pullback.fst sM t y ∉ V → 2 ≤ ringKrullDim ((pullback sM t).presheaf.stalk y)) →
    ∀ (R₀ : Type) [CommRing R₀] (k : ℕ) (r s : Rule (trivialObjectCondition 𝔠) R₀ k),
    (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → r.AgreeAt s X) →
    ∀ (W : M.Opens) (hW : IsAffineOpen W) (X : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W)))) (φ : X.A.left ⟶ U.A.left),
      X.IsPullBy U (coefSpecMap hW R₀) φ → r.AgreeAt s X := by
  intro F _ _ 𝔠 N M sM U V hV hflat hnorm hcod R₀ _ k r s hrap W hW X φ hX δ
  rw [← sub_eq_zero]
  have key : TensorProduct.comm ℤ R₀ Γ(M, W) (r.val _ X trivial δ - s.val _ X trivial δ) = 0 := by
    refine rTensor_eq_zero_of_restrict_affine_inf N M sM V hflat hnorm hcod W hW R₀ _ fun W' hW' hle ↦ ?_
    let ρ : R₀ ⊗[ℤ] Γ(M, W) →ₐ[R₀] R₀ ⊗[ℤ] Γ(M, W') :=
      Algebra.TensorProduct.map (AlgHom.id R₀ R₀) (M.presheaf.map (homOfLE (hle.trans inf_le_left)).op).hom.toIntAlgHom
    obtain ⟨X', φ', hX'⟩ := Obj.exists_isPullBy X (spMap ρ.toRingHom)
    obtain ⟨δ', hδ', -⟩ := Obj.IsPullBy.existsUnique_detGen (R := R₀ ⊗[ℤ] Γ(M, W)) (R' := R₀ ⊗[ℤ] Γ(M, W')) _ hX' δ
    have hU : X'.IsPullBy U (coefSpecMap hW' R₀) (φ' ≫ φ) := by
      rw [← GlobalTheory.T.coefficient_spec_restriction_compatible M W W' hW hW' (hle.trans inf_le_left) R₀]; exact hX'.comp hX
    have hrng : Set.range (coefSpecMap hW' R₀) ⊆ U.rapLocus := by
      rintro _ ⟨y, rfl⟩
      rw [← hV]
      have : (coefSpecMap hW' R₀) y ∈ Set.range hW'.fromSpec := ⟨_, rfl⟩
      rw [hW'.range_fromSpec] at this
      exact (hle.trans inf_le_right) this
    have hrX' := isRapoport_of_range_subset U _ X' _ hU hrng
    have e := hrap _ X' hrX' δ'
    rw [r.baseChange _ _ ρ X trivial X' trivial φ' δ δ' hX' hδ', s.baseChange _ _ ρ X trivial X' trivial φ' δ δ' hX' hδ',
      ← sub_eq_zero, ← map_sub] at e
    have hcomm : ∀ h, LinearMap.rTensor R₀
        (M.presheaf.map (homOfLE (hle.trans inf_le_left)).op).hom.toAddMonoidHom.toIntLinearMap
        (TensorProduct.comm ℤ R₀ Γ(M, W) h) =
          TensorProduct.comm ℤ R₀ Γ(M, W') (ρ h) := by
      intro h
      induction h using TensorProduct.induction_on with
      | zero => simp
      | tmul a g => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hcomm, e, map_zero]
  exact (TensorProduct.comm ℤ R₀ Γ(M, W)).map_eq_zero_iff.1 key

end GlobalTheory.RealMult.QUniq

namespace GlobalTheory.RealMult.QUniq

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R₀ : Type} [CommRing R₀] {k : ℕ}

theorem agreeAt_of_one (r s : Rule (trivialObjectCondition 𝔠) R₀ k) {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R))
    (δ₀ : X.DetGen) (h : r.val R X trivial δ₀ = s.val R X trivial δ₀) : r.AgreeAt s X := by
  intro δ
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (δ.2.symm ▸ Submodule.mem_top : δ₀.1 ∈ Submodule.span R {δ.1})
  rw [← r.homog R X trivial δ δ₀ c hc.symm, ← s.homog R X trivial δ δ₀ c hc.symm, h]

theorem agreeAt_of_inj (r s : Rule (trivialObjectCondition 𝔠) R₀ k) {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R))
    {J : Type} (R' : J → Type) [∀ i, CommRing (R' i)] [∀ i, Algebra R₀ (R' i)] (σ : ∀ i, R →ₐ[R₀] R' i)
    (hinj : ∀ x y : R, (∀ i, σ i x = σ i y) → x = y)
    (h : ∀ i (X' : Obj F 𝔠 (Sp (R' i))) (φ : X'.A.left ⟶ X.A.left),
      X'.IsPullBy X (spMap (σ i : R →+* R' i)) φ → r.AgreeAt s X') : r.AgreeAt s X := by
  intro δ
  refine hinj _ _ fun i ↦ ?_
  obtain ⟨X', φ, hX'⟩ := Obj.exists_isPullBy X (spMap (σ i : R →+* R' i))
  obtain ⟨δ', hδ', -⟩ := hX'.existsUnique_detGen (σ i : R →+* R' i) δ
  have e1 := r.baseChange R (R' i) (σ i) X trivial X' trivial φ δ δ' hX' hδ'
  have e2 := s.baseChange R (R' i) (σ i) X trivial X' trivial φ δ δ' hX' hδ'
  change r.val (R' i) X' trivial δ' = (σ i : R →+* R' i) _ at e1
  change s.val (R' i) X' trivial δ' = (σ i : R →+* R' i) _ at e2
  have := h i X' φ hX' δ'
  simpa [e1, e2] using this

end GlobalTheory.RealMult.QUniq

namespace GlobalTheory.RealMult.QUniq

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {𝔠 : FracId F} {R₀ : Type} [CommRing R₀] {k : ℕ}

theorem agreeAt_of_level (hDP : GlobalTheory.Published.DelignePappasModel) (r s : Rule (trivialObjectCondition 𝔠) R₀ k)
    (hrap : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → r.AgreeAt s X)
    (N : ℕ) (hN : 3 ≤ N) {R : Type} [CommRing R] [Algebra R₀ R] (hu : IsUnit (N : R)) (X : Obj F 𝔠 (Sp R))
    (α : X.Level N) : r.AgreeAt s X := by
  obtain ⟨M, sM, U, αU, hfine, -, -, -, hflat, -, ⟨V, hV, -, -, hcod⟩, hnorm, -⟩ := hDP F 𝔠 N hN
  let t : Sp R ⟶ Sp (Localization.Away (N : ℤ)) :=
    spMap (IsLocalization.Away.lift (S := Localization.Away (N : ℤ)) (N : ℤ) (g := Int.castRingHom R) (by simpa using hu))
  obtain ⟨b, ⟨-, φ, hφ, -⟩, -⟩ := hfine (Sp R) t X α
  have hmod := agreeAt_on_model F 𝔠 N M sM U V hV hflat hnorm hcod R₀ k r s hrap
  choose W hW hmW hgen using fun x : Sp R ↦ GlobalTheory.T.determinant_generator_locally_exists F 𝔠 M U R₀ (b x)
  choose f hf g hg using fun x : Sp R ↦ GlobalTheory.T.local_section_of_coefficient_spec M R₀ R b (W x) (hW x) x (hmW x)
  refine agreeAt_of_inj r s X (fun x : Sp R ↦ Localization.Away (f x)) (fun x ↦ IsScalarTower.toAlgHom R₀ R _)
    (eq_of_loc_away R f hf) fun x X' φ' hX' ↦ ?_
  obtain ⟨UW, φW, hUW⟩ := Obj.exists_isPullBy U (coefSpecMap (hW x) R₀)
  obtain ⟨δW⟩ := hgen x UW φW hUW
  have h1 : X'.IsPullBy U (spMap (g x : _ →+* _) ≫ coefSpecMap (hW x) R₀) (φ' ≫ φ) := by
    rw [hg x]; exact hX'.comp hφ
  obtain ⟨ψ, hψ, -⟩ := h1.cancel hUW
  obtain ⟨δ', hδ', -⟩ := Obj.IsPullBy.existsUnique_detGen (R := R₀ ⊗[ℤ] Γ(M, W x)) (R' := Localization.Away (f x)) _ hψ δW
  refine agreeAt_of_one r s X' δ' ?_
  rw [r.baseChange _ _ (g x) UW trivial X' trivial ψ δW δ' hψ hδ',
    s.baseChange _ _ (g x) UW trivial X' trivial ψ δW δ' hψ hδ', hmod (W x) (hW x) UW φW hUW δW]

theorem agreeAt_of_unit (hDP : GlobalTheory.Published.DelignePappasModel) (hlev : (∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
      ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ X : Obj F 𝔠 (Sp R),
        ∃ (R' : Type) (_ : CommRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
          σ.FaithfullyFlat ∧ X'.IsPullBy X (spMap σ) φ ∧ Nonempty (X'.Level N))) (r s : Rule (trivialObjectCondition 𝔠) R₀ k)
    (hrap : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → r.AgreeAt s X)
    (N : ℕ) (hN : 3 ≤ N) {R : Type} [CommRing R] [Algebra R₀ R] (hu : IsUnit (N : R)) (X : Obj F 𝔠 (Sp R)) :
    r.AgreeAt s X := by
  obtain ⟨R', _, σ, X', φ, hff, hX', ⟨α⟩⟩ := hlev F 𝔠 N (by omega) R hu X
  letI : Algebra R₀ R' := (σ.comp (algebraMap R₀ R)).toAlgebra
  let σ' : R →ₐ[R₀] R' := { σ with commutes' := fun _ ↦ rfl }
  refine agreeAt_of_inj r s X (fun _ : Unit ↦ R') (fun _ ↦ σ') (fun x y h ↦ hff.injective (h ()))
    fun _ X'' φ'' hX'' ↦ ?_
  have h2 : X''.IsPullBy X (𝟙 _ ≫ spMap σ) φ'' := by rw [Category.id_comp]; exact hX''
  obtain ⟨ψ, hψ, -⟩ := h2.cancel hX'
  obtain ⟨α'', -⟩ := hψ.exists_level α
  exact agreeAt_of_level hDP r s hrap N hN (by simpa using hu.map σ) X'' α''

theorem agreeAt_all (hDP : GlobalTheory.Published.DelignePappasModel) (hlev : (∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
      ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ X : Obj F 𝔠 (Sp R),
        ∃ (R' : Type) (_ : CommRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
          σ.FaithfullyFlat ∧ X'.IsPullBy X (spMap σ) φ ∧ Nonempty (X'.Level N))) (r s : Rule (trivialObjectCondition 𝔠) R₀ k)
    (hrap : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → r.AgreeAt s X)
    {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) : r.AgreeAt s X := by
  refine agreeAt_of_inj r s X (fun b : Bool ↦ Localization.Away (if b then (2 : R) else 3))
    (fun b ↦ IsScalarTower.toAlgHom R₀ R _) (fun x y h ↦ eq_of_loc_two_three R x y (h true) (h false)) fun b X' φ' hX' ↦ ?_
  cases b
  · have h3 : IsUnit (algebraMap R (Localization.Away (3 : R)) 3) := IsLocalization.Away.algebraMap_isUnit 3
    have h3' : IsUnit ((3 : ℕ) : Localization.Away (3 : R)) := by
      rw [Nat.cast_ofNat, ← map_ofNat (algebraMap R (Localization.Away (3 : R))) 3]; exact h3
    exact agreeAt_of_unit hDP hlev r s hrap 3 le_rfl h3' X'
  · have h2 : IsUnit (algebraMap R (Localization.Away (2 : R)) 2) := IsLocalization.Away.algebraMap_isUnit 2
    have h4 : ((4 : ℕ) : Localization.Away (2 : R)) = algebraMap R _ 2 * algebraMap R _ 2 := by
      rw [← map_mul, show (2 : R) * 2 = 4 by norm_num, map_ofNat, Nat.cast_ofNat]
    exact agreeAt_of_unit hDP hlev r s hrap 4 (by norm_num) (by rw [h4]; exact h2.mul h2) X'

end GlobalTheory.RealMult.QUniq

theorem GlobalTheory.RealMult.rule_eq_of_agree_rapoport_of_level (hlev : (∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
      ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ X : Obj F 𝔠 (Sp R),
        ∃ (R' : Type) (_ : CommRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
          σ.FaithfullyFlat ∧ X'.IsPullBy X (spMap σ) φ ∧ Nonempty (X'.Level N))) : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀]
  (k : ℕ) (r s : Rule (trivialObjectCondition 𝔠) R₀ k),
  (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → ∀ δ : X.DetGen,
    r.val R X trivial δ = s.val R X trivial δ) → r = s := by
  intro hDP F _ _ _ 𝔠 R₀ _ k r s h
  apply Rule.ext
  funext R _ _ X hX δ
  exact QUniq.agreeAt_all hDP hlev r s h X δ
