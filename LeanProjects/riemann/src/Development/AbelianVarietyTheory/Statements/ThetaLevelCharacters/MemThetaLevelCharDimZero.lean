import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

def TorusAlgebraic : Prop :=
  ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef →
    (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) →
    ∃ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (th : P.L.Sec), P.g = g ∧
      (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
      ((∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
      u.IsFn th (thetaChar τ a b) ∧
      (∀ n : ℕ,
        (∀ s, ∃! θ, θ ∈ thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) n τ ∧ u.IsFnPow n s θ) ∧
        ∀ θ ∈ thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) n τ, ∃! s, u.IsFnPow n s θ) ∧
      (∀ N : ℕ, 3 ≤ N → Out.VeryAmpleAt P.A P.L N) ∧
      ∀ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ l ∈ u.Λ, F l ∈ u.Λ) →
        ∃ f : P.A ⟶ P.A, IsMonHom f ∧ ∀ z, u.ex (F z) = u.ex z ≫ f

namespace TorusAlg

open ReciprocityTheory.PTheta

section Signs

variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}

theorem ofRealVec_re (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) : ofRealVec (fun i => (a i).re) = a := by
  funext i
  rcases ha i with h | h <;> simp [ofRealVec, h]

theorem thetaChar_ofRealVec (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) :
    thetaChar τ (ofRealVec a) (ofRealVec b) = fun z => theta a b z τ := by
  funext z
  unfold thetaChar theta thetaTerm eC
  refine tsum_congr fun n => ?_
  have e1 : ((fun i => (n i : ℂ)) + ofRealVec a) = shiftVec a n := rfl
  rw [e1]
  congr 1
  ring

theorem thetaChar_eq_theta (τ : Matrix (Fin g) (Fin g) ℂ) (ha : ∀ i, a i = 0 ∨ a i = 1 / 2)
    (hb : ∀ i, b i = 0 ∨ b i = 1 / 2) :
    thetaChar τ a b = fun z => theta (fun i => (a i).re) (fun i => (b i).re) z τ := by
  rw [← thetaChar_ofRealVec, ofRealVec_re ha, ofRealVec_re hb]

theorem thetaChar_level (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (ha : ∀ i, a i = 0 ∨ a i = 1 / 2)
    (hb : ∀ i, b i = 0 ∨ b i = 1 / 2) :
    thetaChar τ a b ≠ 0 ∧
    thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) 1 τ = Submodule.span ℂ {thetaChar τ a b} ∧
    ∀ n : ℕ, 0 < n → Module.finrank ℂ (thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) n τ) = n ^ g := by
  rw [thetaChar_eq_theta τ ha hb]
  refine ⟨theta_ne_zero ⟨hs, hp⟩ _ _, thetaLevelChar_one ⟨hs, hp⟩, fun n hn => ?_⟩
  rw [finrank_thetaLevelChar ⟨hs, hp⟩ hn, Fintype.card_fin]

theorem mem_periodLattice_iff (z : Fin g → ℂ) : z ∈ periodLattice τ ↔
    ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) :=
  ⟨fun ⟨n, m, h⟩ => ⟨m, n, h.trans (add_comm _ _)⟩, fun ⟨m, n, h⟩ => ⟨n, m, h.trans (add_comm _ _)⟩⟩

theorem frame_eq_autFactor_mul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g) (th : L.Sec)
    (hs : τ.IsSymm) (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    (hΛ : ∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))
    (hth : u.IsFn th (thetaChar τ a b)) (k k' : Fin g → ℤ) (i : L.ι) (z : Fin g → ℂ)
    (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) (h0 : thetaChar τ a b z ≠ 0) :
    u.fr i z = autFactor (fun i => (a i).re) (fun i => (b i).re) τ k k' z *
      u.fr i (z + τ *ᵥ ofIntVec k + ofIntVec k') := by
  have hl : u.ex (τ *ᵥ ofIntVec k + ofIntVec k') = 1 := (u.ker _).2 ((hΛ _).2 ⟨k', k, add_comm _ _⟩)
  have he : u.ex (z + τ *ᵥ ofIntVec k + ofIntVec k') = u.ex z := by
    rw [add_assoc, u.ex_add, hl, _root_.mul_one]
  have h1 := hth i z hz
  have h2 := hth i (z + τ *ᵥ ofIntVec k + ofIntVec k') (by rw [he]; exact hz)
  rw [he, h1] at h2
  rw [thetaChar_eq_theta τ ha hb] at h2 h0
  simp only [thetaQuasiPeriod_holds _ _ _ z τ k k' hs] at h2 h0
  apply mul_left_cancel₀ h0
  rw [h2]; ring

end Signs

section Hypotheses

theorem hypotheses_inhabited :
    (∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.IsSymm →
      (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ) + B.map Complex.ofReal).IsSymm ∧
      ((Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ) + B.map Complex.ofReal).map Complex.im).PosDef) ∧
    ((!![Complex.I, 1 / 3; 1 / 3, Complex.I] : Matrix (Fin 2) (Fin 2) ℂ).IsSymm ∧
      ((!![Complex.I, 1 / 3; 1 / 3, Complex.I] : Matrix (Fin 2) (Fin 2) ℂ).map Complex.im).PosDef ∧
      (∀ i, (![1 / 2, 0] : Fin 2 → ℂ) i = 0 ∨ (![1 / 2, 0] : Fin 2 → ℂ) i = 1 / 2) ∧
      ∀ i, (![1 / 2, 1 / 2] : Fin 2 → ℂ) i = 0 ∨ (![1 / 2, 1 / 2] : Fin 2 → ℂ) i = 1 / 2) := by
  refine ⟨fun g B hB => ⟨(Matrix.isSymm_one.smul _).add (hB.map _), ?_⟩, ?_, ?_, ?_, ?_⟩
  · convert (Matrix.PosDef.one : (1 : Matrix (Fin g) (Fin g) ℝ).PosDef) using 1
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · convert (Matrix.PosDef.one : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef) using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro i; fin_cases i <;> simp
  · intro i; fin_cases i <;> simp

end Hypotheses

section DimZero

open Out Out.Inh

theorem valAt'_id (f : Γ(Sp ℂ, ⊤)) :
    valAt' (𝟙 (Sp ℂ)) ⊤ f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom f := by
  rw [valAt', dif_pos (show (⊤ : (Sp ℂ).Opens) ≤ 𝟙 (Sp ℂ) ⁻¹ᵁ ⊤ from le_rfl), valAt]
  congr 1

theorem valAt'_id_bijective (U : (Sp ℂ).Opens) (hU : U = ⊤) :
    Function.Bijective (valAt' (𝟙 (Sp ℂ)) U) ∧ valAt' (𝟙 (Sp ℂ)) U 1 = 1 := by
  subst hU
  refine ⟨?_, by rw [valAt'_id, map_one]⟩
  rw [show valAt' (𝟙 (Sp ℂ)) ⊤ = _ from funext valAt'_id]
  exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom

theorem unit_hom_left {X : Over (Sp ℂ)} (v : X ⟶ 𝟙_ (Over (Sp ℂ))) : v.left = X.hom :=
  (Category.comp_id v.left).symm.trans (Over.w v)

def zeroUnif : HolUnif (zeroPolAV (Sp ℂ)).A (zeroPolAV (Sp ℂ)).L 0 where
  ex _ := 1
  ex_add _ _ := (_root_.mul_one _).symm
  ex_onto x := ⟨0, toUnit_unique _ _⟩
  Λ := ⊤
  ker _ := by simp
  discrete := inferInstance
  full := by simp
  hol U f := ⟨isOpen_discrete _, differentiableOn_const _⟩
  fr _ _ := 1
  fr_hol _ := differentiableOn_const _
  fr_ne _ _ _ := one_ne_zero
  fr_compat i j z _ := by
    rw [_root_.mul_one]
    exact (valAt'_id_bijective _ (inf_idem _)).2.symm

theorem isTangent_zero (v : epsR ℂ ⟶ (zeroPolAV (Sp ℂ)).A) : IsTangent v := by
  have h1 : v.left = (epsR ℂ).hom := unit_hom_left v
  have h2 : η[(zeroPolAV (Sp ℂ)).A].left = 𝟙 (Sp ℂ) := unit_hom_left (X := 𝟙_ _) _
  rw [IsTangent, h1, h2]
  change spMap _ ≫ spMap _ = _
  rw [← Spec.map_comp]
  refine Eq.trans ?_ (Spec.map_id (CommRingCat.of ℂ))
  congr 1

theorem snd_pull_eq_zero (φ : Sp (DualNumber ℂ) ⟶ Sp ℂ) (hφ : φ = spMap (algebraMap ℂ (DualNumber ℂ)))
    (U : (Sp ℂ).Opens) (h : ⊤ ≤ φ ⁻¹ᵁ U) (f : Γ(Sp ℂ, U)) :
    TrivSqZeroExt.snd (show DualNumber ℂ from
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((φ.appLE U ⊤ h).hom f)) = 0 := by
  have hU : U = ⊤ := top_unique fun x _ => by
    obtain ⟨y⟩ : Nonempty (Sp (DualNumber ℂ)) := inferInstanceAs (Nonempty (PrimeSpectrum (DualNumber ℂ)))
    have hy : φ y ∈ U := h (show y ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
    rwa [show x = φ y from Subsingleton.elim (α := PrimeSpectrum ℂ) _ _]
  subst hU hφ
  have e : (spMap (algebraMap ℂ (DualNumber ℂ))).appLE ⊤ ⊤ h = (spMap (algebraMap ℂ (DualNumber ℂ))).appTop :=
    Scheme.Hom.appLE_eq_app _
  have n := congrArg (fun k => k.hom f) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))))
  rw [e]
  exact (congrArg (TrivSqZeroExt.snd (R := ℂ) (M := ℂ)) n).trans rfl

theorem isDiff_zero (w : Fin 0 → ℂ) (v : epsR ℂ ⟶ (zeroPolAV (Sp ℂ)).A) : zeroUnif.IsDiff w v := by
  intro U h f
  rw [Subsingleton.elim w 0, map_zero]
  exact snd_pull_eq_zero v.left (unit_hom_left v) U h f

end DimZero

end TorusAlg

end GlobalTheory
