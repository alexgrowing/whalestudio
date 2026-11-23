import Mathlib
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.GenMain
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaLawSymplecticNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueAtNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ProdCompEqOfFiniteFamily
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInNormalAt

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyConst

theorem exists_rescale (P : Out.PolAV (Sp ℂ)) (hg rig hr th hth v hv)
    (τ M : Matrix (Fin P.g) (Fin P.g) ℂ) (a b : Fin P.g → ℂ) (c : ℂ) (hc : c ≠ 0) (hM : M.det ≠ 0)
    (hx : NormalAt ⟨P, hg, rig, hr, th, hth, v, hv⟩ τ M a b c) :
    ∃ th₀ hth₀ v₀ hv₀, NormalAt ⟨P, hg, rig, hr, th₀, hth₀, v₀, hv₀⟩ τ 1 a b 1 ∧
      (∀ i, LB.Sec.f th i = constFn P.A.hom _ c * LB.Sec.f th₀ i) ∧ ∀ i, IsLieComb (M i) v₀ (v i) := by
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hx
  haveI := P.isAb.comm
  obtain ⟨ex, tan, comp, sgl, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v hv.1
  choose v₀ hv₀ using fun i => (ex (M⁻¹ i)).exists
  have hb₀ : IsLieBasis v₀ := (bas M⁻¹ v₀ hv hv₀).2 (Matrix.isUnit_nonsing_inv_det M hM.isUnit)
  obtain ⟨ex₀, -, -, -, -⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v₀ hb₀.1
  have hMv : ∀ i, IsLieComb (M i) v₀ (v i) := fun i => by
    obtain ⟨w, hw⟩ := (ex₀ (M i)).exists
    have h1 := comp _ (fun i => M⁻¹ i) v₀ (M i) w hv₀ hw
    have e : ∑ j, M i j • M⁻¹ j = Pi.single i 1 := by
      rw [← Matrix.vecMul_eq_sum]
      refine (congrFun (Matrix.mul_nonsing_inv M hM.isUnit) i).trans ?_
      simpa using smul_one_row (1 : ℂ) i
    rw [e] at h1
    rwa [(ex _).unique (sgl i) h1]
  obtain ⟨th₀, e₀, e₁, hle⟩ := exists_sec_div P.A.hom (mul_inv_cancel₀ hc) th
  have hth₀ : ∀ s : Sp ℂ, ∃ y : P.A.left, P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th₀ :=
    fun s => (hth s).imp fun y hy => ⟨hy.1, hle hy.2⟩
  refine ⟨th₀, hth₀, v₀, hb₀, ⟨u, h₁, h₂, h₃, h₄, ?_, ?_⟩, e₁, hMv⟩
  · intro i z hz
    have e := h₅ i z hz
    refine ((congrArg (valAt' _ _) (e₀ i)).trans (valAt'_mul _ _ _ _)).trans ?_
    rw [valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz]
    refine (congrArg (c⁻¹ * ·) e).trans ?_
    beta_reduce
    rw [_root_.one_mul, ← _root_.mul_assoc, inv_mul_cancel_left₀ hc]
  · intro i
    have h1 := GlobalTheory.UnifDifferential.isDiff_of_isLieComb P.A P.L P.g P.g u _ v _ _ hv.1 h₆ (hv₀ i)
    have e : ∑ j, M⁻¹ i j • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M j) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • (1 : Matrix (Fin P.g) (Fin P.g) ℂ) i := by
      simp only [smul_comm (M⁻¹ i _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
      rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum, ← Matrix.nonsing_inv_mul M hM.isUnit]
      rfl
    rwa [e] at h1

theorem value_eq {g c N : ℕ} {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hk : KaRuleK g c N ka)
    (a b : Fin g → ℂ) (U : Matrix (Fin g) (Fin g) ℂ → ℂ)
    (hU : ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 →
        (ka ℂ x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm)))
    (x : KeyIn ℂ) (h : x.P.g = g) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c₀ : ℂ) (hc : c₀ ≠ 0)
    (hM : M.det ≠ 0) (hx : NormalAt x τ M (fun i => a (i.cast h)) (fun i => b (i.cast h)) c₀) :
    (ka ℂ x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm)) * (M.det ^ 4 / c₀ ^ 8) ^ c := by
  obtain ⟨P, hg, rig, hr, th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, hN, e₁, hMv⟩ := exists_rescale P hg rig hr th hth v hv τ M _ _ c₀ hc hM hx
  have h0 := hU ⟨P, hg, rig, hr, th₀, hth₀, v₀, hv₀⟩ h τ hN
  have h1 := hk.1 ℂ P hg rig hr _ hth₀ v₀ hv₀ th hth v hv c₀ M h e₁ hMv
  rw [h0] at h1
  rw [div_pow, ← pow_mul, ← pow_mul, ← mul_div_assoc, eq_div_iff (pow_ne_zero _ hc), mul_comm, mul_comm (U _)]
  exact h1

theorem value_spAct {g c N : ℕ} {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hk : KaRuleK g c N ka)
    (n n' k k' : Fin g → ℤ) (U V : Matrix (Fin g) (Fin g) ℂ → ℂ)
    (hU : ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => (n (i.cast h) : ℂ) / 2) (fun i => (n' (i.cast h) : ℂ) / 2) 1 →
        (ka ℂ x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm)))
    (hV : ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
        NormalAt x τ 1 (fun i => (k (i.cast h) : ℂ) / 2) (fun i => (k' (i.cast h) : ℂ) / 2) 1 →
        (ka ℂ x : ℂ) = V (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm)))
    (sp : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (hsp : sp ∈ Matrix.symplecticGroup (Fin g) ℤ)
    (hL : ThetaLaw g sp n n' k k') (τ : Matrix (Fin g) (Fin g) ℂ) (x : KeyIn ℂ) (h : x.P.g = g)
    (hx : NormalAt x (τ.submatrix (Fin.cast h) (Fin.cast h)) 1 (fun i => (n (i.cast h) : ℂ) / 2)
      (fun i => (n' (i.cast h) : ℂ) / 2) 1) :
    U τ = V (Key.Chi.spAct sp τ) := by
  subst h
  have hx' : NormalAt x τ 1 (fun i => (n i : ℂ) / 2) (fun i => (n' i : ℂ) / 2) 1 := hx
  obtain ⟨M', c', hc', e, hN⟩ := GlobalTheory.SpMove.normalAt_spAct x τ 1 1 sp n n' k k' hsp hL one_ne_zero hx'
  have e' : M'.det ^ 4 / c' ^ 8 = 1 := by rw [e]; simp
  have hM' : M'.det ≠ 0 := fun h0 => by rw [h0] at e'; simp at e'
  have h1 : (ka ℂ x : ℂ) = U τ := hU x rfl τ hx'
  have h2 : (ka ℂ x : ℂ) = V (Key.Chi.spAct sp τ) * (M'.det ^ 4 / c' ^ 8) ^ c :=
    value_eq hk (fun i => (k i : ℂ) / 2) (fun i => (k' i : ℂ) / 2) V hV x rfl _ M' c' hc' hM' hN
  rw [e', _root_.one_pow, _root_.mul_one] at h2
  rw [← h1, h2]

abbrev Bits (g : ℕ) : Type := {n : Fin g → ℤ // ∀ i, n i = 0 ∨ n i = 1}

instance finite_bits (g : ℕ) : Finite (Bits g) := by
  have h : {n : Fin g → ℤ | ∀ i, n i ∈ ({0, 1} : Set ℤ)}.Finite :=
    Set.Finite.pi' fun _ => Set.toFinite _
  exact h.to_subtype

theorem charHalf_bits {g : ℕ} (n n' : Bits g) :
    charHalf g (fun i => (n.1 i : ℂ) / 2) (fun i => (n'.1 i : ℂ) / 2) :=
  ⟨fun i => (n.2 i).imp (fun h => by simp [h]) (fun h => by simp [h]),
    fun i => (n'.2 i).imp (fun h => by simp [h]) (fun h => by simp [h])⟩

def IsValueFn {g : ℕ} (κ : KeyIn ℂ → ℂˣ) (n n' : Fin g → ℤ) (U : Matrix (Fin g) (Fin g) ℂ → ℂ) : Prop :=
  ∀ (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ),
    NormalAt x τ 1 (fun i => (n (i.cast h) : ℂ) / 2) (fun i => (n' (i.cast h) : ℂ) / 2) 1 →
    (κ x : ℂ) = U (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm))

theorem exists_valueFn {g c N : ℕ} {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ}
    (hk : KaRuleK g c N ka) (p : Bits g × Bits g) :
    ∃ U, Key.IsHoloSiegel g U ∧ IsValueFn (ka ℂ) p.1.1 p.2.1 U := by
  obtain ⟨-, -, -, h⟩ := hk
  obtain ⟨U, h₁, h₂⟩ := h (fun i => (p.1.1 i : ℂ) / 2) (fun i => (p.2.1 i : ℂ) / 2) (charHalf_bits p.1 p.2)
  exact ⟨U, h₁, fun x hx τ hN => h₂ x hx τ hN⟩

theorem valueFn_perm (hT : ThetaUnifAV) (hI : Key.Chi.InversionStatement) (hA : GlobalTheory.TorusAlgebraic)
    {g c N : ℕ} {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (hg : 1 ≤ g) (hk : KaRuleK g c N ka)
    (U : Bits g × Bits g → Matrix (Fin g) (Fin g) ℂ → ℂ) (hU : ∀ p, IsValueFn (ka ℂ) p.1.1 p.2.1 (U p)) :
    ∀ sp ∈ Matrix.symplecticGroup (Fin g) ℤ, ∀ i, ∃ j,
      ∀ τ ∈ ReciprocityTheory.PTheta.SiegelH (Fin g), U i τ = U j (Key.Chi.spAct sp τ) := by
  intro sp hsp i
  obtain ⟨k, k', hk₁, hk₂, hL⟩ :=
    (chiAt_iff_thetaLaw g sp).1 (Key.Chi.chi_of hI Key.Chi.spGen g sp hsp) i.1.1 i.2.1
  refine ⟨(⟨k, hk₁⟩, ⟨k', hk₂⟩), fun τ hτ => ?_⟩
  obtain ⟨x, h, hx⟩ := GlobalTheory.KeyOfPeriod.exists_keyIn_normalAt hT hA g τ _ _ hg hτ.1 hτ.2 (charHalf_bits i.1 i.2)
  exact value_spAct hk i.1.1 i.2.1 k k' _ _ (hU i) (hU (⟨k, hk₁⟩, ⟨k', hk₂⟩)) sp hsp hL τ x h hx

theorem value_zero {c N : ℕ} {ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (x : KeyIn ℂ)
    (hk : KaRuleK x.P.g c N ka) (U : Matrix (Fin x.P.g) (Fin x.P.g) ℂ → ℂ) (hU : IsValueFn (ka ℂ) 0 0 U)
    (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c₀ : ℂ) (hc : c₀ ≠ 0) (hM : Mx.det ≠ 0)
    (hx : NormalAt x τ Mx 0 0 c₀) : (ka ℂ x : ℂ) = U τ * (Mx.det ^ 4 / c₀ ^ 8) ^ c := by
  have e : (fun i : Fin x.P.g => (((0 : Fin x.P.g → ℤ) i : ℤ) : ℂ) / 2) = 0 := by
    funext i; simp
  have hx' : NormalAt x τ Mx (fun i => (((0 : Fin x.P.g → ℤ) i : ℤ) : ℂ) / 2)
      (fun i => (((0 : Fin x.P.g → ℤ) i : ℤ) : ℂ) / 2) c₀ := by
    rw [e]; exact hx
  exact value_eq hk (fun i => (((0 : Fin x.P.g → ℤ) i : ℤ) : ℂ) / 2)
    (fun i => (((0 : Fin x.P.g → ℤ) i : ℤ) : ℂ) / 2) U hU x rfl τ Mx c₀ hc hM hx'

theorem exists_const : ThetaUnifAV → Key.Chi.InversionStatement → Key.PhHoloStatement → GlobalTheory.TorusAlgebraic → ∀ (g c M : ℕ) (ka : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ), 2 ≤ g → KaRuleK g c M ka → ∃ a₀ : ℂ, ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c₀ : ℂ), x.P.g = g → c₀ ≠ 0 → Mx.det ≠ 0 → NormalAt x τ Mx 0 0 c₀ → (ka ℂ x : ℂ) = a₀ * (Mx.det ^ 4 / c₀ ^ 8) ^ c := by
  intro hT hI hP hA g c N ka hg hk
  choose U hUh hU using exists_valueFn hk
  obtain ⟨a₀, ha⟩ := GlobalTheory.const_of_finite_family_spAct hP g _ U hg hUh (valueFn_perm hT hI hA (by omega) hk U hU)
    (⟨0, fun _ => Or.inl rfl⟩, ⟨0, fun _ => Or.inl rfl⟩)
  refine ⟨a₀, fun x τ Mx c₀ h hc hM hx => ?_⟩
  subst h
  rw [← ha τ hx.mem_siegelH]
  exact value_zero x hk _ (hU (⟨0, fun _ => Or.inl rfl⟩, ⟨0, fun _ => Or.inl rfl⟩)) τ Mx c₀ hc hM hx

end GlobalTheory.KeyConst
end
