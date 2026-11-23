import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAevalEqSmulOnEigenspace

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module

namespace GlobalTheory.WeilDeligne

section Reduction

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def WDRep.resZero {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (U : Submodule ℂ V) (hU : ∀ σ, ∀ v ∈ U, a.ρ σ v ∈ U) : WDRep h U where
  ρ := { toFun := fun σ => (a.ρ σ).restrict (hU σ)
         map_one' := by ext; simp
         map_mul' := fun σ τ => by ext; simp }
  N := 0
  smooth := a.smooth.of_le fun σ hσ => by ext; simp [hσ]
  semisimple σ := End.IsSemisimple.restrict (hU σ) (a.semisimple σ)
  nilpotent := IsNilpotent.zero
  comm σ := by simp

theorem WDRep.charpoly_eq_mul_of_isCompl {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (a : WDRep h V) (U U' : Submodule ℂ V)
    (hU : ∀ σ, ∀ v ∈ U, a.ρ σ v ∈ U) (hU' : ∀ σ, ∀ v ∈ U', a.ρ σ v ∈ U') (hc : IsCompl U U')
    (σ : Weil h) :
    (a.ρ σ).charpoly = ((a.resZero U hU).ρ σ).charpoly * ((a.resZero U' hU').ρ σ).charpoly := by
  rw [← LinearMap.charpoly_prodMap, ← LinearEquiv.charpoly_conj (Submodule.prodEquivOfIsCompl U U' hc)]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := (Submodule.prodEquivOfIsCompl U U' hc).surjective v
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simp [Submodule.coe_prodEquivOfIsCompl', WDRep.resZero]

theorem finite_range_of_frob_pow_eq_one {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ) {m : ℕ} (hm : 0 < m)
    (h1 : ρ (frob h) ^ m = 1) : (Set.range ρ).Finite := by
  refine (Set.Finite.image2 (· * ·) (Set.finite_range fun j : Fin m => ρ (frob h) ^ (j : ℕ))
    hρ.finite_range).subset ?_
  rintro _ ⟨σ, rfl⟩
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (h := h) deg_frob σ
  have hker : frob h ^ m ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_pow, h1]
  set k := deg σ
  have hk : frob h ^ k = frob h ^ ((k % m).toNat) * (frob h ^ m) ^ (k / m) := by
    rw [← zpow_natCast (frob h) m, ← zpow_mul, ← zpow_natCast (frob h) ((k % m).toNat),
      ← zpow_add, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne')),
      add_comm, Int.mul_ediv_add_emod]
  have hlt : (k % m).toNat < m := by
    have := Int.emod_lt_of_pos k (by exact_mod_cast hm : (0 : ℤ) < m)
    omega
  refine ⟨ρ (frob h) ^ ((k % m).toNat), ⟨⟨_, hlt⟩, rfl⟩, ρ (ineIncl h τ), ⟨τ, rfl⟩, ?_⟩
  have h2 : ρ ((frob h ^ m) ^ (k / m)) = 1 := (ρ.ker.zpow_mem hker _)
  show _ = ρ σ
  rw [hτ, hk, map_mul, map_mul, h2, mul_one, map_pow]

theorem exists_of_lpSum_twist_finite (S : WD h → Prop)
    (hsum : ∀ x y, S x → S y → S (x.lpSum y))
    (hfin : ∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ),
      (Set.range a.ρ).Finite → S (WD.mk (a.twist μ hμ))) :
    ∀ (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
      finrank ℂ V = d → ∀ (ρ : Representation ℂ (Weil h) V), IsSmooth ρ →
      (∀ σ, End.IsSemisimple (ρ σ)) → ∃ y : WD h, S y ∧ ∀ σ, y.charPol σ = (ρ σ).charpoly := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V _ _ _ hd ρ hρ hs
  let a0 : WDRep h V := ⟨ρ, 0, hρ, hs, IsNilpotent.zero, by simp⟩
  obtain ⟨m, hm, hcomm⟩ := exists_pow_frob_commute ρ hρ
  have hsm : ρ (frob h) ^ m = ρ (frob h ^ m) := (map_pow _ _ _).symm
  by_cases hsc : ∃ c : ℂ, c ≠ 0 ∧ ρ (frob h) ^ m = c • (1 : Module.End ℂ V)
  · obtain ⟨c, hc0, hsc⟩ := hsc
    obtain ⟨c', hc'⟩ := IsAlgClosed.exists_pow_nat_eq c hm
    have hc'0 : c' ≠ 0 := by rintro rfl; exact hc0 (by rw [← hc', zero_pow hm.ne'])
    set u : ℂˣ := Units.mk0 c' hc'0
    let b : WDRep h V := a0.twist (unrChar h u⁻¹) (isSmooth_unrChar h _)
    have hb1 : b.ρ (frob h) ^ m = 1 := by
      show ((((unrChar h u⁻¹) (frob h) : ℂˣ) : ℂ) • ρ (frob h)) ^ m = 1
      rw [_root_.smul_pow, hsc, smul_smul, unrChar_apply, deg_frob, zpow_one, ← Units.val_pow_eq_pow_val,
        inv_pow]
      have : u ^ m = Units.mk0 c hc0 := Units.ext (by simp [u, hc'])
      rw [this]
      simp [hc0]
    have hfinb := finite_range_of_frob_pow_eq_one b.ρ b.smooth hm hb1
    have hfins : (Set.range (WD.std b).2.ρ).Finite :=
      (hfinb.image ((finBasis ℂ V).equivFun.conjAlgEquiv ℂ)).subset (by rintro _ ⟨σ, rfl⟩; exact ⟨_, ⟨σ, rfl⟩, rfl⟩)
    refine ⟨WD.mk ((WD.std b).2.twist (unrChar h u) (isSmooth_unrChar h _)),
      hfin _ _ _ _ hfins, fun σ => ?_⟩
    rw [← WD.sound ((WD.iso_std b).twist _ _), WD.charPol_mk]
    show ((((unrChar h u) σ : ℂˣ) : ℂ) • ((((unrChar h u⁻¹) σ : ℂˣ) : ℂ) • ρ σ)).charpoly = _
    rw [smul_smul, ← Units.val_mul, unrChar_apply, unrChar_apply, ← mul_zpow, mul_inv_cancel,
      one_zpow, Units.val_one, one_smul]
  · have hnt : Nontrivial V := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      exact hsc ⟨1, one_ne_zero, LinearMap.ext fun v => Subsingleton.elim _ _⟩
    set s := ρ (frob h) ^ m with hs_def
    have hss : End.IsSemisimple s := by rw [hsm]; exact hs _
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue s
    have hinv : ∀ σ α, ∀ v ∈ End.eigenspace s α, ρ σ v ∈ End.eigenspace s α := by
      intro σ α v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [← Module.End.mul_apply, (hcomm σ).eq, Module.End.mul_apply, hv, map_smul]
    set U := End.eigenspace s c
    set U' := ⨆ α ∈ ({c}ᶜ : Set ℂ), End.eigenspace s α
    have hU : ∀ σ, ∀ v ∈ U, ρ σ v ∈ U := fun σ => hinv σ c
    have hU' : ∀ σ, ∀ v ∈ U', ρ σ v ∈ U' := by
      intro σ v hv
      have : U' ≤ U'.comap (ρ σ) := iSup₂_le fun α hα w hw =>
        (le_iSup₂_of_le α hα le_rfl : End.eigenspace s α ≤ U') (hinv σ α w hw)
      exact this hv
    have hcompl : IsCompl U U' := by
      refine ⟨(Module.End.eigenspaces_iSupIndep s).disjoint_biSup (by simp), ?_⟩
      rw [codisjoint_iff, eq_top_iff, ← hss.iSup_eigenspace_eq_top]
      refine iSup_le fun α => ?_
      by_cases hα : α = c
      · subst hα; exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le α hα le_rfl)
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨v, hv, hv0⟩ := hc.exists_hasEigenvector
      apply hv0
      have h1 := Module.End.mem_eigenspace_iff.mp hv
      rw [zero_smul] at h1
      have h1' : ρ (frob h ^ m) v = 0 := by rw [← hsm]; exact h1
      have := congrArg (ρ (frob h ^ m)⁻¹) h1'
      rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
        map_zero] at this
    have hUb : U ≠ ⊥ := hc
    have hU'b : U' ≠ ⊥ := by
      intro hb
      apply hsc
      refine ⟨c, hc0, LinearMap.ext fun v => ?_⟩
      have hv : v ∈ U := by
        have := hcompl.sup_eq_top
        rw [hb, sup_bot_eq] at this
        rw [this]; trivial
      rw [Module.End.mem_eigenspace_iff.mp hv]
      simp
    have hrk := Submodule.finrank_add_eq_of_isCompl hcompl
    have h1 : 0 < finrank ℂ U := Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hUb)
    have h2 : 0 < finrank ℂ U' :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hU'b)
    obtain ⟨y1, hS1, hy1⟩ := ih (finrank ℂ U) (by omega) U rfl (a0.resZero U hU).ρ
      (a0.resZero U hU).smooth (a0.resZero U hU).semisimple
    obtain ⟨y2, hS2, hy2⟩ := ih (finrank ℂ U') (by omega) U' rfl (a0.resZero U' hU').ρ
      (a0.resZero U' hU').smooth (a0.resZero U' hU').semisimple
    refine ⟨y1.lpSum y2, hsum _ _ hS1 hS2, fun σ => ?_⟩
    rw [WD.charPol_lpSum, hy1, hy2]
    exact (a0.charpoly_eq_mul_of_isCompl U U' hU hU' hcompl σ).symm

end Reduction

theorem WD.induction_lpSum_twist_finite : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (S : WD h → Prop), (∀ x y, S x → S y → S (x.lpSum y)) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → S x → S y) → (∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ), (Set.range a.ρ).Finite → S (WD.mk (a.twist μ hμ))) → ∀ x, S x := by
  intro E Ω _ _ _ _ _ A w h S hsum hchar hfin x
  induction x using WD.ind with
  | hP n a =>
  obtain ⟨y, hy, hyc⟩ := exists_of_lpSum_twist_finite S hsum hfin _ (Fin n → ℂ) rfl a.ρ a.smooth
    a.semisimple
  exact hchar y _ (fun σ => by rw [hyc, WD.charPol_mk]) hy

end GlobalTheory.WeilDeligne
