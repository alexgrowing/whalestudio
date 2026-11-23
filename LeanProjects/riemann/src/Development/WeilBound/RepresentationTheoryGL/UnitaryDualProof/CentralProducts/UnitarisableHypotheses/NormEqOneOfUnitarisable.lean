import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.UnitarisableHypotheses.IsUnitarisableCast
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.UnitarisableHypotheses.IrrSub
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.AddChar
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.IrrAdm
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.AdmProd
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.UnitaryAdmissibleComplements.UnitaryAdmissibleComplementHolds
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.UnitaryAdmissibleComplements.IsIrreducibleIffFinrank
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestDerivativeOfProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorNonscalarOffdiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import GroundTheory.AutomorphicForms.SmoothRepSchur
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.Asm

open PositivityTheory.PfBern.Assembly (subIncl subProj subProj_subIncl_left subProj_subIncl_right isSmooth_sub
  eq_bot_or_eq_top_of_equiv_twist range_ne_bot_ne_top)

section Gen

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isUnitarisable_sub {ρ : Representation ℂ G V} (h : IsUnitarisable ρ) (S : Subrepresentation ρ) :
    IsUnitarisable S.toRepresentation := by
  obtain ⟨B, h1, h2, h3⟩ := h
  exact ⟨(B.comp S.toSubmodule.subtype).compl₂ S.toSubmodule.subtype, fun v w => h1 _ _,
    fun v hv => h2 _ (fun h0 => hv (Subtype.ext h0)), fun g v w => h3 g v w⟩

theorem isUnitarisable_of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (E : ρ.Equiv σ)
    (h : IsUnitarisable σ) : IsUnitarisable ρ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B.comp E.toLinearMap).compl₂ E.toLinearMap, fun v w => h1 _ _,
    fun v hv => h2 _ (fun h0 => hv (E.toLinearEquiv.map_eq_zero_iff.1 h0)), fun g v w => ?_⟩
  have hc : ∀ u, E.toLinearMap (ρ g u) = σ g (E.toLinearMap u) := fun u =>
    LinearMap.congr_fun (E.isIntertwining' g) u
  simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, hc]
  exact h3 g _ _

theorem norm_eq_one_of_unitarisable {ρ : Representation ℂ G V} (h : IsUnitarisable ρ) (g : G) {v : V} {c : ℂ}
    (hv : v ≠ 0) (hc : ρ g v = c • v) : ‖c‖ = 1 := by
  obtain ⟨B, -, h2, h3⟩ := h
  have e := h3 g v v
  rw [hc, LinearMap.map_smulₛₗ (B (c • v)), map_smul B c v, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at e
  have hB : B v v ≠ 0 := fun h0 => by
    have := h2 v hv
    rw [h0] at this
    simp at this
  have hcc : c * (starRingEnd ℂ) c = 1 := by
    have e' : (c * (starRingEnd ℂ) c) * B v v = 1 * B v v := by
      rw [one_mul]
      exact (by ring : (c * (starRingEnd ℂ) c) * B v v = (starRingEnd ℂ) c * (c * B v v)).trans e
    exact mul_right_cancel₀ hB e'
  rw [Complex.mul_conj] at hcc
  have hn : ‖c‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact_mod_cast hcc
  have h0 := norm_nonneg c
  have h4 : (‖c‖ - 1) * (‖c‖ + 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.1 h4 with h5 | h5 <;> linarith

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Maps

def idH {N : ℕ} (X : GRep k N) : X.ρ.IntertwiningMap X.ρ where
  toLinearMap := LinearMap.id
  isIntertwining' _ := rfl

def zeroH {N : ℕ} (X Y : GRep k N) : X.ρ.IntertwiningMap Y.ρ where
  toLinearMap := 0
  isIntertwining' _ := by ext; simp

def inclLe {N : ℕ} {X : GRep k N} {S T : Subrepresentation X.ρ} (h : S.toSubmodule ≤ T.toSubmodule) :
    (subG S).ρ.IntertwiningMap (subG T).ρ where
  toLinearMap := Submodule.inclusion h
  isIntertwining' _ := by ext; rfl

theorem DM_proj_incl (ψ : AddChar k Circle) (j : ℕ) {N n : ℕ} (e : N = n + j) {X : GRep k N}
    (S T : Subrepresentation X.ρ) (hc : IsCompl T.toSubmodule S.toSubmodule) (a : (derivB ψ j ((subG S).cast e)).V) :
    DM ψ j e (X := X) (Y := subG S) (subProj T S hc) (DM ψ j e (X := subG S) (Y := X) (subIncl S) a) = a :=
  (DM_comp ψ j e (subIncl S) (subProj T S hc) (idH _) (fun v => (subProj_subIncl_right T S hc v).symm) a).symm.trans
    (DM_id ψ j e (idH _) (fun _ => rfl) a)

theorem DM_subIncl_injective (ψ : AddChar k Circle) (j : ℕ) {N n : ℕ} (e : N = n + j) {X : GRep k N}
    (S T : Subrepresentation X.ρ) (hc : IsCompl T.toSubmodule S.toSubmodule) :
    Function.Injective (DM ψ j e (X := subG S) (Y := X) (subIncl S)) := fun a b hab => by
  rw [← DM_proj_incl ψ j e S T hc a, ← DM_proj_incl ψ j e S T hc b, hab]

theorem nontrivial_of_nd (ψ : AddChar k Circle) {N j : ℕ} (X : GRep k N) (h : ND ψ X j) : Nontrivial X.V := by
  obtain ⟨n, e, hnt⟩ := h
  by_contra hX
  rw [not_nontrivial_iff_subsingleton] at hX
  obtain ⟨y, hy⟩ := exists_ne (0 : (derivB ψ j (X.cast e)).V)
  apply hy
  rw [← DM_id ψ j e (idH X) (fun _ => rfl) y]
  exact DM_zero ψ j e (idH X) (fun v => Subsingleton.elim _ _) y

theorem nd_mono (ψ : AddChar k Circle) {N h : ℕ} {X : GRep k N} (S₀ S T₀ : Subrepresentation X.ρ)
    (hle : S₀.toSubmodule ≤ S.toSubmodule) (hc : IsCompl T₀.toSubmodule S₀.toSubmodule) (hnd : ND ψ (subG S₀) h) :
    ND ψ (subG S) h := by
  obtain ⟨n, e, hnt⟩ := hnd
  refine ⟨n, e, ?_⟩
  by_contra hS
  rw [not_nontrivial_iff_subsingleton] at hS
  obtain ⟨a, ha⟩ := exists_ne (0 : (derivB ψ h ((subG S₀).cast e)).V)
  apply ha
  apply DM_subIncl_injective ψ h e S₀ T₀ hc
  rw [DM_comp ψ h e (inclLe hle) (subIncl S) (subIncl S₀) (fun v => rfl) a,
    Subsingleton.elim (DM ψ h e (inclLe hle) a) 0, map_zero, map_zero]

end Maps

section Steps

theorem exists_top (ψ : AddChar k Circle) {N : ℕ} (X : GRep k N) {j₀ : ℕ} (h₀ : ND ψ X j₀) :
    ∃ j, j₀ ≤ j ∧ ND ψ X j ∧ ∀ j', j < j' → ¬ ND ψ X j' := by
  classical
  refine ⟨Nat.findGreatest (ND ψ X) N, Nat.le_findGreatest (le_of_nd ψ X h₀) h₀,
    Nat.findGreatest_spec (le_of_nd ψ X h₀) h₀, fun j' hlt hj' => ?_⟩
  exact Nat.findGreatest_is_greatest hlt (le_of_nd ψ X hj') hj'

theorem exists_nd_pos (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ} (X : GRep k N)
    (hN : 0 < N) (hs : IsSmooth X.ρ) (hX : Nontrivial X.V) : ∃ j, 1 ≤ j ∧ ND ψ X j := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  obtain ⟨n, hn, hnt⟩ := GlobalTheory.T.exists_nontrivial_derivative k ψ hψc hψ1 m (resM k X.ρ).V (resM k X.ρ).ρ
    (fun v => (hs v).preimage continuous_subtype_val) hX
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨E⟩ := GlobalTheory.T.twisted_jacquet_iterated_phi_equiv k ψ n j (resM k X.ρ)
  exact ⟨j + 1, by omega, n, rfl, E.symm.injective.nontrivial⟩

theorem norm_dpow_sc (n : ℕ) (s : ℝ) (x : kˣ) :
    ‖((dpow n s (Prod.sc n x) : ℂˣ) : ℂ)‖ = nabs k x ^ ((n : ℝ) * s) := by
  have hdet : GeneralLinearGroup.det (Prod.sc n x) = x ^ n := by
    ext; simp [Prod.sc]
  simp only [dpow, detChar_apply, hdet]
  rw [val_absPow_ofReal, Complex.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k _).le _)]
  rw [show nabs k (x ^ n) = nabs k x ^ n by simp [nabs, map_pow]]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (nabs_pos' k x).le]

theorem exists_eig_top (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) (hT : DerivTop k) {n j : ℕ}
    (π : GRep k (n + j)) (hj : 1 ≤ j) (hs : IsSmooth π.ρ) (hi : π.ρ.IsIrreducible) (hu : IsUnitarisable π.ρ)
    (htop : Prod.IsTopD ψ π) (x : kˣ) :
    ∃ (v : (derivB ψ j π).V) (c : ℂ), v ≠ 0 ∧ (derivB ψ j π).ρ (Prod.sc n x) v = c • v ∧
      ‖c‖ = nabs k x ^ ((n : ℝ) * ((j : ℝ) - 1) / 2) := by
  obtain ⟨hirr, hunit⟩ := hT ψ hψc hψ1 n j π hj hs hi hu htop.1 htop.2
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hDs : IsSmooth (derivB ψ (j' + 1) π).ρ := GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ j' hs
  have hTs : IsSmooth ((derivB ψ (j' + 1) π).tw ((1 - ((j' + 1 : ℕ) : ℝ)) / 2)).ρ :=
    isSmooth_twist hDs (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar
  have := hirr
  obtain ⟨c', hc'⟩ := GroundTheory.Automorphic.exists_central_character
    ((PositivityTheory.PfBern.Props1.isSmooth_found_iff _).2 hTs) (z := Prod.sc n x)
    (Submonoid.mem_center_iff.2 fun g => (GlobalTheory.CuspRep.scalar_comm x g).symm)
  have : Nontrivial (derivB ψ (j' + 1) π).V := htop.1
  obtain ⟨v, hv⟩ := exists_ne (0 : (derivB ψ (j' + 1) π).V)
  have h1 := norm_eq_one_of_unitarisable hunit (Prod.sc n x) hv (hc' v)
  set d : ℂ := ((dpow n ((1 - ((j' + 1 : ℕ) : ℝ)) / 2) (Prod.sc n x) : ℂˣ) : ℂ) with hd
  have htw : ((derivB ψ (j' + 1) π).tw ((1 - ((j' + 1 : ℕ) : ℝ)) / 2)).ρ (Prod.sc n x) v =
      d • (derivB ψ (j' + 1) π).ρ (Prod.sc n x) v := rfl
  have hd0 : d ≠ 0 := Units.ne_zero _
  refine ⟨v, d⁻¹ * c', hv, ?_, ?_⟩
  · have hc'' : c' • v = d • (derivB ψ (j' + 1) π).ρ (Prod.sc n x) v := (hc' v).symm.trans htw
    rw [mul_smul, hc'', smul_smul, inv_mul_cancel₀ hd0, one_smul]
  · rw [norm_mul, h1, mul_one, norm_inv, hd, norm_dpow_sc, ← Real.rpow_neg (nabs_pos' k x).le]
    congr 1
    push_cast
    ring

end Steps

section Main

theorem irreducible_of_top (ψ : AddChar k Circle) {N n h : ℕ} (X : GRep k N) (e : N = n + h) [Nontrivial X.V]
    (hcompl : ∀ S : Subrepresentation X.ρ, ∃ T : Subrepresentation X.ρ, IsCompl S.toSubmodule T.toSubmodule)
    (hdepth : ∀ S : Subrepresentation X.ρ, S ≠ ⊥ → ND ψ (subG S) h)
    {Z : Type} [AddCommGroup Z] [Module ℂ Z] (τ : Representation ℂ (GL (Fin n) k) Z) (hτ : τ.IsIrreducible)
    (χ : GL (Fin n) k →* ℂˣ) (eqv : (derivB ψ h (X.cast e)).ρ.Equiv (twist τ χ)) : X.ρ.IsIrreducible := by
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h0 => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule ℂ X.V) (congrArg Subrepresentation.toSubmodule h0)
  · by_contra hS
    rw [not_or] at hS
    obtain ⟨hS0, hS1⟩ := hS
    obtain ⟨T, hc⟩ := hcompl S
    have hT0 : T ≠ ⊥ := by
      rintro rfl
      apply hS1
      apply Subrepresentation.toSubmodule_injective
      have h2 := hc.sup_eq_top
      rw [show (⊥ : Subrepresentation X.ρ).toSubmodule = ⊥ from rfl, sup_bot_eq] at h2
      exact h2
    have := (nd_iff ψ (subG S) e).1 (hdepth S hS0)
    have := (nd_iff ψ (subG T) e).1 (hdepth T hT0)
    have h0 : ∀ a, DM ψ h e (X := X) (Y := subG T) (subProj S T hc)
        (DM ψ h e (X := subG S) (Y := X) (subIncl S) a) = 0 := fun a =>
      (DM_comp ψ h e (X := subG S) (Y := X) (Z := subG T) (subIncl S) (subProj S T hc) (zeroH _ _)
        (fun v => (subProj_subIncl_left S T hc v).symm) a).symm.trans (DM_zero ψ h e _ (fun _ => rfl) a)
    have key := range_ne_bot_ne_top (DM ψ h e (X := subG S) (Y := X) (subIncl S)).toLinearMap
      (DM ψ h e (X := subG T) (Y := X) (subIncl T)).toLinearMap
      (DM ψ h e (X := X) (Y := subG T) (subProj S T hc)).toLinearMap
      (DM_subIncl_injective ψ h e S T hc.symm)
      h0 (DM_proj_incl ψ h e T S hc)
    rcases eq_bot_or_eq_top_of_equiv_twist eqv hτ
        (LinearMap.range (DM ψ h e (X := subG S) (Y := X) (subIncl S)).toLinearMap) (by
        rintro g _ ⟨a, rfl⟩
        exact ⟨_, DM_comm ψ h e (subIncl S) g a⟩) with h1 | h1
    · exact key.1 h1
    · exact key.2 h1

theorem nd_of_irr (hT : DerivTop k) (hP : PosProdD k) (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ1 : ψ ≠ 1)
    {r t : ℕ} (π₁ : GRep k r) (π₂ : GRep k t) (s₁ : IsSmooth π₁.ρ) (i₁ : π₁.ρ.IsIrreducible)
    (u₁ : IsUnitarisable π₁.ρ) (s₂ : IsSmooth π₂.ρ) (i₂ : π₂.ρ.IsIrreducible) (u₂ : IsUnitarisable π₂.ρ)
    {n h : ℕ} (e : r + t = n + h) (htop : Prod.IsTopD ψ ((π₁.prod π₂).cast e)) (hsm : IsSmooth (π₁.prod π₂).ρ)
    (hun : IsUnitarisable (π₁.prod π₂).ρ)
    (hcompl : ∀ S : Subrepresentation (π₁.prod π₂).ρ, ∃ T : Subrepresentation (π₁.prod π₂).ρ,
      IsCompl S.toSubmodule T.toSubmodule)
    (S₀ : Subrepresentation (π₁.prod π₂).ρ) (hS₀ : S₀ ≠ ⊥) (hirr : S₀.toRepresentation.IsIrreducible) :
    ND ψ (subG S₀) h := by
  have hS₀nt : Nontrivial (subG S₀).V :=
    Submodule.nontrivial_iff_ne_bot.2 (fun h0 => hS₀ (Subrepresentation.toSubmodule_injective h0))
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · exact ⟨r + t, rfl, hS₀nt⟩
  have htop' := (isTopD_iff ψ _ e).1 htop
  have hN : 0 < r + t := by have := le_of_nd ψ _ htop'.1; omega
  obtain ⟨j₀, hj₀, hnd₀⟩ := exists_nd_pos ψ hψc hψ1 (subG S₀) hN (isSmooth_sub hsm S₀) hS₀nt
  obtain ⟨j, hjj, hndj, hgreat⟩ := exists_top ψ (subG S₀) hnd₀
  obtain ⟨T₀, hc⟩ := hcompl S₀
  have hjN := le_of_nd ψ _ hndj
  have ej : r + t = (r + t - j) + j := by omega
  have hinj := DM_subIncl_injective ψ j ej S₀ T₀ hc.symm
  rcases lt_trichotomy j h with hlt | heq | hgt
  · exfalso
    have htopS : Prod.IsTopD ψ ((subG S₀).cast ej) := (isTopD_iff ψ (subG S₀) ej).2 ⟨hndj, hgreat⟩
    obtain ⟨x, hx⟩ := GlobalTheory.CompanionTheory.CellOff.exists_nabs_lt k
    obtain ⟨v, c, hv0, hv, hc'⟩ := exists_eig_top ψ hψc hψ1 hT ((subG S₀).cast ej) (by omega)
      ((isSmooth_cast ej _).2 (isSmooth_sub hsm S₀)) ((isIrreducible_cast ej _).2 hirr)
      ((isUnitarisable_cast ej _).2 (isUnitarisable_sub hun S₀)) htopS x
    have hne : DM ψ j ej (X := subG S₀) (Y := π₁.prod π₂) (subIncl S₀) v ≠ 0 := fun h0 =>
      hv0 (hinj (h0.trans (map_zero _).symm))
    have hev : (derivB ψ j ((π₁.prod π₂).cast ej)).ρ (Prod.sc (r + t - j) x)
        (DM ψ j ej (X := subG S₀) (Y := π₁.prod π₂) (subIncl S₀) v) =
        c • DM ψ j ej (X := subG S₀) (Y := π₁.prod π₂) (subIncl S₀) v := by
      rw [← DM_comm ψ j ej (subIncl S₀) (Prod.sc (r + t - j) x) v, hv, map_smul]
    have hlt' := hP ψ hψc hψ1 r t π₁ π₂ s₁ i₁ u₁ s₂ i₂ u₂ n h e htop (r + t - j) j ej hlt x hx _ c hne hev
    linarith
  · exact heq ▸ hndj
  · exfalso
    have : Nontrivial (derivB ψ j ((subG S₀).cast ej)).V := (nd_iff ψ _ ej).1 hndj
    exact htop'.2 j hgt ⟨_, ej, hinj.nontrivial⟩

theorem prod_irreducible (hT : DerivTop k) (hP : PosProdD k) (hTop : TopProdD k) (ψ : AddChar k Circle)
    (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) : ∀ (N r t : ℕ), r + t = N → ∀ (π₁ : GRep k r) (π₂ : GRep k t),
      IsSmooth π₁.ρ → π₁.ρ.IsIrreducible → IsUnitarisable π₁.ρ → IsSmooth π₂.ρ → π₂.ρ.IsIrreducible →
      IsUnitarisable π₂.ρ → (π₁.prod π₂).ρ.IsIrreducible := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro r t hN π₁ π₂ s₁ i₁ u₁ s₂ i₂ u₂
  obtain ⟨E⟩ := GlobalTheory.CompanionTheory.HighestDeriv.nonempty_prod2_equiv π₁.ρ π₂.ρ
  rcases Nat.eq_zero_or_pos N with hN0 | hpos
  · subst hN0
    obtain ⟨rfl, rfl⟩ : r = 0 ∧ t = 0 := ⟨by omega, by omega⟩
    exact (GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv E).2
      (PositivityTheory.PfBern.Props2.prodGL0Irreducible_at _ _ π₁.ρ π₂.ρ i₁ i₂)
  obtain ⟨n, h, e, hh, htop, r', t', e₂, σ₁, σ₂, χ, sm1, ir1, un1, sm2, ir2, un2, ⟨eqv⟩⟩ :=
    hTop ψ hψc hψ1 r t π₁ π₂ s₁ i₁ u₁ s₂ i₂ u₂ (by omega)
  have hY := IH n (by omega) r' t' e₂ σ₁ σ₂ sm1 ir1 un1 sm2 ir2 un2
  have hadm : IsAdmissible (π₁.prod π₂).ρ := PositivityTheory.PfBern.Props1.isAdmissible_of_equiv E
    (PositivityTheory.PfBern.Props1.admissibleProd_holds k r t π₁.V π₂.V π₁.ρ π₂.ρ
      (PositivityTheory.PfBern.Props1.irrSmoothAdmissible_holds k r π₁.V π₁.ρ s₁ i₁)
      (PositivityTheory.PfBern.Props1.irrSmoothAdmissible_holds k t π₂.V π₂.ρ s₂ i₂))
  have hun : IsUnitarisable (π₁.prod π₂).ρ :=
    isUnitarisable_of_equiv E (GlobalTheory.SmGL.UnitInd.isUnitarisable_prod₂ u₁ u₂)
  have hcompl := PositivityTheory.PfBern.Props2.unitaryAdmissibleComplement_at (r + t) _ (π₁.prod π₂).ρ hadm hun
  have : Nontrivial (π₁.prod π₂).V := nontrivial_of_nd ψ _ ((isTopD_iff ψ _ e).1 htop).1
  refine irreducible_of_top ψ (π₁.prod π₂) e hcompl (fun S hS => ?_) _ ((isIrreducible_cast e₂ _).2 hY) χ eqv
  obtain ⟨S₀, hS₀, hle, hirr⟩ := exists_irreducible_le (π₁.prod π₂).ρ (GlobalTheory.T.compact_open_subgroups_basis k (r + t)) hadm hcompl S hS
  obtain ⟨T₀, hc⟩ := hcompl S₀
  exact nd_mono ψ S₀ S T₀ hle hc.symm
    (nd_of_irr hT hP ψ hψc hψ1 π₁ π₂ s₁ i₁ u₁ s₂ i₂ u₂ e htop hadm.1 hun hcompl S₀ hS₀ hirr)

end Main

variable (k) in

theorem bern_of_parts : DerivTop k → PosProdD k → TopProdD k → BernAt k := by
  intro hT hP hTop r t V W _ _ _ _ π₁ π₂ s₁ i₁ u₁ s₂ i₂ u₂
  obtain ⟨ψ, hψc, hψ1⟩ := PositivityTheory.PfBern.Props1.existsAddChar_holds k
  obtain ⟨E⟩ := GlobalTheory.CompanionTheory.HighestDeriv.nonempty_prod2_equiv π₁ π₂
  exact (GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv E).1
    (prod_irreducible hT hP hTop ψ hψc hψ1 (r + t) r t rfl ⟨V, π₁⟩ ⟨W, π₂⟩ s₁ i₁ u₁ s₂ i₂ u₂)

end PositivityTheory.RgUd.Prod.Asm
