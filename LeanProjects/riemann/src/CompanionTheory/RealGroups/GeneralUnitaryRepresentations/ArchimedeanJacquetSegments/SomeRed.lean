import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Complementary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DualClassInvolutiveImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace CompanionTheory.RgGu.NR

namespace SomeRed

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem intw {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (g : G) (v : V) :
    E.toLinearEquiv (π g v) = σ g (E.toLinearEquiv v) :=
  Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g v

theorem intw' {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (g : G) (v : V) :
    E.toIntertwiningMap.toLinearMap (π g v) = σ g (E.toIntertwiningMap.toLinearMap v) :=
  Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g v

theorem intw_symm {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (g : G) (w : W) :
    E.toLinearEquiv.symm (σ g w) = π g (E.toLinearEquiv.symm w) := by
  apply E.toLinearEquiv.injective
  rw [intw E, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem smooth_of_equiv [TopologicalSpace G] {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ)
    (h : IsSmooth π) : IsSmooth σ := by
  intro w
  have e : {g : G | σ g w = w} = {g : G | π g (E.toLinearEquiv.symm w) = E.toLinearEquiv.symm w} := by
    ext g
    simp only [Set.mem_setOf_eq]
    rw [← intw_symm E]
    exact ⟨fun h => by rw [h], fun h => E.toLinearEquiv.symm.injective h⟩
  rw [e]
  exact h _

theorem admissible_of_equiv [TopologicalSpace G] {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ)
    (h : IsAdmissible π) : IsAdmissible σ := by
  refine ⟨smooth_of_equiv E h.1, fun K hK hc => ?_⟩
  haveI := h.2 K hK hc
  have hle : fixed σ K ≤ (fixed π K).map E.toLinearEquiv.toLinearMap := by
    intro w hw
    refine ⟨E.toLinearEquiv.symm w, ?_, E.toLinearEquiv.apply_symm_apply w⟩
    intro x
    have hx := hw x
    show π (x : G) (E.toLinearEquiv.symm w) = _
    rw [← intw_symm E]
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at hx ⊢
    rw [hx]
  exact Submodule.finiteDimensional_of_le hle

theorem sesq_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (h : HasSesq σ) :
    HasSesq π := by
  obtain ⟨B, hB, hi⟩ := h
  refine ⟨(B.comp E.toLinearEquiv.toLinearMap).compl₂ E.toLinearEquiv.toLinearMap, ?_, fun g v w => ?_⟩
  · intro h0
    apply hB
    ext v w
    have := LinearMap.congr_fun (LinearMap.congr_fun h0 (E.toLinearEquiv.symm v)) (E.toLinearEquiv.symm w)
    have e1 : E.toIntertwiningMap.toLinearMap (E.toLinearEquiv.symm v) = v := E.toLinearEquiv.apply_symm_apply v
    have e2 : E.toIntertwiningMap.toLinearMap (E.toLinearEquiv.symm w) = w := E.toLinearEquiv.apply_symm_apply w
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.zero_apply] at this ⊢
    rw [e1, e2] at this
    exact this
  · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply]
    rw [intw' E, intw' E, hi]

theorem unit_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (h : IsUnitarisable π) :
    IsUnitarisable σ :=
  GlobalTheory.GenericUnitary.isUnitarisable_of_equiv E h

theorem irr_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (h : π.IsIrreducible) :
    σ.IsIrreducible :=
  GlobalTheory.Parabolic.isIrreducible_of_equiv E h

theorem unit_twist {ρ : Representation ℂ G V} (h : IsUnitarisable ρ) (χ : G →* ℂˣ) (hχ : ∀ g, ‖(χ g : ℂ)‖ = 1) :
    IsUnitarisable (twist ρ χ) := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨B, h1, h2, fun g v w => ?_⟩
  show B ((χ g : ℂ) • ρ g v) ((χ g : ℂ) • ρ g w) = B v w
  rw [B.map_smul, LinearMap.smul_apply, (B _).map_smulₛₗ, h3, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Complex.mul_conj', hχ g]
  simp

end SomeRed

open SomeRed

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem chi_apply (d : ℕ) (s : ℝ) (g : Levi k fun _ : Fin 2 => Fin d) :
    (chi k d s g : ℂ) = ((nabs k (Matrix.GeneralLinearGroup.det (g 0)) : ℝ) : ℂ) ^ (-(s : ℂ)) *
      ((nabs k (Matrix.GeneralLinearGroup.det (g 1)) : ℝ) : ℂ) ^ (s : ℂ) := by
  simp [chi, val_absPow]

theorem norm_chi (d : ℕ) (s : ℝ) (g : Levi k fun _ : Fin 2 => Fin d) :
    ‖(chi k d s g : ℂ)‖ = nabs k (Matrix.GeneralLinearGroup.det (g 0)) ^ (-s) *
      nabs k (Matrix.GeneralLinearGroup.det (g 1)) ^ s := by
  rw [chi_apply, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (nabs_pos' k _),
    Complex.norm_cpow_eq_rpow_re_of_pos (nabs_pos' k _)]
  simp

set_option maxHeartbeats 2000000 in
theorem someRed_of (h1 : Complementary) (h2 : Compact k) (h3 : Bound k) (h4 : Herm k) (h5 : ProdModel k) :
    SomeRed k := by
  intro x hx hu
  by_contra hcon
  push_neg at hcon
  set d := x.1 with hdd
  have hd2 : ∀ s : ℝ, ∑ a, (![x.nu (-(s : ℂ)), x.nu (s : ℂ)] a).1 = x.1 + x.1 := fun s => by
    simp [Fin.sum_univ_two, IrrGL.nu]
  have hirr : ∀ s : ℝ, 0 ≤ s → (prodIrr ![x.nu (-(s : ℂ)), x.nu (s : ℂ)] (hd2 s)).IsIrreducible := by
    intro s hs
    obtain ⟨N, hd, hi⟩ := hcon s hs
    have e : N = x.1 + x.1 := hd.symm.trans (hd2 s)
    subst e
    exact hi
  let τ := piTensor fun _ : Fin 2 => x.rep
  obtain ⟨K₀, F, hKo, hKc, hF, hFe⟩ := h2 d _ τ
  have hE : ∀ s : ℝ, (F s).Equiv (prodIrr ![x.nu (-(s : ℂ)), x.nu (s : ℂ)] (hd2 s)) := fun s =>
    (hFe s).some.trans (h5 x s (hd2 s)).some.symm
  have hsm : ∀ s : ℝ, IsSmooth (prodIrr ![x.nu (-(s : ℂ)), x.nu (s : ℂ)] (hd2 s)) := fun s => isSmooth_prodIrr _ _
  have hadm : ∀ s : ℝ, 0 ≤ s → IsAdmissible (prodIrr ![x.nu (-(s : ℂ)), x.nu (s : ℂ)] (hd2 s)) := fun s hs =>
    GlobalTheory.CompanionTheory.BZCuspPair.irrAdm k _ _ _ (hsm s) (hirr s hs)
  have hxu : IsUnitarisable τ := GlobalTheory.SmGL.UnitInd.isUnitarisable_piTensor fun _ => hu
  have hU0 : IsUnitarisable (F 0) := by
    refine unit_of_equiv (hFe 0).some.symm (GlobalTheory.SmGL.UnitInd.isUnitarisable_parInd _ (unit_twist hxu _ fun g => ?_))
    rw [norm_chi]
    simp
  have hUs := h1 _ _ K₀ hKo hKc F hF (fun s hs => ⟨admissible_of_equiv (hE s).symm (hadm s hs),
    smooth_of_equiv (hE s).symm (hsm s), irr_of_equiv (hE s).symm (hirr s hs),
    sesq_of_equiv (hE s) (h4 x hu s _ (hd2 s) (hirr s hs))⟩) hU0

  have hd0 : 0 < d := hx.1
  set s : ℝ := (d : ℝ) with hs
  have hs0 : 0 ≤ s := by positivity
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar x.2.rep.smooth x.2.rep.irr
  obtain ⟨t, -, ht⟩ := GlobalTheory.CentralExponent.exists_nabs_lt_one k
  have hω1 : ‖(ω t : ℂ)‖ = 1 := by
    obtain ⟨B, b1, b2, b3⟩ := hu
    haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible x.2.rep.irr
    obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
    have e := b3 (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) v v
    rw [hω t v, B.map_smul, LinearMap.smul_apply, (B _).map_smulₛₗ, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      Complex.mul_conj'] at e
    have hp := b2 v hv
    have hne : B v v ≠ 0 := fun h0 => by rw [h0] at hp; simp at hp
    have e2 : ((‖(ω t : ℂ)‖ ^ 2 : ℝ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hne (e.trans (one_mul _).symm)
      exact_mod_cast this
    have e3 : ‖(ω t : ℂ)‖ ^ 2 = 1 := by exact_mod_cast e2
    have hn := norm_nonneg (ω t : ℂ)
    nlinarith
  let g : Levi k fun _ : Fin 2 => Fin d := ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1]
  let c : ℂ := (chi k d s g : ℂ) * (ω t : ℂ)
  have hτ : ∀ w, τ g w = (ω t : ℂ) • w := by
    intro w
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      have hfun : (fun a : Fin 2 => x.rep (g a) (f a)) = Function.update f 0 ((ω t : ℂ) • f 0) := by
        funext a
        fin_cases a
        · simp [g]
          exact hω t (f 0)
        · simp [g]
      rw [map_smul, piTensor_tprod, hfun, MultilinearMap.map_update_smul, Function.update_eq_self, smul_comm]
    | add a b ha hb => rw [map_add, ha, hb, smul_add]
  have hc : ∀ w, twist τ (chi k d s) g w = c • w := fun w => by
    show (chi k d s g : ℂ) • τ g w = c • w
    rw [hτ, smul_smul]
  have hW : Nontrivial (PiTensorProduct ℂ fun _ : Fin 2 => x.2.rep.V) := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    have hi := irr_of_equiv (hFe s).some (irr_of_equiv (hE s).symm (hirr s hs0))
    haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hi
    obtain ⟨f, f', hff⟩ := exists_pair_ne (IndSp (blk2 d) (twist τ (chi k d s)))
    exact hff (Subtype.ext (Subtype.ext (funext fun _ => Subsingleton.elim _ _)))
  have hb := h3 d _ (twist τ (chi k d s))
    (isSmooth_twist (isSmooth_piTensor fun _ => x.2.rep.smooth)
      (((isSmoothChar_absPow (-(s : ℂ))).detChar.comp _ (continuous_apply 0)).mul
        ((isSmoothChar_absPow (s : ℂ)).detChar.comp _ (continuous_apply 1))))
    (admissible_of_equiv ((hE s).symm.trans (hFe s).some) (hadm s hs0))
    (unit_of_equiv (hFe s).some (hUs s hs0)) t c ht.le hc
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin d) t) = t ^ d := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
  have hnp : ∀ m : ℕ, nabs k (t ^ m) = nabs k t ^ m := fun m => by simp [nabs]
  have hn1 : nabs k (1 : kˣ) = 1 := by simp [nabs]
  have htp : 0 < nabs k t := nabs_pos' k t
  have hnc : ‖c‖ = nabs k t ^ (-((d : ℝ) * s)) := by
    simp only [c, norm_mul, hω1, mul_one, norm_chi]
    have e0 : g 0 = Matrix.GeneralLinearGroup.scalar (Fin d) t := rfl
    have e1 : g 1 = 1 := rfl
    rw [e0, e1, hdet, hnp, map_one, hn1, Real.one_rpow, mul_one, ← Real.rpow_natCast, ← Real.rpow_mul htp.le]
    ring_nf
  rw [hnc, ← Real.rpow_add htp] at hb
  have hlt : 1 < nabs k t ^ (-((d : ℝ) * s) + ((d * d : ℕ) : ℝ) / 2) := by
    refine Real.one_lt_rpow_of_pos_of_lt_one_of_neg htp ht ?_
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    rw [hs]
    push_cast
    nlinarith
  linarith

end CompanionTheory.RgGu.NR

end
