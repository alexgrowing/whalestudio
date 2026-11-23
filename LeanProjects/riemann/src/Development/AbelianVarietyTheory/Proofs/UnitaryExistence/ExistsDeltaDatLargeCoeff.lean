import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentWeight

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.SplitPrimeData

theorem exists_char_ne_one {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R) [Finite (R ⧸ I)]
    {r : ℕ} (hr : 1 ≤ r) (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) (h2 : (-1 : (R ⧸ I)ˣ) ≠ 1) :
    ∃ ψ : (Q ≃ₗ[R] Q) →* ℂˣ, ψ ≠ 1 := by
  classical
  have hs : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  let cj : (Q ≃ₗ[R] Q) →* ((Fin r → R ⧸ I) ≃ₗ[R ⧸ I] (Fin r → R ⧸ I)) :=
    MonoidHom.mk' (fun k => (e.symm ≪≫ₗ k ≪≫ₗ e).extendScalarsOfSurjective hs) (fun a b => by
      ext x i
      simp [LinearEquiv.mul_apply])
  let i₀ : Fin r := ⟨0, hr⟩
  let δ : Fin r → R ⧸ I := Function.update 1 i₀ (-1)
  have hδ : Matrix.diagonal δ * Matrix.diagonal δ = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : i = i₀
    · subst h; simp [δ]
    · simp [δ, h]
  let g : (Fin r → R ⧸ I) ≃ₗ[R ⧸ I] (Fin r → R ⧸ I) := Matrix.toLin'OfInv hδ hδ
  have hg : LinearEquiv.det g = -1 := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    have : (g : (Fin r → R ⧸ I) →ₗ[R ⧸ I] (Fin r → R ⧸ I)) = Matrix.toLin' (Matrix.diagonal δ) := rfl
    rw [this, LinearMap.det_toLin', Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  have hk : cj (e ≪≫ₗ g.restrictScalars R ≪≫ₗ e.symm) = g := by
    ext x i
    simp [cj]
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (R ⧸ I)ˣ ℂ h2
  refine ⟨φ.comp (LinearEquiv.det.comp cj), fun h => hφ ?_⟩
  have := DFunLike.congr_fun h (e ≪≫ₗ g.restrictScalars R ≪≫ₗ e.symm)
  rwa [MonoidHom.comp_apply, MonoidHom.comp_apply, hk, hg] at this

theorem value_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {N : ℕ} (hN : 0 < N) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hm : ζ ∈ c.F) (f : Rul Xo c) (hf : f ^ N = 1) (y : FrPt Xo c (CAt c.F.val.toRingHom))
    (h0 : evR Xo c f y ≠ 0) : ∃ a : c.F, evR Xo c f y = algebraMap c.F (CAt c.F.val.toRingHom) a := by
  have : IsDomain (CAt c.F.val.toRingHom) := inferInstanceAs (IsDomain ℂ)
  have hmul : ∀ a b : Rul Xo c, evR Xo c (a * b) y = evR Xo c a y * evR Xo c b y :=
    fun a b => evalAt_mul _ _ a b y
  have e₁ : evR Xo c 1 y = 1 := by
    have := hmul f 1
    rw [mul_one] at this
    exact (mul_eq_left₀ h0).1 this.symm
  have e₂ : ∀ m : ℕ, evR Xo c (f ^ m) y = evR Xo c f y ^ m := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, e₁]
    | succ m ih => rw [pow_succ, pow_succ, hmul, ih]
  have e₃ := e₂ N
  rw [hf, e₁] at e₃
  have : NeZero N := ⟨hN.ne'⟩
  let z : ℂ := evR Xo c f (S := CAt c.F.val.toRingHom) y
  have e₄ : z ^ N = 1 := e₃.symm
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one e₄
  exact ⟨⟨ζ ^ i, pow_mem hm i⟩, hi.symm⟩

theorem exists_deltaDat_large_coeff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (p : ℕ), p.Prime → 5 ≤ p → p.Coprime l.M → jacobiSym (-(H.d : ℤ)) p = 1 → ∃ (I : Ideal (𝓞 E)) (c' : Coeff l), c.F ≤ c'.F ∧ ∀ c'' : Coeff l, c'.F ≤ c''.F → ∀ n : ℕ, ∃ d : DeltaDat Xo c'' n, d.pd = p ∧ d.I = I ∧ d.IsLev ∧ d.l₂.A = 1 ∧ (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧ (∃ m : ℕ, 0 < m ∧ d.cδ ^ m = 1) ∧ (∀ y : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom), ∃ a : d.c₂.F, evR d.Xo₂ d.c₂ d.cδ y = algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom) a) ∧ (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, ψ ≠ 1 ∧ d.PhiPin ph ψ x₀ ∧ d.PsiTie ψ) := by
  intro E _ _ _ H Dw l Xo c hr hA pd hp h5 hcop hj
  classical
  have hp2 : pd ≠ 2 := by omega
  obtain ⟨I, hK, hprod, hI⟩ := (GlobalTheory.exists_level_mul_split E H l).2 pd hp hp2 hj
  obtain ⟨l₂, hdvd, hM, hMb, hA₂⟩ := (GlobalTheory.exists_level_mul_split E H l).1 pd I (hp.odd_of_ne_two hp2) hcop hK hprod hI
  rw [hA] at hA₂
  obtain ⟨Xo₂⟩ := GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.1 E H Dw l₂ hr
  obtain ⟨g₀, ty, hty⟩ := (PeriodExists.typeFn_period_exist E H Dw).1
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H Dw l₂ Xo₂ (KA l₂).val.toRingHom g₀ ty hr rfl hty
  have hpI : (pd : 𝓞 E) ∈ I := CharacterFunction.natCast_mem_half hM hMb
  have hI0 : I ≠ ⊥ := fun e => hp.ne_zero (by rw [e, Ideal.mem_bot] at hpI; exact_mod_cast hpI)
  have : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI0
  have := Dw.fin
  have := Dw.proj
  have := c.fin
  obtain ⟨e⟩ := HalfPairing.nonempty_equiv_quot (N := Dw.La) I _ Dw.rank
  have : Finite (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La)) := Finite.of_equiv _ e.symm.toEquiv
  have : Finite ((Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La)) ≃ₗ[𝓞 E] (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La))) :=
    Finite.of_injective _ DFunLike.coe_injective
  have hItop : I ≠ ⊤ := by
    rintro rfl
    rw [Ideal.map_top, Ideal.top_mul, eq_comm, Ideal.span_singleton_eq_top] at hprod
    have h1 : IsUnit ((pd : ℤ)) := by
      have hu : IsUnit (algebraMap ℤ (𝓞 E) (pd : ℤ)) := by simpa using hprod
      exact (isUnit_map_iff (algebraMap ℤ (𝓞 E)) _).1 hu
    rcases Int.isUnit_iff.1 h1 with h | h <;> omega
  have h2 : (-1 : (𝓞 E ⧸ I)ˣ) ≠ 1 := by
    intro h
    have h3 : (-1 : 𝓞 E ⧸ I) = 1 := by simpa using congrArg Units.val h
    have h4 : (pd : 𝓞 E ⧸ I) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hpI
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
    rw [hm] at h4
    push_cast at h4
    have := Ideal.Quotient.nontrivial_iff.2 hItop
    exact (one_ne_zero : (1 : 𝓞 E ⧸ I) ≠ 0) (by linear_combination h4 + (m : 𝓞 E ⧸ I) * h3)
  obtain ⟨ψ₀, hψ₀⟩ := exists_char_ne_one I hr e h2
  obtain ⟨N, hN₀, hNψ⟩ : ∃ N : ℕ, 0 < N ∧ ∀ k : ((Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La)) ≃ₗ[𝓞 E]
      (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La))), k ^ N = 1 := ⟨_, Nat.card_pos, fun k => pow_card_eq_one'⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N := ⟨_, Complex.isPrimitiveRoot_exp N hN₀.ne'⟩
  let b := Module.finBasis ℚ c.F
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.exists_coeff_containing E H l₂ (insert ζ (Finset.univ.image fun i => (b i : ℂ))) (by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact IsAlgebraic.of_pow hN₀ (by rw [hζ.pow_eq_one]; exact isAlgebraic_one)
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom c.F.val)
  have hle : c.F ≤ c₀.F := fun x hx => by
    have e := congrArg c.F.val (b.sum_repr ⟨x, hx⟩)
    rw [map_sum] at e
    change _ = x at e
    rw [← e]
    refine sum_mem fun i _ => ?_
    rw [Algebra.smul_def, map_mul, eq_ratCast, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem c₀.F _)
      (hc₀ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  obtain ⟨c₁, hc₁, hχ⟩ := GlobalTheory.CompIdem.exists_coeff_idempotent_sections E H Dw l₂ Xo₂ c₀ hr g₀ ty F hty
  have hKA : KA l = KA l₂ := by rw [KA, KA, hA, hA₂]
  obtain ⟨c', hc'⟩ : ∃ c' : Coeff l, c₁.F = c'.F := by
    refine ⟨⟨c₁.F, c₁.fin, c₁.conj, ?_, ?_⟩, rfl⟩
    · obtain ⟨k, hk⟩ := LevelExist.zeta_eq_pow_of_dvd (a := l.M') (LevelExist.M'_pos l₂)
        (Nat.lcm_dvd (hdvd.1.trans (Nat.dvd_lcm_left _ _)) (hdvd.2.2.trans (Nat.dvd_lcm_right _ _)))
      rw [hk]
      exact pow_mem c₁.zeta_mem k
    · rw [hKA]
      exact c₁.le
  refine ⟨I, c', hc' ▸ hle.trans hc₁, fun c'' hc'' n => ?_⟩
  rw [← hc'] at hc''
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : Coeff l₂, c₂.F = c''.F :=
    ⟨⟨c''.F, c''.fin, c''.conj, hc'' c₁.zeta_mem, hKA ▸ c''.le⟩, rfl⟩
  choose χ hχ₁ _ hχ₂ using hχ c₂ (hc₂ ▸ hc'')
  have hζm : ζ ∈ c''.F := hc'' (hc₁ (hc₀ _ (Finset.mem_insert_self _ _)))
  obtain ⟨ψ, hψ⟩ := CharacterFunction.exists_char_subfield ψ₀ c''.F fun k => by
    have : NeZero N := ⟨hN₀.ne'⟩
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := ((ψ₀ k : ℂˣ) : ℂ)) (by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hNψ, map_one, Units.val_one])
    exact hi ▸ pow_mem hζm i
  have hψ1 : ψ ≠ 1 := fun h => hψ₀ (MonoidHom.ext fun k => Units.ext (by rw [← hψ k, h]; rfl))
  have hN : ∀ k, ψ k ^ N = 1 := fun k => by rw [← map_pow, hNψ, map_one]
  obtain ⟨v, hv₀, hv⟩ := CharacterFunction.exists_component_weight hr hp h5 hM hA₂ hMb ψ Xo₂ c₂ hty F N hN
  obtain ⟨⟨pd', I', l₂', Xo₂', c₂', hF, r, m, nab, cδ, φ₀⟩, rfl, rfl, rfl, e₁, e₂, -, hd, hnab⟩ :=
    GlobalTheory.LevelCover.exists_deltaDat_isLev E H Dw l Xo c'' hr n pd I l₂ Xo₂ c₂ hc₂ hdvd hM hcop hMb hI
  obtain rfl := eq_of_heq e₁
  obtain rfl := eq_of_heq e₂
  obtain ⟨f, hf, hf', hfN⟩ := CharacterFunction.isLev_psiTie _ hd ψ F χ hχ₁ hχ₂ v N hv₀ hv
  have hval : ∀ y : FrPt Xo₂' c₂' (CAt c₂'.F.val.toRingHom), ∃ a : c₂'.F,
      evR Xo₂' c₂' f y = algebraMap c₂'.F (CAt c₂'.F.val.toRingHom) a := fun y =>
    value_mem Xo₂' c₂' hN₀ hζ (hc₂ ▸ hζm) f hfN y
      (@hf.2.2.2.2.2.2.2.2 (CAt c₂'.F.val.toRingHom) (inferInstanceAs (Field ℂ)) (inferInstanceAs (IsAlgClosed ℂ))
        (inferInstanceAs (Algebra c₂'.F (CAt c₂'.F.val.toRingHom))) y)
  by_cases hn : Dw.p + Dw.q ≤ n
  · obtain ⟨φ, ph, x₀, hφ⟩ := GlobalTheory.exists_phiPin_of_character E H Dw l Xo c'' n _ hf hn ψ
    exact ⟨⟨pd', I', l₂', Xo₂', c₂', hF, r, m, nab, f, φ⟩, rfl, rfl, hf, hA₂, hnab, ⟨N, hN₀, hfN⟩, hval,
      fun _ => ⟨ph, ψ, x₀, hψ1, hφ, hf'⟩⟩
  · exact ⟨⟨pd', I', l₂', Xo₂', c₂', hF, r, m, nab, f, φ₀⟩, rfl, rfl, hf, hA₂, hnab, ⟨N, hN₀, hfN⟩, hval,
      fun h => absurd h hn⟩

end GlobalTheory.SplitPrimeData
