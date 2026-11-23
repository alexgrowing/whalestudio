import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.EigInert
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.JacquetLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteria
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlValuedDatum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUniqueStatement
import GroundTheory.GlobalFields.LocalAtPlace

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Eig.GluingInclusion

section Transport

variable {G H : Type} [Group G] [Group H] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {ρ' : Representation ℂ H W} {p : G ≃* H} {e : V ≃ₗ[ℂ] W}

theorem mem_fixed_iff (he : ∀ g v, e (ρ g v) = ρ' (p g) (e v)) {J : Subgroup G} {J' : Subgroup H}
    (hJ : ∀ x, x ∈ J ↔ p x ∈ J') (v : V) : e v ∈ fixed ρ' J' ↔ v ∈ fixed ρ J := by
  simp only [fixed, eig, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq,
    MonoidHom.one_apply, Units.val_one, one_smul, Subtype.forall]
  constructor
  · intro h x hx
    apply e.injective
    rw [he]
    exact h _ ((hJ x).1 hx)
  · intro h y hy
    have hx : p.symm y ∈ J := (hJ _).2 (by simpa using hy)
    have := he (p.symm y) v
    rw [h _ hx, MulEquiv.apply_symm_apply] at this
    exact this.symm

theorem map_fixed (he : ∀ g v, e (ρ g v) = ρ' (p g) (e v)) {J : Subgroup G} {J' : Subgroup H}
    (hJ : ∀ x, x ∈ J ↔ p x ∈ J') : (fixed ρ J).map (e : V →ₗ[ℂ] W) = fixed ρ' J' := by
  ext w
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (mem_fixed_iff he hJ v).2 hv
  · intro hw
    refine ⟨e.symm w, ?_, by simp⟩
    rw [← mem_fixed_iff he hJ]
    simpa using hw

def fixEquiv (he : ∀ g v, e (ρ g v) = ρ' (p g) (e v)) {J : Subgroup G} {J' : Subgroup H}
    (hJ : ∀ x, x ∈ J ↔ p x ∈ J') : fixed ρ J ≃ₗ[ℂ] fixed ρ' J' :=
  (e.submoduleMap (fixed ρ J)).trans (LinearEquiv.ofEq _ _ (map_fixed he hJ))

theorem fixEquiv_apply (he : ∀ g v, e (ρ g v) = ρ' (p g) (e v)) {J : Subgroup G} {J' : Subgroup H}
    (hJ : ∀ x, x ∈ J ↔ p x ∈ J') (v : fixed ρ J) : ((fixEquiv he hJ v : fixed ρ' J') : W) = e v := rfl

theorem hecke_transport (he : ∀ g v, e (ρ g v) = ρ' (p g) (e v)) {J : Subgroup G} {J' : Subgroup H}
    (hJ : ∀ x, x ∈ J ↔ p x ∈ J') (g : G) (U : Module.End ℂ (fixed ρ J)) (hU : PositivityTheory.Lbc.IsHeckeOpG ρ J g U) :
    PositivityTheory.Lbc.IsHeckeOpG ρ' J' (p g) ((fixEquiv he hJ).conj U) := by
  intro v f hf
  have hf0 : ∀ x ∈ J, (f ∘ₗ (e : V →ₗ[ℂ] W)) ∘ₗ ρ x = f ∘ₗ (e : V →ₗ[ℂ] W) := by
    intro x hx
    ext u
    have := LinearMap.congr_fun (hf (p x) ((hJ x).1 hx)) (e u)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this ⊢
    rw [he, this]
  have key := hU ((fixEquiv he hJ).symm v) (f ∘ₗ (e : V →ₗ[ℂ] W)) hf0
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at key
  have h1 : e (((fixEquiv he hJ).symm v : fixed ρ J) : V) = v := by
    rw [← fixEquiv_apply he hJ, LinearEquiv.apply_symm_apply]
  rw [he, h1] at key
  rw [key, LinearEquiv.conj_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [fixEquiv_apply]

theorem admissible_transport [TopologicalSpace G] [TopologicalSpace H] (he : ∀ g v, e (ρ g v) = ρ' (p g) (e v))
    (hp : Continuous p) (hps : Continuous p.symm) (hA : IsAdmissible ρ) : IsAdmissible ρ' := by
  refine ⟨fun w => ?_, fun K' hKo hKc => ?_⟩
  · have e1 : {h : H | ρ' h w = w} = p.symm ⁻¹' {g : G | ρ g (e.symm w) = e.symm w} := by
      ext h
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      have := he (p.symm h) (e.symm w)
      rw [MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
      rw [← this]
      constructor
      · intro h1; apply e.injective; rw [h1]; simp
      · intro h1; rw [h1]; simp
    rw [e1]
    exact (hA.1 _).preimage hps
  · let K : Subgroup G := K'.comap p.toMonoidHom
    have hK : ∀ x, x ∈ K ↔ p x ∈ K' := fun x => Iff.rfl
    have hKo' : IsOpen (K : Set G) := hKo.preimage hp
    have hKc' : IsCompact (K : Set G) := by
      have e2 : (K : Set G) = p.symm '' (K' : Set H) := by
        ext x
        simp only [SetLike.mem_coe, Set.mem_image]
        constructor
        · intro hx; exact ⟨p x, hx, by simp⟩
        · rintro ⟨y, hy, rfl⟩; show p (p.symm y) ∈ K'; simpa using hy
      rw [e2]
      exact hKc.image hps
    have := hA.2 K hKo' hKc'
    exact LinearEquiv.finiteDimensional (fixEquiv he hK)

end Transport

theorem relIndex_transport {G H : Type} [Group G] [Group H] (p : G ≃* H) {J : Subgroup G} {J' : Subgroup H}
    (hJ : ∀ x, x ∈ J ↔ p x ∈ J') (t : G) :
    (J.map (MulAut.conj t).toMonoidHom).relIndex J = (J'.map (MulAut.conj (p t)).toMonoidHom).relIndex J' := by
  have h1 : J.map (MulAut.conj t).toMonoidHom = (J'.map (MulAut.conj (p t)).toMonoidHom).comap p.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_comap, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
      MulAut.conj_symm_apply, hJ]
    simp
  have h2 : J.map p.toMonoidHom = J' := by
    ext y
    rw [Subgroup.mem_map_equiv, hJ, MulEquiv.apply_symm_apply]
  rw [h1, Subgroup.relIndex_comap, h2]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cj_continuous (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with h
  · exact h.choose_spec.1
  · exact continuous_id

theorem mem_iwGL_iff {w : Pl E} (n : ℕ) {ϖ : w.adicCompletion E}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (g : GLw n w) : g ∈ iwGL n w ↔ g ∈ PositivityTheory.SphericalProduct.IwGL (w.adicCompletion E) n := by
  rw [(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1, GlobalTheory.CompanionTheory.IwGLV.mem_IwGL_iff hϖ]
  rfl

theorem mem_iwU_iff_p {n : ℕ} {w : Pl E} {b : GLw n w} {ϖ : w.adicCompletion E}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (p : UL n w ≃* GU (cj w) n) (hp : ∀ x, (p x).1 = b⁻¹ * x.1 * b) (x : UL n w) :
    x ∈ iwU n w b ↔ p x ∈ PositivityTheory.SphericalProduct.IwU (cj w) n := by
  rw [GlobalTheory.CompanionTheory.UnitaryWitt.mem_iwU_iff, PositivityTheory.SphericalProduct.IwU, Subgroup.mem_subgroupOf, hp, mem_iwGL_iff n hϖ]

theorem p_continuous {n : ℕ} {w : Pl E} {b : GLw n w}
    (p : UL n w ≃* GU (cj w) n) (hp : ∀ x, (p x).1 = b⁻¹ * x.1 * b) : Continuous p := by
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  have hc : Continuous fun x : UL n w => b⁻¹ * x.1 * b :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  refine hc.congr fun x => ?_
  rw [Function.comp_apply, hp]

theorem p_symm_val {n : ℕ} {w : Pl E} {b : GLw n w}
    (p : UL n w ≃* GU (cj w) n) (hp : ∀ x, (p x).1 = b⁻¹ * x.1 * b) (g : GU (cj w) n) :
    (p.symm g).1 = b * g.1 * b⁻¹ := by
  have := hp (p.symm g)
  rw [MulEquiv.apply_symm_apply] at this
  rw [this]
  group

theorem p_symm_continuous {n : ℕ} {w : Pl E} {b : GLw n w}
    (p : UL n w ≃* GU (cj w) n) (hp : ∀ x, (p x).1 = b⁻¹ * x.1 * b) : Continuous p.symm := by
  rw [Topology.IsInducing.subtypeVal.continuous_iff]
  have hc : Continuous fun x : GU (cj w) n => b * x.1 * b⁻¹ :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  refine hc.congr fun x => ?_
  rw [Function.comp_apply, p_symm_val p hp]

theorem cone_gap {m : ℕ} {l : Fin m → ℤ} (hl : Cone l) :
    ∀ k : ℕ, ∀ i j : Fin m, (j : ℕ) = i + k + 1 → l j + 2 ≤ l i := by
  intro k
  induction k with
  | zero =>
    intro i j hij
    have := hl.1 i j (by omega)
    omega
  | succ k ih =>
    intro i j hij
    have hk : (i : ℕ) + k + 1 < m := by omega
    have h1 := ih i ⟨(i : ℕ) + k + 1, hk⟩ rfl
    have h2 := hl.1 ⟨(i : ℕ) + k + 1, hk⟩ j (by simp only; omega)
    omega

theorem cone_anti {m : ℕ} {l : Fin m → ℤ} (hl : Cone l) {i j : Fin m} (h : i < j) : l j < l i := by
  have hij : (i : ℕ) < j := h
  have := cone_gap hl ((j : ℕ) - i - 1) i j (by omega)
  omega

theorem wexp_lt (n : ℕ) (l : Fin (n / 2) → ℤ) (i : Fin (n / 2)) (h : (i : ℕ) < n) :
    wexp n l ⟨i, h⟩ = l i := by
  unfold wexp
  rw [dif_pos (show ((⟨i, h⟩ : Fin n) : ℕ) < n / 2 from i.2)]

theorem wexp_rev (n : ℕ) (l : Fin (n / 2) → ℤ) (i : Fin n) : wexp n l i.rev = - wexp n l i := by
  unfold wexp
  have hr : (i.rev : ℕ) = n - 1 - i := by rw [Fin.val_rev]; omega
  have hi := i.2
  by_cases h1 : (i : ℕ) < n / 2
  · have h2 : ¬ (i.rev : ℕ) < n / 2 := by omega
    have h3 : n - 1 - (i.rev : ℕ) < n / 2 := by omega
    have e : (⟨n - 1 - (i.rev : ℕ), h3⟩ : Fin (n / 2)) = ⟨i, h1⟩ := Fin.ext (by show n - 1 - (i.rev : ℕ) = i; omega)
    rw [dif_neg h2, dif_pos h3, dif_pos h1, e]
  · by_cases h4 : n - 1 - (i : ℕ) < n / 2
    · have h5 : (i.rev : ℕ) < n / 2 := by omega
      have e : (⟨(i.rev : ℕ), h5⟩ : Fin (n / 2)) = ⟨n - 1 - i, h4⟩ := Fin.ext (by show (i.rev : ℕ) = n - 1 - i; omega)
      rw [dif_pos h5, dif_neg h1, dif_pos h4, neg_neg, e]
    · have h5 : ¬ (i.rev : ℕ) < n / 2 := by omega
      have h6 : ¬ n - 1 - (i.rev : ℕ) < n / 2 := by omega
      rw [dif_neg h5, dif_neg h6, dif_neg h1, dif_neg h4, neg_zero]

theorem wexp_anti (n : ℕ) {l : Fin (n / 2) → ℤ} (hl : Cone l) {i j : Fin n} (h : i < j) :
    wexp n l j < wexp n l i := by
  have hij : (i : ℕ) < j := h
  have hjn := j.2
  unfold wexp
  by_cases hj : (j : ℕ) < n / 2
  · rw [dif_pos hj, dif_pos (show (i : ℕ) < n / 2 by omega)]
    exact cone_anti hl (Fin.mk_lt_mk.2 hij)
  · rw [dif_neg hj]
    by_cases hi : (i : ℕ) < n / 2
    · rw [dif_pos hi]
      have := hl.2 ⟨i, hi⟩
      split_ifs with hj'
      · have := hl.2 ⟨_, hj'⟩
        omega
      · omega
    · rw [dif_neg hi]
      by_cases hj' : n - 1 - (j : ℕ) < n / 2
      · rw [dif_pos hj']
        by_cases hi' : n - 1 - (i : ℕ) < n / 2
        · rw [dif_pos hi']
          have := cone_anti hl (Fin.mk_lt_mk.2 (show n - 1 - (j : ℕ) < n - 1 - i by omega) :
            (⟨n - 1 - (j : ℕ), hj'⟩ : Fin (n / 2)) < ⟨n - 1 - (i : ℕ), hi'⟩)
          omega
        · rw [dif_neg hi']
          have := hl.2 ⟨_, hj'⟩
          omega
      · exfalso
        omega

theorem S_nonneg (n : ℕ) {l : Fin (n / 2) → ℤ} (hl : Cone l) :
    0 ≤ ∑ i : Fin (n / 2), ((n : ℤ) - 1 - 2 * (i : ℕ)) * l i := by
  refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (by have := hl.2 i; omega)
  have := i.2
  omega

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
theorem tdiag_val {n : ℕ} {w : Pl E} (ϖ : (w.adicCompletion E)ˣ) (a : Fin n → ℤ) :
    ((tdiag ϖ a : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.diagonal fun i => (ϖ : w.adicCompletion E) ^ a i := by
  unfold tdiag
  rw [GlobalTheory.SmGL.val_diagT]
  simp only [Units.val_zpow_eq_zpow_val]

theorem tdiag_mem {n : ℕ} {w : Pl E} (ϖ : (w.adicCompletion E)ˣ) (hc : cj w (ϖ : w.adicCompletion E) = ϖ)
    (l : Fin (n / 2) → ℤ) : tdiag ϖ (wexp n l) ∈ GU (cj w) n := by
  unfold tdiag
  rw [GlobalTheory.CompanionTheory.UnitaryWitt.diagT_mem_UJ_antiJ_iff]
  intro i
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, hc, wexp_rev]
  rw [← zpow_add₀ (Units.ne_zero ϖ)]
  simp

omit [IsCMField E] in
theorem qh_eq {w : Pl E} {ϖ : w.adicCompletion E} {σ : w.adicCompletion E →+* w.adicCompletion E} {q : ℕ}
    (hU : IsUnramInv ϖ σ q) : qh w = (q : ℂ) := by
  have h1 : qV E w = q ^ 2 := by
    unfold qV
    rw [← GroundTheory.Global.natCard_residueField_adicCompletionIntegers]
    exact hU.2.2.2.2.2.2
  unfold qh
  rw [h1]
  push_cast
  rw [Real.sqrt_sq (Nat.cast_nonneg q)]
  simp

theorem chi_eq {n : ℕ} {w : Pl E} {ϖ : (w.adicCompletion E)ˣ}
    (hv : Valued.v (ϖ : w.adicCompletion E) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {q : ℕ} (hq : q ≠ 0) (β : Fin (n / 2) → ℂˣ) (l : Fin (n / 2) → ℤ) (t : GU (cj w) n)
    (ht : (t : GLw n w) = tdiag ϖ (wexp n l)) :
    chiDeltaU q (fun i => (β i : ℂ)) t =
      pw β l * (q : ℂ) ^ (-∑ i : Fin (n / 2), ((n : ℤ) - 1 - 2 * (i : ℕ)) * l i) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hent : ∀ (i : Fin (n / 2)) (h : (i : ℕ) < n),
      ordL (((t : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ⟨i, h⟩ ⟨i, h⟩) =
        l i := by
    intro i h
    rw [ht, tdiag_val, Matrix.diagonal_apply_eq, GlobalTheory.CompanionTheory.KUFactsU.ordL_zpow hv, wexp_lt]
  unfold chiDeltaU pw
  rw [Finset.prod_congr rfl fun i _ => by rw [dif_pos (show (i : ℕ) < n by have := i.2; omega), hent],
    Finset.prod_mul_distrib, ← GlobalTheory.BorelUMod.zpow_finset_sum hq0]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by rw [Units.val_zpow_eq_zpow_val]
  · congr 1
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

end PositivityTheory.Rg.BcB.F.Eig.GluingInclusion

namespace PositivityTheory.Rg.BcB.F.Eig

open GluingInclusion in
theorem eigInertOf : EigInertOf := by
  intro hAbs hSum hIdx E _ _ _ n w hw b ϖ q σ α hb _ hU hA hSat
  obtain ⟨p, σ', hp, hS', ⟨e⟩⟩ := hSat
  have hc := cj_continuous w
  have hv : Valued.v (ϖ : w.adicCompletion E) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := hU.2.2.2.1
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  have hJ := mem_iwU_iff_p hv p hp
  have he : ∀ g v, e.toLinearEquiv (σ.ρ g v) = σ'.ρ (p g) (e.toLinearEquiv v) := fun g v => by
    have := LinearMap.congr_fun (e.isIntertwining' g) v
    simpa using this
  have hA' : IsAdmissible σ'.ρ := admissible_transport he (p_continuous p hp) (p_symm_continuous p hp) hA
  obtain ⟨β, hW, hmono, hge, y', hy'0, hy'⟩ :=
    hAbs (w.adicCompletion E) ϖ (cj w) q n σ'.V σ'.ρ α hU hA' σ'.irred hS'
  set φ := fixEquiv he hJ with hφ
  refine ⟨β, hW, hmono, hge, ((φ.symm y' : fixed σ.ρ (iwU n w b)) : σ.V), (φ.symm y').2, ?_, fun l hl => ?_⟩
  · intro h0
    have h3 : φ.symm y' = 0 := by rw [← Submodule.coe_eq_zero]; exact h0
    apply hy'0
    simpa using congrArg φ h3
  obtain ⟨t, htv⟩ : ∃ t : GU (cj w) n, (t : GLw n w) = tdiag ϖ (wexp n l) :=
    ⟨⟨_, tdiag_mem ϖ hU.2.2.1 l⟩, rfl⟩
  have htm : ((t : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.diagonal fun i => (ϖ : w.adicCompletion E) ^ wexp n l i := by
    rw [htv, tdiag_val]
  have hdiag : PositivityTheory.SphericalProduct.IsDiagM (t : GL (Fin n) (w.adicCompletion E)) := fun i j hij => by
    rw [htm]; exact Matrix.diagonal_apply_ne _ hij
  have hdom : PositivityTheory.SphericalProduct.IsStrictDom (t : GL (Fin n) (w.adicCompletion E)) := fun i j hij => by
    rw [htm, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, GlobalTheory.CompanionTheory.KUFactsU.ordL_zpow hv,
      GlobalTheory.CompanionTheory.KUFactsU.ordL_zpow hv]
    exact wexp_anti n hl hij
  have ht' : (p.symm t).1 = b * tdiag ϖ (wexp n l) * b⁻¹ := by rw [p_symm_val p hp, htv]
  have ht'p : p (p.symm t) = t := p.apply_symm_apply t
  generalize p.symm t = t' at ht' ht'p
  obtain ⟨U, hUH, -⟩ := GlobalTheory.T.hecke_character_exists_unique (UL n w) (iwU n w b) (GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w b)
    (GlobalTheory.CompanionTheory.UnitaryWitt.isCompact_iwU hw n b hc) σ.V σ.ρ σ.smooth t'
  have hUy : U (φ.symm y') = chiDeltaU q (fun i => (β i : ℂ)) t • φ.symm y' := by
    have h2 := hecke_transport he hJ t' U hUH
    rw [ht'p, ← hφ] at h2
    have h1 := hy' t hdiag hdom _ h2
    rw [LinearEquiv.conj_apply] at h1
    have h3 : φ (U (φ.symm y')) = chiDeltaU q (fun i => (β i : ℂ)) t • y' := by simpa using h1
    calc U (φ.symm y') = φ.symm (φ (U (φ.symm y'))) := (φ.symm_apply_apply _).symm
      _ = _ := by rw [h3, map_smul]
  have hf : fU n w b ϖ l = fun g => if ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, g = x * t' * z then 1 else 0 := by
    funext g
    unfold fU
    congr 1
    apply propext
    refine exists_congr fun x => and_congr_right fun _ => exists_congr fun z => and_congr_right fun _ => ?_
    rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul, ht']
  have key := hSum (UL n w) σ.V σ.ρ σ.smooth (KL n w) (iwU n w b) (GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w b)
    (GlobalTheory.CompanionTheory.IwLevels.isCompact_KL hw n hc) (GlobalTheory.CompanionTheory.IwLevels.iwU_le_KL n w b hb.1) t' U hUH (φ.symm y')
  rw [hf, key]
  rw [hUy]
  simp only [Submodule.coe_smul, smul_smul]
  refine congrArg (· • ((φ.symm y' : fixed σ.ρ (iwU n w b)) : σ.V)) ?_
  have hidx := hIdx (w.adicCompletion E) ϖ (cj w) q n hU l hl t htm
  rw [relIndex_transport p hJ t', ht'p]
  have hR : ((((PositivityTheory.SphericalProduct.IwU (cj w) n).map (MulAut.conj t).toMonoidHom).relIndex (PositivityTheory.SphericalProduct.IwU (cj w) n) : ℕ) : ℂ)
      = (q : ℂ) ^ (2 * ∑ i : Fin (n / 2), (((n : ℤ) - 1 - 2 * (i : ℕ)) * l i)) := by
    have := congrArg (fun z : ℤ => (z : ℂ)) hidx
    push_cast at this
    rw [this, ← zpow_natCast, Int.toNat_of_nonneg (by have := S_nonneg n hl; omega)]
  rw [hR, chi_eq hv hq β l t htv]
  unfold dlt
  rw [qh_eq hU]
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hpow : (q : ℂ) ^ (2 * ∑ i : Fin (n / 2), (((n : ℤ) - 1 - 2 * (i : ℕ)) * l i)) *
      (q : ℂ) ^ (-∑ i : Fin (n / 2), (((n : ℤ) - 1 - 2 * (i : ℕ)) * l i)) =
      (q : ℂ) ^ (∑ i : Fin (n / 2), (((n : ℤ) - 1 - 2 * (i : ℕ)) * l i)) := by
    rw [← zpow_add₀ hq0]
    ring_nf
  linear_combination (((iwU n w b).relIndex (KL n w) : ℂ)⁻¹ * pw β l) * hpow

end PositivityTheory.Rg.BcB.F.Eig

end
