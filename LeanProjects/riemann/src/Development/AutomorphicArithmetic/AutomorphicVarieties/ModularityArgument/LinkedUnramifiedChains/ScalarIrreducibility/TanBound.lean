import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DerRep

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem add_vanish {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] (f : H → PadicAlgCl l) (hf : Continuous f) (hm : ∀ a b, f (a * b) = f a + f b)
    {ι : Type} (u : ι → H) (g : H)
    (hg : ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : H →* A, IsOpen (χ.ker : Set H) →
      (∀ a, χ (u a) = 1) → χ g = 1) (hu : ∀ a, f (u a) = 0) : f g = 0 := by
  classical
  have f1 : f 1 = 0 := by
    have h11 := hm 1 1
    rw [mul_one] at h11
    have h12 : f 1 + f 1 = f 1 + 0 := by rw [add_zero, ← h11]
    exact add_left_cancel h12
  have fpow : ∀ (h : H) (m : ℕ), f (h ^ m) = (m : PadicAlgCl l) * f h := by
    intro h m
    induction m with
    | zero => simp [f1]
    | succ m ih =>
      rw [pow_succ, hm, ih]
      push_cast
      ring
  let fm : H →* Multiplicative (PadicAlgCl l) :=
    { toFun := fun h => Multiplicative.ofAdd (f h)
      map_one' := by
        show Multiplicative.ofAdd (f 1) = 1
        rw [f1]
        rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (f (a * b)) = Multiplicative.ofAdd (f a) * Multiplicative.ofAdd (f b)
        rw [hm]
        rfl }
  have hl : ‖((l : ℕ) : PadicAlgCl l)‖ = 1 / (l : ℝ) := by
    rw [← PadicAlgCl.valuation_coe, PadicAlgCl.valuation_p]
    simp
  have hl1 : 1 / (l : ℝ) < 1 := by
    have h2 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact (div_lt_one (by linarith)).mpr h2
  have key : ∀ ε : ℝ, 0 < ε → ‖f g‖ < ε := by
    intro ε hε
    let W : Subgroup (Multiplicative (PadicAlgCl l)) :=
      { carrier := {x | ‖Multiplicative.toAdd x‖ < ε}
        one_mem' := by
          show ‖(0 : PadicAlgCl l)‖ < ε
          rw [norm_zero]
          exact hε
        mul_mem' := fun {a b} ha hb => by
          show ‖Multiplicative.toAdd a + Multiplicative.toAdd b‖ < ε
          exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
        inv_mem' := fun {a} ha => by
          show ‖-Multiplicative.toAdd a‖ < ε
          rw [norm_neg]
          exact ha }
    let N : Subgroup fm.range := W.subgroupOf fm.range
    let χ : H →* fm.range ⧸ N := (QuotientGroup.mk' N).comp fm.rangeRestrict
    have hker : ∀ h, χ h = 1 ↔ ‖f h‖ < ε := by
      intro h
      simp only [χ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      rfl
    have hsurj : Function.Surjective χ :=
      (QuotientGroup.mk'_surjective N).comp fm.rangeRestrict_surjective
    have hopen : IsOpen (χ.ker : Set H) := by
      have hset : (χ.ker : Set H) = {h | ‖f h‖ < ε} := by
        ext h
        exact hker h
      rw [hset]
      exact isOpen_lt (continuous_norm.comp hf) continuous_const
    haveI : Finite (fm.range ⧸ N) := by
      haveI : Finite (H ⧸ χ.ker) := Subgroup.quotient_finite_of_isOpen _ hopen
      exact Finite.of_surjective (QuotientGroup.kerLift χ)
        (fun a => by
          obtain ⟨h, rfl⟩ := hsurj a
          exact ⟨h, rfl⟩)
    have hp : IsPGroup l (fm.range ⧸ N) := by
      intro a
      obtain ⟨h, rfl⟩ := hsurj a
      have hpos : (0 : ℝ) < ‖f h‖ + 1 := by positivity
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hpos) hl1
      refine ⟨k, ?_⟩
      rw [← map_pow, hker, fpow, norm_mul, Nat.cast_pow, norm_pow, hl]
      calc (1 / (l : ℝ)) ^ k * ‖f h‖ ≤ (1 / (l : ℝ)) ^ k * (‖f h‖ + 1) := by
            gcongr
            linarith
        _ < ε / (‖f h‖ + 1) * (‖f h‖ + 1) := by gcongr
        _ = ε := by field_simp
    exact (hker g).mp (hg _ hp χ hopen (fun a => (hker _).mpr (by rw [hu a, norm_zero]; exact hε)))
  by_contra hne
  exact lt_irrefl _ (key _ (norm_pos_iff.mpr hne))

private theorem rank_le_card_add_rank_of_kernel {K M : Type} [Field K] [AddCommGroup M] [Module K M] {ι : Type} [Fintype ι]
    (P Q : Submodule K M) (e : ι → M →ₗ[K] K) (h : ∀ x ∈ P, (∀ i, e i x = 0) → x ∈ Q) :
    Module.rank K P ≤ (Fintype.card ι : ℕ) + Module.rank K Q := by
  classical
  let φ : P →ₗ[K] (ι → K) := LinearMap.pi (fun i => (e i).comp P.subtype)
  have h1 := LinearMap.rank_range_add_rank_ker φ
  have h2 : Module.rank K (LinearMap.range φ) ≤ (Fintype.card ι : ℕ) := by
    calc Module.rank K (LinearMap.range φ) ≤ Module.rank K (ι → K) := Submodule.rank_le _
      _ = _ := rank_fun'
  have h3 : Module.rank K (LinearMap.ker φ) ≤ Module.rank K Q := by
    rw [(Submodule.equivMapOfInjective P.subtype Subtype.val_injective (LinearMap.ker φ)).rank_eq]
    apply Submodule.rank_mono
    rintro _ ⟨x, hx, rfl⟩
    apply h _ x.2
    intro i
    have := congrFun (LinearMap.mem_ker.mp hx) i
    simpa [φ] using this
  rw [← h1]
  exact add_le_add h2 h3

theorem UpperTheory.V.J.tanBound :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, IntPt S ξ →
          Module.rank (Qbar l) (PtDer ξ (Qbar l)) ≤ (n * F.d : ℕ) + Module.rank (Qbar l) (FixTan S ξ) := by
  intro l _ c _ F C₀ n hF hn S ξ hξ
  choose u a₀ hu1 hu2 hgen using hF.gen
  let ev : S.A → ((S.A →ₗ[c.O] Qbar l) →ₗ[Qbar l] Qbar l) := fun x =>
    { toFun := fun D => D x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have key := rank_le_card_add_rank_of_kernel (PtDer ξ (Qbar l)) (FixTan S ξ)
    (fun j : (Σ v : F.V, Fin n × Fin (F.dv v)) => ev ↑(S.u.ψ j.1 j.2.1 (u j.1 j.2.2))) ?_
  · have hc : Fintype.card (Σ v : F.V, Fin n × Fin (F.dv v)) = n * F.d := by
      rw [Fintype.card_sigma, UpperTheory.V.Fr.Frame.d, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    rw [hc] at key
    exact key
  · intro D hD hz
    have hD' : ∀ x y, D (x * y) = ξ x • D y + ξ y • D x := hD
    refine Submodule.mem_inf.mpr ⟨hD, ?_⟩
    show ∀ (v : F.V) (i : Fin n), ∀ g ∈ F.Iv v, D ↑((S.u.ψ v i) g) = 0
    intro v i g hg
    obtain ⟨hx, hd⟩ := (derRep l c F C₀ n hF hn S ξ hξ D hD).2.2 v i
    have hne : ∀ h : F.Gv v, ξ ↑((S.u.ψ v i) h) ≠ 0 := by
      intro h hh
      have h1 := congrArg ξ (congrArg Units.val (mul_inv_cancel ((S.u.ψ v i) h)))
      rw [Units.val_mul, map_mul, hh, zero_mul, Units.val_one, map_one] at h1
      exact zero_ne_one h1
    let f : F.Gv v → PadicAlgCl l := fun h => D ↑((S.u.ψ v i) h) * (ξ ↑((S.u.ψ v i) h))⁻¹
    have hfc : Continuous f := hd.mul (hx.inv₀ hne)
    have hfm : ∀ a b, f (a * b) = f a + f b := by
      intro a b
      have ha := hne a
      have hb := hne b
      simp only [f, map_mul, Units.val_mul, hD', smul_eq_mul]
      field_simp
      ring
    have hzero : ∀ a, f (u v a) = 0 := by
      intro a
      have := hz ⟨v, (i, a)⟩
      simp only [f]
      rw [show D ↑((S.u.ψ v i) (u v a)) = 0 from this, zero_mul]
    have h0 := add_vanish f hfc hfm (u v) g
      (fun A _ _ hA χ ho h1 => hgen v A hA χ ho h1 g hg) hzero
    have hg0 := hne g
    simp only [f, mul_eq_zero, inv_eq_zero] at h0
    exact h0.resolve_right hg0
