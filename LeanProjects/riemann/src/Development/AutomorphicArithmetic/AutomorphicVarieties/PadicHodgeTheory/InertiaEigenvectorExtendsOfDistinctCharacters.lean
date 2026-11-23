import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.inertia_eigenvector_extends_of_distinct_characters :
    ∀ {Γ I W : Type} [Group Γ] [Group I] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ} (i : I →* Γ) (ρ : Γ →* Module.End ℂ W) (μ : Fin n → Γ →* ℂˣ), (∀ σ s, ∃ t, σ * i s = i t * σ) → (Set.range fun s => ρ (i s)).Finite → (∀ σ, (ρ σ).charpoly = ∏ j, (X - C (μ j σ : ℂ))) → (∀ j k, j ≠ k → ∃ s, μ j (i s) ≠ μ k (i s)) → (∀ N : Module.End ℂ W, IsNilpotent N → (∀ s, ρ (i s) * N = N * ρ (i s)) → N = 0) ∧ ∀ j, (∃ y : W, y ≠ 0 ∧ ∀ s, ρ (i s) y = (μ j (i s) : ℂ) • y) ∧ ∀ y : W, (∀ s, ρ (i s) y = (μ j (i s) : ℂ) • y) → ∀ σ, ρ σ y = (μ j σ : ℂ) • y := by
  intro Γ I W _ _ _ _ _ n i ρ μ hnorm hfin hchar hdist
  classical
  have htr : ∀ σ, LinearMap.trace ℂ W (ρ σ) = ∑ j, (μ j σ : ℂ) := by
    intro σ
    have hs : (ρ σ).charpoly.Splits := by
      rw [hchar]
      exact Splits.prod (fun j _ => Splits.X_sub_C _)
    have hr := Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map fun j => (μ j σ : ℂ))
    simp only [Multiset.map_map, Function.comp_def] at hr
    rw [Module.End.trace_eq_sum_roots_charpoly_of_splits hs, hchar, Finset.prod_eq_multiset_prod, hr,
      Finset.sum_eq_multiset_sum]
  have hK : ∀ u : I, ρ (i u) = 1 → ∀ k, μ k (i u) = 1 := by
    intro u hu k
    have hroot : (ρ (i u)).charpoly.IsRoot (μ k (i u) : ℂ) := by
      rw [hchar, Polynomial.IsRoot, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
    rw [← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hroot
    obtain ⟨v, hv⟩ := hroot.exists_hasEigenvector
    have h1 := hv.apply_eq_smul
    rw [hu, Module.End.one_apply] at h1
    have h2 : ((μ k (i u) : ℂ) - 1) • v = 0 := by
      rw [sub_smul, ← h1, one_smul, sub_self]
    have h3 := (smul_eq_zero.mp h2).resolve_right hv.2
    ext
    simpa [sub_eq_zero] using h3
  have hK' : ∀ s s' : I, ρ (i s) = ρ (i s') → ∀ k, μ k (i s) = μ k (i s') := by
    intro s s' h k
    have h1 : ρ (i (s'⁻¹ * s)) = 1 := by
      rw [map_mul, map_mul, h, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    have h2 := hK _ h1 k
    rw [map_mul, map_mul, map_inv, map_inv] at h2
    exact (inv_mul_eq_one.mp h2).symm
  set U : I →* (Module.End ℂ W)ˣ := (ρ.comp i).toHomUnits with hU
  have hUval : ∀ s, ((U s : (Module.End ℂ W)ˣ) : Module.End ℂ W) = ρ (i s) := fun s => rfl
  have hKU : ∀ s s', U s = U s' → ∀ k, μ k (i s) = μ k (i s') :=
    fun s s' h k => hK' s s' (by rw [← hUval, ← hUval, h]) k
  have hfinU : (Set.range U).Finite := by
    refine (hfin.preimage (Function.Injective.injOn (fun a b h => Units.ext h))).subset ?_
    rintro x ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  haveI : Finite U.range := hfinU.to_subtype
  letI : Fintype U.range := Fintype.ofFinite _
  have hpre0 : ∀ h : U.range, ∃ s, U s = h := fun h => h.2
  choose pre hpre using hpre0
  have hpreval : ∀ h : U.range, (((h : (Module.End ℂ W)ˣ)) : Module.End ℂ W) = ρ (i (pre h)) := by
    intro h
    rw [← hUval, hpre]
  let ψ : Fin n → U.range →* ℂˣ := fun k =>
    { toFun := fun h => μ k (i (pre h))
      map_one' := by
        have : U (pre 1) = U 1 := by rw [hpre, map_one]; rfl
        show μ k (i (pre 1)) = 1
        rw [hKU _ _ this k, map_one, map_one]
      map_mul' := fun a b => by
        have : U (pre (a * b)) = U (pre a * pre b) := by rw [map_mul, hpre, hpre, hpre]; rfl
        show μ k (i (pre (a * b))) = μ k (i (pre a)) * μ k (i (pre b))
        rw [hKU _ _ this k, map_mul, map_mul] }
  have hψ : ∀ k (h : U.range), ψ k h = μ k (i (pre h)) := fun k h => rfl
  have hψU : ∀ k s, ψ k ⟨U s, s, rfl⟩ = μ k (i s) := fun k s => hKU _ _ (hpre _) k
  have horth : ∀ k m, ∑ h : U.range, (((ψ m * (ψ k)⁻¹) h : ℂˣ) : ℂ) =
      if m = k then (Fintype.card U.range : ℂ) else 0 := by
    intro k m
    split_ifs with hmk
    · subst hmk
      simp
    · let φ : U.range →* ℂ := (Units.coeHom ℂ).comp (ψ m * (ψ k)⁻¹)
      have hφ : φ ≠ 1 := by
        intro h1
        obtain ⟨s, hs⟩ := hdist m k hmk
        apply hs
        have h2 := DFunLike.congr_fun h1 ⟨U s, s, rfl⟩
        have h3 : ((ψ m * (ψ k)⁻¹) ⟨U s, s, rfl⟩ : ℂˣ) = 1 := Units.ext h2
        rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one, hψU, hψU] at h3
        exact h3
      exact sum_hom_units_eq_zero φ hφ
  let P : Fin n → Module.End ℂ W := fun k =>
    ∑ h : U.range, ((((ψ k)⁻¹ h : ℂˣ)) : ℂ) • (((h : (Module.End ℂ W)ˣ)) : Module.End ℂ W)
  let E : Fin n → W → Prop := fun k y => ∀ s, ρ (i s) y = (μ k (i s) : ℂ) • y
  have hcard0 : (Fintype.card U.range : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hact : ∀ k y, E k y → ∀ h : U.range,
      ((h : (Module.End ℂ W)ˣ) : Module.End ℂ W) y = (ψ k h : ℂ) • y := by
    intro k y hy h
    rw [hpreval, hy, hψ]
  have hPE : ∀ k y, E k y → ∀ m, P m y = if m = k then (Fintype.card U.range : ℂ) • y else 0 := by
    intro k y hy m
    have h1 : P m y = (∑ h : U.range, (((ψ k * (ψ m)⁻¹) h : ℂˣ) : ℂ)) • y := by
      simp only [P, LinearMap.sum_apply, LinearMap.smul_apply, hact k y hy,
        smul_smul, Finset.sum_smul]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [MonoidHom.mul_apply, Units.val_mul, mul_comm]
    rw [h1, horth m k]
    by_cases hmk : m = k
    · subst hmk
      simp
    · simp [hmk, Ne.symm hmk]
  have hPT : ∀ k s, ρ (i s) * P k = (μ k (i s) : ℂ) • P k := by
    intro k s
    let g : U.range := ⟨U s, s, rfl⟩
    let F : U.range → Module.End ℂ W := fun h' =>
      (((ψ k)⁻¹ h' : ℂˣ) : ℂ) • ((h' : (Module.End ℂ W)ˣ) : Module.End ℂ W)
    have key : ∀ h : U.range, (((ψ k)⁻¹ h : ℂˣ) : ℂ) •
        (ρ (i s) * ((h : (Module.End ℂ W)ˣ) : Module.End ℂ W)) = (μ k (i s) : ℂ) • F (g * h) := by
      intro h
      have e1 : (((ψ k)⁻¹ (g * h) : ℂˣ) : ℂ) =
          (((ψ k g)⁻¹ : ℂˣ) : ℂ) * (((ψ k)⁻¹ h : ℂˣ) : ℂ) := by
        rw [MonoidHom.inv_apply, MonoidHom.inv_apply, map_mul, _root_.mul_inv_rev, Units.val_mul, mul_comm]
      have e2 : (((g * h : U.range) : (Module.End ℂ W)ˣ) : Module.End ℂ W) =
          ρ (i s) * ((h : (Module.End ℂ W)ˣ) : Module.End ℂ W) := rfl
      have e3 : (μ k (i s) : ℂ) * (((ψ k g)⁻¹ : ℂˣ) : ℂ) = 1 := by
        rw [show ψ k g = μ k (i s) from hψU k s, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      show _ = (μ k (i s) : ℂ) • ((((ψ k)⁻¹ (g * h) : ℂˣ) : ℂ) •
        (((g * h : U.range) : (Module.End ℂ W)ˣ) : Module.End ℂ W))
      rw [e1, e2, smul_smul, ← mul_assoc, e3, one_mul]
    calc ρ (i s) * P k = ∑ h : U.range, (((ψ k)⁻¹ h : ℂˣ) : ℂ) •
          (ρ (i s) * ((h : (Module.End ℂ W)ˣ) : Module.End ℂ W)) := by
          simp only [P, Finset.mul_sum, mul_smul_comm]
      _ = ∑ h : U.range, (μ k (i s) : ℂ) • F (g * h) := Finset.sum_congr rfl fun h _ => key h
      _ = (μ k (i s) : ℂ) • ∑ h : U.range, F h := by
          rw [← Finset.smul_sum]
          congr 1
          exact Equiv.sum_comp (Equiv.mulLeft g) F
  have htrP : ∀ k, LinearMap.trace ℂ W (P k) = (Fintype.card U.range : ℂ) := by
    intro k
    simp only [P, map_sum, map_smul, hpreval, htr, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h1 : ∀ m, ∑ h : U.range, (((ψ k)⁻¹ h : ℂˣ) : ℂ) * (μ m (i (pre h)) : ℂ) =
        if m = k then (Fintype.card U.range : ℂ) else 0 := by
      intro m
      rw [← horth k m]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [MonoidHom.mul_apply, Units.val_mul, mul_comm, ← hψ]
    simp only [h1, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hPne : ∀ k, ∃ w, P k w ≠ 0 := by
    intro k
    by_contra hcon
    push_neg at hcon
    have h1 : P k = 0 := LinearMap.ext hcon
    have h2 := htrP k
    rw [h1, map_zero] at h2
    exact hcard0 h2.symm
  choose w hw using hPne
  have hPzE : ∀ k z, E k (P k z) := by
    intro k z s
    rw [← Module.End.mul_apply, hPT k s]
    rfl
  let yv : Fin n → W := fun k => P k (w k)
  have hyvE : ∀ k, E k (yv k) := fun k => hPzE k (w k)
  have hPE' : ∀ j k, P j (yv k) = if j = k then (Fintype.card U.range : ℂ) • yv k else 0 :=
    fun j k => hPE k (yv k) (hyvE k) j
  have hli : LinearIndependent ℂ yv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := congrArg (P j) hg
    rw [map_sum, map_zero] at h1
    simp only [map_smul, hPE', smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
    rw [smul_smul] at h1
    have h2 := (smul_eq_zero.mp h1).resolve_right (hw j)
    exact (mul_eq_zero.mp h2).resolve_right hcard0
  have hdim : Module.finrank ℂ W = n := by
    rw [← LinearMap.charpoly_natDegree (ρ 1), hchar 1]
    rw [Polynomial.natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ, Fintype.card_fin]
  let b := basisOfLinearIndependentOfCardEqFinrank' yv hli (by rw [Fintype.card_fin, hdim])
  have hb : ∀ k, b k = yv k := fun k => by simp [b]
  have hspan : ∀ k y, E k y → y = b.repr y k • yv k := by
    intro k y hy
    have hsum := b.sum_repr y
    have hzero : ∀ m, m ≠ k → b.repr y m = 0 := by
      intro m hm
      have h1 := congrArg (P m) hsum
      rw [map_sum] at h1
      simp only [map_smul, hb, hPE', smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        if_true] at h1
      rw [hPE k y hy m, if_neg hm, smul_smul] at h1
      have h2 := (smul_eq_zero.mp h1).resolve_right (hw m)
      exact (mul_eq_zero.mp h2).resolve_right hcard0
    conv_lhs => rw [← hsum]
    rw [Finset.sum_eq_single k (fun m _ hm => by rw [hzero m hm, zero_smul]) (by simp), hb]
  refine ⟨?_, ?_⟩
  · intro N hN hcomm
    apply b.ext
    intro k
    rw [hb, LinearMap.zero_apply]
    have hNE : E k (N (yv k)) := by
      intro s
      rw [← Module.End.mul_apply, hcomm s, Module.End.mul_apply, hyvE k s, map_smul]
    set a := b.repr (N (yv k)) k with ha_def
    have ha : N (yv k) = a • yv k := hspan k _ hNE
    obtain ⟨p, hp⟩ := hN
    have hpow : ∀ q : ℕ, (N ^ q) (yv k) = a ^ q • yv k := by
      intro q
      induction q with
      | zero => simp
      | succ q ih =>
        rw [pow_succ N q, Module.End.mul_apply, ha, map_smul, ih, smul_smul, pow_succ' a q, mul_comm]
    have h0 := hpow p
    rw [hp, LinearMap.zero_apply] at h0
    have ha0 : a ^ p = 0 := (smul_eq_zero.mp h0.symm).resolve_right (hw k)
    have ha00 : a = 0 := by
      by_contra hne
      exact pow_ne_zero p hne ha0
    rw [ha, ha00, zero_smul]
  · intro j
    refine ⟨⟨yv j, hw j, hyvE j⟩, ?_⟩
    intro y hy σ
    have hpres : ∀ z, E j z → E j (ρ σ z) := by
      intro z hz s
      obtain ⟨t, ht⟩ := hnorm σ⁻¹ s
      have e1 : i s * σ = σ * i t := by
        calc i s * σ = σ * (σ⁻¹ * i s) * σ := by group
          _ = σ * (i t * σ⁻¹) * σ := by rw [ht]
          _ = σ * i t := by group
      have e2 : μ j (i t) = μ j (i s) := by
        have e3 : i s = σ * i t * σ⁻¹ := by rw [← e1]; group
        rw [e3, map_mul, map_mul, map_inv, mul_comm (μ j σ), mul_assoc, mul_inv_cancel, mul_one]
      rw [← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply, hz t, map_smul, e2]
    set c := b.repr (ρ σ (yv j)) j with hc
    have hcy : ρ σ (yv j) = c • yv j := hspan j _ (hpres _ (hyvE j))
    have hσP : ρ σ * P j = c • P j := by
      refine LinearMap.ext fun z => ?_
      have hz := hspan j _ (hPzE j z)
      rw [Module.End.mul_apply, LinearMap.smul_apply, hz, map_smul, hcy, smul_comm]
    have htrσ : ∀ h : U.range, LinearMap.trace ℂ W (ρ σ * ((h : (Module.End ℂ W)ˣ) : Module.End ℂ W)) =
        ∑ m, (μ m σ : ℂ) * (μ m (i (pre h)) : ℂ) := by
      intro h
      rw [hpreval, ← map_mul, htr]
      simp [Units.val_mul]
    have htr1 : LinearMap.trace ℂ W (ρ σ * P j) = c * (Fintype.card U.range : ℂ) := by
      rw [hσP, map_smul, htrP, smul_eq_mul]
    have htr2 : LinearMap.trace ℂ W (ρ σ * P j) = (μ j σ : ℂ) * (Fintype.card U.range : ℂ) := by
      simp only [P, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, htrσ, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      have h1 : ∀ m, ∑ h : U.range, (((ψ j)⁻¹ h : ℂˣ) : ℂ) * ((μ m σ : ℂ) * (μ m (i (pre h)) : ℂ)) =
          (μ m σ : ℂ) * (if m = j then (Fintype.card U.range : ℂ) else 0) := by
        intro m
        rw [← horth j m, Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [MonoidHom.mul_apply, Units.val_mul, ← hψ]
        ring
      simp only [h1, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hceq : c = μ j σ := mul_right_cancel₀ hcard0 (htr1.symm.trans htr2)
    rw [hspan j y hy, map_smul, hcy, hceq, smul_comm]
