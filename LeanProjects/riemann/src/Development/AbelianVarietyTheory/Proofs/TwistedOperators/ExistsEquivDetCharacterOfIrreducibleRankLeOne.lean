import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL.RankLeOne

theorem scalar_det_of_subsingleton {k : Type} [CommRing k] {c : Type} [Fintype c] [DecidableEq c] [Subsingleton c]
    (g : GL c k) : Matrix.GeneralLinearGroup.scalar c (Matrix.GeneralLinearGroup.det g) = g := by
  ext i j
  obtain rfl : i = j := Subsingleton.elim i j
  haveI : Unique c := uniqueOfSubsingleton i
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique, Subsingleton.elim default i]

private theorem aeval_injective_of_sub_smul_injective {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (h : ∀ a : ℂ, Function.Injective (T - a • (1 : Module.End ℂ V))) (n : ℕ) :
    ∀ p : Polynomial ℂ, p.natDegree = n → p ≠ 0 → Function.Injective (Polynomial.aeval T p) := by
  induction n with
  | zero =>
    intro p hp hp0
    have hp' := Polynomial.eq_C_of_natDegree_eq_zero hp
    have hc : p.coeff 0 ≠ 0 := fun h0 => hp0 (by rw [hp', h0, map_zero])
    rw [hp', Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    intro x y hxy
    simp only [LinearMap.smul_apply, Module.End.one_apply] at hxy
    exact smul_right_injective V hc hxy
  | succ n ih =>
    intro p hp hp0
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p (by
      rw [Polynomial.degree_eq_natDegree hp0, hp]; exact_mod_cast Nat.succ_ne_zero n)
    have hfac := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hr
    have hq0 : p /ₘ (Polynomial.X - Polynomial.C r) ≠ 0 := by
      intro hq
      rw [hq, mul_zero] at hfac
      exact hp0 hfac.symm
    have hqd : (p /ₘ (Polynomial.X - Polynomial.C r)).natDegree = n := by
      have hd := Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq0
      rw [hfac, hp, Polynomial.natDegree_X_sub_C] at hd
      omega
    rw [← hfac, map_mul]
    have h1 : Polynomial.aeval T (Polynomial.X - Polynomial.C r) = T - r • (1 : Module.End ℂ V) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    rw [h1, Module.End.mul_eq_comp, LinearMap.coe_comp]
    exact (h r).comp (ih _ hqd hq0)

private theorem false_of_forall_sub_smul_bijective {V : Type} [AddCommGroup V] [Module ℂ V] {S : Set V}
    (hS : S.Countable) (hspan : Submodule.span ℂ S = ⊤) {v : V} (hv : v ≠ 0) (T : Module.End ℂ V)
    (h : ∀ a : ℂ, Function.Bijective (T - a • (1 : Module.End ℂ V))) : False := by
  classical
  have hX : ∀ a : ℂ, Polynomial.aeval T (Polynomial.X - Polynomial.C a) = T - a • (1 : Module.End ℂ V) := fun a => by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
  have hf : ∀ a : ℂ, (T - a • (1 : Module.End ℂ V)) ((LinearEquiv.ofBijective (T - a • (1 : Module.End ℂ V)) (h a)).symm v) = v :=
    fun a => (LinearEquiv.ofBijective (T - a • (1 : Module.End ℂ V)) (h a)).apply_symm_apply v
  have hinj : ∀ p : Polynomial ℂ, p ≠ 0 → Function.Injective (Polynomial.aeval T p) :=
    fun p hp => aeval_injective_of_sub_smul_injective T (fun a => (h a).1) _ p rfl hp
  have hli : LinearIndependent ℂ (fun a : ℂ => (LinearEquiv.ofBijective (T - a • (1 : Module.End ℂ V)) (h a)).symm v) := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    have hP : ∀ j ∈ s, Polynomial.aeval T (∏ l ∈ s.erase j, (Polynomial.X - Polynomial.C l)) v =
        Polynomial.aeval T (∏ l ∈ s, (Polynomial.X - Polynomial.C l))
          ((LinearEquiv.ofBijective (T - j • (1 : Module.End ℂ V)) (h j)).symm v) := by
      intro j hj
      rw [← Finset.mul_prod_erase s (fun l => Polynomial.X - Polynomial.C l) hj,
        mul_comm (Polynomial.X - Polynomial.C j), map_mul, Module.End.mul_apply, hX, hf]
    set Q : Polynomial ℂ := ∑ j ∈ s, Polynomial.C (g j) *
      ∏ l ∈ s.erase j, (Polynomial.X - Polynomial.C l) with hQdef
    have hQ : Polynomial.aeval T Q v = 0 := by
      calc Polynomial.aeval T Q v
          = ∑ j ∈ s, g j • Polynomial.aeval T (∏ l ∈ s.erase j, (Polynomial.X - Polynomial.C l)) v := by
            rw [hQdef, map_sum, LinearMap.sum_apply]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply]
        _ = Polynomial.aeval T (∏ l ∈ s, (Polynomial.X - Polynomial.C l))
              (∑ j ∈ s, g j • (LinearEquiv.ofBijective (T - j • (1 : Module.End ℂ V)) (h j)).symm v) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [map_smul, hP j hj]
        _ = 0 := by rw [hsum, map_zero]
    have hQ0 : Q = 0 := by
      by_contra hQne
      exact hv (hinj Q hQne (by rw [hQ, map_zero]))
    have hev : Q.eval i = g i * ∏ l ∈ s.erase i, (i - l) := by
      rw [hQdef, Polynomial.eval_finset_sum, Finset.sum_eq_single i]
      · rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      · intro j _ hji
        rw [Polynomial.eval_mul, Polynomial.eval_prod,
          Finset.prod_eq_zero (Finset.mem_erase.2 ⟨fun h' => hji h'.symm, hi⟩)
            (by rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]), mul_zero]
      · intro h'
        exact absurd hi h'
    have hne : ∏ l ∈ s.erase i, (i - l) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro l hl
      exact sub_ne_zero.2 fun h' => Finset.ne_of_mem_erase hl h'.symm
    rw [hQ0, Polynomial.eval_zero] at hev
    exact (mul_eq_zero.1 hev.symm).resolve_right hne
  have hle := hli.cardinal_le_rank
  have hr : Module.rank ℂ V ≤ Cardinal.mk S := by
    have h' := rank_span_le (R := ℂ) S
    rw [hspan, rank_top] at h'
    exact h'
  have hS' : Cardinal.mk S ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.2 hS.to_subtype
  have hC : Cardinal.mk ℂ ≤ Cardinal.aleph0 := (hle.trans hr).trans hS'
  rw [Cardinal.mk_complex] at hC
  exact absurd hC (not_le.2 Cardinal.aleph0_lt_continuum)

private theorem exists_eq_smul_one_of_intertwining {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {σ : Representation ℂ G V} (hi : σ.IsIrreducible) {S : Set V} (hS : S.Countable)
    (hspan : Submodule.span ℂ S = ⊤) {v : V} (hv : v ≠ 0) (T : Module.End ℂ V)
    (hT : ∀ h x, T (σ h x) = σ h (T x)) : ∃ a : ℂ, T = a • (1 : Module.End ℂ V) := by
  by_contra hne
  push_neg at hne
  refine false_of_forall_sub_smul_bijective hS hspan hv T fun a => ?_
  have hU : ∀ h x, (T - a • (1 : Module.End ℂ V)) (σ h x) = σ h ((T - a • (1 : Module.End ℂ V)) x) := by
    intro h x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hT]
  have hU0 : T - a • (1 : Module.End ℂ V) ≠ 0 := fun h0 => hne a (sub_eq_zero.1 h0)
  let K : Subrepresentation σ := ⟨LinearMap.ker (T - a • (1 : Module.End ℂ V)), fun h x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hU, hx, map_zero]⟩
  let R : Subrepresentation σ := ⟨LinearMap.range (T - a • (1 : Module.End ℂ V)), fun h x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨σ h y, hU h y⟩⟩
  constructor
  · rcases hi.eq_bot_or_eq_top K with hK | hK
    · have hK' : LinearMap.ker (T - a • (1 : Module.End ℂ V)) = ⊥ := congrArg Subrepresentation.toSubmodule hK
      exact LinearMap.ker_eq_bot.1 hK'
    · have hK' : LinearMap.ker (T - a • (1 : Module.End ℂ V)) = ⊤ := congrArg Subrepresentation.toSubmodule hK
      exact absurd (LinearMap.ker_eq_top.1 hK') hU0
  · rcases hi.eq_bot_or_eq_top R with hR | hR
    · have hR' : LinearMap.range (T - a • (1 : Module.End ℂ V)) = ⊥ := congrArg Subrepresentation.toSubmodule hR
      exact absurd (LinearMap.range_eq_bot.1 hR') hU0
    · have hR' : LinearMap.range (T - a • (1 : Module.End ℂ V)) = ⊤ := congrArg Subrepresentation.toSubmodule hR
      exact LinearMap.range_eq_top.1 hR'

theorem exists_equiv_detRep (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (c : Type) [Fintype c] [DecidableEq c] [Subsingleton c] (V : Type) [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL c k) V) (hs : IsSmooth σ) (hi : σ.IsIrreducible) :
    ∃ ψ : kˣ →* ℂˣ, IsSmoothChar ψ ∧ Nonempty (σ.Equiv (detRep c ψ)) := by
  classical
  haveI := hi
  have hcomm : ∀ g h : GL c k, g * h = h * g := by
    intro g h
    calc g * h = Matrix.GeneralLinearGroup.scalar c (Matrix.GeneralLinearGroup.det g) *
          Matrix.GeneralLinearGroup.scalar c (Matrix.GeneralLinearGroup.det h) := by
          rw [scalar_det_of_subsingleton, scalar_det_of_subsingleton]
      _ = Matrix.GeneralLinearGroup.scalar c (Matrix.GeneralLinearGroup.det h) *
          Matrix.GeneralLinearGroup.scalar c (Matrix.GeneralLinearGroup.det g) := by
          rw [← map_mul (Matrix.GeneralLinearGroup.scalar c), ← map_mul (Matrix.GeneralLinearGroup.scalar c),
            mul_comm (Matrix.GeneralLinearGroup.det g)]
      _ = h * g := by rw [scalar_det_of_subsingleton, scalar_det_of_subsingleton]

  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    haveI : Subsingleton V := ⟨fun x y => by rw [hcon x, hcon y]⟩
    apply (bot_ne_top : (⊥ : Subrepresentation σ) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    exact (Submodule.eq_bot_of_subsingleton (p := (⊤ : Submodule ℂ V))).symm

  let O : Subrepresentation σ := ⟨Submodule.span ℂ (Set.range fun g : GL c k => σ g v), fun h x hx => by
    have hle : Submodule.map (σ h) (Submodule.span ℂ (Set.range fun g : GL c k => σ g v)) ≤
        Submodule.span ℂ (Set.range fun g : GL c k => σ g v) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨h * g, by simp only [map_mul, Module.End.mul_apply]⟩
    exact hle (Submodule.mem_map_of_mem hx)⟩
  have hO : Submodule.span ℂ (Set.range fun g : GL c k => σ g v) = ⊤ := by
    rcases hi.eq_bot_or_eq_top O with h0 | h0
    · have h0' : Submodule.span ℂ (Set.range fun g : GL c k => σ g v) = ⊥ :=
        congrArg Subrepresentation.toSubmodule h0
      have hvm : v ∈ Submodule.span ℂ (Set.range fun g : GL c k => σ g v) :=
        Submodule.subset_span ⟨1, by simp only [map_one, Module.End.one_apply]⟩
      rw [h0', Submodule.mem_bot] at hvm
      exact absurd hvm hv
    · exact congrArg Subrepresentation.toSubmodule h0

  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  haveI : SecondCountableTopology kᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology kˣ := Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense kˣ
  have hsc : Continuous (Matrix.GeneralLinearGroup.scalar c : kˣ → GL c k) := by
    unfold Matrix.GeneralLinearGroup.scalar
    apply Continuous.units_map
    show Continuous fun x : k => Matrix.scalar c x
    simp only [Matrix.scalar_apply]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
  have hsub : ∀ g : GL c k,
      σ g v ∈ (fun x : kˣ => σ (Matrix.GeneralLinearGroup.scalar c x) v) '' D := by
    intro g
    have hgx : Matrix.GeneralLinearGroup.scalar c (Matrix.GeneralLinearGroup.det g) = g :=
      scalar_det_of_subsingleton g
    generalize Matrix.GeneralLinearGroup.det g = x at hgx
    have hUo : IsOpen {y : kˣ | σ (Matrix.GeneralLinearGroup.scalar c (x⁻¹ * y)) v = v} :=
      (hs v).preimage (hsc.comp (continuous_mul_left x⁻¹))
    have hxU : x ∈ {y : kˣ | σ (Matrix.GeneralLinearGroup.scalar c (x⁻¹ * y)) v = v} := by
      show σ (Matrix.GeneralLinearGroup.scalar c (x⁻¹ * x)) v = v
      rw [inv_mul_cancel, map_one, map_one, Module.End.one_apply]
    obtain ⟨d, hdU, hdD⟩ := hD.inter_open_nonempty _ hUo ⟨x, hxU⟩
    have hdU' : σ (Matrix.GeneralLinearGroup.scalar c (x⁻¹ * d)) v = v := hdU
    refine ⟨d, hdD, ?_⟩
    show σ (Matrix.GeneralLinearGroup.scalar c d) v = σ g v
    have hsplit : Matrix.GeneralLinearGroup.scalar c d = Matrix.GeneralLinearGroup.scalar c x *
        Matrix.GeneralLinearGroup.scalar c (x⁻¹ * d) := by
      rw [← map_mul, mul_inv_cancel_left]
    rw [hsplit, map_mul, Module.End.mul_apply, hdU', hgx]
  have hspan : Submodule.span ℂ ((fun x : kˣ => σ (Matrix.GeneralLinearGroup.scalar c x) v) '' D) = ⊤ := by
    refine top_unique ?_
    rw [← hO]
    apply Submodule.span_mono
    rintro _ ⟨g, rfl⟩
    exact hsub g

  have hscal : ∀ g : GL c k, ∃ a : ℂ, σ g = a • (1 : Module.End ℂ V) := fun g =>
    exists_eq_smul_one_of_intertwining hi (hDc.image _) hspan hv (σ g) fun h x => by
      show (σ g * σ h) x = (σ h * σ g) x
      rw [← map_mul, ← map_mul, hcomm g h]

  have hline : Submodule.span ℂ {v} = ⊤ := by
    let L : Subrepresentation σ := ⟨Submodule.span ℂ {v}, fun g x hx => by
      obtain ⟨a, ha⟩ := hscal g
      rw [ha, LinearMap.smul_apply, Module.End.one_apply]
      exact Submodule.smul_mem _ a hx⟩
    rcases hi.eq_bot_or_eq_top L with h0 | h0
    · have h0' : Submodule.span ℂ {v} = ⊥ := congrArg Subrepresentation.toSubmodule h0
      rw [Submodule.span_singleton_eq_bot] at h0'
      exact absurd h0' hv
    · exact congrArg Subrepresentation.toSubmodule h0
  have hmem : ∀ x : V, ∃ t : ℂ, t • v = x := fun x =>
    Submodule.mem_span_singleton.1 (by rw [hline]; exact Submodule.mem_top)
  choose a ha using fun g : GL c k => hmem (σ g v)
  have ha1 : a 1 = 1 := smul_left_injective ℂ hv (by
    show a 1 • v = (1 : ℂ) • v
    rw [ha, map_one, Module.End.one_apply, one_smul])
  have hmul : ∀ g h, a (g * h) = a g * a h := fun g h => smul_left_injective ℂ hv (by
    show a (g * h) • v = (a g * a h) • v
    rw [ha, map_mul, Module.End.mul_apply, ← ha h, map_smul, ← ha g, smul_smul, mul_comm])
  let χ : GL c k →* ℂ := { toFun := a, map_one' := ha1, map_mul' := hmul }
  let e₀ : ℂ ≃ₗ[ℂ] V :=
    (LinearEquiv.toSpanNonzeroSingleton ℂ V v hv).trans (LinearEquiv.ofTop _ hline)
  have he₀ : ∀ t : ℂ, e₀.symm (t • v) = t := fun t => by
    have h1 : e₀ t = t • v := by
      simp only [e₀, LinearEquiv.trans_apply, LinearEquiv.ofTop_apply,
        LinearEquiv.toSpanNonzeroSingleton_apply]
    rw [← h1, LinearEquiv.symm_apply_apply]
  refine ⟨(χ.comp (Matrix.GeneralLinearGroup.scalar c)).toHomUnits, ?_, ?_⟩
  ·
    have hker : (((χ.comp (Matrix.GeneralLinearGroup.scalar c)).toHomUnits).ker : Set kˣ) =
        (Matrix.GeneralLinearGroup.scalar c) ⁻¹' {g | σ g v = v} := by
      ext x
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq]
      rw [Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one]
      show a (Matrix.GeneralLinearGroup.scalar c x) = 1 ↔ _
      rw [← ha]
      constructor
      · intro h1
        rw [h1, one_smul]
      · intro h1
        exact smul_left_injective ℂ hv (show _ • v = (1 : ℂ) • v by rw [h1, one_smul])
    unfold IsSmoothChar
    rw [hker]
    exact (hs v).preimage hsc
  ·
    refine ⟨Representation.Equiv.mk e₀.symm fun g => ?_⟩
    apply LinearMap.ext
    intro x
    obtain ⟨t, rfl⟩ := hmem x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [map_smul, ← ha g, smul_smul, he₀, he₀, GlobalTheory.SmGL.detRep, GlobalTheory.SmGL.ofChar_apply,
      GlobalTheory.SmGL.detChar_apply, MonoidHom.coe_toHomUnits, MonoidHom.comp_apply, scalar_det_of_subsingleton]
    exact mul_comm _ _

end GlobalTheory.SmGL.RankLeOne
