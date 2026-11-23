import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IzumiBoundModPrincipalIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonUnitAtOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.CplDiv

theorem dvd_of_forall_mem_sup_pow : ∀ (O R : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R] (j : O →+* R), IsCpl j → ∀ (c s : R), (∀ e : ℕ, s ∈ Ideal.span {c} ⊔ (maximalIdeal O ^ e).map j) → c ∣ s := by
  intro O R _ _ _ _ j hj c s hs
  obtain ⟨e, he⟩ := hj
  haveI : IsNoetherianRing (AdicCompletion (maximalIdeal O) O) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion O (maximalIdeal O)
  haveI : IsNoetherianRing R := isNoetherianRing_of_ringEquiv _ e
  haveI : IsLocalRing R := e.isLocalRing
  have hjl : (maximalIdeal O).map j ≤ maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha hu
    have h1 : IsUnit (algebraMap O (AdicCompletion (maximalIdeal O) O) a) := by
      have := hu.map e.symm.toRingHom
      rw [← he a] at this
      simpa using this
    exact ha (isUnit_of_map_unit _ _ h1)
  have hJ : (maximalIdeal O).map j ≠ ⊤ := fun h => by
    have := hjl
    rw [h, top_le_iff] at this
    exact (maximalIdeal.isMaximal R).ne_top this
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ Ideal.span {c}) ((maximalIdeal O).map j) hJ
  have hmem : (Ideal.Quotient.mk (Ideal.span {c}) s : R ⧸ Ideal.span {c}) ∈ (⨅ i : ℕ, ((maximalIdeal O).map j) ^ i • ⊤ : Submodule R (R ⧸ Ideal.span {c})) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hs i)
    rw [Ideal.map_pow] at hv
    have : (Ideal.Quotient.mk (Ideal.span {c}) s : R ⧸ Ideal.span {c}) = v • (Ideal.Quotient.mk (Ideal.span {c}) 1) := by
      rw [← huv, Algebra.smul_def, map_one, _root_.mul_one, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hu, _root_.zero_add]
      rfl
    rw [this]
    exact Submodule.smul_mem_smul hv trivial
  rw [hK, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmem
  exact hmem

theorem exists_sub_mem_map_pow : ∀ (O R : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R] (j : O →+* R), IsCpl j → ∀ (s : R) (n : ℕ), ∃ t : O, s - j t ∈ (maximalIdeal O ^ n).map j := by
  intro O R _ _ _ _ j hj s n
  obtain ⟨e, he⟩ := hj
  have fg : (maximalIdeal O).FG := (maximalIdeal O).fg_of_isNoetherianRing
  obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ ((e.symm s).val n)
  refine ⟨t, ?_⟩
  have hker : e.symm s - algebraMap O _ t ∈ (AdicCompletion.eval (maximalIdeal O) O n).ker := by
    rw [LinearMap.mem_ker, map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of]
    rw [Algebra.algebraMap_self, RingHom.id_apply, Submodule.mkQ_apply, ht, AdicCompletion.eval_apply, sub_self]
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval fg, Ideal.smul_top_eq_map] at hker
  have h2 := Ideal.mem_map_of_mem e.toRingHom hker
  rw [Ideal.map_map] at h2
  have hc : e.toRingHom.comp (algebraMap O _) = j := RingHom.ext fun a => he a
  rw [hc] at h2
  simpa [he] using h2

theorem exists_norm_le_of_mem_map_pow : ∀ (O R : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R] (j : O →+* R) (p : ℕ) [Fact p.Prime] (ev : R →+* OO p) (n : ℕ) (t : R), t ∈ (maximalIdeal O ^ n).map j → ∃ g ∈ maximalIdeal O, ‖(ev t : PadicAlgCl p)‖ ≤ ‖(ev (j g) : PadicAlgCl p)‖ ^ n := by
  intro O R _ _ _ _ j p _ ev n t ht
  have hle1 : ∀ r : R, ‖(ev r : PadicAlgCl p)‖ ≤ 1 := fun r => (mem_OO_iff _).1 (ev r).2
  have hadd : ∀ (x y : R) (B : ℝ), ‖(ev x : PadicAlgCl p)‖ ≤ B → ‖(ev y : PadicAlgCl p)‖ ≤ B →
      ‖(ev (x + y) : PadicAlgCl p)‖ ≤ B := by
    intro x y B hx hy
    rw [map_add, AddMemClass.coe_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  have hmul : ∀ (x y : R) (B : ℝ), ‖(ev y : PadicAlgCl p)‖ ≤ B → ‖(ev (x * y) : PadicAlgCl p)‖ ≤ B := by
    intro x y B hy
    rw [map_mul, MulMemClass.coe_mul, norm_mul]
    calc ‖(ev x : PadicAlgCl p)‖ * ‖(ev y : PadicAlgCl p)‖ ≤ 1 * ‖(ev y : PadicAlgCl p)‖ :=
          mul_le_mul_of_nonneg_right (hle1 x) (norm_nonneg _)
      _ ≤ B := by rw [_root_.one_mul]; exact hy
  obtain ⟨S, hS⟩ := (maximalIdeal O).fg_of_isNoetherianRing
  let N : O → ℝ := fun g => ‖(ev (j g) : PadicAlgCl p)‖
  obtain ⟨g, hgS, hgmax⟩ := (insert 0 S).exists_max_image N ⟨0, Finset.mem_insert_self _ _⟩
  have hgm : g ∈ maximalIdeal O := by
    rcases Finset.mem_insert.1 hgS with h | h
    · rw [h]; exact Ideal.zero_mem _
    · rw [← hS]; exact Ideal.subset_span h
  refine ⟨g, hgm, ?_⟩
  have c1 : ∀ a ∈ maximalIdeal O, N a ≤ N g := by
    intro a ha
    rw [← hS] at ha
    induction ha using Submodule.span_induction with
    | mem x hx => exact hgmax x (Finset.mem_insert_of_mem hx)
    | zero => exact hgmax 0 (Finset.mem_insert_self _ _)
    | add x y _ _ hx hy =>
      show ‖(ev (j (x + y)) : PadicAlgCl p)‖ ≤ N g
      rw [map_add]; exact hadd _ _ _ hx hy
    | smul r x _ hx =>
      show ‖(ev (j (r • x)) : PadicAlgCl p)‖ ≤ N g
      rw [smul_eq_mul, map_mul]; exact hmul _ _ _ hx
  have c2 : ∀ k : ℕ, ∀ a ∈ maximalIdeal O ^ k, N a ≤ N g ^ k := by
    intro k
    induction k with
    | zero => intro a _; rw [pow_zero]; exact hle1 _
    | succ k ih =>
      intro a ha
      rw [pow_succ] at ha
      refine Submodule.mul_induction_on ha ?_ ?_
      · intro x hx y hy
        show ‖(ev (j (x * y)) : PadicAlgCl p)‖ ≤ N g ^ (k + 1)
        rw [map_mul, map_mul, MulMemClass.coe_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih x hx) (c1 y hy) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
      · intro x y hx hy
        show ‖(ev (j (x + y)) : PadicAlgCl p)‖ ≤ N g ^ (k + 1)
        rw [map_add]; exact hadd _ _ _ hx hy
  unfold Ideal.map at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact c2 n a ha
  | zero => rw [map_zero, ZeroMemClass.coe_zero, norm_zero]; exact pow_nonneg (norm_nonneg _) _
  | add x y _ _ hx hy => exact hadd _ _ _ hx hy
  | smul r x _ hx => rw [smul_eq_mul]; exact hmul _ _ _ hx

theorem val_stalkHom_eq : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) (x : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (φ : M.Z.presheaf.stalk x →+* OO p), y (cPt p) = x → spMap φ ≫ M.Z.fromSpecStalk x = y → ∀ a : M.Z.presheaf.stalk x, M.val (gPt p ≫ y) (M.stalkHom x a) = ((φ a : OO p) : PadicAlgCl p) := by
  intro o' Ω _ _ _ M x p _ y φ hy hφ a
  have h : y (cPt p) ⤳ x := hy ▸ specializes_rfl
  have hψ : Spec.map (M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo y) ≫ M.Z.fromSpecStalk x = y := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  haveI : Mono (M.Z.fromSpecStalk x) := inferInstance
  have heq : spMap φ = Spec.map (M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo y) := by
    rw [← cancel_mono (M.Z.fromSpecStalk x), hφ, hψ]
  have hφψ := Spec.map_injective heq
  have e1 : M.stalkHom x a = (M.stalkEquiv x a : Ω) := rfl
  rw [e1, RatModel.val_gPt hy (M.stalkEquiv x a)]
  simp only [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply]
  have := congrArg (fun g => ((g.hom a : OO p) : PadicAlgCl p)) hφψ
  exact this.symm

theorem dvd_of_norm_le_at_classical : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U₀ : M.Z.Opens), (U₀ : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → ∀ (b : M.Z.presheaf.stalk x) (s : R), b ≠ 0 → (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ‖(ev s : PadicAlgCl p)‖ ≤ ‖(ev (j b) : PadicAlgCl p)‖) → j b ∣ s := by
  intro o' Ω _ _ _ _ M hN U₀ hU₀ x hx R _ j hj b s hb hs
  haveI : IsNoetherianRing (M.O x) := GlobalTheory.FibreCorr.isNoetherianRing_O M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := isNoetherianRing_of_ringEquiv _ (M.stalkEquiv x).symm
  have hfO : M.stalkHom x b ∈ M.O x := (M.stalkEquiv x b).2
  have hf0 : M.stalkHom x b ≠ 0 := fun h => hb ((map_eq_zero_iff _ (M.stalkHom_injective x)).1 h)
  obtain ⟨C, hC⟩ := GlobalTheory.T.izumi_bound_mod_principal_ideal o' Ω M hN U₀ hU₀ x hx _ hfO hf0
  refine dvd_of_forall_mem_sup_pow _ _ j hj (j b) s fun e => ?_
  obtain ⟨t, ht⟩ := exists_sub_mem_map_pow _ _ j hj s (max e (C e))
  obtain ⟨a, c, hac, hc⟩ := hC e (M.stalkEquiv x t) (by
    intro p _ y hy
    obtain ⟨V, _, _, _, ev₀, i, -, -, -, -, hev, -⟩ := GlobalTheory.ClassicalPt.extend_completion o' Ω M x R j hj p y hy.1
    have hsb := hs p y (i.comp ev₀) hy hev
    have hφ : spMap ((i.comp ev₀).comp j) ≫ M.Z.fromSpecStalk x = y := by
      rw [← hev, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hval := val_stalkHom_eq o' Ω M x p y _ hy.1 hφ
    have e1 : M.val (gPt p ≫ y) (M.stalkEquiv x t : Ω) = ((i.comp ev₀) (j t) : PadicAlgCl p) := hval t
    have e2 : M.val (gPt p ≫ y) (M.stalkHom x b) = ((i.comp ev₀) (j b) : PadicAlgCl p) := hval b
    obtain ⟨g, hg, hgn⟩ := exists_norm_le_of_mem_map_pow _ _ j p (i.comp ev₀) _ _ ht
    rw [e1, e2]
    have key : ((i.comp ev₀) (j t) : PadicAlgCl p) = ((i.comp ev₀) s : PadicAlgCl p) - ((i.comp ev₀) (s - j t) : PadicAlgCl p) := by
      simp
    have hmax : ‖((i.comp ev₀) s : PadicAlgCl p) - ((i.comp ev₀) (s - j t) : PadicAlgCl p)‖ ≤ max ‖((i.comp ev₀) s : PadicAlgCl p)‖ ‖((i.comp ev₀) (s - j t) : PadicAlgCl p)‖ := by
      rw [sub_eq_add_neg, ← norm_neg ((i.comp ev₀) (s - j t) : PadicAlgCl p)]
      exact IsUltrametricDist.norm_add_le_max _ _
    by_cases hle : ‖((i.comp ev₀) (s - j t) : PadicAlgCl p)‖ ≤ ‖((i.comp ev₀) s : PadicAlgCl p)‖
    · left
      rw [key]
      exact hmax.trans ((max_le le_rfl hle).trans hsb)
    · right
      refine ⟨M.stalkHom x g, ⟨(M.stalkEquiv x g).2, ?_⟩, ?_⟩
      · have hnu : ¬ IsUnit (M.stalkEquiv x g) := fun h => hg (by simpa using h.map (M.stalkEquiv x).symm)
        rw [RatModel.isUnit_O_iff] at hnu
        by_cases h0 : (M.stalkEquiv x g : Ω) = 0
        · exact Or.inl h0
        · exact Or.inr fun h => hnu ⟨h0, h⟩
      · rw [hval g, key]
        have h1 : ‖((i.comp ev₀) (j g) : PadicAlgCl p)‖ ≤ 1 := (mem_OO_iff _).1 ((i.comp ev₀) (j g)).2
        have h2 := pow_le_pow_of_le_one (norm_nonneg _) h1 (le_max_right e (C e))
        exact hmax.trans ((max_le (le_of_not_ge hle) le_rfl).trans (hgn.trans h2)))
  have hmax : maximalIdeal (M.O x) = (maximalIdeal (M.Z.presheaf.stalk x)).map (M.stalkEquiv x) := by
    have : ((maximalIdeal (M.Z.presheaf.stalk x)).map (M.stalkEquiv x)).IsMaximal :=
      Ideal.map_isMaximal_of_equiv (M.stalkEquiv x)
    exact (IsLocalRing.eq_maximalIdeal this).symm
  have hspan : Ideal.span {c : M.O x | ¬ IsUnit c} = maximalIdeal (M.O x) := by
    have : {c : M.O x | ¬ IsUnit c} = (maximalIdeal (M.O x) : Set (M.O x)) := rfl
    rw [this, Ideal.span_eq]
  rw [hspan, hmax, ← Ideal.map_pow] at hc
  have hc' : (M.stalkEquiv x).symm c ∈ maximalIdeal (M.Z.presheaf.stalk x) ^ e := by
    obtain ⟨c₀, hc₀, hc₀e⟩ := (Ideal.mem_map_of_equiv (M.stalkEquiv x) c).1 hc
    rw [← hc₀e, RingEquiv.symm_apply_apply]
    exact hc₀
  have ht' : t = (M.stalkEquiv x).symm a * b + (M.stalkEquiv x).symm c := by
    apply (M.stalkEquiv x).injective
    apply Subtype.ext
    rw [map_add, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact hac
  have hle : (maximalIdeal (M.Z.presheaf.stalk x) ^ max e (C e)).map j ≤ (maximalIdeal (M.Z.presheaf.stalk x) ^ e).map j :=
    Ideal.map_mono (Ideal.pow_le_pow_right (le_max_left _ _))
  have hs' : s = (j t + (s - j t)) := by ring
  have hd := hle ht
  rw [hs']
  refine Ideal.add_mem _ ?_ (Ideal.mem_sup_right hd)
  rw [ht', map_add, map_mul]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hc'))

end GlobalTheory.CplDiv
