import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelPointLatticePeriodsTraitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrWithProportionalValuationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomAdicCompletionExtend
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongStalkPointEqMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTraitCharacterGroupFinrankLeGenusThree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongEqTopOfNotMemSupport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Extend

theorem pow_exp_eq {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (h : Irreducible ϖ) {a b : ℕ}
    (e : Associated (ϖ ^ a) (ϖ ^ b)) : a = b :=
  le_antisymm ((pow_dvd_pow_iff h.ne_zero h.not_isUnit).1 e.dvd) ((pow_dvd_pow_iff h.ne_zero h.not_isUnit).1 e.symm.dvd)

theorem form_eq_zero {X I : Type} [AddCommGroup X] (B : LinearMap.BilinForm ℤ X) (hB : ∀ a b, B a b = B b a) (b : I → X)
    (hb : Submodule.span ℤ (Set.range b) = ⊤) (h : ∀ i j, B (b i + b j) (b i + b j) = 0) : B = 0 := by
  have h1 : ∀ i j, B (b i) (b i) + 2 * B (b i) (b j) + B (b j) (b j) = 0 := by
    intro i j
    have := h i j
    simp only [map_add, LinearMap.add_apply] at this
    rw [hB (b j) (b i)] at this
    linarith
  have h2 : ∀ i, B (b i) (b i) = 0 := fun i => by have := h1 i i; linarith
  have h3 : ∀ i j, B (b i) (b j) = 0 := fun i j => by have := h1 i j; have := h2 i; have := h2 j; linarith
  refine LinearMap.ext_on_range hb fun i => LinearMap.ext_on_range hb fun j => ?_
  simpa using h3 i j

theorem evalZ_prop {g n : ℕ} (hn : 2 ≤ n) {F : SFam g n (zetaAway n)} {φ : InvFun ℤ} (hφ : IsPolFan id g φ) (T T' : Trait F)
    (e : T.D.toPre.X ≃+ T'.D.toPre.X) (m s : ℕ) (he : ∀ a b, (m : ℤ) * T'.β (e a) (e b) = s * T.β a b) :
    (m : ℝ) * φ.evalZ T'.β = s * φ.evalZ T.β := by
  have hon := hφ T.D.toPre.X (Trait.finrank_le g n hn F T)
  have hc : toReal T.β ∈ psdCone (id : ℤ → ℤ) T.D.toPre.X :=
    GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 T.symm) fun x => by simpa using T.mono.nonneg 0 x
  have hc' : toReal (pull e.toIntLinearEquiv.toLinearMap T'.β) ∈ psdCone (id : ℤ → ℤ) T.D.toPre.X :=
    GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 fun a b => T'.symm _ _) fun x => by
      simpa using T'.mono.nonneg 0 (e x)
  rw [← evalR_toReal φ T.β, ← hon.homog _ hc s s.cast_nonneg,
    ← evalZ_pull φ (r := e.toIntLinearEquiv.toLinearMap) e.surjective, ← evalR_toReal,
    ← hon.homog _ hc' m m.cast_nonneg]
  congr 1
  refine LinearMap.ext₂ fun a b => ?_
  have h := he a b
  simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]
  exact_mod_cast h

theorem idlAlong_ne_bot {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ X) (h : (jK R ≫ ξ) (closedPoint (FractionRing R)) ∉ J.support) : idlAlong J ξ ≠ ⊥ := by
  intro h0
  have h1 := idlAlong_eq_top_of_notMem_support X J _ _ h
  have h2 := GlobalTheory.TraitOrder.idlAlong_comp J ξ (algebraMap R (FractionRing R))
  rw [h0, Ideal.map_bot] at h2
  exact bot_ne_top (h2.symm.trans h1)

theorem isCpl_props {O R : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R] [IsLocalRing R]
    {j : O →+* R} (hj : IsCpl j) : Function.Injective j ∧ IsLocalHom j ∧
      ∀ (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ φ : O →+* V, IsLocalHom φ →
        ∃ ψ : R →+* V, IsLocalHom ψ ∧ ψ.comp j = φ := by
  obtain ⟨e, he⟩ := hj
  have hj : j = e.toRingHom.comp (algebraMap O _) := RingHom.ext fun a => (he a).symm
  have hl : IsLocalHom (algebraMap O (AdicCompletion (maximalIdeal O) O)) := inferInstance
  refine ⟨?_, ?_, fun V _ _ hV φ hφ => ?_⟩
  · rw [hj]
    exact e.injective.comp (AdicCompletion.of_injective (maximalIdeal O) O)
  · refine ⟨fun a ha => ?_⟩
    rw [← he, MulEquiv.isUnit_map] at ha
    exact isUnit_of_map_unit _ _ ha
  · obtain ⟨ψ, h1, h2⟩ := GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend O V hV φ hφ
    refine ⟨ψ.comp e.symm.toRingHom, ⟨fun a ha => ?_⟩, RingHom.ext fun a => ?_⟩
    · have := isUnit_of_map_unit ψ _ ha
      exact (MulEquiv.isUnit_map e.symm).1 this
    · rw [← h2, RingHom.comp_apply, ← he]
      simp

theorem orders_extend : ∀ (g n : ℕ), 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (D : GlobalTheory.EffCartierData M.Z) (ι : ℕ), (∀ z ∈ D.idealSheaf.support, z ∉ V) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V), jK T.V ≫ ξ = spMap γ ≫ M.pt → T.y = spMap γ ≫ spMap S.R.val.toRingHom ≫ u → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M V v (𝟙 F.X) T ξ → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  intro g n hn F φ hφ W hW o' Ω _ _ _ _ S ρ u hu M U₀ EE FinalForm hU V v hv D ι hD hgen T ξ hT
  haveI : CharZero Ω := ArithBase.char o'
  haveI : IsDedekindDomain o' := ArithBase.ded Ω
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨R, _, _, _, j, Λ, _, p, c, hR, hj, hc, hper⟩ :=
    GlobalTheory.T.thetaModel_point_lattice_periods_traits g n _ _ F W hW o' Ω S ρ u hu M U₀ EE FinalForm hU V v hv (ξ (closedPoint T.V))
  haveI := hR.1.1
  haveI := hR.2
  obtain ⟨jinj, jloc, jext⟩ := isCpl_props hj
  obtain ⟨ψ, ψloc, hψ⟩ := jext T.V T.complete (Scheme.stalkClosedPointTo ξ).hom inferInstance
  have hξ : spMap (ψ.comp j) ≫ M.Z.fromSpecStalk (ξ (closedPoint T.V)) = ξ := by
    rw [hψ]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  obtain ⟨d, hd⟩ : ∃ d, FinalTheorems.stalkId D.idealSheaf (ξ (closedPoint T.V)) = Ideal.span {d} := by
    obtain ⟨i, hi⟩ := D.exists_mem (ξ (closedPoint T.V))
    exact ⟨_, D.stalkId_idealSheaf i _ hi⟩
  have hid : idlAlong D.idealSheaf ξ = Ideal.span {ψ (j d)} := by
    rw [idlAlong, hd, Ideal.map_span, Set.image_singleton, ← hψ]
    rfl
  obtain ⟨ξ₀, hξ₀, hξ₀'⟩ := hT
  have hmem : (jK T.V ≫ ξ) (closedPoint (FractionRing T.V)) ∈ V := by
    rw [← hξ₀]
    exact (ξ₀ (closedPoint (FractionRing T.V))).2
  have hne := idlAlong_ne_bot D.idealSheaf ξ fun h => hD _ h hmem
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne T.irr
  refine ⟨a, ?_, ha⟩
  have hda : Associated (ψ (j d)) (T.ϖ ^ a) := Ideal.span_singleton_eq_span_singleton.1 (hid.symm.trans ha)
  obtain ⟨e, he⟩ := hper T ψ ψloc (by rw [hξ]; exact ⟨ξ₀, hξ₀, hξ₀'⟩)
  choose k hk hk' using he
  haveI := T.D.toPre.finX
  obtain ⟨N, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := T.D.toPre.X)
  obtain ⟨A, _, _, _, ϖ', ψ', m, m', k', hA, hϖ', ψ'inj, ψ'loc, hm, hm', hk''⟩ :=
    GlobalTheory.T.exists_complete_dvr_with_proportional_valuations R T.V T.ϖ T.irr ψ ψloc (Option (Fin N × Fin N))
      (fun i => i.elim (j d) fun ii => p (e.symm (b ii.1 + b ii.2)))
      (fun i => i.elim a fun ii => k (e.symm (b ii.1 + b ii.2)))
      (by rintro (_ | ii); exacts [hda, hk' _])
  obtain ⟨T', f, γ, finj, floc, -, hγ, hy⟩ := GlobalTheory.T.exists_trait_moduli_of_stalk_completeDVR g n _ _ F o' Ω M (spMap S.R.val.toRingHom ≫ u)
    (ξ (closedPoint T.V)) A hA (ψ'.comp j) (ψ'inj.comp jinj)
  have hrange : Set.range M.pt ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact (M.pt_specializes w _).mem_open V.isOpen hmem
  have hx₀ := IsOpenImmersion.lift_fac V.ι M.pt hrange
  obtain ⟨e', he'⟩ := hper T' (f.comp ψ') inferInstance
    ⟨spMap γ ≫ IsOpenImmersion.lift V.ι M.pt hrange, by rw [Category.assoc, hx₀]; exact hγ.symm,
      by rw [Category.comp_id, Category.assoc, hv _ hx₀, hy]⟩
  obtain ⟨r, hr⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    ((map_ne_zero_iff f finj).2 hϖ'.ne_zero) T'.irr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hr
    exact hϖ'.not_isUnit ((isUnit_map_iff f ϖ').1 (associated_one_iff_isUnit.1 hr))
  have hpow : ∀ {x : A} {l : ℕ}, Associated x (ϖ' ^ l) → Associated (f x) (T'.ϖ ^ (r * l)) := by
    intro x l h
    have h1 := h.map f
    rw [map_pow] at h1
    rw [pow_mul]
    exact h1.trans hr.pow_pow
  obtain ⟨a', ha', hid'⟩ := hgen T' _ γ hγ hy
  rw [GlobalTheory.TraitStalk.idlAlong_spMap_fromSpecStalk _ _ _ _ _ inferInstance, hd, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_eq_span_singleton] at hid'
  have h0 := hk'' none
  have ea : a' = r * k' none := pow_exp_eq T'.irr (hid'.symm.trans (hpow h0.1))
  have h02 : m * k' none = m' * a := h0.2
  let E := e.symm.trans e'
  have hz := form_eq_zero ((m : ℤ) • pull E.toIntLinearEquiv.toLinearMap T'.β - ((m' * r : ℕ) : ℤ) • T.β)
    (fun x y => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, pull_apply]
      rw [T.symm x y, T'.symm]) b hb (fun i i' => by
      obtain ⟨l, hl, hl'⟩ := he' (e.symm (b i + b i'))
      obtain ⟨h1, h2⟩ := hk'' (some (i, i'))
      have h3 : l = r * k' (some (i, i')) := pow_exp_eq T'.irr (hl'.symm.trans (hpow h1))
      have h4 := hk (e.symm (b i + b i'))
      rw [e.apply_symm_apply] at h4
      have h5 : (m : ℤ) * k' (some (i, i')) = m' * k (e.symm (b i + b i')) := by exact_mod_cast h2
      have hc0 : (c : ℤ) ≠ 0 := by omega
      change (m : ℤ) * T'.β (e' (e.symm (b i + b i'))) (e' (e.symm (b i + b i'))) -
        ((m' * r : ℕ) : ℤ) * T.β (b i + b i') (b i + b i') = 0
      refine mul_left_cancel₀ hc0 ?_
      rw [h3] at hl
      push_cast at hl ⊢
      linear_combination (-(m : ℤ)) * hl + r * h5 + m' * r * h4)
  have hev := evalZ_prop (by omega) hφ T T' E m (m' * r) fun x y =>
    sub_eq_zero.1 (congrArg (fun B : LinearMap.BilinForm ℤ T.D.toPre.X => B x y) hz)
  have h02' : (m : ℝ) * k' none = m' * a := by exact_mod_cast h02
  have hmr : ((m' : ℝ) * r) ≠ 0 := by
    have : m' ≠ 0 := by omega
    positivity
  refine mul_left_cancel₀ hmr ?_
  rw [ea] at ha'
  push_cast at ha' hev
  linear_combination (-(r : ℝ)) * h02' + m * ha' + ι * hev

end GlobalTheory.Poinc.Extend
