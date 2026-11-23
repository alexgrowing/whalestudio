import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.Skeleton
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Lemmata.GeneralBFactThirdSide.Imports

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef IsDedekindDomain

namespace PI.UnitaryGroupMassFormula.BetaModX.Iota

section Copied

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem exists_smul_mem (Λ : Submodule (𝓞 E) V) (hsp : Submodule.span E (Λ : Set V) = ⊤) (x : V) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ Λ := by
  first | exact Bl.general_b_fact_third'''''.goal1 .. | (apply Bl.general_b_fact_third'''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third'''''.goal1 <;> assumption)

variable [StarRing E]

theorem riesz [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E) (hs : h.IsSymm) (hnd : h.Nondegenerate)
    (Λ : Submodule (𝓞 E) V) (hΛ : Λ.FG) (hsp : Submodule.span E (Λ : Set V) = ⊤)
    (f : Λ →ₗ[𝓞 E] E) : ∃ w : V, ∀ y (hy : y ∈ Λ), h w y = f ⟨y, hy⟩ := by
  classical
  obtain ⟨s, _, b, hb, hsL⟩ := Formalism.HermitianLatticesTheory.dualLattice_basis (R := 𝓞 E) Λ hsp
  obtain ⟨d, hd, hdL⟩ := Formalism.HermitianLatticesTheory.dualLattice_denom b Λ hΛ
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis h hnd b
  have hbL : ∀ i, b i ∈ Λ := fun i => by rw [hb i]; exact hsL i.2
  refine ⟨∑ k, star (f ⟨b k, hbL k⟩) • bs k, ?_⟩
  set w := ∑ k, star (f ⟨b k, hbL k⟩) • bs k with hw
  have e : ∀ j k, h (bs k) (b j) = if j = k then 1 else 0 := by
    intro j k
    rw [← hs.eq (b j) (bs k), hbs]
    split_ifs <;> simp
  have hwb : ∀ j, h w (b j) = f ⟨b j, hbL j⟩ := by
    intro j
    simp [hw, e, starRingEnd_apply, star_star]
  have hspL : Submodule.span (𝓞 E) (Set.range b) ≤ Λ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hbL j
  have hspan : ∀ u (hu : u ∈ Submodule.span (𝓞 E) (Set.range b)) (huL : u ∈ Λ),
      h w u = f ⟨u, huL⟩ := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro _
      exact hwb j
    | zero =>
      intro huL
      have : (⟨0, huL⟩ : Λ) = 0 := rfl
      rw [this, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      intro huL
      have e2 : (⟨x + y, huL⟩ : Λ) = ⟨x, hspL hx⟩ + ⟨y, hspL hy⟩ := rfl
      rw [e2, map_add, map_add, ihx (hspL hx), ihy (hspL hy)]
    | smul r x hx ih =>
      intro huL
      have e2 : (⟨r • x, huL⟩ : Λ) = r • ⟨x, hspL hx⟩ := rfl
      rw [e2, f.map_smul, ← algebraMap_smul E r x, (h w).map_smul, ih (hspL hx), algebraMap_smul]
  intro y hy
  have h1 := hspan (d • y) (hdL y hy) (Λ.smul_mem d hy)
  have e2 : (⟨d • y, Λ.smul_mem d hy⟩ : Λ) = d • ⟨y, hy⟩ := rfl
  rw [e2, f.map_smul, ← algebraMap_smul E d y, (h w).map_smul, ← algebraMap_smul E d (f _),
    smul_eq_mul, smul_eq_mul] at h1
  exact mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd) h1

omit [StarRing E] in

theorem exists_retract (Λ : Submodule (𝓞 E) V) (hΛ : Λ.FG) (X : Submodule E V) :
    ∃ ρ : Λ →ₗ[𝓞 E] Λ, (∀ y, ((ρ y : Λ) : V) ∈ X) ∧ ∀ y : Λ, (y : V) ∈ X → ρ y = y := by
  classical
  let N : Submodule (𝓞 E) Λ := (X.restrictScalars (𝓞 E)).comap Λ.subtype
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ
  have htf : Module.IsTorsionFree (𝓞 E) (Λ ⧸ N) := by
    refine ⟨fun r hr q₁ q₂ hq => ?_⟩
    have hr0 : r ≠ 0 := hr.ne_zero
    obtain ⟨y₁, rfl⟩ := N.mkQ_surjective q₁
    obtain ⟨y₂, rfl⟩ := N.mkQ_surjective q₂
    have hq' : N.mkQ (r • (y₁ - y₂)) = 0 := by
      rw [map_smul, map_sub, smul_sub, sub_eq_zero]
      exact hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq'
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    have hmem : ((r • (y₁ - y₂) : Λ) : V) ∈ X := hq'
    have hrE : algebraMap (𝓞 E) E r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hr0
    have e : ((y₁ - y₂ : Λ) : V) = (algebraMap (𝓞 E) E r)⁻¹ • ((r • (y₁ - y₂) : Λ) : V) := by
      rw [Submodule.coe_smul, ← algebraMap_smul E r, smul_smul, inv_mul_cancel₀ hrE, one_smul]
    show ((y₁ - y₂ : Λ) : V) ∈ X
    rw [e]
    exact X.smul_mem _ hmem
  have : Module.FinitePresentation (𝓞 E) (Λ ⧸ N) := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) (Λ ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  let ρ : Λ →ₗ[𝓞 E] Λ := LinearMap.id - s ∘ₗ N.mkQ
  refine ⟨ρ, fun y => ?_, fun y hy => ?_⟩
  · have h0 : N.mkQ (ρ y) = 0 := by
      have := congrArg (fun φ => φ (N.mkQ y)) hs
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
      simp only [ρ, LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.coe_comp,
        Function.comp_apply, map_sub, this, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  · have h0 : N.mkQ y = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hy
    simp [ρ, h0]

end Copied

section Loc

variable {E : Type} [Field E] [NumberField E]

theorem mem_of_local {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (N : Submodule (𝓞 E) M) (x : M) (g : 𝓞 E)
    (hg : g ≠ 0) (hgx : g • x ∈ N)
    (hloc : ∀ P : HeightOneSpectrum (𝓞 E), g ∈ P.asIdeal → ∃ s, s ∉ P.asIdeal ∧ s • x ∈ N) : x ∈ N := by
  let I : Ideal (𝓞 E) := N.comap (LinearMap.toSpanSingleton (𝓞 E) M x)
  have hI : ∀ t, t ∈ I ↔ t • x ∈ N := fun t => by
    simp [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  by_cases htop : I = ⊤
  · have h1 : (1 : 𝓞 E) ∈ I := htop ▸ Submodule.mem_top
    simpa using (hI 1).1 h1
  · obtain ⟨P, hPm, hIP⟩ := Ideal.exists_le_maximal I htop
    have hgP : g ∈ P := hIP ((hI g).2 hgx)
    have hP0 : P ≠ ⊥ := fun h => hg (by rw [h] at hgP; exact (Submodule.mem_bot _).1 hgP)
    obtain ⟨s, hs, hsx⟩ := hloc ⟨P, hPm.isPrime, hP0⟩ hgP
    exact absurd (hIP ((hI s).2 hsx)) hs

theorem unitri_mem {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (Q : Submodule (𝓞 E) M) {n : ℕ}
    (ξ : Matrix (Fin n) (Fin n) (𝓞 E)) (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1)
    (u : Fin n → M) (b : Fin n) (hb : ∀ b' : Fin n, b' ≤ b → ∑ a, ξ a b' • u a ∈ Q) : u b ∈ Q := by
  suffices H : ∀ k : ℕ, ∀ b : Fin n, b.val = k →
      (∀ b' : Fin n, b' ≤ b → ∑ a, ξ a b' • u a ∈ Q) → u b ∈ Q from H _ b rfl hb
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro b hbk hb
    have hs := hb b le_rfl
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), h2 b, one_smul] at hs
    have hrest : ∑ a ∈ Finset.univ.erase b, ξ a b • u a ∈ Q := by
      refine Q.sum_mem (fun a ha => ?_)
      have hab : a ≠ b := Finset.ne_of_mem_erase ha
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · have hlt' : a.val < k := by rw [← hbk]; exact Fin.lt_def.mp hlt
        exact Q.smul_mem _ (ih a.val hlt' a rfl (fun b' hb' => hb b' (le_trans hb' hlt.le)))
      · rw [h1 a b hgt, zero_smul]; exact Q.zero_mem
    have := Q.sub_mem hs hrest
    simpa using this

end Loc

section Main

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem herm'' (x y : S.V) : S.hT y x = star (S.hT x y) := by
  rw [← S.herm.eq x y, starRingEnd_apply]

theorem mem_orth'' {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem int_val {Λ : Submodule (𝓞 E) S.V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {x y : S.V} (hx : x ∈ Λ)
    (hy : y ∈ Λ) : ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT x y := by
  have hU' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hU
  have hy' : y ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hU']; exact hy
  exact Submodule.mem_one.1 ((Formalism.HermitianLatticesTheory.dualBasic_mem_dual S.hT Λ y).1 hy' x hx)

theorem loc_div (Λ : Submodule (𝓞 E) S.V) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (g : ℕ) {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') (hadm : IsAdmissible Λ g F F') (w : S.V) (hwΛ : w ∈ Λ)
    (hwo : w ∈ orth S (Xsp F')) (P : HeightOneSpectrum (𝓞 E)) (hgP : (g : 𝓞 E) ∈ P.asIdeal) (b : Fin r) :
    S.hT w (F.fl.e b) ∈ (haveI := P.isPrime;
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 E) {((g : 𝓞 E) : E)})) := by
  have := P.isPrime
  obtain ⟨ξ, h1, h2, h3⟩ := hadm
  set Q := Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 E) {((g : 𝓞 E) : E)}) with hQ
  have key := unitri_mem Q ξ h1 h2 (fun a => S.hT w (frame F a)) (Fin.castSucc b) ?_
  · simpa [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using key
  intro b' hb'
  have hb'l : b' ≠ Fin.last r := by
    intro h; rw [h] at hb'; exact absurd hb' (not_le.mpr (Fin.castSucc_lt_last b))
  obtain ⟨c, rfl⟩ := Fin.exists_castSucc_eq.mpr hb'l
  obtain ⟨s, hs, hsv⟩ := h3 (Fin.castSucc c) P hgP
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hsv
  obtain ⟨lam, hlam, hlv⟩ := hsv
  obtain ⟨o, ho⟩ := int_val hU hwΛ hlam
  have he' : S.hT w (frame F' (Fin.castSucc c)) = 0 := by
    have hmem : frame F' (Fin.castSucc c) ∈ Xsp F' := by
      simp only [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
      exact Submodule.subset_span ⟨c, rfl⟩
    rw [herm'', mem_orth''.1 hwo _ hmem, star_zero]
  have hsum : S.hT w (frameAct (frame F) ξ (Fin.castSucc c)) =
      ∑ a, ξ a (Fin.castSucc c) • S.hT w (frame F a) := by
    unfold frameAct
    rw [map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [LinearMap.map_smul, smul_eq_mul, Algebra.smul_def]
  refine ⟨s, hs, ?_⟩
  have hv := congrArg (⇑(S.hT w)) hlv.symm
  rw [← algebraMap_smul E s, ← algebraMap_smul E (g : 𝓞 E), LinearMap.map_smul, LinearMap.map_smul,
    map_sub, he', hsum, zero_sub, ← ho] at hv
  rw [Submodule.mem_span_singleton]
  refine ⟨-o, ?_⟩
  have : s • ∑ a, ξ a (Fin.castSucc c) • S.hT w (frame F a) =
      -(algebraMap (𝓞 E) E s • -∑ a, ξ a (Fin.castSucc c) • S.hT w (frame F a)) := by
    rw [algebraMap_smul, smul_neg, neg_neg]
  rw [this, hv, smul_eq_mul, neg_smul, Algebra.smul_def, mul_comm]

theorem glob_div (Λ : Submodule (𝓞 E) S.V) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (g : ℕ) (hg : g ≠ 0)
    {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (hfix : IsFixedConv Λ g F)
    (hadm : IsAdmissible Λ g F F') (w : S.V) (hwΛ : w ∈ Λ) (hwo : w ∈ orth S (Xsp F')) (e : S.V)
    (heΛ : e ∈ Λ) (heX : e ∈ Xsp F) : S.hT w e ∈ Submodule.span (𝓞 E) {((g : 𝓞 E) : E)} := by
  have hg' : (g : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hg
  apply mem_of_local _ _ (g : 𝓞 E) hg'
  · obtain ⟨o, ho⟩ := int_val hU hwΛ heΛ
    rw [Submodule.mem_span_singleton]
    refine ⟨o, ?_⟩
    rw [← ho, Algebra.smul_def, Algebra.smul_def, mul_comm]
  intro P hgP
  have := P.isPrime
  obtain ⟨c, _, hc1, hloc⟩ := hfix.1 P
  have hc : ∀ a, c a = 1 := hc1 hgP
  have heL : e ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) := ⟨1, P.asIdeal.primeCompl.one_mem, by
    rw [one_smul]; exact ⟨heΛ, heX⟩⟩
  rw [hloc] at heL
  obtain ⟨t, ht, hte⟩ := heL
  set Q := Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 E) {((g : 𝓞 E) : E)}) with hQ
  have hspan : Submodule.span (𝓞 E) (Set.range fun a => c a • F.fl.e a) ≤
      Q.comap ((S.hT w).restrictScalars (𝓞 E)) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    show S.hT w (c a • F.fl.e a) ∈ Q
    rw [hc a, one_smul]
    exact loc_div Λ hU g F F' hadm w hwΛ hwo P hgP a
  have h1 : S.hT w (t • e) ∈ Q := hspan hte
  obtain ⟨s, hs, hse⟩ := h1
  refine ⟨s * t, fun hst => (P.isPrime.mem_or_mem hst).elim hs ht, ?_⟩
  rw [← algebraMap_smul E t e, LinearMap.map_smul, algebraMap_smul] at hse
  rw [mul_smul]
  exact hse

theorem iota_gen (Λ : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E Λ)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (g : ℕ) (hg : g ≠ 0) {T T' : E} (F : LFlag S r T) (F' : LFlag S r T')
    (hfix : IsFixedConv Λ g F) (hadm : IsAdmissible Λ g F F') (w : S.V) (hw : w ∈ Lrep Λ F') :
    ∃ l ∈ Lrep Λ F, l - w ∈ NgX Λ g F F' := by
  obtain ⟨hwΛ, hwo⟩ := hw
  have hgE : ((g : 𝓞 E) : E) ≠ 0 := by
    have : ((g : 𝓞 E) : E) = (g : E) := map_natCast _ g
    rw [this]; exact Nat.cast_ne_zero.mpr hg
  obtain ⟨ρ, hρX, hρid⟩ := exists_retract Λ hL.fg (Xsp F)
  let f : Λ →ₗ[𝓞 E] E := LinearMap.mulLeft (𝓞 E) (((g : 𝓞 E) : E)⁻¹) ∘ₗ
    (S.hT w).restrictScalars (𝓞 E) ∘ₗ Λ.subtype ∘ₗ ρ
  have hf : ∀ y, f y = (((g : 𝓞 E) : E))⁻¹ * S.hT w (ρ y : S.V) := fun y => rfl
  obtain ⟨m, hm⟩ := riesz S.hT S.herm S.nondeg Λ hL.fg hL.span_eq_top f
  have hfint : ∀ y : Λ, ∃ o : 𝓞 E, f y = algebraMap (𝓞 E) E o := by
    intro y
    have hd := glob_div Λ hU g hg F F' hfix hadm w hwΛ hwo (ρ y : S.V) (ρ y).2 (hρX y)
    obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hd
    refine ⟨o, ?_⟩
    rw [hf, ← ho, Algebra.smul_def, mul_comm, mul_assoc, mul_inv_cancel₀ hgE, mul_one]
  have hmΛ : m ∈ Λ := by
    have hU' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hU
    rw [← hU', Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    obtain ⟨o, ho⟩ := hfint ⟨y, hy⟩
    rw [herm'', hm y hy, ho, Submodule.mem_one]
    exact ⟨⟨star (algebraMap (𝓞 E) E o), o.isIntegral_coe.map (starRingEnd E).toIntAlgHom⟩, rfl⟩
  refine ⟨w - (g : 𝓞 E) • m, ⟨Λ.sub_mem hwΛ (Λ.smul_mem _ hmΛ), ?_⟩, ?_⟩
  · show w - (g : 𝓞 E) • m ∈ orth S (Xsp F)
    rw [mem_orth'']
    intro x hx
    obtain ⟨d, hd0, hdx⟩ := exists_smul_mem Λ hL.span_eq_top x
    have hdX : d • x ∈ Xsp F := by
      rw [← algebraMap_smul E d x]; exact (Xsp F).smul_mem _ hx
    have hρd : ρ ⟨d • x, hdx⟩ = ⟨d • x, hdx⟩ := hρid _ hdX
    have hval : S.hT (d • x) (w - (g : 𝓞 E) • m) = 0 := by
      have hmx := hm (d • x) hdx
      rw [hf, hρd] at hmx
      rw [map_sub, ← algebraMap_smul E (g : 𝓞 E) m, LinearMap.map_smul, herm'' m, hmx, smul_eq_mul,
        star_mul, ← herm'', star_inv₀]
      have hst : star (((g : 𝓞 E) : E)) = ((g : 𝓞 E) : E) := by
        rw [show ((g : 𝓞 E) : E) = (g : E) from map_natCast _ g, star_natCast]
      rw [hst]
      field_simp
      ring
    rw [← algebraMap_smul E d x, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at hval
    have hd0' : (starRingEnd E) (algebraMap (𝓞 E) E d) ≠ 0 := by
      rw [map_ne_zero]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0
    exact (mul_eq_zero.1 hval).resolve_left hd0'
  · have hgm : (g : 𝓞 E) • m ∈ Ideal.span {(g : 𝓞 E)} • Λ :=
      Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hmΛ
    have : w - (g : 𝓞 E) • m - w = -((g : 𝓞 E) • m) := by abel
    rw [this]
    exact Submodule.neg_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left hgm))

end Main

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem iota_surjective_holds : IotaSurj := by
  intro D u u' F0 Λ hΛ x w hw
  have hg : gS D ≠ 0 := by
    unfold gS
    exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  exact iota_gen Λ hΛ.2.1.1 hΛ.2.1.2.1 (gS D) hg (lf D F0) x.1 hΛ.2.1.2.2.2 x.2.2.1 w hw

end D7

end PI.UnitaryGroupMassFormula.BetaModX.Iota
