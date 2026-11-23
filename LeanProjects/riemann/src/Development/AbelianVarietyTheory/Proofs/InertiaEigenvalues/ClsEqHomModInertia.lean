import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusGenDegreeHomToZlStatement

noncomputable section

namespace GlobalTheory.TopSteps.ChiOne

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
open ReciprocityTheory.Def (Z1 H1)
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O)

def IsLcHom {X : Type} [AddCommGroup X] (f : G → X) : Prop :=
  IsLocallyConstant f ∧ ∀ g h, f (g * h) = f g + f h

def coc {X : Type} [AddCommGroup X] [Module O X] (f : G → X) (hf : IsLcHom f) :
    ↥(Z1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤) :=
  ⟨fun g => (1 : O) ⊗ₜ[O] f g, ⟨hf.1.comp (fun x => (1 : O) ⊗ₜ[O] x), fun _ => Submodule.mem_top⟩, by
    funext x
    change twCoef (Γ.Wchi 1) Γ.χ₁ X x.1 ((1 : O) ⊗ₜ[O] f x.2) - (1 : O) ⊗ₜ[O] f (x.1 * x.2) + (1 : O) ⊗ₜ[O] f x.1 = 0
    rw [twCoef_chi_one, hf.2, tmul_add]
    abel⟩

def cl {X : Type} [AddCommGroup X] [Module O X] (f : G → X) (hf : IsLcHom f) :
    H1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤ := Submodule.Quotient.mk (coc Γ f hf)

variable {X X' : Type} [AddCommGroup X] [Module O X] [AddCommGroup X'] [Module O X']

theorem exists_cl (c : H1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤) : ∃ f hf, cl Γ f hf = c := by
  induction c using Submodule.Quotient.induction_on with
  | _ z =>
  have hlc : IsLocallyConstant (z : G → O ⊗[O] X) := z.2.1.1
  refine ⟨fun g => TensorProduct.lid O X ((z : G → O ⊗[O] X) g),
    ⟨hlc.comp _, fun g h => by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.cocycle_add Γ X z g h, map_add]⟩, ?_⟩
  unfold cl
  congr 1
  apply Subtype.ext
  funext g
  show (1 : O) ⊗ₜ[O] TensorProduct.lid O X ((z : G → O ⊗[O] X) g) = (z : G → O ⊗[O] X) g
  rw [← TensorProduct.lid_symm_apply, LinearEquiv.symm_apply_apply]

theorem IsLcHom.map {f : G → X} (hf : IsLcHom f) (φ : X →ₗ[O] X') : IsLcHom (fun g => φ (f g)) :=
  ⟨hf.1.comp φ, fun g h => by simp only [hf.2 g h, map_add]⟩

theorem IsLcHom.sub {f f' : G → X} (hf : IsLcHom f) (hf' : IsLcHom f') : IsLcHom (fun g => f g - f' g) :=
  ⟨hf.1.comp₂ hf'.1 (· - ·), fun g h => by
    show f (g * h) - f' (g * h) = (f g - f' g) + (f h - f' h)
    rw [hf.2 g h, hf'.2 g h]; abel⟩

theorem coefH1_cl {f : G → X} (hf : IsLcHom f) (φ : X →ₗ[O] X') :
    coefH1 (Γ.Wchi 1) Γ.χ₁ φ (cl Γ f hf) = cl Γ _ (hf.map φ) := rfl

theorem cl_sub {f f' : G → X} (hf : IsLcHom f) (hf' : IsLcHom f') :
    cl Γ _ (hf.sub hf') = cl Γ f hf - cl Γ f' hf' := by
  unfold cl
  rw [← Submodule.Quotient.mk_sub]
  congr 1
  apply Subtype.ext
  funext g
  show (1 : O) ⊗ₜ[O] (f g - f' g) = (1 : O) ⊗ₜ[O] f g - (1 : O) ⊗ₜ[O] f' g
  exact TensorProduct.tmul_sub _ _ _

theorem eq_zero_of_comb {f f' : G → X} (hf : IsLcHom f) (hf' : IsLcHom f') (a b : O)
    (h : a • cl Γ f hf + b • cl Γ f' hf' = 0) (g : G) : a • f g + b • f' g = 0 := by
  unfold cl at h
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_eq_zero] at h
  have h' : ((a • coc Γ f hf + b • coc Γ f' hf' : ↥(Z1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤)) : G → O ⊗[O] X) ∈
      ReciprocityTheory.Def.B1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤ := h
  obtain ⟨m, -, hm⟩ := Submodule.mem_map.1 h'
  have h1 := congrFun hm g
  have h0 : (ReciprocityTheory.Def.d0 (twCoef (Γ.Wchi 1) Γ.χ₁ X) m) g = 0 := by
    show twCoef (Γ.Wchi 1) Γ.χ₁ X g m - m = 0
    rw [twCoef_chi_one, sub_self]
  rw [h0] at h1
  have h2 : a • ((1 : O) ⊗ₜ[O] f g) + b • ((1 : O) ⊗ₜ[O] f' g) = (0 : O ⊗[O] X) := h1.symm
  have h3 := congrArg (TensorProduct.lid O X) h2
  simpa using h3

theorem cl_mem_hom {f : G → X} (hf : IsLcHom f) (I : Subgroup G) (h : ∀ g ∈ I, f g = 0) :
    cl Γ f hf ∈ homModInertia Γ X I := by
  unfold homModInertia
  refine ⟨coc Γ f hf, rfl, fun g hg => ?_⟩
  show (1 : O) ⊗ₜ[O] f g = 0
  rw [h g hg, TensorProduct.tmul_zero]

theorem isLcHom_unr {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O] [Finite X] (ν : G →* Multiplicative ℤ_[l])
    (hν : Continuous ν) (x : X) : IsLcHom (fun g => algebraMap ℤ_[l] O (Multiplicative.toAdd (ν g)) • x) := by
  refine ⟨?_, fun g h => by simp only [map_mul, toAdd_mul, map_add, add_smul]⟩
  have hadd : ∀ s t : ℤ_[l], algebraMap ℤ_[l] O (s + t) • x =
      algebraMap ℤ_[l] O s • x + algebraMap ℤ_[l] O t • x := fun s t => by
    rw [map_add, add_smul]
  have hN0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  obtain ⟨e, m, hm, hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 l (Fact.out : l.Prime).one_lt.ne'
  have hmu : IsUnit (m : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
  obtain ⟨u, hu⟩ := hmu
  have hkill : ∀ w : ℤ_[l], algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ e * w) • x = 0 := by
    intro w
    have hw : ((l : ℤ_[l]) ^ e * w) = ((Nat.card X : ℕ) : ℤ_[l]) * ((↑u⁻¹ : ℤ_[l]) * w) := by
      rw [hNe, Nat.cast_mul, Nat.cast_pow, ← hu, mul_assoc, ← mul_assoc (u : ℤ_[l]), Units.mul_inv, one_mul]
    rw [hw, map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul, card_nsmul_eq_zero']
  have hlc : IsLocallyConstant (fun t : ℤ_[l] => algebraMap ℤ_[l] O t • x) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    have hpos : (0 : ℝ) < (l : ℝ) ^ (-(e : ℤ)) :=
      zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
    filter_upwards [Metric.closedBall_mem_nhds t hpos] with s hs
    rw [Metric.mem_closedBall, dist_eq_norm] at hs
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 ((PadicInt.norm_le_pow_iff_mem_span_pow (s - t) e).1 hs)
    have hst : s = t + (l : ℤ_[l]) ^ e * w := by rw [mul_comm, hw]; ring
    show algebraMap ℤ_[l] O s • x = algebraMap ℤ_[l] O t • x
    rw [hst, hadd, hkill, add_zero]
  exact hlc.comp_continuous (continuous_toAdd.comp hν)

theorem exists_map_res [IsLocalRing O] {lam : O} (hm : IsLocalRing.maximalIdeal O = Ideal.span {lam})
    (Y : Type) [AddCommGroup Y] [Module O Y] [Finite Y] [Nontrivial Y] :
    ∃ φ : Y →ₗ[O] O ⧸ Ideal.span {lam}, φ ≠ 0 := by
  have hmax : (Ideal.span {lam}).IsMaximal := hm ▸ IsLocalRing.maximalIdeal.isMaximal O
  let _ : Field (O ⧸ Ideal.span {lam}) := Ideal.Quotient.field _
  have hne : (Ideal.span {lam} • ⊤ : Submodule O Y) ≠ ⊤ := by
    intro h
    have hb := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {lam}) (⊤ : Submodule O Y)
      Module.Finite.fg_top h.ge (by rw [← hm]; exact IsLocalRing.maximalIdeal_le_jacobson ⊥)
    exact top_ne_bot hb
  obtain ⟨y, hy⟩ : ∃ y : Y, y ∉ (Ideal.span {lam} • ⊤ : Submodule O Y) := by
    by_contra hc
    push_neg at hc
    exact hne (eq_top_iff.2 fun y _ => hc y)
  have hq : (Submodule.mkQ (Ideal.span {lam} • ⊤ : Submodule O Y)) y ≠ 0 := by
    rwa [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero (O ⧸ Ideal.span {lam}) hq
  refine ⟨(ψ.restrictScalars O).comp (Submodule.mkQ _), fun h => hψ ?_⟩
  have := LinearMap.congr_fun h y
  simpa using this

theorem eq_hom_of_res {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O] [IsLocalRing O]
    (hm : IsLocalRing.maximalIdeal O = Ideal.span {Γ.lam}) [Finite (resK Γ)]
    (I : Subgroup G) (F : G) (ν : G →* Multiplicative ℤ_[l]) (hν : Continuous ν) (hI : ∀ σ ∈ I, ν σ = 1)
    (hF : ν F = Multiplicative.ofAdd 1)
    (A : ∀ (X : Type) [AddCommGroup X] [Module O X], Set (H1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤))
    (hsub : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X],
      ∃ B : Submodule O (H1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤), A X = B)
    (hmap : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X]
      (X' : Type) [AddCommGroup X'] [Module O X'] [Finite X'] (f : X →ₗ[O] X')
      (c : H1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤),
      (c ∈ A X → coefH1 (Γ.Wchi 1) Γ.χ₁ f c ∈ A X') ∧
      (Function.Injective f → coefH1 (Γ.Wchi 1) Γ.χ₁ f c ∈ A X' → c ∈ A X))
    (hres : ∀ (s : ℕ) (c : Fin s → H1 (twCoef (Γ.Wchi 1) Γ.χ₁ (resK Γ)) ⊤), (∀ a, c a ∈ A (resK Γ)) →
      IndepMod Γ.lam c → s ≤ 1)
    (hunr : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], homModInertia Γ X I ⊆ A X)
    (X : Type) [AddCommGroup X] [Module O X] [Finite X] : A X = homModInertia Γ X I := by
  have hmax : (Ideal.span {Γ.lam}).IsMaximal := hm ▸ IsLocalRing.maximalIdeal.isMaximal O
  refine Set.Subset.antisymm ?_ (hunr X)
  intro c hc
  obtain ⟨f, hf, rfl⟩ := exists_cl Γ c
  have hu : IsLcHom (fun g => algebraMap ℤ_[l] O (Multiplicative.toAdd (ν g)) • f F) :=
    isLcHom_unr ν hν (f F)
  have huI : ∀ g ∈ I, algebraMap ℤ_[l] O (Multiplicative.toAdd (ν g)) • f F = 0 := by
    intro g hg
    simp [hI g hg]
  set h : G → X := fun g => f g - algebraMap ℤ_[l] O (Multiplicative.toAdd (ν g)) • f F with hh_eq
  have hh : IsLcHom h := hf.sub hu
  have hhF : h F = 0 := by simp [hh_eq, hF]
  have hclu : cl Γ _ hu ∈ A X := hunr X (cl_mem_hom Γ hu I huI)
  obtain ⟨B, hB⟩ := hsub X
  have hclh : cl Γ h hh ∈ A X := by
    have hd : cl Γ h hh = cl Γ f hf - cl Γ _ hu := cl_sub Γ hf hu
    rw [hB] at hc hclu ⊢
    rw [hd]
    exact B.sub_mem hc hclu
  have hzero : ∀ g, h g = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨g₀, hg₀⟩ := hne
    set Y : Submodule O X := Submodule.span O (Set.range h) with hY_eq
    have hY : ∀ g, h g ∈ Y := fun g => Submodule.subset_span ⟨g, rfl⟩
    set hY' : G → ↥Y := fun g => ⟨h g, hY g⟩ with hY'_eq
    have hYlc : IsLcHom hY' := by
      refine ⟨?_, fun a b => Subtype.ext (hh.2 a b)⟩
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      filter_upwards [(IsLocallyConstant.iff_eventually_eq h).1 hh.1 x] with y hy
      exact Subtype.ext hy
    have : Nontrivial ↥Y := ⟨⟨hY' g₀, 0, fun e => hg₀ (congrArg Subtype.val e)⟩⟩
    obtain ⟨φ, hφ⟩ := exists_map_res hm ↥Y
    have hex : ∃ g, φ (hY' g) ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hφ
      have hle : Y ≤ (LinearMap.ker φ).map Y.subtype := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨g, rfl⟩
        exact Submodule.mem_map.2 ⟨hY' g, hall g, rfl⟩
      apply LinearMap.ext
      intro y
      obtain ⟨y', hy', hyy⟩ := Submodule.mem_map.1 (hle y.2)
      have hyy' : y' = y := Subtype.ext hyy
      rw [← hyy']
      simpa using hy'
    obtain ⟨g₁, hg₁⟩ := hex
    have hclY : cl Γ hY' hYlc ∈ A ↥Y := by
      refine (hmap ↥Y X Y.subtype (cl Γ hY' hYlc)).2 Y.injective_subtype ?_
      rw [coefH1_cl]
      exact hclh
    have hc1 : cl Γ _ (hYlc.map φ) ∈ A (resK Γ) := by
      have := (hmap ↥Y (resK Γ) φ (cl Γ hY' hYlc)).1 hclY
      rwa [coefH1_cl] at this
    have hu1 : IsLcHom (fun g => algebraMap ℤ_[l] O (Multiplicative.toAdd (ν g)) • (1 : resK Γ)) :=
      isLcHom_unr ν hν 1
    have hc0 : cl Γ _ hu1 ∈ A (resK Γ) :=
      hunr (resK Γ) (cl_mem_hom Γ hu1 I (fun g hg => by simp [hI g hg]))
    have hmk : ∀ a : O, algebraMap O (resK Γ) a = 0 ↔ Γ.lam ∣ a := fun a => by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    have hle := hres 2 ![cl Γ _ hu1, cl Γ _ (hYlc.map φ)] ?_ ?_
    · omega
    · intro a
      fin_cases a
      · simpa using hc0
      · simpa using hc1
    · intro x hx
      rw [Fin.sum_univ_two] at hx
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx
      have hcomb := eq_zero_of_comb Γ hu1 (hYlc.map φ) (x 0) (x 1) hx
      have h0 : Γ.lam ∣ x 0 := by
        have := hcomb F
        have hYF : hY' F = 0 := Subtype.ext hhF
        simp only [hF, toAdd_ofAdd, map_one, hYF, map_zero, Algebra.smul_def, mul_one, mul_zero,
          add_zero] at this
        exact (hmk _).1 this
      have h1 : Γ.lam ∣ x 1 := by
        have := hcomb g₁
        rw [Algebra.smul_def (x 0), (hmk _).2 h0, zero_mul, zero_add, Algebra.smul_def] at this
        exact (hmk _).1 ((mul_eq_zero.1 this).resolve_right hg₁)
      intro a
      fin_cases a
      · simpa using h0
      · simpa using h1
  apply cl_mem_hom Γ hf I
  intro g hg
  have h1 : f g - algebraMap ℤ_[l] O (Multiplicative.toAdd (ν g)) • f F = 0 := hzero g
  rw [sub_eq_zero] at h1
  rw [h1, huI g hg]

end Gen

theorem local_res {l : ℕ} [Fact l.Prime] (LL : FinExt l) {lam : ↥(OL LL)} (h : Irreducible lam) :
    ∃ _ : IsLocalRing ↥(OL LL), IsLocalRing.maximalIdeal ↥(OL LL) = Ideal.span {lam} ∧
      Finite (↥(OL LL) ⧸ Ideal.span {lam}) := by
  obtain ⟨⟨⟨hdom, hdvr, -⟩, -⟩, hfin⟩ := GlobalTheory.LocalIntegers.good_integers l LL
  have hloc : IsLocalRing ↥(OL LL) := @IsDiscreteValuationRing.toIsLocalRing _ _ hdom hdvr
  have hmax : IsLocalRing.maximalIdeal ↥(OL LL) = Ideal.span {lam} :=
    (@IsDiscreteValuationRing.irreducible_iff_uniformizer _ _ hdom hdvr lam).1 h
  refine ⟨hloc, hmax, ?_⟩
  have hl : ((l : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    have := LL.2
    refine (GlobalTheory.mem_maximalIdeal_integralClosure_iff LL.1 ((l : ℕ) : ↥(OL LL))).2 ?_
    have hc : ((((l : ℕ) : ↥(OL LL)) : ↥LL.1) : PadicAlgCl l) =
        algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
      simp
    rw [hc, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hle : Ideal.span {((l : ℕ) : ↥(OL LL)) ^ 1} ≤ Ideal.span {lam} := by
    rw [pow_one, Ideal.span_le, Set.singleton_subset_iff, ← hmax]
    exact hl
  have := hfin 1
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)

theorem cls_eq_homModInertia : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Lem0 (S.Γ.Wchi 1) →
    S.ResBound (S.Γ.Wchi 1) 1 → S.UnrAdm → ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X],
    S.cls (S.Γ.Wchi 1) X = GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.homModInertia S.Γ X (IK S.K) := by
  intro l _ P S h0 hb hu X _ _ _
  obtain ⟨F, ν, hν, hI, hF, -⟩ := GlobalTheory.T.exists_frobenius_gen_degree_hom_to_Zl S.K
  have hst : Standing P S.K S.LL S.emb S.Γ.lam := S.hyp.1
  obtain ⟨_, hm, hfin⟩ := local_res S.LL hst.2.2.2.2.2
  refine eq_hom_of_res S.Γ hm (IK S.K) F ν hν hI hF (fun X _ _ => S.cls (S.Γ.Wchi 1) X) ?_ ?_ hb hu X
  · intro X _ _ _
    exact (h0 X).1
  · intro X _ _ _ X' _ _ _ f c
    exact (h0 X).2.2 X' f c

end GlobalTheory.TopSteps.ChiOne
