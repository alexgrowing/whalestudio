import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFactsAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflFacts

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L.FiniteActions

section Gen

variable {G H Γ V : Type} [Group G] [Group H] [Group Γ] [AddCommGroup V] [Module ℂ V]

private theorem mem_fx (ρ : Representation ℂ G V) (U : Subgroup G) (v : V) :
    v ∈ fixed ρ U ↔ ∀ u ∈ U, ρ u v = v := by
  show (∀ h : U, ρ h v = ((1 : U →* ℂˣ) h : ℂ) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun h u hu => h ⟨u, hu⟩, fun h u => h u u.2⟩

private theorem fx_stable (ρ : Representation ℂ G V) (ι : H →* G) (p : H →* Γ) (y : H) {v : V}
    (hv : v ∈ fixed ρ (p.ker.map ι)) : ρ (ι y) v ∈ fixed ρ (p.ker.map ι) := by
  rw [mem_fx] at hv ⊢
  rintro u ⟨k, hk, rfl⟩
  have hk0 : p k = 1 := hk
  have hk' : y⁻¹ * k * y ∈ p.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, hk0, mul_one, map_inv, inv_mul_cancel]
  have hfix := hv _ ⟨_, hk', rfl⟩
  calc ρ (ι k) (ρ (ι y) v) = ρ (ι (k * y)) v := by rw [map_mul ι, map_mul ρ, Module.End.mul_apply]
    _ = ρ (ι (y * (y⁻¹ * k * y))) v := by congr 2; group
    _ = ρ (ι y) (ρ (ι (y⁻¹ * k * y)) v) := by rw [map_mul ι y, map_mul ρ, Module.End.mul_apply]
    _ = ρ (ι y) v := by rw [hfix]

private theorem fx_eq (ρ : Representation ℂ G V) (ι : H →* G) (p : H →* Γ) {y y' : H} (h : p y = p y')
    {v : V} (hv : v ∈ fixed ρ (p.ker.map ι)) : ρ (ι y) v = ρ (ι y') v := by
  rw [mem_fx] at hv
  have hk : y'⁻¹ * y ∈ p.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hfix := hv _ ⟨_, hk, rfl⟩
  calc ρ (ι y) v = ρ (ι (y' * (y'⁻¹ * y))) v := by rw [mul_inv_cancel_left]
    _ = ρ (ι y') (ρ (ι (y'⁻¹ * y)) v) := by rw [map_mul ι, map_mul ρ, Module.End.mul_apply]
    _ = ρ (ι y') v := by rw [hfix]

private def rp (ρ : Representation ℂ G V) (ι : H →* G) (p : H →* Γ) (hp : Function.Surjective p) :
    Representation ℂ Γ (fixed ρ (p.ker.map ι)) where
  toFun g := (ρ (ι (Function.surjInv hp g))).restrict fun _ hv => fx_stable ρ ι p _ hv
  map_one' := by
    ext ⟨v, hv⟩
    have h : p (Function.surjInv hp 1) = p 1 := by simp [Function.surjInv_eq]
    simpa using fx_eq ρ ι p h hv
  map_mul' a b := by
    ext ⟨v, hv⟩
    have h : p (Function.surjInv hp (a * b)) = p (Function.surjInv hp a * Function.surjInv hp b) := by
      simp [Function.surjInv_eq]
    simpa using fx_eq ρ ι p h hv

private theorem rp_spec (ρ : Representation ℂ G V) (ι : H →* G) (p : H →* Γ) (hp : Function.Surjective p)
    (y : H) (x : fixed ρ (p.ker.map ι)) : (rp ρ ι p hp (p y) x : V) = ρ (ι y) x := by
  show ρ (ι (Function.surjInv hp (p y))) x = _
  exact fx_eq ρ ι p (Function.surjInv_eq hp (p y)) x.2

private theorem rel_eq (ι : H →* G) (hι : Function.Injective ι) (p : H →* Γ) (hp : Function.Surjective p) :
    (p.ker.map ι).relIndex ι.range = Nat.card Γ := by
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hι, Subgroup.relIndex_top_right,
    Subgroup.index_ker, MonoidHom.range_eq_top.mpr hp]
  exact Subgroup.card_top

private theorem lev_eq_lemma (ι : H →* G) (hι : Function.Injective ι) (p : H →* Γ) (a b : H) :
    ((ι a : G) : G ⧸ p.ker.map ι) = ((ι b : G) : G ⧸ p.ker.map ι) ↔ p a = p b := by
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨k, hk, hke⟩
    have hk0 : p k = 1 := hk
    have hkb : k = a⁻¹ * b := hι (by rw [hke, map_mul, map_inv])
    rw [hkb, map_mul, map_inv, inv_mul_eq_one] at hk0
    exact hk0
  · intro h
    refine ⟨a⁻¹ * b, ?_, by rw [map_mul, map_inv]⟩
    show p (a⁻¹ * b) = 1
    rw [map_mul, map_inv, h, inv_mul_cancel]

private theorem exists_quotient_out_eq_and_eq_of_map_ker (ι : H →* G) (p : H →* Γ) (y : H) :
    ∃ z, Quotient.out ((ι y : G) : G ⧸ p.ker.map ι) = ι z ∧ p z = p y := by
  obtain ⟨⟨u, k, hk, rfl⟩, hu⟩ := QuotientGroup.mk_out_eq_mul (p.ker.map ι) (ι y)
  have hk0 : p k = 1 := hk
  exact ⟨y * k, by simp [hu], by rw [map_mul, hk0, mul_one]⟩

private theorem lev_eq [Fintype Γ] (ρ : Representation ℂ G V) (ι : H →* G) (hι : Function.Injective ι)
    (p : H →* Γ) (hp : Function.Surjective p) (f : G → ℂ) (fb : Γ → ℂ) (hf1 : ∀ y, f (ι y) = fb (p y))
    (hf0 : ∀ x, x ∉ ι.range → f x = 0) (A : V →ₗ[ℂ] V) {x : V} (hx : A x ∈ fixed ρ (p.ker.map ι)) :
    GlobalTheory.BCT.levOp ρ ι.range (p.ker.map ι) f A x =
      (Nat.card Γ : ℂ)⁻¹ • ∑ g : Γ, fb g • ρ (ι (Function.surjInv hp g)) (A x) := by
  classical
  let φ : Γ → G ⧸ p.ker.map ι := fun g => ((ι (Function.surjInv hp g) : G) : G ⧸ p.ker.map ι)
  have hφ : Function.Injective φ := by
    intro g g' h
    have h2 := (lev_eq_lemma ι hι p _ _).1 h
    rwa [Function.surjInv_eq hp, Function.surjInv_eq hp] at h2
  have hsupp : Function.support (fun q : G ⧸ p.ker.map ι => f (Quotient.out q) • ρ (Quotient.out q) ∘ₗ A) ⊆
      (Finset.univ.image φ : Set (G ⧸ p.ker.map ι)) := by
    intro q hq
    by_contra hn
    apply hq
    have hf : f (Quotient.out q) = 0 := by
      apply hf0
      intro hr
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hr
      apply hn
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨p y, Finset.mem_univ _, ?_⟩)
      rw [← QuotientGroup.out_eq' q, ← hy]
      exact (lev_eq_lemma ι hι p _ _).2 (Function.surjInv_eq hp _)
    simp [hf]
  have hterm : ∀ g, f (Quotient.out (φ g)) • ρ (Quotient.out (φ g)) (A x) =
      fb g • ρ (ι (Function.surjInv hp g)) (A x) := by
    intro g
    obtain ⟨z, hz, hpz⟩ := exists_quotient_out_eq_and_eq_of_map_ker ι p (Function.surjInv hp g)
    show f (Quotient.out ((ι (Function.surjInv hp g) : G) : G ⧸ p.ker.map ι)) •
      ρ (Quotient.out ((ι (Function.surjInv hp g) : G) : G ⧸ p.ker.map ι)) (A x) = _
    rw [hz, hf1, hpz, Function.surjInv_eq hp]
    congr 1
    exact fx_eq ρ ι p hpz hx
  unfold GlobalTheory.BCT.levOp
  rw [rel_eq ι hι p hp, LinearMap.smul_apply, finsum_eq_sum_of_support_subset _ hsupp, LinearMap.sum_apply,
    Finset.sum_image (fun a _ b _ h => hφ h)]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply]
  exact hterm g

private theorem tr_eq [Finite Γ] (ρ : Representation ℂ G V) (ι : H →* G) (hι : Function.Injective ι)
    (p : H →* Γ) (hp : Function.Surjective p) (f : G → ℂ) (fb : Γ → ℂ) (hf1 : ∀ y, f (ι y) = fb (p y))
    (hf0 : ∀ x, x ∉ ι.range → f x = 0) (A : V →ₗ[ℂ] V)
    (hA : ∀ x ∈ fixed ρ (p.ker.map ι), A x ∈ fixed ρ (p.ker.map ι)) :
    GlobalTheory.BCT.twTr ρ ι.range (p.ker.map ι) f A =
      (Nat.card Γ : ℂ)⁻¹ * LinearMap.trace ℂ _ (∑ᶠ g, fb g • (rp ρ ι p hp g ∘ₗ A.restrict hA)) := by
  haveI := Fintype.ofFinite Γ
  have hL : ∀ v ∈ fixed ρ (p.ker.map ι),
      GlobalTheory.BCT.levOp ρ ι.range (p.ker.map ι) f A v ∈ fixed ρ (p.ker.map ι) := by
    intro v hv
    rw [lev_eq ρ ι hι p hp f fb hf1 hf0 A (hA v hv)]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ ?_)
    exact fx_stable ρ ι p _ (hA v hv)
  unfold GlobalTheory.BCT.twTr
  rw [dif_pos hL, finsum_eq_sum_of_fintype, ← smul_eq_mul, ← map_smul]
  congr 1
  ext ⟨v, hv⟩
  simp only [LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    Submodule.coe_smul, Submodule.coe_sum]
  rw [lev_eq ρ ι hι p hp f fb hf1 hf0 A (hA v hv)]
  rfl

end Gen

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {F₀ : Type} [Field F₀]

private theorem iota_inj (n : ℕ) :
    Function.Injective (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)) := by
  intro a b h
  ext i j
  have h2 := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) h
  simpa using h2

private theorem unit_of_ne (rd : 𝒪[k] →+* F₀) (hrd : Function.Surjective rd) {x : 𝒪[k]} (hx : rd x ≠ 0) :
    IsUnit x := by
  by_contra hu
  apply hx
  have hmax := RingHom.ker_isMaximal_of_surjective rd hrd
  have hm : x ∈ IsLocalRing.maximalIdeal 𝒪[k] := (IsLocalRing.mem_maximalIdeal x).2 hu
  rw [← IsLocalRing.eq_maximalIdeal hmax] at hm
  exact (RingHom.mem_ker).1 hm

private theorem gl_onto (rd : 𝒪[k] →+* F₀) (hrd : Function.Surjective rd) (n : ℕ) :
    Function.Surjective (GeneralLinearGroup.map (n := Fin n) rd) := by
  intro g
  let M : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => Function.surjInv hrd ((g : Matrix (Fin n) (Fin n) F₀) i j)
  have hM : M.map rd = (g : Matrix (Fin n) (Fin n) F₀) := by
    ext i j
    rw [Matrix.map_apply]
    exact Function.surjInv_eq hrd _
  have hdet : IsUnit M.det := by
    apply unit_of_ne rd hrd
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  refine ⟨Matrix.nonsingInvUnit M hdet, ?_⟩
  ext i j
  show rd (M i j) = _
  exact Function.surjInv_eq hrd _

private theorem infl_on (rd : 𝒪[k] →+* F₀) {n : ℕ} (fb : GL (Fin n) F₀ → ℂ) (y : GL (Fin n) 𝒪[k]) :
    infl rd fb (GeneralLinearGroup.map (algebraMap 𝒪[k] k) y) = fb (GeneralLinearGroup.map rd y) := by
  have h : ∃ y', GeneralLinearGroup.map (algebraMap 𝒪[k] k) y' = GeneralLinearGroup.map (algebraMap 𝒪[k] k) y :=
    ⟨y, rfl⟩
  unfold infl
  rw [dif_pos h, iota_inj (k := k) n h.choose_spec]

private theorem infl_off (rd : 𝒪[k] →+* F₀) {n : ℕ} (fb : GL (Fin n) F₀ → ℂ) (x : GL (Fin n) k)
    (hx : x ∉ (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)).range) : infl rd fb x = 0 := by
  unfold infl
  rw [dif_neg (fun h => hx (MonoidHom.mem_range.2 h))]

end Loc

end UpperTheory.Gal.InertialTypesAlt.L.FiniteActions

open UpperTheory.Gal.InertialTypesAlt.L.FiniteActions in
theorem UpperTheory.Gal.InertialTypesAlt.L.finAct :
    UpperTheory.Gal.InertialTypesAlt.L.FinAct := by
  intro k _ _ _ _ F₀ _ _ rd hrd n V _ _ ρ
  have hp := gl_onto rd hrd n
  refine ⟨fun g => hp g, rp ρ _ _ hp, fun y x => rp_spec ρ _ _ hp y x, fun fb A hA => ?_⟩
  exact tr_eq ρ _ (iota_inj n) _ hp (infl rd fb) fb (infl_on rd fb) (infl_off rd fb) A hA
