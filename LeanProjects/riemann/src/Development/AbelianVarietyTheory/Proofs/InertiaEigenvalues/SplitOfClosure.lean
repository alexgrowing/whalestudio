import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff

noncomputable section

namespace GlobalTheory.Pass.FinDesc

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Polynomial Module TensorProduct GlobalTheory.Pass

theorem cob_of_vanish {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex] {L M : Type} [Field L] [CharZero L]
    [AddCommGroup M] [Module L M] (a : G → M →ₗ[L] M) (c : G → M)
    (hc : ∀ g h, c (g * h) = c g + a g (c h)) (h0 : ∀ h ∈ H, c h = 0) :
    ∃ y, ∀ g, c g = a g y - y := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hq : ∀ g : G, c (Quotient.out (g : G ⧸ H)) = c g := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    rw [hh, hc, h0 _ h.2, map_zero, add_zero]
  set S : M := ∑ q : G ⧸ H, c q.out with hS
  have hn : ((Fintype.card (G ⧸ H) : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨-(((Fintype.card (G ⧸ H) : ℕ) : L)⁻¹ • S), fun g => ?_⟩
  have h1 : S = ∑ q : G ⧸ H, c (g • q).out := (Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ H => c q.out)).symm
  have h2 : ∀ q : G ⧸ H, c (g • q).out = c g + a g (c q.out) := by
    intro q
    rw [← hc, ← hq (g * q.out)]
    congr 2
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  simp only [h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum] at h1
  rw [← hS, ← Nat.cast_smul_eq_nsmul L] at h1
  have h3 : c g = ((Fintype.card (G ⧸ H) : ℕ) : L)⁻¹ • (S - a g S) := by
    rw [eq_inv_smul_iff₀ hn, eq_sub_iff_add_eq]; exact h1.symm
  rw [h3, map_neg, map_smul, smul_sub]
  abel

section Ext

variable {G : Type} [Group G] {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

def extRep (ρ : Representation LL G V) (f : G → V) (hf : ∀ g h, f (g * h) = f g + ρ g (f h)) :
    Representation LL G (V × LL) where
  toFun g := LinearMap.prod (LinearMap.coprod (ρ g) (LinearMap.toSpanSingleton LL V (f g))) (LinearMap.snd LL V LL)
  map_one' := by
    have : f 1 = 0 := by
      have := hf 1 1
      simpa using this
    ext <;> simp [this]
  map_mul' g h := by
    refine LinearMap.ext fun z => ?_
    simp [hf]
    abel

theorem extRep_apply (ρ : Representation LL G V) (f : G → V) (hf : ∀ g h, f (g * h) = f g + ρ g (f h))
    (g : G) (z : V × LL) : extRep ρ f hf g z = (ρ g z.1 + z.2 • f g, z.2) := by
  simp [extRep]

end Ext

section OnePD

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem actVB_tmul (ρ : Representation LL G V) (g : G) (v : V) (b : B) :
    actVB PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actB g b := rfl

theorem mem_Dcris (ρ : Representation LL G V) (z : V ⊗[Qp] B) :
    z ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g z = z := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem actVB_mul (ρ : Representation LL G V) (g h : G) (z : V ⊗[Qp] B) :
    actVB PD ρ (g * h) z = actVB PD ρ g (actVB PD ρ h z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB_tmul]
  | add x y hx hy => simp [hx, hy]

abbrev tB (B : Type) [CommRing B] [Algebra Qp B] (u : V →ₗ[LL] V') : V ⊗[Qp] B →ₗ[LL] V' ⊗[Qp] B :=
  AlgebraTensorModule.map u (LinearMap.id : B →ₗ[Qp] B)

theorem tB_act (ρ : Representation LL G V) (ρ' : Representation LL G V') (u : V →ₗ[LL] V')
    (hu : ∀ g x, u (ρ g x) = ρ' g (u x)) (g : G) (z : V ⊗[Qp] B) :
    tB B u (actVB PD ρ g z) = actVB PD ρ' g (tB B u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB_tmul, hu]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem fst_inl (z : V ⊗[Qp] B) :
    tB B (LinearMap.fst LL V LL) (tB B (LinearMap.inl LL V LL) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem snd_inl (z : V ⊗[Qp] B) :
    tB B (LinearMap.snd LL V LL) (tB B (LinearMap.inl LL V LL) z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem decomp (z : (V × LL) ⊗[Qp] B) :
    tB B (LinearMap.inl LL V LL) (tB B (LinearMap.fst LL V LL) z) +
      tB B (LinearMap.inr LL V LL) (tB B (LinearMap.snd LL V LL) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [← add_tmul]
  | add x y hx hy => simp only [map_add]; rw [add_add_add_comm, hx, hy]

theorem split_of_crys [FiniteDimensional LL V] (ρ : Representation LL G V) (f : G → V)
    (hf : ∀ g h, f (g * h) = f g + ρ g (f h)) (h0 : IsCrys PD ρ) (h1 : IsCrys PD (extRep ρ f hf))
    (h2 : IsCrys PD (Representation.trivial LL G LL)) :
    ∃ y : V ⊗[Qp] B, ∀ g, f g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g y - y := by
  haveI := PD.finK₀
  have hn : 0 < finrank Qp K₀ := Module.finrank_pos
  unfold IsCrys at h0 h1 h2
  rw [Module.finrank_prod, Module.finrank_self] at h1
  rw [Module.finrank_self] at h2
  haveI : Module.Finite LL ↥(Dcris PD (extRep ρ f hf)) := Module.finite_of_finrank_pos (by rw [h1]; positivity)
  haveI : Module.Finite LL ↥(Dcris PD (Representation.trivial LL G LL)) :=
    Module.finite_of_finrank_pos (by rw [h2]; positivity)
  have ei : ∀ g x, LinearMap.inl LL V LL (ρ g x) = extRep ρ f hf g (LinearMap.inl LL V LL x) := by
    intro g x; simp [extRep_apply]
  have es : ∀ g x, LinearMap.snd LL V LL (extRep ρ f hf g x) =
      Representation.trivial LL G LL g (LinearMap.snd LL V LL x) := by
    intro g x; simp [extRep_apply]
  let s : ↥(Dcris PD (extRep ρ f hf)) →ₗ[LL] ↥(Dcris PD (Representation.trivial LL G LL)) :=
    (tB B (LinearMap.snd LL V LL)).restrict fun z hz => by
      rw [mem_Dcris] at hz ⊢
      intro g
      rw [← tB_act PD _ _ _ es, hz]
  let p : ↥(LinearMap.ker s) →ₗ[LL] ↥(Dcris PD ρ) :=
    ((tB B (LinearMap.fst LL V LL)).comp ((Submodule.subtype _).comp (Submodule.subtype _))).codRestrict _ fun z => by
      rw [mem_Dcris]
      intro g
      have hz : tB B (LinearMap.snd LL V LL) z.1.1 = 0 := congrArg Subtype.val z.2
      have hd := decomp (B := B) (Qp := Qp) z.1.1
      rw [hz, map_zero, add_zero] at hd
      have h3 := (mem_Dcris PD _ _).1 z.1.2 g
      rw [← hd, ← tB_act PD _ _ _ ei] at h3
      have h4 := congrArg (tB B (LinearMap.fst LL V LL)) h3
      rw [fst_inl, fst_inl] at h4
      exact h4
  have hpb : Function.Bijective p := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z h
      have hz : tB B (LinearMap.snd LL V LL) z.1.1 = 0 := congrArg Subtype.val z.2
      have hz' : tB B (LinearMap.fst LL V LL) z.1.1 = 0 := congrArg Subtype.val h
      have hd := decomp (B := B) (Qp := Qp) z.1.1
      rw [hz, hz', map_zero, map_zero, add_zero] at hd
      exact Subtype.ext (Subtype.ext hd.symm)
    · intro y
      refine ⟨⟨⟨tB B (LinearMap.inl LL V LL) y.1, ?_⟩, ?_⟩, ?_⟩
      · rw [mem_Dcris]
        intro g
        rw [← tB_act PD _ _ _ ei, (mem_Dcris PD _ _).1 y.2 g]
      · exact Subtype.ext (snd_inl y.1)
      · exact Subtype.ext (fst_inl y.1)
  have hk : finrank LL ↥(LinearMap.ker s) = finrank LL ↥(Dcris PD ρ) := (LinearEquiv.ofBijective p hpb).finrank_eq
  have hr := s.finrank_range_add_finrank_ker
  have hr' : LinearMap.range s = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hk, h0, h1, mul_add] at hr
    omega
  have hone : ((1 : LL) ⊗ₜ[Qp] (1 : B)) ∈ Dcris PD (Representation.trivial LL G LL) := by
    rw [mem_Dcris]; intro g; simp [actVB_tmul]
  obtain ⟨z, hz⟩ := LinearMap.range_eq_top.1 hr' ⟨_, hone⟩
  have hz1 : tB B (LinearMap.snd LL V LL) z.1 = (1 : LL) ⊗ₜ[Qp] (1 : B) := congrArg Subtype.val hz
  have hd := decomp (B := B) (Qp := Qp) z.1
  rw [hz1] at hd
  refine ⟨-tB B (LinearMap.fst LL V LL) z.1, fun g => ?_⟩
  have h3 := (mem_Dcris PD _ _).1 z.2 g
  rw [← hd, map_add, ← tB_act PD _ _ _ ei] at h3
  have h4 := congrArg (tB B (LinearMap.fst LL V LL)) h3
  rw [map_add, map_add, fst_inl, fst_inl] at h4
  have h5 : tB B (LinearMap.fst LL V LL) (actVB PD (extRep ρ f hf) g
      (tB B (LinearMap.inr LL V LL) ((1 : LL) ⊗ₜ[Qp] (1 : B)))) = f g ⊗ₜ[Qp] (1 : B) := by
    simp [actVB_tmul, extRep_apply]
  have h6 : tB B (LinearMap.fst LL V LL) (tB B (LinearMap.inr LL V LL) ((1 : LL) ⊗ₜ[Qp] (1 : B))) = 0 := by
    simp
  rw [h5, h6, add_zero] at h4
  rw [map_neg, sub_neg_eq_add, eq_neg_add_iff_add_eq]
  exact h4

end OnePD

section Reps

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]

def extG (W : GRep G Qp LL O) (f : G → W.V) (hf : ∀ g h, f (g * h) = f g + W.ρ g (f h)) (hc : Continuous f) :
    GRep G Qp LL O where
  V := W.V × LL
  ρ := extRep W.ρ f hf
  cont z := by
    simp only [extRep_apply]
    exact ((W.cont z.1).add (hc.const_smul z.2)).prodMk continuous_const

variable (G Qp LL O) in

def trivG : GRep G Qp LL O where
  V := LL
  ρ := Representation.trivial LL G LL
  cont z := by
    simp only [Representation.trivial_apply]
    exact continuous_const

def quotG (A : GRep G Qp LL O) (S : Submodule LL A.V) (hS : ∀ g, S ≤ S.comap (A.ρ g)) : GRep G Qp LL O where
  V := A.V ⧸ S
  cadd := IsModuleTopology.toContinuousAdd LL _
  ρ := A.ρ.quotient S hS
  cont z := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective S z
    exact continuous_quot_mk.comp (A.cont x)

def resG {H : Type} [Group H] [TopologicalSpace H] (i : H →* G) (hi : Continuous i) (A : GRep G Qp LL O) :
    GRep H Qp LL O where
  V := A.V
  ρ := A.ρ.comp i
  cont z := (A.cont z).comp hi

end Reps

section Closure

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]

omit [IsTopologicalRing LL] in
theorem cocycle_of_inj (A W : GRep G Qp LL O) (j : W.V →ₗ[LL] A.V) (hj : Function.Injective j)
    (he : ∀ g v, j (W.ρ g v) = A.ρ g (j v)) (x : A.V) (f : G → W.V) (hf : ∀ g, j (f g) = A.ρ g x - x) :
    f ∈ continuousCocycles W.ρ := by
  refine ⟨?_, fun g h => hj ?_⟩
  · obtain ⟨r, hr⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hj)
    have : f = fun g => r (A.ρ g x + -x) := by
      funext g
      rw [← sub_eq_add_neg, ← hf]
      exact (LinearMap.congr_fun hr (f g)).symm
    rw [this]
    haveI : ContinuousSMul LL W.V := IsModuleTopology.toContinuousSMul LL _
    exact (IsModuleTopology.continuous_of_linearMap r).comp ((A.cont x).add continuous_const)
  · rw [map_add, he, hf, hf, hf, map_mul, map_sub, Module.End.mul_apply]
    abel

theorem split_of_closure
    (hcl : ∀ (A₀ A₁ A₂ : GRep G Qp LL O) (ι : A₀.V →ₗ[LL] A₁.V) (π : A₁.V →ₗ[LL] A₂.V),
      (∀ g x, ι (A₀.ρ g x) = A₁.ρ g (ι x)) → (∀ g x, π (A₁.ρ g x) = A₂.ρ g (π x)) → Function.Injective ι →
      Function.Surjective π → LinearMap.range ι = LinearMap.ker π → IsCrys PD A₁.ρ →
      IsCrys PD A₀.ρ ∧ IsCrys PD A₂.ρ)
    (A W : GRep G Qp LL O) (j : W.V →ₗ[LL] A.V) (hj : Function.Injective j)
    (he : ∀ g v, j (W.ρ g v) = A.ρ g (j v)) (hA : IsCrys PD A.ρ) (x : A.V) (f : G → W.V)
    (hf : ∀ g, j (f g) = A.ρ g x - x) :
    ∃ y : W.V ⊗[Qp] B, ∀ g, f g ⊗ₜ[Qp] (1 : B) = actVB PD W.ρ g y - y := by
  by_cases hx : x ∈ LinearMap.range j
  · obtain ⟨w, rfl⟩ := hx
    refine ⟨w ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
    have : f g = W.ρ g w - w := hj (by rw [hf, map_sub, he])
    rw [this, actVB_tmul, map_one, sub_tmul]
  obtain ⟨hc, hz⟩ := cocycle_of_inj A W j hj he x f hf
  let u : (W.V × LL) →ₗ[LL] A.V := j.coprod (LinearMap.toSpanSingleton LL A.V x)
  have hu : ∀ g z, u (extRep W.ρ f hz g z) = A.ρ g (u z) := by
    intro g z
    simp [u, extRep_apply, he, hf, smul_sub]
    abel
  have hui : Function.Injective u := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨w, c⟩ h
    have h' : j w + c • x = 0 := by simpa [u] using h
    have hc0 : c = 0 := by
      by_contra hne
      apply hx
      refine ⟨-(c⁻¹ • w), ?_⟩
      rw [map_neg, map_smul, eq_neg_of_add_eq_zero_left h', smul_neg, neg_neg, inv_smul_smul₀ hne]
    subst hc0
    rw [zero_smul, add_zero, map_eq_zero_iff j hj] at h'
    subst h'
    rfl
  have hS : ∀ g, LinearMap.range u ≤ (LinearMap.range u).comap (A.ρ g) := by
    rintro g _ ⟨z, rfl⟩
    exact ⟨_, hu g z⟩
  have h1 := (hcl (extG W f hz hc) A (quotG A _ hS) u (LinearMap.range u).mkQ hu (fun g z => rfl) hui
    (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _).symm hA).1
  have ei : ∀ g z, LinearMap.inl LL W.V LL (W.ρ g z) = extRep W.ρ f hz g (LinearMap.inl LL W.V LL z) := by
    intro g z; simp [extRep_apply]
  have er : LinearMap.range (LinearMap.inl LL W.V LL) = LinearMap.ker (LinearMap.snd LL W.V LL) :=
    (LinearMap.ker_snd LL W.V LL).symm
  have es : Function.Surjective (LinearMap.snd LL W.V LL) := LinearMap.snd_surjective
  have h2 := hcl W (extG W f hz hc) (trivG G Qp LL O) (LinearMap.inl LL W.V LL) (LinearMap.snd LL W.V LL)
    ei
    (fun g z => rfl) LinearMap.inl_injective es er h1
  exact split_of_crys PD W.ρ f hz h2.1 h1 h2.2

omit [TopologicalSpace G] [TopologicalSpace LL] [IsTopologicalRing LL] in
theorem actVB_congr {G' : Type} [Group G'] {K₀' K' : Type} [Field K₀'] [Field K']
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    [Algebra K₀' B] [IsScalarTower Qp K₀' B] [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR] (PD' : PeriodData G' Qp K₀' K' B BdR)
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (ρ' : Representation LL G' V) (g : G) (g' : G') (h1 : ρ g = ρ' g')
    (h2 : ∀ b, PD.actB g b = PD'.actB g' b) (z : V ⊗[Qp] B) : actVB PD ρ g z = actVB PD' ρ' g' z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul v b => rw [actVB_tmul, actVB_tmul, h1, h2]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

omit [TopologicalSpace G] [TopologicalSpace LL] [IsTopologicalRing LL] in

theorem descend [CharZero LL] (H : Subgroup G) [H.FiniteIndex]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (f : G → V) (hf : ∀ g h, f (g * h) = f g + ρ g (f h)) (y : V ⊗[Qp] B)
    (hy : ∀ g ∈ H, f g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g y - y) :
    ∃ z : V ⊗[Qp] B, ∀ g, f g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g z - z := by
  obtain ⟨w, hw⟩ := cob_of_vanish H (actVB PD ρ)
    (fun g => f g ⊗ₜ[Qp] (1 : B) - (actVB PD ρ g y - y))
    (fun g k => by
      rw [hf, actVB_mul, add_tmul, map_sub, map_sub, actVB_tmul, map_one]
      abel)
    (fun g hg => sub_eq_zero.2 (hy g hg))
  refine ⟨w + y, fun g => ?_⟩
  rw [map_add, sub_eq_iff_eq_add.1 (hw g)]
  abel

end Closure

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1), (GKin h).Normal → (GKin h).FiniteIndex → (∀ (A₀ A₁ A₂ : GRep ↥(GK K') ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : A₀.V →ₗ[↥LL.1] A₁.V) (π : A₁.V →ₗ[↥LL.1] A₂.V), (∀ g x, ι (A₀.ρ g x) = A₁.ρ g (ι x)) → (∀ g x, π (A₁.ρ g x) = A₂.ρ g (π x)) → Function.Injective ι → Function.Surjective π → LinearMap.range ι = LinearMap.ker π → IsCrys (P.PD K') A₁.ρ → IsCrys (P.PD K') A₀.ρ ∧ IsCrys (P.PD K') A₂.ρ) → ∀ (A W : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (j : W.V →ₗ[↥LL.1] A.V), Function.Injective j → (∀ g v, j (W.ρ g v) = A.ρ g (j v)) → IsCrys (P.PD K') (A.ρ.comp (Subgroup.inclusion (GK_le h))) → ∀ (x : A.V) (f : ↥(GK K) → W.V), (∀ g, j (f g) = A.ρ g x - x) → f ∈ finiteCocycles (P.PD K) W.ρ := by
  intro l _ P K K' LL h _ hF hcl A W j hj he hA x f hf
  have hZ := cocycle_of_inj A W j hj he x f hf
  refine ⟨hZ, ?_⟩
  have hi : Continuous (Subgroup.inclusion (GK_le h)) := continuous_inclusion (GK_le h)
  let ρ' : Representation ↥LL.1 ↥(GK K') W.V := W.ρ.comp (Subgroup.inclusion (GK_le h))
  obtain ⟨y', hy⟩ : ∃ y : W.V ⊗[ℚ_[l]] P.R.B, ∀ g, f (Subgroup.inclusion (GK_le h) g) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      actVB (P.PD K') ρ' g y - y :=
    split_of_closure (P.PD K') hcl (resG _ hi A) (resG _ hi W) j hj (fun g v => he _ v) hA x
      (fun g => f (Subgroup.inclusion (GK_le h) g)) (fun g => hf _)
  have hact : ∀ (g : ↥(GK K')) (z : W.V ⊗[ℚ_[l]] P.R.B), actVB (P.PD K') ρ' g z =
      actVB (P.PD K) W.ρ (Subgroup.inclusion (GK_le h) g) z := by
    intro g z
    exact actVB_congr (P.PD K') (P.PD K) ρ' W.ρ g _ rfl
      (fun b => (P.PD_actB K' g b).trans (P.PD_actB K (Subgroup.inclusion (GK_le h) g) b).symm) z
  haveI : CharZero ↥LL.1 := algebraRat.charZero _
  exact descend (P.PD K) (GKin h) W.ρ f hZ.2 y' fun g hg => (hy ⟨g.1, hg⟩).trans (congrArg (· - y') (hact ⟨g.1, hg⟩ y'))

end GlobalTheory.Pass.FinDesc

end
