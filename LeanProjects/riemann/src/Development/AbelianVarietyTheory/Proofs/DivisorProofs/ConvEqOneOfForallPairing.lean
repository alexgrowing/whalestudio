import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv Module

namespace GlobalTheory

namespace TateFree

theorem exists_compat_of_surjective (n : ℕ) : ∀ (X : ℕ → Type) (π : ∀ k, X (k + 1) → X k),
    (∀ k, Function.Surjective (π k)) → ∀ x : X n,
      ∃ s : ∀ k, X k, (∀ k, π k (s (k + 1)) = s k) ∧ s n = x := by
  induction n with
  | zero =>
    intro X π hπ x
    exact ⟨fun k => Nat.rec x (fun k y => Function.surjInv (hπ k) y) k,
      fun k => Function.surjInv_eq (hπ k) _, rfl⟩
  | succ n ih =>
    intro X π hπ x
    obtain ⟨s, hs, hx⟩ := ih (fun k => X (k + 1)) (fun k => π (k + 1)) (fun k => hπ (k + 1)) x
    refine ⟨fun k => Nat.casesOn k (π 0 (s 0)) s, fun k => ?_, hx⟩
    cases k with
    | zero => rfl
    | succ k => exact hs k

section Points

variable (O C A : Type) [CommRing O] [Field C] [Algebra O C] [IsIntegrallyClosedIn O C]
  [CommRing A]

theorem comp_ofId_bijective [Algebra O A] [Module.Finite O A] :
    Function.Bijective fun x : A →ₐ[O] O => (Algebra.ofId O C).comp x := by
  have hi : Function.Injective (Algebra.ofId O C) := IsIntegralClosure.algebraMap_injective O O C
  refine ⟨fun x y h => AlgHom.ext fun a => hi (DFunLike.congr_fun h a), fun y => ?_⟩
  have hm : ∀ a, y a ∈ (Algebra.ofId O C).range := fun a =>
    IsIntegrallyClosedIn.isIntegral_iff.1 ((Algebra.IsIntegral.isIntegral a).map y)
  let e := AlgEquiv.ofInjective _ hi
  exact ⟨(e.symm : (Algebra.ofId O C).range →ₐ[O] O).comp (y.codRestrict _ hm),
    AlgHom.ext fun a => congrArg Subtype.val (e.apply_symm_apply ⟨y a, hm a⟩)⟩

variable [IsAlgClosed C] [CharZero C] [HopfAlgebra O A] [Module.Finite O A]

theorem natCard_pts : Nat.card (A →ₐ[O] O) = finrank C (C ⊗[O] A) := by
  have := etale_of_hopfAlgebra C (C ⊗[O] A)
  rw [Nat.card_congr (Equiv.ofBijective _ (comp_ofId_bijective O C A)),
    Nat.card_congr (AlgHom.liftEquiv O C A C), natCard_algHom_eq_finrank_of_etale]

include C in

theorem eq_of_forall_pts [Module.Flat O A] {a b : A} (h : ∀ x : A →ₐ[O] O, x a = x b) :
    a = b := by
  have := etale_of_hopfAlgebra C (C ⊗[O] A)
  have hi : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[O] C ⊗[O] A) :=
    Algebra.TensorProduct.includeRight_injective (IsIntegralClosure.algebraMap_injective O O C)
  refine hi ((Algebra.FormallyEtale.equivPiOfIsSepClosed C (C ⊗[O] A)).injective
    (funext fun q => ?_))
  let χ : C ⊗[O] A →ₐ[C] C := (Pi.evalAlgHom C (fun _ => C) q).comp
    (Algebra.FormallyEtale.equivPiOfIsSepClosed C (C ⊗[O] A) : _ →ₐ[C] _)
  obtain ⟨φ, hφ⟩ := (comp_ofId_bijective O C A).2 ((AlgHom.liftEquiv O C A C).symm χ)
  exact (DFunLike.congr_fun hφ a).symm.trans
    ((congrArg (Algebra.ofId O C) (h φ)).trans (DFunLike.congr_fun hφ b))

end Points

section Padic

variable {p : ℕ} [Fact p.Prime] {M N : Type} [AddCommGroup M] [Module ℤ_[p] M] [AddCommGroup N]
  [Module ℤ_[p] N]

theorem mem_pow_smul_top_iff (n : ℕ) (x : M) :
    x ∈ (IsLocalRing.maximalIdeal ℤ_[p] ^ n • ⊤ : Submodule ℤ_[p] M) ↔
      ∃ y, (p : ℤ_[p]) ^ n • y = x := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem surjective_of_mod (f : M →ₗ[ℤ_[p]] N) [Module.Finite ℤ_[p] M]
    (hN : ∀ y : N, (∀ n, ∃ z, (p : ℤ_[p]) ^ n • z = y) → y = 0)
    (h : ∀ y, ∃ x z, (p : ℤ_[p]) • z = y - f x) : Function.Surjective f := by
  have := isPrecomplete_of_finite (IsLocalRing.maximalIdeal ℤ_[p]) M
  have : IsHausdorff (IsLocalRing.maximalIdeal ℤ_[p]) N := ⟨fun y hy => hN y fun n =>
    (mem_pow_smul_top_iff n y).1 (SModEq.zero.1 (hy n))⟩
  refine surjective_of_mkQ_comp_surjective (I := IsLocalRing.maximalIdeal ℤ_[p]) fun y => ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨x, z, hz⟩ := h y
  refine ⟨x, ((Submodule.Quotient.eq _).2 ?_).symm⟩
  have := (mem_pow_smul_top_iff 1 (y - f x)).2 ⟨z, by rw [pow_one, hz]⟩
  rwa [pow_one] at this

theorem natCard_eq_pow_finrank [Module.Finite ℤ_[p] M] [Module.Free ℤ_[p] M] {X : Type}
    [AddCommGroup X] (f : M →+ X) (hf : Function.Surjective f)
    (hk : ∀ x, f x = 0 ↔ ∃ y, (p : ℤ_[p]) • y = x) : Nat.card X = p ^ finrank ℤ_[p] M := by
  let b := Module.finBasis ℤ_[p] M
  let g : M →+ (Fin (finrank ℤ_[p] M) → ZMod p) :=
    AddMonoidHom.pi fun i => (PadicInt.toZMod (p := p)).toAddMonoidHom.comp
      (b.coord i).toAddMonoidHom
  have hg : Function.Surjective g := fun v =>
    ⟨b.equivFun.symm fun i => ((v i).val : ℤ_[p]), funext fun i => by
      change PadicInt.toZMod (b.equivFun (b.equivFun.symm _) i) = _
      rw [LinearEquiv.apply_symm_apply]
      simp⟩
  have hker : f.ker = g.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hk]
    constructor
    · rintro ⟨y, rfl⟩
      funext i
      simp [g]
    · intro hx
      have : ∀ i, ∃ c : ℤ_[p], c * p = b.repr x i := fun i => by
        have h1 : b.repr x i ∈ RingHom.ker (PadicInt.toZMod (p := p)) := congrFun hx i
        rwa [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
          Ideal.mem_span_singleton'] at h1
      choose c hc using this
      refine ⟨b.equivFun.symm c, b.equivFun.injective (funext fun i => ?_)⟩
      rw [map_smul, LinearEquiv.apply_symm_apply]
      simp [← hc, mul_comm]
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv, hker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv]
  simp [Nat.card_pi]

theorem bijective_of_mod [Module.Finite ℤ_[p] M] [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] N]
    [Module.Free ℤ_[p] N] (f : M →ₗ[ℤ_[p]] N) (hr : finrank ℤ_[p] M = finrank ℤ_[p] N)
    (h : ∀ x, (∃ z, (p : ℤ_[p]) • z = f x) → ∃ y, (p : ℤ_[p]) • y = x) :
    Function.Bijective f := by
  obtain ⟨e⟩ := (FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq).2 hr.symm
  suffices H : IsUnit (LinearMap.det (e.toLinearMap ∘ₗ f)) by
    have h1 := ((LinearMap.isUnit_iff_isUnit_det _).2 H)
    rw [Module.End.isUnit_iff] at h1
    exact (Function.Bijective.of_comp_iff' e.bijective f).1 h1
  let b := Module.finBasis ℤ_[p] M
  let A := LinearMap.toMatrix b b (e.toLinearMap ∘ₗ f)
  rw [← LinearMap.det_toMatrix b, ← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod,
    RingHom.mem_ker, RingHom.map_det]
  intro h0
  obtain ⟨v, hv, hA⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  let c : _ → ℤ_[p] := fun i => ((v i).val : ℤ_[p])
  have hc : ∀ i, PadicInt.toZMod (c i) = v i := fun i => by simp [c]
  have h1 : ∀ i, ∃ d : ℤ_[p], d * p = A.mulVec c i := fun i => by
    have h1 : A.mulVec c i ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [RingHom.mem_ker, RingHom.map_mulVec, show PadicInt.toZMod ∘ c = v from funext hc]
      exact congrFun hA i
    rwa [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h1
  choose d hd using h1
  obtain ⟨y, hy⟩ := h (b.equivFun.symm c) ⟨e.symm (b.equivFun.symm d), e.injective <|
    b.equivFun.injective <| funext fun i => by
      have h2 := congrFun (LinearMap.toMatrix_mulVec_repr b b (e.toLinearMap ∘ₗ f)
        (b.equivFun.symm c)) i
      rw [← b.equivFun_apply, b.equivFun.apply_symm_apply] at h2
      rw [map_smul, map_smul, e.apply_symm_apply, b.equivFun.apply_symm_apply, Pi.smul_apply,
        smul_eq_mul, mul_comm, hd]
      exact h2⟩
  refine hv (funext fun i => ?_)
  have h3 := congrFun (congrArg b.equivFun hy) i
  rw [map_smul, b.equivFun.apply_symm_apply] at h3
  rw [← hc, ← h3]
  simp

end Padic

end TateFree

namespace PDivGroup

open PDiv TateFree

variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)

section General

variable {B : Type} [CommRing B] [Algebra O B]

theorem ptsMap_res_injective (n : ℕ) : Function.Injective (pointsMap B (G.res n)) := fun x y h =>
  ofConv_injective <| AlgHom.ext fun a => by
    obtain ⟨b, rfl⟩ := G.res_surjective n a
    exact DFunLike.congr_fun (congrArg ofConv h) b

theorem ptsMap_res_mulP (n : ℕ) (x : WithConv (G.A (n + 1) →ₐ[O] B)) :
    pointsMap B (G.res n) (pointsMap B (G.mulP n) x) = x ^ p :=
  ofConv_injective <| Eq.symm <| (comp_mulBy_pts x.ofConv p).symm.trans <|
    AlgHom.ext fun a => congrArg x.ofConv (G.mulP_res n a).symm

theorem pointsMap_mulP_res_eq_pow (n : ℕ) (x : WithConv (G.A n →ₐ[O] B)) :
    pointsMap B (G.mulP n) (pointsMap B (G.res n) x) = x ^ p :=
  ofConv_injective <| Eq.symm <| (comp_mulBy_pts x.ofConv p).symm.trans <|
    AlgHom.ext fun a => congrArg x.ofConv (G.res_mulP n a).symm

theorem natCard_ker_ptsMap_mulP (n : ℕ) :
    Nat.card (pointsMap O (G.mulP n)).ker = Nat.card (G.A 1 →ₐ[O] O) := by
  obtain ⟨f, hf, hk⟩ := G.exists_res_le (m := 1) (n := n + 1) (by omega)
  have key : ∀ x : WithConv (G.A (n + 1) →ₐ[O] O),
      x ∈ (pointsMap O (G.mulP n)).ker ↔ RingHom.ker f ≤ RingHom.ker x.ofConv := fun x => by
    rw [hk, torsionIdeal_le_ker_iff, pow_one, toConv_ofConv, ← ptsMap_res_mulP,
      map_eq_one_iff _ (G.ptsMap_res_injective n), MonoidHom.mem_ker]
  have hm : ∀ y : G.A 1 →ₐ[O] O, toConv (y.comp (f : G.A (n + 1) →ₐ[O] G.A 1)) ∈
      (pointsMap O (G.mulP n)).ker := fun y => (key _).2 fun a ha => by
    have ha' : f a = 0 := ha
    change y (f a) = 0
    rw [ha', map_zero]
  refine (Nat.card_congr (Equiv.ofBijective (fun y => ⟨_, hm y⟩)
    ⟨fun y z h => AlgHom.ext fun a => ?_, fun x => ?_⟩)).symm
  · obtain ⟨b, rfl⟩ := hf a
    exact DFunLike.congr_fun (congrArg ofConv (congrArg Subtype.val h)) b
  · have h1 := AlgHom.liftOfSurjective_comp (f : G.A (n + 1) →ₐ[O] G.A 1) hf x.1.ofConv
      ((key x.1).1 x.2)
    exact ⟨_, Subtype.ext (ofConv_injective h1)⟩

variable [Fact p.Prime] {G}

theorem TateOver.p_smul_conv (x : G.TateOver B) (n : ℕ) :
    ((p : ℤ_[p]) • x).conv n = x.conv n ^ p :=
  pow_digit_natCast (G.pts_pow_self n _) p

theorem TateOver.pow_smul_conv (x : G.TateOver B) (k n : ℕ) :
    ((p : ℤ_[p]) ^ k • x).conv n = x.conv n ^ p ^ k := by
  rw [← Nat.cast_pow]
  exact pow_digit_natCast (G.pts_pow_self n _) _

theorem TateOver.exists_p_smul_eq (t : G.TateOver B) (n : ℕ) (ht : t.conv (n + 1) = 1) :
    ∃ s : G.TateOver B, s.conv n = 1 ∧ (p : ℤ_[p]) • s = t := by
  have h1 : ∀ k, t.conv (k + 1) = 1 → t.conv 1 = 1 := fun k => by
    induction k with
    | zero => exact id
    | succ k ih => exact fun h => ih (by rw [← t.compat_conv, h, map_one])
  have h2 : ∀ k, t.conv (k + 1) ^ p ^ k = 1 := fun k => by
    induction k with
    | zero => rw [pow_zero, pow_one]; exact h1 n ht
    | succ k ih => rw [pow_succ', pow_mul, t.conv_succ_pow, ← map_pow, ih, map_one]
  choose s hs using fun k => (G.exists_comp_res_iff k (t.pt (k + 1))).2 (h2 k)
  have hs' : ∀ k, pointsMap B (G.res k) (toConv (s k)) = t.conv (k + 1) := fun k =>
    congrArg toConv (hs k)
  refine ⟨⟨s, fun k => congrArg ofConv (G.ptsMap_res_injective k
    (a₁ := pointsMap B (G.mulP k) (toConv (s (k + 1)))) (a₂ := toConv (s k)) ?_)⟩,
    G.ptsMap_res_injective n (((hs' n).trans ht).trans (map_one _).symm),
    TateOver.ext_conv fun k => ?_⟩
  · rw [ptsMap_res_mulP, ← pointsMap_mulP_res_eq_pow, hs', hs', t.compat_conv]
  · rw [TateOver.p_smul_conv, ← pointsMap_mulP_res_eq_pow, ← t.compat_conv, ← hs']

theorem TateOver.conv_eq_one_iff (t : G.TateOver B) (n : ℕ) :
    t.conv n = 1 ↔ ∃ s : G.TateOver B, (p : ℤ_[p]) ^ n • s = t := by
  constructor
  · induction n generalizing t with
    | zero => exact fun _ => ⟨t, by rw [pow_zero, one_smul]⟩
    | succ n ih =>
      intro ht
      obtain ⟨s, hs, rfl⟩ := t.exists_p_smul_eq n ht
      obtain ⟨u, rfl⟩ := ih s hs
      exact ⟨u, by rw [pow_succ', mul_smul]⟩
  · rintro ⟨s, rfl⟩
    rw [TateOver.pow_smul_conv, G.pts_pow_self]

theorem TateOver.eq_zero_of_forall_pow_smul (t : G.TateOver B)
    (h : ∀ n, ∃ s : G.TateOver B, (p : ℤ_[p]) ^ n • s = t) : t = 0 :=
  TateOver.ext_conv fun n => (t.conv_eq_one_iff n).2 (h n)

theorem TateOver.eq_zero_of_p_smul (t : G.TateOver B) (h : (p : ℤ_[p]) • t = 0) : t = 0 :=
  TateOver.ext_conv fun n => G.ptsMap_res_injective n <| by
    rw [← t.conv_succ_pow, ← TateOver.p_smul_conv, h, TateOver.zero_conv, TateOver.zero_conv,
      map_one]

instance TateOver.isTorsionFree : IsTorsionFree ℤ_[p] (G.TateOver B) := by
  refine .of_smul_eq_zero fun a t h => ?_
  by_cases ha : a = 0
  · exact .inl ha
  refine .inr ?_
  have key : ∀ (k : ℕ) (t : G.TateOver B), (p : ℤ_[p]) ^ k • t = 0 → t = 0 := fun k => by
    induction k with
    | zero => intro t h; rwa [pow_zero, one_smul] at h
    | succ k ih =>
      intro t h
      exact t.eq_zero_of_p_smul (ih _ (by rwa [pow_succ, mul_smul] at h))
  rw [PadicInt.unitCoeff_spec ha, mul_smul] at h
  exact key _ t ((Units.isUnit _).smul_eq_zero.1 h)

variable (G) in

def tateLevel (n : ℕ) : G.Tate →+ Additive (WithConv (G.A n →ₐ[O] O)) where
  toFun t := Additive.ofMul (t.conv n)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem tateLevel_apply (n : ℕ) (t : G.Tate) :
    tateLevel G n t = Additive.ofMul (t.conv n) := rfl

theorem muRoot_eq_one_iff (x : (mu p O).TateOver B) (n : ℕ) :
    muRoot x n = 1 ↔ ∃ y : (mu p O).TateOver B, (p : ℤ_[p]) ^ n • y = x := by
  rw [← TateOver.conv_eq_one_iff, ← muRoot_zero (p := p) (O := O) n]
  exact ⟨fun h => congrArg toConv (mu_algHom_ext h),
    fun h => DFunLike.congr_fun (congrArg ofConv h) _⟩

theorem smul_muTate_bijective [IsDomain B] (ζ : ℕ → B) (h0 : ζ 0 = 1)
    (h : ∀ n, ζ (n + 1) ^ p = ζ n) (hζ : ∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) :
    Function.Bijective fun a : ℤ_[p] => a • muTate O ζ h0 h := by
  change Function.Bijective (LinearMap.toSpanSingleton ℤ_[p] _ (muTate O ζ h0 h))
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    have h1 := congrArg (muRoot · n) ha
    simp only [LinearMap.toSpanSingleton_apply, muRoot_smul, muRoot_muTate, muRoot_zero] at h1
    rw [← cast_digit, map_zero, ZMod.natCast_eq_zero_iff]
    exact ((hζ n).pow_eq_one_iff_dvd _).1 h1
  · refine surjective_of_mod _ TateOver.eq_zero_of_forall_pow_smul fun y => ?_
    obtain ⟨k, -, hk⟩ := (hζ 1).eq_pow_of_pow_eq_one (muRoot_pow_self y 1)
    have h1 : muRoot ((k : ℤ_[p]) • muTate O ζ h0 h) 1 = muRoot y 1 := by
      rw [muRoot_smul, pow_digit_natCast (muRoot_pow_self _ 1), muRoot_muTate, hk]
    obtain ⟨z, hz⟩ := (muRoot_eq_one_iff (y - (k : ℤ_[p]) • muTate O ζ h0 h) 1).1 <| by
      have h2 := muRoot_add (y - (k : ℤ_[p]) • muTate O ζ h0 h) ((k : ℤ_[p]) • muTate O ζ h0 h) 1
      rw [sub_add_cancel, h1] at h2
      have h3 : muRoot y 1 ≠ 0 := (IsUnit.of_pow_eq_one (muRoot_pow_self y 1)
        (NeZero.ne _)).ne_zero
      exact mul_right_cancel₀ h3 (h2.symm.trans (one_mul _).symm)
    exact ⟨k, z, by rwa [pow_one] at hz⟩

end General

section Closed

variable (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C]
  [CharZero C]
include C

theorem natCard_pts_eq (n : ℕ) : Nat.card (G.A n →ₐ[O] O) = p ^ (n * G.height) := by
  have h := congrFun (rankAtStalk_eq_finrank_of_free (R := C) (M := C ⊗[O] G.A n)) ⊥
  rw [rankAtStalk_baseChange, G.rank_eq] at h
  rw [natCard_pts O C]
  exact h.symm

variable [Fact p.Prime]

theorem natCard_conv_pts_eq (n : ℕ) :
    Nat.card (WithConv (G.A n →ₐ[O] O)) = p ^ (n * G.height) :=
  (Nat.card_congr (WithConv.equiv _)).trans (G.natCard_pts_eq C n)

theorem pointsMap_mulP_surjective (n : ℕ) : Function.Surjective (pointsMap O (G.mulP n)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have : Finite (WithConv (G.A n →ₐ[O] O)) :=
    Nat.finite_of_card_ne_zero (by rw [G.natCard_conv_pts_eq C]; positivity)
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (pointsMap O (G.mulP n)).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, natCard_ker_ptsMap_mulP,
    G.natCard_pts_eq C, G.natCard_conv_pts_eq C, add_mul, pow_add] at h
  rw [← MonoidHom.range_eq_top]
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [G.natCard_conv_pts_eq C]
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos hp _) h).symm

theorem pt_surjective (n : ℕ) : Function.Surjective fun t : G.Tate => t.pt n := fun x => by
  obtain ⟨s, hs, hx⟩ := exists_compat_of_surjective n (fun k => WithConv (G.A k →ₐ[O] O))
    (fun k => pointsMap O (G.mulP k)) (G.pointsMap_mulP_surjective C) (toConv x)
  exact ⟨⟨fun k => (s k).ofConv, fun k => congrArg ofConv (hs k)⟩, congrArg ofConv hx⟩

theorem tateLevel_surjective (n : ℕ) : Function.Surjective (tateLevel G n) := fun x => by
  obtain ⟨t, ht⟩ := G.pt_surjective C n x.toMul.ofConv
  exact ⟨t, congrArg (fun y => Additive.ofMul (toConv y)) ht⟩

theorem finite_tate : Module.Finite ℤ_[p] G.Tate := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have : Finite (G.A 1 →ₐ[O] O) :=
    Nat.finite_of_card_ne_zero (by rw [G.natCard_pts_eq C]; positivity)
  choose l hl using G.pt_surjective C 1
  refine .of_surjective (Finsupp.linearCombination ℤ_[p] l)
    (surjective_of_mod _ TateOver.eq_zero_of_forall_pow_smul fun y => ?_)
  obtain ⟨z, hz⟩ := (TateOver.conv_eq_one_iff (y - l (y.pt 1)) 1).1 <| by
    have h : tateLevel G 1 (y - l (y.pt 1)) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg (fun y => Additive.ofMul (toConv y)) (hl _).symm
    exact h
  exact ⟨Finsupp.single (y.pt 1) 1, z, by simpa using hz⟩

theorem free_tate : Module.Free ℤ_[p] G.Tate :=
  have := G.finite_tate C
  inferInstance

theorem finrank_tate : finrank ℤ_[p] G.Tate = G.height := by
  have := G.finite_tate C
  have h := natCard_eq_pow_finrank (p := p) (tateLevel G 1) (G.tateLevel_surjective C 1)
    fun t => by simpa using t.conv_eq_one_iff 1
  rw [Nat.card_congr Additive.toMul, G.natCard_conv_pts_eq C, one_mul] at h
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm

theorem conv_eq_one_of_forall_pairing (χ : G.dual.Tate) (n : ℕ)
    (h : ∀ t : G.Tate, muRoot (pairing G O t χ) n = 1) : χ.conv n = 1 := by
  have h1 : charElem χ n = charElem (0 : G.dual.Tate) n := eq_of_forall_pts O C _ fun x => by
    obtain ⟨t, rfl⟩ := G.pt_surjective C n x
    rw [charElem_zero, map_one, ← muRoot_pairing, h]
  exact ofConv_injective <| AlgHom.ext fun φ =>
    (apply_charElem χ n φ).symm.trans <| (congrArg φ.ofConv h1).trans (apply_charElem 0 n φ)

theorem conv_eq_one_of_forall_pairing' (t : G.Tate) (n : ℕ)
    (h : ∀ χ : G.dual.Tate, muRoot (pairing G O t χ) n = 1) : t.conv n = 1 := by
  have h1 : (toConv (t.pt n).toLinearMap : CartierDual O (G.A n)) =
      toConv ((0 : G.Tate).pt n).toLinearMap := eq_of_forall_pts O C (G.dual.A n) fun x => by
    obtain ⟨χ, rfl⟩ := G.dual.pt_surjective C n x
    refine (apply_charElem χ n _).symm.trans (Eq.trans ?_ (apply_charElem χ n _))
    change t.pt n (charElem χ n) = (0 : G.Tate).pt n (charElem χ n)
    rw [← muRoot_pairing, ← muRoot_pairing, h, map_zero, LinearMap.zero_apply, muRoot_zero]
  exact ofConv_injective <| AlgHom.ext fun a => LinearMap.congr_fun (congrArg ofConv h1) a

theorem pairing_bijective : Function.Bijective (pairing G O) := by
  have := G.finite_tate C
  have := G.dual.finite_tate C
  have := (mu p O).finite_tate C
  refine bijective_of_mod _ ?_ fun t ⟨z, hz⟩ => ?_
  · rw [finrank_linearMap, G.finrank_tate C, G.dual.finrank_tate C, (mu p O).finrank_tate C,
      mul_one]
  · have h := (t.conv_eq_one_iff 1).1 <| G.conv_eq_one_of_forall_pairing' C t 1 fun χ =>
      (muRoot_eq_one_iff _ 1).2 ⟨z χ, by rw [pow_one, ← hz, LinearMap.smul_apply]⟩
    rwa [pow_one] at h

theorem pairing_flip_bijective : Function.Bijective (pairing G O).flip := by
  have := G.finite_tate C
  have := G.dual.finite_tate C
  have := (mu p O).finite_tate C
  refine bijective_of_mod _ ?_ fun χ ⟨z, hz⟩ => ?_
  · rw [finrank_linearMap, G.finrank_tate C, G.dual.finrank_tate C, (mu p O).finrank_tate C,
      mul_one]
  · have h := (χ.conv_eq_one_iff 1).1 <| G.conv_eq_one_of_forall_pairing C χ 1 fun t =>
      (muRoot_eq_one_iff _ 1).2 ⟨z t, by
        rw [pow_one, ← LinearMap.flip_apply (pairing G O), ← hz, LinearMap.smul_apply]⟩
    rwa [pow_one] at h

variable (p O) in

theorem exists_primitive_system : ∃ ζ : ℕ → O, ζ 0 = 1 ∧ (∀ n, ζ (n + 1) ^ p = ζ n) ∧
    ∀ n, IsPrimitiveRoot (ζ n) (p ^ n) := by
  have hp : p.Prime := Fact.out
  have hi : Function.Injective (algebraMap O C) := IsIntegralClosure.algebraMap_injective O O C
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  obtain ⟨η, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.1
    ((hξ.isIntegral hp.pos).tower_top (A := O))
  have hη : IsPrimitiveRoot η p := hξ.of_map_of_injective hi
  obtain ⟨t, ht⟩ := (mu p O).pt_surjective C 1
    (muPoint O η (by rw [pow_one]; exact hη.pow_eq_one))
  have h1 : muRoot t 1 = η := (DFunLike.congr_fun ht _).trans (muPoint_muT _ _)
  have h2 : ∀ n, muRoot t (n + 1) ^ p ^ n = η := fun n => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ', pow_mul, muRoot_succ_pow, ih]
  refine ⟨muRoot t, by simpa using muRoot_pow_self t 0, muRoot_succ_pow t, fun n => ?_⟩
  cases n with
  | zero => rw [show muRoot t 0 = 1 by simpa using muRoot_pow_self t 0, pow_zero]; exact .one
  | succ n =>
    have := (algebraMap O C).domain_nontrivial
    rw [← orderOf_eq_prime_pow (by rw [h2]; exact hη.ne_one hp.one_lt) (muRoot_pow_self t (n + 1))]
    exact IsPrimitiveRoot.orderOf _

end Closed

end PDivGroup

theorem PDivGroup.tate_free_perfect (p : ℕ) [Fact p.Prime] (O C : Type) [CommRing O] [IsDomain O]
    [IsIntegrallyClosed O] [Field C] [Algebra O C] [IsFractionRing O C] [IsAlgClosed C]
    [CharZero C] (G : PDivGroup p O) :
    (∀ n, Nat.card (G.A n →ₐ[O] O) = p ^ (n * G.height)) ∧
    (∀ n, Function.Surjective fun t : G.Tate => t.pt n) ∧
    (∀ (n : ℕ) (t : G.Tate), t.conv n = 1 ↔ ∃ s : G.Tate, (p : ℤ_[p]) ^ n • s = t) ∧
    (Module.Finite ℤ_[p] G.Tate ∧ Module.Free ℤ_[p] G.Tate ∧
      finrank ℤ_[p] G.Tate = G.height) ∧
    (∃ ζ : ℕ → O, ζ 0 = 1 ∧ (∀ n, ζ (n + 1) ^ p = ζ n) ∧ ∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) ∧
    (∀ (ζ : ℕ → O) (h0 : ζ 0 = 1) (h : ∀ n, ζ (n + 1) ^ p = ζ n),
      (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) →
        Function.Bijective fun a : ℤ_[p] => (a • PDivGroup.muTate O ζ h0 h :
          (PDivGroup.mu p O).Tate)) ∧
    Function.Bijective (PDivGroup.pairing G O) ∧
    Function.Bijective (PDivGroup.pairing G O).flip :=
  ⟨G.natCard_pts_eq C, G.pt_surjective C, fun n t => t.conv_eq_one_iff n,
    ⟨G.finite_tate C, G.free_tate C, G.finrank_tate C⟩, PDivGroup.exists_primitive_system p O C,
    PDivGroup.smul_muTate_bijective, G.pairing_bijective C, G.pairing_flip_bijective C⟩

end GlobalTheory
