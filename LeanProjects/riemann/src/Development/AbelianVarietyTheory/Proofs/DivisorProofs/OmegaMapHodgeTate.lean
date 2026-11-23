import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeFiniteProjectiveReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingChainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeNakayamaApproximation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularOfIsReflexive

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.GroupBplus (IsPropG TorsionMap dualVec EF_dualVec)
open GlobalTheory.RingChain (RChain IsOf)
open GlobalTheory.PDivGroup (muRoot omegaMap tateMap dualHom dlog hodgeTate)
open GlobalTheory.PerfdLat (PrismData ConstTate eps dualBaseChange bcTate bcChar)
open GlobalTheory.Published (CycPerfd)
open scoped TensorProduct Pointwise

namespace GlobalTheory.ChainPts.SysB.KerRho

section Group

variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] {GG : PDivGroup p A}

theorem hodgeTate_bcTate (R : Type) [CommRing R] [Algebra A R] (t : GG.Tate) :
    omegaMap _ _ (dualBaseChange R GG).inv (hodgeTate _ (bcTate R t)) = (GG.dual.toBase R).omega (hodgeTate GG t) := by
  rw [PDivGroup.hodgeTate_apply t, ← PerfdLat.dlog_bcChar]
  refine Subtype.ext (funext fun n => ?_)
  rw [PDivGroup.omegaMap_val, PDivGroup.hodgeTate_val, PDiv.cotMap_d, PDivGroup.dlog_val, PerfdLat.charElem_bcChar]
  congr 1
  change (CartierDual.baseChange A R (GG.A n)).symm _ = _
  apply (CartierDual.baseChange A R (GG.A n)).injective
  refine ((CartierDual.baseChange A R (GG.A n)).apply_symm_apply _).trans ?_
  have h1 : PDivGroup.charElem (tateMap GG GG.dual.dual A GG.bidual.hom t) n = WithConv.toConv (t.pt n).toLinearMap :=
    (PDivGroup.charHom_app_muT _ n).symm.trans (PDivGroup.dualChar_app_muT t n)
  rw [h1]
  refine WithConv.ext (TensorProduct.AlgebraTensorModule.ext fun r a => ?_)
  refine (PerfdLat.bcTate_pt R t n r a).trans (Eq.trans ?_ (CartierDual.baseChange_tmul_tmul R 1 r _ a).symm)
  simp [Algebra.smul_def, mul_comm]

theorem omegaMap_hodgeTate (pol : GG ⟶ GG.dual) (h : GG.bidual.hom ≫ dualHom GG GG.dual pol = -pol) (t : GG.Tate) :
    omegaMap _ _ pol (hodgeTate GG t) = -dlog GG (tateMap GG GG.dual A pol t) := by
  rw [PDivGroup.hodgeTate_apply, ← PDivGroup.dlog_tateMap, ← PDivGroup.tateMap_comp, h, map_neg, LinearMap.neg_apply,
    map_neg]

theorem level_ker (R : Type) [CommRing R] [Algebra A R] {M : Type} [AddCommGroup M] [Module A M] (c : M →ₗ[A] GG.omega)
    (hc : IsLevels c) (n : ℕ) (x : R ⊗[A] M) (hx : (GG.omegaBCMap c x).1 n = 0) : ∃ y, x = (p : R) ^ n • y := by
  rw [PDivGroup.omegaBCMap_level, LinearEquiv.map_eq_zero_iff] at hx
  have hex : Function.Exact ((p : A) ^ n • LinearMap.id : M →ₗ[A] M) ((GG.omegaLevel n).comp c) := by
    intro y
    rw [LinearMap.comp_apply, PDivGroup.omegaLevel_apply, hc.2 n y]
    exact ⟨fun ⟨w', hw'⟩ => ⟨w', by simp [hw']⟩, fun ⟨w', hw'⟩ => ⟨w', by simp [← hw']⟩⟩
  have hex' := lTensor_exact R hex (hc.1 n)
  have hx' : LinearMap.lTensor R ((GG.omegaLevel n).comp c) x = 0 := by
    rwa [← LinearMap.baseChange_eq_ltensor]
  obtain ⟨y, hy⟩ := (hex' x).1 hx'
  refine ⟨y, ?_⟩
  rw [← hy, LinearMap.lTensor_smul, LinearMap.lTensor_id, LinearMap.smul_apply,
    LinearMap.id_apply, ← algebraMap_smul R, map_pow, map_natCast]

end Group

theorem toBase_omegaMap {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] (R : Type) [CommRing R] [Algebra A R]
    {G G' : PDivGroup p A} (f : G ⟶ G') (w : G'.omega) : (G.toBase R).omega (omegaMap G G' f w) =
      omegaMap _ _ (PDivGroup.baseChangeMap R f) ((G'.toBase R).omega w) :=
  PDivGroup.SemiHom.omega_naturality _ _ f _ (fun _ _ => rfl) w

theorem eq_sum_dualVec {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {J : Type} [Fintype J]
    (b : Module.Basis J ℤ Dw.La) (x : Dw.La) : x = ∑ j, Dw.EF (b j) x • dualVec b j := by
  refine Dw.unimod.1 (b.ext fun i => ?_)
  rw [← LinearMap.IsAlt.neg Dw.alt, ← LinearMap.IsAlt.neg Dw.alt (b i), map_sum]
  classical
  simp [EF_dualVec, Finsupp.single_apply]

theorem rho_smul {p h o : ℕ} {A : Type} [CommRing A] {π : A} {γ : ℕ → A} {Lie Om : Type} [AddCommGroup Lie] [Module A Lie]
    [AddCommGroup Om] [Module A Om] (C : RChain p A h o π γ Lie Om) (w : Om) : C.ρ (π • w) = 0 := by
  rw [map_smul]
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (C.ρ w)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← hx, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _ (x := π • x)).2,
    Submodule.Quotient.mk_zero]
  exact Submodule.smul_mem_pointwise_smul x.1 π ⊤ trivial

theorem rho_eq_zero_iff {p : ℕ} [Fact p.Prime] {D : PrismData p} {S : CycPerfd p} {G : PDivGroup p S.R}
    {c : ConstTate (eps S) G} {A : Type} [CommRing A] [Algebra A S.R] {h o : ℕ} {e : G.height = h} {π : A} {γ : ℕ → A}
    {Lie Om : Type} [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] {iL : Lie → G.Lie}
    {iO : Om → G.dual.omega} {C : RChain p A h o π γ Lie Om} (hC : IsOf D c e iL iO C)
    (hr : Module.IsReflexive S.R G.dual.omega) (w : Om) : C.ρ w = 0 ↔ iO w ∈ LinearMap.range c.al := by
  have hW := (PerfdLat.FirstLattice.exact_seq p D S G c hr).2.1
  have reg := PerfdLat.FirstLattice.isSMulRegular_of_isReflexive (M := G.dual.omega)
    (PerfdLat.isSMulRegular_zeta_sub_one S 0)
  have h0 : RingChain.toR (G := G) e ((0 : C.L 0) : Fin h → A) = 0 := funext fun i => map_zero (algebraMap A S.R)
  have k := hC.ρ w 0
  rw [Submodule.Quotient.mk_zero, Submodule.Quotient.mk_zero, h0] at k
  rw [k]
  constructor
  · rintro ⟨x, -, hx, hm⟩
    rw [zero_sub, neg_mem_iff] at hm
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hm
    obtain ⟨y, rfl⟩ := (PerfdLat.mem_base S u).1 hu
    rw [map_add, (c.mem_W v).1 (hW hv), add_zero, map_smul] at hx
    exact ⟨y, (reg hx).symm⟩
  · rintro ⟨y, hy⟩
    have hb := (PerfdLat.mem_base S _).2 ⟨y, rfl⟩
    refine ⟨_, PerfdLat.base_le_H D c 0 hb, by rw [map_smul, hy], ?_⟩
    rw [zero_sub, neg_mem_iff]
    exact Submodule.mem_sup_left hb

theorem ker_rho : RingRSt := by
  intro E _ _ _ H Dw p _ D A _ t GG act pol θ ε τ hP n o e b π γ Lie Om _ _ _ _ _ _ cω pr C η hC hL hη hπ w
  have hp : ∀ v, C.ρ ((p : A) • v) = 0 := fun v => by
    obtain ⟨q, hq⟩ := hπ
    rw [hq, mul_smul, rho_smul]
  by_cases hu : IsUnit (p : A)
  · obtain ⟨q, hq⟩ := hu.exists_right_inv
    have hw : w = (p : A) • q • w := by rw [← mul_smul, hq, one_smul]
    exact iff_of_true (hw ▸ hp _) (Submodule.mem_sup_right (hw ▸ Submodule.smul_mem_pointwise_smul _ _ _ trivial))
  obtain ⟨S, _, ec, hec, hε, eL, eO, -, hO, hI⟩ := hC hu
  subst e
  haveI : Module.Finite S.R (GG.baseChange S.R).dual.omega := Module.Finite.equiv eO
  haveI : Module.Projective S.R (GG.baseChange S.R).dual.omega := Module.Projective.of_equiv eO
  have hr : Module.IsReflexive S.R (GG.baseChange S.R).dual.omega := inferInstance
  have mp := RingChain.Exist.modIso_of_dvd ec hec (dvd_refl (p : A))
  set c := (ct hP rfl b).baseChange S.R hε with hc
  let b' := b.reindex (finCongr (rfl : GG.height = GG.height).symm)
  let P := omegaMap _ _ (polBC pol S.R)
  let Φ := GG.omegaBCMap (R' := S.R) cω
  have hΦ1 : ∀ w, Φ (1 ⊗ₜ w) = (GG.toBase S.R).omega (cω w) := fun w =>
    (LinearMap.liftBaseChange_tmul _ _ _ _).trans (one_smul _ _)
  have hΦ : ∀ x, Φ x = P (eO x) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r w =>
      have : r ⊗ₜ[A] w = r • ((1 : S.R) ⊗ₜ[A] w) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, map_smul, map_smul, hΦ1, hO]
  let F : Dw.La →+ (GG.baseChange S.R).omega := (GG.toBase S.R).omega.toAddMonoidHom.comp
    ((dlog GG).comp ((tateMap GG GG.dual A pol.hom).toAddMonoidHom.comp τ))
  have hF : ∀ x, P (hodgeTate _ (bcTate S.R (τ x))) = -F x := fun x => by
    change omegaMap _ _ (_ ≫ _) _ = _
    rw [PDivGroup.omegaMap_comp, LinearMap.comp_apply, hodgeTate_bcTate, ← toBase_omegaMap,
      omegaMap_hodgeTate _ hP.skew, map_neg]
    rfl
  have hal : ∀ y, P (c.al y) = -∑ i, y i • F (b' i) := fun y => by
    rw [c.al_apply, map_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, ← smul_neg, ← hF]; rfl
  let lv := (GG.baseChange S.R).omegaLevel 1
  have hlv : ∀ j, lv (Φ (1 ⊗ₜ η j)) = lv (F (dualVec b' j)) := fun j => by
    rw [hΦ1]
    exact congrArg ((GG.toBase S.R).app 1).cot (hη j)
  have hk : ∀ x, lv (Φ x) = 0 → ∃ y, x = (p : S.R) • y := fun x hx => by
    simpa using level_ker S.R cω hL 1 x hx
  have hlp : ∀ v, (p : S.R) • lv v = 0 := fun v => by
    simpa using (GG.baseChange S.R).pow_smul_cot 1 (lv v)
  constructor
  · intro hw
    obtain ⟨y, hy⟩ := (rho_eq_zero_iff hI hr w).1 hw
    choose a ha using fun j => mp.1 (-∑ i, y i * (Dw.EF (b' j) (b' i) : ℤ))
    have h1 : lv (Φ (1 ⊗ₜ w)) = ∑ j, (-∑ i, y i * (Dw.EF (b' j) (b' i) : ℤ)) • lv (F (dualVec b' j)) := by
      rw [hΦ, ← hy, hal, map_neg, map_sum]
      simp only [neg_smul, Finset.sum_smul, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
      conv_lhs => rw [eq_sum_dualVec b' (b' i)]
      simp only [map_sum, map_zsmul, map_smul, Finset.smul_sum, mul_smul, Int.cast_smul_eq_zsmul]
    have h2 : lv (Φ (1 ⊗ₜ (w - ∑ j, a j • η j))) = 0 := by
      rw [TensorProduct.tmul_sub, map_sub, map_sub, h1, TensorProduct.tmul_sum, map_sum, map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun j _ => ?_
      obtain ⟨q, hq⟩ := ha j
      rw [TensorProduct.tmul_smul, ← algebraMap_smul S.R (a j), map_smul, map_smul, hlv, ← sub_smul, hq, map_natCast, mul_comm,
        mul_smul, hlp, smul_zero]
    obtain ⟨z, hz⟩ := hk _ h2
    have h3 := (RingChain.modIso_tensor_mod A S.R p p (map_natCast _ _) mp Om _ (LinearEquiv.refl _ _)).2
      (w - ∑ j, a j • η j) (by rw [LinearEquiv.refl_apply, hz]; exact Submodule.smul_mem_pointwise_smul _ _ _ trivial)
    rw [← add_sub_cancel (∑ j, a j • η j) w]
    exact Submodule.add_mem_sup
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)) h3
  · intro hw
    refine (sup_le (Submodule.span_le.2 ?_) fun v hv => ?_ : _ ≤ LinearMap.ker C.ρ) hw
    · rintro _ ⟨j, rfl⟩
      refine (rho_eq_zero_iff hI hr _).2 ?_
      let y : Fin GG.height → S.R := fun i => -(b'.repr (dualVec b' j) i : ℤ)
      have h1 : P (c.al y) = F (dualVec b' j) := by
        rw [hal]
        conv_rhs => rw [← b'.sum_repr (dualVec b' j)]
        simp only [y, neg_smul, Finset.sum_neg_distrib, neg_neg, map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
      obtain ⟨z, hz⟩ := hk (1 ⊗ₜ η j - eO.symm (c.al y)) (by
        rw [map_sub, map_sub, hlv, hΦ, LinearEquiv.apply_symm_apply, h1, sub_self])
      have h2 : eO (1 ⊗ₜ η j) = c.al y + (p : S.R) • eO z := by
        rw [← map_smul, ← hz, map_sub, LinearEquiv.apply_symm_apply, add_sub_cancel]
      obtain ⟨q, hq⟩ := PerfdLat.zeta_one_sub_one_dvd S
      change eO _ ∈ _
      rw [h2, hq, mul_smul]
      exact add_mem ⟨y, rfl⟩ ((PerfdLat.FirstLattice.exact_seq p D S _ c hr).2.2.2.2.1 _)
    · obtain ⟨v, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv
      exact hp v

end GlobalTheory.ChainPts.SysB.KerRho

end
