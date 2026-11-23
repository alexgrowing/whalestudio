import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.SplitW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CLocConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWtBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PartU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AbsoluteIrreducibleRankFour
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatFrobT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnifVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreUp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreEig
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.LgAway

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.GalN.V
def UpperTheory.V.Z.Desc.W.StrongEquivalenceHida {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ} (ι : Qbar l ≃+* ℂ) (σ : Submodule ℂ (UA L n → ℂ))
    (ρ : G L Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ (u : s.St) (τ : SmIrr (GLw n (s.w u))), ((l : ℕ) : 𝓞 L) ∉ (s.w u).asIdeal →
    IsCompAlong σ (locU n (s.w u)) ((cLoc (s.w u)).comp (locU n (s.w u)).subtype) τ.ρ → ∀ rc, _root_.UpperTheory.Zero.LLC.IsRecT (s.hw u) rc →
      IsWDOf ι ρ (rc (algNorm τ))
open UpperTheory.V.Z.Desc.W
namespace UpperTheory.V.Hi.Up
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} {Q : QData V} {c : Coef l} {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r}
private theorem split_w {v : Plc (Lp L)} (hv : v ∈ s.S) : IsSplitAt (s.w v) :=
  UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω (s.A v) v (s.hA v) (s.split v hv) _ (under_w v)
private theorem types (hn : 1 ≤ n) (x : B.Pt) {σ : Submodule ℂ (UA L n → ℂ)} {ρ : G L Ω →* GL (Fin n) (Qbar l)} (hσ : IsAutRepU σ)
    (hs : Formalism.MainNotions.N.IsSSRep ρ) (hx : x.IsRep ρ) (hSt : _root_.UpperTheory.V.Z.Desc.W.StrongEquivalenceHida s ι σ ρ)
    (t : Fin n → V.frame.G₀ →* c.Oˣ) (ht : r.IsTeich t) (u : s.St) :
    ∃ τ : SmIrr (GLw n (s.w u)), IsCompAlong σ (locU n (s.w u)) ((cLoc (s.w u)).comp (locU n (s.w u)).subtype) τ.ρ ∧
      ∀ rc, _root_.UpperTheory.Zero.LLC.IsRecT (s.hw u) rc → IsTypeWD (s.hw u) (fun i => W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l)))
        ((t i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype))) (rc (algNorm τ)) := by
  have hw : IsSplitAt (s.w u) := split_w (Or.inr (Or.inl u.2))
  have hu : ((l : ℕ) : 𝓞 L) ∉ (s.w u).asIdeal := fun h => s.St_l u u.2 (by
    rw [← under_w (s := s) u]
    change algebraMap _ (𝓞 L) _ ∈ (s.w u).asIdeal
    rwa [map_natCast])
  obtain ⟨τ, hτ⟩ := comp_ex hσ hw
  obtain ⟨P, hP⟩ := diag_pt x V.pr ρ hx hn hs t ht u (Ine (F := L) (s.A u)) fun g hg => ⟨g, hg, rfl⟩
  suffices hop : ∀ i, IsOpen ((W.pushCh (algebraMap c.O (Qbar l)) ((t i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype))).ker :
      Set (Ine (F := L) (s.A u))) from ⟨τ, hτ, fun rc hrc => wd_type hu _ hop P hP (hSt u τ hu hτ rc hrc)⟩
  intro i
  obtain ⟨-, hfin, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine Subgroup.isOpen_mono (H₁ := (r.chib i).ker.comap (V.pr.comp (Ine (F := L) (s.A u)).subtype)) (fun g hg => ?_)
    ((r.chib_open i).preimage ((V.pr_cont W.continuous_resP).comp continuous_subtype_val))
  have h1 : residue c.O (t i (V.pr g)) = 1 := (ht i _).1.trans (congrArg Units.val hg)
  have h2 : ((t i (V.pr g) : c.O)) ^ (Nat.card (ResidueField c.O) - 1) = 1 :=
    (Units.val_pow_eq_pow_val _ _).symm.trans (congrArg Units.val (ht i _).2)
  have h3 := geom_sum_mul ((t i (V.pr g) : c.O)) (Nat.card (ResidueField c.O) - 1)
  rw [h2, sub_self, mul_eq_zero] at h3
  have h4 : t i (V.pr g) = 1 := Units.ext (sub_eq_zero.1 (h3.resolve_left fun h5 => by
    have h6 := congrArg (residue c.O) h5
    simp only [map_sum, map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_one, map_zero] at h6
    rw [Nat.cast_pred Nat.card_pos] at h6
    letI := Fintype.ofFinite (ResidueField c.O)
    simp [Nat.card_eq_fintype_card] at h6))
  exact (congrArg (Units.map (algebraMap c.O (Qbar l) : c.O →* Qbar l)) h4).trans (map_one _)
private theorem chi_map {A A' H : Type} [CommRing A] [CommRing A'] [Group H] (D : W.GDet n A H) (f : A →+* A') (g : H) :
    (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  rw [← (AlgebraTools.Det.mapApi D f).1, MonoidAlgebra.mapRingHom_single, map_one]
end UpperTheory.V.Hi.Up
set_option maxHeartbeats 1000000 in
open UpperTheory.V.Hi.Up in
theorem UpperTheory.V.Z.Desc.W.upU_w_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → ∀ (x : B.Pt) (h : s.Wt n) (lam : Wt L l n), x.Arith h → WtOf h lam → ∀ (σ : Submodule ℂ (UA L n → ℂ)) (ρ : G L Ω →* GL (Fin n) (Qbar l)), IsAutRepU σ → Continuous ρ → Formalism.MainNotions.N.IsSSRep ρ → x.IsRep ρ → SphEq ι σ ρ → (∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual) → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsUnramU σ w) → (∃ τ : SmIrr (GLw n (s.w s.v0)), IsCompAlong σ (locU n (s.w s.v0)) ((cLoc (s.w s.v0)).comp (locU n (s.w s.v0)).subtype) τ.ρ ∧ fixd τ.ρ (Kc _ n 1) ≠ ⊥) → (∀ v : V.frame.Vl, ∃ (τ : SmIrr (GLw n (s.w v.1))) (ω : Fin n → ((s.w v.1).adicCompletion L)ˣ →* ℂˣ), IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) τ.ρ ∧ Nonempty (τ.ρ.Equiv (PS ω)) ∧ ∀ i, OrdChar ι (artOf (s.hw v.1)) (ω i) (htW lam i) (x.psi v i)) → _root_.UpperTheory.V.Z.Desc.W.StrongEquivalenceHida s ι σ ρ → J ≤ RingHom.ker x := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K hS J hJ x h lam hx hlam σ ρ hσ hρ hss hrep hloc hwt hunr h0 hord hSt
  have hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis := hP.litN
  have hA := _root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V Q c R.m R.τ₀
  have har := ((_root_.UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight hN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h hx.1).2 lam hlam x).1.1 hx
  obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c _ hA Λ.Λ R.θ R.isWt ι _ lam har
  obtain ⟨e, he⟩ := hsp.alg
  obtain ⟨Y, -, -, hY, hYl⟩ := _root_.UpperTheory.V.Z.Desc.P.partU_alt hP l L Ω s n hn V Q c r ι R.m R.τ₀ R.type lam d e ξ he σ hσ
    (_root_.UpperTheory.V.Hi.nonempty_unitary_hecke_parts hP l L Ω s n hn V Q c r ι R.m R.τ₀ R.type lam d e ξ he σ hσ hwt hunr h0 (types hn x hσ hss hrep hSt))
  choose τ ω hτ hω ho using hord
  have hfr : ∀ w ∈ (hset Q R.τ₀).Wp, ∀ (A : ValuationSubring Ω) (g : G L Ω), IsPlaceOver A w → IsFrob A (normV w) g →
      (ρ g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = (Y.r (V.pr g⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro w hw A g hAw hg
    obtain ⟨π, hπ⟩ := comp_ex hσ hw.2
    have hl := hA.Wp_away w hw
    obtain ⟨z, hz, h0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.SphBC.isSpherical_of_isCompAlong_split hσ hw.2 π.ρ hπ (hunr w hw.1))
    obtain ⟨b, hb⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results hP.toClassicalTheorems L n w π).1 ⟨z, h0, GlobalTheory.LGrp.mem_fixed.1 hz⟩
    have h1 := (hloc w hw.2 hl π b hπ hb A hAw).2 g hg
    have h2 := (_root_.UpperTheory.V.Z.Desc.W.satFrobT_alt hP.toClassicalTheorems L Ω l ι n _ (Y.cont.comp (V.pr_cont W.continuous_resP)) w hl π b hb
      (_root_.UpperTheory.V.Z.Desc.W.lgAway' (hYl w hw.2 π hπ) hl) A hAw).2 g hg
    exact Polynomial.map_injective ι.toRingHom ι.injective (h1.trans h2.symm)
  have hD : B.u.D.map (x : B.B →+* Qbar l) = W.GDet.ofRep (W.mat Y.r) := by
    refine AlgebraTools.Det.extDense _ _ _ hA.dense (fun i _ => ?_)
      (fun i _ => AlgebraTools.Det.repCont _ (Units.continuous_val.comp Y.cont) i) ?_
    · simp only [(AlgebraTools.Det.mapApi B.u.D (x : B.B →+* Qbar l)).2.2.1]
      exact pt_cont x (B.u.cont i)
    · rintro _ ⟨w, hw, A, g, hAw, hg, rfl⟩
      exact (chi_map _ _ _).trans ((chi_pt x V.pr ρ hrep _).trans
        ((hfr w hw A g hAw hg).trans ((AlgebraTools.Det.repApi (W.mat Y.r)).2.1 _).symm))
  have hsph : ∀ (w : (hset Q R.τ₀).Wp) (j : Fin n),
      ‖ι.symm (Y.a w (j + 1)) - algebraMap c.O (Qbar l) (R.a (.inl (w, j)))‖ < 1 := by
    intro w j
    have hAw := isPlaceOver_placeOf Ω w.1
    have hg := deg_eq_one_iff.1 (deg_frob (h := hAw))
    have hq : IsUnit ((normV w.1 : ℕ) : B.B) := by
      have := ((cycZ L Ω l (frob hAw)).isUnit.map (algebraMap ℤ_[l] c.O)).map (algebraMap c.O B.B)
      rwa [cycZ_of_isFrob (hA.Wp_away _ w.2) hAw hg, map_natCast, map_natCast] at this
    have hq' := pt_unit x hq.unit
    rw [IsUnit.unit_spec, map_natCast] at hq'
    have := hecke_cong (algebraMap c.O (Qbar l)) ι hq' _ (Y.a w)
      (fun j => if h : 0 < j ∧ j - 1 < n then R.a (.inl (w, ⟨j - 1, h.2⟩)) else 1)
      ((congrArg _ (hfr _ w.2 _ _ hAw hg)).trans (Y.frob w _ _ hAw hg))
      (chi_cong x V.pr ρ hrep _ _ (by
        refine (R.res.frob w _ _ hAw hg).trans ?_
        rw [hecke_map]
        congr 1
        funext j
        split_ifs <;> simp)) (j + 1) j.2
    rwa [dif_pos ⟨Nat.succ_pos _, j.2⟩] at this
  have hfin := fun v i => _root_.UpperTheory.V.Hi.Up.ordChar_unit_mul_finite_component_eq_one R x hN hA v i (ho v i)
  have up : ∀ [Fact (CommOn (R.M K) ((hset Q R.τ₀).op Λ.Λ))], _ :=
    _root_.UpperTheory.V.Hi.coreUp_alt hN L Ω l n c _ hA Λ.Λ R.θ R.isWt ι _ lam d ξ c0 sp hsp Y K
      (fun q => absurd (hS ▸ Q.range ▸ Or.inr ⟨q, rfl⟩) (Q.notS q)) ω
      (fun v => (UpperTheory.building_component_uniqueness L n σ hσ _ (split_w (Or.inl v.2)) _ _ _ _ (hY v) (hτ v)).elim fun a => (hω v).elim fun b =>
        ⟨a.trans b⟩) hfin R.a hsph (fun v => _root_.UpperTheory.V.Hi.Up.norm_lowVal_inv_mul_psEig_eq_one_and_norm_sub_lt_one R x hN hA v (ho v))
  rcases hJ with ⟨hb, -⟩ | ⟨hc, hco, f, -, hmap, -, -, rfl⟩
  · haveI := Fact.mk ((hiComm L Ω l n c _ hA Λ.Λ R.θ R.isWt K).2.2.2 R.a).1
    exact absurd hb up.1
  obtain ⟨-, y, hy, hy1, hy2⟩ := up
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 Y.ne
  obtain ⟨k1, k2⟩ := _root_.UpperTheory.V.Hi.core_eigen_of_weight_char_hecke_level hN L Ω l n c _ hA Λ.Λ R.θ R.isWt ι R.a K _ _ hmap y lam d ξ Y F hF hF0 fun w j => by
    rw [hy1]
    exact Y.sph w _ F hF
  obtain ⟨hcp, hfn, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero Fact.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  have key : x = y.comp f := by
    refine pt_ext _ x _ (UpperTheory.V.CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B) ?_
    rintro _ (⟨i, g, -, -, rfl⟩ | ⟨v, i, g, rfl⟩)
    · have e1 := (AlgebraTools.Det.mapApi B.u.D (x : B.B →+* Qbar l)).2.2.1 i g
      have e2 := (AlgebraTools.Det.mapApi (B.u.D.map f.toRingHom) y.toRingHom).2.2.1 i g
      rw [(AlgebraTools.Det.mapApi B.u.D f.toRingHom).2.2.1 i g] at e2
      rw [hD] at e1
      exact e1.symm.trans ((congrArg (fun D : W.GDet n (Qbar l) V.frame.G₀ => D.lam i (MonoidAlgebra.single g 1)) k1).symm.trans e2)
    · exact congrArg Units.val (DFunLike.congr_fun (ord_uniq (ho v i)
        (k2 v (ω v) (fun i => (ho v i).smooth) (by rw [hy]; exact hfin v) (hy2 v) i)) g)
  intro b hb
  rw [RingHom.mem_ker] at hb ⊢
  rw [key, AlgHom.comp_apply, hb, map_zero]
end
