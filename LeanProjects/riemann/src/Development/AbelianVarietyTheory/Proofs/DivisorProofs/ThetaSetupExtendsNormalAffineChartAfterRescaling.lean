import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoThrough
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaExtend
open GlobalTheory.ThetaPtMove GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift GlobalTheory.ThetaReal GlobalTheory.UnivBasisMove GlobalTheory.ThetaGeom

set_option maxHeartbeats 2000000 in

theorem exists_real_rechart (hL : Laws) {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (S : ThetaSys o Ω) (ρ : S.Real) (R' : Subalgebra o Ω) [IsIntegrallyClosed R'] (fg : R'.FG)
    (frac : ∀ x : Ω, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (P' : PolAV (Sp R')) (P₀ : PolAV (Sp Ω))
    (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ P'.A.left) (pt' : S.Gam → (baseOver (Sp R') ⟶ P'.A))
    (th : LB.Sec (LPow P'.A P'.L 1 (baseOver (Sp R'))))
    (b : Fin (S.N ^ P'.g) → SecM P'.A P'.L (S.N : ℕ) (baseOver (Sp R')))
    (gp : IsGrpPullback P₀.A ρ.P.A (spMap S.R.val.toRingHom) a)
    (gp' : IsGrpPullback P₀.A P'.A (spMap R'.val.toRingHom) a')
    (lb : LBIso P₀.L (ρ.P.L.pull a)) (lb' : LBIso P₀.L (P'.L.pull a')) (hg : P'.g = S.g) (hS : HypS P'.A P'.L)
    (hadd : ∀ x y, pt' (x + y) = pt' x * pt' y)
    (hbij : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R') (z : Over.mk x ⟶ P'.A), z ^ (S.r * S.N) = 1 →
      ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R')) ≫ pt' c = z)
    (hweil : ∀ x y (c : R'ˣ), (c : R') = algebraMap o R' (S.ζ ^ (S.r * S.N * (eStd S.g _ x y).val)) →
      WeilIs P'.A P'.L (S.r * S.N : ℕ) (pt' x) (pt' y) (unitOn c))
    (hw0 : ∀ x, ∃ w0 : Sp Ω ⟶ P₀.A.left, w0 ≫ a = spMap S.R.val.toRingHom ≫ (ρ.pt x).left ∧
      w0 ≫ a' = spMap R'.val.toRingHom ≫ (pt' x).left)
    (hth : UnivBasis P' 1 (fun _ : Fin 1 => SecM.ofSec P'.A th)) (hb : UnivBasis P' (S.N : ℕ) b)
    (Q : (P : PolAV (Sp R')) → (S.Gam → (baseOver (Sp R') ⟶ P.A)) → Prop) (hQ : Q P' pt') :
    ∃ (c₀ : Ω) (hc : c₀ ≠ 0) (hth : ∀ x, c₀ * S.th x ∈ R') (hev : ∀ x k, c₀ * S.ev x k ∈ R')
      (ρ' : (S.rechart c₀ hc R' fg frac hth hev).Real), Q ρ'.P ρ'.pt ∧ ρ'.i₀ = ρ.i₀ := by
  classical
  haveI := isNoetherian_of_fg fg
  haveI : IsAffine (baseOver (Sp R')).left := inferInstanceAs (IsAffine (Sp R'))
  haveI : IsAffine (baseOver (Sp Ω)).left := inferInstanceAs (IsAffine (Sp Ω))
  haveI : IsIntegral (baseOver (Sp R')).left := inferInstanceAs (IsIntegral (Sp R'))
  haveI : GlobalTheory.IsNormalScheme (baseOver (Sp R')).left := inferInstanceAs (GlobalTheory.IsNormalScheme (Sp R'))
  haveI : Subsingleton (baseOver (Sp Ω)).left := inferInstanceAs (Subsingleton (Sp Ω))
  haveI : Nontrivial Γ((baseOver (Sp R')).left, ⊤) := (fn_injective (R := R')).nontrivial
  haveI := P₀.isAb.comm
  have hL₁ := ρ.P.isLB
  have hL' := P'.isLB
  have hL₀ := P₀.isLB
  let τ : (baseOver (Sp Ω)).left ⟶ (baseOver (Sp S.R)).left := spMap S.R.val.toRingHom
  let τ' : (baseOver (Sp Ω)).left ⟶ (baseOver (Sp R')).left := spMap R'.val.toRingHom
  have hτ : τ ≫ (baseOver (Sp S.R)).hom = (baseOver (Sp Ω)).hom ≫ spMap S.R.val.toRingHom :=
    (Category.comp_id _).trans (Category.id_comp _).symm
  have hτ' : τ' ≫ (baseOver (Sp R')).hom = (baseOver (Sp Ω)).hom ≫ spMap R'.val.toRingHom :=
    (Category.comp_id _).trans (Category.id_comp _).symm
  have tf : ∀ x : S.R, τ.appTop.hom (fn x) = fn (x : Ω) := fun x => spMap_appTop_fn _ x
  have tf' : ∀ x : R', τ'.appTop.hom (fn x) = fn (x : Ω) := fun x => spMap_appTop_fn _ x
  have fs : ∀ v : Γ((baseOver (Sp R')).left, ⊤), ∃ x : R', fn x = v := fun v => ⟨_, fn_hom v⟩
  have fs₀ : ∀ v : Γ((baseOver (Sp Ω)).left, ⊤), ∃ x : Ω, fn x = v := fun v => ⟨_, fn_hom v⟩
  have fm : ∀ x y : Ω, fn (x * y) = fn x * fn y := fun x y => map_mul _ x y
  have tinj : Function.Injective τ'.appTop.hom := fun v v' e => by
    obtain ⟨x, rfl⟩ := fs v
    obtain ⟨y, rfl⟩ := fs v'
    rw [tf', tf'] at e
    exact congrArg fn (Subtype.ext (fn_injective e))
  have frac' : ∀ x : Ω, ∃ a b : R', x = R'.val.toRingHom a / R'.val.toRingHom b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := frac x
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩

  have hN := ρ.N_eq
  have hNo : Odd S.N := hN ▸ ρ.n_odd.pow.pow
  have hm1 : 1 ≤ ρ.n ^ ρ.k := Nat.one_le_pow _ _ ρ.n_prime.pos
  have hM : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  let κ' : o →+* Γ((baseOver (Sp R')).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom.comp (algebraMap o R')
  have uN : IsUnit (S.N : Γ(Sp R', ⊤)) := by
    have := S.unit.map κ'
    rw [map_natCast, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_right this
  have um : IsUnit ((ρ.n ^ ρ.k : ℕ) : Γ(Sp R', ⊤)) := by
    rw [hN, Nat.cast_pow, isUnit_pow_iff two_ne_zero] at uN
    exact uN

  choose w0 hw₁ hw₂ using hw0
  have hw₃ : ∀ x, w0 x ≫ P₀.A.hom = 𝟙 _ := fun x => eq_id_of_comp _ frac' _ (by
    rw [Category.assoc, ← gp'.1.w, ← Category.assoc, hw₂, Category.assoc, Over.w (pt' x)]
    exact Category.comp_id _)
  let pt₀ : S.Gam → (baseOver (Sp Ω) ⟶ P₀.A) := fun x => Over.homMk (w0 x) (hw₃ x)
  have hx : ∀ x, (pt₀ x).left ≫ a = τ ≫ (ρ.pt x).left := hw₁
  have hx' : ∀ x, (pt₀ x).left ≫ a' = τ' ≫ (pt' x).left := hw₂
  obtain ⟨h0, hsm⟩ := pt_nsmul pt' hadd
  have tors : ∀ x, pt' (S.r • x) ^ S.N = 1 := fun x => by
    rw [← hsm, smul_smul, mul_comm S.N S.r, nsmul_self, h0]
  have tors₀ : ∀ x, pt₀ (S.r • x) ^ S.N = 1 := fun x => FrameMove.pow_eq_one_of gp' (hx' _) (tors x)

  obtain ⟨w, hw⟩ := lb
  obtain ⟨rig₀, fr₀, hrig₀, vrig, hfr₀⟩ := exists_frames_move_through gp hw ρ.rig_gen hx ρ.fr_tors
  obtain ⟨rig', hrig'⟩ := P'.rigid
  obtain ⟨w', hw', vrig'⟩ := exists_iso_through gp' lb' hrig' hrig₀
  let y : (baseOver (Sp Ω)).left := closedPoint Ω
  haveI : IsDomain ((baseOver (Sp Ω)).left.presheaf.stalk y) := inferInstanceAs (IsDomain ((Sp Ω).presheaf.stalk y))
  obtain ⟨g₁, g₂⟩ := generic_spMap R'.val.toRingHom Subtype.val_injective frac' y
  choose fr' hfr' vfr' using fun x => exists_frame_up hL (h := τ') y g₁ g₂ gp' hw' hrig' vrig' (hx' x) (by omega)
    (by rw [← hsm, nsmul_self, h0]) (hfr₀ x).1

  obtain ⟨th₀, r₁⟩ := exists_secRel gp τ hτ hw hL₁ hL₀ ρ.th₁
  obtain ⟨th₀', r₁'⟩ := exists_secRel gp' τ' hτ' hw' hL' hL₀ th
  obtain ⟨dd, hdd⟩ : ∃ dd : Ω, SecM.ofSec P₀.A th₀ = fn dd • SecM.ofSec P₀.A th₀' := by
    obtain ⟨c, hc⟩ := (univBasis_of_rel (hp := gp') (hτ := hτ') hw' hth (b := fun _ => SecM.ofSec P₀.A th₀')
      fun _ => r₁').exists_basis
    obtain ⟨dd, e⟩ := fs₀ (c.equivFun (SecM.ofSec P₀.A th₀) 0)
    refine ⟨dd, ?_⟩
    rw [e, ← hc 0]
    exact (c.sum_equivFun _).symm.trans (Fin.sum_univ_one _)
  choose v hv using fun x => ThetaPtExist.exists_isValueAt hL' th (pt' x) (fr' x) (hfr' x).2.1
  choose v₁ hv₁ using fun x => fs (v x)
  have ev₁ : ∀ x, S.th x = dd * v₁ x := fun x => by
    have h₁ := isValueAt_move gp τ hτ hL₁ hL₀ (hx x).symm (hfr₀ x).2 r₁ (ρ.th_val x)
    have h₂ := isValueAt_move gp' τ' hτ' hL' hL₀ (hx' x).symm (vfr' x) r₁' (hv x)
    have := value_smul hL₀ h₂ h₁ hdd
    rw [← hv₁, tf, tf', ← fm] at this
    exact fn_injective this
  have hdd0 : dd ≠ 0 := by
    obtain ⟨x, hx⟩ := S.th_ne
    exact fun h => hx (by rw [ev₁, h, zero_mul])
  have ev₂ : ∀ x, dd⁻¹ * S.th x = v₁ x := fun x => by rw [ev₁, inv_mul_cancel_left₀ hdd0]
  have hdd' : SecM.ofSec P₀.A th₀' = fn dd⁻¹ • SecM.ofSec P₀.A th₀ := by
    rw [hdd, smul_smul, ← fm, inv_mul_cancel₀ hdd0]
    exact ((congrArg (· • _) (map_one _)).trans (one_smul _ _)).symm

  obtain ⟨α', hα', nα'⟩ := GlobalTheory.T.exists_normalised_mulPull_iso_origin hL _ P' rig' hrig' (ρ.n ^ ρ.k) S.N hN (baseOver (Sp R'))
  obtain ⟨α₀, hα₀, vα⟩ := exists_genThrough₂ gp τ hτ hw hL₁ hL₀ (psi_pow gp τ hτ (ρ.n ^ ρ.k)) ρ.α ρ.α_gen
  obtain ⟨α₀', hα₀', vα'⟩ := exists_genThrough₂ gp' τ' hτ' hw' hL' hL₀ (psi_pow gp' τ' hτ' (ρ.n ^ ρ.k)) α' hα'
  obtain rfl : α₀ = α₀' := gen_eq_of_section hL₀ (fst _ P₀.A).left (ptSecT P₀.A 1).left (ptSecT_fst _)
    (SymLiftOdd.surj_fst hL.globalFns P₀.isAb _) hα₀ hα₀' fun Z r z J hJ =>
      ((val_pull hJ _ _ r).symm.trans (val_corr hJ (norm_move gp τ hτ hL₁ hL₀ vrig vα ρ.α_norm) r)).trans
        ((val_pull hJ _ _ r).symm.trans (val_corr hJ (norm_move gp' τ' hτ' hL' hL₀ vrig' vα' nα') r)).symm
  obtain ⟨s₁, hs₁⟩ := VVRank.exists_isTwistPull P'.A (ψ := mulT P'.A (baseOver (Sp R')) (ρ.n ^ ρ.k))
    (hm := lift_snd _ _) (b := 1) hL' hα' th
  choose s₀ r₂ using fun i => exists_secRel gp τ hτ hw hL₁ hL₀ (ρ.s i)
  obtain ⟨t₀, r₂'⟩ := exists_secRel gp' τ' hτ' hw' hL' hL₀ s₁
  have ht₀ : SecM.ofSec P₀.A t₀ = fn dd⁻¹ • SecM.ofSec P₀.A (s₀ ρ.i₀) := twistPull_smul (b := 1) hL₀
    (isTwistPull_move gp τ hτ hL₁ hL₀ (psi_pow gp τ hτ _) hα₀ vα r₁ (r₂ ρ.i₀) ρ.s_zero)
    (isTwistPull_move gp' τ' hτ' hL' hL₀ (psi_pow gp' τ' hτ' _) hα₀ vα' r₁' r₂' hs₁) hdd'

  choose U' hU' using fun x => GlobalTheory.T.exists_symLift_of_pow_eq_one hL _ P' S.N hNo uN _ _ (tors x)
  choose U₀ hU₀ aU₀ using fun x => symLift_move gp τ hτ hw hL₁ hL₀ (hx (S.r • x)).symm (tors₀ x) (ρ.U_sym x)
  choose U₀' hU₀' aU₀' using fun x => symLift_move gp' τ' hτ' hw' hL' hL₀ (hx' (S.r • x)).symm (tors₀ x) (hU' x)
  obtain ⟨u₁, hu₁, -⟩ := thetaGrp_acts_linearly hL.globalFns _ ρ.P S.N (baseOver (Sp S.R))
  obtain ⟨u₀, hu₀, -⟩ := thetaGrp_acts_linearly hL.globalFns _ P₀ S.N (baseOver (Sp Ω))
  obtain ⟨u', hu', -⟩ := thetaGrp_acts_linearly hL.globalFns _ P' S.N (baseOver (Sp R'))
  have act : ∀ x {s σ}, Rel gp' τ' hτ' w' s σ → Rel gp' τ' hτ' w' (u₀ (U₀ x) s) (u' (U' x) σ) := fun x s σ h => by
    obtain ⟨t, ht⟩ := exists_rel gp' τ' hτ' hw' hL' hL₀ (u' (U' x) σ)
    have e : u₀ (U₀ x) s = t := (hu₀ _ _ _).1 (isActOf_congr hL.globalFns P₀.isAb hL₀ hNo (hU₀' x) (hU₀ x)
      (aU₀' x (SecM.toSec _ σ) (SecM.toSec _ (u' (U' x) σ)) (SecM.toSec _ s) (SecM.toSec _ t) h ht ((hu' _ _ _).2 rfl)))
    exact e ▸ ht
  have mat : ∀ x i, u₀ (U₀ x) (SecM.ofSec _ (s₀ i)) =
      ∑ l, τ'.appTop.hom (κ' (S.ρ x l i)) • SecM.ofSec _ (s₀ l) := fun x i => by
    have a₀ : IsActOf ρ.P.A ρ.P.L S.N (ρ.U x) (ρ.s i) (SecM.toSec _ (u₁ (ρ.U x) (SecM.ofSec _ (ρ.s i)))) :=
      (hu₁ _ _ _).2 rfl
    let c : S.J → Γ((baseOver (Sp S.R)).left, ⊤) := fun l => fn (algebraMap o S.R (S.ρ x l i))
    have a₁ := aU₀ x _ _ _ (SecM.toSec _ (∑ l, τ.appTop.hom (c l) • SecM.ofSec _ (s₀ l))) (r₂ i)
      (secRel_comb gp τ hτ c r₂ rfl ((comb_iff _ _ _).1 (ρ.U_act x i _ a₀))) a₀
    exact ((hu₀ _ _ _).1 a₁).trans (Finset.sum_congr rfl fun l _ => congrArg (· • _) ((tf _).trans (tf' (algebraMap o R' (S.ρ x l i))).symm))
  have r₃ : Rel gp' τ' hτ' w' (fn dd⁻¹ • SecM.ofSec P₀.A (s₀ ρ.i₀)) (SecM.ofSec _ s₁) := ht₀ ▸ r₂'
  have ex : ∀ i, ∃ s', Rel gp' τ' hτ' w' (fn dd⁻¹ • SecM.ofSec P₀.A (s₀ i)) s' := fun i => by
    obtain ⟨x, e, he⟩ := ρ.orbit i
    have hq : (S.r * S.N) ^ 2 - 1 + 1 = (S.r * S.N) ^ 2 := Nat.sub_add_cancel (Nat.one_le_pow _ _ hM)
    have e₁ : (S.ζ ^ e) ^ ((S.r * S.N) ^ 2 - 1) * S.ζ ^ e = 1 := by
      rw [← pow_succ, hq, ← pow_mul, mul_comm e, pow_mul, S.prim.pow_eq_one, one_pow]
    have h := (act x r₃).smul (κ' ((S.ζ ^ e) ^ ((S.r * S.N) ^ 2 - 1)))
    rw [map_smul, mat, Finset.sum_eq_single i (fun l _ hl => by rw [he, if_neg hl, map_zero, map_zero, zero_smul])
      (fun h => (h (Finset.mem_univ _)).elim), he, if_pos rfl, smul_comm, smul_smul (τ'.appTop.hom _), ← map_mul,
      ← map_mul, e₁, map_one, map_one, one_smul] at h
    exact ⟨_, h⟩
  choose s' hs' using ex
  have e₀ : s' ρ.i₀ = SecM.ofSec _ s₁ := rel_inj hw' hb tinj (hs' _) r₃
  have mat' : ∀ x i, u' (U' x) (s' i) = ∑ l, κ' (S.ρ x l i) • s' l := fun x i => by
    refine rel_inj hw' hb tinj (act x (hs' i)) ?_
    have h := rel_sum (fun l => κ' (S.ρ x l i)) hs'
    rw [map_smul, mat, Finset.smul_sum]
    simpa only [smul_comm (fn dd⁻¹)] using h
  have hspan := GlobalTheory.T.span_translates_multiplicationPullback_theta hL _ P' (ρ.n ^ ρ.k) S.N hN hm1 um th hth _ b hb α' hα' s₁ hs₁ _ U'
    (fun x => SecM.toSec P'.A (u' (U' x) (SecM.ofSec P'.A s₁))) (fun K _ _ x z hz => by
      obtain ⟨a, ha, uniq⟩ := hbij K x z (by rw [mul_comm, pow_mul, hz, one_pow])
      obtain ⟨a₀, -, uniq₀⟩ := hbij K x 1 (one_pow _)
      have e : S.N • a = 0 := (uniq₀ _ (by beta_reduce; rw [hsm, MonObj.comp_pow, ha, hz])).trans
        (uniq₀ _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm
      obtain ⟨c, rfl⟩ := exists_nsmul_eq hM a e
      exact ⟨c, by rw [(hU' c).pt_eq, ha]⟩) (fun x => (hu' _ _ _).2 rfl)
  have hspan' : ⊤ ≤ Submodule.span Γ((baseOver (Sp R')).left, ⊤) (Set.range s') := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    change u' (U' x) (SecM.ofSec P'.A s₁) ∈ _
    rw [← e₀, mat']
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  obtain ⟨bb, -⟩ := hb.exists_basis
  let sb := basisOfTopLeSpanOfCardEqFinrank s' hspan' (by
    rw [Module.finrank_eq_card_basis bb, Fintype.card_fin, ρ.card, hg])
  have hsb : ∀ i, sb i = s' i := fun i => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) i

  choose z hz using fun x i => (hL.evVal _ P' S.N (pt' x) (fr' x) (hfr' x).2.1 (SecM.toSec P'.A (s' i))).exists
  choose z₁ hz₁ using fun x i => fs (z x i)
  have ev₃ : ∀ x i, dd⁻¹ * S.ev x i = z₁ x i := fun x i => by
    have h₁ := isValueAt_move gp τ hτ hL₁ hL₀ (hx x).symm (genThrough_pow τ (hfr₀ x).2 S.N) (r₂ i) (ρ.ev_val i x)
    have h₂ := isValueAt_move gp' τ' hτ' hL' hL₀ (hx' x).symm (genThrough_pow τ' (vfr' x) S.N)
      (s := SecM.toSec _ (fn dd⁻¹ • SecM.ofSec P₀.A (s₀ i))) (hs' i) (hz x i)
    have := value_smul hL₀ h₁ h₂ rfl
    rw [← hz₁, tf, tf', ← fm] at this
    exact (fn_injective this).symm
  obtain ⟨c₁, hc₁⟩ := hth.exists_basis
  refine ⟨dd⁻¹, inv_ne_zero hdd0, fun x => ev₂ x ▸ (v₁ x).2, fun x i => ev₃ x i ▸ (z₁ x i).2,
    { P := P', g_eq := hg, hypS := hS, n := ρ.n, n_prime := ρ.n_prime, n_odd := ρ.n_odd, k := ρ.k, two_le := ρ.two_le
      N_eq := ρ.N_eq, r_eq := ρ.r_eq, card := ρ.card, pt := pt', pt_add := hadd, pt_bij := hbij, weil := hweil
      rig := rig', rig_gen := hrig', th₁ := th
      th₁_basis := fun σ => by
        have := existsUnique_of_basis c₁ σ
        simp only [hc₁] at this
        exact this
      fr := fr', fr_tors := hfr'
      th_val := fun x => (congrArg (IsValueAt _ _ _ _ _ _)
        ((congrArg fn (Subtype.ext (ev₂ x))).trans (hv₁ x))).mpr (hv x)
      s := fun i => SecM.toSec P'.A (s' i)
      s_basis := fun σ => by
        have := existsUnique_of_basis sb σ
        simp only [hsb] at this
        exact this
      ev_val := fun i x => (congrArg (IsValueAt _ _ _ _ _ _)
        ((congrArg fn (Subtype.ext (ev₃ x i))).trans (hz₁ x i))).mpr (hz x i)
      i₀ := ρ.i₀, α := α', α_gen := hα', α_norm := nα'
      s_zero := by
        have e : SecM.toSec P'.A (s' ρ.i₀) = s₁ := by rw [e₀]; rfl
        exact e ▸ hs₁
      U := U', U_sym := hU'
      U_act := fun x i σ H => (sum_iff σ s' _).2 (((hu' _ _ _).1 H).symm.trans (mat' x i))
      orbit := ρ.orbit }, hQ, rfl⟩

end GlobalTheory.ThetaExtend

theorem GlobalTheory.Poinc.exists_real_rechart_of_univBasis : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (U : X₁.M.Z.Opens) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (fg : (X₁.M.ringOn U).FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ (X₁.M.ringOn U), ∃ b ∈ (X₁.M.ringOn U), x = a / b) (u' : Sp (X₁.M.ringOn U) ⟶ F.X) (P' : PolAV (Sp (X₁.M.ringOn U))) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A)) (P₀ : PolAV (Sp X₁.Ω₁)) (a : P₀.A.left ⟶ X₁.ρ.P.A.left) (a' : P₀.A.left ⟶ P'.A.left) (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)) (pt' : X₁.S.Gam → (baseOver (Sp (X₁.M.ringOn U)) ⟶ P'.A)) (th : LB.Sec (LPow P'.A P'.L 1 (baseOver (Sp (X₁.M.ringOn U))))) (b : Fin (X₁.S.N ^ P'.g) → SecM P'.A P'.L (X₁.S.N : ℕ) (baseOver (Sp (X₁.M.ringOn U)))), IsAffineOpen U → (U : Set X₁.M.Z).Nonempty → IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → IsDiagEnd F W P' u' ε' → IsGrpPullback P₀.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a → IsGrpPullback P₀.A P'.A (spMap (X₁.M.ringOn U).val.toRingHom) a' → LBIso P₀.L (X₁.ρ.P.L.pull a) → LBIso P₀.L (P'.L.pull a') → (∀ E, (ε₀ E).left ≫ a = a ≫ (ε₁ E).left ∧ (ε₀ E).left ≫ a' = a' ≫ (ε' E).left) → P'.g = X₁.S.g → HypS P'.A P'.L → (∀ x y, pt' (x + y) = pt' x * pt' y) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp (X₁.M.ringOn U)) (z : Over.mk x ⟶ P'.A), z ^ (X₁.S.r * X₁.S.N) = 1 → ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp (X₁.M.ringOn U))) ≫ pt' c = z) → (∀ x y (c : (X₁.M.ringOn U)ˣ), (c : (X₁.M.ringOn U)) = algebraMap X₁.o₁ (X₁.M.ringOn U) (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)) → WeilIs P'.A P'.L (X₁.S.r * X₁.S.N : ℕ) (pt' x) (pt' y) (unitOn c)) → (∀ x, ∃ w0 : Sp X₁.Ω₁ ⟶ P₀.A.left, w0 ≫ a = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w0 ≫ a' = spMap (X₁.M.ringOn U).val.toRingHom ≫ (pt' x).left) → GlobalTheory.ThetaReal.UnivBasis P' 1 (fun _ : Fin 1 => SecM.ofSec P'.A th) → GlobalTheory.ThetaReal.UnivBasis P' (X₁.S.N : ℕ) b → ∃ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (hth : ∀ x, c₀ * X₁.S.th x ∈ (X₁.M.ringOn U)) (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ (X₁.M.ringOn U)) (ρ' : (X₁.S.rechart c₀ hc (X₁.M.ringOn U) fg frac hth hev).Real) (ε'' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X₁.ρ ε₁ ρ' ε'' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X₁.ρ.i₀ ∧ IsDiagEnd F W ρ'.P u' ε'' := by
  intro g n F W Z i X₁ U ε₁ fg frac u' P' ε' P₀ a a' ε₀ pt' th b _ hne _ hd gp gp' lb lb' hε hg hS hadd hbij hweil hw0
    hth hb
  haveI : GlobalTheory.IsNormalScheme X₁.M.Z := X₁.normal
  haveI : Nonempty U := hne.to_subtype
  haveI : IsIntegrallyClosed (X₁.M.ringOn U) := .of_equiv (X₁.M.sectionsEquiv U hne)
  obtain ⟨c₀, hc, h₁, h₂, ρ', ⟨ε'', q₁, q₂⟩, e⟩ := GlobalTheory.ThetaExtend.exists_real_rechart GlobalTheory.abelianSchemeLaws_all.1 X₁.S X₁.ρ
    (X₁.M.ringOn U) fg frac P' P₀ a a' pt' th b gp gp' lb lb' hg hS hadd hbij hweil hw0 hth hb
    (fun P pt => ∃ ε'' : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A), IsDiagEnd F W P u' ε'' ∧
      ∃ a' : P₀.A.left ⟶ P.A.left, IsGrpPullback P₀.A P.A (spMap (X₁.M.ringOn U).val.toRingHom) a' ∧
        LBIso P₀.L (P.L.pull a') ∧
        (∀ E, (ε₀ E).left ≫ a = a ≫ (ε₁ E).left ∧ (ε₀ E).left ≫ a' = a' ≫ (ε'' E).left) ∧
        ∀ x, ∃ w0 : Sp X₁.Ω₁ ⟶ P₀.A.left, w0 ≫ a = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧
          w0 ≫ a' = spMap (X₁.M.ringOn U).val.toRingHom ≫ (pt x).left) ⟨ε', hd, a', gp', lb', hε, hw0⟩
  obtain ⟨a'', q₂, q₃, q₄, q₅⟩ := q₂
  exact ⟨c₀, hc, h₁, h₂, ρ', ε'', ⟨P₀, a, a'', ε₀, gp, q₂, lb, q₃, q₄, q₅⟩, e, q₁⟩
