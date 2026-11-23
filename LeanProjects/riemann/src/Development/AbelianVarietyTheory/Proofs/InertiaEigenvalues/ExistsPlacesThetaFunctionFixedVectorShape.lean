import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DropPlInsert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFinsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiVNeOneOfTrace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.ShapeOff

theorem rel_indep {G M : Type} [AddCommGroup G] [AddCommGroup M] [Module ℂ M] (ρ : G → Module.End ℂ M) (κ γ : G → G → ℂ)
    (hκ : ∀ x y, κ x y ≠ 0) (h0 : ∀ s, ρ 0 s = s) (hρ : ∀ x y s, ρ x (ρ y s) = κ x y • ρ (x + y) s)
    (hγ : ∀ x y s, ρ x (ρ y s) = γ x y • ρ y (ρ x s)) (X L : AddSubgroup G) (hLX : L ≤ X)
    (hdist : ∀ x ∈ X, ∀ y ∈ X, (∀ u ∈ L, γ u x = γ u y) → x - y ∈ L) (c : G →₀ ℂ) (hc : ∀ x ∈ c.support, x ∈ X)
    {s s' : M} (hs : s ≠ 0) (hvac : ∀ u ∈ L, ρ u s = s) (hvac' : ∀ u ∈ L, ρ u s' = s')
    (hsum : (c.sum fun x z => z • ρ x s) = 0) : (c.sum fun x z => z • ρ x s') = 0 := by
  classical
  have hnz : ∀ x, ρ x s ≠ 0 := by
    intro x h
    have := hρ (-x) x s
    rw [h, map_zero, neg_add_cancel, h0] at this
    exact hs ((smul_eq_zero.mp this.symm).resolve_left (hκ _ _))
  have hmem : ∀ x : G, -(QuotientAddGroup.mk x : G ⧸ L).out + x ∈ L := by
    intro x
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
  set k : G → ℂ := fun x => (κ (QuotientAddGroup.mk x : G ⧸ L).out (-(QuotientAddGroup.mk x : G ⧸ L).out + x))⁻¹ with hk
  have hdec1 : ∀ t, (∀ u ∈ L, ρ u t = t) → ∀ x, ρ x t = k x • ρ (QuotientAddGroup.mk x : G ⧸ L).out t := by
    intro t ht x
    have := hρ (QuotientAddGroup.mk x : G ⧸ L).out (-(QuotientAddGroup.mk x : G ⧸ L).out + x) t
    rw [ht _ (hmem x), add_neg_cancel_left] at this
    rw [this, smul_smul, hk, inv_mul_cancel₀ (hκ _ _), one_smul]
  set I : Finset (G ⧸ L) := c.support.image (fun x => (QuotientAddGroup.mk x : G ⧸ L)) with hI
  set C : (G ⧸ L) → ℂ := fun y => ∑ x ∈ c.support with (QuotientAddGroup.mk x : G ⧸ L) = y, c x * k x with hC
  have hdec : ∀ t, (∀ u ∈ L, ρ u t = t) → (c.sum fun x z => z • ρ x t) = ∑ y ∈ I, C y • ρ y.out t := by
    intro t ht
    unfold Finsupp.sum
    have e1 : ∑ x ∈ c.support, c x • ρ x t = ∑ x ∈ c.support, (c x * k x) • ρ (QuotientAddGroup.mk x : G ⧸ L).out t := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hdec1 t ht x, smul_smul]
    rw [e1, ← Finset.sum_fiberwise_of_maps_to (s := c.support) (t := I) (g := fun x => (QuotientAddGroup.mk x : G ⧸ L))
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hC, Finset.sum_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.mp hx).2]
  have hout : ∀ y ∈ I, y.out ∈ X := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have := sub_mem (hc x hx) (hLX (hmem x))
    rwa [neg_add_eq_sub, sub_sub_cancel] at this
  have hC0 : ∀ y ∈ I, C y = 0 := by
    have hind := GlobalTheory.Hk3.eig_indep (fun u : L => ρ (u : G)) (fun (y : G ⧸ L) (u : L) => γ u y.out)
      (fun y => ρ y.out s) (fun y u => by rw [hγ, hvac u u.2]) I
      (by
        intro y hy y' hy' hyy
        by_contra hcon
        push Not at hcon
        apply hyy
        have hm := hdist y.out (hout y hy) y'.out (hout y' hy') (fun u hu => hcon ⟨u, hu⟩)
        rw [← QuotientAddGroup.out_eq' y, ← QuotientAddGroup.out_eq' y', QuotientAddGroup.eq_iff_sub_mem]
        exact hm)
      C (by rw [← hdec s hvac]; exact hsum)
    intro y hy
    exact (smul_eq_zero.mp (hind y hy)).resolve_right (hnz _)
  rw [hdec s' hvac']
  exact Finset.sum_eq_zero fun y hy => by rw [hC0 y hy, zero_smul]

variable {D : D7}

open GlobalTheory.ThetaVacuumAE in

theorem exists_latO_le (S T : HSp D) (U : AddSubgroup (WO S T)) (hU : IsOpen (U : Set (WO S T))) :
    ∃ Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)), latO S T (L0c D S) (L0c D T) (fun v => v ∉ Sb) ≤ U := by
  classical
  obtain ⟨M, hM, hMx⟩ := exists_fg_coord S
  obtain ⟨N, hN, hNy⟩ := exists_fg_coord T
  have hA : ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E).restrictScalars ℤ).FG :=
    fg_int (FractionalIdeal.fg_of_isNoetherianRing le_rfl _)
  have hJ : (Submodule.span ℤ (Set.range fun p : Fin S.rank × Fin S.rank => S.gram p.1 p.2)).FG :=
    Submodule.fg_span (Set.finite_range _)
  obtain ⟨G, hG⟩ := (hA.mul hN).mul (hM.mul hJ)
  have h1 : ∀ (i : Fin T.rank) (j : Fin S.rank) (e : D.host.E), ∃ Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      ∀ α ∈ intAf D.host.F, (∀ v ∈ Sb, evalV D.host.F v α = 0) →
        (Matrix.single i j (pairA D.host.F 0 α ⊗ₜ[D.host.F] e : AE D) : WO S T) ∈ U := by
    intro i j e
    have hc : Continuous fun α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F =>
        (Matrix.single i j (pairA D.host.F 0 α ⊗ₜ[D.host.F] e : AE D) : WO S T) := by
      refine continuous_pi fun k => continuous_pi fun l => ?_
      simp only [Matrix.single, Matrix.of_apply]
      split_ifs
      · exact continuous_tmul D e
      · exact continuous_const
    refine exists_finset_of_mem_nhds ((hU.preimage hc).mem_nhds ?_)
    change Matrix.single i j ((0 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) ∈ U
    rw [TensorProduct.zero_tmul, Matrix.single_zero]
    exact zero_mem U
  choose Sb hS using h1
  refine ⟨Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => G.biUnion (Sb i j), (AddSubgroup.closure_le _).2 ?_⟩
  rintro _ ⟨α, hα, h0, a, ha, x, hx, y, hy, rfl⟩
  have h2 : ∀ i j, ∀ e ∈ Submodule.span ℤ (G : Set D.host.E),
      (Matrix.single i j (pairA D.host.F 0 α ⊗ₜ[D.host.F] e : AE D) : WO S T) ∈ U := by
    intro i j e he
    induction he using Submodule.span_induction with
    | mem e he =>
      refine hS i j e α hα fun v hv => h0 v (not_not.2 ?_)
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, j, e, he, hv⟩
    | zero => rw [TensorProduct.tmul_zero, Matrix.single_zero]; exact zero_mem U
    | add e e' _ _ h h' => rw [TensorProduct.tmul_add, Matrix.single_add]; exact add_mem h h'
    | smul n e _ h =>
      let Φ : D.host.E →+ WO S T := (Matrix.singleAddMonoidHom i j).comp
        (TensorProduct.mk D.host.F (AF D.host.F) D.host.E (pairA D.host.F 0 α)).toAddMonoidHom
      have h' : Φ e ∈ U := h
      change Φ (n • e) ∈ U
      rw [map_zsmul]
      exact zsmul_mem h' n
  rw [SetLike.mem_coe, Matrix.matrix_eq_sum_single (Matrix.of _)]
  refine sum_mem fun i _ => sum_mem fun j _ => h2 i j _ ?_
  rw [hG]
  exact Submodule.mul_mem_mul (Submodule.mul_mem_mul ha (hNy y hy i).1) (sum_mem fun k _ =>
    Submodule.mul_mem_mul (hMx x hx k).2 (Submodule.subset_span ⟨(k, j), rfl⟩))

def offIdem (F : Type) [Field F] [NumberField F] (Sb : Finset (HeightOneSpectrum (𝓞 F))) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F :=
  1 - ∑ v ∈ Sb, singleV F v 1

theorem evalV_offIdem {F : Type} [Field F] [NumberField F] (Sb : Finset (HeightOneSpectrum (𝓞 F)))
    (w : HeightOneSpectrum (𝓞 F)) :
    (w ∈ Sb → evalV F w (offIdem F Sb) = 0) ∧ (w ∉ Sb → evalV F w (offIdem F Sb) = 1) := by
  have e1 : evalV F w (singleV F w 1) = 1 := GlobalTheory.StdCharTotReal.single_same w 1
  have e2 : ∀ v, v ≠ w → evalV F w (singleV F v 1) = 0 := fun v hv => GlobalTheory.StdCharTotReal.single_ne v 1 hv.symm
  unfold offIdem
  rw [map_sub, map_one, map_sum]
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · rw [Finset.sum_eq_single_of_mem w hw fun v _ hv => e2 v hv, e1, sub_self]
  · rw [Finset.sum_eq_zero fun v hv => e2 v fun h => hw (h ▸ hv), sub_zero]

theorem offIdem_mul_self {F : Type} [Field F] [NumberField F] (Sb : Finset (HeightOneSpectrum (𝓞 F))) :
    offIdem F Sb * offIdem F Sb = offIdem F Sb := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change evalV F w (offIdem F Sb * offIdem F Sb) = evalV F w (offIdem F Sb)
  rw [map_mul]
  by_cases hw : w ∈ Sb
  · rw [(evalV_offIdem Sb w).1 hw, mul_zero]
  · rw [(evalV_offIdem Sb w).2 hw, mul_one]

def offE (D : D7) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AE D :=
  algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (offIdem D.host.F Sb))

theorem offE_mul_self (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) : offE D Sb * offE D Sb = offE D Sb := by
  unfold offE
  rw [← RingHom.map_mul]
  congr 1
  exact Prod.ext (mul_zero _) (offIdem_mul_self Sb)

theorem cA_offE (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) : cA D (offE D Sb) = offE D Sb := by
  unfold offE
  rw [Algebra.algebraMap_eq_smul_one, GlobalTheory.FinTranslate.cA_smul, RingHom.map_one]

variable {S T : HSp D}

theorem offE_smul_mem (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) {LS : Set (Fin S.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)} {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    offE D Sb • u ∈ latO S T LS LT fun w => w ∉ Sb := by
  have hβ : offIdem D.host.F Sb ∈ intAf D.host.F := fun w => by
    by_cases hw : w ∈ Sb
    · rw [(evalV_offIdem Sb w).1 hw]; exact zero_mem _
    · rw [(evalV_offIdem Sb w).2 hw]; exact one_mem _
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨offIdem D.host.F Sb * α, GlobalTheory.WeilUnramifiedCompare.intAf_mul hβ hα,
      fun w hw => ?_, a, ha, s, hs, t, ht, ?_⟩
    · rw [map_mul, (evalV_offIdem Sb w).1 (not_not.1 hw), zero_mul]
    · ext i j
      change (pairA D.host.F 0 (offIdem D.host.F Sb) ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x x' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg x _ h => rw [smul_neg]; exact neg_mem h

theorem infPart_of_half (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) {u : WO S T}
    (hu : u ∈ GlobalTheory.PlaceModel.half S T (offE D Sb)) : u.map (infPart D) = 0 := by
  have h0 : infPart D (offE D Sb) = 0 := TensorProduct.zero_tmul _ _
  ext i j
  rw [Matrix.map_apply, ← (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu i j, RingHom.map_mul, h0, zero_mul]
  rfl

theorem half_of_offPl (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) {u : WO S T} (hu : OffPl Sb u) :
    u ∈ GlobalTheory.PlaceModel.half S T (offE D Sb) := by
  refine (GlobalTheory.PlaceModel.isHalf_iff S T).1 fun i j => ?_
  have h1 : algebraMap (AF D.host.F) (AE D) (GlobalTheory.FinTranslate.eInf D) * u i j = 0 := by
    rw [← Algebra.smul_def]
    exact GlobalTheory.FinTranslate.smul_eq_zero_of_inf (congrFun (congrFun hu.1 i) j)
  have h2 : ∀ v ∈ Sb, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) * u i j = 0 :=
    fun v hv => hu.2 v hv _ ⟨_, rfl, GlobalTheory.StdCharTotReal.single_same v 1,
      fun w hw => GlobalTheory.StdCharTotReal.single_ne v 1 hw⟩ i j
  have e : pairA D.host.F 0 (offIdem D.host.F Sb) =
      1 - GlobalTheory.FinTranslate.eInf D - ∑ v ∈ Sb, pairA D.host.F 0 (singleV D.host.F v 1) := by
    have e0 : ∑ v ∈ Sb, pairA D.host.F 0 (singleV D.host.F v 1) = pairA D.host.F 0 (∑ v ∈ Sb, singleV D.host.F v 1) :=
      (map_sum (AddMonoidHom.inr (Ainf D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) _ _).symm
    rw [e0]
    exact Prod.ext (show (0 : Ainf D.host.F) = 1 - 1 - 0 by ring)
      (show 1 - ∑ v ∈ Sb, singleV D.host.F v 1 = 1 - 0 - ∑ v ∈ Sb, singleV D.host.F v 1 by rw [sub_zero])
  unfold offE
  rw [e, RingHom.map_sub, RingHom.map_sub, RingHom.map_one, map_sum, sub_mul, sub_mul, one_mul, h1, Finset.sum_mul,
    Finset.sum_eq_zero h2, sub_zero, sub_zero]

open GlobalTheory.PlaceModel in

theorem exists_rel_off {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {s f : WO S T → ℂ}
    (hs : IsThetaFunO ψ S T s) (hs0 : s ≠ 0) (hf : IsThetaFunO ψ S T f) :
    ∃ Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ c : WO S T →₀ ℂ, (∀ u ∈ c.support, OffPl Sb u) →
      (c.sum fun u z => z • heisO ψ S T u s) = 0 → (c.sum fun u z => z • heisO ψ S T u f) = 0 := by
  obtain ⟨U, hU, hUs⟩ := hs.level
  obtain ⟨U', hU', hUf⟩ := hf.level
  obtain ⟨Sb, hSb⟩ := exists_latO_le S T (U ⊓ U') (hU.inter hU')
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ (isSelfDualC_latFrame S) (isSelfDualC_latFrame T)).1
  rw [coe_latFrame, coe_latFrame] at hdual
  have hne : ∀ a, ψ a ≠ 0 := fun a h => by
    have := ψ.map_add_eq_mul a (-a)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this
  have hLU : ∀ u ∈ (latO S T (L0c D S) (L0c D T) fun _ => True) ⊓ half S T (offE D Sb), u ∈ U ⊓ U' := fun u hu => by
    have := hSb (offE_smul_mem Sb hu.1)
    rwa [(mem_half S T).1 hu.2] at this
  refine ⟨Sb, fun c hc hsum => ?_⟩
  refine rel_indep (heisL S T ψ) (fun x y => ψ (symplOH S T x y)) (fun x y => ψ (symplO S T x y)) (fun _ _ => hne _)
    (GlobalTheory.LatVac.heisO_zero ψ) (heisL_heisL S T ψ) (heisL_comm S T ψ) (half S T (offE D Sb))
    ((latO S T (L0c D S) (L0c D T) fun _ => True) ⊓ half S T (offE D Sb)) inf_le_right (fun x hx y hy h => ?_) c
    (fun x hx => half_of_offPl Sb (hc x hx)) hs0 (fun u hu => hUs u (hLU u hu).1 (infPart_of_half Sb hu.2))
    (fun u hu => hUf u (hLU u hu).2 (infPart_of_half Sb hu.2)) hsum
  have hxy := sub_mem hx hy
  refine ⟨(hdual _ (infPart_of_half Sb hxy)).2 fun u hu => ?_, hxy⟩
  have h1 := h (offE D Sb • u) ⟨latO_le_top _ (offE_smul_mem Sb hu),
    (mem_half S T).2 (by rw [smul_smul, offE_mul_self])⟩
  simp only [symplO_smul, cA_offE, (mem_half S T).1 hx, (mem_half S T).1 hy] at h1
  have h2 : symplO S T u x = symplO S T u (x - y) + symplO S T u y := by rw [← symplO_add_right, sub_add_cancel]
  rw [h2, AddChar.map_add_eq_mul, mul_left_eq_self₀] at h1
  rw [symplO_skew, AddChar.map_neg_eq_inv, h1.resolve_right (hne _), inv_one]

theorem exists_likeOff : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∃ Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)), GlobalTheory.DownLift.GenFinite.LikeOff R i t Sb f := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t f hf
  have hL := hG.core
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hv0 : R.vP i t ≠ 0 := GlobalTheory.AdTh.VecNe.thPVec_ne_zero
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βV i))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βW i))
    ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hL.thP.vP i t)
  obtain ⟨Sb, h⟩ := exists_rel_off (hL.thP.ωP i t).std hth hv0 hf
  exact ⟨Sb, hf, h⟩

end GlobalTheory.DownLift.ShapeOff

end
