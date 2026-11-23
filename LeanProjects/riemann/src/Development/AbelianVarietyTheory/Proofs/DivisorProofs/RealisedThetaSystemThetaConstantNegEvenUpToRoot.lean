import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarizedAbelianValueTableMapsUnderBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMaps
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSymmetricIffExistsGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsPullbackPrescribed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGenSecNear
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoOfAssociatedGermsFlat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.ThetaParity

theorem exists_rigPull_inv {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (hrig : rig.IsGen) :
    haveI := P.isAb.comm
    ∃ w : LB.Iso P.L (P.L.pull (ι[P.A]).left), GlobalTheory.OneBasis.RigPull P.A P.A (𝟙 S) (ι[P.A]).left w rig rig := by
  haveI := P.isAb.comm
  obtain ⟨u, hu⟩ := GlobalTheory.exists_gen_neg_of_sym GlobalTheory.globalFns_holds P.isAb P.isLB P.sym
  obtain ⟨s, hs, hr⟩ := GlobalTheory.AbPackage.exists_rigidified_sym P.isLB u hu
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨he, w, hw, hm⟩ := GlobalTheory.SymmetricBundle.isSymmetric_of_gen L s hs hr
  refine ⟨w, GlobalTheory.SabBaseChange.isGrpPullback_inv P.A, hw, hrig, ?_⟩
  exact (maps_iff w (K := PUnit) (fun _ => eSec P.A) (fun _ => eSec P.A) (fun _ => 1) rig rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) he P.L j) (fun _ => rfl)).1 hm

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem pt_neg {S : ThetaSys o Ω} (ρ : S.Real) (a : S.Gam) : ρ.pt (-a) = (ρ.pt a)⁻¹ := by
  have h0 : ρ.pt 0 = 1 := by
    have h := ρ.pt_add 0 0
    rw [add_zero] at h
    have h' : ρ.pt 0 * ρ.pt 0 = ρ.pt 0 * 1 := by rw [_root_.mul_one]; exact h.symm
    exact mul_left_cancel h'
  have h := ρ.pt_add (-a) a
  rw [neg_add_cancel, h0] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem pt_neg_left {S : ThetaSys o Ω} (ρ : S.Real) (a : S.Gam) :
    haveI := ρ.P.isAb.comm
    (ρ.pt (-a)).left ≫ (ι[ρ.P.A]).left = 𝟙 _ ≫ (ρ.pt a).left := by
  rw [pt_neg, Category.id_comp, ← Over.comp_left]
  congr 1
  simp [Hom.inv_def]

theorem key_fn (S : ThetaSys o Ω) (ρ : S.Real) :
    ∃ c₀ : Γ((baseOver (Sp S.R)).left, ⊤), ∀ a, ∃ d : Γ((baseOver (Sp S.R)).left, ⊤),
      d ^ ((S.r * S.N) ^ 2) = 1 ∧ c₀ * fn (⟨S.th (-a), S.th_mem (-a)⟩ : S.R) = d * fn (⟨S.th a, S.th_mem a⟩ : S.R) := by
  haveI := ρ.P.isAb.comm
  obtain ⟨w, R⟩ := exists_rigPull_inv ρ.P ρ.rig ρ.rig_gen
  have hφ : (ι[ρ.P.A]).left ≫ ρ.P.A.hom = ρ.P.A.hom ≫ 𝟙 _ := by rw [Over.w, Category.comp_id]
  obtain ⟨s', hs', -⟩ := GlobalTheory.OneBasis.Calc.existsUnique_thru (k := 1) (T := baseOver (Sp S.R))
    (T' := baseOver (Sp S.R)) hφ R.2.1 ρ.P.isLB ρ.P.isLB (h := 𝟙 _) (by simp) ρ.th₁
  obtain ⟨c, hc, -⟩ := ρ.th₁_basis s'
  refine ⟨c 0, fun a => ?_⟩
  obtain ⟨e', he', He⟩ := GlobalTheory.OneBasis.TabMap.frame_move R (h := 𝟙 _) (pt_neg_left ρ a) (ρ.fr_tors a)
  have v₁ := He 1 ρ.th₁ s' (fn (⟨S.th a, S.th_mem a⟩ : S.R)) hs' (fun z J hJ => by
    have := GlobalTheory.FrameMove.sval_valueAt (ρ.th_val a) (𝟙 _) hJ
    rw [Category.id_comp] at this
    rw [GlobalTheory.FrameMove.val_powFrame]
    simpa using this)
  have v₂ := (GlobalTheory.OneBasis.Calc.cmb_iff ρ.P.isLB (k := 1) (fun _ => ρ.th₁) c s').1 hc
  obtain ⟨d, hd⟩ := GlobalTheory.AbPackage.exists_unit_ratio ρ.P.isLB he'.2.1 (ρ.fr_tors (-a)).2.1
  obtain ⟨α, hα⟩ := GlobalTheory.EmbLocal.exists_mulPull GlobalTheory.globalFns_holds ρ.P (S.r * S.N) (baseOver (Sp S.R))

  refine ⟨(d : Γ((baseOver (Sp S.R)).left, ⊤)), ?_, ?_⟩
  · have hu : d ^ ((S.r * S.N) ^ 2) = 1 := by
      apply Units.ext
      apply fn_ext
      intro z _
      obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' ρ.P.isLB z
      have t₁ := GlobalTheory.ThetaCompare.torsFrame_pow GlobalTheory.globalFns_holds ρ.P hα he' hJ
      have t₂ := GlobalTheory.ThetaCompare.torsFrame_pow GlobalTheory.globalFns_holds ρ.P hα (ρ.fr_tors (-a)) hJ
      have e := hd _ (𝟙 _) z J hJ
      rw [e, mul_pow, ← t₂, _root_.mul_assoc] at t₁
      have g := mul_eq_right.1 t₁
      rw [gs_unit (𝟙 _) z ⊤ trivial, gs_unit (𝟙 _) z ⊤ trivial, map_pow, g, map_one]
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  · apply fn_ext
    intro z _
    obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' ρ.P.isLB z
    have a₁ := v₁ z J hJ
    have a₂ := v₂ _ (ptSecT ρ.P.A (ρ.pt (-a))).left z J hJ
    have a₃ := GlobalTheory.FrameMove.sval_valueAt (ρ.th_val (-a)) (𝟙 _) hJ
    have a₄ := hd _ (𝟙 _) z J hJ
    rw [Category.id_comp] at a₃
    rw [gs_mul _ z ⊤ trivial, gs_mul _ z ⊤ trivial]

    simp only [GlobalTheory.FrameGen.sv, Fin.sum_univ_one] at a₂
    have f₁ : (ptSecT ρ.P.A (ρ.pt (-a))).left ≫ (fst (baseOver (Sp S.R)) ρ.P.A).left = 𝟙 _ := by
      rw [← Over.comp_left, ptSecT, lift_fst, Over.id_left]
    rw [f₁, ← GlobalTheory.FrameGen.gs_top, a₃] at a₂
    have hp : ∀ u : ((baseOver (Sp S.R)).left.presheaf.stalk z)ˣ, u ^ ((1 : ℕ) : ℤ) = u := fun u => by simp
    rw [GlobalTheory.FrameMove.val_powFrame, hp, a₄, Units.val_mul] at a₁
    have e := a₂.symm.trans a₁
    rw [← gs_unit (𝟙 _) z ⊤ trivial d] at e
    refine (Units.mul_left_inj (Geo.Tor.val (ρ.fr (-a)) (𝟙 _) z J)).1 ?_
    linear_combination e

theorem key (S : ThetaSys o Ω) (ρ : S.Real) :
    ∃ C : Ω, ∀ a, ∃ D : Ω, D ^ ((S.r * S.N) ^ 2) = 1 ∧ C * S.th (-a) = D * S.th a := by
  obtain ⟨c₀, h⟩ := key_fn S ρ
  let φ : Γ((baseOver (Sp S.R)).left, ⊤) →+* Ω :=
    S.R.val.toRingHom.comp (Scheme.ΓSpecIso (CommRingCat.of S.R)).hom.hom
  have hφ : ∀ x : S.R, φ (fn x) = x := fun x => by simp [φ, fn]
  refine ⟨φ c₀, fun a => ?_⟩
  obtain ⟨d, hd, e⟩ := h a
  refine ⟨φ d, by rw [← map_pow, hd, map_one], ?_⟩
  have := congrArg φ e
  rwa [map_mul, map_mul, hφ, hφ] at this

theorem odd_rN (S : ThetaSys o Ω) (ρ : S.Real) : Odd ((S.r * S.N) ^ 2) := by
  obtain ⟨j, -, hj⟩ := ρ.r_eq
  rw [hj, ρ.N_eq]
  exact ((ρ.n_odd.pow).mul ((ρ.n_odd.pow).pow)).pow

end GlobalTheory.ThetaParity

namespace GlobalTheory.ThetaParity

theorem theta_neg : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (ρ : S.Real) (a : S.Gam), ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a := by
  intro o Ω _ _ _ _ S ρ a
  obtain ⟨C, hC⟩ := key S ρ
  have hodd := odd_rN S ρ
  set m := (S.r * S.N) ^ 2 with hm
  obtain ⟨x, hx⟩ := S.th_ne
  obtain ⟨D₁, hD₁, e₁⟩ := hC x
  obtain ⟨D₂, hD₂, e₂⟩ := hC (-x)
  rw [neg_neg] at e₂
  have hm0 : m ≠ 0 := hodd.pos.ne'
  have nz : ∀ D : Ω, D ^ m = 1 → D ≠ 0 := fun D h h0 => by
    rw [h0, zero_pow hm0] at h; exact zero_ne_one h
  have hx' : S.th (-x) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at e₁; exact (mul_ne_zero (nz _ hD₁) hx) e₁.symm
  have hC0 : C ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e₁; exact (mul_ne_zero (nz _ hD₁) hx) e₁.symm
  have hC2 : C ^ 2 = D₁ * D₂ := by
    have h2 : C ^ 2 * (S.th (-x) * S.th x) = D₁ * D₂ * (S.th (-x) * S.th x) := by
      linear_combination (C * S.th x) * e₁ + (D₁ * S.th x) * e₂
    exact mul_right_cancel₀ (mul_ne_zero hx' hx) h2
  have hCi : C⁻¹ ^ (2 * m) = 1 := by
    rw [inv_pow, pow_mul, hC2, mul_pow, hD₁, hD₂, _root_.one_mul, inv_one]
  obtain ⟨D, hD, e⟩ := hC a
  obtain ⟨k, hk⟩ := hodd
  refine ⟨C⁻¹ ^ m, C⁻¹ ^ (m + 1) * D, ?_, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, hCi]
  · rw [mul_pow, hD, _root_.mul_one, ← pow_mul, show (m + 1) * m = 2 * m * (k + 1) by rw [hk]; ring, pow_mul, hCi,
      one_pow]
  · have e' : S.th (-a) = C⁻¹ * D * S.th a := by
      rw [_root_.mul_assoc, ← e, ← _root_.mul_assoc, inv_mul_cancel₀ hC0, _root_.one_mul]
    rw [e', ← _root_.mul_assoc, ← pow_add, show m + (m + 1) = 2 * m + 1 by ring, pow_succ, hCi, _root_.one_mul]

end GlobalTheory.ThetaParity
