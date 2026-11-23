import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermute
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

noncomputable section
namespace GlobalTheory.ZH.EvRoot
open GlobalTheory.ThetaCompare

variable {S : Scheme.{0}}

private theorem val_powFrame_divisor {S : Scheme.{0}} (P : PolAV S) {T : Over S} (h : T ⟶ P.A)
    (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => h.left) (fun _ => 1))) (k : ℤ)
    (y : T.left) (J : (T.left ⟶ P.A.left) → P.L.ι) :
    val (powFrame P.A P.L h τ k) (𝟙 _) y J = val τ (𝟙 _) y J ^ k := by
  unfold powFrame val gm
  split_ifs
  · exact map_zpow _ _ _
  · exact (one_zpow k).symm

private theorem val_rigPow' {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (k : ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ S) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι) :
    val (rigPow P.A P.L rig k) r z J = val rig r z J ^ k := by
  unfold rigPow val gm
  split_ifs
  · exact map_zpow _ _ _
  · exact (one_zpow k).symm

open CommPairing in

theorem exists_root_stalk_pull (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {N M m : ℕ}
    {rig : LB.Gen (P.L.pull (eSec P.A))}
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1])}
    (hα : α.IsGen)
    (hn : LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left)
      (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T N) (rigT P.A P.L rig T (-1))))
    {h w : T ⟶ P.A} (hw : w = h ^ m) {τ τ'} (hτ : IsTorsFrame P rig M h τ)
    (hτ' : IsTorsFrame P rig M w τ') {th : LB.Sec (LPow P.A P.L 1 T)} {s : LB.Sec (LPow P.A P.L N T)}
    (hs : IsTwistPull P.A P.L (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _) N 1 α th s) {v v' : Γ(T.left, ⊤)}
    (hv : IsValueAt P.A P.L N s h (powFrame P.A P.L h τ N) v) (hv' : IsValueAt P.A P.L 1 th w τ' v') (y : T.left) :
    ∃ ξ : (T.left.presheaf.stalk y)ˣ, ξ ^ (M ^ 2) = 1 ∧ gs (𝟙 _) y ⊤ v = ξ.val * gs (𝟙 _) y ⊤ v' := by
  have hL : P.L.IsLB := P.isLB
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt hL y
  have e1 := sval_twist hs (ptSecT P.A h).left hJ
  rw [pt_mulT, ← hw, sval_valueAt hv hJ, sval_valueAt hv' hJ] at e1
  refine ⟨val α (ptSecT P.A h).left y J * val τ' (𝟙 _) y J * (val (powFrame P.A P.L h τ N) (𝟙 _) y J)⁻¹, ?_, ?_⟩
  · unfold IsTorsFrame at hτ hτ'
    obtain ⟨hhM, -, β, hβ, hnβ, hcβ⟩ := hτ
    obtain ⟨-, -, β', hβ', hnβ', hcβ'⟩ := hτ'
    have eτ : val τ (𝟙 _) y J ^ ((M : ℤ) ^ 2) = val β h.left y J * val rig T.hom y J := by
      rw [← val_powFrame_divisor, val_corr hJ hcβ (𝟙 _), val_mul hJ, val_pull hJ, val_rigT rig 1 hJ, zpow_one,
        Category.id_comp]
    have eτ' : val τ' (𝟙 _) y J ^ ((M : ℤ) ^ 2) = val β' w.left y J * val rig T.hom y J := by
      rw [← val_powFrame_divisor, val_corr hJ hcβ' (𝟙 _), val_mul hJ, val_pull hJ, val_rigT rig 1 hJ, zpow_one,
        Category.id_comp]
    have orbitMap_conj_smul_one : val α (ptSecT P.A 1).left y J = val rig T.hom y J ^ (N : ℤ) * val rig T.hom y J ^ (-1 : ℤ) := by
      have := val_corr hJ hn (𝟙 _)
      rw [val_pull hJ, val_mul hJ, val_rigT rig _ hJ, val_rigT rig _ hJ, Category.id_comp] at this
      exact this
    have eB1 : val β (T.hom ≫ eSec P.A) y J = val rig T.hom y J ^ ((M : ℤ) ^ 2) * (val rig T.hom y J)⁻¹ := by
      have := val_corr hJ hnβ T.hom
      rw [val_pull hJ, val_mul hJ, val_inv, val_rigPow'] at this
      exact this
    have eB1' : val β' (T.hom ≫ eSec P.A) y J = val rig T.hom y J ^ ((M : ℤ) ^ 2) * (val rig T.hom y J)⁻¹ := by
      have := val_corr hJ hnβ' T.hom
      rw [val_pull hJ, val_mul hJ, val_inv, val_rigPow'] at this
      exact this
    have rA := Reg.two (L := P.L) (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
    have rB := Reg.two (L := P.L) (y := y) (J := J) (LB.pullGen P.L _ _ β (snd T P.A).left)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen P.L _ _ β hβ _) (snd T P.A) (snd T P.A ^ M)
      (by simp)
      (by show (snd T P.A).left ≫ (mulA P.A M).left = (snd T P.A ^ M).left
          rw [← Over.comp_left, GlobalTheory.DivisibleHom.comp_mulA])
    have rB' := Reg.two (L := P.L) (y := y) (J := J) (LB.pullGen P.L _ _ β' (snd T P.A).left)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen P.L _ _ β' hβ' _) (snd T P.A) (snd T P.A ^ M)
      (by simp)
      (by show (snd T P.A).left ≫ (mulA P.A M).left = (snd T P.A ^ M).left
          rw [← Over.comp_left, GlobalTheory.DivisibleHom.comp_mulA])
    have rF := ((rA.pow hJ (M ^ 2)).mul hJ (rB'.pull hJ (snd T P.A ^ m))).mul hJ
      (((rB.pow hJ N).inv).mul hJ ((rA.pull hJ (snd T P.A ^ M)).inv))
    have hmM : (snd T P.A ^ m) ^ M = (snd T P.A ^ M) ^ m := by
      rw [← pow_mul, ← pow_mul, _root_.mul_comm]
    have hF := Reg.const hG P.isAb hL hJ rF (by
      intro U _ hh
      simp only [CartesianMonoidalCategory.lift_snd, GlobalTheory.SymLiftOdd.comp_pow', hmM]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv, ofMul_one]
      simp only [← natCast_zsmul]
      push_cast
      module) h 1
    simp only [val_pull hJ, ← Over.comp_left, pt_snd, GlobalTheory.SymLiftOdd.comp_pow', one_pow, hhM, ← hw,
      GlobalTheory.UU.one_left] at hF
    rw [val_powFrame_divisor]
    apply Additive.ofMul.injective
    have f1 := congrArg Additive.ofMul hF
    have f2 := congrArg Additive.ofMul eτ
    have f3 := congrArg Additive.ofMul eτ'
    have f4 := congrArg Additive.ofMul orbitMap_conj_smul_one
    have f5 := congrArg Additive.ofMul eB1
    have f6 := congrArg Additive.ofMul eB1'
    simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv, ofMul_one, ← natCast_zsmul] at f1 f2 f3 f4 f5 f6 ⊢
    push_cast at f1 f2 f3 f4 f5 f6 ⊢
    linear_combination (norm := module) f1 + f3 - (N : ℤ) • f2 + ((M : ℤ) ^ 2) • f4 + f6 - (N : ℤ) • f5
  · have e2 : gs (𝟙 _) y ⊤ v = gs (𝟙 _) y ⊤ v * (val (powFrame P.A P.L h τ N) (𝟙 _) y J).val *
        ((val (powFrame P.A P.L h τ N) (𝟙 _) y J)⁻¹ : (T.left.presheaf.stalk y)ˣ).val := by
      rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    rw [e2, e1]
    simp only [Units.val_mul]
    ring

private theorem real_pt_nsmul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    ∀ (c : ℕ) (b : S.Gam), ρ.pt (c • b) = ρ.pt b ^ c := by
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  intro c b
  induction c with
  | zero => rw [zero_smul, h0, pow_zero]
  | succ c ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]

private theorem exists_injective_stalk_hom_gs_eq {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) :
    ∃ (y : (baseOver (Sp S.R)).left) (φ : S.R →+* (baseOver (Sp S.R)).left.presheaf.stalk y),
      Function.Injective φ ∧ ∀ a : S.R, gs (𝟙 _) y ⊤ (fn a) = φ a := by
  have hI : IsIntegral (baseOver (Sp S.R)).left := by
    first
    | infer_instance
    | (show IsIntegral (Spec (CommRingCat.of S.R)); infer_instance)
  refine ⟨genericPoint _, (((baseOver (Sp S.R)).left.presheaf.germ ⊤ (genericPoint _) trivial).hom).comp
    (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom, ?_, ?_⟩
  · intro a b h
    have h1 := AlgebraicGeometry.germ_injective_of_isIntegral (baseOver (Sp S.R)).left (U := ⊤) (genericPoint _) trivial
    exact (Scheme.ΓSpecIso (CommRingCat.of S.R)).commRingCatIsoToRingEquiv.symm.injective (h1 h)
  · intro a
    unfold gs
    rw [dif_pos (show _ ∈ (⊤ : (baseOver (Sp S.R)).left.Opens) from trivial)]
    rfl

private theorem exists_rootOfUnity_mul_of_pow_eq_pow {K : Type} [Field K] (a b : K) (n : ℕ) (hn : 0 < n) (h : a ^ n = b ^ n) :
    ∃ u : K, u ^ n = 1 ∧ a = u * b := by
  by_cases hb : b = 0
  · subst hb
    rw [zero_pow hn.ne'] at h
    exact ⟨1, one_pow n, by rw [pow_eq_zero_iff hn.ne'] at h; simp [h]⟩
  · refine ⟨a / b, ?_, (div_mul_cancel₀ a hb).symm⟩
    rw [div_pow, h, div_self (pow_ne_zero n hb)]

theorem ev_eq_root_mul_th : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (x : S.Gam) (j : S.J), ∃ (y : S.Gam) (u : Ω) (k : ℕ), 0 < k ∧ u ^ k = 1 ∧ S.ev x j = u * S.th y := by
  intro o Ω _ _ _ _ S ρ x j
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨a, e, ha⟩ := ρ.orbit j
  have hpt : ∀ (c : ℕ) (b : S.Gam), ρ.pt (c • b) = ρ.pt b ^ c := real_pt_nsmul ρ
  have hpt0 : ρ.pt 0 = 1 := by simpa using hpt 0 0
  have hzero : ∀ b : S.Gam, (S.r * S.N) • b = 0 := by
    intro b; funext i; simp [nsmul_eq_mul]
  have hN : Odd S.N := by rw [ρ.N_eq]; exact (ρ.n_odd.pow).pow
  have hx : ρ.pt (S.r • a) ^ S.N = 1 := by
    rw [← hpt, smul_smul, show S.N * S.r = 1 * (S.r * S.N) by ring, mul_smul, hzero, smul_zero, hpt0]
  have hM : ρ.pt (S.r • a) ^ (S.r * S.N) = 1 := by
    rw [← hpt, smul_smul, show S.r * S.N * S.r = S.r * (S.r * S.N) by ring, mul_smul, hzero, smul_zero, hpt0]
  have hev : ∀ (i : S.J) (b : S.Gam), IsValueAt ρ.P.A ρ.P.L (S.N : ℤ) (ρ.s i) (ρ.pt b)
      (powFrame ρ.P.A ρ.P.L (ρ.pt b) (ρ.fr b) S.N) (fn (⟨S.ev b i, S.ev_mem b i⟩ : S.R)) := by
    intro i b; have := ρ.ev_val i; unfold IsEvT at this; exact this b
  obtain ⟨y, φ, hφi, hφ⟩ := exists_injective_stalk_hom_gs_eq S
  obtain ⟨ξ1, hξ1, H1⟩ := GlobalTheory.ZH.EvCrd.exists_root_stalk hG ρ.P (T := baseOver (Sp S.R)) (N := S.N)
    (M := S.r * S.N) hN (rig := ρ.rig) (x := ρ.pt (S.r • a)) (h := ρ.pt x) (w := ρ.pt (S.r • a + x)) hx hM
    (ρ.pt_add _ _) (θ := ρ.U a) (ρ.U_sym a) (ρ.fr_tors x) (ρ.fr_tors (S.r • a + x)) y
  have E1 := H1 S.J ρ.s (ρ.s ρ.i₀) (fun l => fn (algebraMap o S.R (S.ρ a l ρ.i₀)))
    (fun l => fn (⟨S.ev x l, S.ev_mem x l⟩ : S.R)) (fn (⟨S.ev (S.r • a + x) ρ.i₀, S.ev_mem _ _⟩ : S.R))
    (ρ.U_act a ρ.i₀) (fun l => hev l x) (hev ρ.i₀ _)
  obtain ⟨ξ2, hξ2, H2⟩ := exists_root_stalk_pull hG ρ.P (T := baseOver (Sp S.R)) (N := S.N) (M := S.r * S.N)
    (m := ρ.n ^ ρ.k) (rig := ρ.rig) (α := ρ.α) ρ.α_gen ρ.α_norm (h := ρ.pt (S.r • a + x))
    (w := ρ.pt ((ρ.n ^ ρ.k) • (S.r • a + x))) (hpt _ _) (ρ.fr_tors _) (ρ.fr_tors _) (th := ρ.th₁)
    (s := ρ.s ρ.i₀) ρ.s_zero (hev ρ.i₀ _) (ρ.th_val _) y
  simp only [hφ] at E1 H2
  rw [Finset.sum_eq_single j (fun l _ hl => by rw [ha l, if_neg hl]; simp)
    (fun hj => absurd (Finset.mem_univ j) hj)] at E1
  rw [ha j, if_pos rfl] at E1
  set K := (S.r * S.N) ^ 2 with hK
  have hKpos : 0 < K := by
    have := S.r_pos; have := S.N_ge; positivity
  have hu1 := congrArg Units.val hξ1
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hu1
  have hu2 := congrArg Units.val hξ2
  rw [Units.val_pow_eq_pow_val, Units.val_one] at hu2
  have hR : (algebraMap o S.R (S.ζ ^ e) * ⟨S.ev x j, S.ev_mem x j⟩) ^ K =
      (⟨S.th ((ρ.n ^ ρ.k) • (S.r • a + x)), S.th_mem _⟩ : S.R) ^ K := by
    apply hφi
    rw [map_pow, map_mul, E1, H2, map_pow, mul_pow, mul_pow, hu1, hu2, _root_.one_mul, _root_.one_mul]
  have hz : (algebraMap o Ω S.ζ) ^ K = 1 := by rw [hK, ← map_pow, S.prim.pow_eq_one, map_one]
  have hΩ := congrArg (fun z : S.R => (z : Ω)) hR
  simp only [SubmonoidClass.coe_pow, Subalgebra.coe_mul, Subalgebra.coe_algebraMap] at hΩ
  rw [mul_pow, map_pow, ← pow_mul, _root_.mul_comm e, pow_mul, hz, one_pow, _root_.one_mul] at hΩ
  obtain ⟨u, hu, hux⟩ := exists_rootOfUnity_mul_of_pow_eq_pow _ _ K hKpos hΩ
  exact ⟨_, u, K, hKpos, hu, hux⟩

end GlobalTheory.ZH.EvRoot
end
