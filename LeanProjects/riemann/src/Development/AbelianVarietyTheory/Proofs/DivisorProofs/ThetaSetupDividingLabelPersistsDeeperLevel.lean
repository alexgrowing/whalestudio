import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsFrameTwoLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalPointCentredClosedPointArithmetic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadNonnegOfInt
import Development.AbelianVarietyTheory.Definitions.Divisors.IdlAlongNeTopOfValOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVector
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.DivDeep

theorem root_mem_O {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {z : M.Z}
    (hn : IsIntegrallyClosed (M.O z)) {u : Ω} {k : ℕ} (hk : 0 < k) (hu : u ^ k = 1) : u ∈ M.O z := by
  have hint : IsIntegral (M.O z) u := ⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z) hk.ne', by simp [hu]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← hy]
  exact y.2

theorem exists_eq_smul_of_smul_eq_zero {L k : ℕ} (hL : 0 < L) (hk : k ∣ L) (a : ZMod L) (ha : k • a = 0) :
    ∃ x : ZMod L, (L / k) • x = a := by
  obtain ⟨d, rfl⟩ := hk
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hL)
  haveI : NeZero (k * d) := ⟨hL.ne'⟩
  rw [Nat.mul_div_cancel_left _ hk]
  have h : ((k * a.val : ℕ) : ZMod (k * d)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul, ha]
  obtain ⟨e, he⟩ := Nat.dvd_of_mul_dvd_mul_left hk ((ZMod.natCast_eq_zero_iff _ _).1 h)
  exact ⟨e, by rw [nsmul_eq_mul, ← Nat.cast_mul, ← he, ZMod.natCast_zmod_val]⟩

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem exists_div_of_isLab (X : Setup F W i) {ε} {p : ℕ} [Fact p.Prime] {z : X.M.Z} (c : CTrait X p z) {yy}
    (h : IsLab X ε c yy) {k : ℕ} (hk : 2 ≤ k) (hd : k ∣ X.S.r * X.S.N) :
    ∃ a : X.S.Gam, k • a = 0 ∧ X.M.Div X.S.th a z := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, hle, y₀, hy₀, u, l, j, hq, -⟩ := h
  have hint : ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one c.cen ((X.M.O z).algebraMap_mem a)
  obtain ⟨sc, h0, h₁, -, h₃⟩ := TestVal.exists_scale GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 u l hint
  have hδ := (GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint).1
  have hle' : ∀ a, ‖y₀ ⟨c₀ * X.S.th a, hth a⟩‖ ≤ sc := fun a => by
    obtain ⟨w, -, hw⟩ := h₁ a
    refine hw.trans (mul_le_of_le_one_right h0 (Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg ?_ (by positivity)))))
    rw [hq]
    exact mul_nonneg c.scale_pos.le (by
      exact_mod_cast qW_nonneg_of_posW W X.posW c.T.β c.T.symm (Basic₂.trait_nonneg c.T) (j w))
  have hsc : 0 < sc := hδ.trans_le (Real.iSup_le hle' h0)
  obtain ⟨a, -, ha, hn⟩ := h₃ k hk hd 0 (zero_mem _)
  refine ⟨a, by simpa using ha, ?_⟩
  obtain ⟨d, hdv⟩ := X.div z
  refine (hdv.div_iff_isUnit a).2 ((RatModel.norm_val_eq_one_iff c.cen (hdv.2 a)).1 ?_)
  have hs := RatModel.gPt_specializes c.cen
  have e : ‖y₀ ⟨c₀ * X.S.th a, hth a⟩‖ =
      ‖y₀ ⟨c₀ * X.S.th d, hth d⟩‖ * ‖X.M.val (gPt p ≫ c.y) (X.S.th a / X.S.th d)‖ := by
    rw [hy₀, hy₀, ← norm_mul, ← RatModel.val_mul (z := (gPt p ≫ c.y) (closedPoint (PadicAlgCl p)))
      (fun w => by rw [Subsingleton.elim w (closedPoint (PadicAlgCl p))]) (hle (hth d))
      (RatModel.O_le_of_specializes (hs _) (hdv.2 a))]
    congr 2
    have := hdv.1
    field_simp
  have hn' : ‖y₀ ⟨c₀ * X.S.th a, hth a⟩‖ = sc := hn
  have b₁ := RatModel.norm_val_le_one c.cen (hdv.2 a)
  have b₂ := hle' d
  refine le_antisymm b₁ (not_lt.1 fun hlt => ?_)
  have := mul_le_mul_of_nonneg_right b₂ (norm_nonneg (X.M.val (gPt p ≫ c.y) (X.S.th a / X.S.th d)))
  nlinarith

theorem exists_div_torsion (X : Setup F W i) {ε} (hε : IsDiagEnd F W X.ρ.P X.u ε) (z : X.M.Z) {k : ℕ} (hk : 2 ≤ k)
    (hd : k ∣ X.S.r * X.S.N) : ∃ a : X.S.Gam, k • a = 0 ∧ X.M.Div X.S.th a z := by
  haveI := X.M.qc
  haveI := X.imm
  haveI : CompactSpace X.M.Z := QuasiCompact.compactSpace_of_compactSpace X.M.s
  obtain ⟨z', hz', hcl⟩ := (isClosed_closure (s := {z})).exists_closed_singleton ⟨z, subset_closure rfl⟩
  have hsp : z ⤳ z' := specializes_iff_mem_closure.2 hz'
  obtain ⟨p, _, y, hy, hU⟩ := exists_cen_main _ _ X.M z' hcl (X.π ⁻¹ᵁ i.opensRange)
    ⟨X.M.pt (closedPoint X.Ω₁), by
      show (X.M.pt ≫ X.π) _ ∈ Set.range i
      rw [X.comp]
      exact ⟨_, rfl⟩⟩
  obtain ⟨c, -⟩ := GCTrait.exists_cTrait g n F W Z i X X.one_le X.three_le X.odd X.imm p y (by
    rintro _ ⟨w, rfl⟩
    exact hU ⟨w, rfl⟩)
  obtain ⟨yy, hyy⟩ := exists_isLab g n F W Z i X X.one_le X.three_le X.odd X.imm X.e8 X.thetaInt X.projM ε hε p _ c
  obtain ⟨a, ha, hdv⟩ := exists_div_of_isLab X c hyy hk hd
  exact ⟨a, ha, hdv.of_specializes (hy ▸ hsp)⟩

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (z₁ : X₁.M.Z) (x₀ : X₁.S.Gam), x₀ ∈ X₁.S.supI X₁.M z₁ → ∀ (z' : D.X.M.Z), D.q z' = z₁ → D.X.M.Div D.X.S.th (D.lab x₀) z' := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ D z₁ x₀ hx₀ z' hz'
  have hx : X₁.M.Div X₁.S.th x₀ z₁ := hx₀
  have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N :=
    (D.dvd.trans (D.sq ▸ dvd_pow_self D.m two_ne_zero)).trans (dvd_mul_left _ _)
  obtain ⟨a, ha, hdv⟩ := exists_div_torsion D.X D.diag z'
    (X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)) hdvd
  have hL : 0 < D.X.S.r * D.X.S.N := Nat.mul_pos D.X.S.r_pos (by have := D.X.S.N_ge; omega)
  choose x hxa using fun s => exists_eq_smul_of_smul_eq_zero hL hdvd (a s) (congrFun ha s)
  obtain ⟨b, hb⟩ := D.lab_range x
  obtain rfl : D.lab b = a := hb.trans (funext hxa)
  obtain ⟨k, hk, e⟩ := same_ratio D.same x₀ b
  set φ := algebraMap X₁.Ω₁ D.X.Ω₁
  have h₁ : φ (X₁.S.th x₀) ≠ 0 := (map_ne_zero φ).2 hx.1
  have h₂ := hdv.1
  have h₃ : D.X.S.th (D.lab x₀) * φ (X₁.S.th b) ≠ 0 := fun h => by
    rw [h, zero_pow hk.ne'] at e
    exact pow_ne_zero k (mul_ne_zero h₂ h₁) e.symm
  have h₄ := left_ne_zero_of_mul h₃
  have h₅ := right_ne_zero_of_mul h₃
  have hN : IsIntegrallyClosed (D.X.M.O z') := RatModel.isIntegrallyClosed_O (fun z => by
    haveI := D.X.normal
    exact ⟨D.X.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩) z'
  have m₁ : D.X.S.th (D.lab b) * φ (X₁.S.th x₀) / (D.X.S.th (D.lab x₀) * φ (X₁.S.th b)) ∈ D.X.M.O z' :=
    root_mem_O hN hk (by rw [div_pow, e, div_self (pow_ne_zero k (mul_ne_zero h₂ h₁))])
  have m₂ : φ (X₁.S.th b / X₁.S.th x₀) ∈ D.X.M.O z' := by
    obtain ⟨U, f, hU, hf⟩ := hx.2 b
    refine ⟨D.q ⁻¹ᵁ U, D.q.app U f, show D.q z' ∈ U from hz' ▸ hU, ?_⟩
    refine (GlobalTheory.Points.valR_comp D.X.M.pt D.q U f).symm.trans ?_
    rw [D.gen, ← hf]
    exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hU⟩) f
  refine ⟨h₄, fun j => ?_⟩
  have := mul_mem (hdv.2 j) (mul_mem m₁ m₂)
  convert this using 1
  rw [map_div₀]
  field_simp

end GlobalTheory.Poinc.DivDeep
