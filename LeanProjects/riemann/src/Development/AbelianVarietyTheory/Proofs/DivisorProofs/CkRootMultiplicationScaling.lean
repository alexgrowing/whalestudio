import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkUniqueCharacterizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoDivisorClassRootStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsoFlagLiftExistsStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CkSMulRoot

theorem ck_flagPair_smul (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ)
    [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (Z : GlobalTheory.Vert.Model O)
    (hZ : GlobalTheory.IsNormalScheme Z.X) (E : Z.X.Modules) (r k : ℕ) (hE : GlobalTheory.VB.IsVB E r)
    (φ : Z.GenIso E E) (hφ : φ = GlobalTheory.Vert.Model.GenIso.smul E (p : O) (GlobalTheory.Vert.natCast_ne_zero O p))
    (P' : GlobalTheory.Vert.Model.FlagPair φ r) (Q : PicSym Z.X) :
    ck (P'.toFPair p) k Q = k * (Z.toITh p).capDeg (Z.toITh p).divP
      ((∑ i, c1 (P'.fl.root i) (P'.fl.isLB_root i) ^ (k - 1)) * Q) := by
  subst hφ
  have hI := (GlobalTheory.T.ck_unique_characterization O p Z hZ E E
    (GlobalTheory.Vert.Model.GenIso.smul E (p : O) (GlobalTheory.Vert.natCast_ne_zero O p)) r k hE hE).2.2
  rw [← hI P' Q, hI (GlobalTheory.Vert.Model.FlagPair.ofSMul P'.fl _ (GlobalTheory.Vert.natCast_ne_zero O p)) Q,
    GlobalTheory.RootChernRules.ck_scalar _ 1 (fun i => by
      rw [one_smul]; exact GlobalTheory.Vert.Model.FlagPair.toFPair_ofSMul_Dv (p := p) (fl := P'.fl) i),
    mul_one]
  rfl

theorem isRootOfP_appTop {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}
    [Fact p.Prime] {Z Z₁ : GlobalTheory.Vert.Model O} (f : Z₁.X ⟶ Z.X) {g : Γ(Z.X, ⊤)} {a : ℕ}
    (hg : IsRootOfP p g a) : IsRootOfP p (f.appTop g) a := by
  obtain ⟨u, hu⟩ := hg
  refine ⟨Units.map f.appTop.hom.toMonoidHom u, ?_⟩
  rw [← map_pow, hu, map_mul, map_natCast]
  rfl

theorem ck_smul_root : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (P : Pres B) (g : Γ(B.X, ⊤)) (a : ℕ) (e : P.E' ≅ P.E), IsRootOfP p g a → P.ψ = e.hom ≫ smulHom P.E g → ∀ k : ℕ, (a : ℚ) • P.ck p k = ckP p (GlobalTheory.Vert.Model.GenIso.smul P.E (p : O) (GlobalTheory.Vert.natCast_ne_zero O p)) P.r k ∧ ∀ (fl : GlobalTheory.Vert.Flag P.E P.r) (Q : PicSym B.X), ckP p (GlobalTheory.Vert.Model.GenIso.smul P.E (p : O) (GlobalTheory.Vert.natCast_ne_zero O p)) P.r k Q = k * (B.toITh p).capDeg (B.toITh p).divP ((∑ i, c1 (fl.root i) (fl.isLB_root i) ^ (k - 1)) * Q) := by
  intro O _ _ _ p _ _ _ B hB P g a e hg hψ k
  have h0 := GlobalTheory.Vert.natCast_ne_zero O p
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso
      subst h
      obtain ⟨u, hu⟩ := hg
      rw [pow_zero] at hu
      have hpu : IsUnit (B.const (p : O)) := by
        rw [show B.const (p : O) = (p : Γ(B.X, ⊤)) from map_natCast _ _]
        exact isUnit_iff_exists_inv.2 ⟨(u : Γ(B.X, ⊤)), (mul_comm _ _).trans hu.symm⟩
      obtain ⟨x, hx⟩ := B.exists_notMem_gen
      apply hx
      rw [B.gen_eq_basicOpen h0 (GlobalTheory.Vert.natCast_mem_maximalIdeal O p),
        B.X.basicOpen_of_isUnit hpu]
      trivial
    · exact h
  haveI := P.iso
  have hI := GlobalTheory.T.ck_unique_characterization O p B hB P.E P.E (GlobalTheory.Vert.Model.GenIso.smul P.E (p : O) h0) P.r k P.vb P.vb
  have hJ := GlobalTheory.T.ck_unique_characterization O p B hB P.E P.E' (GlobalTheory.Vert.Model.GenIso.ofHom P.ψ) P.r k P.vb P.vb'
  refine ⟨?_, fun fl Q => ?_⟩
  swap
  · rw [hI.2.2 (GlobalTheory.Vert.Model.FlagPair.ofSMul fl _ h0) Q]
    exact ck_flagPair_smul O p B hB P.E P.r k P.vb _ rfl (GlobalTheory.Vert.Model.FlagPair.ofSMul fl _ h0) Q
  show (a : ℚ) • ckP p (GlobalTheory.Vert.Model.GenIso.ofHom P.ψ) P.r k = _
  refine hI.2.1 _ fun M hMn hMr Q => ?_

  have hA := ck_flagPair_smul O p M.B hMn _ P.r k (P.vb.pullback _) _
    (GlobalTheory.Vert.Model.GenIso.pull_smul M.π.comp_str (p : O) h0) M.pair (picSymPull M.π.f Q)

  have hinv : ((GlobalTheory.Vert.Model.GenIso.ofHom P.ψ).pull M.π.comp_str).inv =
      M.B.genRes.map (((Scheme.Modules.pullback M.π.f).mapIso e).hom ≫
        smulHom _ (M.π.f.appTop g)) := by
    rw [GlobalTheory.Vert.Model.GenIso.pull_inv M.π.comp_str (ψ := P.ψ) rfl, hψ, Functor.map_comp,
      VB.pullback_map_smulHom]
    rfl
  obtain ⟨Pψ, hfl, hgr⟩ := GlobalTheory.T.generic_iso_flag_lift_exists O p M.B _ _ P.r _ _ _ a ha
    (isRootOfP_appTop M.π.f hg) hinv M.pair.fl
  have hDv : ∀ i, (Pψ.toFPair p).Dv i = ((a : ℚ)⁻¹) • (M.B.toITh p).divP := by
    intro i
    obtain ⟨ei, hei⟩ := hgr i
    have hd := GlobalTheory.T.generic_iso_divisor_class_root O p M.B _ _ 1 (Pψ.fl.isVB_gr i) (Pψ.fl'.isVB_gr i)
      (Pψ.grIso i) ei _ a ha (isRootOfP_appTop M.π.f hg) hei
    have hq : (a : ℚ) • (Pψ.toFPair p).Dv i = (M.B.toITh p).divP := by
      change (a : ℚ) • GlobalTheory.Vert.Model.toQ (Pψ.div i).cls = GlobalTheory.Vert.Model.toQ (M.B.divP p)
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul]
      exact congrArg GlobalTheory.Vert.Model.toQ (hd.trans (one_nsmul _))
    rw [← hq, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 ha.ne'), one_smul]
  have hB' := GlobalTheory.RootChernRules.ck_scalar (Pψ.toFPair p) _ hDv k (picSymPull M.π.f Q)
  have hC := hJ.1 ⟨M.B, M.π, Pψ⟩ hMn hMr Q
  change ck (Pψ.toFPair p) k _ = M.π.fibreDeg 1 * _ at hC
  change ck (M.toFPair p) k _ = _
  rw [show M.toFPair p = M.pair.toFPair p from rfl, hA, LinearMap.smul_apply, smul_eq_mul]
  have hS : (∑ i, (M.B.toITh p).c1 ((Pψ.toFPair p).x i) ^ (k - 1)) =
      ∑ i, c1 (M.pair.fl.root i) (M.pair.fl.isLB_root i) ^ (k - 1) := by
    rw [← hfl]; rfl
  rw [hS, hC] at hB'
  have haq : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  rw [← mul_assoc, mul_comm (M.π.fibreDeg 1) (a : ℚ), mul_assoc, hB']
  field_simp

end GlobalTheory.CkSMulRoot

end
