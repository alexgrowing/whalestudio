import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QDivBdQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MbarSectionsCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorRelation

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.CovHt.Link.FrameLog

theorem grp_key {G : Type} [CommGroup G] {ι : Type} (s : Finset ι) (g0 : G) (E T : ι → G) (m0 q0 : ℤ) (m q t : ι → ℤ)
    (a c : ℕ) (h0 : m0 * a + q0 * c = 0) (h : ∀ i ∈ s, m i * a + q i * c = t i) :
    (g0 ^ m0 * ∏ i ∈ s, E i ^ m i) ^ a * (g0 ^ q0 * ∏ i ∈ s, E i ^ q i) ^ c * ∏ i ∈ s, (T i * (E i)⁻¹) ^ t i =
      ∏ i ∈ s, T i ^ t i := by
  have e1 : (g0 ^ m0 * ∏ i ∈ s, E i ^ m i) ^ a * (g0 ^ q0 * ∏ i ∈ s, E i ^ q i) ^ c =
      g0 ^ (m0 * a + q0 * c) * ∏ i ∈ s, E i ^ (m i * a + q i * c) := by
    rw [mul_pow, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
    simp only [← zpow_natCast, ← zpow_mul, zpow_add, Finset.prod_mul_distrib]
    ac_rfl
  rw [e1, h0, zpow_zero, one_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [h i hi, mul_zpow, inv_zpow', zpow_neg, mul_left_comm, mul_inv_cancel, mul_one]

section Val

variable {K : Type} [Field K] {Z : AlgebraicGeometry.Scheme.{0}} [AlgebraicGeometry.IsIntegral Z] (y : Sp K ⟶ Z)

theorem valAt_mul_unit {a u : Z.functionField} (hu : UnitAt (below y) u) :
    valAt y (a * u) = valAt y a * valAt y u := by
  by_cases ha : RegAt (below y) a
  · exact SmallSec.valAt_mul ha hu.regAt
  · have h2 : ¬ RegAt (below y) (a * u) := fun h => ha (by
      have := h.mul hu.inv.regAt
      rwa [mul_assoc, mul_inv_cancel₀ hu.ne_zero, mul_one] at this)
    simp [GlobalTheory.TrueGeo.valAt, ha, h2]

end Val

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

def frT (n : Letter Dw → ℤ) (b : Y.Y.X) : Y.Y.Fnˣ :=
  ∏ x : Letter Dw, (Y.gr_spec b).choose_spec.choose_spec.choose x.1 x.2 ^ n x

theorem isEqn_frT (n : Letter Dw → ℤ) (b : Y.Y.X) : (divOf Y n).IsEqn b (frT Y n b) := LineTest.isEqn_divOf Y n b

theorem frT_add (n n' : Letter Dw → ℤ) (b : Y.Y.X) : frT Y (n + n') b = frT Y n b * frT Y n' b := by
  rw [frT, frT, frT, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun x _ => zpow_add _ _ _

theorem unitAt_frT (n : Letter Dw → ℤ) (b : Y.Y.X) :
    UnitAt b ((frT Y n b * (eqn (divOf Y n) b)⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) := by
  have := (Base.isEqn_eqn (divOf Y n) b).iff_unitAt.1 (isEqn_frT Y n b)
  rwa [div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul] at this

def lgLin (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) : ℝ :=
  lgOf Y w v ε y - Real.log (ε.w (valAt y.1 ((frT Y (expo Dw w) (below y.1) *
    (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn)))

theorem lgOf_eq (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) :
    lgOf Y w v ε y = Real.log (ε.w (valAt y.1 ((frT Y (expo Dw w) (below y.1) *
      (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) + lgLin Y w v ε y := by
  rw [lgLin]; ring

theorem log_valAt_mul {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v) (y : AlgPt Y.Y) {a b : Y.Y.Fn}
    (ha : UnitAt (below y.1) a) (hb : UnitAt (below y.1) b) :
    Real.log (ε.w (valAt y.1 (a * b))) = Real.log (ε.w (valAt y.1 a)) + Real.log (ε.w (valAt y.1 b)) := by
  rw [SmallSec.valAt_mul ha.regAt hb.regAt, map_mul,
    Real.log_mul (ε.w.pos (SmallSec.valAt_ne_zero ha)).ne' (ε.w.pos (SmallSec.valAt_ne_zero hb)).ne']

theorem lgLin_add (w₁ w₂ : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) :
    lgLin Y (w₁ + w₂) v ε y = lgLin Y w₁ v ε y + lgLin Y w₂ v ε y := by
  have hE : (divOf Y (expo Dw (w₁ + w₂))).IsEqn (below y.1)
      (eqn (divOf Y (expo Dw w₁)) (below y.1) * eqn (divOf Y (expo Dw w₂)) (below y.1)) := by
    rw [LineTest.expo_add, LineTest.divOf_add]; exact (Base.isEqn_eqn _ _).add (Base.isEqn_eqn _ _)
  have Uc : UnitAt (below y.1) ((eqn (divOf Y (expo Dw w₁)) (below y.1) * eqn (divOf Y (expo Dw w₂)) (below y.1) *
      (eqn (divOf Y (expo Dw (w₁ + w₂))) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) := by
    have := (Base.isEqn_eqn _ _).iff_unitAt.1 hE
    rwa [div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul] at this
  have U₁ := unitAt_frT Y (expo Dw w₁) (below y.1)
  have U₂ := unitAt_frT Y (expo Dw w₂) (below y.1)
  have e : frT Y (expo Dw (w₁ + w₂)) (below y.1) * (eqn (divOf Y (expo Dw (w₁ + w₂))) (below y.1))⁻¹ =
      frT Y (expo Dw w₁) (below y.1) * (eqn (divOf Y (expo Dw w₁)) (below y.1))⁻¹ *
        (frT Y (expo Dw w₂) (below y.1) * (eqn (divOf Y (expo Dw w₂)) (below y.1))⁻¹) *
        (eqn (divOf Y (expo Dw w₁)) (below y.1) * eqn (divOf Y (expo Dw w₂)) (below y.1) *
          (eqn (divOf Y (expo Dw (w₁ + w₂))) (below y.1))⁻¹) := by
    rw [LineTest.expo_add Dw w₁ w₂, frT_add, ← LineTest.expo_add]
    exact GlobalTheory.CombInd.Tens.commGroup_coboundary_relation_identity _ _ _ _ _
  have h := GlobalTheory.CombInd.Tens.lgOf_add Y w₁ w₂ v ε y
  simp only [lgLin]
  rw [e, Units.val_mul, Units.val_mul, log_valAt_mul Y ε y (U₁.mul U₂) Uc, log_valAt_mul Y ε y U₁ U₂, h]
  ring

def lgLinHom (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) : (Sym E →₀ ℤ) →+ ℝ :=
  AddMonoidHom.mk' (fun w => lgLin Y w v ε y) fun w₁ w₂ => lgLin_add Y w₁ w₂ v ε y

theorem lgLin_sum {ι : Type} (s : Finset ι) (c : ι → ℤ) (w : ι → Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v)
    (y : AlgPt Y.Y) : lgLin Y (∑ i ∈ s, c i • w i) v ε y = ∑ i ∈ s, (c i : ℝ) * lgLin Y (w i) v ε y := by
  have := map_sum (lgLinHom Y v ε y) (fun i => c i • w i) s
  simp only [map_zsmul, zsmul_eq_mul] at this
  exact this

end Free

section Comb

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {ι : Type} [Fintype ι] (ρ : ι → Adl (cxSt F) Y) (t : ι → ℚ)
  (g : ∀ σ, Pts Y σ → ℝ)

theorem nrmFin_comb (v : HeightOneSpectrum (𝓞 F)) (τ : ℕ) (f : Y.Fn) (e : Ext v) (y : AlgPt Y) :
    (comb ρ t g).nrmFin v τ f e y =
      e.w (valAt y.1 (f ^ (combDen ρ t : ℕ) * (combEqn ρ t (below y.1) : Y.Fn) ^ τ)) ^ (1 / ((combDen ρ t : ℕ) : ℝ)) *
        Real.exp (τ * (∑ i, (combNum ρ t i : ℝ) * (ρ i).lg v e y) / (combDen ρ t : ℕ)) := by
  have hq : UnitAt (below y.1) ((combEqn ρ t (below y.1) : Y.Fn) / eqn (comb ρ t g).D (below y.1)) :=
    (Base.isEqn_eqn _ _).iff_unitAt.1 (isEqn_combEqn ρ t (below y.1))
  have e1 : f ^ (combDen ρ t : ℕ) * (combEqn ρ t (below y.1) : Y.Fn) ^ τ =
      f ^ (combDen ρ t : ℕ) * (eqn (comb ρ t g).D (below y.1) : Y.Fn) ^ τ *
        ((combEqn ρ t (below y.1) : Y.Fn) / eqn (comb ρ t g).D (below y.1)) ^ τ := by
    have := (eqn (comb ρ t g).D (below y.1)).ne_zero
    rw [div_pow, mul_assoc, mul_div_cancel₀ _ (pow_ne_zero _ this)]
  have hB := e.w.pos (SmallSec.valAt_ne_zero hq)
  rw [e1, valAt_mul_unit _ (ApproxSec.unitAt_pow hq τ), SmallSec.valAt_pow hq.regAt, map_mul, map_pow,
    Real.mul_rpow (e.w.nonneg _) (pow_nonneg (e.w.nonneg _) _), ← Real.rpow_natCast, ← Real.rpow_mul (e.w.nonneg _),
    Real.rpow_def_of_pos hB, mul_assoc, ← Real.exp_add, Adl.nrmFin]
  congr 2
  simp only [GlobalTheory.ShFam.comb]
  ring

end Comb

section Bd

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} {Φ : s.Flag}
  {hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)} {h0 : RefMets Φ}

theorem eff_bdQ (P : PolDat s Φ hm h0) (k : s.Comp) : (bdQ P k).D.Eff := by
  have hn : ((((bdQ P k).n : ℕ)) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (bdQ P k).n.ne_zero
  have h1 : (1 : ℚ) ⊗ₜ[ℤ] (bdQ P k).D = 1 ⊗ₜ (((bdQ P k).n : ℕ) • P.bd k) := by
    have := congrArg ((((bdQ P k).n : ℕ) : ℚ) • ·) (qDiv_bdQ P k)
    simp only [qDiv, TensorProduct.smul_tmul', smul_eq_mul, mul_inv_cancel₀ hn, mul_one] at this
    rw [this, ← natCast_zsmul, ← TensorProduct.smul_tmul, zsmul_eq_mul, Int.cast_natCast, mul_one]
  obtain ⟨q, hq, e⟩ := one_tmul_eq_iff.1 h1
  refine CartierDiv.eff_iff.2 fun x g hg => ?_
  obtain ⟨b, hb⟩ := (P.bd k).exists_isEqn x
  have hb' := (hb.nsmul ((bdQ P k).n : ℕ)).nsmul q
  rw [← e] at hb'
  have hu := (hg.nsmul q).iff_unitAt.1 hb'
  have hr := CartierDiv.eff_iff.1 (P.eff_bd k) x b hb
  have hreg : RegAt x ((g : (Φ.C k).Y.Fn) ^ q) := by
    have h2 := ApproxSec.regAt_pow (ApproxSec.regAt_pow hr ((bdQ P k).n : ℕ)) q
    have h3 := hu.inv.regAt.mul h2
    have e2 : ((((b ^ ((bdQ P k).n : ℕ)) ^ q : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) /
        ((g ^ q : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn))⁻¹ * ((b : (Φ.C k).Y.Fn) ^ ((bdQ P k).n : ℕ)) ^ q =
        (g : (Φ.C k).Y.Fn) ^ q := by
      have := b.ne_zero
      have := g.ne_zero
      simp only [Units.val_pow_eq_pow_val]
      field_simp
    rwa [e2] at h3
  exact ApproxSec.regAt_of_pow (have := (Φ.C k).Y.isNormalScheme; inferInstance) hq hreg

end Bd

section Roots

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j)

theorem rootSym_eq_single (a : ℕ → Bool) (R : Option ℝ) (x : DV.Rt D.what₂.Tau N) :
    rootSym S.Dw a R (DV.tauEmb D x.1) x.2 = Finsupp.single (a, R, .inl ((RootSum.rootLetter S x).1,
      ((RootSum.rootLetter S x).2 : ℕ))) (if (x.2 : ℕ) < S.Dw.p then 1 else -1) := by
  have e := RootSum.rootLetter_key S x
  by_cases h : (x.2 : ℕ) < S.Dw.p
  · rw [if_pos h] at e
    rw [rootSym, if_pos h, if_pos h, e]
  · rw [if_neg h] at e
    rw [rootSym, if_neg h, if_neg h, e]

theorem drSym_eq (L : CmList A) (la : AllWt.Weight S.Dw) :
    drSym la = ∑ x : DV.Rt D.what₂.Tau N,
      (-(la (L.ψ x.1) (Fin.cast S.rank_eq.symm x.2))) • rootSym S.Dw (fun _ => false) none (DV.tauEmb D x.1) x.2 := by
  classical
  rw [drSym, ← Fintype.sum_bijective (RootSum.rootLetter S) (RootSum.rootLetter_bijective S)
    (fun x => Finsupp.single ((fun _ => false, none, .inl ((RootSum.rootLetter S x).1, ((RootSum.rootLetter S x).2 : ℕ))) :
      Sym D.host.E) (-exOf S.Dw la 0 (some (RootSum.rootLetter S x)))) _ (fun _ => rfl)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rootSym_eq_single, Finsupp.smul_single, smul_eq_mul]
  congr 1
  rw [← ApproxSec.sum_rootExp L la, Finset.sum_eq_single x]
  · rw [RootSum.rootExp_eq, if_pos rfl]
    split_ifs <;> ring
  · intro x' _ hx
    rw [RootSum.rootExp_eq, if_neg fun h => hx ((RootSum.rootLetter_bijective S).1 h.symm), mul_zero]
  · simp
end Roots

end GlobalTheory.CovHt.Link.FrameLog
