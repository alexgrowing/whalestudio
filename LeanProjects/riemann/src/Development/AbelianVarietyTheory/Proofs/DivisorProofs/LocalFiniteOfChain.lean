import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkUniqueCharacterizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkAdditiveCompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkRootMultiplicationScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkChainPeriodicRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeFinitePullbackStatement

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.MixedLocalChains.ChainFin

private theorem phiPow_eq_iterate (D : D7) {p : ℕ} [Fact p.Prime] (m : ℕ) (τ : Emb D p) :
    phiPow D m τ = (phiPow D (p := p) 1)^[m] τ := by
  induction m with
  | zero => ext x; simp [phiPow]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ← ih]
    ext x
    simp [phiPow, pow_succ']

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem pull_cDQ {Zn : NModel O} (C : Zn.Comp) {B : GlobalTheory.Vert.Model O} (f : GlobalTheory.Vert.Model.Hom B (Zn.comp C))
    (D : Zn.VDivQ) : picSymPull f.f (picSymPull (Zn.compι C) (Zn.cDQ D)) =
      B.cDQ (GlobalTheory.Vert.Model.vPullQ f.comp_str (NModel.vResQ C D)) := by
  induction D using TensorProduct.induction_on with
  | zero => simp
  | tmul a D =>
    have h : a ⊗ₜ[ℤ] D = a • NModel.toQ D := by simp [NModel.toQ, TensorProduct.smul_tmul']
    rw [h, map_smul, map_smul, map_smul, map_smul, map_smul, map_smul, NModel.cDQ_toQ, NModel.vResQ_toQ,
      GlobalTheory.Vert.Model.vPullQ_toQ, GlobalTheory.Vert.Model.cDQ_toQ, picSymPull_c1Pic, picSymPull_c1Pic,
      GlobalTheory.Vert.Model.vCls_vPull, NModel.vCls_vRes]
  | add a b ha hb => simp only [map_add, ha, hb]

variable (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

private theorem pull_divP {Zn : NModel O} (C : Zn.Comp) {B : GlobalTheory.Vert.Model O} (f : GlobalTheory.Vert.Model.Hom B (Zn.comp C)) :
    GlobalTheory.Vert.Model.vPullQ f.comp_str (NModel.vResQ C (NModel.toQ (Zn.divP p))) = GlobalTheory.Vert.Model.toQ (B.divP p) := by
  rw [NModel.vResQ_toQ, NModel.divP, NModel.vRes_div, GlobalTheory.Vert.Model.vPullQ_toQ, GlobalTheory.Vert.Model.vPull_div]
  rfl

private theorem capDeg_eq_inv {Zn : NModel O} (C : Zn.Comp) {B : GlobalTheory.Vert.Model O} (f : GlobalTheory.Vert.Model.Hom B (Zn.comp C))
    (hf : f.relDim = 0) (D : (Zn.comp C).VDivQ) (Q : PicSym (Zn.comp C).X) :
    (Zn.comp C).capDeg_vp p D Q = (f.fibreDeg 1)⁻¹ * B.capDeg_vp p (GlobalTheory.Vert.Model.vPullQ f.comp_str D) (picSymPull f.f Q) := by
  obtain ⟨hpos, h⟩ := GlobalTheory.T.cap_degree_finite_pullback O p (Zn.comp C) (GlobalTheory.IsNormalScheme.opens (X := Zn.X) C.opens) B f hf
  rw [h D Q, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

end GlobalTheory.MixedLocalChains.ChainFin

namespace GlobalTheory.MixedLocalChains.ChainFin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

private theorem comp_ck {Zn : NModel O} {d r : ℕ} (F : FPair (Zn.toITh p d) r) (C : Zn.Comp)
    {B : GlobalTheory.Vert.Model O} (f : GlobalTheory.Vert.Model.Hom B (Zn.comp C)) (hf : f.relDim = 0) (hB : GlobalTheory.IsNormalScheme B.X)
    {E E' : B.X.Modules} (φ : B.GenIso E E') (hE : GlobalTheory.VB.IsVB E r) (hE' : GlobalTheory.VB.IsVB E' r)
    (P : GlobalTheory.Vert.Model.FlagPair φ r)
    (hP : ∀ i, picSymPull f.f (picSymPull (Zn.compι C) ((Zn.toITh p d).c1 (F.x i))) = (B.toITh p).c1 ((P.toFPair p).x i) ∧
      GlobalTheory.Vert.Model.vPullQ f.comp_str (NModel.vResQ C (F.Dv i)) = (P.toFPair p).Dv i)
    (k : ℕ) (Q : PicSym Zn.X) :
    ∑ i, (Zn.comp C).capDeg_vp p (NModel.vResQ C (F.Dv i))
        (picSymPull (Zn.compι C) (Gk _ k ((Zn.toITh p d).c1 (F.x i)) ((Zn.toITh p d).c1 (F.x' i)) * Q)) =
      (f.fibreDeg 1)⁻¹ * ckP p φ r k (picSymPull f.f (picSymPull (Zn.compι C) Q)) := by
  rw [(GlobalTheory.T.ck_unique_characterization O p B hB E E' φ r k hE hE').2.2 P, Formalism.BasicNotions.DV.ck, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [capDeg_eq_inv p C f hf, (hP i).2]
  refine congrArg (fun x => (f.fibreDeg 1)⁻¹ * B.capDeg_vp p ((P.toFPair p).Dv i) x) ?_
  have hx' : picSymPull f.f (picSymPull (Zn.compι C) ((Zn.toITh p d).c1 (F.x' i))) =
      (B.toITh p).c1 ((P.toFPair p).x' i) := by
    rw [F.hx i, (P.toFPair p).hx i, map_sub, map_sub, (hP i).1]
    congr 1
    exact (pull_cDQ C f _).trans (congrArg B.cDQ (hP i).2)
  simp only [Gk, map_mul, map_sum, map_pow, (hP i).1, hx']

private theorem comp_chDiv {Zn : NModel O} {d r : ℕ} (F : FPair (Zn.toITh p d) r) (C : Zn.Comp)
    {B : GlobalTheory.Vert.Model O} (f : GlobalTheory.Vert.Model.Hom B (Zn.comp C)) (hf : f.relDim = 0) (hB : GlobalTheory.IsNormalScheme B.X)
    {E E' : B.X.Modules} (φ : B.GenIso E E') (hE : GlobalTheory.VB.IsVB E r)
    (P : GlobalTheory.Vert.Model.FlagPair φ r)
    (hP : ∀ i, picSymPull f.f (picSymPull (Zn.compι C) ((Zn.toITh p d).c1 (F.x i))) = (B.toITh p).c1 ((P.toFPair p).x i))
    (k : ℕ) (Q : PicSym Zn.X) :
    (k : ℚ) * (Zn.comp C).capDeg_vp p (NModel.vResQ C (NModel.toQ (Zn.divP p)))
        (picSymPull (Zn.compι C) ((∑ l, (Zn.toITh p d).c1 (F.x l) ^ (k - 1)) * Q)) =
      (f.fibreDeg 1)⁻¹ * ckP p (GlobalTheory.Vert.Model.GenIso.smul E (p : O) (GlobalTheory.Vert.natCast_ne_zero O p)) r k
        (picSymPull f.f (picSymPull (Zn.compι C) Q)) := by
  let Pr : Pres B := ⟨r, E, E, hE, hE, smulHom E (B.const (p : O)),
    GlobalTheory.Vert.Model.isIso_genRes_map_smulHom E (GlobalTheory.Vert.natCast_ne_zero O p)⟩
  have hroot : IsRootOfP p (B.const (p : O)) 1 := ⟨1, by simp [map_natCast]⟩
  have h := (GlobalTheory.T.ck_root_multiplication_scaling O p B hB Pr (B.const (p : O)) 1 (Iso.refl _) hroot (Category.id_comp _).symm k).2 P.fl
    (picSymPull f.f (picSymPull (Zn.compι C) Q))
  rw [h, capDeg_eq_inv p C f hf, pull_divP p C f]
  simp only [map_mul, map_sum, map_pow, hP]
  rw [mul_left_comm]
  rfl

end GlobalTheory.MixedLocalChains.ChainFin

namespace GlobalTheory.MixedLocalChains.ChainFin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

private theorem ck_eq_sum {Zn : NModel O} {d r : ℕ} (F : FPair (Zn.toITh p d) r) (s : Finset Zn.Comp)
    (hs : ∀ Dv Q', Zn.capDeg_vp p d Dv Q' = ∑ C ∈ s, (Zn.comp C).capDeg_vp p (NModel.vResQ C Dv) (picSymPull (Zn.compι C) Q'))
    (g : Zn.Comp → ℚ) (k : ℕ) (Q : PicSym Zn.X)
    (hg : ∀ C ∈ s, ∑ i, (Zn.comp C).capDeg_vp p (NModel.vResQ C (F.Dv i))
        (picSymPull (Zn.compι C) (Gk _ k ((Zn.toITh p d).c1 (F.x i)) ((Zn.toITh p d).c1 (F.x' i)) * Q)) = g C) :
    Formalism.BasicNotions.DV.ck F k Q = ∑ C ∈ s, g C := by
  rw [Formalism.BasicNotions.DV.ck]
  simp only [hs]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl hg)

private theorem cap_eq_sum {Zn : NModel O} {d : ℕ} (s : Finset Zn.Comp)
    (hs : ∀ Dv Q', Zn.capDeg_vp p d Dv Q' = ∑ C ∈ s, (Zn.comp C).capDeg_vp p (NModel.vResQ C Dv) (picSymPull (Zn.compι C) Q'))
    (g : Zn.Comp → ℚ) (k : ℕ) (Q : PicSym Zn.X)
    (hg : ∀ C ∈ s, (k : ℚ) * (Zn.comp C).capDeg_vp p (NModel.vResQ C (NModel.toQ (Zn.divP p)))
        (picSymPull (Zn.compι C) Q) = g C) :
    (k : ℚ) * (Zn.toITh p d).capDeg (Zn.toITh p d).divP Q = ∑ C ∈ s, g C := by
  change (k : ℚ) * Zn.capDeg_vp p d (NModel.toQ (Zn.divP p)) Q = _
  rw [hs, Finset.mul_sum]
  exact Finset.sum_congr rfl hg

end GlobalTheory.MixedLocalChains.ChainFin

namespace GlobalTheory.MixedLocalChains.ChainFin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

private theorem period_rat {Zn : NModel O} {d : ℕ} {ι : Type} (φ : ι → ι) (o : ℕ) (hper : ∀ τ, φ^[o] τ = τ) {rk rk' : ι → ℕ}
    (lie : ∀ τ, FPair (Zn.toITh p d) (rk τ)) (om : ∀ τ, FPair (Zn.toITh p d) (rk' τ))
    (hch : ∀ c : Zn.Comp, ∃ (B : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B (Zn.comp c))
      (Ch : Chain p B φ o), GlobalTheory.IsNormalScheme B.X ∧ f.relDim = 0 ∧ ∀ τ,
      (Ch.lw τ).r = rk τ ∧ (Ch.oo τ).r = rk' τ ∧
      Reads p (lie τ) (fun x => picSymPull f.f (picSymPull (Zn.compι c) x))
        (fun d => GlobalTheory.Vert.Model.vPullQ f.comp_str (NModel.vResQ c d))
        (haveI := (Ch.lw τ).iso; (GlobalTheory.Vert.Model.GenIso.ofHom (Ch.lw τ).ψ).symm) ∧
      Reads p (om τ) (fun x => picSymPull f.f (picSymPull (Zn.compι c) x))
        (fun d => GlobalTheory.Vert.Model.vPullQ f.comp_str (NModel.vResQ c d))
        (haveI := (Ch.oo τ).iso; GlobalTheory.Vert.Model.GenIso.ofHom (Ch.oo τ).ψ))
    (τ : ι) (k : ℕ) (Q : (Zn.toITh p d).Ch) :
    (1 - ((p : ℚ) ^ (o * k))⁻¹) * (Formalism.BasicNotions.DV.ck (lie τ) k Q + Formalism.BasicNotions.DV.ck (om τ) k Q +
      (k : ℚ) * (Zn.toITh p d).capDeg (Zn.toITh p d).divP
        ((∑ l, (Zn.toITh p d).c1 ((lie τ).x l) ^ (k - 1)) * Q) / ((p : ℚ) - 1)) =
      ∑ n ∈ Finset.range o, ((p : ℚ) ^ ((n + 1) * k))⁻¹ * ((k : ℚ) * (Zn.toITh p d).capDeg (Zn.toITh p d).divP
        ((∑ l, (Zn.toITh p d).c1 ((lie (φ^[n + 1] τ)).x l) ^ (k - 1)) * Q)) := by
  choose B f Ch hB using hch
  obtain ⟨s, hs⟩ : ∃ s : Finset Zn.Comp, ∀ Dv Q', Zn.capDeg_vp p d Dv Q' =
      ∑ C ∈ s, (Zn.comp C).capDeg_vp p (NModel.vResQ C Dv) (picSymPull (Zn.compι C) Q') :=
    ⟨_, NModel.capDeg_vp_eq_sum p _⟩
  let aQ : ∀ c, PicSym (B c).X := fun c => picSymPull (f c).f (picSymPull (Zn.compι c) Q)
  let w : Zn.Comp → ℚ := fun c => ((f c).fibreDeg 1)⁻¹
  let La : Zn.Comp → ι → ℚ := fun c τ' =>
    ckP p (GlobalTheory.Vert.Model.GenIso.smul ((Ch c).lw τ').E' (p : O) (GlobalTheory.Vert.natCast_ne_zero O p)) ((Ch c).lw τ').r k (aQ c)
  have hLie : Formalism.BasicNotions.DV.ck (lie τ) k Q = ∑ c ∈ s, w c * -(((Ch c).lw τ).ck p k (aQ c)) := by
    refine ck_eq_sum p (lie τ) s hs _ k Q fun c _ => ?_
    obtain ⟨hBn, hfr, hτ⟩ := hB c
    obtain ⟨hr, -, ⟨P, hP⟩, -⟩ := hτ τ
    haveI := ((Ch c).lw τ).iso
    refine (comp_ck p (lie τ) c (f c) hfr hBn (GlobalTheory.Vert.Model.GenIso.ofHom ((Ch c).lw τ).ψ).symm
      (hr ▸ ((Ch c).lw τ).vb') (hr ▸ ((Ch c).lw τ).vb) P (fun i => hP i) k Q).trans ?_
    have e := (GlobalTheory.T.ck_additive_composition _ p (B c) hBn _ _ _ (GlobalTheory.Vert.Model.GenIso.ofHom ((Ch c).lw τ).ψ) (Iso.refl _)
      ((Ch c).lw τ).r k ((Ch c).lw τ).vb ((Ch c).lw τ).vb' ((Ch c).lw τ).vb').2
    rw [← hr, e]
    rfl
  have hOm : Formalism.BasicNotions.DV.ck (om τ) k Q = ∑ c ∈ s, w c * ((Ch c).oo τ).ck p k (aQ c) := by
    refine ck_eq_sum p (om τ) s hs _ k Q fun c _ => ?_
    obtain ⟨hBn, hfr, hτ⟩ := hB c
    obtain ⟨-, hro, -, ⟨P, hP⟩⟩ := hτ τ
    haveI := ((Ch c).oo τ).iso
    refine (comp_ck p (om τ) c (f c) hfr hBn (GlobalTheory.Vert.Model.GenIso.ofHom ((Ch c).oo τ).ψ)
      (hro ▸ ((Ch c).oo τ).vb) (hro ▸ ((Ch c).oo τ).vb') P (fun i => hP i) k Q).trans ?_
    rw [← hro]
    rfl
  have hK : ∀ τ', (k : ℚ) * (Zn.toITh p d).capDeg (Zn.toITh p d).divP
      ((∑ l, (Zn.toITh p d).c1 ((lie τ').x l) ^ (k - 1)) * Q) = ∑ c ∈ s, w c * La c τ' := by
    intro τ'
    refine cap_eq_sum p s hs _ k _ fun c _ => ?_
    obtain ⟨hBn, hfr, hτ⟩ := hB c
    obtain ⟨hr, -, ⟨P, hP⟩, -⟩ := hτ τ'
    haveI := ((Ch c).lw τ').iso
    refine (comp_chDiv p (lie τ') c (f c) hfr hBn (GlobalTheory.Vert.Model.GenIso.ofHom ((Ch c).lw τ').ψ).symm
      (hr ▸ ((Ch c).lw τ').vb') P (fun i => (hP i).1) k Q).trans ?_
    rw [← hr]
  have hc : ∀ c, (1 - ((p : ℚ) ^ (o * k))⁻¹) * (((Ch c).oo τ).ck p k (aQ c) - ((Ch c).lw τ).ck p k (aQ c) +
      ((p : ℚ) - 1)⁻¹ * La c τ) = ∑ n ∈ Finset.range o, ((p : ℚ) ^ ((n + 1) * k))⁻¹ * La c (φ^[n + 1] τ) := by
    intro c
    have hBn := (hB c).1
    have h := GlobalTheory.T.ck_chain_periodic_relation _ p (B c) hBn ι φ o (Ch c) hper k
      (fun τ' => ckP p (GlobalTheory.Vert.Model.GenIso.smul ((Ch c).lw τ').E' (p : O) (GlobalTheory.Vert.natCast_ne_zero O p))
        ((Ch c).lw τ').r k) (fun _ => rfl) τ
    have h2 := LinearMap.congr_fun h (aQ c)
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sum_apply,
      smul_eq_mul] at h2
    exact h2
  simp only [hLie, hOm, hK]
  rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  simp only [Finset.mul_sum]
  refine Eq.trans ?_ Finset.sum_comm.symm
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show ∀ x y z a b : ℚ, a * (x * -y + x * z + x * b / ((p : ℚ) - 1)) = x * (a * (z - y + ((p : ℚ) - 1)⁻¹ * b))
    from fun x y z a b => by ring, hc c, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

end GlobalTheory.MixedLocalChains.ChainFin

namespace GlobalTheory.MixedLocalChains.ChainFin

private theorem localFin_of_rat {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : DV.Mdl D p N rk) (o : ℕ)
    (h : ∀ (τ : Emb D p) (k : ℕ) (Q : M.Z.Ch),
      (1 - ((p : ℚ) ^ (o * k))⁻¹) * (Formalism.BasicNotions.DV.ck (M.lie τ) k Q + Formalism.BasicNotions.DV.ck (M.om τ) k Q +
        (k : ℚ) * M.Z.capDeg M.Z.divP ((∑ l, M.Z.c1 ((M.lie τ).x l) ^ (k - 1)) * Q) / ((p : ℚ) - 1)) =
      ∑ n ∈ Finset.range o, ((p : ℚ) ^ ((n + 1) * k))⁻¹ * ((k : ℚ) * M.Z.capDeg M.Z.divP
        ((∑ l, M.Z.c1 ((M.lie ((phiPow D (p := p) 1)^[n + 1] τ)).x l) ^ (k - 1)) * Q))) : LocalFin M o := by
  intro τ k hk Q
  have hq := congrArg (fun x : ℚ => (x : ℝ) / (Nat.factorial k : ℝ)) (h τ k Q)
  have hf : (Nat.factorial k : ℝ) = k * (Nat.factorial (k - 1) : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega)).symm
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have key : ∀ a : ℝ, a / (Nat.factorial (k - 1) : ℝ) = k * a / (Nat.factorial k : ℝ) := fun a => by
    rw [hf, mul_div_mul_left _ _ hk0]
  simp only [Rat.cast_mul, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_one, Rat.cast_sum, Finset.sum_div] at hq
  unfold chk chDiv
  refine Eq.trans ?_ (hq.trans (Finset.sum_congr rfl fun n _ => ?_))
  · rw [key]; ring
  · rw [key, phiPow_eq_iterate D (n + 1) τ]; ring

private theorem localFin_of_hasChain : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) [Fact p.Prime] (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ), ∀ o : ℕ, (∀ τ : Emb D p, (phiPow D (p := p) 1)^[o] τ = τ) → HasChain z jc o → LocalFin (mdlOf z jc) o := by
  intro D A N j S κ p _ hp W hW z jc o hper hch
  refine localFin_of_rat (mdlOf z jc) o ?_
  exact
    haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
    haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
    period_rat p (Zn := nmodel z.Z) (d := dimFl D.what₂.Tau N) (phiPow D (p := p) 1) o hper
      (mdlOf z jc).lie (mdlOf z jc).om hch

end GlobalTheory.MixedLocalChains.ChainFin

theorem _root_.GlobalTheory.T.local_finite_of_chain : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) [Fact p.Prime] (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ), ∀ o : ℕ, (∀ τ : Emb D p, (phiPow D (p := p) 1)^[o] τ = τ) → HasChain z jc o → LocalFin (mdlOf z jc) o :=
  GlobalTheory.MixedLocalChains.ChainFin.localFin_of_hasChain

end
