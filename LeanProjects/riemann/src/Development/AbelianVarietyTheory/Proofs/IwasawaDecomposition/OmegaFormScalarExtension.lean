import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalNegFirstFamilyFrameCartanMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilVacuumFiniteSelfDualLatticeSplittingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUnitIsDetRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstOrtho
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymplecticBasesMatched
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSqGaussProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPointMovesAdelicThetaByDetCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormGaloisEquivariance
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.FrameConst

variable {D : D7} {S T : HSp D} {r : ℕ}

theorem le_of_isAA {k : ℕ} {Λ L L' : Lt D.host.E k} (h : GlobalTheory.Ker.IsAA Λ L) (h' : GlobalTheory.Ker.IsAA Λ L') : L ≤ L' := by
  intro u hu
  have hA := Formalism.L2.Pj.AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have key : ∀ b ∈ D.host.AA⁻¹, ∀ x ∈ Λ, b • x ∈ L' := by
    intro b hb x hx
    have hx' := (h' x).1 hx
    clear hx
    induction hx' using AddSubgroup.closure_induction with
    | mem v hv =>
      obtain ⟨a, ha, w, hw, rfl⟩ := hv
      have : b * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
        rw [← inv_mul_cancel₀ hA]; exact FractionalIdeal.mul_mem_mul hb ha
      obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 this
      rw [smul_smul, ← hz, algebraMap_smul]
      exact L'.smul_mem z hw
    | zero => simp
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | neg v _ hv => rw [smul_neg]; exact neg_mem hv
  have h1 : (1 : D.host.E) ∈ D.host.AA⁻¹ * D.host.AA := by
    rw [inv_mul_cancel₀ hA]; exact FractionalIdeal.one_mem_one _
  have : ∀ c ∈ D.host.AA⁻¹ * D.host.AA, c • u ∈ L' := by
    intro c hc
    refine FractionalIdeal.mul_induction_on hc (C := fun c => c • u ∈ L') ?_ ?_
    · intro b hb a ha
      rw [mul_smul]
      exact key b hb _ ((h _).2 (AddSubgroup.subset_closure ⟨a, ha, u, hu, rfl⟩))
    · intro x y hx hy
      rw [add_smul]; exact add_mem hx hy
  simpa using this 1 h1

theorem fmt_mul (g h : GA D T) : GlobalTheory.Ker.fmt T (g * h) = GlobalTheory.Ker.fmt T g * GlobalTheory.Ker.fmt T h := by
  change (finHom T (g * h)).1 = (finHom T g).1 * (finHom T h).1
  rw [map_mul, Units.val_mul]

theorem fmt_real {a : GA D T} (ha : a ∈ GinfC T) : GlobalTheory.Ker.fmt T a = 1 :=
  congrArg Units.val (show finHom T a = 1 from ha)

theorem isMov_one (L : Lt D.host.E T.rank) : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T 1) L L := by
  intro u
  rw [fmt_real (one_mem _)]
  simp only [Matrix.one_mulVec, exists_eq_right']

theorem isMov_quot {g g' a : GA D T} (ha : a ∈ GinfC T) {L L' : Lt D.host.E T.rank}
    (h : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T g) L L') (h' : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T g') L L') :
    GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T ((a * g)⁻¹ * g')) L L := by
  have e1 : GlobalTheory.Ker.fmt T g⁻¹ * GlobalTheory.Ker.fmt T g = 1 := by rw [← fmt_mul, inv_mul_cancel, fmt_real (one_mem _)]
  intro u
  rw [_root_.mul_inv_rev, fmt_mul, fmt_mul, fmt_real (inv_mem ha), mul_one]
  constructor
  · intro hu
    obtain ⟨u₀, h0, e⟩ := (h' _).1 ((h _).2 ⟨u, hu, rfl⟩)
    refine ⟨u₀, h0, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← e, Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
  · rintro ⟨u₀, h0, rfl⟩
    obtain ⟨u₁, h1, e⟩ := (h _).1 ((h' _).2 ⟨u₀, h0, rfl⟩)
    rw [← Matrix.mulVec_mulVec, e, Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
    exact h1

theorem eq_one_of_rat {θ : InfFam D} (hθ : IsInfFam θ) {δ : GA D T} (h1 : δ ∈ GQ T) (h2 : δ ∈ GfC T) : δ = 1 := by
  obtain ⟨ga, hga, hδ'⟩ := id h1
  have hm : Formalism.L2.Theta.mt T δ = (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map (incA D) :=
    (congrArg Units.val hδ').symm
  have h3 : (Formalism.L2.Theta.mt T δ).map (infPart D) = 1 := congrArg Units.val (show infHom T δ = 1 from h2)
  have ρ : D.what₂.Tau := D.eTau.symm 1
  have h4 : (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E) = 1 := by
    refine Matrix.ext fun i j => (tauE D ρ).injective ?_
    have h5 := congrArg (θ ρ) (congrFun (congrFun h3 i) j)
    rw [hm] at h5
    refine ((hθ ρ).1 _).symm.trans (h5.trans ?_)
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  refine Subtype.ext (Units.ext ?_)
  change Formalism.L2.Theta.mt T δ = 1
  rw [hm, h4, Matrix.map_one _ (map_zero _) (map_one _)]

theorem frOf_injective (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) {Z Z' : Fam T}
    (h : frOf hr eT Z = frOf hr eT Z') : Z = Z' := by
  subst hr
  funext ρ
  have := congrFun h (eT ρ)
  unfold frOf at this
  rw [Equiv.symm_apply_apply] at this
  exact this

theorem thR_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (a : ℂ) (φ : TF n g) (x : Frame X.Ψ r)
    (p : GlobalTheory.Ker.WR X n) : GlobalTheory.Ker.thR X bas idx (a • φ) x p = a * GlobalTheory.Ker.thR X bas idx φ x p := by
  simp only [GlobalTheory.Ker.thR, thA, SW.thS, show ∀ y, (a • φ) y = a * φ y from fun _ => rfl, _root_.mul_assoc, tsum_mul_left]
  ring

theorem hostHalfRoot_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have := congrArg (algebraMap (𝓞 E) E) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  rw [map_add, map_one] at this
  exact (congrArg _ (H.bar_eq _).symm).trans this

theorem isRelTraceOneIdempotentModTwo_hostElement {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) :
    GlobalTheory.Ker.IdemTwo (H.w0 : E) := by
  obtain ⟨k, hk⟩ : ∃ k, H.d = 16 * k + 7 := ⟨H.d / 16, by have := H.d_mod; omega⟩
  have h1 := hostHalfRoot_add_conj_eq_one H
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    rwa [map_mul, map_add, map_one, map_ofNat] at this
  have h3 : (H.rt : E) ^ 2 = -(16 * k + 7) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast, hk] at this
    exact this.trans (by push_cast; rfl)
  refine ⟨((2 * k + 1 : ℕ) : E), isIntegral_natCast _, ?_⟩
  rw [eq_sub_of_add_eq' h1]
  push_cast
  linear_combination (-(1 / 4 : E)) * h3 - (1 / 4 : E) * (2 * (H.w0 : E) - 1 + (H.rt : E)) * h2

theorem finUnit_one : FinUnit (1 : (AE D)ˣ) := by
  have : finPart D (1 : AE D) ∈ intAE D := by
    rw [map_one]
    exact AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, 1, rfl⟩
  exact ⟨map_one _, this, this⟩

theorem isDetRoot_one : IsDetRoot S 1 1 := by
  unfold IsDetRoot
  simp

open scoped ComplexOrder in
theorem isCartanInv_one (h : S.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D S τ) 1 := by
  have : gramAt D S τ = 1 := by rw [gramAt, h, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]
  exact ⟨Matrix.mul_one _, by simp, by rw [Matrix.mul_one]; exact Matrix.PosDef.one⟩

theorem om_vac_move {g : ℕ} {hr : T.rank = r} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {X : Data D.host.E r}
    {eT : D.what₂.Tau ≃ X.Ψ} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hS : IsSet ψ θ S T hr X eT bas) (sS : S.SigOK) (sT : T.SigOK) {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (hη : ∃ η, IsEtaTilde D η)
    (hun : ∀ v ε, NonSplitAt D v ε → UnramAt ε χS ∧ UnramAt ε χT) {Z₀ : Fam T} (hZ : IsONeg T X.p0 Z₀)
    {ΛS : Lt D.host.E S.rank} {ΛT : Lt D.host.E T.rank} (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT)
    {f₀ : WO S T → ℂ} (hf : IsVacO ψ θ S T (fun _ => 1) (cartZ T X.p0 Z₀) (ΛS : Set _) (ΛT : Set _) f₀)
    {mu : GA D T → ℂ} (hmu : MuVal T χS mu) {g₀ g₁ : GA D T} {L : Lt D.host.E T.rank}
    (m₀ : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T g₀) ΛT L) (m₁ : GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T g₁) ΛT L)
    {φ : TF S.rank g} (hφ : GlobalTheory.SW.IsSB φ) (hz : Zak ψ θ hr eT bas idx (frOf hr eT (mvZ θ g₀ Z₀)) φ (om (1, g₀) f₀))
    (w : WO S T) (hw : GlobalTheory.Ker.IsRealPt w) :
    om (1, g₁) f₀ w = mu g₁ / mu g₀ * GlobalTheory.Ker.thR X bas idx φ (frOf hr eT (mvZ θ g₁ Z₀)) (rePt θ hr eT w) := by
  obtain ⟨-, -, -, hc, hF⟩ := oneg_frames D S T r g hr ψ θ X eT bas idx hS Z₀ hZ
  have h0 := (hF g₀).1
  obtain ⟨a, ha, hae⟩ := ((oneg_frames D S T r g hr ψ θ X eT bas idx hS _ h0).2.2.2.2 1).2.2.2.2.2 _ (hF g₁).1
  have hk : (a * g₀)⁻¹ * g₁ ∈ GfC T := by
    apply (hF _).2.2.2.2.1
    rw [(hF g₁).2.2.1, hae, ← (hF g₀).2.2.1, ← (hF _).2.2.1, inv_mul_cancel]
    exact (hF 1).2.2.2.1 (one_mem _)
  have hmov := isMov_quot ha m₀ m₁
  obtain ⟨k, hke⟩ : ∃ k, k = (a * g₀)⁻¹ * g₁ := ⟨_, rfl⟩
  rw [← hke] at hk hmov
  have e1 : g₁ = a * g₀ * k := by rw [hke, mul_inv_cancel_left]
  obtain ⟨y, hy, hyk⟩ := GlobalTheory.LatticeUnitRoot.exists_finUnit_isDetRoot D T ΛT dT k hk hmov
  have h1 := GlobalTheory.T.weil_vacuum_finite_selfDualLattice_splitting D S T ψ θ hS.2.1 sS sT χS χT om hW hη hun (fun _ => 1) _ (isCartanInv_one hS.2.2.1) hc
    ΛS ΛT dS dT f₀ hf 1 (one_mem _) k hk (isMov_one _) hmov 1 y finUnit_one hy isDetRoot_one hyk
  obtain ⟨ya, hya⟩ := hmu.1 a
  obtain ⟨y₀, hy₀⟩ := hmu.1 g₀
  have h2 := (GlobalTheory.T.real_point_moves_adelic_theta_by_det_character D S T r g hr ψ θ X eT bas idx hS χS χT om hW hη _ h0 a ha ya hya φ hφ _ hz).2 w hw
  have h3 : om (1, g₁) f₀ = om (1, a) (om (1, g₀) (om (1, k) f₀)) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, e1]
    simp
  have h4 : mu g₁ = (χS ya : ℂ) * mu g₀ * χS y := by
    rw [hmu.2 g₀ y₀ hy₀, hmu.2 g₁ (ya * y₀ * y)
      (e1 ▸ detRootMul_holds T _ _ _ _ (detRootMul_holds T _ _ _ _ hya hy₀) hyk)]
    simp
  have h5 : mu g₀ ≠ 0 := norm_ne_zero_iff.1 (by rw [hmu.norm]; exact one_ne_zero)
  rw [h3, h1, map_smul, map_smul, Pi.smul_apply, h2, thR_smul, ← hae, h4, map_one, inv_one, one_mul, smul_eq_mul]
  field_simp

section Geo

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}

theorem exists_const (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (hr1 : 1 ≤ r) (hA : l.A = 1) (k : U.Comp)
    {t : ℝ} (ht : ∀ τ, (U.X k).c τ = t) (hsd : SelfD (U.X k) (U.X k).Λ) {n : ℕ} (hn : Even n) {g : ℕ}
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (hs : IsSympl (U.X k) bas) (hm : Matched c σ (U.X k) idx e) :
    ∃ φ : TF n g, GlobalTheory.SW.IsSB φ ∧ ∀ (x : Frame (U.X k).Ψ r) (hx : x ∈ (U.X k).dom), (U.X k).IsOrtho x →
      ∀ (g' : ℕ) (bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx' : Fin g' ≃ (U.X k).Ψ × Fin r)
        (e' : Fin g' ≃ Lt1 Dw), IsSympl (U.X k) bas' → Matched c σ (U.X k) idx' e' →
      letI : Algebra c.F ℂ := σ.toAlgebra
      ∀ (A : AnFib (U.X k) bas' idx' e' x (U.X k).Λ (ptC U k ⟨x, hx⟩)) (th : (Fin g' → ℂ) → ℂ),
        A.Reads 1 (ptC U k ⟨x, hx⟩).s th → ∀ p : GlobalTheory.Ker.WR (U.X k) n,
          GlobalTheory.Ker.gaussR (U.X k) bas' idx' x (GlobalTheory.Ker.zR (U.X k) idx' x p) * ∏ b, th (GlobalTheory.Ker.zR (U.X k) idx' x p b) =
            GlobalTheory.Ker.thR (U.X k) bas idx φ x p := by
  obtain ⟨v, hv⟩ := (TensVac.vacua _ _ _ _ bas idx n hs hn _ H.w0.isIntegral_coe (hostHalfRoot_add_conj_eq_one H) _ hsd 1 _
    (Base.stdL_mem_Vset n 1)).1
  obtain ⟨C, hC⟩ := exists_const_ortho D H Dw l Xo c σ r U hσ hU hr1 hA k t ht n hn g bas idx e hs hm v hv
  refine ⟨C • v, TensVac.sb_smul _ hv.1, fun x hx ho g' bas' idx' e' hs' hm' A th hth p => ?_⟩
  have key := anFib_move_renum D H Dw l Xo c σ r g g' (U.X k) (U.X k) ⟨rfl, rfl, rfl, rfl, rfl⟩ bas' idx' e' bas idx e
    hs' hs hm' hm x hx _ hsd 1 (fun a b => by simp) _ A th hth
  have e1 : lact (1 : GL (Fin r) D.host.E) (castFr (rfl : (U.X k).Ψ = (U.X k).Ψ) x) = x := by
    funext τ
    simp only [lact, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    rfl
  have e2 : mapL (1 : GL (Fin r) D.host.E) (U.X k).Λ = (U.X k).Λ := by
    simp [mapL]
  rw [e1, e2] at key
  obtain ⟨A₁, th₁, h1, -, h2⟩ := key
  rw [← h2 n p p fun τ j => by simp, hC ⟨x, hx⟩ ho A₁ th₁ h1, thR_smul, GlobalTheory.Ker.thR]
  ring

def IsPt (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S : HSp D) (hr : T.rank = r) (U : Unf Xo c σ r) (q : ℕ)
    (Z₀ : Fam T) (k : U.Comp) (x : Frame (U.X k).Ψ r) (h : GA D T) : Prop :=
  ∃ γ ∈ GQ T, ∃ (g : ℕ) (eT : D.what₂.Tau ≃ (U.X k).Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ)
    (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (hx : x ∈ (U.X k).dom),
    IsSet ψ θ S T hr (U.X k) eT bas ∧ Matched c σ (U.X k) idx e ∧ (U.X k).p0 = q ∧ SelfD (U.X k) (U.X k).Λ ∧
    GlobalTheory.OneMapRef.latW hr (U.X k).Λ = latG T (γ * h) ∧ x = frOf hr eT (mvZ θ (γ * h) Z₀) ∧
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∃ (A : AnFib (U.X k) bas idx e x (U.X k).Λ (ptC U k ⟨x, hx⟩)) (th : (Fin g → ℂ) → ℂ),
      A.Reads 1 (ptC U k ⟨x, hx⟩).s th ∧ MeanOne (U.X k) bas idx x (U.X k).Λ th

theorem exists_frConst {hr : T.rank = r} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (sS : S.SigOK) (sT : T.SigOK) {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (hη : ∃ η, IsEtaTilde D η)
    (hun : ∀ v ε, NonSplitAt D v ε → UnramAt ε χS ∧ UnramAt ε χT) {q : ℕ} {Z₀ : Fam T} (hZ : IsONeg T q Z₀)
    {ΛT : Lt D.host.E T.rank} (dS : IsSelfDualC S (stdL D.host.E S.rank)) (dT : IsSelfDualC T ΛT)
    {f₀ : WO S T → ℂ} (hf : IsVacO ψ θ S T (fun _ => 1) (cartZ T q Z₀) (stdL D.host.E S.rank : Set _) (ΛT : Set _) f₀)
    {mu : GA D T → ℂ} (hmu : MuVal T χS mu) (hQ : ∀ γ ∈ GQ T, ∀ h, mu (γ * h) = mu h)
    (hlat : ∀ h : GA D T, ∃ LT : Lt D.host.E T.rank, GlobalTheory.Ker.IsAA (latG T h) LT ∧
      GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T h) ΛT LT ∧ ∀ u : WO S T,
        u ∈ (latO S T (stdL D.host.E S.rank : Set _) (LT : Set _) fun _ => True) ↔
          ∃ u₀ ∈ (latO S T (stdL D.host.E S.rank : Set _) (ΛT : Set _) fun _ => True), u = actO S T 1 h u₀)
    (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (hr1 : 1 ≤ r) (hA : l.A = 1) {t : ℝ}
    (ht : ∀ k τ, (U.X k).c τ = t) (dict : GA D T → Σ k, Frame (U.X k).Ψ r)
    (hpt : ∀ h, IsPt ψ θ S hr U q Z₀ (dict h).1 (dict h).2 h) :
    ∃ cc : U.Comp → ℂ, CUnit cc ∧ FrConst ψ θ S hr om f₀ U dict mu Z₀ cc := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  have key : ∀ k : U.Comp, ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ (x : Frame (U.X k).Ψ r) (h : GA D T), IsPt ψ θ S hr U q Z₀ k x h →
      ∀ γ ∈ GQ T, ∀ (g : ℕ) (eT : D.what₂.Tau ≃ (U.X k).Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ)
        (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSet ψ θ S T hr (U.X k) eT bas →
        Matched c σ (U.X k) idx e → x = frOf hr eT (mvZ θ (γ * h) Z₀) → ∀ (hx : x ∈ (U.X k).dom)
        (A : AnFib (U.X k) bas idx e x (U.X k).Λ (ptC U k ⟨x, hx⟩)) (th : (Fin g → ℂ) → ℂ),
        A.Reads 1 (ptC U k ⟨x, hx⟩).s th → ∀ w : WO S T, Ker.IsRealPt w →
          om (1, γ * h) f₀ w = a * mu h *
            (Ker.gaussR (U.X k) bas idx x (Ker.zR (U.X k) idx x (rePt θ hr eT w)) *
              ∏ b, th (Ker.zR (U.X k) idx x (rePt θ hr eT w) b)) := by
    intro k
    by_cases hk : ∃ x h, IsPt ψ θ S hr U q Z₀ k x h
    swap
    · exact ⟨1, norm_one, fun x h hp => absurd ⟨x, h, hp⟩ hk⟩
    obtain ⟨x₀, h₀, γ₀, hγ₀, g₀, eT, bas₀, idx₀, e₀, hx₀, hS, hm₀, rfl, hsd, hL₀, rfl, A₀, th₀, hr₀, hmean⟩ := hk
    obtain ⟨-, -, -, -, hF⟩ := oneg_frames D S T r g₀ hr ψ θ _ eT bas₀ idx₀ hS Z₀ hZ
    have hortho := fun h => (oneg_frames D S T r g₀ hr ψ θ _ eT bas₀ idx₀ hS _ (hF h).1).2.2.1
    have hs₀ := hS.2.2.2.2.2.2.2
    obtain ⟨L₀, a₀, m₀, l₀⟩ := hlat (γ₀ * h₀)
    have hv := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hS.2.1 (fun _ => 1) (fun _ => 1) _ _ _ _ _ _ 1 (γ₀ * h₀)
      (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (hF _).2.1 l₀ f₀ hf
    obtain ⟨a, ha, hval⟩ := VacUnit.vac_eq_unit_mul D S T r g₀ hr ψ θ _ eT bas₀ idx₀ hS _ H.w0.isIntegral_coe (hostHalfRoot_add_conj_eq_one H)
      (isRelTraceOneIdempotentModTwo_hostElement H) _ (hF (γ₀ * h₀)).1 L₀ _ hsd (hL₀ ▸ a₀) _ hv th₀
      (isTheta1_of_reads_generator _ H Dw l Xo c r g₀ _ bas₀ idx₀ e₀ _ _ _ A₀ hs₀ hx₀ hsd th₀ hr₀) hmean
    obtain ⟨φ, hφ, hall⟩ := exists_const U hσ hU hr1 hA k (ht k) hsd hS.2.2.2.1 bas₀ idx₀ e₀ hs₀ hm₀
    have hz : Zak ψ θ hr eT bas₀ idx₀ (frOf hr eT (mvZ θ (γ₀ * h₀) Z₀)) (a • φ) (om (1, γ₀ * h₀) f₀) :=
      ⟨hv.2.theta, fun w hw => by
        rw [hval w hw, thR_smul, hall _ hx₀ (hortho _) g₀ bas₀ idx₀ e₀ hs₀ hm₀ A₀ th₀ hr₀]⟩
    refine ⟨a / mu h₀, by rw [norm_div, ha, hmu.norm, div_one], ?_⟩
    rintro x h ⟨γ₁, hγ₁, g₁, eT₁, bas₁, -, -, -, hS₁, -, -, -, hL₁, hx₁, -⟩ γ hγ g eT₂ bas idx e hS₂ hm hx₂ hx A th hth w hw
    have he : ∀ {g' : ℕ} {eT' : D.what₂.Tau ≃ (U.X k).Ψ} {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] (U.X k).Λ},
        IsSet ψ θ S T hr (U.X k) eT' bas' → eT = eT' := fun h' =>
      Equiv.ext fun ρ => Subtype.ext ((hS.2.2.2.2.2.2.1 ρ).trans (h'.2.2.2.2.2.2.1 ρ).symm)
    obtain rfl := he hS₁
    obtain rfl := he hS₂
    have e1 := frOf_injective hr eT (hx₁.symm.trans hx₂)
    have hfin : (γ * h)⁻¹ * (γ₁ * h) ∈ GfC T := by
      apply (hF _).2.2.2.2.1
      rw [(hF (γ₁ * h)).2.2.1, e1, ← (hF _).2.2.1, inv_mul_cancel]
      exact (hF 1).2.2.2.1 (one_mem _)
    have e2 : γ⁻¹ * γ₁ = 1 := by
      refine eq_one_of_rat hS.2.1 (mul_mem (inv_mem hγ) hγ₁) ?_
      have := (MonoidHom.normal_ker (infHom T)).conj_mem _ hfin h
      rwa [show h * ((γ * h)⁻¹ * (γ₁ * h)) * h⁻¹ = γ⁻¹ * γ₁ by group] at this
    obtain rfl : γ = γ₁ := inv_mul_eq_one.1 e2
    obtain ⟨L₁, a₁, m₁, -⟩ := hlat (γ * h)
    rw [← hL₁] at a₁
    rw [← hL₀] at a₀
    obtain rfl : L₀ = L₁ := le_antisymm (le_of_isAA a₀ a₁) (le_of_isAA a₁ a₀)
    subst hx₂
    rw [om_vac_move idx₀ hS sS sT hW hη hun hZ dS dT hf hmu m₀ m₁ (TensVac.sb_smul a hφ) hz w hw, thR_smul,
      hall _ hx (hortho _) g bas idx e hS₂.2.2.2.2.2.2.2 hm A th hth, hQ _ hγ, hQ _ hγ₀]
    ring
  choose cc hcc hkey using key
  exact ⟨cc, hcc, fun h γ hγ => hkey _ _ h (hpt h) γ hγ⟩

end Geo

theorem mu_rat_cast {V W : HSp D} (hV : V = W) {mu : GA D V → ℂ} (h : ∀ γ ∈ GQ V, ∀ h, mu (γ * h) = mu h) :
    ∀ γ ∈ GQ W, ∀ h, castDict hV mu (γ * h) = castDict hV mu h := by
  subst hV; exact h

end GlobalTheory.OneMapRef.FrameConst

end
