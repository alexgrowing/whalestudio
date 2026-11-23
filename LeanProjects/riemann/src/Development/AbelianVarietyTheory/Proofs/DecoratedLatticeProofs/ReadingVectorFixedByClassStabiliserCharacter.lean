import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveTopMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainComplexFormsEqAlgebraicModularForms
import Formalism.LocalToGlobal.Columns.CoefModB

noncomputable section

namespace GlobalTheory.AdForm.StabInv

section Pair
open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.ColAd Matrix

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem lT_fnOf (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (u : ι → GL (Fin n) ℂ) (P : Pol ℂ ι n) :
    lT G u (fnOf G (shiftOf lam) 1 P) = fnOf G (shiftOf lam) 1 (rhoP lam (invTrK u⁻¹) P) := by
  funext y
  have e1 : ∀ τ, ((invTrK u⁻¹ τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ = (u τ : Matrix (Fin n) (Fin n) ℂ) := fun τ => by
    rw [invTrK_coe, Matrix.transpose_transpose, Pi.inv_apply, inv_inv]
  simp only [lT_apply, fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, frL, rhoP, MonoidHom.coe_mk,
    OneHom.coe_mk, actP, trAct, detTwK, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_mul, MvPolynomial.smul_eval,
    Formalism.GradedWeylDivisibility.blockAct, eval_aeval_poly, e1, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  have e2 : ∀ τ, detPow ℂ n (invTrK u⁻¹ τ) (lam τ).detShift = (u τ : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift :=
    fun τ => by rw [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, e1]
  simp only [e2, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, shiftOf, Matrix.mul_apply]
  ring

theorem eq_smul_of_pair (G G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam lam' : ι → DomWeight n) (hl : lam = lam') (o : Frames G')
    (ho : ∀ τ, o.1 τ = 1) (k k' : ι → GL (Fin n) ℂ) (hk : k = k') {w : Pol ℂ ι n} (hw : w ∈ VV ℂ lam) (c : ℂ)
    (h : ∀ φ ∈ ValC G lam', ∃ φ' : Frames G → ℂ, lT G k φ' = φ ∧
      pairB lam (polOf G' (shiftOf lam) o φ') w = c * pairB lam (polOf G' (shiftOf lam) o φ) w) :
    w = c • rhoP lam k' w := by
  subst hl hk
  have hp : ∀ P, polOf G' (shiftOf lam) o (fnOf G (shiftOf lam) 1 P) = P := fun P => by
    have e : (fun τ => (o.1 τ)⁻¹) = 1 := funext fun τ => by rw [ho τ]; exact inv_one
    have := polOf_fnOf G' (shiftOf lam) o P
    rw [e] at this
    exact this
  have hm : w - c • rhoP lam k w ∈ VV ℂ lam := sub_mem hw (Submodule.smul_mem _ _ (polyAction_mem_VV lam k hw))
  have h0 := (pairingBNondegenerate_holds ℂ ι n lam).2 ⟨_, hm⟩ fun P => by
    obtain ⟨φ', e1, e2⟩ := h (lT G k (fnOf G (shiftOf lam) 1 P.1))
      (lT_mem G lam k ⟨P.1, by simpa [MvPolynomial.map_id] using map_mem_CSpan (RingHom.id ℂ) lam _ P.2, rfl⟩)
    have e3 : φ' = fnOf G (shiftOf lam) 1 P.1 := by
      have := congrArg (lT G k⁻¹) e1
      rwa [← lT_mul, ← lT_mul, mul_inv_cancel, lT_one, lT_one] at this
    rw [e3, lT_fnOf, hp, hp] at e2
    have e4 := pairingBInvariantK_holds ℂ ι n lam k⁻¹ P.1 (rhoP lam k w)
    have e5 : actP lam k⁻¹ (rhoP lam k w) = w := by
      show (rhoP lam k⁻¹ * rhoP lam k) w = w
      rw [← map_mul, inv_mul_cancel, map_one]; rfl
    rw [e5] at e4
    rw [pairBK_apply]
    show pairB lam P.1 (w - c • rhoP lam k w) = 0
    rw [map_sub, map_smul, e2, ← e4, smul_eq_mul]
    exact sub_self _
  exact sub_eq_zero.1 (congrArg Subtype.val h0)

end Pair

section Law
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
  Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top GlobalTheory.Core.Rk.TopOnto
open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.TopLift GlobalTheory.Core.Rk.Top.Model GlobalTheory.PointAtPlaceHom Formalism.MainNotions.StandardLattice Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} {θ : InfFam D} {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S}
  {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ}

set_option maxHeartbeats 1000000 in

theorem coset_law_moved (hθ : IsInfFam θ) (hj : IsJ u M j) {b : GA D D.sp.X'} (hb : b ∈ GfC D.sp.X') {γ : GA D D.sp.X'}
    (hγ : γ ∈ GQ D.sp.X') {k h h' : GA D D.sp.X'} {κ x x'} (hk : HasMat k κ) (hJ : b⁻¹ * k * b ∈ J) (hh : HasMat h x)
    (hh' : HasMat h' x') (e : x' = (finPt γ).1 * x * κ) (v : SmT M) :
    ∃ v' : SmT M, lT _ (infPt θ γ) (j v') = j v ∧
      ∀ T ∈ MultT θ M J χ, T v' (h' * b) = χ (b⁻¹ * k * b) * T v (h * b) := by
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ D.sp.X'
  obtain ⟨f, hf, a, ha, rfl⟩ := R.2.2.2.2.2.2.1 γ
  obtain ⟨v', e1, e2⟩ := real_translate (J := J) (χ := χ) hθ hj a ha v
  have e3 : h' = f * h * k := by
    refine hasMat_pt hh' ?_
    have := hasMat_finPt (mul_mem (mul_mem hf hh.1) hk.1)
    rwa [finPt_mul, finPt_mul, finPt_of_hasMat hh, finPt_of_hasMat hk, ← finPt_mul_inf f ha, ← e] at this
  refine ⟨v', by rw [map_mul (infPt θ), infPt_of_fin θ hf, one_mul, e1], fun T hT => ?_⟩
  have e4 : h' * b * a = f * a * (h * b * (b⁻¹ * k * b)) := by
    have e5 : h * b * (b⁻¹ * k * b) = h * k * b := by group
    rw [e5, e3, mul_assoc f a, comm_of_mem _ ha (mul_mem (mul_mem hh.1 hk.1) hb)]
    simp only [mul_assoc]
  rw [e2 T hT, e4, multT_rel' (h * b * (b⁻¹ * k * b)) (f * a * (h * b * (b⁻¹ * k * b))) 1 (fun m hm w => by
    rw [one_mul]; exact (hm.aut w).left _ hγ _) hT, one_mul,
    multT_rel' (h * b) (h * b * (b⁻¹ * k * b)) (χ (b⁻¹ * k * b)) (fun m hm w => hm.lev w _ hJ (h * b)) hT]

end Law

section Chi
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem chi_eq_chr {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι) {Lb U chi y lat st} (hR : I.ReadsP a Lb U chi y lat st)
    (c : (I.stX a).Cl) (s : (I.stX a).Stab c) (κ : U)
    (e' : y c = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1) * y c * κ.1) :
    ((chi κ : ℂˣ) : ℂ) = B.embLL (((I.stX a).chr c.1 s.1 : B.LLˣ) : B.LL) := by
  let κ0 : (I.stX a).G c.1 := (1, s.1.2.1, s.1.2.2)
  have hgam : (I.stX a).gam c.1 κ0 = 1 := map_one (ufGL B.fields.E (B.R.N B.R.m - 1))
  have hp := GlobalTheory.Mem.Col2.TilX.isPtOf_rat (hR.pt c) (s.1.1)⁻¹
  have hact : ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
      GLG B.fields.E (B.R.N B.R.m - 1) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) •
      ((I.stX a).rep c).1.1 := by
    have e1 : FrmG.incl _ _ s.1 • ((I.stX a).rep c).1.1 = ((I.stX a).rep c).1.1 :=
      congrArg (fun d : (I.stX a).D c.1 => d.1.1) s.2
    conv_rhs => rw [← e1]
    refine Eq.trans ?_ (smul_smul _ _ _).symm
    have e2 : FrmG.incl _ _ κ0 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
        GLG B.fields.E (B.R.N B.R.m - 1) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) *
        FrmG.incl _ _ s.1 := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (inv_mul_cancel _).symm
      · exact (one_mul _).symm
      · exact (one_mul _).symm
    exact congrArg (fun t => t • ((I.stX a).rep c).1.1) e2
  have hyk : y c * κ.1 = ratAd B.host.F (s.1.1)⁻¹ * y c := by
    have e3 : ratAd B.host.F (s.1.1)⁻¹ =
        (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1))⁻¹ := by
      unfold ratAd
      rw [map_inv, map_inv]
      rfl
    rw [e3]
    conv_rhs => rw [e']
    group
  have hq : PtOf (y c * κ.1) ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 := by
    rw [hyk, hact]
    exact hp
  exact hR.chr c κ κ0 hgam hq

theorem sgT_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    (I.perIn u a).sgT = (Formalism.L2.Forms.sgT (D := I.rec7 l Z) u : B.fields.Tau → DomWeight (B.R.N B.R.m - 1)) := by
  funext τ
  obtain ⟨a, ha⟩ := B.R.t_odd
  have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (a + 1) := by
    rw [ha, show B.R.m * (2 * a + 1 + 1) = 2 * (B.R.m * (a + 1)) by ring]; omega
  have e2 : (B.R.t + 1) / 2 = a + 1 := by omega
  show GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) =
    Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ)
  rw [e1, e2]
  unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
  congr 1

theorem star_eq_inv {H K : Type} [Group H] [Finite H] [Field K] (φ : H →* Kˣ) (σ : K →+* ℂ) (s : H) :
    star (σ (φ s : K)) = (σ (φ s : K))⁻¹ := by
  have e : σ (φ s : K) ^ Nat.card H = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, map_one]
  exact (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one e Nat.card_pos.ne')).symm

end Chi

section Main
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.TopLift GlobalTheory.Core.Rk.TopOnto GlobalTheory.Core.Rk.Top.Model

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem reading_stab_inv : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∀ (c : (I.stX a).Cl) (w : Formalism.L2.DIV.Pol ℂ (I.rec7 l Z).what₂.Tau (B.R.N B.R.m - 1)), w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT → (∀ v h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 → f.1 v (h * g.bT) = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w) → ∀ s : (I.stX a).Stab c, w = (B.embLL ((I.stX a).chr c.1 s.1 : B.LL))⁻¹ • Formalism.L2.DIV.rhoP (I.perIn u a).sgT (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) ((I.stX a).gam c.1 s.1)) w := by
  intro B X I hI hP l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ hX j hj P t a bad K hR hb hL f c w hw hf s
  have hθ : IsInfFam R.θ := hX.inf
  have hst : (K.stabI c s).1 = (I.stX a).gam c.1 s.1 := hR.stab c s
  obtain ⟨κ₀, hκ₀, e0⟩ := (K.stabI_range c (K.stabI c s)).1 ⟨s, rfl⟩
  let κ : K.lev.U := ⟨κ₀, hκ₀⟩⁻¹
  have e1 : (K.y c).1 = Formalism.UG.bc (Formalism.UG.inclE (F := (I.rec7 l Z).host.F)
      (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (K.stabI c s).1 * (K.y c).1 * κ.1 := by
    rw [← e0]
    show _ = (K.y c).1 * κ₀ * (K.y c).1⁻¹ * (K.y c).1 * κ₀⁻¹
    group
  have e2 := chi_eq_chr I a hR c s κ (by
    have h0 := e1
    rw [hst] at h0
    exact h0)
  haveI : Finite ((I.stX a).Stab c) := ((I.fm l u a).stabPFin c : Finite _)
  have e3 := star_eq_inv (((I.stX a).chr c.1).comp (Subgroup.subtype _ : (I.stX a).Stab c →* _)) B.embLL s
  obtain ⟨γ, hγ, e4, e5⟩ := exists_ratPt hθ (rankP (I.rec7 l Z)) (K.stabI c s).1 (K.stabI c s).2
  obtain ⟨k, hk⟩ := hasMat_exists (D := I.rec7 l Z) ⟨κ.1, ((K.lev.U_eq _).1 κ.2).1⟩
  obtain ⟨h, hh⟩ := hasMat_exists (D := I.rec7 l Z) (K.y c)
  have e6 : levChi _ R.βX (datXP R P t) (g.bT⁻¹ * k * g.bT) = (B.embLL ((I.stX a).chr c.1 s.1 : B.LL))⁻¹ :=
    (hL.2 k κ hk).trans ((congrArg star e2).trans e3)
  refine eq_smul_of_pair (gramC (gramP (I.rec7 l Z)) (embT (I.rec7 l Z))) _ _ _ (sgT_eq I l Z u a)
    (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (fun _ => rfl) (infPt R.θ γ) _ ?_ hw _ fun φ hφ => ?_
  · funext τ
    refine Units.ext ((e5 τ).trans ?_)
    rw [hst]
    ext p q
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  · obtain ⟨v, rfl⟩ := (hj.range ▸ hφ : φ ∈ LinearMap.range j)
    obtain ⟨v', e7, e8⟩ := coset_law_moved (χ := levChi _ R.βX (datXP R P t)) hθ hj hb hγ hk ((hL.1 k).2 ⟨κ, hk⟩) hh hh
      (e1.trans (congrArg (· * (K.y c).1 * κ.1) e4.symm)) v
    refine ⟨j v', e7, ?_⟩
    have e9 := e8 f.1 f.2
    rw [hf v' h hh, hf v h hh, e6] at e9
    exact e9

end Main

end GlobalTheory.AdForm.StabInv

end
