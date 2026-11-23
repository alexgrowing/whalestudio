import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvOfRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToRatHyp0
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKsFormOfAlgebraicFormsIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodBaseDataWeightEqLiftCoeffModuleWeight

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

open GlobalTheory.ConjTwist

theorem exists_aut_on {K : Type} [Field K] (e e' : K →+* ℂ) {s : Set K} (hs : s.Countable) :
    ∃ τ : ℂ ≃+* ℂ, ∀ a ∈ s, τ (e a) = e' a := by
  haveI : Countable (Subfield.closure s) := Cardinal.mk_le_aleph0_iff.1
    ((Subfield.cardinalMk_closure_le_max _).trans (max_le (Cardinal.mk_le_aleph0_iff.2 hs.to_subtype) le_rfl))
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq (Subfield.closure s) (e.comp (Subfield.closure s).subtype)
    (e'.comp (Subfield.closure s).subtype)
  exact ⟨τ, fun a ha => hτ ⟨a, Subfield.subset_closure ha⟩⟩

theorem countable_alg {K : Type} [Field K] (e : K →+* ℂ) : {a : K | IsAlgebraic ℚ (e a)}.Countable :=
  (Algebraic.countable ℚ ℂ).preimage e.injective

theorem isAlgebraic_of_root {ζ : ℂ} {n : ℕ} (hn : n ≠ 0) (h : ζ ^ n = 1) : IsAlgebraic ℚ ζ :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) 1, by simp [h]⟩

section Coord

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (j : Fin D.R.m)

theorem exists_fns (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW) (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _))
    (hK : (S.A ((j : ℕ) + 1)).IsKsForm) : ∃ (m : ℕ) (φ : Fin m → (GA D (Wc D j) → ℂ)), LinearIndependent ℂ φ ∧
      ∀ g : NX.FmK S ((j : ℕ) + 1), ∃ r : Fin m → ↥D.LL0, evW YS v₀ j g.val = ∑ a, Formalism.L2.Host.embLL0 D (r a) • φ a := by
  classical
  let L : (Rl.HW j (sg0 D A3.A)).H →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
    { toFun := fun x => (Rl.HW j (sg0 D A3.A)).e x (v₀ j _)
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hL : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.2 fun x y h => GlobalTheory.LiftScalarCompare.eval_inj hW hv h
  obtain ⟨m, bb, -, hKs, hspan, hLL, -⟩ := hK
  let bK : Module.Basis (Fin m) S.Ks ↥(S.A ((j : ℕ) + 1)).WK :=
    (Module.Basis.span hKs).map (LinearEquiv.ofEq _ _ hspan)
  have hbK : ∀ k, ((bK k : ↥(S.A ((j : ℕ) + 1)).WK) : S.WL ((j : ℕ) + 1)) = bb k := fun k => by
    simp [bK, Module.Basis.span_apply]
  refine ⟨m, fun k => evW YS v₀ j (bb k), ?_, fun g => ⟨fun a => S.kKs (bK.repr g a), ?_⟩⟩
  · have h1 : LinearIndependent D.what₂.LL fun k => (YS.fi j).e (bb k) :=
      hLL.map' (YS.fi j).e.toLinearMap (YS.fi j).e.ker
    exact ((hU j (sg0 D A3.A)).1 m _ h1).map' L hL
  · conv_lhs => rw [← bK.sum_repr g]
    rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Submodule.coe_smul, ← algebraMap_smul D.what₂.LL, evW_smul, hbK, ← S.kKs_spec]
    rfl

def fracIncl (i : D.ntw.Tw) (k : ℕ) : FractionRing (D.ntw.O i) →+* FractionRing (D.ntw.Ok i k) :=
  IsFractionRing.map (A := D.ntw.O i) (B := D.ntw.Ok i k) (D.ntw.Ok_inj i k)

theorem ek_fracIncl {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (x : FractionRing (D.ntw.O i)) :
    ρ.ek i b k (fracIncl i k x) = ρ.e i b x := by
  have : (ρ.ek i b k).comp (fracIncl i k) = ρ.e i b := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (D.ntw.O i)) (RingHom.ext fun a => ?_)
    have e := hρ.ek_e i b k a
    simp only [RingHom.comp_apply, fracIncl, IsFractionRing.map, IsLocalization.map_eq]
    exact e
  exact RingHom.congr_fun this x

theorem exists_coords {m : ℕ} {φ : Fin m → (GA D (Wc D j) → ℂ)}
    (hφ : ∀ g : NX.FmK S ((j : ℕ) + 1), ∃ r : Fin m → ↥D.LL0, evW YS v₀ j g.val = ∑ a, Formalism.L2.Host.embLL0 D (r a) • φ a)
    (i : D.ntw.Tw) (b : Bool) (k : ℕ) (y : D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b) :
    ∃ A : Fin m → FractionRing (D.ntw.Ok i k), ∀ (ρ : Setup D.ntw) (hρ : ρ.Good) (ν : ℂ),
      rdK (realRd YS v₀ hρ i j b ν) hρ k y = ν⁻¹ • ∑ a, ρ.ek i b k (A a) • φ a := by
  have key : ∀ x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1), ∃ A : Fin m → FractionRing (D.ntw.O i),
      ∀ (ρ : Setup D.ntw) (hρ : ρ.Good), evK YS v₀ hρ i j b x = ∑ a, ρ.e i b (A a) • φ a := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, fun ρ hρ => by simp⟩
    | add x y hx hy =>
      obtain ⟨A, hA⟩ := hx
      obtain ⟨A', hA'⟩ := hy
      exact ⟨A + A', fun ρ hρ => by rw [map_add, hA, hA', ← Finset.sum_add_distrib]; simp [add_smul]⟩
    | tmul c g =>
      obtain ⟨r, hr⟩ := hφ g
      refine ⟨fun a => (show FractionRing (D.ntw.O i) from c) * sideEmb D.ntw i b (r a), fun ρ hρ => ?_⟩
      rw [evK_tmul, hr, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hρ.e_LL0, smul_smul]
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, fun ρ hρ ν => by simp⟩
  | add x y hx hy =>
    obtain ⟨A, hA⟩ := hx
    obtain ⟨A', hA'⟩ := hy
    exact ⟨A + A', fun ρ hρ ν => by rw [map_add, hA, hA', ← smul_add, ← Finset.sum_add_distrib]; simp [add_smul]⟩
  | tmul c f =>
    obtain ⟨A, hA⟩ := key (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
    refine ⟨fun a => algebraMap _ _ c * fracIncl i k (A a), fun ρ hρ ν => ?_⟩
    rw [rdK_tmul]
    change _ • ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) = _
    rw [hA, smul_comm, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, ek_fracIncl hρ, smul_smul]
    rfl

theorem conjChar_tw {ρ ρ' : Setup D.ntw} (hs : SameBut ρ ρ') {i : D.ntw.Tw} (b : Bool) {k : ℕ} {Q : Finset (Pl D.host.E)}
    {ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hψ : IntegralHeckeForms.TwOK i k Q ψ) {τ : ℂ ≃+* ℂ}
    (hτ : ∀ a, IsAlgebraic ℚ (ρ.ek i b k a) → τ (ρ.ek i b k a) = ρ'.ek i b k a) :
    ConjChar τ (ρ.tw i b k Q ψ) (ρ'.tw i b k Q ψ) := by
  refine ⟨by simp only [Setup.tw, twistOf, hs.2.1], fun x => ?_⟩
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  have hn : D.ntw.l i ^ k ≠ 0 := pow_ne_zero _ (D.ntw.lPrime i).out.ne_zero
  have h1 : ψ σ ^ (D.ntw.l i ^ k) = 1 := by
    obtain ⟨n, hn⟩ := hψ.2.2.2.2.1 σ
    have hz : D.ntw.zk i k ^ (D.ntw.l i ^ k) = 1 := Units.ext (by simpa using (D.ntw.zk_prim i k).pow_eq_one)
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  have e1 := charOf_eq ρ.rc (ρ.eOk i b k) hψ.2.2.1 hσ hn h1
  have e2 := charOf_eq ρ.rc (ρ'.eOk i b k) hψ.2.2.1 hσ hn h1
  change ((GlobalTheory.SeriesTie.charOf ρ'.rc (ρ'.eOk i b k) ψ x : Circle) : ℂ) = τ ((GlobalTheory.SeriesTie.charOf ρ.rc (ρ.eOk i b k) ψ x : Circle) : ℂ)
  rw [hs.1, e1, e2]
  refine (hτ _ (isAlgebraic_of_root hn ?_)).symm
  change ρ.eOk i b k _ ^ _ = 1
  rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]

theorem eq_smul_of_conj (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW)
    (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) (hK : (S.A ((j : ℕ) + 1)).IsKsForm)
    {ρ ρ' : Setup D.ntw} (hρ : ρ.Good) (hρ' : ρ'.Good) (i : D.ntw.Tw) (b : Bool) (k : ℕ) {ν ν' : ℂ} (hν : ν ≠ 0) (hν' : ν' ≠ 0)
    (hνν : ∃ n : ℕ, n ≠ 0 ∧ ν' ^ n = ν ^ n) (y y' : D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b)
    (h : ∀ τ : ℂ ≃+* ℂ, (∀ z, τ (Formalism.L2.Host.embLL0 D z) = Formalism.L2.Host.embLL0 D z) →
      (∀ a, IsAlgebraic ℚ (ρ.ek i b k a) → τ (ρ.ek i b k a) = ρ'.ek i b k a) →
      ∃ c : ℂ, IsRoot1 c ∧ ∃ (n : ℕ) (β : Fin n → ℂ) (g : Fin n → NX.FmK S ((j : ℕ) + 1)),
        ν • rdK (realRd YS v₀ hρ i j b ν) hρ k y = ∑ l, β l • evW YS v₀ j (g l).val ∧
        ∑ l, τ (β l) • evW YS v₀ j (g l).val = c • ν • rdK (realRd YS v₀ hρ' i j b ν') hρ' k y') :
    ∃ o : D.ntw.Ok i k, y = o • y' := by
  obtain ⟨m, φ, hφ, hr⟩ := exists_fns YS v₀ j hU hW hv hK
  obtain ⟨A, hA⟩ := exists_coords YS v₀ j hr i b k y
  obtain ⟨A', hA'⟩ := exists_coords YS v₀ j hr i b k y'
  obtain ⟨τ, hτ⟩ := exists_aut_on (ρ.ek i b k) (ρ'.ek i b k) ((countable_alg (ρ.ek i b k)).union (Set.countable_range A))
  have hfix : ∀ z, τ (Formalism.L2.Host.embLL0 D z) = Formalism.L2.Host.embLL0 D z := fun z => by
    have h1 := (ek_fracIncl hρ i b k _).trans (hρ.e_LL0 i b z)
    have h2 := (ek_fracIncl hρ' i b k _).trans (hρ'.e_LL0 i b z)
    have hz : IsAlgebraic ℚ (Formalism.L2.Host.embLL0 D z) :=
      (Algebra.IsAlgebraic.isAlgebraic z).algHom (Formalism.L2.Host.embLL0 D).toRatAlgHom
    rw [← h1] at hz
    rw [← h1, hτ _ (Or.inl hz), h2, h1]
  obtain ⟨c, ⟨nc, hnc, hc⟩, n, β, g, h1, h2⟩ := h τ hfix fun a ha => hτ a (Or.inl ha)
  choose r hr using hr
  have hexp : ∀ d : Fin n → ℂ, ∑ l, d l • evW YS v₀ j (g l).val =
      ∑ a, (∑ l, d l * Formalism.L2.Host.embLL0 D (r (g l) a)) • φ a := fun d => by
    simp only [hr, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [hA, smul_inv_smul₀ hν, hexp] at h1
  rw [hA', hexp, smul_smul, smul_smul, Finset.smul_sum] at h2
  simp only [smul_smul] at h2
  have e1 := Fintype.linearIndependent_iffₛ.1 hφ _ _ h1
  have e2 := Fintype.linearIndependent_iffₛ.1 hφ _ _ h2
  have e3 : ∀ a, ρ'.ek i b k (A a) = c * ν * ν'⁻¹ * ρ'.ek i b k (A' a) := fun a => by
    rw [← e2, ← hτ _ (Or.inr ⟨a, rfl⟩), e1, map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_mul, hfix]
  have hinj := (realRd_faithful _ _ _ _ _ _ _ Rl cG S YS v₀ ρ' hρ' i j b ν' hν' hU hW hv hK).injective_rdK hρ' k
  have e4 : rdK (realRd YS v₀ hρ' i j b ν') hρ' k y = (c * ν * ν'⁻¹) • rdK (realRd YS v₀ hρ' i j b ν') hρ' k y' := by
    rw [hA, hA', smul_comm (c * ν * ν'⁻¹), Finset.smul_sum (r := c * ν * ν'⁻¹)]
    simp only [e3, smul_smul]
  by_cases h0 : ∀ a, A' a = 0
  · refine ⟨0, hinj ?_⟩
    rw [e4, hA', zero_smul, map_zero]
    simp [h0]
  · obtain ⟨a, ha⟩ := not_forall.1 h0
    obtain ⟨nn, hnn, hνn⟩ := hνν
    have hu : ρ'.ek i b k (A' a / A a) = (c * ν * ν'⁻¹)⁻¹ := by
      have : ρ'.ek i b k (A' a) ≠ 0 := (map_ne_zero _).2 ha
      rw [map_div₀, e3, div_mul_eq_div_div_swap, div_self this, one_div]
    have hp : (A' a / A a) ^ (nc * nn) = 1 := (ρ'.ek i b k).injective (by
      rw [map_pow, hu, map_one, inv_pow, mul_assoc, mul_pow, pow_mul, hc, one_pow, one_mul, mul_comm nc, pow_mul, mul_pow, inv_pow,
        hνn, mul_inv_cancel₀ (pow_ne_zero _ hν), one_pow, inv_one])
    obtain ⟨o, ho⟩ := exists_inv_of_root _ _ (Nat.mul_ne_zero hnc.ne' hnn) hp
    refine ⟨o, hinj ?_⟩
    rw [e4, map_smulₛₗ]
    congr 1
    change _ = ρ'.ek i b k (algebraMap _ _ o)
    rw [ho, map_inv₀, hu, inv_inv]

end Coord

theorem mem_GfC_of_suppAt {D : D7} {V : TH.HSp D} {Q : Finset (Pl D.host.E)} (hQ : SplitSet Q) {g : GA D V}
    (hg : SuppAt (idem Q) V g) : g ∈ GfC V := by
  have h0 := GlobalTheory.PlaceVec.idemSum_infPart hQ.isIdemSum
  have hf : infPart D (idem Q + cA D (idem Q)) = 0 := by rw [map_add, h0, GlobalTheory.PlaceVec.infPart_cA h0, add_zero]
  refine Units.ext (Matrix.ext fun a c => ?_)
  have h := congrArg (infPart D) (hg a c)
  rw [map_mul, hf, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero] at h
  change infPart D (Formalism.L2.Theta.mt V g a c) = (1 : Matrix _ _ _) a c
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

abbrev baseW (ex : Extra D L hT Gi Gl Kc Y cX) (w : D.what₂.places.Pl) (j : Fin D.R.m) (ρ : Setup D.ntw) : Base (Vc D j) (Wc D j) :=
  ρ.B (ex.nch.twI w) j (ex.nch.sd w)

abbrev twW (ex : Extra D L hT Gi Gl Kc Y cX) (w : D.what₂.places.Pl) (ρ : Setup D.ntw) : Twist D Circle :=
  ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)

abbrev genW (ex : Extra D L hT Gi Gl Kc Y cX) (w : D.what₂.places.Pl) (j : Fin D.R.m) (ρ : Setup D.ntw) (ψ : Twist D Circle)
    (h : GA D (Vc D j)) : PolF D (Wc D j).rank (Vc D j).rank →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
  (baseW ex w j ρ).gen (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) ψ h

variable (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)

def OneAt : Prop := ∀ (ρ ρ' : Setup D.ntw) (ν : ℂ), ρ.Good → ρ'.Good → RealPin p.R p.cG ρ → SameBut ρ ρ' → ρ.LevelOf D.nexp →
  (Adapted p w ρ ∨ Adapted p w ρ') → IsNorm p.R p.v₀ (baseW ex w j ρ) ν →
  ∀ h₀, ∀ P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h₀, ∀ h ∈ GfC (Vc D j), ∀ τ : ℂ ≃+* ℂ,
    (∀ z, τ (Formalism.L2.Host.embLL0 D z) = Formalism.L2.Host.embLL0 D z) → ConjChar τ (twW ex w ρ) (twW ex w ρ') →
    ∃ c : ℂ, IsRoot1 c ∧ ∃ (n : ℕ) (β : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
      ν • genW ex w j ρ (twW ex w ρ) h P = ∑ l, β l • evW p.nexp p.v₀ j (g l).val ∧
      ∑ l, τ (β l) • evW p.nexp p.v₀ j (g l).val = c • ν • genW ex w j ρ (twW ex w ρ') h P

theorem twLat_le (hU : p.R.toRealDat.LUnif) (hW : p.R.toRealDat.models_HW) (hv : FWT.IsChosenExtremalVector p.R.toRealDat j (sg0 D p.P.A3.A) (p.v₀ j _))
    (hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm)
    (hψ : IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))
    (hgen : ∀ (ρ : Setup D.ntw), ρ.Good → RealPin p.R p.cG ρ → ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range h →
      P ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
        (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)))
    (hone : OneAt p w j) (ρ ρ' : Setup D.ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ) (hp : RealPin p.R p.cG ρ)
    (hS : SameBut ρ ρ') (hL : ρ.LevelOf D.nexp) (hA : Adapted p w ρ ∨ Adapted p w ρ') (hN : IsNorm p.R p.v₀ (baseW ex w j ρ) ν)
    (hν' : ν' ≠ 0) (hνν : ∃ n : ℕ, n ≠ 0 ∧ ν' ^ n = ν ^ n) (hR : RatAt p w j hρ ν) (hR' : RatAt p w j hρ' ν') :
    twLat p w j hρ ν ≤ twLat p w j hρ' ν' := by
  have hbad := hS.2.2.1
  have hB := hS.2.2.2.1
  have hom := hS.2.2.2.2
  have hQ : (twW ex w ρ').Q = (twW ex w ρ).Q := by simp only [Setup.tw, twistOf, hS.2.1]
  have hg : ∀ ψ h, genW ex w j ρ' ψ h = genW ex w j ρ ψ h := fun ψ h => by simp only [genW, baseW, hB, hom]
  have hlat : ∀ O h, ρ'.lat (ex.nch.twI w) j (ex.nch.sd w) O h = ρ.lat (ex.nch.twI w) j (ex.nch.sd w) O h := by
    intro O h
    simp only [Setup.lat, hB]
  have hinj := (realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ (ex.nch.twI w) j (ex.nch.sd w) ν hN.1 hU hW hv
    hK).injective_rdK hρ (ex.nch.k' w)
  have hgood := (GlobalTheory.TwistGood.tw_good _ _ _ ρ hρ _ j (ex.nch.sd w) _ _ _ hψ).1
  have hsm : ∀ (o : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) y,
      GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.incl D.nexp (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w) (ex.nch.Oe w) (ex.nch.k' w) (o • y) =
        algebraMap _ (ex.nch.Oe w) o •
          GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.incl D.nexp (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w) (ex.nch.Oe w) (ex.nch.k' w) y := fun o y => by
    induction y using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
    | tmul a f =>
      rw [TensorProduct.smul_tmul', GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.incl, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.smul_tmul']
      congr 1
      simp [Algebra.smul_def]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨y, ⟨s, h, P, hd, hQ', hsup, hy⟩, rfl⟩
  have hfin : h * hQ' ∈ GfC (Vc D j) := mul_mem hd.fin (mem_GfC_of_suppAt hgood.split hsup)
  have key : ∀ P₁ ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
      (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)),
      ∃ z, rdK (rdAt p w j hρ ν) hρ (ex.nch.k' w) z = genW ex w j ρ (twW ex w ρ) (h * hQ') P₁ ∧
        GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.incl D.nexp (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w) (ex.nch.Oe w) (ex.nch.k' w) z ∈
          twLat p w j hρ' ν' := by
    intro P₁ hP₁
    induction hP₁ using Submodule.span_induction with
    | mem P₁ hP₁ =>
      have hd1 : ρ.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h P₁ :=
        ⟨hd.split, hd.off, hd.fin, hd.supp, lat_mono ρ _ j _ (smallInt_le hρ _ _) h hP₁⟩
      have hd2 : ρ'.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h P₁ :=
        ⟨hd.split, by rw [hbad]; exact hd.off, hd.fin, hd.supp,
          lat_mono ρ' _ j _ (smallInt_le hρ' _ _) h (by rw [hlat]; exact hP₁)⟩
      have hm' : genW ex w j ρ' (twW ex w ρ') (h * hQ') P₁ ∈ ρ'.gens (ex.nch.twI w) j (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w)
          (GlobalTheory.TwistIndex.chosenChar ex.nch w) h P₁ := ⟨hQ', hQ.symm ▸ hsup, rfl⟩
      obtain ⟨z, hz⟩ := hR.2 s h P₁ hd1 ⟨hQ', hsup, rfl⟩
      obtain ⟨z', hz'⟩ := hR'.2 s h P₁ hd2 hm'
      obtain ⟨o, ho⟩ := eq_smul_of_conj p.nexp p.v₀ j hU hW hv hK hρ hρ' _ _ _ hN.1 hν' hνν z z' fun τ h1 h2 => by
        have := hone ρ ρ' ν hρ hρ' hp hS hL hA hN h P₁ hP₁ _ hfin τ h1 (conjChar_tw hS _ hψ h2)
        rwa [← hg (twW ex w ρ'), ← hz', show genW ex w j ρ (twW ex w ρ) (h * hQ') P₁ = _ from hz.symm] at this
      refine ⟨z, hz, ?_⟩
      rw [ho, hsm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z', ⟨s, h, P₁, hd2, hz' ▸ hm'⟩, rfl⟩)
    | zero => exact ⟨0, by rw [map_zero, map_zero], by rw [map_zero]; exact zero_mem _⟩
    | add P₁ P₂ _ _ h1 h2 =>
      obtain ⟨g1, e1, m1⟩ := h1
      obtain ⟨g2, e2, m2⟩ := h2
      exact ⟨g1 + g2, by rw [map_add, map_add, e1, e2], by rw [map_add]; exact add_mem m1 m2⟩
    | smul a P₁ _ h1 =>
      obtain ⟨g1, e1, m1⟩ := h1
      obtain ⟨o, ho⟩ := a.2
      refine ⟨algebraMap _ (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) o • g1, ?_, by rw [hsm]; exact Submodule.smul_mem _ _ m1⟩
      rw [map_smulₛₗ, e1, hρ.ek_e, ho]
      exact (map_smul _ (a : ℂ) P₁).symm
  obtain ⟨z, hz, hm⟩ := key P (hgen ρ hρ hp h P hd.mem)
  rw [hinj (hy.trans hz.symm)]
  exact hm

end Point

section Tuples

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def HasTuples (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)) (ψ ψ' : Twist D Circle) : Prop :=
  ∃ (T0' : Type) (A' : FamIn D.what₂.LL G Pl0 T0' D.R.m) (R' : RealDat D A' T.Q.c.F) (F' : Face D A')
    (v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)),
    GlobalTheory.Hk3.Core R' F' ∧ Finite T0' ∧ Nonempty (FWTie T R' κ v₀') ∧ IoExt R' ∧ QGuard R' ∧ OMPins T R' κ v₀' O' j ∧
    PhaseTie T R' κ v₀' O' ph j ∧ BaseOf R' j B ∧ (∀ τ, FixBase T R j τ → FixBase T R' j τ) ∧
    (∀ τ ζ Φ Φ', ConjFun (O' j) (κ j) τ ζ Φ Φ' → ConjFun (O j) (κ j) τ ζ Φ Φ') ∧
    (∀ (c : VsV D j ℂ →ₗ[ℂ] (R.cV j).W) (u : ∀ ρ, lowT (R.MW j (sg0 D A)) ρ), ExtC R j (inC (O j).c') (O j).c0' c →
      (∀ ρ, (u ρ : (R.MW j (sg0 D A)).sm ρ) = v₀ j (sg0 D A) ρ) →
      ∃ (c' : VsV D j ℂ →ₗ[ℂ] (R'.cV j).W) (u' : ∀ ρ, lowT (R'.MW j (sg0 D A')) ρ), ExtC R' j (inC (O' j).c') (O' j).c0' c' ∧
        (∀ ρ, (u' ρ : (R'.MW j (sg0 D A')).sm ρ) = v₀' j (sg0 D A') ρ) ∧
        ∀ x, R'.ioP j (PiTensorProduct.tprod ℂ u') (c' x) = R.ioP j (PiTensorProduct.tprod ℂ u) (c x)) ∧
    ∃ t t', IsTupOf R' B ψ t ∧ IsTupOf R' B ψ' t'

theorem hasTuples_self {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} {ph : Fin D.R.m → ℂ} {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)}
    {ψ ψ' : Twist D Circle} (h1 : GlobalTheory.Hk3.Core R F) (h2 : Finite T0) (h3 : Nonempty (FWTie T R κ v₀)) (h4 : IoExt R) (h5 : QGuard R)
    (h6 : OMPins T R κ v₀ O j) (h7 : PhaseTie T R κ v₀ O ph j) (h8 : BaseOf R j B) {t t' : T0} (ht : IsTupOf R B ψ t)
    (ht' : IsTupOf R B ψ' t') : HasTuples T R κ v₀ O ph j B ψ ψ' :=
  ⟨T0, A, R, F, v₀, O, h1, h2, h3, h4, h5, h6, h7, h8, fun _ h => h, fun _ _ _ _ h => h, fun c u hc hu => ⟨c, u, hc, hu, fun _ => rfl⟩,
    t, t', ht, ht'⟩

end Tuples

theorem baseOf_of_realPin {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} (hL : Rl.toLevCh.Is A3.A.μ0) {ρ : Setup D.ntw} (hρ : ρ.Good)
    (hp : RealPin Rl cG ρ) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) : BaseOf Rl.toRealDat j (ρ.B i j b) := by
  have hB := hρ.base i j b
  have hlam := GlobalTheory.BaseLiftWeight.lam_eq D _ Rl.toLevCh A3.A.μ0 j (ρ.B i j b) hL hB (hp.mu0 i j b) (hp.ap i j b) (hp.am i j b)
  have hc : ∀ τ, (ρ.B i j b).w.c τ = liftC D j τ := fun τ => GlobalTheory.BaseLiftWeight.c_eq hL hB (hp.mu0 i j b) τ
  have hP : (ρ.B i j b).w.p = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS D j := funext fun τ => congrArg Prod.fst (hB.sig τ)
  have hQ : (ρ.B i j b).w.q = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS D j := funext fun τ => congrArg Prod.snd (hB.sig τ)
  have hAP : (ρ.B i j b).w.ap = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aP D j := funext fun τ => hp.ap i j b τ
  have hAM : (ρ.B i j b).w.am = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aM D j := funext fun τ => hp.am i j b τ
  refine
    { ψ := hp.psi i j b, θ := hp.inf i j b, sT := hp.cartT i j b, BS := hp.onbS i j b, BT := hp.onbT i j b,
      ΛS := hp.latS i j b, ΛT := hp.latT i j b, βS := hp.frS i j b, βT := hp.frT i j b, vac := hp.vac i j b,
      Pg := hp.Pg i j b, mu0 := hp.mu0 i j b, eta := hp.eta i j b, lam := hlam, delta := ?_, p := hP, q := hQ,
      c := funext hc }
  rw [← liftWeight_delta, Weight.delta, Weight.delta, hP, hQ, hAP, hAM]
  rfl

abbrev phs {eps : ℝ} {Fm : FamP eps} {x : ℝ} {hx : Fm.x1 < x} {i : Fm.Ix x} (p : Pt Fm x hx i) (j : Fin (Fm.D x i).R.m) : ℂ :=
  cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) (p.R.phs j)

def TwOne : Prop := AtTw fun _ _ _ _ p w j => OneAt p w j

def TupAt : Prop := AtTw fun Fm x hx i p w j => ∀ ρ ρ' : Setup (Fm.D x i).ntw, ρ.Good → ρ'.Good → RealPin p.R p.cG ρ →
  SameBut ρ ρ' → (Adapted p w ρ ∨ Adapted p w ρ') →
  HasTuples p.T p.R.toRealDat p.κ p.v₀ p.O (phs p) j (baseW (Fm.ex x hx i) w j ρ) (twW (Fm.ex x hx i) w ρ) (twW (Fm.ex x hx i) w ρ')

def FixAt : Prop := AtTw fun Fm x hx i p w j => ∀ ρ : Setup (Fm.D x i).ntw, ρ.Good → RealPin p.R p.cG ρ →
  ρ.LevelOf (Fm.D x i).nexp → ∀ τ : ℂ ≃+* ℂ, (∀ z, τ (Formalism.L2.Host.embLL0 (Fm.D x i) z) = Formalism.L2.Host.embLL0 (Fm.D x i) z) →
  FixBase p.T p.R.toRealDat j τ ∧ FixDat (baseW (Fm.ex x hx i) w j ρ) τ

def CoefAt : Prop := AtTw fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (ν : ℂ), ρ.Good → RealPin p.R p.cG ρ →
  IsNorm p.R p.v₀ (baseW (Fm.ex x hx i) w j ρ) ν →
  ∃ (c : VsV (Fm.D x i) j ℂ →ₗ[ℂ] (p.R.cV j).W) (u : ∀ σ, lowT (p.R.MW j (sg0 (Fm.D x i) p.P.A3.A)) σ) (ξ : ℂ),
    ExtC p.R.toRealDat j (inC (p.O j).c') (p.O j).c0' c ∧
    (∀ σ, (u σ : (p.R.MW j (sg0 (Fm.D x i) p.P.A3.A)).sm σ) = p.v₀ j (sg0 (Fm.D x i) p.P.A3.A) σ) ∧ IsRoot1 ξ ∧
    ∀ h₀, ∀ P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h₀,
      ∃ y : VsV (Fm.D x i) j ℂ, ν • P = (ξ * phs p j) • p.R.ioP j (PiTensorProduct.tprod ℂ u) (c y) ∧
        ∀ τ : ℂ ≃+* ℂ, (∀ z, τ (Formalism.L2.Host.embLL0 (Fm.D x i) z) = Formalism.L2.Host.embLL0 (Fm.D x i) z) → ConjVec j τ y y

def NormAt : Prop := AtTw fun Fm x _ i p _ j => ∀ (B : Base (Vc (Fm.D x i) j) (Wc (Fm.D x i) j)) (ν ν' : ℂ),
  IsNorm p.R p.v₀ B ν → IsNorm p.R p.v₀ B ν' → ∃ n : ℕ, n ≠ 0 ∧ ν' ^ n = ν ^ n

theorem conjTw_of_one (hA : TwAdm) (hG : LatSmallGen) (hN : NormAt) (hO : TwOne) : ConjTw := by
  refine AtTw.imp (AtTw.and (AtTw.and hA hG) (AtTw.and hN hO)) fun Fm x hx i p hr hm w _ j H => ?_
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := H
  intro ρ ρ' hρ hρ' ν ν' hp hS hν hR hF
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  have hL : ρ.LevelOf (Fm.D x i).nexp := levelOf_of_sameBut hm.2.2 hρ' hρ hF.pin hp hS.symm hF.level
  have hν' := hF.norm
  have hν'' := hν'
  rw [hS.2.2.2.1] at hν''
  exact le_antisymm
    (twLat_le p w j hU hW (Z.vec j) hK a1.1 a2 a4 ρ ρ' hρ hρ' ν ν' hp hS hL (Or.inr hF.adapted) hν hν'.1 (a3 _ _ _ hν hν'') hR hF.rat)
    (twLat_le p w j hU hW (Z.vec j) hK a1.1 a2 a4 ρ' ρ hρ' hρ ν' ν hF.pin hS.symm hF.level (Or.inl hF.adapted) hν' hν.1
      (a3 _ _ _ hν'' hν) hF.rat hR)

end GlobalTheory.BigOn.Exp.TwConj
