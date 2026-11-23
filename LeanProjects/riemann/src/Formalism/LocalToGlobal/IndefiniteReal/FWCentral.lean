import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.ConjLemmas
import Formalism.LocalToGlobal.IndefiniteReal.MultGood
import Formalism.LocalToGlobal.ProjectiveLattices.MuValFix
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ImageLcv
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT

noncomputable section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.JoinChr Formalism.IndefR.Links
  Formalism.IndefR.Arith Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {D : D7}

variable (D) in

def PlIdemEx : Prop := ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e, IsPlIdem D e P

end Loc

section Frame

open ReciprocityTheory.ChartRestriction.G.FD

theorem arr_inj {n q : ℕ} (_hq : q ≤ n) : Function.Injective (arr (n := n) q) := by
  intro c c' h
  have h1 := congrArg Fin.val h
  have h2 := c.2
  have h3 := c'.2
  unfold arr at h1
  apply Fin.ext
  split_ifs at h1 <;> simp only at h1 <;> omega

def arrE {n q : ℕ} (hq : q ≤ n) : Fin n ≃ Fin n :=
  Equiv.ofBijective (arr q) (Finite.injective_iff_bijective.1 (arr_inj hq))

variable {D : D7}

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

def Shape (q : ℕ) : Prop := q ≤ V.rank ∧ ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < V.rank - q)

variable {M}

variable (M) in

abbrev reframe (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hu : ∀ τ, IsUnit (fr τ))
    (hg : ∀ τ, (fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * fr τ = gramAt D V τ) : DSModel V S :=
  { M with fr := fr, fr_unit := hu, fr_gram := hg }

end Frame

section Cut

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

omit [Algebra T.Q.c.F D.what₂.LL] in

def ChiRec (C : Formalism.L2.Host.CharFrame D) : Prop :=
  ∀ i : Fin D.R.m, ChrEq (T.chiW ((i : ℕ) + 1) T.toCore.σ₀) (C.mu0 i)

def ChiAlg : Prop :=
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → IsHeckeChar D (T.chiW ((i : ℕ) + 1) (res T σ)) ∧
    (∀ ρ, HasInfExp D (T.chiW ((i : ℕ) + 1) (res T σ)) ρ (-(D.hc (lab σ ρ)).e i)) ∧
    ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : T.Q.c.F,
      ((T.chiW ((i : ℕ) + 1) T.toCore.σ₀ x : Circle) : ℂ) = T.toCore.σ₀ y ∧ ((T.chiW ((i : ℕ) + 1) (res T σ) x : Circle) : ℂ) = res T σ y

end Cut

section Central

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G0 : Type} [Group G0] [Fintype G0] (A : FormsL LL Ks WL W G0)

def IsRootU (ζ : LLˣ) : Prop := ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1

theorem IsRootU.int {ζ : LLˣ} (h : IsRootU ζ) : ∃ a : 𝓞 LL, (a : LL) = ζ := by
  obtain ⟨n, hn, h⟩ := h
  have h1 : (ζ : LL) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  exact ⟨⟨ζ, IsIntegral.of_pow hn (h1 ▸ isIntegral_one)⟩, rfl⟩

theorem IsRootU.norm {ζ : LLˣ} (h : IsRootU ζ) (σ : LL →+* ℂ) : ‖σ ζ‖ = 1 := by
  obtain ⟨n, hn, h⟩ := h
  refine Complex.norm_eq_one_of_pow_eq_one ?_ hn.ne'
  rw [← map_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, map_one]

def cen (ζ : LLˣ) (z : G0) : WL →ₗ[LL] WL := (ζ : LL) • A.ρ z

theorem cen_apply (ζ : LLˣ) (z : G0) (x : WL) : cen A ζ z x = (ζ : LL) • A.ρ z x := rfl

theorem cen_cen (ζ ζ' : LLˣ) (z z' : G0) (x : WL) : cen A ζ z (cen A ζ' z' x) = cen A (ζ * ζ') (z * z') x := by
  rw [cen_apply, cen_apply, cen_apply, LinearMap.map_smul, smul_smul, map_mul, Units.val_mul]
  rfl

theorem cen_one (x : WL) : cen A 1 1 x = x := by
  rw [cen_apply, map_one, Units.val_one, one_smul]
  rfl

def cenE (ζ : LLˣ) (z : G0) : WL ≃ₗ[LL] WL :=
  LinearEquiv.ofLinearMap (cen A ζ z) (cen A ζ⁻¹ z⁻¹)
    (LinearMap.ext fun x => by rw [LinearMap.comp_apply, cen_cen, mul_inv_cancel, mul_inv_cancel, cen_one]; rfl)
    (LinearMap.ext fun x => by rw [LinearMap.comp_apply, cen_cen, inv_mul_cancel, inv_mul_cancel, cen_one]; rfl)

variable {ζ : LLˣ} {z : G0}

end Central

section Mat

open Formalism.IndefR.Cx Formalism.L2.Indef

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool)
  (i : Fin D.R.m)

theorem principal_form_tensor_expansion (c : Fin (finrank D.what₂.LL (R.toRealDat.WL F.lv2 b i)) → ℂ) :
    Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).w0C b i c) =
      ∑ l, cj (twAt D.what₂.embLL A3.A.v0) (c l) • (R.FW i).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 b i l) := by
  have hnP : ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < RealDat.nP F.lv2 b := by unfold RealDat.nP; exact_mod_cast Nat.card_pos
    exact_mod_cast (Real.sqrt_pos.2 this).ne'
  show ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).subtype
    (∑ l, cj (twAt D.what₂.embLL A3.A.v0) (c l) •
      (⟨R.toRealDat.bC F.lv2 b i _ l, Submodule.subset_span ⟨l, rfl⟩⟩ : R.toRealDat.WS F.lv2 b i (sg0 D A3.A))) = _
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [LinearMap.map_smul, smul_comm]
  congr 1
  show ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • (((Real.sqrt (RealDat.nP F.lv2 b))⁻¹ : ℝ) : ℂ) •
    (R.FW i).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 b i l) = _
  rw [smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hnP, one_smul]

abbrev zVec (t : T0) (k : Fin ((lv (F.fc (R.toCx3 F).zs) b).dZ i t)) : A3.A.fam.amb.FL i t :=
  F.cr.toL (R.toCx3 F).zs b i t (Pi.single k 1)

end Mat

section CC

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]
  {D : D7} {V : HSp D} {σ0 : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ0 r} {dict : GA D V → Σ k, Frame (U.X k).Ψ r}
  {mu : GA D V → ℂ} {xr : ℝ} {a : (E →+* ℂ) × ℕ → ℕ} {G : Type} [Group G] {act : G → Rul Xo c →ₗ[c.F] Rul Xo c} {Tup : Type}
  {dδ : Tup → DeltaDat Xo c n} {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)]
  {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c.F} {La : ∀ t, Cl' t → GenLat E n} {Nc gam : ∀ t, Cl' t → ℕ}
  {vol : Tup → c.F} {ep : ∀ t, Cl' t → c.F} {io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F}
  {thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop} {LL : IntermediateField ℚ ℂ}
  {Cu : Submodule c.F (Rul Xo c)} {cc cc' : U.Comp → ℂ} {ph ph' : ℂ}

def RootC (ζ : ℂ) : Prop := ∃ m : ℕ, 0 < m ∧ ζ ^ m = 1

theorem RootC.mul {x y : ℂ} (hx : RootC x) (hy : RootC y) : RootC (x * y) := by
  obtain ⟨m, hm, h⟩ := hx
  obtain ⟨k, hk, h'⟩ := hy
  exact ⟨m * k, Nat.mul_pos hm hk, by rw [mul_pow, pow_mul, h, one_pow, mul_comm m, pow_mul, h', one_pow, one_mul]⟩

theorem RootC.ne_zero {x : ℂ} (hx : RootC x) : x ≠ 0 := by
  obtain ⟨m, hm, h⟩ := hx
  rintro rfl
  rw [zero_pow hm.ne'] at h
  exact zero_ne_one h

variable (U dict mu a act dδ Cl' w La Nc gam vol ep io Pl) in

def EigOn (k : U.Comp) : Prop :=
  ∃ t x, Pl t x ∧ ∃ f ∈ sec Xo c a n, IsThClsD Xo c (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f ∧
    (∀ z ∈ Subgroup.center G, ∃ om : c.F, RootC (σ0 om) ∧ act z f = om • f) ∧
    ∃ q : AutQ V, (dict q.out).1 = k ∧ jFn V σ0 (rdU U) dict mu f q ≠ 0

variable (U dict mu a dδ Cl' w La Nc gam vol ep io Pl) in

def ThOn (k : U.Comp) : Prop :=
  ∃ t x, Pl t x ∧ ∃ f ∈ sec Xo c a n, IsThClsD Xo c (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f ∧
    ∃ q : AutQ V, (dict q.out).1 = k ∧ jFn V σ0 (rdU U) dict mu f q ≠ 0

variable (U dict mu a act dδ Cl' w La Nc gam vol ep io Pl) in

def CenSplit : Prop :=
  ∀ k, ThOn U dict mu a dδ Cl' w La Nc gam vol ep io Pl k → EigOn U dict mu a act dδ Cl' w La Nc gam vol ep io Pl k

end CC

section CCTie

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} {hle : c.F ≤ c'.F} {n r : ℕ} {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]
  {LL : IntermediateField ℚ ℂ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ0' : c'.F →+* ℂ} {D : D7} {V : HSp D}
  {dict : GA D V → Σ k, Frame ((unfBC hle U σ0').X k).Ψ r} {mu : GA D V → ℂ} {xr : ℝ} {a : (E →+* ℂ) × ℕ → ℕ}
  {G : Type} [Group G] {act : G → Rul Xo c →ₗ[c.F] Rul Xo c} {act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c'} {Tup : Type}
  {dδ : Tup → DeltaDat Xo c' n} {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)]
  {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F} {La : ∀ t, Cl' t → GenLat E n} {Nc gam : ∀ t, Cl' t → ℕ}
  {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F} {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
  {thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop} {cc cc' : (unfBC hle U σ0').Comp → ℂ} {ph ph' : ℂ}

end CCTie

section CCDat

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

def OMDat.ThOn (k : (C.U ((i : ℕ) + 1) O.s0).Comp) : Prop :=
  FWT.ThOn (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (wtA κ) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.Plc k

def OMDat.CenSplit : Prop :=
  FWT.CenSplit (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (wtA κ) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam
    O.vol O.ep O.io O.Plc

end CCDat

section Phase

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem phiC_zero {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    phiC T hV a 0 = 0 := by
  subst hV
  show T.phiJ j σ a 0 = 0
  rw [CoreJ.phiJ, map_zero, map_zero, smul_zero]

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem phiC_apply {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (h : σ = σ') {W : HSp D} (hV : T.V j σ = W) (hV' : T.V j σ' = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D W) :
    phiC T hV a f g = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * adel W (castDict hV' (T.dict j σ'))
      (muPin W (castDict hV' (T.dict j σ')) (castDict hV' (T.mu j σ')) (T.cE j σ')) (rdU (T.U j σ') f) g := by
  subst h
  subst hV
  rfl

theorem FWTie.evaluates_of_lUnif (t : FWTie T R κ v₀) (hU : R.LUnif) : t.Evaluates := by
  intro i σ hσ hV
  refine t.ev i σ hσ hV (Classical.byContradiction fun hn => hn ⟨0, fun f => ?_⟩)
  have h0 := t.ev0 i σ hσ hV hn
  have h1 := (hU i σ).1 _ _ (Pi.basisFun D.what₂.LL (Fin (R.nW i))).linearIndependent
  have h2 : ((t.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = 0 :=
    funext fun k => absurd (by rw [h0]; rfl) (h1.ne_zero k)
  have h3 : f = 0 := (t.e i).map_eq_zero_iff.1 (Subtype.ext h2)
  subst h3
  exact (congrArg (fun F : MMap (R.MW i σ) => F (v₀ i σ)) (R.HW i σ).e.map_zero).trans (phiC_zero hV _).symm

theorem FWTie.rat_of_val (t : FWTie T R κ v₀) (ht : t.Evaluates) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (hσ : GoodEmb T.Q.c (res T σ))
    (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (hinj : Function.Injective (evAt R i σ (v₀ i σ))) {w : (R.HW i σ).H} {n : ℕ}
    (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κ i)
    (h : ∀ g, evAt R i σ (v₀ i σ) w g = ∑ k, σ (a k) * phiC T hV (wtA (κ i)) (f k : T.R ((i : ℕ) + 1)) g) :
    ∃ y, (R.FW i).j σ y = w := by
  refine ⟨∑ k, a k • ((t.e i (f k) : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL), hinj (funext fun g => ?_)⟩
  rw [h g, evAt, map_sum, map_sum, _root_.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ, map_smul, ← ht i σ hσ hV (f k)]
  rfl

theorem baseEmbedding_restriction_eq_coefficientInclusion (t : FWTie T R κ v₀) {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) :
    res T (sg0 D A) = O.s0 :=
  (congrArg (res T) (sgAt_mk _ R.hv0)).trans ((res_embLL T t.alg_eq t.laws.pins.2.2.1).trans (sOv_eq T.toCore O.c' O.hle).symm)

theorem phi_eq_phiC {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) {σ : T.Q.c.F →+* ℂ} (hs : σ = O.s0)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (g : GA D (Wc D i)) :
    (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * O.phi (T.cE ((i : ℕ) + 1) O.s0) f g = phiC T hV a f g :=
  (phiC_apply hs hV O.hV a f g).symm

theorem evAt_smul (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) (c : ℂ) (w : (R.HW i σ).H) (g : GA D (Wc D i)) :
    evAt R i σ v (c • w) g = c * (R.HW i σ).e w v g := by
  rw [evAt, map_smul]
  rfl

theorem phase_of_phRat (t : FWTie T R κ v₀) (hU : R.LUnif) {i : Fin D.R.m}
    (hinj : Function.Injective (evAt R i (sg0 D A) (v₀ i (sg0 D A)))) {Tp : Type} {tup : Tp → T0}
    (O : OMDat T.toCore R i Tp tup) {ph : ℂ} (h : O.PhRat (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O.s0) ph)
    (x : A.fam.amb.FL i A.μ0) : ∃ y, (R.FW i).j (sg0 D A) y = ph • R.thG i A.μ0 (R.jV i A.μ0 x) :=
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) (baseEmbedding_restriction_eq_coefficientInclusion t O)).trans O.hV
  have hg : ∀ y, D.what₂.embLL y = sg0 D A y := fun y => (DFunLike.congr_fun (sgAt_mk _ R.hv0) y).symm
  (h x).elim fun _ h1 => h1.elim fun a h2 => h2.elim fun f hf =>
    t.rat_of_val (t.evaluates_of_lUnif hU) (base_embedding_good T R t.alg_eq t.laws.pins.2.2.1) hV hinj a f fun g =>
      (evAt_smul i _ _ ph _ g).trans ((hf g).trans (Finset.sum_congr rfl fun _ _ =>
        congrArg₂ (· * ·) (hg _) (phi_eq_phiC O (baseEmbedding_restriction_eq_coefficientInclusion t O) hV _ _ g)))

theorem phase_of_oneMap (t : FWTie T R κ v₀) (hU : R.LUnif) {i : Fin D.R.m}
    (hinj : Function.Injective (evAt R i (sg0 D A) (v₀ i (sg0 D A)))) {Tp : Type} {tup : Tp → T0}
    (O : OMDat T.toCore R i Tp tup) {ph : ℂ} (h : O.OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O.s0) ph) :
    ‖ph‖ = 1 ∧ ∀ x, ∃ y, (R.FW i).j (sg0 D A) y = ph • R.thG i A.μ0 (R.jV i A.μ0 x) :=
  ⟨h.2.1.2.2.2.2.1, phase_of_phRat t hU hinj O h.2.2⟩

end Phase

end Formalism.IndefR.FWT
