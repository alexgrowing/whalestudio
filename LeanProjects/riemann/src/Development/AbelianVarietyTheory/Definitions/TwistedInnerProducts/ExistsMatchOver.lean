import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTestLatUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus posDef_dual rowForm Cols)

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Columns

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (θ : InfFam D)

def colOf (Ψ : GLf G → WtSp G) : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W := fun g =>
  GlobalTheory.CoefModel.toHilb (LaP G) (posDef_dual G)
    (GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP G) (Ψ (Formalism.UG.bc (Lev.swapAE D) (g : GL _ _))))

theorem pairVec_colOf (ξ : Module.Dual ℂ (coefPlus G θ).W) (Ψ : GLf G → WtSp G) :
    pairVec (coefPlus G θ) ξ (colOf θ Ψ) = scal θ (ξ ∘ₗ (GlobalTheory.CoefModel.toHilb (LaP G) (posDef_dual G)).toLinearMap) Ψ := by
  funext h
  exact congrArg ξ (GlobalTheory.CoefModel.rhoH_toHilb (LaP G) (posDef_dual G) _ _)

theorem fin_mul (γ : GQ (Xp G)) (γE : UR D.sp.cm (Xp G).gram) (hm : Bridge.IsRatMat (Xp G) γ γE.1) (g k : Bridge.Gf (Xp G)) :
    Formalism.UG.bc (Lev.swapAE D) (Bridge.ratF (Xp G) γ * g * k).1 =
      ratIn G γE * Formalism.UG.bc (Lev.swapAE D) g.1 * Formalism.UG.bc (Lev.swapAE D) k.1 := by
  rw [← TestLatModel.finE_rat γ γE hm, Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  rfl

variable {θ} in

theorem map_rat (hθ : IsInfFam θ) (V : HSp D) (lam : D.what₂.Tau → DomWeight V.rank) (γ : GQ V)
    (γE : GL (Fin V.rank) D.host.E) (h : Bridge.IsRatMat V γ γE) (v : VV D.what₂.LL lam) :
    GlobalTheory.CoefModel.mapVV D.what₂.embLL lam (rhoVr (labLL D) lam γE v) =
      rhoK lam (invTrK (GlobalTheory.CoefModel.realGL θ V γ)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL lam v) := by
  have h := TestLatModel.map_rhoVr hθ V lam γ γE h γ.1⁻¹ v
  rwa [mul_inv_cancel, inv_one, map_one (GlobalTheory.CoefModel.realGL θ V), map_one invTrK, map_one (rhoK lam), inv_inv,
    Module.End.one_apply] at h

variable {θ} in

theorem colOf_mem (hθ : IsInfFam θ) {Ψ : GLf G → WtSp G} (hl : ∀ γ g, Ψ (ratIn G γ * g) = rhoW G γ (Ψ g))
    (hr : ∀ g, ∀ k ∈ G.Kplus, Ψ (g * k) = Ψ g) : colOf θ Ψ ∈ Cols G θ := by
  refine (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.mem_cols G θ _).2 fun γ g k => ?_
  obtain ⟨γE, hU, hγ⟩ := γ.2
  have hm : Bridge.IsRatMat (Xp G) γ γE := hγ.symm
  have hk : Formalism.UG.bc (Lev.swapAE D) k.1.1 ∈ G.Kplus := k.2
  unfold colOf
  rw [fin_mul γ ⟨γE, hU⟩ hm g k.1, hr _ _ hk, hl]
  exact (congrArg (GlobalTheory.CoefModel.toHilb (LaP G) (posDef_dual G)) (map_rat hθ _ _ γ γE hm _)).trans
    (GlobalTheory.CoefModel.rhoH_toHilb (LaP G) (posDef_dual G) _ _).symm

end Columns

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure ChainVec (R : RealDat D A Ks) where

  polY : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank

  polX : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank

  v : SmT R.MX

namespace ChainVec

variable {R : RealDat D A Ks} (d : ChainVec R)

noncomputable def dnVec : ∀ n, SmT (R.MY n) →ₗ[ℂ] SmT (R.MY 0)
  | 0 => LinearMap.id
  | n + 1 => dnVec n ∘ₗ R.ItY n (d.polY n)

def w : SmT (R.MY 0) := d.dnVec (D.R.m - 1) (R.ItX d.polX d.v)

noncomputable def dnFun (t : T) : ∀ n, (GA D (Yc D n) → ℂ) → GA D (Yc D 0) → ℂ
  | 0, φ => φ
  | n + 1, φ => dnFun t n (Lift.liftInt (R.νY t (n + 1)) (R.fdY t (n + 1)) (thetaKO (R.ωY t n)) (R.ptY t n (d.polY n)) φ)

def formX (t : T) (x : (R.HX t).H) : GA D D.sp.X' → ℂ := R.cX.toMap R.prX ((R.HX t).e x) d.v

def lift (t : T) (x : (R.HX t).H) : GA D (Yc D 0) → ℂ :=
  d.dnFun t (D.R.m - 1) (Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t d.polX) (d.formX t x))

theorem dnFrom_dnVec (h : R.chain_ioY) (t : T) : ∀ n, n ≤ D.R.m - 1 → ∀ (F : R.CC t n) (v : SmT (R.MY n)),
    (Lift.dnFrom (R.CC t) (R.ioY t) n F).1 (d.dnVec n v) = d.dnFun t n (F.1 v)
  | 0, _, _, _ => rfl
  | n + 1, hn, F, v => (dnFrom_dnVec h t n (by omega) (R.ioY t n F) (R.ItY n (d.polY n) v)).trans
      (congrArg (d.dnFun t n) (funext fun g => ((h t n hn).eq F (d.polY n) v g).symm))

theorem thDn_w (h : R.IsChain) (t : T) (x : (R.HX t).H) : R.thDn t x d.w = d.lift t x :=
  (d.dnFrom_dnVec h.ioY t _ le_rfl _ _).trans
    (congrArg (d.dnFun t _) (funext fun g => ((h.ioX t).eq _ d.polX d.v g).symm))

theorem rowForm_Th (h : R.IsChain) (t : T) (x : (R.HX t).H) : rowForm R d.w (R.HE.e (R.Th t x)) = R.e0 (d.lift t x) := by
  have e : PiTensorProduct.lift (Mult.postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x))) = R.e0 ∘ₗ R.thDn t x := by
    ext v
    simp [Mult.postOn]
  rw [h.Th, rowForm, e, LinearMap.comp_apply, d.thDn_w h]

end ChainVec

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Choice (R : RealDat D A Ks) where

  sc : Consts

  G : GridData R.toLevCh sc

  W : G.Weil

  M : Vol G

  ρ : G.RealVec

  ξ : Module.Dual ℂ (coefPlus G W.θ).W

  cv : ChainVec R

  rm : RealMatch W

  S : SumChoice W Set.univ

  rp : ClassReps G

  n : ℕ

  e : Fin n ≃ TestIx G × VVIdx (LaP G)

  c : Fin D.R.m → Fin D.R.m → T → ℂ

def Guard (R : RealDat D A Ks) : Prop :=
  ∀ t, ∀ PP ∈ R.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

theorem guard_of_qGuard {R : RealDat D A Ks} (h : Formalism.IndefR.FWT.QGuard R) : Guard R := fun t PP hP h' =>
  h.2 t PP hP (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h')

theorem guard_of_top (R : RealDat D A Ks) (h : D.host.ccK = ⊤) : Guard R := fun _ PP _ h' => by
  rw [h, Ideal.absNorm_top, Nat.cast_one] at h'
  exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h')

variable {R : RealDat D A Ks}

namespace Choice

variable (ch : Choice R)

abbrev w : SmT (R.MY 0) := ch.cv.w

def Psi (a : Fin ch.n) : GLf ch.G → WtSp ch.G := psi ch.rp ch.e a

def Phi (a : Fin ch.n) : ch.G.Datum := datumOf ch.e a

def col (a : Fin ch.n) : Bridge.Gf (ch.G.V (.top 0)) → (coefPlus ch.G ch.W.θ).W := colOf ch.W.θ (ch.Psi a)

def form : R.HE.H →ₗ[ℂ] (GA D (Yc D 0) → ℂ) :=
  LinearMap.applyₗ ch.w ∘ₗ PiTensorProduct.lift.toLinearMap ∘ₗ R.HE.e

theorem form_apply (u : R.HE.H) : ch.form u = rowForm R ch.w (R.HE.e u) := rfl

abbrev withReal (ρ : ch.G.RealVec) (ξ : Module.Dual ℂ (coefPlus ch.G ch.W.θ).W) : Choice R := { ch with ρ := ρ, ξ := ξ }

end Choice

variable (ch : Choice R)

def psiK (a : Fin ch.n) (u : R.HE.H) : ℂ := fPsiPhi ch.W ch.M ch.ρ ch.ξ (ch.col a) (ch.Phi a) (ch.form u)

def ConvK (a : Fin ch.n) (u : R.HE.H) : Prop := FConv ch.W ch.M ch.ρ ch.ξ (ch.col a) (ch.Phi a) (ch.form u)

def cTot (t : T) : ℂ := ∏ i, ∏ j, ch.c i j t

def vK (t : T) (x : A.fam.amb.FR t) (a : Fin ch.n) : ℂ := vSum ch.W ch.S ch.rp ch.e t x a

def sqRatio (i j : Fin D.R.m) (t : T) : ℂ := ch.c i j t / ch.c i j A.μ0

def ratio (t : T) : ℂ := cTot ch t / cTot ch A.μ0

def psiN (κ : ℂˣ) (a : Fin ch.n) (u : R.HE.H) : ℂ := cTot ch A.μ0 * ((κ⁻¹ : ℂˣ) : ℂ) * psiK ch a u

namespace Choice

def RealOK : Prop :=
  ∀ u, (∀ a, psiK ch a u = 0) → ∀ ρ' ξ' a, psiK (ch.withReal ρ' ξ') a u = 0

structure IsBase : Prop where

  guard : Guard R

  weil : ch.W.Over R

  vol : ch.M.IsRow

  vac : ch.rm.Over R

  w_ne : ch.w ≠ 0

  const : ∀ i j t, IsSquareConst ch.W ch.S.B ch.rm t i j (ch.c i j t)

structure Is : Prop extends ch.IsBase where

  real : ch.RealOK

def AtScale (C b : ℝ) : Prop := ch.sc = ⟨1, C, b⟩

variable {ch}

theorem IsBase.withReal (h : ch.IsBase) (ρ ξ) : (ch.withReal ρ ξ).IsBase := ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩

theorem IsBase.c_eq (h : ch.IsBase) {i j t} (h0 : SquareNonzero ch.W ch.S.B ch.rm t i j) {c : ℂ}
    (hc : IsSquareConst ch.W ch.S.B ch.rm t i j c) : ch.c i j t = c := (h.const i j t).unique h0 hc

end Choice

theorem psiK_eq (a : Fin ch.n) (u : R.HE.H) : psiK ch a u =
    Bplus ch.W ch.M (scal ch.W.θ (ch.ξ ∘ₗ (GlobalTheory.CoefModel.toHilb (LaP ch.G) (posDef_dual ch.G)).toLinearMap) (ch.Psi a))
      (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.form u)) := by
  rw [← pairVec_colOf]; rfl

theorem col_mem (a : Fin ch.n) : ch.col a ∈ Cols ch.G ch.W.θ :=
  colOf_mem ch.W.θ_is (psi_left _ _ a) fun g _ hk => psi_right _ _ a g hk

theorem psiK_smul (a : Fin ch.n) (z : ℂ) (u : R.HE.H) : psiK ch a (z • u) = z * psiK ch a u := by
  have := fPsiPhi_smul ch.W ch.M ch.ρ ch.ξ 1 z (ch.col a) (ch.Phi a) (ch.form u)
  rwa [one_smul, one_mul, ← map_smul] at this

theorem psiK_zero (a : Fin ch.n) : psiK ch a 0 = 0 := by
  simpa using psiK_smul ch a 0 0

variable {ch} in

theorem psiK_add {a : Fin ch.n} {u u' : R.HE.H} (h : ConvK ch a u) (h' : ConvK ch a u') :
    psiK ch a (u + u') = psiK ch a u + psiK ch a u' := by
  rw [psiK, map_add]; exact fPsiPhi_add ch.W ch.M h h'

def psiL (a : Fin ch.n) (h : ∀ u, ConvK ch a u) : R.HE.H →ₗ[ℂ] ℂ where
  toFun := psiK ch a
  map_add' u u' := psiK_add (h u) (h u')
  map_smul' := psiK_smul ch a

theorem form_Th (h : R.IsChain) (t : T) (x : (R.HX t).H) : ch.form (R.Th t x) = R.e0 (ch.cv.lift t x) :=
  ch.cv.rowForm_Th h t x

theorem realOK_of_inj (h : ∀ u, (∀ a, psiK ch a u = 0) → u = 0) : ch.RealOK := fun u hu ρ' ξ' a => by
  rw [h u hu]; exact psiK_zero _ a

variable {ch} in

theorem Choice.RealOK.inj (h : ch.RealOK) {ρ' ξ'} (h' : ∀ u, (∀ a, psiK (ch.withReal ρ' ξ') a u = 0) → u = 0) (u : R.HE.H)
    (hu : ∀ a, psiK ch a u = 0) : u = 0 := h' u (h u hu ρ' ξ')

variable {ch} in

theorem Choice.IsBase.is_withReal (h : ch.IsBase) {ρ' ξ'} (h' : ∀ u, (∀ a, psiK (ch.withReal ρ' ξ') a u = 0) → u = 0) :
    (ch.withReal ρ' ξ').Is := ⟨h.withReal ρ' ξ', realOK_of_inj _ h'⟩

theorem cTot_ne_zero_iff (t : T) : cTot ch t ≠ 0 ↔ ∀ i j, ch.c i j t ≠ 0 := by
  simp [cTot, Finset.prod_ne_zero_iff]

theorem ratio_eq_prod (t : T) : ratio ch t = ∏ i, ∏ j, sqRatio ch i j t := by
  simp only [ratio, cTot, sqRatio, Finset.prod_div_distrib]

theorem ratio_base (h : cTot ch A.μ0 ≠ 0) : ratio ch A.μ0 = 1 := div_self h

theorem psiN_eq_iff (h : cTot ch A.μ0 ≠ 0) (κ : ℂˣ) (z v : ℂ) (t : T) (a : Fin ch.n) (u : R.HE.H) :
    psiN ch κ a u = (z * ratio ch t)⁻¹ * v ↔ psiK ch a u = (z * cTot ch t)⁻¹ * κ * v := by
  have e : (z * ratio ch t)⁻¹ * v = cTot ch A.μ0 * ((κ⁻¹ : ℂˣ) : ℂ) * ((z * cTot ch t)⁻¹ * κ * v) := by
    have := κ.ne_zero
    rw [ratio, Units.val_inv_eq_inv_val, mul_inv, mul_inv, inv_div, div_eq_mul_inv]
    field_simp
  rw [e, psiN, mul_right_inj' (mul_ne_zero h (Units.ne_zero _))]

theorem vK_smul (t : T) (z : D.what₂.LL) (x : A.fam.amb.FR t) (a : Fin ch.n) :
    vK ch t (z • x) a = D.what₂.embLL z * vK ch t x a := vSum_smul _ _ _ _ t z x a

theorem vK_add (t : T) {a : Fin ch.n} (h : ch.S.SumOK t (ch.Phi a)) (x x' : A.fam.amb.FR t) :
    vK ch t (x + x') a = vK ch t x a + vK ch t x' a := vSum_add _ _ _ _ t h x x'

theorem exists_match_over (hL : R.toLevCh.Is A.μ0) (hch : R.IsChain) {sc : Consts} {G : GridData R.toLevCh sc} {W : G.Weil}
    (hW : W.Over R) : ∃ rm : RealMatch W, rm.Over R := by
  obtain ⟨rm⟩ := nonempty_realMatch W hL
  have key : ∀ (Y Y' : LSp D) (s s') (S S' : HSp D) Λ Λ' s₀ s₀' (f : WO S S' → ℂ), Y = ⟨S, Λ⟩ → Y' = ⟨S', Λ'⟩ → HEq s s₀ → HEq s' s₀' →
      IsVacO R.ψ R.θ S S' s₀ s₀' (Λ : Set _) (Λ' : Set _) f →
      ∃ f', IsVacO W.ψ W.θ Y.sp Y'.sp s s' (Y.lat : Set _) (Y'.lat : Set _) f' ∧ HEq f' f := by
    rintro _ _ s s' S S' Λ Λ' s₀ s₀' f rfl rfl h1 h2 h
    obtain rfl := eq_of_heq h1
    obtain rfl := eq_of_heq h2
    exact ⟨f, hW.ψ ▸ hW.θ ▸ h, HEq.rfl⟩
  have top : ∀ k, k = D.R.m → columnBlock R.toLevCh k = ⟨D.sp.X', R.ΛX⟩ ∧ HEq (W.cart (.grid 0 k)) (cart R.MX) := by
    rintro _ rfl; exact ⟨colY_m _, hW.cartX⟩
  have H : ∀ i j, ∃ f : WO (G.V (.grid i j)) (G.V (.grid i (j + 1))) → ℂ,
      (∀ t, i ≤ D.R.m → j < D.R.m → W.IsVac (.mu t i j) f) ∧
      (i = 0 → j + 1 < D.R.m → HEq f (R.vac j)) ∧ (i = 0 → j + 1 = D.R.m → HEq f R.vacX) := fun i j => by
    rcases i with _ | i
    · rcases lt_trichotomy (j + 1) D.R.m with h | h | h
      · obtain ⟨f, h1, h2⟩ := key _ _ _ _ _ _ _ _ _ _ _ (colY_lt R.toLevCh (show j < D.R.m by omega)) (colY_lt R.toLevCh h)
          (hW.cartY j (by omega)) (hW.cartY _ h) (hch.vY A.μ0 j h).1
        exact ⟨f, fun _ _ _ => h1, fun _ _ => h2, fun _ _ => by omega⟩
      · obtain rfl : j = D.R.m - 1 := by omega
        obtain ⟨f, h1, h2⟩ := key _ _ _ _ _ _ _ _ _ _ _ (colY_lt R.toLevCh (show D.R.m - 1 < D.R.m by omega)) (top _ h).1
          (hW.cartY _ (by omega)) (top _ h).2 (hch.vX A.μ0).1
        exact ⟨f, fun _ _ _ => h1, fun _ _ => by omega, fun _ _ => h2⟩
      · exact ⟨0, fun _ _ _ => by omega, fun _ _ => by omega, fun _ _ => by omega⟩
    · exact ⟨rm.vT _ j, fun t => rm.vT_is t _ j, fun h => by omega, fun h => by omega⟩
  choose vT h1 h2 h3 using H
  exact ⟨{ rm with vT := vT, vT_is := fun t i j => h1 i j t }, fun k => h2 0 k rfl, fun k => h3 0 k rfl⟩

theorem exists_choice (hL : R.toLevCh.Is A.μ0) (hch : R.IsChain) {sc : Consts} {G : GridData R.toLevCh sc} {W : G.Weil}
    (hW : W.Over R) (S : SumChoice W Set.univ) (cv : ChainVec R) :
    ∃ M rm rp n e, 0 < n ∧ M.IsRow ∧ rm.Over R ∧ ∀ ρ ξ c, Guard R → cv.w ≠ 0 →
      (∀ i j t, IsSquareConst W S.B rm t i j (c i j t)) → (⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩ : Choice R).IsBase := by
  obtain ⟨M, hM⟩ := exists_vol G hL A.μ0
  obtain ⟨rm, hrm⟩ := exists_match_over hL hch hW
  obtain ⟨n, e, -, -, hn, -⟩ := TestLatModel.exists_testLat (G := G) (node_isV G hL (X := .grid 0 0) ⟨Nat.zero_le _, Nat.zero_le _⟩).sd.1.fg default
  exact ⟨M, rm, default, n, e, hn, hM.isRow, hrm, fun _ _ _ h1 h2 h3 => ⟨h1, hW, hM.isRow, hrm, h2, h3⟩⟩

example (ρ ξ) (t : T) : vK (ch.withReal ρ ξ) t = vK ch t ∧ cTot (ch.withReal ρ ξ) t = cTot ch t := ⟨rfl, rfl⟩

example (ρ) (h : (ch.withReal ρ 0).RealOK) (a : Fin ch.n) (u : R.HE.H) : psiK ch a u = 0 := by
  refine h u (fun b => ?_) ch.ρ ch.ξ a
  have e : pairVec (coefPlus ch.G ch.W.θ) 0 (ch.col b) = (0 : ℂ) • pairVec (coefPlus ch.G ch.W.θ) 0 (ch.col b) := by
    funext x; simp [pairVec_apply]
  show Bplus _ _ (pairVec (coefPlus ch.G ch.W.θ) 0 (ch.col b)) _ = 0
  rw [e, ← one_smul ℂ (thetaChi _ _ _ _ _), Bplus_smul, zero_mul, zero_mul]

example (d : ChainVec R) (v : SmT (R.MY 2)) : d.dnVec 2 v = R.ItY 0 (d.polY 0) (R.ItY 1 (d.polY 1) v) := rfl

end GlobalTheory.RowTest

end
