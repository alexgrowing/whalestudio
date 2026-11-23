import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Core.Rk.Top GlobalTheory.Core.Rk.Top.Model
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.Check

variable {D : D7}

section Read

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (K : ClassesAtPrimes M bad)

theorem levG_exists (x : GA D D.sp.X') : ∃ J χ, LevG K x J χ ∧ ∀ κ : K.lev.U, ∃ h, HasMat h κ.1 ∧ x⁻¹ * h * x ∈ J := by
  let χ : GA D D.sp.X' → ℂ := fun h => if hh : ∃ κ : K.lev.U, HasMat h κ.1 then star ((K.lev.chi hh.choose : ℂˣ) : ℂ) else 0
  have hχ : ∀ h (κ : K.lev.U), HasMat h κ.1 → χ h = star ((K.lev.chi κ : ℂˣ) : ℂ) := by
    intro h κ hk
    have hh : ∃ κ : K.lev.U, HasMat h κ.1 := ⟨κ, hk⟩
    simp only [χ, dif_pos hh]
    rw [show hh.choose = κ from Subtype.ext (hasMat_mat hh.choose_spec hk)]
  have e : ∀ h : GA D D.sp.X', x * (x⁻¹ * h * x) * x⁻¹ = h := fun h => by group
  refine ⟨{k | ∃ κ : K.lev.U, HasMat (x * k * x⁻¹) κ.1}, fun k => χ (x * k * x⁻¹), ⟨fun h => ?_, fun h κ hk => ?_⟩, fun κ => ?_⟩
  · simp only [Set.mem_setOf_eq, e]
  · simp only [e]; exact hχ h κ hk
  · obtain ⟨h, hh⟩ := hasMat_exists ⟨κ.1, ((K.lev.U_eq _).1 κ.2).1⟩
    exact ⟨h, hh, κ, by rw [e]; exact hh⟩

theorem levG_type {x : GA D D.sp.X'} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ} (hL : LevG K x J χ) (f : GA D D.sp.X' → ℂ)
    (hf : ∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) (g h : GA D D.sp.X') (κ : K.lev.U) (hk : HasMat h κ.1) :
    f (g * h * x) = star ((K.lev.chi κ : ℂˣ) : ℂ) * f (g * x) := by
  rw [← hL.2 h κ hk, ← hf _ ((hL.1 h).2 ⟨κ, hk⟩)]
  congr 1; group

variable {S : D.what₂.Tau → SPar} {MX : DSModel D.sp.X' S} (eW : Pm.Wrow ≃ₗ[ℂ] (M.clsP → FrP D → ℂ))
  (j : SmT MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X')

theorem y_inj : Function.Injective fun c => (K.y c).1 := fun a b h =>
  K.y_bij.1 (by have : K.y a = K.y b := Subtype.ext h
                simp only [this])

theorem readsG_exists (G : Pm.Mt) : ∃ f, ReadsG K eW j x G f := by
  let φ : M.clsP → SmT MX →ₗ[ℂ] ℂ := fun c => (Nat.card (M.stabilizer₂ c) : ℂ) •
    ((Pm.period.flip G) ∘ₗ (eW.symm : _ →ₗ[ℂ] Pm.Wrow) ∘ₗ (LinearMap.single ℂ (fun _ => FrP D → ℂ) c) ∘ₗ j)
  refine ⟨LinearMap.pi fun g => if hh : ∃ c, HasMat (g * x⁻¹) (K.y c).1 then φ hh.choose else 0, fun c v h hc => ?_⟩
  have hh : ∃ c, HasMat (h * x * x⁻¹) (K.y c).1 := ⟨c, by rwa [mul_inv_cancel_right]⟩
  have e : hh.choose = c := y_inj K (hasMat_mat hh.choose_spec (by rwa [mul_inv_cancel_right]))
  simp only [LinearMap.pi_apply, dif_pos hh, e, φ]
  simp

theorem ReadsG.period_eq {G G' : Pm.Mt} {f : SmT MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)} (h : ReadsG K eW j x G f) (h' : ReadsG K eW j x G' f)
    (w : Pm.Wrow) (hw : ∀ c, eW w c ∈ LinearMap.range j) : Pm.period w G = Pm.period w G' := by
  choose v hv using hw
  have e : w = ∑ c, eW.symm (Pi.single c (j (v c))) := by
    rw [← map_sum, LinearEquiv.eq_symm_apply]
    simp only [hv]
    exact (Finset.univ_sum_single _).symm
  rw [e, map_sum, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := hasMat_exists (K.y c)
  have hc : (Nat.card (M.stabilizer₂ c) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := M.stabilizer₂ c)).ne'
  exact mul_left_cancel₀ hc ((h c _ g hg).symm.trans (h' c _ g hg))

theorem not_readsG_zero {G : Pm.Mt} (w : Pm.Wrow) (hw : ∀ c, eW w c ∈ LinearMap.range j) (hG : Pm.period w G ≠ 0) :
    ¬ ReadsG K eW j x G 0 := fun h =>
  hG (by simpa using ReadsG.period_eq K eW j x h (readsG_zero K eW j x) w hw)

theorem ReadsG.scalar {G : Pm.Mt} {f : SmT MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)} {a : ℂ} (h : ReadsG K eW j x G f)
    (h' : ReadsG K eW (a • j) x G f) (w : Pm.Wrow) (hw : ∀ c, eW w c ∈ LinearMap.range j) (hG : Pm.period w G ≠ 0) : a = 1 := by
  have h2 : ReadsG K eW j x (a • G) f := fun c v g hg => by
    rw [h' c v g hg]
    simp [Pi.single_smul']
  have := ReadsG.period_eq K eW j x h h2 w hw
  rw [map_smul, smul_eq_mul] at this
  exact (mul_right_cancel₀ hG (this.symm.trans (one_mul _).symm))

end Read

section Package

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {P : LevelP R.Pg D.R.r ℂ} {u : D.what₂.Word} {g : Geo D}

theorem chars_agree {t : T} {r : RowCh R P u g t} (h : r.Is) :
    (∀ j ρ hj, ((r.sBF j ρ hj).χV, (r.sBF j ρ hj).χW) = Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1)) ∧
    ∀ j σ hj, ((r.sFB j σ hj).χV, (r.sFB j σ hj).χW) = Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1 + 1) := by
  obtain ⟨a, ha⟩ := D.R.m_even
  refine ⟨fun j ρ hj => ?_, fun j σ hj => ?_⟩
  · have : Odd (j + 1) := ⟨a - ρ - 1, by omega⟩
    rw [(h.sBF j ρ hj).2.2.1, (h.sBF j ρ hj).2.2.2, Lift.chrStep, if_pos this]
  · have : ¬ Odd (j + 1 + 1) := Nat.not_odd_iff_even.2 ⟨a - σ - 1, by omega⟩
    rw [(h.sFB j σ hj).2.2.1, (h.sFB j σ hj).2.2.2, Lift.chrStep, if_neg this]

theorem isStepVector_trivial_of_chain (hv : R.chain_vY) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) :
    IsStepVecOf R.ψ R.θ (Yc D j) (Yc D (j + 1)) (cart (R.MY j)) (cart (R.MY (j + 1))) (R.ΛY j)
      (R.ΛY (j + 1)) (R.βY j) (R.βY (j + 1)) (R.datYt t j R.triv) (R.chi (j + 1)) (R.Q t) (R.xiR t) (R.vac j) (R.vY t j) := hv t j hj

example (t : T) (j : ℕ) : CP R R.triv t j = R.CC t j := rfl

example (t : T) : datXP R R.triv t = R.datXt t := rfl

theorem GeoMeas.common (h : GeoMeas R g) (t t' : T) :
    ENNReal.ofReal (g.κ D.R.m * volLev R g t (D.R.m - 1)) • R.νX t = ENNReal.ofReal (g.κ D.R.m * volLev R g t' (D.R.m - 1)) • R.νX t' :=
  (h.volT t).symm.trans (h.volT t')

theorem not_geoMeas (t : T) (h0 : R.νX t = 0) : ¬ GeoMeas R g := fun h => by
  have := g.volT.haar
  exact NeZero.ne g.volT.μ (by rw [h.volT t, h0, smul_zero])

theorem colCh_nonempty (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) : ∃ k : ColCh u C, ∀ j, Nonempty (k.Ch j) :=
  ⟨{ kom := fun _ => 1, Ch := fun _ => Unit, dd := fun _ _ _ => 0, e := fun _ _ => Finsupp.single 1 1, eT := fun _ _ _ => Finsupp.single 1 1,
     Ram := fun _ => Set.univ, S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 1, cK := fun _ => 1, cP := 1 },
    fun _ => ⟨()⟩⟩

theorem geo_nonempty (bes : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ)
    (jac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → JacAt (Yc D (j + 1)) (D.sp.X (j + 1)) ρ)
    (lnk : ∀ j σ h v, Link ((bes j (σ + 1) h).lev v) (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ)
    (Lz : HSp D) (o : OrthDec (D.sp.X D.R.m) D.sp.X' Lz) : Nonempty (Geo D) := by
  obtain ⟨h1, -, h3, -⟩ := VolExist.measures_exist D
  exact ⟨{ vol := fun _ => (h1 _).some, volT := (h1 _).some, x := fun j => ⟨fun _ => 1, fun _ => 1, ⊥, (h1 _).some⟩, vac := fun _ _ => 0,
           bes := bes, jac := jac, lnk := fun j σ h => lnk j σ h _, vL := fun _ _ _ => (h3 _ _).some, Lz := Lz,
           oT := fun n h => h ▸ o, μf := fun _ => 0, μT := 0, ρJ := fun _ _ _ => 0, ρB := fun _ _ _ => 0, κ := fun _ => 1,
           b := fun _ => 1, bT := 1, LT := ⊥ }⟩

end Package

section Real

open GlobalTheory.MiS

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

theorem reads_exists (u : D.what₂.Word) (j : SmT (pk W).MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') (μ : D.what₂.Tup) (G : D.what₂.Amb μ) :
    ∃ f, Reads W u j x μ G f := by
  by_cases h : μ = D.what₂.mu0
  · subst h
    obtain ⟨f, hf⟩ := readsG_exists (W.R.T.cols.forms u).clsP.toG (W.R.T.cols.forms u).valP.eW j x ((D.eMt u).symm G)
    exact ⟨f, fun _ => hf, fun h => absurd rfl h⟩
  · obtain ⟨f, hf⟩ := readsG_exists (W.R.T.tw.pt.cls u μ h) (W.R.T.tw.pt.val u μ h).eW j x ((D.eMtTw u μ).symm G)
    exact ⟨f, fun h' => absurd h' h, fun _ => hf⟩

theorem tailOf_eq (u : D.what₂.Word) (j : SmT (pk W).MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') (μ : D.what₂.Tup) (h : μ ≠ D.what₂.mu0)
    (ψ : (D.chTw u μ).cls D.R.m → (D.chTw u μ).Y D.R.m → ℂ) (G : D.what₂.Amb μ) (f : SmT (pk W).MX →ₗ[ℂ] (GA D D.sp.X' → ℂ))
    (hG : Reads W u j x μ G f)
    (hψ : ∀ c, (W.R.T.tw.pt.val u μ h).eW ((D.PTw u μ).lowerMap ((D.PTw u μ).evz ψ)) c ∈ LinearMap.range j) :
    tailOf W u j x μ ψ f = (D.PTw u μ).Ptil ψ ((D.eMtTw u μ).symm G) := by
  have hx : ∃ G, Reads W u j x μ G f := ⟨G, hG⟩
  rw [tailOf, dif_pos hx, dif_neg h]
  exact ReadsG.period_eq _ _ j x (hx.choose_spec.2 h) (hG.2 h) _ hψ

theorem not_topReadAt_zero (u : D.what₂.Word) (x : GA D D.sp.X') : ¬ TopReadAt W u 0 x := fun h => not_isJ_zero _ h.1

theorem not_unitRatio_base (u : D.what₂.Word) (p : ℕ) (hp : p.Prime) : ¬ UnitRatio (badPrime W u W.P.A3.A.μ0) (p : ℂ) 1 := by
  rintro ⟨-, k, hk, r, -, e, hS⟩
  have hr : r = ((p ^ k : ℕ) : ℚ) := by
    have : (r : ℂ) = (((p ^ k : ℕ) : ℚ) : ℂ) := by rw [← e]; simp
    exact_mod_cast this
  refine not_badPrime_base W u p (hS p hp ?_)
  have := Fact.mk hp
  rw [hr, padicValRat.of_nat, padicValNat.prime_pow]
  exact_mod_cast hk.ne'

end Real

end GlobalTheory.Fam.Check

end
