import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastTwoStepsGuarded

noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator (FnModAt FnMod facTop facPen Zmu)
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis)

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))

def Bd {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    (c : K) (M : Submodule (𝓞 K) V) (M' : Submodule (𝓞 K) V') (k : V →ₗ[K] V') : Prop :=
  ∀ v ∈ localization₂ w.asIdeal M, c • k v ∈ localization₂ w.asIdeal M'

def WtUnit (S : GSD K) : Prop := ∀ d : S.D, w.valuation K ((Nat.card (MulAction.stabilizer S.G d) : ℕ) : K)⁻¹ ≤ 1

variable {w}

theorem Bd.transfer {S S' : GSD K} (g : S.G) (g' : S'.G) {M M₂ : Submodule (𝓞 K) S.V} {M' M₂' : Submodule (𝓞 K) S'.V}
    (hM : M₂ = M.map ((S.ρ g).restrictScalars (𝓞 K))) (hM' : M₂' = M'.map ((S'.ρ g').restrictScalars (𝓞 K)))
    {k k₂ : S.V →ₗ[K] S'.V} (hk : k₂ = (S'.ρ g') ∘ₗ k ∘ₗ (S.ρ g⁻¹)) {c : K} (h : Bd w c M₂ M₂' k₂) : Bd w c M M' k := by
  subst hM hM' hk
  rintro v ⟨s, hs, hv⟩
  obtain ⟨t, ht, y, hy, e⟩ := h (S.ρ g v) ⟨s, hs, s • v, hv, by simp⟩
  refine ⟨t, ht, ?_⟩
  have e1 : S.ρ g⁻¹ (S.ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e2 : y = t • c • k v := by
    have h2 := congrArg (S'.ρ g'⁻¹) e
    simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, e1, LinearMap.map_smul_of_tower, map_smul] at h2
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at h2
    exact h2
  exact e2 ▸ hy

theorem opOf_bound {S S' : GSD K} (A : ClsKer S S') (h : S.Ok) (s : S.Sec) (hw : WtUnit w S) {c : K}
    (hk : ∀ d d', Bd w c (S.Del d) (S'.Del d') (A.k d d')) {c₀ : K} (φ : S.EqFun)
    (hφ : ∀ d, c₀ • φ.1 d ∈ localization₂ w.asIdeal (S.Del d)) (d' : S'.D) :
    (c * c₀) • (A.opOf h s φ).1 d' ∈ localization₂ w.asIdeal (S'.Del d') := by
  change (c * c₀) • A.appOf h s φ d' ∈ _
  unfold ClsKer.appOf
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [smul_comm, wt_eq_card]
  refine smul_mem_localizationAt_of_le w _ (hw _) ?_
  rw [mul_smul, ← map_smul]
  exact hk _ _ _ (hφ _)

theorem comp_bound {S₀ S S₁ : GSD K} {Y : Cpl S} (A : CplKer S₀ S S₁ Y) (h : S.Ok) (s : S.Sec) (hw : WtUnit w S) {c₁ c₂ : K}
    (h1 : ∀ d₀ d, ∀ y ∈ Y.ys d, Bd w c₁ (S₀.Del d₀) (S.Del d) (A.k1 d₀ d y))
    (h2 : ∀ d d₁, ∀ y ∈ Y.ys d, Bd w c₂ (S.Del d) (S₁.Del d₁) (A.k2 d y d₁)) (d₀ : S₀.D) (d₁ : S₁.D) :
    Bd w (c₂ * c₁) (S₀.Del d₀) (S₁.Del d₁) ((A.comp h s).k d₀ d₁) := by
  intro v hv
  simp only [CplKer.comp, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [smul_comm, wt_eq_card]
  refine smul_mem_localizationAt_of_le w _ (hw _) ?_
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun y hy => ?_
  have hy' : y ∈ Y.ys (s.rep x) := by simpa using hy
  rw [mul_smul, ← map_smul]
  exact h2 _ _ y hy' _ (h1 _ _ y hy' v hv)

theorem colTo_bound {F : ℕ → GFam K} (kk : KerFam F) (hF : ∀ j, (F j).Ok) (c : ℕ → K)
    (φ : (F 0).Forms) (hφ : ∀ b d, (φ b).1 d ∈ localization₂ w.asIdeal (((F 0).mem b).Del d)) (n : ℕ)
    (hw : ∀ j < n, ∀ b, WtUnit w ((F j).mem b))
    (hk : ∀ j < n, ∀ al be d d', Bd w (c j) (((F j).mem al).Del d) (((F (j + 1)).mem be).Del d') ((kk j al be).k d d'))
    (b : (F n).β) (d : ((F n).mem b).D) :
    (∏ j ∈ Finset.range n, c j) • (kk.colTo hF n φ b).1 d ∈ localization₂ w.asIdeal (((F n).mem b).Del d) := by
  induction n with
  | zero => rw [Finset.prod_range_zero, one_smul]; exact hφ b d
  | succ n ih =>
    have e : (kk.colTo hF (n + 1) φ b).1 d =
        ∑ al, ((kk n al b).opOf (hF n al) ((F n).mem al).outSec (kk.colTo hF n φ al)).1 d := by
      change (KerFam.step kk hF n (kk.colTo hF n φ) b).1 d = _
      simp only [KerFam.step, GFam.Mat.opOf, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, Submodule.coe_sum, Finset.sum_apply]
    rw [e, Finset.smul_sum, Finset.prod_range_succ, mul_comm]
    exact Submodule.sum_mem _ fun al _ => opOf_bound _ _ _ (hw n (Nat.lt_succ_self n) al) (hk n (Nat.lt_succ_self n) al b) _
      (ih (fun j hj => hw j (Nat.lt_succ_of_lt hj)) (fun j hj => hk j (Nat.lt_succ_of_lt hj)) al) d

theorem colCpl_bound {F : ℕ → GFam K} (kk : KerFam F) (hF : ∀ j, (F j).Ok) {n : ℕ} (hw : ∀ j ≤ n, ∀ b, WtUnit w ((F j).mem b))
    (c : ℕ → K) {S S₁ : GSD K} {Y : Cpl S} (A : ∀ b : (F n).β, CplKer ((F n).mem b) S S₁ Y) (h : S.Ok) (hS : WtUnit w S)
    (hk : ∀ j < n, ∀ al be d d', Bd w (c j) (((F j).mem al).Del d) (((F (j + 1)).mem be).Del d') ((kk j al be).k d d'))
    (h1 : ∀ b d₀ d, ∀ y ∈ Y.ys d, Bd w (c n) (((F n).mem b).Del d₀) (S.Del d) ((A b).k1 d₀ d y))
    (h2 : ∀ b d d₁, ∀ y ∈ Y.ys d, Bd w (c (n + 1)) (S.Del d) (S₁.Del d₁) ((A b).k2 d y d₁))
    (φ : (F 0).Forms) (hφ : ∀ b d, (φ b).1 d ∈ localization₂ w.asIdeal (((F 0).mem b).Del d)) (d : S₁.D) :
    (∏ j ∈ Finset.range (n + 2), c j) • (colCpl kk hF n A h φ).1 d ∈ localization₂ w.asIdeal (S₁.Del d) := by
  have e : (colCpl kk hF n A h φ).1 d =
      ∑ b, (((A b).comp h S.outSec).opOf (hF n b) ((F n).mem b).outSec (kk.colTo hF n φ b)).1 d := by
    simp only [colCpl, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.coe_sum, Finset.sum_apply]
  have e2 : ∏ j ∈ Finset.range (n + 2), c j = (c (n + 1) * c n) * ∏ j ∈ Finset.range n, c j := by
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    ring
  rw [e, Finset.smul_sum, e2]
  exact Submodule.sum_mem _ fun b _ => opOf_bound _ _ _ (hw n le_rfl b) (comp_bound (A b) h _ hS (h1 b) (h2 b)) _
    (colTo_bound kk hF c φ hφ n (fun j hj => hw j hj.le) hk b) d

end Generic

theorem not_dvd_card_stab_frm {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (d : DecoF X.E n ST SG Q)
    [Finite (MulAction.stabilizer (FrmG Λ Θ) d)] {p : ℕ} (hp : p.Prime) (hb : Module.finrank ℚ X.E * n + 1 < p) :
    ¬ p ∣ Nat.card (MulAction.stabilizer (FrmG Λ Θ) d) := by
  refine not_dvd_card_of_injective (((UF X.E n).subtype.comp (MonoidHom.fst _ _)).comp (Subgroup.subtype _)) ?_ hp hb
  rw [injective_iff_map_eq_one]
  rintro ⟨⟨γ, h, c⟩, hs⟩ h1
  have h2 : γ = 1 := Subtype.ext h1
  subst h2
  have h3 : h.1 = 1 := glg_eq_one_of_fix d.1.1 h.1 (congrArg (fun x : DecoF X.E n ST SG Q => x.1.1.1) hs)
  have h4 : c.1 = 1 := by
    funext P
    have h5 : (1 : Sp X.E n ≃ₗ[X.E] Sp X.E n) * d.1.2 P * ((c.1 P)⁻¹).1 = d.1.2 P :=
      congrArg (fun x : DecoF X.E n ST SG Q => x.1.2 P) hs
    rw [one_mul, mul_eq_left] at h5
    exact inv_eq_one.1 (Subtype.ext h5)
  exact Subtype.ext (Prod.ext rfl (Prod.ext (Subtype.ext h3) (Subtype.ext h4)))

theorem stdOver_tilH {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} (hN : N = n + 1)
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ v : SG, pi ∉ v.1.asIdeal)
    (d : DecoSet E n ∅ SG) {p : ℕ} (h : StdOver p d.1.N) : StdOver p (DecoSet.tilH (ST := ST) hN pi d).1.N := by
  subst hN
  change StdOver p (DecoSet.til (ST := ST) pi d).1.N
  rw [DecoSet.til_val d hT hG]
  intro P hP
  ext x
  change x ∈ localization₂ P.asIdeal (tilN d.1.N) ↔ _
  rw [mem_localization_tilN, h P hP, GlobalTheory.TopStep.mem_stdAt, GlobalTheory.TopStep.mem_stdAt, Fin.forall_fin_succ']
  rfl

section Column

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Amb X)

theorem exists_std_pt (hM : StdMove) (hPr : Pr.Ok) (i : Fin 2) (u : Pr.Word) (j : ℕ) (b : L.β j)
    (p : ((chF W sel mu L u j).mem b).D) : ∃ g : ((chF W sel mu L u j).mem b).G, StdOver (Pr.g i) (DecoF.deco (g • p)).1.N := by
  obtain ⟨γ, hγ⟩ := hM X Pr hPr i _ (DecoF.deco p).1.N ⟨(DecoF.deco p).2.lat, (DecoF.deco p).2.uni⟩
  exact ⟨(γ, 1, 1), hγ⟩

theorem evGSD_del_smul (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hS : Pr.T u ∈ S) (P : LevFam X.E X.K R.r Pr.vGs)
    (γ : UF X.E (R.N R.m - 1)) (d : (evGSD W Ch sel mu P u).D) :
    (evGSD W Ch sel mu P u).Del (((γ, 1) : (evGSD W Ch sel mu P u).G) • d) =
      ((evGSD W Ch sel mu P u).Del d).map (((evGSD W Ch sel mu P u).ρ (γ, 1)).restrictScalars (𝓞 X.K)) := by
  have h1 := DecoSet.tilH_smul (ST := Pr.vT u) (N_m_succ R) (γ, (1 : GLG X.E _ (rowSG Pr sel mu))) d (conj_piT_notMem hPr u)
    (piT_notMem_rowSG sel mu hPr hsel u hS)
  have h2 : (evGSD W Ch sel mu P u).ρ (γ, 1) = (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho (extUH (N_m_succ R) γ) := by
    change ((((rowTy Ch sel mu P).inv.chr 1)⁻¹ : X.Kˣ) : X.K) •
      (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho (extUH (N_m_succ R) γ) = _
    rw [map_one, inv_one, Units.val_one, one_smul]
  rw [h2]
  refine Eq.trans ?_ (colVal_del_smul W u R.m (extUH (N_m_succ R) γ, extGH (N_m_succ R) 1) (tilQ sel mu u d))
  exact congrArg (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).Del h1

theorem wtUnit_chF (hX : X.Ok) (u : Pr.Word) (hF : ∀ j, (chF W sel mu L u j).Ok) {p : ℕ} (hp : p.Prime)
    (hb : 2 * X.f * R.N R.m + 1 < p) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) {j : ℕ} (hj : j ≤ R.m)
    (b : L.β j) : WtUnit w ((chF W sel mu L u j).mem b) := by
  intro d
  have hE : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
    rfl
  have := (hF j b).fin_stab d
  have hN : R.N j ≤ R.N R.m := Examples₂.N_mono hj
  exact (valuation_inv_natCast w hp hw (not_dvd_card_stab_frm (L.levG j b) (L.levQ j b) d hp
    (lt_of_le_of_lt (by rw [hE]; gcongr) hb))).le

end Column

end GlobalTheory.ColPeriod
