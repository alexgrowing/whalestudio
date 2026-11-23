import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RepVVAeval
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcGamLiftCore

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.FrobeniusPowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

namespace Formalism.MainNotions.N.Ln17.PCutBoundRho

open Formalism.MainNotions.N.Ln17.PCutBoundRep

theorem H1map_latSmul (T : LocLat G Qp LL O) (o : O) (x : LatticeCohomology T.L) :
    (latSmul T o).H1map x = o • x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    rw [← Submodule.Quotient.mk_smul]
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk (o • z)
    congr 1
    apply Subtype.ext
    funext g
    show (latSmul T o).f ((z : G → T.V) g) = o • (z : G → T.V) g
    simp [latSmul, algebraMap_smul]

section Rho

variable {W : LocWach PD LL O v n} {A : ArcP n} {c : ZMod n} {T : LocLat G Qp LL O}
  (hRelay : RelayCore W) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p) (hA : A.OK) (hc : c ∈ A.cuts)
  (hW : Win W A T)
include hRelay hcase hl hA hc hW

theorem rho_ex {w : W.DD T} (hw : InI W T c w) : ∃ x, IsRho W A T c w x :=
  (((hRelay hcase hl A hA c hc).1 T hW).2.1 w hw).2.2.2.1

theorem rho_uniq {w : W.DD T} (hw : InI W T c w) {x x' : LatticeCohomology T.L} (h : IsRho W A T c w x)
    (h' : IsRho W A T c w x') : x = x' :=
  (((hRelay hcase hl A hA c hc).1 T hW).2.1 w hw).2.2.2.2.1 x x' h h'

theorem isRho_zero_of_pi0 {w : W.DD T} (hw : InI W T c w) (hπ : InFNc W T c W.π₀ w) : IsRho W A T c w 0 :=
  (((hRelay hcase hl A hA c hc).1 T hW).2.1 w hw).2.2.2.2.2.1 hπ

theorem rho_add {w w' : W.DD T} {x x' : LatticeCohomology T.L} (hw : InI W T c w) (hw' : InI W T c w')
    (h : IsRho W A T c w x) (h' : IsRho W A T c w' x') : IsRho W A T c (w + w') (x + x') :=
  ((hRelay hcase hl A hA c hc).1 T hW).2.2 w w' x x' hw hw' h h'

theorem rho_smul {w : W.DD T} {x : LatticeCohomology T.L} (hw : InI W T c w) (h : IsRho W A T c w x) (o : O) :
    IsRho W A T c (o • w) (o • x) := by
  have h2 := (hRelay hcase hl A hA c hc).2 T T (latSmul T o) hW hW w x hw h
  rwa [W.map_latSmul, H1map_latSmul] at h2

theorem rho_sum {ι : Type} (s : Finset ι) (w : ι → W.DD T) (x : ι → LatticeCohomology T.L)
    (hw : ∀ i ∈ s, InI W T c (w i)) (h : ∀ i ∈ s, IsRho W A T c (w i) (x i)) :
    IsRho W A T c (∑ i ∈ s, w i) (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isRho_zero_of_pi0 hRelay hcase hl hA hc hW (TypesA.InI_zero W) ⟨0, zero_mem _, smul_zero _, (smul_zero _).symm⟩
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact rho_add hRelay hcase hl hA hc hW (hw j (Finset.mem_insert_self j s))
      (InI_sum W s w fun i hi => hw i (Finset.mem_insert_of_mem hi)) (h j (Finset.mem_insert_self j s))
      (ih (fun i hi => hw i (Finset.mem_insert_of_mem hi)) fun i hi => h i (Finset.mem_insert_of_mem hi))

end Rho

section abelian₂

variable {W : LocWach PD LL O v n}

theorem γ_Lam (hR : GS.RD W) (A : ArcP n) (a : ZMod n) (e : ℕ) :
    ∃ R ∈ W.AΔ, ∃ R' ∈ W.AΔ, R * R' = 1 ∧ W.γA W.gam (abelian₂ W A a e) = R * abelian₂ W A a e := by
  choose r hr r' hr' hrr hγ using GS.psγ hR
  refine ⟨∏ s ∈ Finset.range e, r s ^ A.Hs a e s, prod_mem fun s _ => pow_mem (GS.mem_invariants_of_mem_S1 W (hr s)) _,
    ∏ s ∈ Finset.range e, r' s ^ A.Hs a e s, prod_mem fun s _ => pow_mem (GS.mem_invariants_of_mem_S1 W (hr' s)) _, ?_, ?_⟩
  · rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun s _ => by rw [← mul_pow, hrr, one_pow]
  · unfold abelian₂
    exact GS.γ_prod r hγ e _

theorem φpow_π₀_prod (hR : GS.RD W) (t : ℕ) :
    ∃ U ∈ W.AΔ, (W.φA ^ t) W.π₀ = W.π₀ * (∏ k ∈ Finset.range t, ps W k ^ (PD.p - 1)) * U := by
  obtain ⟨-, ⟨w, hw⟩, -⟩ := id hR
  have hwΔ : (w : LetA O n) ∈ W.AΔ := by
    refine GS.quot_mem W (W.AΔ.mul_mem (GS.π₀_mem W) (pow_mem (GS.qA_mem W) (PD.p - 1))) ?_ ?_
    · rw [map_mul, map_pow]
      exact (GS.isUnit_π₀ hR).mul ((GS.isUnit_qA hR).pow _)
    · have : W.π₀ * qA W ^ (PD.p - 1) * (w : LetA O n) = W.φA W.π₀ := by rw [hw]; ring
      rw [this]
      simpa using TypesA.φA_pow_mem W (TypesA.pi0_mem_ADelta W) 1
  induction t with
  | zero => exact ⟨1, W.AΔ.one_mem, by simp⟩
  | succ t ih =>
    obtain ⟨U, hU, hUe⟩ := ih
    refine ⟨(W.φA ^ t) (w : LetA O n) * U, W.AΔ.mul_mem (TypesA.φA_pow_mem W hwΔ t) hU, ?_⟩
    rw [pow_succ, AlgHom.mul_apply, hw, map_mul, map_mul, map_pow, hUe, Finset.prod_range_succ]
    simp only [ps]
    ring

theorem φpow_π₀_JJ (hR : GS.RD W) (j M G₀ : ℕ) (h2 : 2 * G₀ ≤ (PD.p - 1) * M) :
    ∃ t ∈ W.AΔ, ((W.φA ^ j) W.π₀) ^ M = Formalism.MainNotions.LiftingTheory.JJ W j (2 * G₀) M * t := by
  obtain ⟨U, hU, hUe⟩ := φpow_π₀_prod hR j
  refine ⟨(∏ k ∈ Finset.range j, ps W k ^ ((PD.p - 1) * M - 2 * G₀)) * U ^ M,
    W.AΔ.mul_mem (prod_mem fun k _ => pow_mem (TypesA.ps_mem W k) _) (pow_mem hU M), ?_⟩
  have e1 : (∏ k ∈ Finset.range j, ps W k ^ (PD.p - 1)) ^ M =
      (∏ k ∈ Finset.range j, ps W k ^ (2 * G₀)) * ∏ k ∈ Finset.range j, ps W k ^ ((PD.p - 1) * M - 2 * G₀) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' h2]
  have hpk : ∀ k, Formalism.MainNotions.LiftingTheory.pk W k = ps W k := fun _ => rfl
  rw [hUe, mul_pow, mul_pow, e1]
  unfold Formalism.MainNotions.LiftingTheory.JJ
  simp only [hpk]
  ring

end abelian₂

section LV

variable (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL)

def LV (g : Fin d → W.EE) (e : ℕ) : Prop :=
  ∃ (w₁ : W.DD T₁) (z : W.DD T₂), InI W T₁ c w₁ ∧ (∃ Λ' ∈ Ps W, InFNc W T₁ c 1 (Λ' • w₁)) ∧
    InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1 (abelian₂ W A c (A.len c) • W.map F w₁) ∧
    InFNc W T₂ c W.π₀ z ∧
    RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol
      (W.map F w₁ - z) (fun k => lE W e * g k)

variable {W A F c b sol}

theorem LV_of_lifts {k₀ : Fin d} {f : W.EE} {e : ℕ} (h : LiftsAt W A F c b sol k₀ f e) :
    LV W A F c b sol (fun k => if k = k₀ then f else 0) e := by
  obtain ⟨w₁, z, hw, hΛ, hP, hz, hR⟩ := h
  exact ⟨w₁, z, hw, hΛ, hP, hz, TypesA.RepVV_congr W hR rfl fun k => by rw [mul_ite, mul_zero]⟩

theorem LV_add {g g' : Fin d → W.EE} {e : ℕ} (h : LV W A F c b sol g e) (h' : LV W A F c b sol g' e) :
    LV W A F c b sol (fun k => g k + g' k) e := by
  obtain ⟨w₁, z, hw, ⟨Λ₁, hΛ₁, hΛw₁⟩, hP, hz, hR⟩ := h
  obtain ⟨w₁', z', hw', ⟨Λ₂, hΛ₂, hΛw₂⟩, hP', hz', hR'⟩ := h'
  refine ⟨w₁ + w₁', z + z', TypesA.InI_add W hw hw', ⟨Λ₁ * Λ₂, mul_mem hΛ₁ hΛ₂, ?_⟩, ?_,
    TypesA.InFNc_add W hz hz', ?_⟩
  · have hsplit : (Λ₁ * Λ₂) • (w₁ + w₁') = Λ₂ • (Λ₁ • w₁) + Λ₁ • (Λ₂ • w₁') := by
      rw [smul_add, mul_smul, mul_smul, smul_comm Λ₁ Λ₂ w₁]
    rw [hsplit]
    exact TypesA.InFNc_add W (TypesA.InFNc_smul W (TypesA.Ps_mem W hΛ₂) hΛw₁)
      (TypesA.InFNc_smul W (TypesA.Ps_mem W hΛ₁) hΛw₂)
  · rw [map_add, smul_add]
    exact TypesA.inMultiple_add W hP hP'
  · exact TypesA.RepVV_congr W (TypesA.RepVV_add W hR hR') (by rw [map_add]; abel)
      fun k => (mul_add _ _ _).symm

theorem LV_zero {e : ℕ}
    (h0 : RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol 0
      (fun _ => 0)) : LV W A F c b sol (fun _ => 0) e := by
  refine ⟨0, 0, TypesA.InI_zero W, ⟨1, one_mem _, ?_⟩, ?_, ⟨0, zero_mem _, smul_zero _, (smul_zero _).symm⟩,
    TypesA.RepVV_congr W h0 (by simp) fun k => (mul_zero _).symm⟩
  · rw [smul_zero]; exact ⟨0, zero_mem _, smul_zero _, (smul_zero _).symm⟩
  · rw [map_zero, smul_zero]; exact ⟨0, zero_mem _, (smul_zero _).symm⟩

theorem LV_sum {e : ℕ}
    (h0 : RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol 0
      (fun _ => 0)) {ι : Type} (s : Finset ι) (g : ι → Fin d → W.EE) (h : ∀ i ∈ s, LV W A F c b sol (g i) e) :
    LV W A F c b sol (fun k => ∑ i ∈ s, g i k) e := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LV_zero h0 (e := e)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact LV_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end LV

end Formalism.MainNotions.N.Ln17.PCutBoundRho
