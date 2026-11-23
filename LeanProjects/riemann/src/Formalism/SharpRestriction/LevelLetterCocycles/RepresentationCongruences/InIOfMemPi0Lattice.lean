import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsRhoZeroOfPi0

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

namespace Formalism.MainNotions.N.Ln17.PCutBoundGal

open Formalism.MainNotions.N.Ln17.PCutBoundRep Formalism.MainNotions.N.Ln17.PCutBoundRho

section Gal

variable {W : LocWach PD LL O v n} {A : ArcP n} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L}
    {c : ZMod n} {d : ℕ} {b : Fin d → W.DD T₂} {sol : Fin d → ℕ → Fin d → LL}

theorem LV_congr {g g' : Fin d → W.EE} {e : ℕ} (h : LV W A F c b sol g e) (hg : ∀ k, g k = g' k) :
    LV W A F c b sol g' e := by
  obtain rfl : g = g' := funext hg
  exact h

theorem LV_galois (hA : A.OK) (hc : c ∈ A.cuts) (hRelay : RelayCore W) (hArc : ArcCore W)
    (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p) (hW₁ : Win W A T₁) (hW₂ : Win W A T₂)
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol)
    {g : Fin d → W.EE} {e : ℕ} (he : A.σ PD.p ≤ e) (h : LV W A F c b sol g e)
    (u : W.DD T₂) (hu : InI W T₂ c u)
    (huP : InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1 (abelian₂ W A c (A.len c) • u))
    (hrep : RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol u
      (fun k => lE W (A.σ PD.p) * g k))
    (x₂ : LatticeCohomology T₂.L) (hx₂ : IsRho W A T₂ c u x₂) :
    ∃ x₁ ∈ latticeFiniteCohomology PD T₁.L, F.H1map x₁ = (((PD.p : ℕ) : O) ^ (e - A.σ PD.p)) • x₂ := by
  obtain ⟨w₁, z, hw, ⟨Λ', hΛ', hΛw⟩, hP, hz, hR⟩ := h
  have hπ := TypesA.pi0_mem_ADelta W
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = PD.p ^ (e - A.σ PD.p) := ⟨_, rfl⟩
  have hjle : A.j ≤ A.len c := hA.2.2.2.1 c hc
  have hAc := hArc hcase hl A hA c hc (A.len c) hjle le_rfl
  simp only [sub_add_cancel] at hAc
  obtain ⟨-, hAT⟩ := hAc
  obtain ⟨hPN, hNP, -, hfr⟩ := hAT T₂ hW₂
  obtain ⟨-, -, -, -, -, h0, -⟩ := hfr d b sol hb
  have hRX : RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol
      (W.map F w₁ - z - ((N : ℕ) : LetA O n) • u) 0 := by
    refine TypesA.RepVV_congr W (TypesA.RepVV_add W hR (TypesA.RepVV_neg W (TypesA.RepVV_nat W N hrep)))
      (sub_eq_add_neg _ _).symm fun k => ?_
    rw [Pi.zero_apply]
    unfold lE
    rw [hN, Nat.cast_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel he, add_neg_cancel]
  have hz1 : InFNc W T₂ c 1 z := TypesA.InFNc_one_smul W hπ hz
  have hΛX : InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1
      (abelian₂ W A c (A.len c) • (W.map F w₁ - z - ((N : ℕ) : LetA O n) • u)) := by
    rw [smul_sub, smul_sub]
    refine TypesA.inMultiple_sub W (TypesA.inMultiple_sub W hP (hNP z hz1)) ?_
    rw [smul_comm]
    exact TypesA.inMultiple_smul W (natCast_mem _ _) huP
  obtain ⟨y, hy, hXy⟩ := h0 _ hΛX hRX
  obtain ⟨y'', hy'', hyc'', hΛy⟩ := hPN y hy
  have hXπ : InFNc W T₂ c W.π₀ (W.map F w₁ - z - ((N : ℕ) : LetA O n) • u) :=
    ⟨y'', hy'', hyc'', by rw [hXy, mul_smul, hΛy, one_smul]⟩
  have hπw : InFNc W T₂ c W.π₀ (W.map F w₁ - ((N : ℕ) : LetA O n) • u) := by
    have hsplit : W.map F w₁ - ((N : ℕ) : LetA O n) • u =
        z + (W.map F w₁ - z - ((N : ℕ) : LetA O n) • u) := by abel
    rw [hsplit]
    exact TypesA.InFNc_add W hz hXπ
  have hIw : InI W T₂ c (W.map F w₁ - ((N : ℕ) : LetA O n) • u) := by
    rw [sub_eq_add_neg]
    exact TypesA.InI_add W (TypesA.InI_map W F hW₁.1 hW₂.1 hw) (TypesA.InI_neg W (TypesA.InI_nat W N hu))
  obtain ⟨hRel, hNat⟩ := hRelay hcase hl A hA c hc
  obtain ⟨-, hR1, -⟩ := hRel T₁ hW₁
  obtain ⟨-, hR2, hAdd⟩ := hRel T₂ hW₂
  obtain ⟨-, -, -, ⟨x₁, hx₁⟩, -, -, hPs⟩ := hR1 w₁ hw
  have hx₁f : x₁ ∈ latticeFiniteCohomology PD T₁.L := hPs Λ' x₁ hΛ' hΛw hx₁
  have hnat := hNat T₁ T₂ F hW₁ hW₂ w₁ x₁ hw hx₁
  have hNu : ∀ k : ℕ, IsRho W A T₂ c (((k : ℕ) : LetA O n) • u) (k • x₂) := by
    intro k
    induction k with
    | zero =>
      rw [Nat.cast_zero, zero_smul, zero_nsmul]
      exact (hR2 0 (TypesA.InI_zero W)).2.2.2.2.2.1 ⟨0, zero_mem _, smul_zero _, (smul_zero _).symm⟩
    | succ k ih =>
      rw [Nat.cast_succ, add_smul, one_smul, succ_nsmul]
      exact hAdd _ _ _ _ (TypesA.InI_nat W k hu) hu ih hx₂
  have hw0 : IsRho W A T₂ c (W.map F w₁ - ((N : ℕ) : LetA O n) • u) 0 :=
    (hR2 _ hIw).2.2.2.2.2.1 hπw
  have hsum := hAdd _ _ _ _ hIw (TypesA.InI_nat W N hu) hw0 (hNu N)
  rw [sub_add_cancel, zero_add] at hsum
  have huniq := (hR2 (W.map F w₁) (TypesA.InI_map W F hW₁.1 hW₂.1 hw)).2.2.2.2.1 _ _ hnat hsum
  refine ⟨x₁, hx₁f, ?_⟩
  rw [huniq, hN, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

end Gal

theorem pk_eq (W : LocWach PD LL O v n) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL)) (κ : ℕ) (P1 : O)
    (hv : v (algebraMap O LL P1) = ((κ : ℕ) : WithTop ℚ)) : ∃ y : O, ((PD.p : ℕ) : O) ^ κ = y * P1 := by
  have hP1 : algebraMap O LL P1 ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hv
    exact (WithTop.natCast_ne_top κ) hv.symm
  set z : LL := (PD.p : LL) ^ κ * (algebraMap O LL P1)⁻¹ with hz
  have hzP : z * algebraMap O LL P1 = (PD.p : LL) ^ κ := by
    rw [hz, mul_assoc, inv_mul_cancel₀ hP1, mul_one]
  have hvz : 0 ≤ v z := by
    by_cases htop : v z = ⊤
    · rw [htop]; exact le_top
    have h1 := congrArg v hzP
    rw [AddValuation.map_mul, AddValuation.map_pow, W.v_l, hv, nsmul_one] at h1
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 htop
    rw [← hq, ← WithTop.coe_natCast, ← WithTop.coe_add, WithTop.coe_inj] at h1
    have hq0 : q = 0 := by linarith
    rw [← hq, hq0]
    exact le_refl _
  obtain ⟨y, hy⟩ := hOv z hvz
  refine ⟨y, hinj ?_⟩
  rw [map_mul, hy, map_pow, map_natCast, hzP]

section Fr

variable (W : LocWach PD LL O v n)

theorem InFr_add {a : ZMod n} {num den : LetA O n} {f f' : W.EE} (h : InFr W a num den f)
    (h' : InFr W a num den f') : InFr W a num den (f + f') := by
  obtain ⟨u, hu, he⟩ := h
  obtain ⟨u', hu', he'⟩ := h'
  exact ⟨u + u', add_mem hu hu', by rw [mul_add, he, he', ← map_add, mul_add]⟩

theorem InFr_zero {a : ZMod n} {num den : LetA O n} : InFr W a num den 0 :=
  ⟨0, zero_mem _, by simp⟩

theorem InFr_smulO {a : ZMod n} {num den : LetA O n} (o : O) {f : W.EE} (h : InFr W a num den f) :
    InFr W a num den (o • f) := by
  obtain ⟨u, hu, he⟩ := h
  refine ⟨algebraMap O (LetA O n) o * u, W.AΔ.mul_mem (W.AΔ.algebraMap_mem o) hu, ?_⟩
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE, mul_left_comm, he, ← map_mul]
  congr 1
  ring

theorem InFr_Lam_iff (A : ArcP n) (a : ZMod n) (e : ℕ) (f : W.EE) :
    InFr W a 1 (abelian₂ W A a e) f ↔ InId W a e (fun s => -(A.Hs a e s : ℤ)) f := by
  unfold InId abelian₂
  have h1 : ∏ s ∈ Finset.range e, ps W s ^ (-(A.Hs a e s : ℤ)).toNat = 1 := by
    refine Finset.prod_eq_one fun s _ => ?_
    rw [show (-(A.Hs a e s : ℤ)).toNat = 0 by omega, pow_zero]
  have h2 : ∀ s, (-(-(A.Hs a e s : ℤ))).toNat = A.Hs a e s := fun s => by omega
  simp only [h1, h2]

theorem InFr_γ (hR : GS.RD W) (A : ArcP n) {a : ZMod n} {e : ℕ} {f : W.EE} (h : InFr W a 1 (abelian₂ W A a e) f) :
    InFr W a 1 (abelian₂ W A a e) (W.γE W.gam f) := by
  rw [InFr_Lam_iff] at h ⊢
  exact (GS.gam_frac_core hR a e _ f h).1

theorem InFr_aeval (hR : GS.RD W) (A : ArcP n) {a : ZMod n} {e : ℕ} {f : W.EE}
    (h : InFr W a 1 (abelian₂ W A a e) f) (P : Polynomial O) :
    InFr W a 1 (abelian₂ W A a e) (Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P f) := by
  rw [aevalE_eq]
  refine Finset.sum_induction _ _ (fun _ _ => InFr_add W) (InFr_zero W) fun i hi => InFr_smulO W _ ?_
  clear hi
  induction i with
  | zero => simpa using h
  | succ i ih => rw [Function.iterate_succ_apply']; exact InFr_γ W hR A ih

end Fr

section Cls

variable (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

theorem inI_of_mem_pi0_lattice (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) {c : ZMod n} {z : W.DD T}
    (h : InFNc W T c W.π₀ z) : InI W T c z := by
  obtain ⟨y, hy, hyc, rfl⟩ := h
  obtain ⟨u, hu, hγπ⟩ := hpi0
  have hy' : y ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ y = y := hy
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • (W.π₀ • y) = W.π₀ • y
    rw [smul_comm, hyc]
  · show ∀ δ ∈ W.DelF, W.γD T δ (W.π₀ • y) = W.π₀ • y
    intro δ hδ
    rw [GS.γD_smulA, TypesA.pi0_mem_ADelta W δ hδ, hy'.2 δ hδ]
  · refine ⟨u • W.γ T y - y, sub_mem (TypesA.NΔ_smul W hu (γ_NΔ W hT hP2 hy)) hy, ?_, ?_⟩
    · rw [smul_sub, hyc, smul_comm, ← GS.γA_letE W W.gam c, ← γ_smul, hyc]
    · rw [γ_smul, hγπ, smul_sub, mul_smul]

variable {c' : ZMod n} {e : ℕ} {Λ : LetA O n}

theorem InFPΛ_γ (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hΛ : ∃ R ∈ W.AΔ, ∃ R' ∈ W.AΔ, R * R' = 1 ∧ W.γA W.gam Λ = R * Λ) {x : W.DD T}
    (h : InFP W T c' e 1 (Λ • x)) : InFP W T c' e 1 (Λ • W.γ T x) := by
  obtain ⟨R, -, R', hR', hRR, hγΛ⟩ := hΛ
  have h2 := γ_InFP W hT hP2 h
  rw [map_one, γ_smul, hγΛ] at h2
  have h3 := TypesA.inMultiple_smul W hR' h2
  rwa [smul_smul, ← mul_assoc, mul_comm R' R, hRR, one_mul] at h3

theorem InFPΛ_aeval (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hΛ : ∃ R ∈ W.AΔ, ∃ R' ∈ W.AΔ, R * R' = 1 ∧ W.γA W.gam Λ = R * Λ) {x : W.DD T}
    (h : InFP W T c' e 1 (Λ • x)) (P : Polynomial O) :
    InFP W T c' e 1 (Λ • Polynomial.aeval (W.γ T) P x) := by
  rw [aeval_eq, Finset.smul_sum]
  refine inMultiple_sum W _ _ fun i hi => ?_
  clear hi
  rw [← algebraMap_smul (LetA O n) (P.coeff i), smul_comm]
  refine TypesA.inMultiple_smul W (W.AΔ.algebraMap_mem _) ?_
  induction i with
  | zero => simpa using h
  | succ i ih => rw [Function.iterate_succ_apply']; exact InFPΛ_γ W hT hP2 hΛ ih

end Cls

end Formalism.MainNotions.N.Ln17.PCutBoundGal
