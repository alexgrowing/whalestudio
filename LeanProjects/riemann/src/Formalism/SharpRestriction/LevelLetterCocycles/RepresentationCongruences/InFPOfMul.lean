import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit

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

namespace Formalism.MainNotions.N.Ln17.PCutBoundRep

variable (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

theorem γ_smul (a : LetA O n) (x : W.DD T) : W.γ T (a • x) = W.γA W.gam a • W.γ T x :=
  GS.γD_smulA W T W.gam a x

theorem γA_lA (k : ℕ) : W.γA W.gam (lA W ^ k) = lA W ^ k := by
  simp only [lA, map_pow, map_natCast]

theorem φD_smulA (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem φpow_smulA (e : ℕ) (a : LetA O n) (x : W.DD T) :
    ((W.φD T) ^ e) (a • x) = (W.φA ^ e) a • ((W.φD T) ^ e) x := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ', pow_succ', Module.End.mul_apply, ih, φD_smulA, Module.End.mul_apply]
      <;> rfl

theorem γ_φpow (e : ℕ) (x : W.DD T) : W.γ T (((W.φD T) ^ e) x) = ((W.φD T) ^ e) (W.γ T x) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    exact (W.φγ_comm T W.gam _).symm

theorem γ_Δ {x : W.DD T} (h : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    ∀ δ ∈ W.DelF, W.γD T δ (W.γ T x) = W.γ T x := by
  intro δ hδ
  show W.γD T δ (W.γD T W.gam x) = W.γD T W.gam x
  rw [← W.γD_mul, mul_comm, W.γD_mul, h δ hδ]

theorem γ_NΔ (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {x : W.DD T} (hx : x ∈ W.NΔ T) :
    W.γ T x ∈ W.NΔ T := by
  have hx' : x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := hx
  show W.γ T x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ (W.γ T x) = W.γ T x
  exact ⟨(hP2 T hT).1 W.gam x hx'.1, γ_Δ W hx'.2⟩

theorem γ_NΔi (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {c : ZMod n} {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : Formalism.MainNotions.LiftingTheory.InNΔi W T c (W.γ T x) := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨γ_NΔ W hT hP2 h1, ?_⟩
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.1 h2
  refine Submodule.mem_map.2 ⟨W.γ T z, (hP2 T hT).1 W.gam z hz, ?_⟩
  rw [← hzx]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [γ_smul, GS.γA_letE]

theorem γ_Pp (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {c : ZMod n} {e : ℕ} {y : W.DD T}
    (hy : y ∈ Pp W T c e) : W.γ T y ∈ Pp W T c e := by
  have key : Pp W T c e ≤ (Pp W T c e).comap (W.γ T).toAddMonoidHom := by
    unfold Pp
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    refine AddSubgroup.mem_comap.2 ?_
    show W.γ T (a • ((W.φD T) ^ e) x) ∈ _
    rw [γ_smul, γ_φpow]
    exact AddSubgroup.subset_closure ⟨_, GS.γA_mem W W.gam ha, _, γ_NΔi W hT hP2 hx, rfl⟩
  exact key hy

theorem γ_InFP (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) {c : ZMod n} {e : ℕ} {f : LetA O n}
    {x : W.DD T} (h : InFP W T c e f x) : InFP W T c e (W.γA W.gam f) (W.γ T x) := by
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨W.γ T y, γ_Pp W hT hP2 hy, γ_smul W f y⟩

theorem inMultiple_of_mul {c : ZMod n} {e : ℕ} {f g : LetA O n} (hg : g ∈ W.AΔ) {x : W.DD T}
    (h : InFP W T c e (f * g) x) : InFP W T c e f x := by
  obtain ⟨y, hy, rfl⟩ := h
  refine ⟨g • y, ?_, mul_smul f g y⟩
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x', hx', rfl⟩ := hz
    apply AddSubgroup.subset_closure
    exact ⟨g * a, mul_mem hg ha, x', hx', (mul_smul g a _).symm⟩
  | zero => rw [smul_zero]; exact (Pp W T c e).zero_mem
  | add u v _ _ hu hv => rw [smul_add]; exact (Pp W T c e).add_mem hu hv
  | neg u _ hu => rw [smul_neg]; exact (Pp W T c e).neg_mem hu

theorem inMultiple_zero {c : ZMod n} {e : ℕ} {f : LetA O n} : InFP W T c e f 0 :=
  ⟨0, (Pp W T c e).zero_mem, (smul_zero f).symm⟩

theorem inMultiple_sum {c : ZMod n} {e : ℕ} {f : LetA O n} {ι : Type} (s : Finset ι) (x : ι → W.DD T)
    (h : ∀ i ∈ s, InFP W T c e f (x i)) : InFP W T c e f (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact inMultiple_zero W
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨y, hy, hxy⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨y', hy', hxy'⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact ⟨y + y', (Pp W T c e).add_mem hy hy', by rw [hxy, hxy', smul_add]⟩

theorem InI_γ (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) {c : ZMod n} {w : W.DD T}
    (h : InI W T c w) : InI W T c (W.γ T w) := by
  obtain ⟨h1, h2, ⟨y, hy, hyc, hxy⟩⟩ := h
  have h1 : (letE (O := O) c : LetA O n) • w = w := h1
  have h2 : ∀ δ ∈ W.DelF, W.γD T δ w = w := h2
  obtain ⟨u, hu, hγπ⟩ := hpi0
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • W.γ T w = W.γ T w
    rw [← GS.γA_letE W W.gam c, ← γ_smul, h1]
  · exact γ_Δ W h2
  · refine ⟨u • W.γ T y, TypesA.NΔ_smul W hu (γ_NΔ W hT hP2 hy), ?_, ?_⟩
    · rw [smul_comm, ← GS.γA_letE W W.gam c, ← γ_smul, hyc]
    · have : W.γ T (W.γ T w) - W.γ T w = W.γ T (W.γ T w - w) := by rw [map_sub]
      rw [this, hxy, γ_smul, hγπ, mul_smul]

theorem InI_smulA {c : ZMod n} {a : LetA O n} (ha : a ∈ W.AΔ) (ha' : W.γA W.gam a = a) {w : W.DD T}
    (h : InI W T c w) : InI W T c (a • w) := by
  obtain ⟨h1, h2, h3⟩ := h
  have h1 : (letE (O := O) c : LetA O n) • w = w := h1
  have h2 : ∀ δ ∈ W.DelF, W.γD T δ w = w := h2
  refine ⟨?_, ?_, ?_⟩
  · show (letE (O := O) c : LetA O n) • (a • w) = a • w
    rw [smul_comm, h1]
  · show ∀ δ ∈ W.DelF, W.γD T δ (a • w) = a • w
    intro δ hδ
    rw [GS.γD_smulA, ha δ hδ, h2 δ hδ]
  · have : W.γ T (a • w) - a • w = a • (W.γ T w - w) := by rw [γ_smul, ha', smul_sub]
    rw [this]
    exact TypesA.InFNc_smul W ha h3

theorem InI_smulO {c : ZMod n} (o : O) {w : W.DD T} (h : InI W T c w) : InI W T c (o • w) := by
  obtain ⟨h1, h2, y, hy, hyl, hyx⟩ := h
  refine ⟨?_, ?_, o • y, (W.NΔ T).smul_mem o hy, ?_, ?_⟩
  · unfold InLet at h1 ⊢
    rw [smul_comm, h1]
  · intro δ hδ
    rw [map_smul, h2 δ hδ]
  · rw [smul_comm, hyl]
  · rw [map_smul, ← smul_sub, hyx, smul_comm]

theorem InI_sum {c : ZMod n} {ι : Type} (s : Finset ι) (x : ι → W.DD T) (h : ∀ i ∈ s, InI W T c (x i)) :
    InI W T c (∑ i ∈ s, x i) := by
  classical
  have hadd : ∀ x y, InI W T c x → InI W T c y → InI W T c (x + y) := by
    rintro x y ⟨hx1, hx2, u, hu, hul, hux⟩ ⟨hy1, hy2, u', hu', hul', hux'⟩
    refine ⟨?_, ?_, u + u', (W.NΔ T).add_mem hu hu', ?_, ?_⟩
    · unfold InLet at hx1 hy1 ⊢
      rw [smul_add, hx1, hy1]
    · intro δ hδ
      rw [map_add, hx2 δ hδ, hy2 δ hδ]
    · rw [smul_add, hul, hul']
    · rw [map_add, add_sub_add_comm, hux, hux', smul_add]
  have hzero : InI W T c 0 := ⟨by unfold InLet; rw [smul_zero], fun δ _ => map_zero _, 0,
    (W.NΔ T).zero_mem, smul_zero _, by rw [map_zero, sub_zero, smul_zero]⟩
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hzero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hadd _ _ (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem InI_iter (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) {c : ZMod n} {w : W.DD T} (h : InI W T c w) (i : ℕ) :
    InI W T c ((W.γ T)^[i] w) := by
  induction i with
  | zero => simpa using h
  | succ i ih => rw [Function.iterate_succ_apply']; exact InI_γ W hT hP2 hpi0 ih

theorem aeval_eq (P : Polynomial O) (x : W.DD T) :
    Polynomial.aeval (W.γ T) P x = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • (W.γ T)^[i] x := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  simp [Module.End.pow_apply]

theorem aevalE_eq (P : Polynomial O) (f : W.EE) :
    Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) P f =
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • (W.γE W.gam)^[i] f := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  simp [Module.End.pow_apply]

theorem InI_aeval (hT : IsCrys PD T.ρ) (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W)
    (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u) {c : ZMod n} {w : W.DD T} (h : InI W T c w)
    (P : Polynomial O) : InI W T c (Polynomial.aeval (W.γ T) P w) := by
  rw [aeval_eq]
  exact InI_sum W _ _ fun i _ => InI_smulO W _ (InI_iter W hT hP2 hpi0 h i)

end Formalism.MainNotions.N.Ln17.PCutBoundRep
