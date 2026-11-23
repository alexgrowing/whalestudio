import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDoubleDescentRanksOneThreeFive
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToOneSpherical
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatEqMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLocalEqIntegralAlmostAllStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl.PinTest
open GlobalTheory.QPl.Model

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]

theorem blk_mul (g h : GL (n ⊕ Fin 0) k) : (g * h).val.toBlocks₁₁ = g.val.toBlocks₁₁ * h.val.toBlocks₁₁ := by
  rw [Units.val_mul, mul_toBlocks₁₁]
  ext i j
  simp [Matrix.mul_apply]

theorem box_stable {g : GL (n ⊕ Fin 0) k} (hg : g ∈ KO k _) (a : kˣ) {y : n → k} (hy : y ∈ box n a) :
    g.val.toBlocks₁₁ *ᵥ y ∈ box n a := fun i => by
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le ((mem_KO.1 hg).1 (Sum.inl i) (Sum.inl j)) (hy j)

theorem sameOrb_mk {J : Subgroup (GL (n ⊕ Fin 0) k)} (hJ : J ≤ KO k _) (a : kˣ) (y : n → k) (yb : (n → k) ⧸ box n a) :
    SameOrb J (box n a) (Submodule.Quotient.mk y) yb ↔ ∃ g ∈ J, Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) = yb := by
  refine ⟨?_, fun ⟨g, hg, e⟩ => ⟨g, hg, y, rfl, e⟩⟩
  rintro ⟨g, hg, y', e, rfl⟩
  refine ⟨g, hg, (Submodule.Quotient.eq _).2 ?_⟩
  rw [← mulVec_sub]
  exact box_stable (hJ hg) a ((Submodule.Quotient.eq _).1 e.symm)

theorem sameOrb_equiv {J : Subgroup (GL (n ⊕ Fin 0) k)} (hJ : J ≤ KO k _) (a : kˣ) : Equivalence (SameOrb J (box n a)) := by
  have h1 : (1 : GL (n ⊕ Fin 0) k).val.toBlocks₁₁ = 1 := by rw [Units.val_one, ← fromBlocks_one, toBlocks_fromBlocks₁₁]
  refine ⟨fun x => ?_, ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨1, one_mem _, y, rfl, by rw [h1, one_mulVec]⟩
  · rintro _ _ ⟨g, hg, y, rfl, rfl⟩
    exact ⟨g⁻¹, inv_mem hg, _, rfl, by rw [mulVec_mulVec, ← blk_mul, inv_mul_cancel, h1, one_mulVec]⟩
  · rintro _ _ z ⟨g, hg, y, rfl, rfl⟩ h
    obtain ⟨g', hg', rfl⟩ := (sameOrb_mk hJ a _ z).1 h
    exact ⟨g' * g, mul_mem hg' hg, y, rfl, by rw [mulVec_mulVec, ← blk_mul]⟩

theorem card_orb_ne_zero {J : Subgroup (GL (n ⊕ Fin 0) k)} (hJ : J ≤ KO k _) (hc : IsCompact (J : Set (GL (n ⊕ Fin 0) k))) (a : kˣ)
    (x : (n → k) ⧸ box n a) : Nat.card {yb | SameOrb J (box n a) x yb} ≠ 0 := by
  refine Nat.card_ne_zero.2 ⟨⟨x, (sameOrb_equiv hJ a).1 x⟩, ?_⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have ho : IsOpen ((box n a : Submodule 𝒪[k] (n → k)) : Set (n → k)) := by
    convert (isOpen_set_pi Set.finite_univ fun (_ : n) _ => isOpen_cball a) using 1
    ext z; simp [mem_box, cball]
  have hd : DiscreteTopology ((n → k) ⧸ box n a) := QuotientAddGroup.discreteTopology (N := (box n a).toAddSubgroup) ho
  have hf : Continuous fun g : GL (n ⊕ Fin 0) k => (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) : (n → k) ⧸ box n a) := by
    refine continuous_quot_mk.comp (Continuous.matrix_mulVec ?_ continuous_const)
    exact continuous_pi fun i => continuous_pi fun j => (Units.continuous_val (M := Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k)).matrix_elem (Sum.inl i) (Sum.inl j)
  have := (hc.image hf).finite_of_discrete
  refine Set.Finite.to_subtype (this.subset fun z hz => ?_)
  obtain ⟨g, hg, e⟩ := (sameOrb_mk hJ a y z).1 hz
  exact ⟨g, hg, e⟩

theorem orb_zero {J : Subgroup (GL (n ⊕ Fin 0) k)} (hJ : J ≤ KO k _) (a : kˣ) :
    {yb | SameOrb J (box n a) (Submodule.Quotient.mk 0) yb} = {Submodule.Quotient.mk 0} := by
  ext z
  simp only [Set.mem_setOf_eq, sameOrb_mk hJ, mulVec_zero, Set.mem_singleton_iff]
  exact ⟨fun ⟨_, _, e⟩ => e.symm, fun e => ⟨1, one_mem _, e.symm⟩⟩

theorem prX_KO {c : ℕ} : prX (Cgrp (KO k (n ⊕ Fin c)) 1) = KO k n := by
  have key : ∀ g : GL n k, g ∈ prX (Cgrp (KO k (n ⊕ Fin c)) 1) → IntM g.val := by
    rintro g ⟨u, hu, h⟩ i j
    have h2 := (mem_KO.1 (mem_Cgrp.1 h).2).1 (Sum.inl i) (Sum.inl j)
    have h3 : (u * embX c g).val.toBlocks₁₁ = g.val := by
      rw [Units.val_mul, mul_toBlocks₁₁, Radical.toBlocks₁₁_of_mem hu]
      change 1 * (fromBlocks g.val 0 0 1).toBlocks₁₁ + _ * (fromBlocks g.val 0 0 1).toBlocks₂₁ = _
      simp
    rw [inv_one, one_mul, mul_one] at h2
    rw [← h3]; exact h2
  ext g
  refine ⟨fun h => mem_KO.2 ⟨key g h, key _ (inv_mem h)⟩, fun h => ⟨1, one_mem _, mem_Cgrp.2 ⟨?_, ?_⟩⟩⟩
  · rw [one_mul]; exact Subgroup.mem_sup_left ⟨g, rfl⟩
  · rw [inv_one, one_mul, one_mul, mul_one]
    refine mem_KO.2 ⟨intM_fromBlocks.2 ⟨(mem_KO.1 h).1, intM_zero, intM_zero, intM_of_mem_KO (one_mem _)⟩, ?_⟩
    rw [← map_inv]
    exact intM_fromBlocks.2 ⟨(mem_KO.1 h).2, intM_zero, intM_zero, intM_of_mem_KO (one_mem _)⟩

variable {s : ℕ} (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z : Type) [Fintype Z] [DecidableEq Z]

def sphChain (s : ℕ) (μ : ℕ → kˣ →* ℂˣ) : Chain k s X Z :=
  ⟨fun _ _ _ => sph k _, fun _ _ _ => 1, sph k _, μ, fun _ _ _ => ind k _ _, ind k _ _⟩

open Classical in
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem ind_apply {a b : Type} (x : Matrix a b k) : ind k a b x = if IntM x then 1 else 0 := Set.indicator_apply _ _ _

theorem ind_SB (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] : ind k a b ∈ SB (Matrix a b k) := by
  obtain ⟨Φ, h, -⟩ := PinModel.exists_isOne (k := k) (Y := a) (Y' := b)
  have e : Φ.1 = ind k _ _ := h
  exact e ▸ Φ.2

theorem sph_reg (μ : ℕ → kˣ →* ℂˣ) : (sphChain X Z s μ).Regular :=
  ⟨fun _ _ _ => ind_SB _ _, ind_SB _ _, fun _ _ _ => ⟨SplitFlip.isOpen_KO, SplitFlip.isCompact_KO, fun g hg => by
    rw [mem_stabLat]; simpa [sphChain, sph] using hg⟩⟩

open Classical in
theorem sph_psi' (μ : ℕ → kˣ →* ℂˣ) (x₀ y) : (sphChain X Z s μ).Psi 1 x₀ y = if IntM x₀ ∧ ∀ i, y i ∈ 𝒪[k] then 1 else 0 := by
  rw [Chain.Psi, om_one]
  refine (ind_apply _).trans (if_congr ⟨fun h => ⟨fun i j => h (.inl i) (.inl j), fun i => h (.inl i) (.inr 0)⟩, fun h => ?_⟩ rfl rfl)
  rintro (r | r) (q | q)
  exacts [h.1 r q, h.2 r, r.elim0, r.elim0]

theorem sph_psi (μ : ℕ → kˣ →* ℂˣ) (x₀ y) : (sphChain X Z s μ).Psi 1 x₀ y ≠ 0 ↔ IntM x₀ ∧ ∀ i, y i ∈ 𝒪[k] := by
  rw [sph_psi']; split_ifs with h <;> simp [h]

theorem mem_box_one {y : n → k} : y ∈ box n (1 : kˣ) ↔ ∀ i, y i ∈ 𝒪[k] := by rw [box_one, mem_latOf_one]

theorem sph_adapt (μ : ℕ → kˣ →* ℂˣ) : (sphChain X Z s μ).Adapted (fun _ _ _ => {1}) (box _ 1) (box _ 1) := by
  classical
  rintro g rfl x₀ y
  refine ⟨fun h => mem_box_one.2 ((sph_psi X Z μ x₀ y).1 h).2, fun z hz => ?_⟩
  rw [sph_psi', sph_psi']
  have hz := mem_box_one.1 hz
  refine if_congr (and_congr_right fun _ => forall_congr' fun i => ?_) rfl rfl
  exact ⟨fun h => by simpa using sub_mem h (hz i), fun h => add_mem h (hz i)⟩

theorem sph_pen (μ : ℕ → kˣ →* ℂˣ) : (sphChain X Z s μ).xiPen (box _ 1) 1 (Submodule.Quotient.mk 0) = ind k _ _ := by
  classical
  funext x₀
  rw [Chain.xiPen_mk (sph_adapt X Z μ) rfl, sph_psi']
  rw [ind_apply]
  exact if_congr ⟨fun h => h.1, fun h => ⟨h, fun _ => zero_mem _⟩⟩ rfl rfl

variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν)
include hψ hν

theorem sph_top (μ : ℕ → kˣ →* ℂˣ) : (sphChain X Z s μ).xiTop (box _ 1) ψ ν (-1) (Submodule.Quotient.mk 0) = ind k _ _ := by
  classical
  funext x
  rw [Chain.xiTop, GlobalTheory.LastTwoSteps.hat_int hψ hν (by simp)]
  change ind k _ _ _ * _ = _
  rw [ind_apply, ind_apply]
  have e : IntM x ↔ IntM (fromCols x.toRows₁ (0 : Matrix Z (Fin 0) k)) ∧ ∀ i, x (Sum.inr ()) i ∈ 𝒪[k] := by
    refine ⟨fun h => ⟨?_, fun i => h _ _⟩, fun h => ?_⟩
    · rintro r (q | q)
      exacts [h _ _, q.elim0]
    · rintro (r | r) q
      exacts [h.1 r (.inl q), h.2 q]
  rw [if_congr e rfl rfl]
  split_ifs <;> simp_all

theorem sph_reps (μ : ℕ → kˣ →* ℂˣ) : (sphChain X Z s μ).IsRepSystem (fun _ _ _ => {1}) ψ ν := by
  refine ⟨fun _ _ => rfl, fun j c h => ?_⟩
  have hc := (covers_ind (n := X (j + 1)) (n' := X j) (c := c) hψ hν (μ (j + 1))).2
  have hx := xi_ind (n := X (j + 1)) (n' := X j) (c := c) hψ hν (μ (j + 1))
  refine ⟨?_, by simp, fun β hβ => ?_⟩
  · rintro g rfl
    simp only [Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]
    refine ⟨1, rfl, fun h0 => ?_⟩
    have := congrFun hx 0
    rw [xi, show GlobalTheory.StepData.flat ψ ν (μ (j + 1)) (ind k _ _) 1 1 = 0 from h0] at this
    rw [ind_apply, if_pos intM_zero] at this
    simp at this
  · simp only [Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left] at hβ
    obtain ⟨g, rfl, hg⟩ := hβ
    obtain ⟨t, ht, e⟩ := hc g hg
    exact ⟨1, rfl, by rw [Finset.mem_singleton.1 ht] at e; exact e.symm⟩

theorem isOneComb_sph {c P : ℕ} (h1 : 1 ≤ P) (h2 : P ≤ c) : IsOneComb ψ ν P (sph k (n ⊕ Fin c)) 1 (Finsupp.single 1 1) :=
  fun A _ _ σ hσ l hl v hv => by
  rw [map_one, Module.End.one_apply, GlobalTheory.PosOneSpherical.toOne_spherical k n c P h1 h2 ψ hψ.continuous hψ ν hν A σ hσ l hl v
    fun g hg => (hv ⟨g, hg⟩).trans (one_smul ℂ v)]
  simp [GlobalTheory.PosOne.comb]

end Local

section Rat
variable {D : D7}

theorem ae_int (a : D.host.E) : ∀ᶠ x : GlobalTheory.FinPl.Pl D in Filter.cofinite, ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.v = x → (ofSplit q).pr a ∈ 𝒪[k] := by
  filter_upwards [GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D a] with x hx k _ _ _ _ q hq
  subst hq
  have h := hx _ ((DblInhab.sec_mem_intAt q 1).2 (by simp))
  have e : incA D a * q.sec 1 = q.sec ((ofSplit q).pr a) := by
    rw [← map_one q.pr, q.sec_pr, mul_one, mul_comm, ← q.sec_pr]; rfl
  exact (DblInhab.sec_mem_intAt q _).1 (e ▸ h)

theorem exists_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (f : D.host.E →+* k)
    {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (M : Matrix (Fin N) Y D.host.E) (F : GlobalTheory.LocMod.Frame k N Y) (h : F.β = M.map f) :
    ∃ M' : Matrix Y (Fin N) D.host.E, M * M' = 1 := by
  let e : Y ≃ Fin N := Fintype.equivFinOfCardEq (Witness.card_frame F).symm
  have h1 : (M.submatrix id e.symm).map f * F.γ.submatrix e.symm id = 1 := by
    rw [← Matrix.submatrix_map, ← h, submatrix_mul_equiv, F.βγ, submatrix_id_id]
  have h2 : (M.submatrix id e.symm).det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det h1
    rw [det_mul, det_one, show ((M.submatrix id e.symm).map f).det = f (M.submatrix id e.symm).det from
      (RingHom.map_det f _).symm, h0, map_zero, zero_mul] at this
    exact zero_ne_one this
  refine ⟨(M.submatrix id e.symm)⁻¹.submatrix e id, ?_⟩
  have := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h2)
  rw [← this]
  conv_lhs => rw [show M = (M.submatrix id e.symm).submatrix id e by simp]
  rw [submatrix_mul_equiv, submatrix_id_id]
  simp

theorem ae_frame (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (hL : Submodule.IsLattice D.host.E L) {Y : Type} [Fintype Y] [DecidableEq Y]
    (M : Matrix (Fin S.rank) Y D.host.E) : ∀ᶠ x : GlobalTheory.FinPl.Pl D in Filter.cofinite, ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.v = x → ∀ F : GlobalTheory.LocMod.Frame k S.rank Y,
      F.β = M.map (ofSplit q).pr → ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔
        (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) := by
  by_cases h : ∃ M' : Matrix Y (Fin S.rank) D.host.E, M * M' = 1
  · obtain ⟨M', h⟩ := h
    filter_upwards [GlobalTheory.T.lattice_local_eq_integral_almost_all D S L hL, Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ae_int (M i j),
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ae_int (M' i j)] with x h1 h2 h3 k _ _ _ _ q hq F hF y
    subst hq
    have e : F.γ = M'.map (Witness.prH (ofSplit q)) := by
      have := congrArg (fun A => F.γ * Matrix.map A (Witness.prH (ofSplit q))) h
      simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this
      rw [← this, show M.map (Witness.prH (ofSplit q)) = F.β from hF.symm, ← Matrix.mul_assoc, F.γβ, Matrix.one_mul]
    rw [h1]
    simp only [DblInhab.sec_mem_intAt]
    refine ⟨fun hy i => (sum_mem fun j _ => mul_mem (by rw [hF]; exact h2 i j k q rfl) (hy j) : _ ∈ 𝒪[k]), fun hy i => ?_⟩
    rw [show y = F.γ *ᵥ (F.β *ᵥ y) by rw [mulVec_mulVec, F.γβ, one_mulVec]]
    exact sum_mem (t := Finset.univ) (f := fun j => F.γ i j * (F.β *ᵥ y) j) fun j _ => mul_mem (by rw [e]; exact h3 i j k q rfl) (hy j)
  · exact Filter.Eventually.of_forall fun x k _ _ _ _ q _ F hF => absurd (exists_inv (Witness.prH (ofSplit q)) M F hF) h

theorem rat_bes {ρ : ℕ} (B : BesLev D ρ) (n c : ℕ) : ∃ M : Matrix (Fin B.V.rank) (Fin B.A.rank ⊕ Fin c) D.host.E,
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
      (F : GlobalTheory.LocMod.Frame k B.V.rank (Fin B.A.rank ⊕ Fin c)), p.IsBesFrame B (p.xi ^ n) (Frame.ofGL 1) F → F.β = M.map p.pr := by
  suffices H : ∀ r y, ∃ m : D.host.E, ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (p : Place D k) (F : GlobalTheory.LocMod.Frame k B.V.rank (Fin B.A.rank ⊕ Fin c)), p.IsBesFrame B (p.xi ^ n) (Frame.ofGL 1) F →
      F.β r y = Witness.prH p m by
    choose M hM using H
    exact ⟨Matrix.of M, fun k _ _ _ _ p F h => Matrix.ext fun r y => hM r y k p F h⟩
  rintro r (a | j)
  · exact ⟨(B.d.i₀ * B.o.iA) r a, fun k _ _ _ _ p F h => by rw [h.2.1]; simp [Frame.ofGL]; rfl⟩
  · by_cases hc : c = 2 * ρ + 1
    swap
    · exact ⟨0, fun k _ _ _ _ p F h => absurd h.1 hc⟩
    have := j.2
    rcases lt_trichotomy j.val ρ with hj | hj | hj
    · exact ⟨D.host.xi0 ^ n * D.host.xi0 ^ (ρ - j.val) * B.d.e r ⟨j, hj⟩, fun k _ _ _ _ p F h => by
        rw [h.2.2.1 ⟨j, hj⟩ j rfl]; simp only [map_mul, map_pow]; rfl⟩
    · exact ⟨D.host.xi0 ^ n * (B.d.i₀ *ᵥ vecB B.o B.ζ) r, fun k _ _ _ _ p F h => by
        rw [h.2.2.2.1 j hj]; simp only [map_mul, map_pow]; rfl⟩
    · exact ⟨D.host.xi0 ^ n * (-(star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) / D.host.xi0) * (-1 / D.host.xi0) ^ (ρ - 1 - (2 * ρ - j.val)) *
        B.d.e' r ⟨2 * ρ - j.val, by omega⟩, fun k _ _ _ _ p F h => by
        rw [h.2.2.2.2 ⟨2 * ρ - j.val, by omega⟩ j (by simp only; omega)]
        simp only [map_mul, map_pow, map_div₀, map_neg, map_one]; rfl⟩

theorem rat_jac {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) (n c : ℕ) : ∃ M : Matrix (Fin J.W.rank) (Fin J.W₀.rank ⊕ Fin c) D.host.E,
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
      (F : GlobalTheory.LocMod.Frame k J.W.rank (Fin J.W₀.rank ⊕ Fin c)), p.IsJacFrame J (p.xi ^ n) (p.hz B) (Frame.ofGL 1) F →
        F.β = M.map p.pr := by
  suffices H : ∀ r y, ∃ m : D.host.E, ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (p : Place D k) (F : GlobalTheory.LocMod.Frame k J.W.rank (Fin J.W₀.rank ⊕ Fin c)),
      p.IsJacFrame J (p.xi ^ n) (p.hz B) (Frame.ofGL 1) F → F.β r y = Witness.prH p m by
    choose M hM using H
    exact ⟨Matrix.of M, fun k _ _ _ _ p F h => Matrix.ext fun r y => hM r y k p F h⟩
  rintro r (a | j)
  · exact ⟨J.d.i₀ r a, fun k _ _ _ _ p F h => by rw [h.2.1]; simp [Frame.ofGL]; rfl⟩
  · by_cases hc : c = 2 * ρ
    swap
    · exact ⟨0, fun k _ _ _ _ p F h => absurd h.1 hc⟩
    have := j.2
    rcases lt_or_ge j.val ρ with hj | hj
    · exact ⟨D.host.xi0 ^ n * D.host.xi0 ^ (ρ - j.val) * J.d.e r ⟨j, hj⟩, fun k _ _ _ _ p F h => by
        rw [h.2.2.1 ⟨j, hj⟩ j rfl]; simp only [map_mul, map_pow]; rfl⟩
    · exact ⟨D.host.xi0 ^ n * ((star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) / D.host.xi0) * (-1 / D.host.xi0) ^ (ρ - 1 - (2 * ρ - 1 - j.val)) *
        J.d.e' r ⟨2 * ρ - 1 - j.val, by omega⟩, fun k _ _ _ _ p F h => by
        rw [h.2.2.2 ⟨2 * ρ - 1 - j.val, by omega⟩ j (by simp only; omega)]
        simp only [map_mul, map_pow, map_div₀, map_neg, map_one]; rfl⟩

end Rat

variable {D : D7} {c : Comm D} {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle}

theorem idx_ne_zero (Q : QAt v χ) (j : ℕ) (h : j ≤ D.R.m) : Q.idx j ≠ 0 := by
  have key : ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (J : Subgroup (GL Y Q.k)), IsOpen (J : Set (GL Y Q.k)) →
      J.relIndex (KO Q.k Y) ≠ 0 := fun Y _ _ J hO => by
    have hc : CompactSpace (KO Q.k Y) := isCompact_iff_compactSpace.1 SplitFlip.isCompact_KO
    have ho : IsOpen ((J.subgroupOf (KO Q.k Y) : Subgroup _) : Set (KO Q.k Y)) := hO.preimage continuous_subtype_val
    have := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.index_ne_zero_of_finite
  have := Q.hs
  by_cases e : j = Q.s + 1 + 1
  · rw [e, Q.idx_top]; exact key _ _ Q.openT
  · rw [Q.idx_mid j (Q.s + 1 - j) (by omega)]; exact key _ _ (Q.reg.2.2 _ _ _).1

theorem wt_ne_zero (Q : QAt v χ) : (∀ y, Q.wt (Q.s + 1) y ≠ 0) ∧ ∀ u, Q.wt (Q.s + 1 + 1) u ≠ 0 := by
  have := Q.hs
  refine ⟨fun y => ?_, fun u => ?_⟩
  · rw [Q.wt_pen]
    exact mul_ne_zero (Nat.cast_ne_zero.2 (idx_ne_zero Q _ (by omega)))
      (Nat.cast_ne_zero.2 (card_orb_ne_zero (Q.le _ _ _) (Q.reg.2.2 _ _ _).2.1 _ _))
  · rw [Q.wt_top]; exact Nat.cast_ne_zero.2 (idx_ne_zero Q _ (by omega))

theorem pin_ne_zero {t : Tup c} {w : VTup t} (h : QPin v w) :
    (∀ j, j + 2 ≤ D.R.m → w.cQ j ≠ 0) ∧ ∀ n hn β, w.εT n hn β ≠ 0 := by
  obtain ⟨F, h⟩ := h
  refine ⟨fun j hj => ?_, fun n hn β => ?_⟩
  · rw [h.cQ j hj]
    exact Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 (idx_ne_zero _ _ (by omega)))
      (Nat.cast_ne_zero.2 (idx_ne_zero _ _ (by omega))))
  · rw [h.εT n hn β, Finsupp.single_ne_zero]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    generalize F.eqv n β i = u
    obtain rfl : n = (F.Q i).s + 1 + 1 := hn.trans (F.Q i).hs.symm
    exact (wt_ne_zero _).2 u

def IsSphAt (Q : QAt v χ) : Prop :=
  (∀ j d h, Q.T.Phi j d h = ind Q.k _ _) ∧ Q.T.PhiTop = ind Q.k _ _ ∧ (∀ j, Nonempty (Unique (Q.Ch j))) ∧ (∀ j, Q.idx j = 1) ∧
    (∀ j α, Q.wt j α = 1) ∧ (∀ j, Q.eL j = Finsupp.single 0 1) ∧ Q.eLT = Finsupp.single 0 1 ∧
    (∀ j α γ, Q.dL j α γ = Finsupp.single 0 1) ∧ (∀ j α, Q.εL j α = Finsupp.single 1 1) ∧ ∀ j, Q.Typed j fun _ => 1

section Rel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_last (p : Place D k) {X T L : HSp D} (o : OrthDec X T L) (hL : L.rank = 1) {Z : Type} [Fintype Z] [DecidableEq Z]
    (FT : Frame k T.rank Z) {a : k} (ha : a ≠ 0) : ∃ FM : Frame k X.rank (Z ⊕ Unit),
      FM.β = fromCols (o.iA.map p.pr * FT.β) (Matrix.of fun r _ => (o.iB.map p.pr *ᵥ fun _ => a) r) := by
  have hs' := congrArg (fun M => Matrix.map M (Witness.prH p)) o.iA_qA_add
  simp only [Matrix.map_add _ (map_add (Witness.prH p)), Matrix.map_one _ (map_zero (Witness.prH p)) (map_one (Witness.prH p))] at hs'
  rw [Matrix.map_mul, Matrix.map_mul] at hs'
  let ζ : Matrix (Fin L.rank) Unit k := Matrix.of fun _ _ => a
  let η : Matrix Unit (Fin L.rank) k := Matrix.of fun _ _ => a⁻¹
  have h1 : η * ζ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Subsingleton.elim i j, Matrix.one_apply_eq]
    simp [η, ζ, hL, ha]
  have h2 : ζ * η = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hL])).1 h1
  refine ⟨Witness.mkFrame (fromCols (o.iA.map (Witness.prH p) * FT.β) (o.iB.map (Witness.prH p) * ζ))
    (fromRows (FT.γ * o.qA.map (Witness.prH p)) (η * o.qB.map (Witness.prH p))) ?_ ?_, rfl⟩
  · rw [fromCols_mul_fromRows, Matrix.mul_assoc, ← Matrix.mul_assoc FT.β, FT.βγ, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc ζ, h2, Matrix.one_mul, hs']
  · simp [← Witness.card_frame FT, ← o.rank_add, hL]

def Spans (q : GlobalTheory.FinPl.SplitPt D k) {S : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y)
    (L : GlobalTheory.FinPl.Lat S) : Prop :=
  ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)

set_option maxHeartbeats 2000000 in

theorem exists_qAt (v : VCom c) (χ : ℕ → (AE D)ˣ →* Circle) (q : GlobalTheory.FinPl.SplitPt D k) (unit : q.UnitAA) {ψk : AddChar k Circle}
    (hk : (ofSplit q).IsChar c.ψ ψk) (hc : HasConductor ψk 1) (μ : ℕ → kˣ →* ℂˣ)
    (hμ : ∀ j, j < D.R.m → (ofSplit q).IsComp (χ j)⁻¹ (μ (j + 1)) ∧ IsUnram (μ (j + 1))) (hL : c.Lz.rank = 1)
    (hτ : ∀ j h, v.τ j h ≠ 0)
    (lB : ∀ j ρ h (F : GlobalTheory.LocMod.Frame k (c.V j).rank (Fin (c.X j).rank ⊕ Fin (2 * ρ + 1))),
      (ofSplit q).IsBesFrame (c.B j ρ h) ((ofSplit q).xi ^ (j / 2)) (Frame.ofGL 1) F → Spans q F (v.N j))
    (lJ : ∀ j ρ h (F : GlobalTheory.LocMod.Frame k (c.V (j + 1)).rank (Fin (c.X (j + 1)).rank ⊕ Fin (2 * ρ))),
      (ofSplit q).IsJacFrame (c.J j ρ h) ((ofSplit q).xi ^ (j / 2)) ((ofSplit q).hz (c.B j ρ h)) (Frame.ofGL 1) F →
        Spans q F (v.N (j + 1)))
    (latT : Spans q (Frame.ofGL 1) v.NT) : ∃ Q : QAt v χ, Q.q.v = q.v ∧ IsSphAt Q := by
  borelize k
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isUnitVol (k := k)
  haveI := hν.1
  obtain ⟨s, hs⟩ : ∃ s, s + 1 + 1 = D.R.m := ⟨D.R.m - 2, by have := D.R.two_le_m; omega⟩
  have hev : s % 2 = 0 := by have := Nat.even_iff.1 D.R.m_even; omega
  set p := ofSplit q with hp
  have hx : p.xi ≠ 0 := Witness.xi_ne p
  let sc : ℕ → k := fun j => p.xi ^ (j / 2)
  have sc0 : ∀ j, sc j ≠ 0 := fun j => pow_ne_zero _ hx
  let X : ℕ → Type := fun j => Fin (c.X j).rank
  let FX : ∀ j, j ≤ s + 1 → GlobalTheory.LocMod.Frame k (c.X j).rank (X j) := fun _ _ => Frame.ofGL 1
  let FT : GlobalTheory.LocMod.Frame k c.T.rank (Fin c.T.rank) := Frame.ofGL 1
  let Q : ∀ j a, j + a = s + 1 → GlobalTheory.LocMod.Frame k (c.V j).rank (X j ⊕ Fin a) → Prop := fun j =>
    match j with
    | 0 => fun _ _ _ => True
    | j + 1 => fun a ha F => ∀ ρ h, p.IsJacFrame (c.J j ρ h) (sc j) (p.hz (c.B j ρ h)) (FX (j + 1) (by omega)) F
  have hFY : ∀ j a (ha : j + a = s + 1), ∃ F : GlobalTheory.LocMod.Frame k (c.V j).rank (X j ⊕ Fin a),
      (∀ ρ h, p.IsBesFrame (c.B j ρ h) (sc j) (FX j (by omega)) F) ∧ Q j a ha F ∧ Spans q F (v.N j) := by
    intro j a ha
    by_cases hj : j % 2 = 0
    · obtain ⟨ρ, rfl⟩ : ∃ ρ, a = 2 * ρ + 1 := ⟨a / 2, by omega⟩
      have h : j + 2 * ρ + 2 = D.R.m := by omega
      obtain ⟨F, hF⟩ := Witness.exists_bes p (c.B j ρ h) (sc0 j) (FX j (by omega))
      refine ⟨F, fun ρ' h' => ?_, ?_, lB j ρ h F hF⟩
      · obtain rfl : ρ' = ρ := by omega
        exact hF
      · cases j with
        | zero => trivial
        | succ j => intro ρ' h'; omega
    · obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      obtain ⟨ρ, rfl⟩ : ∃ ρ, a = 2 * ρ := ⟨a / 2, by omega⟩
      have h : j + 2 * ρ + 2 = D.R.m := by omega
      obtain ⟨F, hF⟩ := Witness.exists_jac p (c.J j ρ h) (sc0 j) (Witness.hz_ne p (c.B j ρ h)) (FX (j + 1) (by omega))
      refine ⟨F, fun ρ' h' => by omega, fun ρ' h' => ?_, lJ j ρ h F hF⟩
      obtain rfl : ρ' = ρ := by omega
      exact hF
  choose FY hB hJ latY using hFY
  have h0 : s + 2 * 0 + 2 = D.R.m := hs
  have l1 := (c.bes s 0 h0).line.1
  haveI : Subsingleton (Fin (c.bes s 0 h0).L.rank) := by rw [l1]; infer_instance
  haveI : Subsingleton (Fin c.Lz.rank) := by rw [hL]; infer_instance
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, v.τ s h0 i j ≠ 0 := by
    by_contra H; push Not at H; exact hτ s h0 (Matrix.ext H)
  have hζ : (c.bes s 0 h0).ζ i₀ ≠ 0 := fun e => (c.bes s 0 h0).line.2 (by
    rw [show (c.bes s 0 h0).ζ = 0 from funext fun i => by rw [Subsingleton.elim i i₀]; exact e]; simp)
  have t0 : p.pr (v.τ s h0 i₀ j₀) ≠ 0 := (map_ne_zero (Witness.prH p)).2 hij
  have z0 : p.pr ((c.bes s 0 h0).ζ i₀) ≠ 0 := (map_ne_zero (Witness.prH p)).2 hζ
  let a : k := -(p.xi * sc s) * p.pr ((c.bes s 0 h0).ζ i₀) / p.pr (v.τ s h0 i₀ j₀)
  have ha : a ≠ 0 := div_ne_zero (mul_ne_zero (neg_ne_zero.2 (mul_ne_zero hx (sc0 s))) z0) t0
  obtain ⟨FM, last⟩ := exists_last p (c.oT (s + 1 + 1) hs) hL FT ha
  choose gl gl_loc using fun j d hd => exists_gl q _ (FY j d hd)
  choose m m1 m2 using fun j => exists_haar ν (X j)
  refine ⟨
    { k := k, ν := ν, unitVol := hν, q := q, unit := unit, ψk := ψk, char := hk, cond := hc, s := s, hs := hs, X := X, Z := Fin c.T.rank
      T := sphChain X _ s μ, reg := sph_reg _ _ _
      laws := ⟨fun j d h => hasTypes_ind (hμ j (by omega)).2, hasTypes_ind (hμ (s + 1) (by omega)).2⟩
      bas := fun _ _ _ => rfl, le := fun _ _ _ => le_rfl, leT := le_rfl, openT := SplitFlip.isOpen_KO
      mu := fun j hj => ⟨(hμ j (by omega)).1, isOpen_ker (hμ j (by omega)).2⟩
      FX := FX, FT := FT, FM := FM, FY := FY, sc := sc, sc_ne := sc0
      sc_step := fun j => by simp only [sc]; rw [show (j + 1 + 1) / 2 = j / 2 + 1 by omega, pow_succ]
      bes := fun j ρ h a ha => hB j a ha ρ h, jac := fun j ρ h a ha => hJ (j + 1) a ha ρ h
      z₀ := fun _ => a, last := last
      tau := fun h => by
        funext i
        rw [Subsingleton.elim i i₀]
        change ∑ j, p.pr (v.τ s h0 i₀ j) * a = -(p.xi * sc s) * p.pr ((c.bes s 0 h0).ζ i₀)
        rw [Fintype.sum_subsingleton _ j₀, mul_div_cancel₀ _ t0]
      latY := latY, latT := latT, gl := gl, gl_loc := gl_loc
      A := fun _ _ _ => {1}, reps := sph_reps _ _ hc hν μ, Ch := fun _ => Unit, rep := fun _ _ _ _ => 1
      rep_bij := fun _ _ _ => ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ h => ⟨(), trivial, h.symm⟩⟩
      c₁ := 1, c₂ := 1, adapt := sph_adapt _ _ μ, cos := fun _ => Submodule.Quotient.mk 0
      cos_inj := fun _ _ _ => rfl
      cos_cov := by
        rintro _ ⟨y, hy, rfl, -⟩
        refine ⟨(), ?_⟩
        rw [show Submodule.Quotient.mk y = Submodule.Quotient.mk (p := box (X (s + 1)) (1 : kˣ)) 0 from
          (Submodule.Quotient.eq _).2 (by rwa [sub_zero])]
        exact (sameOrb_equiv le_rfl 1).1 _
      one := rfl
      eL := fun _ => Finsupp.single 0 1, eLT := Finsupp.single 0 1
      eL_at := fun _ _ _ => PinModel.isCombAt_one _ _ _ _, eLT_at := PinModel.isCombAt_one _ _ _ _
      dL := fun _ _ _ => Finsupp.single 0 1
      dL_mid := fun j d H _ _ => (congrArg _ (xi_ind (c := d) hc hν (μ (j + 1)))).mpr (PinModel.isCombAt_one _ _ _ _)
      dL_pen := fun _ _ => (congrArg _ (sph_pen X _ μ)).mpr (PinModel.isCombAt_one _ _ _ _)
      dL_top := fun _ _ => (congrArg _ (sph_top X _ hc hν μ)).mpr (PinModel.isCombAt_one _ _ _ _)
      εL := fun _ _ => Finsupp.single 1 1
      εL_at := fun j ρ h d hd _ => ⟨_, isOneComb_sph hc hν (by omega) (by omega), by rw [Finsupp.mapDomain_single, map_one]⟩
      idx := fun _ => 1
      idx_mid := fun _ _ _ => (Subgroup.relIndex_self _).symm, idx_top := (Subgroup.relIndex_self _).symm
      m := m, haar := fun j => ⟨m1 j, m2 j⟩, wt := fun _ _ => 1
      wt_mid := fun j d h _ => by
        rw [show prX (Cgrp ((sphChain X (Fin c.T.rank) s μ).lev j (d + 1) (by omega)).J 1) = KO k (X j) from prX_KO, m2]; simp
      wt_pen := fun _ => by
        rw [show {yb | SameOrb ((sphChain X (Fin c.T.rank) s μ).lev (s + 1) 0 rfl).J (box _ 1) (Submodule.Quotient.mk 0) yb} = _
          from orb_zero le_rfl 1]; simp
      wt_top := fun _ => by simp }, rfl,
    fun _ _ _ => rfl, rfl, fun _ => ⟨(inferInstance : Unique Unit)⟩, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl,
    fun _ _ _ => rfl, fun _ _ => rfl, fun j d h x => (one_smul ℂ (fun _ => (1 : ℂ))).symm⟩

end Rel

theorem qpin_of_sph (Q : QAt v χ) (hQ : IsSphAt Q) {t : Tup c} [∀ j, Unique (t.Ch j)] (w : VTup t)
    (kom : ∀ j, j < D.R.m → IsWeilDatumO c.ψ _ _ (χ j) (χ j) (t.kom j))
    (mid : ∀ j σ h, ∃ χz : (AE D)ˣ →* Circle, (t.sBF j (σ + 1) h).χV = χ j * χz ∧ (t.sBF j (σ + 1) h).χW = χ j ∧
      (t.sFB j σ h).χV = χ (j + 1) ∧ (t.sFB j σ h).χW = χ (j + 1) * χz)
    (lastc : ∀ j h, (t.sBF j 0 h).χW = χ j) :
    QPin v { w with
      Q := {Q.q.v}, eQ := fun _ => Finsupp.single 0 1, eQT := fun _ _ => Finsupp.single 0 1, dQ := fun _ _ _ => Finsupp.single 0 1
      ε := fun _ _ => Finsupp.single 1 1, εT := fun _ _ _ => Finsupp.single 1 1, FY := fun _ => {fun _ => 1}, cQ := fun _ => 1 } := by
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hQ
  have := fun j => (h3 j).some
  refine ⟨⟨χ, 1, fun _ => Q, fun j => Equiv.ofUnique _ _⟩, fun _ _ _ => Subsingleton.elim _ _, fun p => by simp [eq_comm], kom, mid, lastc,
    fun j _ => by simp [aconv, h6, -Finsupp.single_mul], fun j h => ?_, fun j _ α γ => by simp [aconv, h5, h8, -Finsupp.single_mul], fun j ρ _ α => by simp [conv, h5, h9, -Finsupp.single_mul],
    fun n _ β => by simp [h5], fun j _ f hf _ => by obtain rfl : f = _ := hf; exact h10 j, fun j _ => by simp [h4]⟩
  obtain rfl : j = Q.s := by have := Q.hs; omega
  have : Q.eT Q.s h = Q.eLT := rfl
  simp [aconv, this, h7, -Finsupp.single_mul]

theorem sum_orbits (Q : QAt v χ) (f : ((Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂) → ℂ)
    (h1 : ∀ x y, SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) x y → f x = f y)
    (h2 : ∀ x, f x ≠ 0 → x ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)) :
    (Q.idx (Q.s + 1) : ℂ) * ∑ᶠ x, f x = ∑ y, Q.wt (Q.s + 1) y * f (Q.cos y) := by
  classical
  have E := sameOrb_equiv (Q.le (Q.s + 1) 0 rfl) Q.c₂
  have hf : ∀ y, {yb | SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb}.Finite := fun y =>
    Set.finite_coe_iff.1 (Nat.finite_of_card_ne_zero (card_orb_ne_zero (Q.le _ _ _) (Q.reg.2.2 _ _ _).2.1 _ (Q.cos y)))
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.biUnion fun y => (hf y).toFinset) f fun x hx => by
    obtain ⟨y, hy⟩ := Q.cos_cov x (h2 x hx)
    simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.Finite.coe_toFinset, Set.mem_iUnion]
    exact ⟨y, hy⟩]
  rw [Finset.sum_biUnion fun y _ y' _ hne => Finset.disjoint_left.2 fun x hx hx' =>
    hne (Q.cos_inj y y' (E.trans ((hf y).mem_toFinset.1 hx) (E.symm ((hf y').mem_toFinset.1 hx')))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_congr rfl fun x hx => (h1 _ _ ((hf y).mem_toFinset.1 hx)).symm, Finset.sum_const, Q.wt_pen, nsmul_eq_mul,
    Nat.card_eq_card_finite_toFinset (hf y), mul_assoc]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem infinite_qAt (hψ : IsStdChar D c.ψ (-1)) (v : VCom c) (χ : ℕ → (AE D)ˣ →* Circle) (hχ : ∀ j, j < D.R.m → Continuous (χ j))
    (hL : c.Lz.rank = 1) (hτ : ∀ j h, v.τ j h ≠ 0) (hN : ∀ j, j < D.R.m → Submodule.IsLattice D.host.E (v.N j))
    (hT : Submodule.IsLattice D.host.E v.NT) : {x | ∃ Q : QAt v χ, Q.q.v = x ∧ IsSphAt Q}.Infinite := by
  have hu := (Filter.eventually_all_finite (Set.finite_lt_nat D.R.m)).2 fun j hj => DblInhab.eventually_isUnram D (χ j)⁻¹ (hχ j hj).inv
  choose MB hMB using fun j ρ h => rat_bes (c.B j ρ h) (j / 2) (2 * ρ + 1)
  choose MJ hMJ using fun j ρ h => rat_jac (c.B j ρ h) (c.J j ρ h) (j / 2) (2 * ρ)
  haveI : Finite {x : ℕ × ℕ // x.1 + 2 * x.2 + 2 = D.R.m} :=
    ((Set.finite_lt_nat D.R.m).prod (Set.finite_lt_nat D.R.m)).subset fun x (hx : x.1 + 2 * x.2 + 2 = D.R.m) =>
      ⟨show x.1 < _ by omega, show x.2 < _ by omega⟩
  have hB := Filter.eventually_all.2 fun x : {x : ℕ × ℕ // x.1 + 2 * x.2 + 2 = D.R.m} =>
    ae_frame (c.V x.1.1) (v.N x.1.1) (hN _ (by have := x.2; omega)) (MB _ _ x.2)
  have hJ := Filter.eventually_all.2 fun x : {x : ℕ × ℕ // x.1 + 2 * x.2 + 2 = D.R.m} =>
    ae_frame (c.V (x.1.1 + 1)) (v.N (x.1.1 + 1)) (hN _ (by have := x.2; omega)) (MJ _ _ x.2)
  have hev := (GlobalTheory.T.standard_character_conductor_almost_all D c.ψ hψ).and ((GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0).and
    ((GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0⁻¹).and ((GlobalTheory.FinPl.AlmostAll.latA_eq_latV D).and
      (hu.and (hB.and (hJ.and (ae_frame c.T v.NT hT (1 : Matrix _ (Fin c.T.rank) _))))))))
  refine Filter.frequently_cofinite_iff_infinite.1
    (((Filter.frequently_cofinite_iff_infinite.2 (GlobalTheory.T.infinitely_many_split_places D)).and_eventually hev).mono ?_)
  rintro x ⟨⟨e, ε, he, hε, hs⟩, a1, a2, a3, a4, a5, a6, a7, a8⟩
  obtain ⟨q, -, hq⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D x e ε he hε hs
  obtain ⟨⟨ψk, hk⟩, -, -, -, hc⟩ := GlobalTheory.LocChar.weil_char_split D _ (ofSplit q) c.ψ hψ
  choose μ hμ using fun j => hc (χ j)⁻¹
  have := exists_qAt v χ q (by unfold GlobalTheory.FinPl.SplitPt.UnitAA; rw [hq]; exact ⟨fun a ha => ⟨a2 a ha, a3 a ha⟩, a4⟩) hk
    (DblInhab.hasConductor q (by rw [hq]; exact a1) (by rw [hq]; exact a2) (by rw [hq]; exact a3) hk) (fun j => μ (j - 1))
    (fun j hj => ⟨hμ j, a5 j hj _ q hq _ (hμ j)⟩) hL hτ
    (fun j ρ h F hF => a6 ⟨(j, ρ), h⟩ _ q hq F (hMB j ρ h _ _ F hF)) (fun j ρ h F hF => a7 ⟨(j, ρ), h⟩ _ q hq F (hMJ j ρ h _ _ F hF))
    (a8 _ q hq _ (Matrix.map_one _ (map_zero (Witness.prH (ofSplit q))) (map_one (Witness.prH (ofSplit q)))).symm)
  rwa [hq] at this

theorem infinite_qAt_of_is (hc : c.Is) (hv : v.Is) {t : Tup c} (hW : WeilOK (t := t) v) (χ : ℕ → (AE D)ˣ →* Circle)
    (hχ : ∀ j, j < D.R.m → Continuous (χ j)) : {x | ∃ Q : QAt v χ, Q.q.v = x ∧ IsSphAt Q}.Infinite := by
  have h0 : D.R.m - 2 + 2 * 0 + 2 = D.R.m := by have := D.R.two_le_m; omega
  refine infinite_qAt hc.std v χ hχ (hW.tau _ h0).1 (fun j h e => ?_) (fun j hj => (hv.sd j hj).1) hv.sdT.1
  obtain ⟨h1, h2⟩ := hW.tau j h
  have hx := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  rw [e, Matrix.mul_zero, Matrix.mul_zero, eq_comm, smul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact mul_ne_zero hx (star_ne_zero.2 hx) (neg_eq_zero.1 h2)
  · have hg := gram_det_ne c.Lz
    haveI : Nonempty (Fin c.Lz.rank) := by rw [h1]; infer_instance
    rw [h2, det_zero] at hg
    exact hg rfl

theorem infinite_qpin (hc : c.Is) (hv : v.Is) {t : Tup c} (hW : WeilOK (t := t) v) [∀ j, Unique (t.Ch j)] (w : VTup t)
    (kom : ∀ j, j < D.R.m → IsWeilDatumO c.ψ _ _ (χ j) (χ j) (t.kom j))
    (mid : ∀ j σ h, ∃ χz : (AE D)ˣ →* Circle, (t.sBF j (σ + 1) h).χV = χ j * χz ∧ (t.sBF j (σ + 1) h).χW = χ j ∧
      (t.sFB j σ h).χV = χ (j + 1) ∧ (t.sFB j σ h).χW = χ (j + 1) * χz)
    (lastc : ∀ j h, (t.sBF j 0 h).χW = χ j) :
    {x | ∃ w' : VTup t, QPin v w' ∧ w'.Q = {x} ∧ (∀ j, w'.cQ j = 1) ∧ ∀ j, ∃ f ∈ w'.FY j, f ≠ 0}.Infinite :=
  (infinite_qAt_of_is hc hv hW χ fun j hj => (kom j hj).hecS.1).mono (by
    rintro _ ⟨Q, rfl, hQ⟩
    exact ⟨_, qpin_of_sph Q hQ w kom mid lastc, rfl, fun _ => rfl, fun _ => ⟨_, rfl, fun h => one_ne_zero (congrFun h 1)⟩⟩)

theorem exists_tup (hψ : IsStdChar D c.ψ (-1)) (t₀ : Tup c) (hp : ∀ j, j ≤ D.R.m → (c.X j).rank % 2 = (c.X 0).rank % 2) :
    ∃ (χ : ℕ → (AE D)ˣ →* Circle) (t : Tup c), (∀ j, Continuous (χ j)) ∧ (∀ j, Nonempty (Unique (t.Ch j))) ∧
      (∀ j, j < D.R.m → IsWeilDatumO c.ψ _ _ (χ j) (χ j) (t.kom j)) ∧
      (∀ j σ h, ∃ χz : (AE D)ˣ →* Circle, (t.sBF j (σ + 1) h).χV = χ j * χz ∧ (t.sBF j (σ + 1) h).χW = χ j ∧
        (t.sFB j σ h).χV = χ (j + 1) ∧ (t.sFB j σ h).χW = χ (j + 1) * χz) ∧ ∀ j h, (t.sBF j 0 h).χW = χ j := by
  obtain ⟨χ, a1, a2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D (c.X 0).rank
  obtain ⟨η, b1, b2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D 1
  have c1 : IsHeckeChar D (χ * η) := ⟨a1.1.mul b1.1, fun x => by rw [MonoidHom.mul_apply, a1.2, b1.2, mul_one]⟩
  have c2 := resEta_mul a2 b2
  have hk : ∀ j, ∃ o : Om (c.X j) (c.X (j + 1)), j < D.R.m → IsWeilDatumO c.ψ _ _ χ χ o := fun j => by
    by_cases hj : j < D.R.m
    · have := hp j (by omega)
      have := hp (j + 1) (by omega)
      obtain ⟨o, w⟩ := Inhab.exists_weil hψ (c.X j) (c.X (j + 1)) a1 a1 (resEta_parity a2 (by omega)) (resEta_parity a2 (by omega))
      exact ⟨o, fun _ => w⟩
    · exact ⟨t₀.kom j, fun h => absurd h hj⟩
  have hB : ∀ j ρ h, ∃ s : StepBF c.ψ (c.B j ρ h) (c.J j ρ h), s.χV = χ * η ∧ s.χW = χ := fun j ρ h => by
    have := hp j (by omega)
    have := hp (j + 1) (by omega)
    have r1 := (c.bes j ρ h).o.rank_add
    have r2 := (c.bes j ρ h).line.1
    have p1 := Inhab.even_im_hermitian_sub (c.bes j ρ h).d
    have p2 := Inhab.even_im_hermitian_sub (c.jac j ρ h).d
    obtain ⟨o₁, w₁⟩ := Inhab.exists_weil hψ (c.V j) (c.V (j + 1)) c1 a1 (resEta_parity c2 (by omega)) (resEta_parity a2 (by omega))
    obtain ⟨o₁', w₁'⟩ := Inhab.exists_weil hψ (c.bes j ρ h).V₀ (c.X (j + 1)) c1 a1 (resEta_parity c2 (by omega))
      (resEta_parity a2 (by omega))
    exact ⟨⟨_, _, o₁, o₁', w₁, w₁', (Inhab.nonempty_vol _).some, (Inhab.nonempty_volM _ _ _).some,
      (Inhab.nonempty_volM _ _ _).some, (Inhab.nonempty_volU _ _).some⟩, rfl, rfl⟩
  have hF : ∀ j σ h, ∃ s : StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)), s.χV = χ ∧ s.χW = χ * η := fun j σ h => by
    have := hp (j + 1) (by omega)
    have := hp (j + 1 + 1) (by omega)
    have r1 := (c.bes (j + 1 + 1) σ (idx_step h)).o.rank_add
    have r2 := (c.bes (j + 1 + 1) σ (idx_step h)).line.1
    have p1 := Inhab.even_im_hermitian_sub (c.bes (j + 1 + 1) σ (idx_step h)).d
    have p2 := Inhab.even_im_hermitian_sub (c.jac j (σ + 1) h).d
    obtain ⟨o₁, w₁⟩ := Inhab.exists_weil hψ (c.V (j + 1)) (c.V (j + 1 + 1)) a1 c1 (resEta_parity a2 (by omega))
      (resEta_parity c2 (by omega))
    obtain ⟨o₁', w₁'⟩ := Inhab.exists_weil hψ (c.X (j + 1)) (c.bes (j + 1 + 1) σ (idx_step h)).V₀ a1 c1 (resEta_parity a2 (by omega))
      (resEta_parity c2 (by omega))
    exact ⟨⟨_, _, o₁, o₁', w₁, w₁', (Inhab.nonempty_vol _).some, (Inhab.nonempty_volM _ _ _).some,
      (Inhab.nonempty_volM _ _ _).some, (Inhab.nonempty_volU _ _).some⟩, rfl, rfl⟩
  choose kom hkom using hk
  choose sBF B1 B2 using hB
  choose sFB F1 F2 using hF
  exact ⟨fun _ => χ, { t₀ with
      kom := kom, sBF := sBF, sFB := sFB, Ch := fun _ => Unit, fin := fun _ => inferInstance, dd := fun _ _ _ => 0, e := fun _ _ => 0
      eT := fun _ _ _ => 0, rd := fun _ _ _ _ _ => 0 }, fun _ => a1.1, fun _ => ⟨(inferInstance : Unique Unit)⟩, hkom,
    fun j σ h => ⟨η, B1 _ _ _, B2 _ _ _, F1 _ _ _, F2 _ _ _⟩, fun j h => B2 _ _ _⟩

end GlobalTheory.QPl.PinTest
end
