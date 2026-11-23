import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralAndGoodOfIsSpherical
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubquotientPrinSeriesOfHasVec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterTriangular
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjEqOfNormalises
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeOneOfIsCuspidalMultiProd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceUnitaryLocEqTransposeInv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformiserConjTransposeInvMemUpperParahoric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNhdsOnePrincipalCongruenceSplitPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetEqOfColsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientUnramPrinSeriesOfHasSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientOfEquiv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ParaToral

open GlobalTheory.PsType (Triv ev theta grp nxt minor HasVec Ordered)

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem det_block_congr {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) {p q : Fin n → Prop} [DecidablePred p]
    [DecidablePred q] (h : ∀ i, p i ↔ q i) : (M.toSquareBlockProp p).det = (M.toSquareBlockProp q).det := by
  obtain rfl : p = q := funext fun i => propext (h i)
  congr!

theorem mem_KO_iff {g : GL (Fin n) k} :
    g ∈ KO k (Fin n) ↔ (∀ i j, valuation k (g.val i j) ≤ 1) ∧ ∀ i j, valuation k ((g⁻¹).val i j) ≤ 1 :=
  GlobalTheory.HeckeScalarSph.mem_GLint_iff (O := 𝒪[k])

theorem ev_mul (χ η : kˣ →* ℂˣ) (x : k) : ev (χ * η) x = ev χ x * ev η x := by
  unfold ev; split_ifs <;> simp

theorem ev_one (x : k) : ev (1 : kˣ →* ℂˣ) x = 1 := by
  unfold ev; split_ifs <;> simp

theorem ev_unit (χ : kˣ →* ℂˣ) (d : kˣ) (hd : valuation k (d : k) = 1) : ev χ (d : k) = χ d := by
  unfold ev; rw [dif_pos hd]; simp

def fam (n m : ℕ) (α β : kˣ →* ℂˣ) : Fin n → kˣ →* ℂˣ := fun i => if (i : ℕ) < m then α * β else β

theorem prod_ev_ite (γ : kˣ →* ℂˣ) (h : GL (Fin n) k) (M : ℕ) (hM : M ≤ n) :
    ∏ j : Fin n, ev (if (j : ℕ) + 1 = M then γ else 1) (minor h j) =
      ev γ (h.val.toSquareBlockProp fun i => (i : ℕ) < M).det := by
  rcases M with _ | M
  · haveI : IsEmpty {i : Fin n // (i : ℕ) < 0} := ⟨fun i => absurd i.2 (Nat.not_lt_zero _)⟩
    rw [Matrix.det_isEmpty]
    have := ev_unit γ 1 (by simp)
    simp only [Units.val_one, map_one] at this
    simp [ev_one, this]
  · rw [Finset.prod_eq_single (⟨M, hM⟩ : Fin n)]
    · rw [if_pos rfl, minor]
      congr 1
      exact det_block_congr _ fun i => by rw [Fin.le_def]; simp only; omega
    · intro j _ hj
      rw [if_neg (fun e => hj (Fin.ext (by simpa using e))), ev_one]
    · simp

theorem theta_fam (m : ℕ) (α β : kˣ →* ℂˣ) (h : GL (Fin n) k) :
    theta (fam n m α β) h = ev α (h.val.toSquareBlockProp fun i => (i : ℕ) < m).det * ev β h.val.det := by
  have key : ∀ j : Fin n, fam n m α β j / nxt (fam n m α β) j =
      (if (j : ℕ) + 1 = min m n then α else 1) * (if (j : ℕ) + 1 = n then β else 1) := by
    intro j
    have hj := j.2
    unfold nxt fam
    simp only
    split_ifs <;> first | omega | simp
  unfold theta
  simp only [key, ev_mul, Finset.prod_mul_distrib]
  rw [prod_ev_ite α h _ (min_le_right _ _), prod_ev_ite β h n le_rfl]
  congr 2
  · exact det_block_congr _ fun i => by have := i.2; omega
  · rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun i : Fin n => (i : ℕ) < n) fun i => i.2)]
    rfl

theorem ordered_fam (m : ℕ) (α β : kˣ →* ℂˣ) : Ordered (fam n m α β) := by
  intro i a b j hia hab hbj x hx
  rw [Fin.le_def] at hia hab hbj
  by_cases h : (a : ℕ) < m ∧ m ≤ b
  · have e : fam n m α β a / fam n m α β b = fam n m α β i / fam n m α β j := by
      unfold fam
      rw [if_pos h.1, if_neg (by omega), if_pos (by omega), if_neg (by omega)]
    rwa [e]
  · have e : fam n m α β a = fam n m α β b := by
      unfold fam
      split_ifs <;> first | rfl | omega
    intro u _ _
    simp [e]

theorem smooth_of_hasVec {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V}
    (hπ : IsSmooth π) {ψ : Fin n → kˣ →* ℂˣ} (h : HasVec ψ π) (i : Fin n) : IsSmoothChar (ψ i) := by
  obtain ⟨v, hv0, hv⟩ := h
  let t : kˣ → Fin n → kˣ := fun x => Pi.mulSingle i x
  have htc : Continuous t := continuous_pi fun j => by
    by_cases e : j = i
    · subst e; simpa [t] using continuous_id'
    · simpa [t, e] using continuous_const
  have hc : Continuous fun x : kˣ => diagT k (Fin n) (t x) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · simp only [Function.comp_def, val_diagT]
      exact Continuous.matrix_diagonal (continuous_pi fun j => Units.continuous_val.comp ((continuous_apply j).comp htc))
    · simp only [← map_inv, val_diagT]
      exact Continuous.matrix_diagonal (continuous_pi fun j => Units.continuous_val.comp ((continuous_apply j).comp htc.inv))
  have h1 : {x : kˣ | valuation k (x : k) = 1} ∈ nhds (1 : kˣ) := by
    have : {x : k | valuation k x = 1} ∈ nhds (1 : k) := by
      refine IsValuativeTopology.mem_nhds_iff'.2 ⟨1, fun z hz => ?_⟩
      have := (valuation k).map_eq_of_sub_lt (x := 1) (y := z) (by simpa using hz)
      simpa using this
    exact Units.continuous_val.tendsto (1 : kˣ) (show _ ∈ nhds ((1 : kˣ) : k) from this)
  have h2 : {x : kˣ | π (diagT k (Fin n) (t x)) v = v} ∈ nhds (1 : kˣ) :=
    ((hπ v).preimage hc).mem_nhds (by simp [t])
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  filter_upwards [h1, h2] with x hx1 hx2
  have ht : ∀ j, valuation k (t x j : k) = 1 := fun j => by
    by_cases e : j = i
    · subst e; simpa [t] using hx1
    · simp [t, e]
  have hg : diagT k (Fin n) (t x) ∈ grp ψ := by
    refine ⟨iwahori_le_KO k _ (diagT_mem_iwahori ht), fun a b hab => ?_⟩
    rw [val_diagT, Matrix.diagonal_apply_ne _ hab.ne]
    intro u _ hu
    have : u = 1 := Units.ext (by simpa [sub_eq_zero] using hu)
    rw [this, map_one]
  have hth := GlobalTheory.PsType.theta_of_triangular k n ψ (diagT k (Fin n) (t x)) (t x) ht
    (fun a => by rw [val_diagT, Matrix.diagonal_apply_eq])
    (Or.inr fun a b hab => by rw [val_diagT, Matrix.diagonal_apply_ne _ hab.ne'])
  rw [Finset.prod_eq_single i (fun b _ hb => by simp [t, hb]) (by simp)] at hth
  rw [hv _ hg, hth] at hx2
  have : ((ψ i (t x i) : ℂ) - 1) • v = 0 := by rw [sub_smul, hx2, one_smul, sub_self]
  have h3 := (smul_eq_zero.1 this).resolve_right hv0
  show ψ i x = 1
  exact Units.ext (by simpa [t, sub_eq_zero] using h3)

theorem val_det_block {h : GL (Fin n) k} (hh : h ∈ KO k (Fin n)) (m : ℕ)
    (hm : ∀ a b : Fin n, (a : ℕ) < m → m ≤ (b : ℕ) → valuation k (h.val a b) < 1) :
    valuation k (h.val.toSquareBlockProp fun i => (i : ℕ) < m).det = 1 := by
  obtain ⟨g, rfl⟩ := hh
  let G := g.val.map (IsLocalRing.residue 𝒪[k])
  have hG : G.det ≠ 0 := by
    have := (Matrix.isUnits_det_units g).map (IsLocalRing.residue 𝒪[k])
    rw [RingHom.map_det] at this
    exact this.ne_zero
  rw [Matrix.twoBlockTriangular_det G fun i => ¬ (i : ℕ) < m] at hG
  · have h2 := (mul_ne_zero_iff.1 hG).2
    rw [det_block_congr (q := fun i => (i : ℕ) < m) _ fun i => not_not] at h2
    have e1 : (G.toSquareBlockProp fun i => (i : ℕ) < m).det =
        IsLocalRing.residue 𝒪[k] (g.val.toSquareBlockProp fun i => (i : ℕ) < m).det := by
      rw [RingHom.map_det]; rfl
    have e2 : ((GeneralLinearGroup.map (algebraMap 𝒪[k] k) g).val.toSquareBlockProp fun i => (i : ℕ) < m).det =
        algebraMap 𝒪[k] k (g.val.toSquareBlockProp fun i => (i : ℕ) < m).det := by
      rw [RingHom.map_det]; rfl
    rw [e1, IsLocalRing.residue_ne_zero_iff_isUnit] at h2
    rw [e2]
    exact (Valuation.integer.integers _).one_of_isUnit h2
  · intro a ha b hb
    have := hm a b (not_not.1 ha) (not_lt.1 hb)
    exact (IsLocalRing.residue_eq_zero_iff _).2
      ((IsLocalRing.mem_maximalIdeal _).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr this))

theorem inv_lower {h : GL (Fin n) k} (hh : h ∈ KO k (Fin n)) (m : ℕ)
    (hm : ∀ a b : Fin n, (a : ℕ) < m → m ≤ (b : ℕ) → valuation k (h.val a b) < 1) :
    ∀ a b : Fin n, (a : ℕ) < m → m ≤ (b : ℕ) → valuation k ((h⁻¹).val a b) < 1 := by
  obtain ⟨g, rfl⟩ := hh
  intro a b ha hb
  let G := GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g
  let β : Fin n → ℕ := fun i => if (i : ℕ) < m then 1 else 0
  have hG : G.val.BlockTriangular β := fun i j hij => by
    have hi : (i : ℕ) < m := by by_contra h0; simp [β, h0] at hij
    have hj : m ≤ (j : ℕ) := by by_contra h0; simp [β, hi, not_le.1 h0] at hij
    exact (IsLocalRing.residue_eq_zero_iff _).2
      ((IsLocalRing.mem_maximalIdeal _).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr (hm i j hi hj)))
  letI := G.invertible
  have h1 := Matrix.blockTriangular_inv_of_blockTriangular hG (i := a) (j := b) (by simp [β, ha, not_lt.2 hb])
  rw [← Matrix.coe_units_inv, ← map_inv] at h1
  rw [← map_inv]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
    ((IsLocalRing.mem_maximalIdeal _).1 ((IsLocalRing.residue_eq_zero_iff _).1 h1))

theorem toral_of_isSubquotient (σ : IrrRep (GL (Fin n) k)) (ω : Fin n → kˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i))
    (h : IsSubquotient σ.ρ (prinSeries ω)) : Toral (GlobalTheory.LocLanglands.cls σ) := by
  have H : IsCuspSupport σ.cl.rep.ρ (fun _ : Fin n => 1) fun a => detRep (Fin 1) (ω a) :=
    ⟨σ.cl.rep.irr, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hω a)⟩, _,
      ((GlobalTheory.JacStages.isSubquotient_of_equiv (equivRep σ).symm).trans h).trans
        (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ω)⟩
  refine ⟨_, hasSupport_of_isCuspSupport H, ?_⟩
  intro y hy
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  rfl

def rv (g : GL (Fin n) k) : GL (Fin n) k :=
  GlobalTheory.PermPrin.permGL (k := k) Fin.revPerm * g * (GlobalTheory.PermPrin.permGL (k := k) Fin.revPerm)⁻¹

theorem rv_apply (g : GL (Fin n) k) (i j : Fin n) : (rv g).val i j = g.val i.rev j.rev :=
  GlobalTheory.PermPrin.permGL_conj_apply _ g i j

theorem rv_mem_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : rv g ∈ KO k (Fin n) := by
  rw [mem_KO_iff] at hg ⊢
  have e : (rv g)⁻¹ = rv g⁻¹ := by unfold rv; group
  rw [e]
  exact ⟨fun i j => by rw [rv_apply]; exact hg.1 _ _, fun i j => by rw [rv_apply]; exact hg.2 _ _⟩

theorem exists_rv {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) {u : V} (hu : u ≠ 0) :
    ∃ u' : V, u' ≠ 0 ∧ ∀ (g : GL (Fin n) k) (c : ℂ), π (rv g) u = c • u → π g u' = c • u' := by
  set w : GL (Fin n) k := GlobalTheory.PermPrin.permGL (k := k) Fin.revPerm
  refine ⟨π w⁻¹ u, fun h0 => hu ?_, fun g c hg => ?_⟩
  · have := congrArg (π w) h0
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero, Module.End.one_apply] at this
  · rw [← map_smul, ← hg, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    show g * w⁻¹ = w⁻¹ * (w * g * w⁻¹)
    group

theorem val_lt_of_mem_iwahori {g : GL (Fin n) k} (hg : g ∈ iwahori k (Fin n)) (a b : Fin n) (hab : b < a) :
    valuation k (g.val a b) < 1 := by
  obtain ⟨x, hx, rfl⟩ := hg
  have := mem_parab_iff.1 hx a b () () hab
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
    ((IsLocalRing.mem_maximalIdeal _).1 ((IsLocalRing.residue_eq_zero_iff _).1 this))

theorem toral_of_lower (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (σ : IrrRep (GL (Fin n) k)) (m : ℕ)
    (α β : kˣ →* ℂˣ) (hαβ : Triv α 1 → Triv β 1) {u : σ.V} (hu0 : u ≠ 0)
    (hu : ∀ h ∈ KO k (Fin n), (∀ a b : Fin n, (a : ℕ) < m → m ≤ (b : ℕ) → valuation k (h.val a b) < 1) →
      ∀ d e : kˣ, (d : k) = (h.val.toSquareBlockProp fun i => (i : ℕ) < m).det → (e : k) = h.val.det →
        σ.ρ h u = ((α d : ℂ) * (β e : ℂ)) • u) :
    Toral (GlobalTheory.LocLanglands.cls σ) := by
  have hu' : ∀ h ∈ KO k (Fin n), (∀ a b : Fin n, (a : ℕ) < m → m ≤ (b : ℕ) → valuation k (h.val a b) < 1) →
      σ.ρ h u = theta (fam n m α β) h • u ∧ (Triv α 1 → theta (fam n m α β) h = 1) := by
    intro h hh hm
    have h1 := val_det_block hh m hm
    have h2 : valuation k h.val.det = 1 := by
      have := val_det_block hh n fun a b _ hb => absurd b.2 (not_lt.2 hb)
      rwa [← Matrix.det_submatrix_equiv_self
        (Equiv.subtypeUnivEquiv (p := fun i : Fin n => (i : ℕ) < n) fun i => i.2).symm] at this
    let d : kˣ := Units.mk0 (h.val.toSquareBlockProp fun i => (i : ℕ) < m).det fun h0 => by
      rw [h0, map_zero] at h1; exact zero_ne_one h1
    let e : kˣ := Units.mk0 h.val.det fun h0 => by rw [h0, map_zero] at h2; exact zero_ne_one h2
    have e1 : theta (fam n m α β) h = (α d : ℂ) * (β e : ℂ) := by
      rw [theta_fam, ← ev_unit α d h1, ← ev_unit β e h2]; rfl
    have hle : ∀ x : k, valuation k x = 1 → valuation k (x - 1) ≤ valuation k 1 := fun x hx => by
      rw [map_one]; exact Valuation.map_sub_le _ hx.le (by simp)
    refine ⟨by rw [e1]; exact hu h hh hm d e rfl rfl, fun hα => ?_⟩
    rw [e1, hα d h1 (hle _ h1), hαβ hα e h2 (hle _ h2)]
    simp
  by_cases hα : Triv α 1
  · obtain ⟨u', hu'0, hu'1⟩ := exists_rv σ.ρ hu0
    have hI : fixed σ.ρ (iwahori k (Fin n)) ≠ ⊥ := by
      refine (Submodule.ne_bot_iff _).2 ⟨u', fun g => ?_, hu'0⟩
      obtain ⟨h1, h2⟩ := hu' (rv g.1) (rv_mem_KO (iwahori_le_KO k _ g.2)) fun a b ha hb => by
        rw [rv_apply]
        exact val_lt_of_mem_iwahori g.2 _ _ (Fin.rev_lt_rev.2 (Fin.lt_def.2 (by omega)))
      rw [h2 hα] at h1
      simpa using hu'1 g.1 1 h1
    have hadm : IsAdmissible σ.ρ := (hBZ k).1 (Fin n) σ.V σ.ρ σ.smooth σ.irr
    obtain ⟨a, ha⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm σ.irr hI
    exact toral_of_isSubquotient σ _ (fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (a i))) ha
  · have hvec : HasVec (fam n m α β) σ.ρ := by
      refine ⟨u, hu0, fun h hh => (hu' h hh.1 fun a b ha hb => ?_).1⟩
      have h1 := hh.2 a b (Fin.lt_def.2 (by omega))
      have e : fam n m α β a / fam n m α β b = α := by
        unfold fam
        rw [if_pos ha, if_neg (by omega), mul_div_cancel_right]
      rw [e] at h1
      by_contra hlt
      exact hα fun x hx hx1 => h1 x hx (hx1.trans (by rw [map_one]; exact not_lt.1 hlt))
    obtain ⟨ω, hω, -, hsub⟩ := GlobalTheory.PsType.subquotient_prinSeries_of_hasVec hBZ k n _ σ.V σ.ρ σ.smooth σ.irr
      (smooth_of_hasVec σ.smooth hvec) (ordered_fam m α β) hvec
    exact toral_of_isSubquotient σ ω hω hsub

theorem toral_of_upper (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (σ : IrrRep (GL (Fin n) k)) (r : ℕ)
    (ξ : kˣ →* ℂˣ) {u : σ.V} (hu0 : u ≠ 0)
    (hu : ∀ h ∈ KO k (Fin n), (∀ a b : Fin n, r ≤ (a : ℕ) → (b : ℕ) < r → valuation k (h.val a b) < 1) →
      ∀ d : kˣ, (d : k) = (h.val.toSquareBlockProp fun i => r ≤ (i : ℕ)).det → σ.ρ h u = (ξ d : ℂ) • u) :
    Toral (GlobalTheory.LocLanglands.cls σ) := by
  obtain ⟨u', hu'0, hu'1⟩ := exists_rv σ.ρ hu0
  refine toral_of_lower hBZ σ (n - r) ξ 1 (fun _ _ _ _ => rfl) hu'0 fun h hh hm d e hd _ => ?_
  rw [MonoidHom.one_apply, Units.val_one, mul_one]
  refine hu'1 h _ (hu _ (rv_mem_KO hh) (fun a b ha hb => ?_) d ?_)
  · rw [rv_apply]
    have := a.2
    have := b.2
    exact hm _ _ (by rw [Fin.val_rev]; omega) (by rw [Fin.val_rev]; omega)
  · let E : {i : Fin n // r ≤ (i : ℕ)} ≃ {i : Fin n // (i : ℕ) < n - r} :=
      Fin.revPerm.subtypeEquiv fun i => by
        have := i.2
        rw [Fin.revPerm_apply, Fin.val_rev]; omega
    rw [hd, ← Matrix.det_submatrix_equiv_self E]
    congr 1
    ext i j
    exact (rv_apply h i.1 j.1).symm

theorem toral_of_lower_inv (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (σ : IrrRep (GL (Fin n) k)) (r : ℕ)
    (ξ : kˣ →* ℂˣ) {u : σ.V} (hu0 : u ≠ 0)
    (hu : ∀ h ∈ KO k (Fin n), (∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → valuation k (h.val a b) < 1) →
      ∀ d : kˣ, (d : k) = ((h⁻¹).val.toSquareBlockProp fun i => r ≤ (i : ℕ)).det → σ.ρ h u = (ξ d : ℂ) • u) :
    Toral (GlobalTheory.LocLanglands.cls σ) := by
  refine toral_of_lower hBZ σ r ξ ξ⁻¹ (fun h x hx hx1 => by simp [h x hx hx1]) hu0 fun h hh hm d e hd he => ?_
  have hJ := GlobalTheory.GramJacobi.jacobi_minor h.val (h⁻¹).val h.inv_mul fun i => (i : ℕ) < r
  rw [det_block_congr (q := fun i => r ≤ (i : ℕ)) _ (fun i => not_lt), ← hd, ← he] at hJ
  rw [hu h hh hm (d * e⁻¹) (by rw [Units.val_mul, ← hJ, Units.mul_inv_cancel_right])]
  simp

end Local

section Global

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem eq_or_eq_conj (s s₀ : SplitPlace L) (h : s.v = s₀.v) : s₀ = s ∨ s₀ = GlobalTheory.TypeTame.conjSP s := by
  obtain ⟨v, i⟩ := s
  obtain ⟨v₀, i₀⟩ := s₀
  obtain rfl : v = v₀ := h
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  set δ : L := y - IsCMField.complexConj L y with hδdef
  have hδ : IsCMField.complexConj L δ = -δ := by
    rw [hδdef, map_sub, IsCMField.complexConj_apply_apply]; ring
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hfix : ∀ x : L, IsCMField.complexConj L x = x → ∀ j j' : L →ₐ[maximalRealSubfield L]
      v.adicCompletion (maximalRealSubfield L), j x = j' x := fun x hx j j' =>
    (j.commutes ⟨x, (IsCMField.complexConj_eq_self_iff L _).1 hx⟩).trans
      (j'.commutes ⟨x, (IsCMField.complexConj_eq_self_iff L _).1 hx⟩).symm
  have hext : ∀ j j' : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L), j δ = j' δ → j = j' := by
    intro j j' hj
    ext1 x
    have e : x = (x + IsCMField.complexConj L x) / 2 + (x - IsCMField.complexConj L x) / (2 * δ) * δ := by
      field_simp; ring
    have h1 := hfix ((x + IsCMField.complexConj L x) / 2) (by
      rw [map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat, add_comm]) j j'
    have h2 := hfix ((x - IsCMField.complexConj L x) / (2 * δ)) (by
      rw [map_div₀, map_sub, IsCMField.complexConj_apply_apply, map_mul, map_ofNat, hδ]
      field_simp; ring) j j'
    rw [e, map_add, map_add, map_mul, map_mul, h1, h2, hj]
  have hsq : i₀ δ * i₀ δ = i δ * i δ := by
    rw [← map_mul, ← map_mul]
    exact hfix _ (by rw [map_mul, hδ]; ring) _ _
  rcases mul_self_eq_mul_self_iff.1 hsq with h | h
  · left; rw [hext i₀ i h]
  · right
    have : i₀ = (GlobalTheory.TypeTame.conjSP (⟨v, i⟩ : SplitPlace L)).i :=
      hext _ _ (by rw [GlobalTheory.TypeTame.conjSP_i, hδ, map_neg]; exact h)
    rw [this]

theorem exists_vec {n : ℕ} (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S)
    (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (hN : ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1)
    {f : GAf L n → a.W} (hf : f ∈ NG.isoTyp a.ρ S) (hfT : f ∈ NG.TypeSp a.ρ J χ) (hf0 : f ≠ 0) (s : SplitPlace L)
    (σ : IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hσ : IsLocS S s σ) :
    ∃ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, (∀ x, Valued.v (c x) = Valued.v x) ∧
      ∃ u : σ.V, u ≠ 0 ∧ ∀ h ∈ KO (s.w.adicCompletion L) (Fin n), ∃ κ : GAf L n, TrivOutside {s.v} κ ∧
        s.loc n κ = GeneralLinearGroup.map c.symm.toRingHom h ∧
        s.loc n κ ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring ∧
        ∀ hJ : κ ∈ J, σ.ρ h u = ((χ ⟨κ, hJ⟩ : ℂˣ) : ℂ) • u := by
  obtain ⟨c, T₀, hc, hci, -, -, -⟩ := id hσ
  have hv := GlobalTheory.SplitConjVal.valuation_eq s c hc hci
  obtain ⟨N, hN0, hN⟩ := hN
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.SplitCongNbhd.exists_nhds_one_cong L n s N hN0
  obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc L n s
  let K := J.comap e ⊓ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring
  let ε : K →* J := (e.comp K.subtype).codRestrict J fun g => g.2.1
  have hopen : IsOpen ((χ.comp ε).ker : Set K) := by
    apply Subgroup.isOpen_of_mem_nhds (g := 1)
    filter_upwards [continuous_subtype_val.tendsto (1 : K) hU] with g hg
    obtain ⟨_, h2⟩ := hN (e g.1) (hUN _ (he1 _) (by rw [he2]; exact hg))
    exact h2
  have hrt : ∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc n κ ∈ K,
      NG.rt L n κ f = (((χ.comp ε) ⟨s.loc n κ, h⟩ : ℂˣ) : ℂ) • f := by
    intro κ hκ h
    obtain ⟨h1, h2⟩ := hN (κ * (e (s.loc n κ))⁻¹) (hUN _
      (GlobalTheory.SatInd.CosetFin.trivOutside_mul hκ (GlobalTheory.SatInd.CosetFin.trivOutside_inv (he1 _)))
      (by rw [map_mul, map_inv, he2, mul_inv_cancel]; exact mem_of_mem_nhds hU))
    let x : J := ⟨_, h1⟩ * ε ⟨s.loc n κ, h⟩
    have hx : (x : GAf L n) = κ := inv_mul_cancel_right κ _
    have := hfT.2 x
    rw [hx, map_mul, h2, one_mul] at this
    exact this
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main L n a S hS s σ hσ c hc hci K (χ.comp ε) (fun g hg => hg.2) hopen f hf hf0 hrt
  refine ⟨c, hv, u, hu0, fun h hh => ?_⟩
  let g := GeneralLinearGroup.map c.symm.toRingHom h
  have key : ∀ y, valuation (s.w.adicCompletion L) y ≤ 1 → Valued.v (c.symm y) ≤ 1 := fun y hy => by
    rw [← hv, RingEquiv.apply_symm_apply]
    exact (GlobalTheory.BlockConj.valued_le_one_iff_w s y).1 hy
  have hg : g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    rw [mem_KO_iff] at hh
    rw [GlobalTheory.HeckeScalarSph.mem_GLint_iff]
    refine ⟨fun p q => key _ (hh.1 p q), fun p q => ?_⟩
    rw [← map_inv]
    exact key _ (hh.2 p q)
  refine ⟨e g, he1 g, he2 g, by rw [he2]; exact hg, fun hJ => ?_⟩
  have e1 : GeneralLinearGroup.map c.toRingHom g = h := Units.ext (Matrix.ext fun p q => c.apply_symm_apply _)
  have := hu g ⟨hJ, hg⟩
  rw [e1] at this
  exact this

end Global

theorem toral_of_levelPara : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → ∀ (s₀ : SplitPlace L) (r : ℕ) (ξ : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelPara J χ s₀ r ξ → ∀ f ∈ NG.isoTyp a.ρ S, f ∈ NG.TypeSp a.ρ J χ → f ≠ 0 → ∀ (s : SplitPlace L), s.v = s₀.v → ∀ (σ : IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → Toral (GlobalTheory.LocLanglands.cls σ) := by
  intro hBZ _ L _ _ _ n a S hS J χ hN s₀ r ξ hP f hf hfT hf0 s hs σ hσ
  obtain ⟨c, hv, u, hu0, hu⟩ := exists_vec a S hS J χ hN hf hfT hf0 s σ hσ
  have key : ∀ y, valuation (s.w.adicCompletion L) y < 1 → Valued.v (c.symm y) < 1 := fun y hy => by
    rw [← hv, RingEquiv.apply_symm_apply]
    exact (GlobalTheory.BlockConj.valued_lt_one_iff_w s y).1 hy
  rcases eq_or_eq_conj s s₀ hs with rfl | rfl
  · refine toral_of_upper hBZ σ r (ξ.comp (Units.map c.symm.toRingHom.toMonoidHom)) hu0 fun h hh hm d hd => ?_
    obtain ⟨κ, hκ, hl, hi, hκu⟩ := hu h hh
    have hJ : κ ∈ J := (hP.mem κ hκ).2 ⟨hi, fun p q hp hq => by rw [hl]; exact key _ (hm p q hp hq)⟩
    rw [hκu hJ, hP.chr κ hJ hκ (Units.map c.symm.toRingHom.toMonoidHom d) ?_]
    · rfl
    · show c.symm.toRingHom (d : _) = _
      rw [hd, hl, RingHom.map_det]
      rfl
  · refine toral_of_lower_inv hBZ σ r (ξ.comp (Units.map c.symm.toRingHom.toMonoidHom)) hu0 fun h hh hm d hd => ?_
    obtain ⟨κ, hκ, hl, hi, hκu⟩ := hu h hh
    have e1 := GlobalTheory.ConjLoc.loc_conjSP n s κ
    have e2 : (((GlobalTheory.TypeTame.conjSP s).loc n κ)⁻¹).val = (s.loc n κ).val.transpose := by
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [e1, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    have hlow : ∀ p q : Fin n, (p : ℕ) < r → r ≤ (q : ℕ) → valuation (s.w.adicCompletion L) ((h⁻¹).val p q) < 1 :=
      inv_lower hh r hm
    have e3 : ∀ p q, ((GlobalTheory.TypeTame.conjSP s).loc n κ).val p q = c.symm ((h⁻¹).val q p) := fun p q => by
      rw [e1, hl, ← map_inv]; rfl
    have hJ : κ ∈ J := by
      rw [GlobalTheory.HeckeScalarSph.mem_GLint_iff] at hi
      refine (hP.mem κ hκ).2 ⟨GlobalTheory.HeckeScalarSph.mem_GLint_iff.2 ⟨fun p q => ?_, fun p q => ?_⟩, fun p q hp hq => ?_⟩
      · rw [e1]; exact hi.2 q p
      · rw [e2]; exact hi.1 q p
      · rw [e3]; exact key _ (hlow q p hq hp)
    rw [hκu hJ, hP.chr κ hJ hκ (Units.map c.symm.toRingHom.toMonoidHom d) ?_]
    · rfl
    · show c.symm.toRingHom (d : _) = _
      rw [hd, RingHom.map_det, NG.detDD, ← Matrix.det_transpose]
      congr 1
      exact Matrix.ext fun p q => (e3 p.1 q.1).symm

end GlobalTheory.ParaToral
