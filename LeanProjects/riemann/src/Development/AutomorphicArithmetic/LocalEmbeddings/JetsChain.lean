import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqFinClSumAvg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtTransInvHolds

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel IsDefiniteSpace)
open scoped ComplexOrder Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.JetsOne

variable {D : D7}

theorem finG_finOf (V : HSp D) (g : GA D V) : finG V (finOf V g) = Lev.finE V g := by
  have h : Lev.finE V (infOf V g : GA D V) = 1 := by
    show Formalism.UG.bc (Lev.swapAE D) (finHom V (infOf V g : GA D V)) = 1
    rw [show finHom V (infOf V g : GA D V) = 1 from (infOf V g).2, map_one]
  conv_rhs => rw [← infOf_mul_finOf V g, map_mul, h, one_mul]
  rfl

theorem avg_rat (V : HSp D) (κ : Measure (GinfC V)) [κ.IsMulLeftInvariant] (Φ : GA D V → ℂ)
    (hΦ : ∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) {γ : GfC V} (hγ : γ ∈ ratFin V) (x : GfC V) :
    ∫ k, Φ (((γ * x : GfC V) : GA D V) * k) ∂κ = ∫ k, Φ ((x : GA D V) * k) ∂κ := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  obtain ⟨q, hq, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hγ)
  have e1 : finOf V q = γ := ClassFin.finG_injective V ((finG_finOf V q).trans e)
  have e2 : ((infOf V q : GinfC V) : GA D V) * γ = q := e1 ▸ infOf_mul_finOf V q
  have c1 := GlobalTheory.AdelicSplit.commute_GinfC_GfC V (infOf V q).2 (γ * x).2
  rw [← integral_mul_left_eq_self (fun k : GinfC V => Φ (((γ * x : GfC V) : GA D V) * k)) (infOf V q)]
  refine integral_congr_ae (.of_forall fun k => ?_)
  have e3 : ((γ * x : GfC V) : GA D V) * ((infOf V q * k : GinfC V) : GA D V) = q * ((x : GA D V) * k) := by
    rw [Subgroup.coe_mul (GinfC V), ← mul_assoc, ← c1, Subgroup.coe_mul, ← mul_assoc, e2, mul_assoc]
  dsimp only
  rw [e3, hΦ q hq]

theorem exists_haar (V : HSp D) (hV : IsDefiniteSpace V) : ∃ κ : Measure (GinfC V), κ.IsHaarMeasure ∧ IsProbabilityMeasure κ := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  haveI : CompactSpace (GinfC V) := isCompact_iff_compactSpace.1 (Eqv.isCompact_GinfC hV.1 hV.2)
  exact ⟨Measure.haarMeasure ⊤, Measure.isHaarMeasure_haarMeasure _, ⟨by
    simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC V)))⟩⟩

theorem exists_fine (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (hK : IsOpenCompactLevel V K) {p : GA D V → Prop}
    (h : ∀ᶠ k in 𝓝 (1 : GA D V), k ∈ GfC V → p k) :
    ∃ K'' ≤ K, IsOpenCompactLevel V K'' ∧ ∀ k ∈ Lev.levA V K'', p k := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hG := hT.2.2.2.2.1
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D V _ h
  have key : ∀ g, Lev.finE V g ∈ (U.comap (GfC V).subtype).map (finG V) ↔ (finOf V g : GA D V) ∈ U := fun g => by
    rw [← finG_finOf, Subgroup.mem_map_iff_mem (ClassFin.finG_injective V)]
    rfl
  have hc : Continuous fun g => (finOf V g : GA D V) :=
    continuous_subtype_val.comp (continuous_snd.comp (GlobalTheory.AdelicSplit.splitEquiv V).symm.continuous)
  have hl : ∀ k, k ∈ Lev.levA V (K ⊓ (U.comap (GfC V).subtype).map (finG V)) ↔ k ∈ Lev.levA V K ∧ k ∈ U := fun k => by
    rw [Lev.mem_levA, Lev.mem_levA, Subgroup.mem_inf, key, and_assoc]
    refine and_congr_right fun hk => ?_
    rw [finOf_fin V ⟨k, hk⟩]
  refine ⟨K ⊓ (U.comap (GfC V).subtype).map (finG V), inf_le_left, ⟨?_, ?_⟩, fun k hk => ?_⟩
  · convert hK.1.inter (hU.preimage hc) using 1
    ext g
    exact and_congr Iff.rfl (key g)
  · convert hK.2.inter_right (U.isClosed_of_isOpen hU) using 1
    ext g
    exact hl g
  · exact hUN k ((hl k).1 hk).2 (Lev.mem_levA.1 hk).1 (Lev.mem_levA.1 hk).1

theorem isFinReal_apply {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : GA D V →* Module.End ℂ M}
    (hρ : ∀ g ∈ GfC V, ρ g = 1) {F : GA D V → ℂ} {Λ : Module.Dual ℂ M} {v : GfC V → M} (h : IsFinReal ρ F Λ v)
    (x : GfC V) (k : GinfC V) : F (x * k) = Λ (ρ (k : GA D V)⁻¹ (v x)) := by
  rw [h, finOf_mul_inf, finOf_fin, mul_inv_rev, map_mul, hρ _ (inv_mem x.2), mul_one]

def wgt (V : HSp D) (μ : Measure (GA D V)) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (c : FinCl V K) : ℂ :=
  ((μ (K.comap (Lev.finE V))).toReal : ℂ) * ((gamOrd V K (Quotient.out c) : ℂ))⁻¹

def ext {P : ℕ → Type} [∀ j, One (P j)] (n : ℕ) (x : ∀ j : Fin n, P j) (j : ℕ) : P j := if h : j < n then x ⟨j, h⟩ else 1

theorem finsum_snoc {A : ℕ → Type} {M : Type} [AddCommMonoid M] (n : ℕ) (hA : ∀ j < n + 1, Finite (A j))
    (f : (∀ j : Fin (n + 1), A j) → M) :
    ∑ᶠ c, f c = ∑ᶠ a : A n, ∑ᶠ c : (∀ j : Fin n, A j), f (Fin.snoc (α := fun j : Fin (n + 1) => A j) c a) := by
  letI : ∀ j : Fin (n + 1), Fintype (A j) := fun j => @Fintype.ofFinite _ (hA j j.2)
  letI : ∀ j : Fin n, Fintype (A j) := fun j => @Fintype.ofFinite _ (hA j (by omega))
  letI : Fintype (A n) := @Fintype.ofFinite _ (hA n (by omega))
  simp only [finsum_eq_sum_of_fintype]
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.snocEquiv fun j : Fin (n + 1) => A j) _ _ fun _ => rfl).symm

section Chain

variable {V : ℕ → HSp D} {Mo : ℕ → Type} [∀ n, AddCommGroup (Mo n)] [∀ n, Module ℂ (Mo n)]

noncomputable def ptV (comp : ∀ n, GfC (V n) → GfC (V (n + 1)) → Mo n →ₗ[ℂ] Mo (n + 1)) (v : GfC (V 0) → Mo 0)
    (x : ∀ n, GfC (V n)) : ∀ n, GfC (V n) → Mo n
  | 0 => v
  | n + 1 => fun y => comp n (x n) y (ptV comp v x n (x n))

noncomputable def sumV {A : ℕ → Type} (o : ∀ n, A n → GfC (V n)) (w : ∀ n, A n → ℂ)
    (comp : ∀ n, GfC (V n) → GfC (V (n + 1)) → Mo n →ₗ[ℂ] Mo (n + 1)) (v : GfC (V 0) → Mo 0) : ∀ n, GfC (V n) → Mo n
  | 0 => v
  | n + 1 => fun y => ∑ᶠ c : A n, w n c • comp n (o n c) y (sumV o w comp v n (o n c))

noncomputable def liftC (μ : ∀ n, Measure (GA D (V n))) (fd : ∀ n, Set (GA D (V n)))
    (ker : ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ) (F : GA D (V 0) → ℂ) : ∀ n, GA D (V n) → ℂ
  | 0 => F
  | n + 1 => fun h => ∫ g in fd n, ker n g h * liftC μ fd ker F n g ∂μ n

def FixAt (ker : ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ) (F : GA D (V 0) → ℂ) : ∀ n, GA D (V n) → Prop
  | 0 => fun k => ∀ g, F (g * k) = F g
  | n + 1 => fun k => ∀ g h, ker n g (h * k) = ker n g h

variable (comp : ∀ n, GfC (V n) → GfC (V (n + 1)) → Mo n →ₗ[ℂ] Mo (n + 1)) (v : GfC (V 0) → Mo 0)

theorem ptV_congr {x x' : ∀ n, GfC (V n)} : ∀ n, (∀ j < n, x j = x' j) → ptV comp v x n = ptV comp v x' n
  | 0, _ => rfl
  | n + 1, h => by
    funext y
    simp only [ptV]
    rw [ptV_congr n fun j hj => h j (by omega), h n (by omega)]

theorem ptV_eq_chainTo (x : ∀ n, GfC (V n)) :
    ∀ n, ptV comp v x n (x n) = chainTo (V := Mo) (fun j => comp j (x j) (x (j + 1))) n (v (x 0))
  | 0 => rfl
  | n + 1 => by
    simp only [ptV, chainTo, LinearMap.comp_apply]
    rw [ptV_eq_chainTo x n]

theorem sumV_eq {A : ℕ → Type} (o : ∀ n, A n → GfC (V n)) (w : ∀ n, A n → ℂ) :
    ∀ n, (∀ j < n, Finite (A j)) → ∀ y, sumV o w comp v n y =
      ∑ᶠ c : (∀ j : Fin n, A j), (∏ j : Fin n, w j (c j)) • ptV comp v (ext n fun j => o j (c j)) n y
  | 0, _, y => by
    rw [finsum_unique]
    simp [sumV, ptV]
  | n + 1, hA, y => by
    rw [finsum_snoc n hA]
    simp only [sumV]
    refine finsum_congr fun a => ?_
    letI : ∀ j : Fin n, Fintype (A j) := fun j => @Fintype.ofFinite _ (hA j (by omega))
    rw [sumV_eq o w n fun j hj => hA j (by omega), finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e1 : ext (P := fun j => GfC (V j)) (n + 1)
        (fun j => o j (Fin.snoc (α := fun j : Fin (n + 1) => A j) c a j)) n = o n a := by
      rw [ext, dif_pos (Nat.lt_succ_self n)]
      exact congrArg (o n) (Fin.snoc_last (α := fun j : Fin (n + 1) => A j) a c)
    have e2 : ptV comp v (ext (n + 1) fun j => o j (Fin.snoc (α := fun j : Fin (n + 1) => A j) c a j)) n =
        ptV comp v (ext n fun j => o j (c j)) n := ptV_congr comp v n fun j hj => by
      rw [ext, ext, dif_pos (Nat.lt_succ_of_lt hj), dif_pos hj]
      exact congrArg (o j) (Fin.snoc_castSucc (α := fun j : Fin (n + 1) => A j) a c ⟨j, hj⟩)
    have e3 : ∏ j : Fin (n + 1), w j (Fin.snoc (α := fun j : Fin (n + 1) => A j) c a j) = w n a * ∏ j : Fin n, w j (c j) := by
      rw [Fin.prod_univ_castSucc, mul_comm]
      refine congrArg₂ _ (congrArg (w n) (Fin.snoc_last (α := fun j : Fin (n + 1) => A j) a c)) ?_
      exact Finset.prod_congr rfl fun j _ => congrArg (w j) (Fin.snoc_castSucc (α := fun j : Fin (n + 1) => A j) a c j)
    simp only [ptV]
    rw [e1, e2, e3, map_smul, smul_smul]

variable (ρ : ∀ n, GA D (V n) →* Module.End ℂ (Mo n)) (ker : ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ)
  (Λ : ∀ n, Module.Dual ℂ (Mo n))

def ArrowOK (n : ℕ) : Prop :=
  IsDefiniteSpace (V n) ∧ (∀ φ : D.host.E →+* ℂ, ((V n).gram.map φ).PosDef) ∧ (∀ g ∈ GfC (V n), ρ n g = 1) ∧
  (∀ u, Continuous fun k : GinfC (V n) => Λ n (ρ n (k : GA D (V n))⁻¹ u)) ∧
  (∀ γ ∈ GQ (V n), ∀ g h, ker n (γ * g) h = ker n g h) ∧ (∀ γ ∈ GQ (V (n + 1)), ∀ g h, ker n g (γ * h) = ker n g h) ∧
  (∀ z h, Continuous fun k : GinfC (V n) => ker n (z * k) h) ∧
  ∀ κ : Measure (GinfC (V n)), κ.IsHaarMeasure → IsProbabilityMeasure κ → ∀ (x : GfC (V n)) (h : GA D (V (n + 1))) (u : Mo n),
    ∫ k, ker n ((x : GA D (V n)) * (k : GA D (V n))) h * Λ n (ρ n (k : GA D (V n))⁻¹ u) ∂κ =
      Λ (n + 1) (ρ (n + 1) h⁻¹ (comp n x (finOf _ h) u))

def ptF (x : ∀ n, GfC (V n)) (n : ℕ) (h : GA D (V n)) : ℂ := Λ n (ρ n h⁻¹ (ptV comp v x n (finOf _ h)))

theorem ptF_real (x : ∀ n, GfC (V n)) (n : ℕ) : IsFinReal (ρ n) (ptF comp v ρ Λ x n) (Λ n) (ptV comp v x n) := fun _ => rfl

variable {comp v ρ ker Λ}

theorem ptF_succ {n : ℕ} (h : ArrowOK comp ρ ker Λ n) (κ : Measure (GinfC (V n))) (h1 : κ.IsHaarMeasure)
    (h2 : IsProbabilityMeasure κ) (x : ∀ n, GfC (V n)) (g : GA D (V (n + 1))) :
    ptF comp v ρ Λ x (n + 1) g = ∫ k, ker n (x n * k) g * ptF comp v ρ Λ x n (x n * k) ∂κ := by
  simp only [isFinReal_apply h.2.2.1 (ptF_real comp v ρ Λ x n)]
  exact (h.2.2.2.2.2.2.2 κ h1 h2 _ _ _).symm

variable {N : ℕ} (hc : ∀ n < N, ArrowOK comp ρ ker Λ n) {F : GA D (V 0) → ℂ} (hF : IsFinReal (ρ 0) F (Λ 0) v)
  (hFa : ∀ γ ∈ GQ (V 0), ∀ g, F (γ * g) = F g)
include hc hF hFa

theorem ptF_left (x : ∀ n, GfC (V n)) : ∀ n ≤ N, ∀ γ ∈ GQ (V n), ∀ g, ptF comp v ρ Λ x n (γ * g) = ptF comp v ρ Λ x n g
  | 0, _, γ, hγ, g => (hF _).symm.trans ((hFa γ hγ g).trans (hF _))
  | n + 1, hn, γ, hγ, g => by
    obtain ⟨κ, h1, h2⟩ := exists_haar _ (hc n hn).1
    simp only [ptF_succ (hc n hn) κ h1 h2, (hc n hn).2.2.2.2.2.1 γ hγ]

theorem ptF_rat {x x' : ∀ n, GfC (V n)} (hx : ∀ j < N, ∃ γ ∈ ratFin (V j), x' j = γ * x j) :
    ∀ n ≤ N, ptF comp v ρ Λ x' n = ptF comp v ρ Λ x n
  | 0, _ => rfl
  | n + 1, hn => by
    obtain ⟨κ, h1, h2⟩ := exists_haar _ (hc n hn).1
    obtain ⟨γ, hγ, e⟩ := hx n hn
    funext g
    rw [ptF_succ (hc n hn) κ h1 h2, ptF_succ (hc n hn) κ h1 h2, ptF_rat hx n (by omega), e]
    exact avg_rat _ κ (fun z => ker n z g * ptF comp v ρ Λ x n z) (fun q hq z => by
      rw [(hc n hn).2.2.2.2.1 q hq, ptF_left hc hF hFa x n (by omega) q hq]) hγ _

omit hF in

theorem liftC_left (μ : ∀ n, Measure (GA D (V n))) (fd : ∀ n, Set (GA D (V n))) :
    ∀ n ≤ N, ∀ γ ∈ GQ (V n), ∀ g, liftC μ fd ker F n (γ * g) = liftC μ fd ker F n g
  | 0, _, γ, hγ, g => hFa γ hγ g
  | n + 1, hn, γ, hγ, g => by simp only [liftC, (hc n hn).2.2.2.2.2.1 γ hγ]

omit hc hF hFa in
theorem liftC_right (μ : ∀ n, Measure (GA D (V n))) (fd : ∀ n, Set (GA D (V n))) :
    ∀ n k, FixAt ker F n k → ∀ g, liftC μ fd ker F n (g * k) = liftC μ fd ker F n g
  | 0, _, hk, g => hk g
  | n + 1, k, hk, g => by
    have hk' : ∀ g h, ker n g (h * k) = ker n g h := hk
    simp only [liftC, hk']

theorem liftC_real (μ : ∀ n, Measure (GA D (V n))) (fd : ∀ n, Set (GA D (V n)))
    (K : ∀ n, Subgroup (GL (Fin (V n).rank) (Lev.EAf D)))
    (hK : ∀ n < N, IsOpenCompactLevel _ (K n) ∧ (∃ K₀, IsOpenCompactLevel _ K₀ ∧ K n ≤ K₀ ∧ IsMeasDef _ K₀ (μ n) (fd n)) ∧
      ∀ k ∈ Lev.levA _ (K n), FixAt ker F n k ∧ ∀ g h, ker n (g * k) h = ker n g h) :
    ∀ n ≤ N, IsFinReal (ρ n) (liftC μ fd ker F n) (Λ n)
      (sumV (A := fun n => FinCl (V n) (K n)) (fun _ c => Quotient.out c) (fun n => wgt (V n) (μ n) (K n)) comp v n)
  | 0, _ => hF
  | n + 1, hn => by
    intro h
    have ih := liftC_real μ fd K hK n (by omega)
    obtain ⟨h1, ⟨K₀, h2, h3, h4⟩, h5⟩ := hK n hn
    obtain ⟨-, a2, a3, a4, a5, -, a7, a8⟩ := hc n hn
    obtain ⟨hfin, κ, hκH, hκP, hU⟩ := GlobalTheory.DefiniteClassReal.integral_eq_finClSum_avg (V n) a2 K₀ (K n) h2 h1 h3 (μ n) (fd n) h4
      (fun g => ker n g h * liftC μ fd ker F n g)
      (fun γ hγ g => by
        rw [a5 γ hγ, liftC_left hc hFa μ fd n (by omega) γ hγ])
      (fun k hk g => by
        rw [(h5 k hk).2, liftC_right μ fd n k (h5 k hk).1])
      (fun z => (a7 z h).mul (by
        have e : ∀ k : GinfC (V n), liftC μ fd ker F n (z * k) = Λ n (ρ n (k : GA D (V n))⁻¹ (ρ n z⁻¹ (sumV
            (A := fun n => FinCl (V n) (K n)) (fun _ c => Quotient.out c) (fun n => wgt (V n) (μ n) (K n)) comp v n
            (finOf _ z)))) := fun k => by
          rw [ih, finOf_mul_inf, mul_inv_rev, map_mul, Module.End.mul_apply]
        simp only [e]
        exact a4 _))
    haveI := Fintype.ofFinite (FinCl (V n) (K n))
    simp only [liftC, sumV]
    rw [hU, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [isFinReal_apply a3 ih]
    rw [a8 κ hκH hκP, map_smul, map_smul, smul_eq_mul, wgt, div_eq_mul_inv]

end Chain

end GlobalTheory.JetsOne

end
