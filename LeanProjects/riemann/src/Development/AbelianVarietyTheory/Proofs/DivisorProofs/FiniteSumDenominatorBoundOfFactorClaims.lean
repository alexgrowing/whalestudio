import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.PairingDivisorProofs.ValAdd
import Formalism.LocalToGlobal.Columns.CoefModAt
import Formalism.LocalToGlobal.Divisibility.JetBounds.JetBoundsProofs.NormEqOneOfNotMem
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TwistedLatticeNaturality
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthogonalSumCoefficientLatticeIsLatticeAndDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFinClAndGamOrd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryConjSplitSupportedFiniteAdelicPoi
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTestLatUnique

namespace DenominatorLossAdditivity
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.CompanionTheory.FinDen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Val

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem vw_eq_zero_of_notMem (w : HeightOneSpectrum (𝓞 K)) {c : 𝓞 K} (hc : c ∉ w.asIdeal) : vw w (c : K) = 0 := by
  have hc0 : c ≠ 0 := fun h => hc (h ▸ zero_mem _)
  have h1 := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w c
  have h2 := (Formalism.L2.DIV.EmbeddingLemmas.mem_pow_iff w c hc0 1).not.1 (by simpa using hc)
  have h3 : 0 ≤ vw w (algebraMap (𝓞 K) K c) := h1
  have h4 : vw w (algebraMap (𝓞 K) K c) < ((1 : ℕ) : ℤ) := not_le.1 h2
  have : vw w (algebraMap (𝓞 K) K c) = 0 := by omega
  exact this

theorem exists_den {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (Lt : Submodule (𝓞 K) (Fin n → K)) (hL : Lt.FG) (y : Fin n → K) (a : ℝ)
    (ha : 0 ≤ a) (h : ∀ x ∈ Lt, y ⬝ᵥ x = 0 ∨ -a ≤ (vw w (y ⬝ᵥ x) : ℝ)) :
    ∃ s : K, s ≠ 0 ∧ (vw w s : ℝ) ≤ a ∧ s • y ∈ dualFr Lt := by
  classical
  obtain ⟨G, hG⟩ := hL
  obtain ⟨u, hu, hv⟩ := Formalism.DivisionValues.shift_exists_val w ⌊a⌋
  have key : ∀ x ∈ Lt, ∃ c z : 𝓞 K, c ∉ w.asIdeal ∧ (c : K) * (u * (y ⬝ᵥ x)) = (z : K) := by
    intro x hx
    by_cases h0 : y ⬝ᵥ x = 0
    · exact ⟨1, 0, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp [h0]⟩
    · refine Formalism.L2.DIV.EmbeddingLemmas.exists_clear w _ ?_
      rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hu h0, hv]
      have h1 := (h x hx).resolve_left h0
      have h2 : -vw w (y ⬝ᵥ x) ≤ ⌊a⌋ := Int.le_floor.2 (by push_cast; linarith)
      omega
  choose! c z hc hz using key
  have hGL : ∀ x ∈ G, x ∈ Lt := fun x hx => hG ▸ Submodule.subset_span hx
  set P : 𝓞 K := ∏ x ∈ G, c x with hP
  have hPw : P ∉ w.asIdeal := by
    intro hm
    obtain ⟨x, hx, hx'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 hm
    exact hc x (hGL x hx) hx'
  have hP0 : (P : K) ≠ 0 := by
    intro h0
    have : P = 0 := by exact_mod_cast h0
    exact hPw (this ▸ zero_mem _)
  refine ⟨u * P, mul_ne_zero hu hP0, ?_, ?_⟩
  · rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hu hP0, hv, vw_eq_zero_of_notMem w hPw, add_zero]
    exact Int.floor_le a
  · intro x hx
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rw [Submodule.mem_one]
      refine ⟨(∏ x' ∈ G.erase x, c x') * z x, ?_⟩
      have e : P = c x * ∏ x' ∈ G.erase x, c x' := (Finset.mul_prod_erase G c hx).symm
      have e2 := hz x (hGL x hx)
      rw [smul_dotProduct, smul_eq_mul, e]
      simp only [map_mul]
      have e3 : algebraMap (𝓞 K) K (c x) * (u * (y ⬝ᵥ x)) = algebraMap (𝓞 K) K (z x) := e2
      have e4 : u * ((c x : K) * ((∏ x' ∈ G.erase x, c x' : 𝓞 K) : K)) * (y ⬝ᵥ x) =
          ((∏ x' ∈ G.erase x, c x' : 𝓞 K) : K) * (algebraMap (𝓞 K) K (c x) * (u * (y ⬝ᵥ x))) := by
        simp only [RingOfIntegers.coe_eq_algebraMap]; ring
      rw [e3] at e4
      simpa [RingOfIntegers.coe_eq_algebraMap, mul_comm, mul_left_comm, mul_assoc] using e4.symm
    | zero => simp [zero_mem]
    | add a b _ _ ha hb =>
      rw [dotProduct_add]
      exact add_mem ha hb
    | smul r a _ ha =>
      rw [dotProduct_smul]
      exact Submodule.smul_mem _ r ha

end Val

section Loss

variable {D : D7} {w : PlL D}

theorem loss_mul {z z' : ℂ} {a a' : ℝ} (h : LossLe w z a) (h' : LossLe w z' a') : LossLe w (z * z') (a + a') := by
  obtain ⟨y, e, h⟩ := h
  obtain ⟨y', e', h'⟩ := h'
  refine ⟨y * y', by rw [map_mul, e, e'], ?_⟩
  rcases h with rfl | h
  · exact Or.inl (zero_mul _)
  rcases h' with rfl | h'
  · exact Or.inl (mul_zero _)
  by_cases h0 : y = 0
  · exact Or.inl (by rw [h0, zero_mul])
  by_cases h0' : y' = 0
  · exact Or.inl (by rw [h0', mul_zero])
  refine Or.inr ?_
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h0 h0']
  push_cast
  linarith

theorem loss_add {z z' : ℂ} {a : ℝ} (h : LossLe w z a) (h' : LossLe w z' a) : LossLe w (z + z') a := by
  obtain ⟨y, e, h⟩ := h
  obtain ⟨y', e', h'⟩ := h'
  refine ⟨y + y', by rw [map_add, e, e'], ?_⟩
  by_cases h0 : y = 0
  · subst h0; simpa using h'
  by_cases h0' : y' = 0
  · subst h0'; simpa using h
  by_cases h1 : y + y' = 0
  · exact Or.inl h1
  refine Or.inr ?_
  have hy := h.resolve_left h0
  have hy' := h'.resolve_left h0'
  have := Formalism.PairingDivisionLocalBalance.vw_add w y y' h0 h0' h1
  have h2 : ((min (vw w y) (vw w y') : ℤ) : ℝ) ≤ (vw w (y + y') : ℝ) := by exact_mod_cast this
  refine le_trans ?_ h2
  push_cast
  exact le_min hy hy'

theorem loss_zero (a : ℝ) : LossLe w 0 a := ⟨0, map_zero _, Or.inl rfl⟩

theorem loss_sum {ι : Type} (s : Finset ι) (f : ι → ℂ) {a : ℝ} (h : ∀ i ∈ s, LossLe w (f i) a) : LossLe w (∑ i ∈ s, f i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using loss_zero a
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact loss_add (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Loss

section Delta

variable {Γ A K M : Type} [Group Γ] [Group A] [Field K] [AddCommGroup M] [Module K M]
  (ι : Γ →* A) (U : Subgroup A) (ρ : Γ →* Module.End K M)

open Classical in

theorem deltaForm_eq_sum (x g : A) (hf : {γ : Γ | x⁻¹ * ((ι γ)⁻¹ * g) ∈ U}.Finite) (v : M) :
    deltaForm ι U ρ x v g = ∑ γ ∈ hf.toFinset, ρ γ v := by
  unfold deltaForm
  rw [finsum_eq_sum_of_support_subset _ (s := hf.toFinset) ?_]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    exact if_pos (hf.mem_toFinset.1 hγ)
  · intro γ hγ
    rw [Function.mem_support] at hγ
    by_contra h
    exact hγ (if_neg (fun h' => h (hf.mem_toFinset.2 h')))

theorem deltaForm_sum {J : Type} (x g : A) (hf : {γ : Γ | x⁻¹ * ((ι γ)⁻¹ * g) ∈ U}.Finite) (s : Finset J) (a : J → K) (v : J → M) :
    deltaForm ι U ρ x (∑ i ∈ s, a i • v i) g = ∑ i ∈ s, a i • deltaForm ι U ρ x (v i) g := by
  classical
  simp only [deltaForm_eq_sum ι U ρ x g hf, map_sum, map_smul, Finset.smul_sum]
  exact Finset.sum_comm

theorem finite_index (x g : A) (h : Finite {δ : Γ // g⁻¹ * ι δ * g ∈ U}) :
    {γ : Γ | x⁻¹ * ((ι γ)⁻¹ * g) ∈ U}.Finite := by
  by_cases hne : ∃ γ₀ : Γ, x⁻¹ * ((ι γ₀)⁻¹ * g) ∈ U
  · obtain ⟨γ₀, h₀⟩ := hne
    have hm : ∀ γ : {γ : Γ | x⁻¹ * ((ι γ)⁻¹ * g) ∈ U}, g⁻¹ * ι (γ.1 * γ₀⁻¹) * g ∈ U := by
      rintro ⟨γ, hγ⟩
      have := U.mul_mem (U.inv_mem hγ) h₀
      have e : (x⁻¹ * ((ι γ)⁻¹ * g))⁻¹ * (x⁻¹ * ((ι γ₀)⁻¹ * g)) = g⁻¹ * ι (γ * γ₀⁻¹) * g := by
        simp only [map_mul, map_inv]; group
      rwa [e] at this
    refine Set.finite_coe_iff.1 ?_
    exact Finite.of_injective (fun γ => (⟨γ.1 * γ₀⁻¹, hm γ⟩ : {δ : Γ // g⁻¹ * ι δ * g ∈ U})) fun a b e => by
      have := congrArg Subtype.val e
      exact Subtype.ext (mul_right_cancel this)
  · have : {γ : Γ | x⁻¹ * ((ι γ)⁻¹ * g) ∈ U} = ∅ := Set.eq_empty_of_forall_notMem fun γ hγ => hne ⟨γ, hγ⟩
    rw [this]
    exact Set.finite_empty

end Delta

section DeltaG

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem exists_lift (γ : UR D.sp.cm (Xp G).gram) : ∃ z : ratFin (Xp G), finG (Xp G) z.1 = ratIn G γ := by
  have hγ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1.1 * (Xp G).gram * γ.1.1 = (Xp G).gram := γ.2
  let q0 : GA D (Xp G) := GlobalTheory.ConjSplit.ratPt D (Xp G) γ.1 hγ
  have hq : q0 ∈ GQ (Xp G) := by
    exact ⟨γ.1, γ.2, rfl⟩
  let q : GQ (Xp G) := ⟨q0, hq⟩
  have hr : Bridge.IsRatMat (Xp G) q γ.1 := rfl
  have e1 : Lev.finE (Xp G) q.1 = ratIn G γ := TestLatModel.finE_rat q γ hr
  obtain ⟨z, hz⟩ := GlobalTheory.FunObj.ClassFin.gfcToGf_surjective (Xp G) (Bridge.ratF (Xp G) q)
  have hz' : finHom (Xp G) z.1 = finHom (Xp G) q.1 := congrArg Subtype.val hz
  have e2 : finG (Xp G) z = Lev.finE (Xp G) q.1 := by
    show Formalism.UG.bc (Lev.swapAE D) (finHom (Xp G) z.1) = Formalism.UG.bc (Lev.swapAE D) (finHom (Xp G) q.1)
    rw [hz']
  exact ⟨⟨z, q.1, q.2, e2.symm⟩, e2.trans e1⟩

theorem finite_stabUR (x : FinPt G (.top 0)) (hx : gamOrd (Xp G) G.Kplus x ≠ 0) :
    Finite {δ : UR D.sp.cm (Xp G).gram // (finG (Xp G) x)⁻¹ * ratIn G δ * finG (Xp G) x ∈ G.Kplus} := by
  have hf := (Nat.card_ne_zero.1 hx).2
  choose z hz using exists_lift (G := G)
  refine Finite.of_injective (β := {γ : ratFin (Xp G) // finG (Xp G) (x⁻¹ * γ * x) ∈ G.Kplus})
    (fun δ => ⟨z δ.1, ?_⟩) ?_
  · rw [map_mul, map_mul, map_inv, hz]
    exact δ.2
  · intro a b e
    have h1 : z a.1 = z b.1 := congrArg Subtype.val e
    have h2 : ratIn G a.1 = ratIn G b.1 := by rw [← hz, ← hz, h1]
    exact Subtype.ext (Subtype.ext (Formalism.L2.DIV.incl_inj D.host.F D.host.E _ h2))

end DeltaG

section Chain

theorem chainTo_loss {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (Q : ∀ j, ℝ → Set (V j))
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (m : ℕ) (δ : ℝ) (hk : ∀ j, j < m → ∀ a, ∀ u ∈ Q j a, k j u ∈ Q (j + 1) (a + δ)) (a : ℝ) (u : V 0)
    (hu : u ∈ Q 0 a) : ∀ n, n ≤ m → chainTo k n u ∈ Q n (a + n * δ)
  | 0, _ => by
    have e : a + ((0 : ℕ) : ℝ) * δ = a := by simp
    rw [e]
    exact hu
  | n + 1, hn => by
    have := hk n (by omega) _ _ (chainTo_loss Q k m δ hk a u hu n (by omega))
    have e : a + ((n + 1 : ℕ) : ℝ) * δ = a + n * δ + δ := by push_cast; ring
    rw [e]
    exact this

end Chain

section Core

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

open Classical in

theorem vCore_lin {S : GridChoice W U} {t : T} {Φ : G.Datum} (h : S.SumOK t Φ) {J : Type} (s : Finset J) (a : J → ℂ)
    (Ψs : J → FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (Ψ0 : FinPt G (.top 0) → VV ℂ (wt G (.top 0)))
    (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m)))
    (hv : ∀ (β : CosFam G t) (c : S.Classes t Φ β), Ψ0 (S.ptTop c 0) = ∑ i ∈ s, a i • Ψs i (S.ptTop c 0)) :
    S.vCore t Φ Ψ0 F = ∑ i ∈ s, a i * S.vCore t Φ (Ψs i) F := by
  have hτ : ∀ β ∈ S.supp t Φ, S.IsExpansion t Φ β (Classical.epsilon (S.IsExpansion t Φ β)) :=
    fun β hβ => Classical.epsilon_spec (h.ex β hβ)
  simp only [h.vCore_eq _ hτ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  have := h.cls β
  have := Fintype.ofFinite (S.Classes t Φ β)
  simp only [GridChoice.classSum, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hv β c, map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

end Core

section Sum

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

set_option maxHeartbeats 1600000 in
open Classical in

theorem core_loss (ch : Choice R) {t : T} {w : PlL D} {Φ : ch.G.Datum} (hS : ch.S.SumOK t Φ)
    (hD : ∀ β ∈ ch.S.supp t Φ, ∃ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ)
    {aC aD aG aT aR aP aF : ℝ}
    (hC : ∀ β ∈ ch.S.supp t Φ, LossLe w (∏ v, ((ch.S.term t Φ β v).coef : ℂ)) aC)
    (hDat : ∀ β ∈ ch.S.supp t Φ, ∀ x y, LossLe w (∏ v, (ch.S.term t Φ β v).datum (ch.S.colAt t v x) (ch.S.rowAt t v y)) aD)
    (hG : ∀ β (c : ch.S.Classes t Φ β), LossLe w (ch.S.invGam c) aG)
    (hT : ∀ β d, Occurs ch.S.toGridChoice t Φ β d → ∀ (c : ch.S.Classes t Φ β) (j : Fin D.R.m) (a : ℝ) v,
      InLat _ w a (latAt ch.S.toGridChoice (.top j) (ch.S.ptTop c j)) v →
      InLat _ w (a + aT) (latAt ch.S.toGridChoice (.top (j + 1)) (ch.S.ptTop c (j + 1)))
        (ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) v))
    (hR : ∀ β d, Occurs ch.S.toGridChoice t Φ β d → ∀ (c : ch.S.Classes t Φ β) (i : Fin D.R.m) (a : ℝ) v,
      InLat _ w a (latAt ch.S.toGridChoice (.grid i D.R.m) (ch.S.ptRow c i)) v →
      InLat _ w (a + aR) (latAt ch.S.toGridChoice (.grid (i + 1) D.R.m) (ch.S.ptRow c (i + 1)))
        (ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) v))
    (hP : ∀ (y : FinPt ch.G (.grid D.R.m D.R.m)) (a a' : ℝ) u v,
      InLat _ w a (latAt ch.S.toGridChoice (.top D.R.m) (finEmb ch.G.sp.topDec y)) u →
      InLat _ w a' (latAt ch.S.toGridChoice (.grid D.R.m D.R.m) y) v → LossLe w (lastPair ch.G u v) (a + a' + aP))
    (Ψ : FinPt ch.G (.top 0) → VV ℂ (wt ch.G (.top 0)))
    (hΨ : ∀ x, InLat _ w 0 (latAt ch.S.toGridChoice (.top 0) x) (rhoVr (tauE D) _ (ch.S.N.fr (.top 0))⁻¹ (Ψ x)))
    (Fm : FinPt ch.G (.grid 0 D.R.m) → VV ℂ (listedWt ch.G (.grid 0 D.R.m)))
    (hF : ∀ y, InLat _ w aF (latAt ch.S.toGridChoice (.grid 0 D.R.m) y) (rowVal ch.S.toGridChoice (Fm y))) :
    LossLe w (ch.S.vCore t Φ Ψ Fm) (aC + (aG + (aD + (0 + D.R.m * aT + (aF + D.R.m * aR) + aP)))) := by
  have ex : ∀ β, ∃ τ, β ∈ ch.S.supp t Φ → IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ := fun β => by
    by_cases hβ : β ∈ ch.S.supp t Φ
    · obtain ⟨τ, h⟩ := hD β hβ
      exact ⟨τ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hβ⟩
  choose τ hτ using ex
  rw [hS.vCore_eq τ (fun β hβ => (hτ β hβ).2.1)]
  refine loss_sum _ _ fun β hβ => ?_
  have hβ' : β ∈ ch.S.supp t Φ := hS.fin.mem_toFinset.1 hβ
  refine loss_mul (hC β hβ') ?_
  have := hS.cls β
  have := Fintype.ofFinite (ch.S.Classes t Φ β)
  rw [GridChoice.classSum, finsum_eq_sum_of_fintype]
  refine loss_sum _ _ fun c _ => loss_mul (hG β c) ?_
  simp only [GridChoice.pairAt, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.compl₁₂_apply]
  refine loss_sum _ _ fun d hd => ?_
  obtain ⟨x', y', e⟩ := (hτ β hβ').coef_eq hd
  rw [e]
  refine loss_mul (hDat β hβ' x' y') ?_
  have hO : Occurs ch.S.toGridChoice t Φ β d := ⟨hβ', τ β, hτ β hβ', hd⟩
  have hcol := chainTo_loss (V := fun j => VV ℂ (wt ch.G (.top j)))
    (fun j a => {v | InLat _ w a (latAt ch.S.toGridChoice (.top j) (ch.S.ptTop c j)) v})
    (fun j => if h : j < D.R.m then ch.S.Z.kkMap 1 (d.1 ⟨j, h⟩) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) else 0) D.R.m aT
    (fun j hj a u hu => by
      simp only [dif_pos hj]
      exact hT β d hO c ⟨j, hj⟩ a u hu) 0 _ (hΨ (ch.S.ptTop c 0)) D.R.m le_rfl
  have hrow := chainTo_loss (V := fun i => VV ℂ (wt ch.G (.grid i D.R.m)))
    (fun i a => {v | InLat _ w a (latAt ch.S.toGridChoice (.grid i D.R.m) (ch.S.ptRow c i)) v})
    (fun i => if h : i < D.R.m then ch.S.Z.kkMap 1 (d.2 ⟨i, h⟩) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) else 0) D.R.m aR
    (fun i hi a u hu => by
      simp only [dif_pos hi]
      exact hR β d hO c ⟨i, hi⟩ a u hu) aF _ (hF (ch.S.ptRow c 0)) D.R.m le_rfl
  have e' : ch.S.ptTop c D.R.m = finEmb ch.G.sp.topDec (ch.S.ptRow c D.R.m) := by
    simp [GridChoice.ptTop]
  simp only [Set.mem_setOf_eq] at hcol hrow
  rw [e'] at hcol
  exact hP _ _ _ _ _ hcol hrow

end Sum

end GlobalTheory.CompanionTheory.FinDen

end

end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.CompanionTheory.FinDen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Test

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem psiC_sum {L : LevCh D T} {sc : Consts} {G : GridData L sc} {J : Type} (s : Finset J) (a : J → D.what₂.LL)
    (Ψ0 : GLf G → WtSp G) (Ψs : J → GLf G → WtSp G) (x : FinPt G (.top 0))
    (h : Ψ0 (finG (Xp G) x) = ∑ i ∈ s, a i • Ψs i (finG (Xp G) x)) :
    psiC Ψ0 x = ∑ i ∈ s, D.what₂.embLL (a i) • psiC (Ψs i) x := by
  apply Subtype.ext
  show (GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP G) (Ψ0 (finG (Xp G) x))).1 = _
  rw [h, map_sum, Submodule.coe_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, Submodule.coe_smul, Submodule.coe_smul]
  rfl

theorem gam_ne {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {S : GridChoice W U} {t : T} {Φ : G.Datum}
    (h : S.SumOK t Φ) {β : CosFam G t} (c : S.Classes t Φ β) : gamOrd (Xp G) G.Kplus (S.ptTop c 0) ≠ 0 := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h1 := left_ne_zero_of_mul (h.gam β c)
  have h2 := Finset.prod_ne_zero_iff.1 h1 ⟨0, hm⟩ (Finset.mem_univ _)
  have e : S.ptTop c 0 = (c.1 ⟨0, hm⟩).out := by
    unfold GridChoice.ptTop
    rw [Function.update_of_ne hm.ne]
    exact dif_pos hm
  rw [e]
  intro h3
  apply h2
  have h4 : gamOrd (G.V (.top ((⟨0, hm⟩ : Fin D.R.m) : ℕ))) (S.levTop t Φ β ((⟨0, hm⟩ : Fin D.R.m) : ℕ) hm) (c.1 ⟨0, hm⟩).out = 0 := h3
  rw [h4]
  simp

set_option maxHeartbeats 1600000 in
open Classical in

theorem exists_intMod_levelPrimePow_eq_add_mul (ch : Choice R) {t : T} {w : PlL D} {B : ℝ} (hB : 0 ≤ B) (hO : ∀ a, ch.S.SumOK t (ch.Phi a))
    {X' : InfinitePlace D.what₂.LL → Matrix (Fin ch.n) (Fin ch.n) ℂ} {M : Submodule (𝓞 D.what₂.LL) (Fin ch.n → D.what₂.LL)}
    (hM : IsTestLat ch.G ch.rp ch.n ch.e X' M) (Fx : A.fam.amb.FR t) (y : Fin ch.n → D.what₂.LL)
    (hy : ∀ a, D.what₂.embLL (y a) = vK ch t Fx a)
    (hb : ∀ (Φ : ch.G.Datum) (cl : ch.G.ClPlus), ch.S.SumOK t Φ → ∀ u ∈ wLat ch.G (ch.rp.lat cl),
      LossLe w (ch.S.sAA * ch.S.vCore t Φ (psiC (ch.rp.delta cl u)) (ch.S.formC t (R.jX t Fx))) B) :
    ∃ s : D.what₂.LL, s ≠ 0 ∧ (vw w s : ℝ) ≤ B ∧ s • y ∈ M := by
  obtain ⟨i0⟩ := GlobalTheory.TestLat.SumLat.idx_nonempty (LaP ch.G)
  haveI : Finite (TestIx ch.G) := Finite.of_injective (fun c => ch.e.symm (c, i0))
    fun _ _ h => congrArg Prod.fst (ch.e.symm.injective h)
  haveI := Fintype.ofFinite (TestIx ch.G)
  have hlat : Submodule.IsLattice D.what₂.LL (formLat ch.G ch.rp ch.e) :=
    GlobalTheory.TestLat.SumLat.isLattice_sumLat _ _ _ fun c =>
      delAtr_isLattice (emb D) (LaP ch.G) _ (isSelfDualE_latOf ch.G (ch.rp.x c.2)).1
  have key : ∀ x ∈ formLat ch.G ch.rp ch.e, y ⬝ᵥ x = 0 ∨ -B ≤ (vw w (y ⬝ᵥ x) : ℝ) := by
    intro x hx
    have e1 : ∑ a, D.what₂.embLL (x a) * vK ch t Fx a =
        ∑ c : TestIx ch.G, ∑ i, D.what₂.embLL (x (ch.e.symm (c, i))) * vK ch t Fx (ch.e.symm (c, i)) := by
      rw [← Equiv.sum_comp ch.e.symm, Fintype.sum_prod_type]
    have hl : LossLe w (∑ a, D.what₂.embLL (x a) * vK ch t Fx a) B := by
      rw [e1]
      refine loss_sum _ _ fun c _ => ?_
      have hc : valAt (LaP ch.G) ch.e c x ∈ wLat ch.G (ch.rp.lat c.2) := (Submodule.mem_iInf _).1 hx c
      have hSO : ch.S.SumOK t c.1 := by
        have h := hO (ch.e.symm (c, i0))
        have e : ch.Phi (ch.e.symm (c, i0)) = c.1 := by
          simp only [Choice.Phi, datumOf, Equiv.apply_symm_apply]
        rwa [e] at h
      have hval : valAt (LaP ch.G) ch.e c x = ∑ i, x (ch.e.symm (c, i)) • bVV D.what₂.LL (LaP ch.G) i := by
        simp [valAt, Module.Basis.equivFun_symm_apply, LinearMap.funLeft_apply]
      have hlin := vCore_lin hSO Finset.univ (fun i => D.what₂.embLL (x (ch.e.symm (c, i))))
        (fun i => psiC (ch.rp.delta c.2 (bVV D.what₂.LL (LaP ch.G) i)))
        (psiC (ch.rp.delta c.2 (valAt (LaP ch.G) ch.e c x))) (ch.S.formC t (R.jX t Fx)) (fun β cc => by
          refine psiC_sum _ _ _ _ _ ?_
          rw [hval]
          exact deltaForm_sum _ _ _ _ _ (finite_index _ _ _ _ (finite_stabUR _ (gam_ne hSO cc))) _ _ _)
      have e2 : ∑ i, D.what₂.embLL (x (ch.e.symm (c, i))) * vK ch t Fx (ch.e.symm (c, i)) =
          ch.S.sAA * ch.S.vCore t c.1 (psiC (ch.rp.delta c.2 (valAt (LaP ch.G) ch.e c x))) (ch.S.formC t (R.jX t Fx)) := by
        rw [hlin, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have e3 : vK ch t Fx (ch.e.symm (c, i)) =
            ch.S.sAA * ch.S.vCore t c.1 (psiC (ch.rp.delta c.2 (bVV D.what₂.LL (LaP ch.G) i))) (ch.S.formC t (R.jX t Fx)) := by
          show ch.S.sAA * ch.S.vCore t (datumOf ch.e (ch.e.symm (c, i))) (psiC (psi ch.rp ch.e (ch.e.symm (c, i))))
            (ch.S.formC t (R.jX t Fx)) = _
          simp only [datumOf, psi, Equiv.apply_symm_apply]
        rw [e3]
        ring
      rw [e2]
      exact hb c.1 c.2 hSO _ hc
    obtain ⟨y', e, h⟩ := hl
    have e2 : y' = y ⬝ᵥ x := D.what₂.embLL.injective (by
      rw [e, dotProduct, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hy, mul_comm])
    rwa [e2] at h
  obtain ⟨s, hs, hv, hm⟩ := exists_den w _ hlat.fg y B hB key
  exact ⟨s, hs, hv, hM.2 ▸ hm⟩

end Test

section Comb

variable {D : D7}

theorem loss_comb {dS dC dD dG dT dR dF dP : PlL D → ℝ} {B m : ℝ} (hm : 1 ≤ m) (hS : Loss dS (m * B)) (hC : Loss dC (m * B))
    (hD : Loss dD (m * B)) (hG : Loss dG (m * B)) (hT : Loss dT B) (hR : Loss dR B) (hF : Loss dF B) (hP : Loss dP B) :
    Loss (fun w => dS w + dC w + dD w + dG w + m * dT w + m * dR w + dF w + dP w) (8 * m * B) := by
  have hB : 0 ≤ B := by simpa using hT.2.2 ∅
  have hm0 : 0 ≤ m := by linarith
  refine ⟨fun w => ?_, ?_, fun s => ?_⟩
  · have h1 := hS.1 w
    have h2 := hC.1 w
    have h3 := hD.1 w
    have h4 := hG.1 w
    have h5 := mul_nonneg hm0 (hT.1 w)
    have h6 := mul_nonneg hm0 (hR.1 w)
    have h7 := hF.1 w
    have h8 := hP.1 w
    show 0 ≤ dS w + dC w + dD w + dG w + m * dT w + m * dR w + dF w + dP w
    linarith
  · refine ((((((((hS.2.1.union hC.2.1).union hD.2.1).union hG.2.1).union hT.2.1).union hR.2.1).union hF.2.1).union hP.2.1)).subset ?_
    intro w hw
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hn
    exact hw (by simp [h1, h2, h3, h4, h5, h6, h7, h8])
  · have e : ∑ w ∈ s, lw w * (dS w + dC w + dD w + dG w + m * dT w + m * dR w + dF w + dP w) =
        ∑ w ∈ s, lw w * dS w + ∑ w ∈ s, lw w * dC w + ∑ w ∈ s, lw w * dD w + ∑ w ∈ s, lw w * dG w + m * ∑ w ∈ s, lw w * dT w +
          m * ∑ w ∈ s, lw w * dR w + ∑ w ∈ s, lw w * dF w + ∑ w ∈ s, lw w * dP w := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [e]
    have h1 := hS.2.2 s
    have h2 := hC.2.2 s
    have h3 := hD.2.2 s
    have h4 := hG.2.2 s
    have h5 := mul_le_mul_of_nonneg_left (hT.2.2 s) hm0
    have h6 := mul_le_mul_of_nonneg_left (hR.2.2 s) hm0
    have h7 := hF.2.2 s
    have h8 := hP.2.2 s
    have h9 : B ≤ m * B := by nlinarith
    linarith

end Comb

section Main

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

set_option maxHeartbeats 1600000 in

theorem fin_at (F : Face D A) (ch : Choice R) (C b : ℝ) (hO : ∀ t a, ch.S.SumOK t (ch.Phi a)) (hD : DepthAt ch)
    (hS : FinScalAt ch (C / 16) b) (hC : FinCoefAt ch (C / 16) b) (hDt : FinDatAt ch (C / 16) b) (hG : FinGamAt ch (C / 16) b)
    (hT : FinTopAt ch (C / 16) b) (hR : FinRowAt ch (C / 16) b) (hP : FinPairAt ch (C / 16) b) (hΨ : FinPsiAt ch)
    (hF : FinFormAt F ch (C / 16) b) : FinAt F ch C b := by
  obtain ⟨dS, lS, hS⟩ := hS
  obtain ⟨dC, lC, hC⟩ := hC
  obtain ⟨dD, lD, hDt⟩ := hDt
  obtain ⟨dG, lG, hG⟩ := hG
  obtain ⟨dT, lT, hT⟩ := hT
  obtain ⟨dR, lR, hR⟩ := hR
  obtain ⟨dP, lP, hP⟩ := hP
  obtain ⟨dF, lF, hF⟩ := hF
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hL := loss_comb hm1 lS lC lD lG lT lR lF lP
  have e : (D.R.m : ℝ) * bOne ch.G C b / 2 = 8 * D.R.m * bOne ch.G (C / 16) b := by
    simp only [bOne]
    ring
  refine ⟨_, e ▸ hL, ?_⟩
  intro X' M hM t w hw x hx y hy
  refine exists_intMod_levelPrimePow_eq_add_mul ch (hL.1 w) (hO t) hM (formOf F t x) y hy fun Φ cl hSO u hu => ?_
  have core := core_loss ch hSO (fun β hβ => (hD t Φ β hβ).1) (hC t w hw Φ) (hDt t w hw Φ) (hG t w Φ) (hT t w hw Φ) (hR t w hw Φ)
    (hP w) (psiC (ch.rp.delta cl u)) (fun z => hΨ w cl u hu z) (ch.S.formC t (R.jX t (formOf F t x))) (fun z => hF t w x hx z)
  exact LossLe.mono (loss_mul (hS w) core) (le_of_eq (by ring))

set_option maxHeartbeats 1600000 in

theorem fin_of_factors : SumOKK → DepthK → FinScalK → FinCoefK → FinDatK → FinGamK → FinTopK → FinRowK → FinPairK → FinPsiK →
    FinFormK → FinK := by
  rintro ⟨a0, hO⟩ ⟨a1, hD⟩ ⟨a2, hS⟩ ⟨a3, hC⟩ ⟨a4, hDt⟩ ⟨a5, hG⟩ ⟨a6, hT⟩ ⟨a7, hR⟩ ⟨a8, hP⟩ ⟨a9, hΨ⟩ ⟨a10, hF⟩
  refine ⟨a0 ⊔ a1 ⊔ a2 ⊔ a3 ⊔ a4 ⊔ a5 ⊔ a6 ⊔ a7 ⊔ a8 ⊔ a9 ⊔ a10, fun CF hCF => ?_⟩
  simp only [sup_le_iff] at hCF
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hCF
  obtain ⟨c1, hD⟩ := hD CF h1
  obtain ⟨c2, hS⟩ := hS CF h2
  obtain ⟨c3, hC⟩ := hC CF h3
  obtain ⟨c4, hDt⟩ := hDt CF h4
  obtain ⟨c5, hG⟩ := hG CF h5
  obtain ⟨c6, hT⟩ := hT CF h6
  obtain ⟨c7, hR⟩ := hR CF h7
  obtain ⟨c8, hP⟩ := hP CF h8
  obtain ⟨c9, hΨ⟩ := hΨ CF h9
  obtain ⟨c10, hF⟩ := hF CF h10
  refine ⟨16 * (c1 ⊔ c2 ⊔ c3 ⊔ c4 ⊔ c5 ⊔ c6 ⊔ c7 ⊔ c8 ⊔ c9 ⊔ c10), fun ε C hCC => ?_⟩
  have hCC' : c1 ⊔ c2 ⊔ c3 ⊔ c4 ⊔ c5 ⊔ c6 ⊔ c7 ⊔ c8 ⊔ c9 ⊔ c10 ≤ C / 16 := by linarith
  simp only [sup_le_iff] at hCC'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩, k9⟩, k10⟩ := hCC'
  obtain ⟨x0, hO⟩ := hO ε CF h0
  obtain ⟨x1, hD⟩ := hD ε (C / 16) k1
  obtain ⟨x2, hS⟩ := hS ε (C / 16) k2
  obtain ⟨x3, hC⟩ := hC ε (C / 16) k3
  obtain ⟨x4, hDt⟩ := hDt ε (C / 16) k4
  obtain ⟨x5, hG⟩ := hG ε (C / 16) k5
  obtain ⟨x6, hT⟩ := hT ε (C / 16) k6
  obtain ⟨x7, hR⟩ := hR ε (C / 16) k7
  obtain ⟨x8, hP⟩ := hP ε (C / 16) k8
  obtain ⟨x9, hΨ⟩ := hΨ ε (C / 16) k9
  obtain ⟨x10, hF⟩ := hF ε (C / 16) k10
  refine ⟨x0 ⊔ x1 ⊔ x2 ⊔ x3 ⊔ x4 ⊔ x5 ⊔ x6 ⊔ x7 ⊔ x8 ⊔ x9 ⊔ x10, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j k => ?_⟩
  simp only [sup_le_iff] at hx
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨y0, y1⟩, y2⟩, y3⟩, y4⟩, y5⟩, y6⟩, y7⟩, y8⟩, y9⟩, y10⟩ := hx
  exact fin_at F ch C large₂.sc.b (hO D large₂ he y0 Γ Pl0 T A Ks R F s ch i j) (hD D large₂ he y1 Γ Pl0 T A Ks R F s ch i j k)
    (hS D large₂ he y2 Γ Pl0 T A Ks R F s ch i j k) (hC D large₂ he y3 Γ Pl0 T A Ks R F s ch i j k)
    (hDt D large₂ he y4 Γ Pl0 T A Ks R F s ch i j k) (hG D large₂ he y5 Γ Pl0 T A Ks R F s ch i j k)
    (hT D large₂ he y6 Γ Pl0 T A Ks R F s ch i j k) (hR D large₂ he y7 Γ Pl0 T A Ks R F s ch i j k)
    (hP D large₂ he y8 Γ Pl0 T A Ks R F s ch i j k) (hΨ D large₂ he y9 Γ Pl0 T A Ks R F s ch i j k)
    (hF D large₂ he y10 Γ Pl0 T A Ks R F s ch i j k)

end Main

end GlobalTheory.CompanionTheory.FinDen

end

end

end DenominatorLossAdditivity
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.finiteSumDenominatorBound_of_factor_claims : SumOKK → DepthK → FinScalK → FinCoefK → FinDatK → FinGamK → FinTopK → FinRowK → FinPairK → FinPsiK → FinFormK → FinK := by
  first | exact @DenominatorLossAdditivity.GlobalTheory.CompanionTheory.FinDen.fin_of_factors | exact DenominatorLossAdditivity.GlobalTheory.CompanionTheory.FinDen.fin_of_factors | (intros; apply DenominatorLossAdditivity.GlobalTheory.CompanionTheory.FinDen.fin_of_factors <;> assumption)

end
