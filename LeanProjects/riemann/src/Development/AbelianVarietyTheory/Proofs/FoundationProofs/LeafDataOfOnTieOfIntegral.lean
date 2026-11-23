import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistTrivialOnRational
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDetOfMemSt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightOnDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.OrientationExclusive
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TraceLattice

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies GlobalTheory.OnTies
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Trace

variable {K Z P : Type} [Field K] [NumberField K] [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z]
  [IsScalarTower (𝓞 K) K Z] [Group P] (ρ : Representation K P Z) (U : Subgroup P) [Fintype U] (ψ : P → 𝓞 K)

def trace : Z →ₗ[K] Z := ∑ u : U, ((ψ (u : P) : 𝓞 K) : K) • ρ (u : P)⁻¹

theorem trace_apply (y : Z) : trace ρ U ψ y = ∑ u : U, ψ (u : P) • ρ (u : P)⁻¹ y := by
  simp only [trace, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun u _ => algebraMap_smul K _ _

variable {ρ U ψ}

theorem mem_eig_iff {y : Z} : y ∈ eig ρ U ψ ↔ ∀ u : U, ρ (u : P) y = ((ψ (u : P) : 𝓞 K) : K) • y := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem trace_mem_eig (hψ : ∀ a ∈ U, ∀ b ∈ U, ψ (a * b) = ψ a * ψ b) (y : Z) : trace ρ U ψ y ∈ eig ρ U ψ := by
  refine mem_eig_iff.2 fun a => ?_
  simp only [trace, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
  refine (Fintype.sum_equiv (Equiv.mulRight a) _ _ fun u => ?_).symm
  have e : ρ (a : P) (ρ ((u : P) * a)⁻¹ y) = ρ (u : P)⁻¹ y := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, mul_inv_cancel_left]
  rw [Equiv.coe_mulRight, Subgroup.coe_mul, e, hψ _ u.2 _ a.2, smul_smul, mul_comm (ψ u)]
  exact congrArg (· • _) (map_mul (algebraMap (𝓞 K) K) _ _).symm

theorem trace_of_mem_eig (h1 : ψ 1 = 1) (hψ : ∀ a ∈ U, ∀ b ∈ U, ψ (a * b) = ψ a * ψ b) {y : Z} (hy : y ∈ eig ρ U ψ) :
    trace ρ U ψ y = ((Nat.card U : ℕ) : K) • y := by
  simp only [trace, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl (g := fun _ => y) fun u _ => ?_, Finset.sum_const, Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul,
    Finset.card_univ]
  have e : ((ψ (u : P) : 𝓞 K) : K) * ((ψ (u : P)⁻¹ : 𝓞 K) : K) = 1 := by
    have := hψ _ u.2 _ (U.inv_mem u.2)
    rw [mul_inv_cancel, h1] at this
    exact_mod_cast congrArg (fun a : 𝓞 K => (a : K)) this.symm
  have := mem_eig_iff.1 hy u⁻¹
  rw [Subgroup.coe_inv] at this
  rw [this, smul_smul, e, one_smul]

end Trace

variable {D : D7}

def ShortSpanFG {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P6 j) (w : WeightFamilies.Wt D j) : Prop :=
  (X.shortTh w).FG

section Coord

variable {F K : Type} [Field F] [Field K] [NumberField K] [Algebra F K] {n : ℕ}

theorem sum_eq_trace {C : Type} [AddCommGroup C] [Module F C] {z : (Fin n → K) ≃ₗ[K] K ⊗[F] C} {P : Type} [Group P]
    {ρ : Representation K P (Fin n → K)} {U : Subgroup P} [Fintype U] (ψ : P → 𝓞 K) {act : P → C → C}
    (hρ : ∀ g y, ρ g (z.symm (1 ⊗ₜ y)) = z.symm (1 ⊗ₜ act g y)) {f : U → C} {y : C} (hf : ∀ u : U, act u (f u) = y) :
    ∑ᶠ u : U, ψ (u : P) • z.symm (1 ⊗ₜ[F] f u) = trace ρ U ψ (z.symm (1 ⊗ₜ y)) := by
  rw [finsum_eq_sum_of_fintype, trace_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← hf u, ← hρ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem spanK_comap_span_le {R : Type} [AddCommGroup R] [Module F R] [Module (𝓞 F) R] [IsScalarTower (𝓞 F) F R]
    (C : Submodule F R) (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) {s : Set R} (hs : ∀ f ∈ s, f ∈ C)
    {M : Submodule (𝓞 K) (Fin n → K)} (hM : ∀ y : C, y.1 ∈ s → z.symm (1 ⊗ₜ y) ∈ M) :
    spanK z {y : C | y.1 ∈ Submodule.span (𝓞 F) s} ≤ M := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨f, hf⟩, hF, rfl⟩
  change f ∈ Submodule.span (𝓞 F) s at hF
  suffices key : ∃ hf : f ∈ C, z.symm (1 ⊗ₜ (⟨f, hf⟩ : C)) ∈ M from key.2
  clear hf
  induction hF using Submodule.span_induction with
  | mem x hx => exact ⟨hs x hx, hM ⟨x, hs x hx⟩ hx⟩
  | zero =>
    refine ⟨zero_mem _, ?_⟩
    change z.symm (1 ⊗ₜ (0 : C)) ∈ _
    rw [TensorProduct.tmul_zero, map_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    obtain ⟨a, hx⟩ := hx
    obtain ⟨b, hy⟩ := hy
    refine ⟨add_mem a b, ?_⟩
    have := add_mem hx hy
    rwa [← map_add, ← TensorProduct.tmul_add] at this
  | smul r x _ hx =>
    obtain ⟨a, hx⟩ := hx
    have e : r • x = (r : F) • x := (algebraMap_smul F r x).symm
    refine ⟨e ▸ C.smul_mem _ a, ?_⟩
    have e1 : (⟨r • x, e ▸ C.smul_mem _ a⟩ : C) = (r : F) • (⟨x, a⟩ : C) := Subtype.ext e
    rw [e1, TensorProduct.tmul_smul, ← algebraMap_smul K (r : F), map_smul]
    exact M.smul_mem (algebraMap (𝓞 F) (𝓞 K) r) hx

theorem sum_eq_trace_cusp {B : WeightFamilies.Prov D} {j : ℕ} {w : WeightFamilies.Wt D j} [Algebra B.KO K]
    {z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w} {P : Type} [Group P]
    {ρ : Representation K P (Fin n → K)} {U : Subgroup P} [Fintype U] (ψ : P → 𝓞 K) {act : P → B.Cusp j w → B.Cusp j w}
    (hρ : ∀ g y, ρ g (z.symm (1 ⊗ₜ y)) = z.symm (1 ⊗ₜ act g y)) {f : U → B.Cusp j w} {y : B.Cusp j w}
    (hf : ∀ u : U, act u (f u) = y) :
    ∑ᶠ u : U, ψ (u : P) • z.symm (1 ⊗ₜ[B.KO] f u) = trace ρ U ψ (z.symm (1 ⊗ₜ y)) := sum_eq_trace ψ hρ hf

theorem spanK_spanIn_le [NumberField F] {R : ℕ → Type} [∀ j, CommRing (R j)] [∀ j, Algebra F (R j)] [∀ j, Algebra (𝓞 F) (R j)]
    [∀ j, IsScalarTower (𝓞 F) F (R j)] (C : ∀ j, WeightFamilies.Wt D j → Submodule F (R j)) (j : ℕ) (w : WeightFamilies.Wt D j)
    (z : (Fin n → K) ≃ₗ[K] K ⊗[F] cutR C j w) {s : Set (R j)} (hs : ∀ f ∈ s, f ∈ cutR C j w)
    {M : Submodule (𝓞 K) (Fin n → K)} (hM : ∀ y : cutR C j w, y.1 ∈ s → z.symm (1 ⊗ₜ y) ∈ M) :
    spanK z (spanIn C j w s : Set (cutR C j w)) ≤ M := spanK_comap_span_le _ z hs hM

theorem spanK_fg_cusp {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} {X : WeightAlgebra.PJ D B P6 j} {w : WeightFamilies.Wt D j} [Algebra B.KO K]
    (z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w) (h : ShortSpanFG X w) : (spanK z (X.shortTh w : Set _)).FG :=
  spanK_fg_of_fg z h

end Coord

section Forms

variable {T : Full D} {h : LawsP T.toTop} {j : ℕ} {w : WeightFamilies.Wt D j} {K : Type} [Field K] [NumberField K]
  [Algebra (recB h.toLawsCore).KO K] {n : ℕ}
  {z : (Fin n → K) ≃ₗ[K] K ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp j w} {P : Type} [Group P]
  {ρ : Representation K P (Fin n → K)} {U : Subgroup P} [Fintype U] {ψ : P → 𝓞 K}
  {ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)}
  {act : P → (recB h.toLawsCore).Cusp j w → (recB h.toLawsCore).Cusp j w}

theorem thetaEig_le_eig (hT : LawsFull T) (hj : InR D j) (hxi : TwistTrivialOnRational T j) (hn : w.n = D.R.nV)
    (hρ : ∀ g F, ρ g (z.symm (1 ⊗ₜ F)) = z.symm (1 ⊗ₜ act g F)) (hact : IsLevAct T.toTop h j w ℓ act)
    (hdet : ∀ u ∈ U, DetOne (ℓ u)) (hψ : ∀ a ∈ U, ∀ b ∈ U, ψ (a * b) = ψ a * ψ b) :
    thetaEig h j w z U ψ ℓ ≤ (eig ρ U ψ).restrictScalars (𝓞 K) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, ⟨Λ, N, x₀, Q, x, h1, h2, h3, h4, h5, h6, h7⟩, rfl⟩
  have hG : GoodDatum T.toTop j w Λ N Q := ⟨h1, h2, h3, h4, h6⟩
  obtain ⟨f₀, s₀⟩ := exists_isSeries hT.sh hj hG (x := x₀) (by simpa [hn] using h5)
  have key : ∀ u : U, ((act u (f u)).1 : T.R j) = f₀ := fun u => (hact _ _).trans
    (mv_series T hT hj hxi (hn ▸ Nat.le_add_right _ _) (hdet _ u.2) hG (h7 u).1
      ⟨by simpa [hn] using (h7 u).2.1, (cutR_le T.C _ _ (f u).2).1, (h7 u).2.2⟩ s₀)
  have e := sum_eq_trace_cusp ψ hρ (f := f) (y := act (1 : U) (f 1)) fun u => Subtype.ext ((key u).trans (key 1).symm)
  exact (congrArg (· ∈ eig ρ U ψ) e).mpr (trace_mem_eig hψ _)

theorem trace_gen_mem (hT : LawsFull T) (hj : InR D j) (hxi : TwistTrivialOnRational T j) (hn : w.n = D.R.nV)
    (hρ : ∀ g F, ρ g (z.symm (1 ⊗ₜ F)) = z.symm (1 ⊗ₜ act g F)) (hact : IsLevAct T.toTop h j w ℓ act)
    (hdet : ∀ u ∈ U, DetOne (ℓ u)) (hc : ∀ f ∈ T.toTop.sh j w, f ∈ cutR T.C j w)
    (F : (recB h.toLawsCore).Cusp j w) (hF : (F.1 : T.R j) ∈ T.toTop.sh j w) :
    trace ρ U ψ (z.symm (1 ⊗ₜ F)) ∈ thetaEig h j w z U ψ ℓ := by
  obtain ⟨hs, Λ, N, x₀, Q, h1, h2, h3, h4, h5, h6, h7⟩ := hF
  have hG : GoodDatum T.toTop j w Λ N Q := ⟨h1, h2, h3, h4, h6⟩
  choose x hx ax using fun u : U => exists_rightMul (ℓ u) h5
  choose f hf using fun u : U => exists_isSeries hT.sh hj hG (ax u)
  let f' : U → (recB h.toLawsCore).Cusp j w := fun u => ⟨f u, hc _ ((hf u).mem_sh hG)⟩
  rw [← sum_eq_trace_cusp ψ hρ (f := f') fun u => Subtype.ext ((hact _ _).trans
    (mv_series T hT hj hxi (hn ▸ Nat.le_add_right _ _) (hdet _ u.2) hG (hx u) (hf u) ⟨h5, hs, h7⟩))]
  exact Submodule.subset_span ⟨f', ⟨Λ, N, x₀, Q, x, h1, h2, h3, h4, by simpa [hn] using h5, h6,
    fun u => ⟨hx u, by simpa [hn] using ax u, (hf u).2.2⟩⟩, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem trace_mem_thetaEig (hT : LawsFull T) (hj : InR D j) (hxi : TwistTrivialOnRational T j) (hn : w.n = D.R.nV)
    (hl : w.LastPos) (hρ : ∀ g F, ρ g (z.symm (1 ⊗ₜ F)) = z.symm (1 ⊗ₜ act g F)) (hact : IsLevAct T.toTop h j w ℓ act)
    (hdet : ∀ u ∈ U, DetOne (ℓ u)) {y : Fin n → K} (hy : y ∈ spanK z ((recPJ h j hj).shortTh w : Set _)) :
    trace ρ U ψ y ∈ thetaEig h j w z U ψ ℓ := by
  have hl' := ((GlobalTheory.WeightOnDatum.weight_on_datum D T.toCore h.pins j hj w).2.2.1 hl).1
  have hc : ∀ f ∈ T.toTop.sh j w, f ∈ cutR T.C j w := fun f hf => by
    rw [cutR_eq T.C hj]
    exact hT.sh.shCusp j hj _ _ (dom_wtA w) hl' (dom_wtA w) hl' hf
  letI : Algebra T.Q.c.F K := ‹Algebra (recB h.toLawsCore).KO K›
  exact spanK_spanIn_le T.C j w z hc
    (M := (thetaEig h j w z U ψ ℓ).comap ((trace ρ U ψ).restrictScalars (𝓞 K)))
    (fun F hF => trace_gen_mem hT hj hxi hn hρ hact hdet hc F hF) hy

end Forms

section Main

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}

def DetOneOn {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (U : Subgroup G)
    (ℓ : G → (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)) : Prop :=
  ∀ u ∈ U, DetOne (ℓ u)

theorem clauses_of_onTie {T : Full D} [Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
    {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
    {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
    {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {inc : P →* G}
    {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
    {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
    {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}
    (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (hT : LawsFull T)
    (hxi : TwistTrivialOnRational T ((ι : ℕ) + 1)) (hn : (κ ι).n = D.R.nV) (hl : (κ ι).LastPos) (hdet : DetOneOn U ℓ)
    (hfg : (O.ThK v i).FG) :
    (O.Th0 v i).FG ∧ O.Th0 v i ≤ (eig (O.ρ i) O.U O.ψ).restrictScalars (𝓞 D.what₂.LL) ∧
      sc ((Nat.card O.U : ℕ) : D.what₂.LL) (cut (eig (O.ρ i) O.U O.ψ) (O.ThK v i)) ≤ O.Th0 v i := by
  haveI := Fintype.ofFinite O.U
  have hU : ∀ u ∈ O.U, inc u ∈ U := fun u hu => by rwa [t.U_eq] at hu
  have h1 : O.ψ 1 = 1 := RingOfIntegers.ext ((t.ψ_eq 1 (hU 1 (one_mem _))).trans (by
    rw [show (⟨inc 1, hU 1 (one_mem _)⟩ : U) = 1 from Subtype.ext (map_one inc), map_one]; rfl))
  have hψ : ∀ a ∈ O.U, ∀ b ∈ O.U, O.ψ (a * b) = O.ψ a * O.ψ b := fun a ha b hb =>
    RingOfIntegers.ext ((t.ψ_eq _ (hU _ (mul_mem ha hb))).trans (by
      rw [show (⟨inc (a * b), hU _ (mul_mem ha hb)⟩ : U) = ⟨inc a, hU a ha⟩ * ⟨inc b, hU b hb⟩ from
        Subtype.ext (map_mul inc a b), map_mul, Units.val_mul, ← t.ψ_eq a, ← t.ψ_eq b]
      exact (map_mul (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) _ _).symm))
  have hd : ∀ u ∈ O.U, DetOne (ℓ (inc u)) := fun u hu => hdet _ (hU u hu)
  refine ⟨hfg.of_le (t.Th0_le_ThK hn), ?_, ?_⟩
  · rw [t.Th0_eq]
    exact thetaEig_le_eig hT (inR_succ ι) hxi hn t.rho_eq t.act_eq hd hψ
  · rintro _ ⟨x, ⟨hx, he⟩, rfl⟩
    rw [t.ThK_eq] at hx
    rw [t.Th0_eq]
    have := trace_mem_thetaEig (ψ := O.ψ) hT (inR_succ ι) hxi hn hl t.rho_eq t.act_eq hd hx
    rwa [trace_of_mem_eig h1 hψ he] at this

variable (A) in

def TiedAt (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (O : OnObj S P oc) (inc : P →* G) (U : Subgroup G)
    (ψ : U →* D.what₂.LLˣ)
    (Q : ∀ (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ), WeightAlgebra.PJ D B P6 j → ℕ → (ka wL wF : WeightFamilies.Wt D j) → ℕ → Prop)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Bs.J) : Prop :=
  ∃ (T : Full D) (_ : Algebra T.J.Q.c.F D.what₂.LL) (R : RealDat D A T.J.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (p : ℕ) (ι : Fin D.R.m) (wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)) (nT : ℕ),
    ∃ z act ℓ ph y, OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y ∧ LawsFull T ∧
      TwistTrivialOnRational T ((ι : ℕ) + 1) ∧ (κ ι).n = D.R.nV ∧ (κ ι).LastPos ∧ DetOneOn U ℓ ∧
      Q _ _ _ (recPJ h ((ι : ℕ) + 1) (inR_succ ι)) p (κ ι) wL wF nT

variable {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {O : OnObj S P oc} {inc : P →* G} {U : Subgroup G}
  {ψ : U →* D.what₂.LLˣ}

theorem leafData_of_onTie
    (H : AtPair S fun v => ∀ i, TiedAt A hinj EX O inc U ψ (fun _ _ _ X _ ka _ _ _ => ShortSpanFG X ka) v i) :
    LeafData O := by
  have key : ∀ v i, TiedAt A hinj EX O inc U ψ (fun _ _ _ X _ ka _ _ _ => ShortSpanFG X ka) v i →
      (O.Th0 v i).FG ∧ O.Th0 v i ≤ (eig (O.ρ i) O.U O.ψ).restrictScalars (𝓞 D.what₂.LL) ∧
        sc ((Nat.card O.U : ℕ) : D.what₂.LL) (cut (eig (O.ρ i) O.U O.ψ) (O.ThK v i)) ≤ O.Th0 v i := by
    rintro v i ⟨T, _, R, κ, v₀, h, fw, p, ι, wL, wF, nT, z, act, ℓ, ph, y, t, hT, hxi, hn, hl, hdet, hfg⟩
    exact clauses_of_onTie t hT hxi hn hl hdet (t.ThK_eq ▸ spanK_fg_cusp z hfg)
  exact fun w hw => ⟨fun i => key w i ((H w hw).1 i), fun i => key _ i ((H w hw).2 i)⟩

theorem leafData_of_onTie_of_leafSpan (hS : LeafSpan O)
    (H : AtPair S fun v => ∀ i, TiedAt A hinj EX O inc U ψ (fun _ _ _ _ _ _ _ _ _ => True) v i) : LeafData O := by
  have key : ∀ v i, TiedAt A hinj EX O inc U ψ (fun _ _ _ _ _ _ _ _ _ => True) v i → (O.ThK v i).FG →
      (O.Th0 v i).FG ∧ O.Th0 v i ≤ (eig (O.ρ i) O.U O.ψ).restrictScalars (𝓞 D.what₂.LL) ∧
        sc ((Nat.card O.U : ℕ) : D.what₂.LL) (cut (eig (O.ρ i) O.U O.ψ) (O.ThK v i)) ≤ O.Th0 v i := by
    rintro v i ⟨T, _, R, κ, v₀, h, fw, p, ι, wL, wF, nT, z, act, ℓ, ph, y, t, hT, hxi, hn, hl, hdet, -⟩ hfg
    exact clauses_of_onTie t hT hxi hn hl hdet hfg
  exact fun w hw => ⟨fun i => key w i ((H w hw).1 i) ((hS w hw).1 i).2.1,
    fun i => key _ i ((H w hw).2 i) ((hS w hw).2 i).2.1⟩

theorem leafData_of_onTie_of_integral
    (H : AtPair S fun v => ∀ i, TiedAt A hinj EX O inc U ψ (fun B _ j X p ka wL wF nT => 0 < p ∧
      Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt B j ka ∧ WeightAlgebra.H2 X (scalOfP B hinj EX p ka wL wF nT) ka wL wF) v i) : LeafData O := by
  have key : ∀ v i, TiedAt A hinj EX O inc U ψ (fun B _ j X p ka wL wF nT => 0 < p ∧
      Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt B j ka ∧ WeightAlgebra.H2 X (scalOfP B hinj EX p ka wL wF nT) ka wL wF) v i →
      TiedAt A hinj EX O inc U ψ (fun _ _ _ X _ ka _ _ _ => ShortSpanFG X ka) v i := by
    rintro v i ⟨T, _, R, κ, v₀, h, fw, p, ι, wL, wF, nT, z, act, ℓ, ph, y, t, hT, hxi, hn, hl, hdet, hp, hL, hH⟩
    exact ⟨T, _, R, κ, v₀, h, fw, p, ι, wL, wF, nT, z, act, ℓ, ph, y, t, hT, hxi, hn, hl, hdet,
      shortTh_fg _ hinj EX hp _ _ _ _ hL hH⟩
  exact leafData_of_onTie fun w hw => ⟨fun i => key w i ((H w hw).1 i), fun i => key _ i ((H w hw).2 i)⟩

end Main

section Pins

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section One

variable {T : Full D} [Algebra T.J.Q.c.F D.what₂.LL]

def HalfPin (R : RealDat D A T.J.Q.c.F) : Prop := T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal

def UnipPin (R : RealDat D A T.J.Q.c.F) (U : Subgroup G) : Prop :=
  ∀ g, g ∈ U ↔ ∀ PP : R.Pg, R.eG g PP ∈ unip (kP PP.1) D.R.r

variable {R : RealDat D A T.J.Q.c.F} {ι : Fin D.R.m}

theorem detOneOn_of_pins (hT : LawsFull T)
    {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
    (hℓ : LevelPin R ι ℓ) (hH : HalfPin R) {U : Subgroup G} (hU : UnipPin R U) : DetOneOn U ℓ := fun u hu =>
  detOne_of_levelPin hT hℓ hH fun PP => by
    rw [Matrix.det_of_upperTriangular fun _ _ h => ((hU u).1 hu PP).1 h]
    exact Finset.prod_eq_one fun a _ => ((hU u).1 hu PP).2 a

theorem twistTrivial_of_runPin (hT : LawsFull T) {n : ℕ} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {p : ℕ}
    (hR : RunPin R ι n v p) : TwistTrivialOnRational T ((ι : ℕ) + 1) := by
  obtain ⟨-, -, -, χ, hχ, hx⟩ := hR
  unfold TwistTrivialOnRational
  rw [hT.p.spaceW _ (inR_succ ι) _ T.toCore.good_σ₀]
  intro γ hγ
  obtain ⟨a, ha⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D ι)).2.2.1 γ hγ
  exact Units.ext ((hx γ _ ha).trans (by rw [hχ.1.2]; rfl))

end One

variable {L : SizeData₂ D} {Pm : ParameterChoice' D L}

theorem kaR_lastPos (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) : (kaR Tp hK j).LastPos := by
  intro τ i hi
  have h1 := GlobalTheory.DepthBoundProbe.kappa_last Tp hK hj τ i hi
  have h2 : (1 : ℤ) ≤ Tp.TO := by have := Tp.TO_40; omega
  have : (1 : ℤ) ≤ ((kaR Tp hK j).aP τ i : ℤ) := by nlinarith
  exact_mod_cast this

variable {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}

variable (A) in

def PinnedAt (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (O : OnObj S P oc) (inc : P →* G) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ)
    (Q : ∀ (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ), WeightAlgebra.PJ D B P6 j → ℕ → (ka wL wF : WeightFamilies.Wt D j) → ℕ → Prop)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Bs.J) : Prop :=
  ∃ (T : Full D) (_ : Algebra T.J.Q.c.F D.what₂.LL) (R : RealDat D A T.J.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (p : ℕ) (ι : Fin D.R.m) (wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)) (nT : ℕ),
    ∃ z act ℓ ph y, OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y ∧ LawsFull T ∧
      κ ι = kaR Tp hK ((ι : ℕ) + 1) ∧ RunPin R ι (κ ι).n v p ∧ LevelPin R ι ℓ ∧ HalfPin R ∧ UnipPin R U ∧
      Q _ _ _ (recPJ h ((ι : ℕ) + 1) (inR_succ ι)) p (κ ι) wL wF nT

variable {Tp : ParamsT D L Pm} {hK : DV.KapDef D} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {O : OnObj S P oc}
  {inc : P →* G} {U : Subgroup G} {ψ : U →* D.what₂.LLˣ}

theorem PinnedAt.tiedAt {Q v i} (H : PinnedAt A Tp hK hinj EX O inc U ψ Q v i) : TiedAt A hinj EX O inc U ψ Q v i := by
  obtain ⟨T, _, R, κ, v₀, h, fw, p, ι, wL, wF, nT, z, act, ℓ, ph, y, t, hT, hκ, hR, hℓ, hH, hU, hQ⟩ := H
  exact ⟨T, _, R, κ, v₀, h, fw, p, ι, wL, wF, nT, z, act, ℓ, ph, y, t, hT, twistTrivial_of_runPin hT hR,
    hκ ▸ kaWt_n _ _ _ _, hκ ▸ kaR_lastPos Tp hK (inR_succ ι), detOneOn_of_pins hT hℓ hH hU, hQ⟩

theorem leafData_of_pins
    (H : AtPair S fun v => ∀ i, PinnedAt A Tp hK hinj EX O inc U ψ (fun _ _ _ X _ ka _ _ _ => ShortSpanFG X ka) v i) :
    LeafData O :=
  leafData_of_onTie fun w hw => ⟨fun i => ((H w hw).1 i).tiedAt, fun i => ((H w hw).2 i).tiedAt⟩

theorem leafData_of_pins_of_leafSpan (hS : LeafSpan O)
    (H : AtPair S fun v => ∀ i, PinnedAt A Tp hK hinj EX O inc U ψ (fun _ _ _ _ _ _ _ _ _ => True) v i) : LeafData O :=
  leafData_of_onTie_of_leafSpan hS fun w hw => ⟨fun i => ((H w hw).1 i).tiedAt, fun i => ((H w hw).2 i).tiedAt⟩

theorem leafData_of_pins_of_integral
    (H : AtPair S fun v => ∀ i, PinnedAt A Tp hK hinj EX O inc U ψ (fun B _ j X p ka wL wF nT => 0 < p ∧
      Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt B j ka ∧ WeightAlgebra.H2 X (scalOfP B hinj EX p ka wL wF nT) ka wL wF) v i) : LeafData O :=
  leafData_of_onTie_of_integral fun w hw => ⟨fun i => ((H w hw).1 i).tiedAt, fun i => ((H w hw).2 i).tiedAt⟩

end Pins

end GlobalTheory.TraceLattice
