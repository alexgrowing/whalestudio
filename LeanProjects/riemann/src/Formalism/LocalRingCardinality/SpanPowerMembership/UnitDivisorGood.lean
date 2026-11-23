import Formalism.LocalRingCardinality.SpanPowerMembership.TrivialLocalDataRank
import Formalism.CyclotomicNorms.StatementT

noncomputable section

namespace Formalism.BasicNotions.Examples₂.ND

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

variable (Tau : Type) [Fintype Tau]

abbrev period2 : PeriodMap R0 (chain1 Tau) where
  Mt := ℂ
  Wz := ℂ
  evz := cst.symm.toLinearMap
  Wrow := ℂ
  lowerMap := LinearMap.id
  period := LinearMap.mul ℂ ℂ

theorem chain1_K (i : ℕ) (z : ℂ) : (chain1 Tau).K i (fun _ _ => z) = fun _ _ => z := by
  funext _ _
  simp [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, ColumnChain.Kmap, ColumnChain.divDe, ColumnChain.sharp, mulFun,
    chain1_wt]

theorem chain1_col (z : ℂ) : (chain1 Tau).col (fun _ _ => z) = fun _ _ => z := by
  show (chain1 Tau).K 1 ((chain1 Tau).K 0 (fun _ _ => z)) = _
  rw [chain1_K, chain1_K]

theorem period2_PtilCol (z F : ℂ) : (period2 Tau).PtilCol (fun _ _ => z) F = z * F := by
  show ((chain1 Tau).col (fun _ _ => z)) () () * F = z * F
  rw [chain1_col]

def oneOLat {O : Type} [CommRing O] (φ : O →+* ℂ) : Rows.OLat O φ ℂ :=
  ⟨{1}, by rw [Finset.coe_singleton]; exact span_one_C⟩

section Rows

variable (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (hTau : Fintype.card Tau = R0.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)
  (eo : ℂ) (heo : eo = 0 ∨ eo = 1)

def slL : LL →ₛₗ[embLL] ℂ where
  toFun x := embLL x
  map_add' x y := map_add _ _ _
  map_smul' c x := by simp

include heo in
theorem smul_id_idem : (eo • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) ∘ₗ (eo • LinearMap.id) = eo • LinearMap.id := by
  rcases heo with rfl | rfl <;> simp

include heo in
theorem smul_id_sa : (eo • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).IsSymmetric := by
  intro x y
  rcases heo with rfl | rfl <;> simp

theorem slL_basis (b : Module.Basis (Module.Free.ChooseBasisIndex LL LL) LL LL) :
    LinearIndependent ℂ (fun i => slL LL embLL (b i)) ∧
      Submodule.span ℂ (Set.range (fun i => slL LL embLL (b i))) = ⊤ := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex LL LL) = 1 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, Module.finrank_self]
  obtain ⟨i0, hi0⟩ := Fintype.card_eq_one_iff.mp hcard
  have : Subsingleton (Module.Free.ChooseBasisIndex LL LL) := ⟨fun a b => (hi0 a).trans (hi0 b).symm⟩
  have hne : slL LL embLL (b i0) ≠ 0 := (map_ne_zero embLL).mpr (b.ne_zero i0)
  refine ⟨LinearIndependent.of_subsingleton i0 hne, ?_⟩
  rw [eq_top_iff]
  intro z _
  have hz : z = (z / slL LL embLL (b i0)) • slL LL embLL (b i0) := by
    rw [smul_eq_mul, div_mul_cancel₀ _ hne]
  rw [hz]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i0, rfl⟩)

abbrev baseRankLevelData : Rows.Data R0 :=
  { toyRowsOfNumberField LL embLL P Tau hTau Dst sha hsha cg hcg with
    EE := ℂ
    instEE := inferInstance
    instEEi := inferInstance
    instEEf := inferInstance
    Drows := 1
    onb := OrthonormalBasis.singleton (Fin 1) ℂ
    Dall := 1
    D_eq := by simp
    EE0 := ℂ
    instEE0 := inferInstance
    instEE0i := inferInstance
    instEE0f := inferInstance
    D0 := 1
    onb0 := OrthonormalBasis.singleton (Fin 1) ℂ
    FT := Unit
    instFT := inferInstance
    instFTd := inferInstance
    ft := fun _ => ()
    ft0 := fun _ => ()
    Amb := fun _ => ℂ
    instAmb := fun _ => inferInstance
    instAmbi := fun _ => inferInstance
    instAmbf := fun _ => inferInstance
    Mult := fun _ _ => ℂ
    instMult := fun _ _ => inferInstance
    instMulti := fun _ _ => inferInstance
    instMultf := fun _ _ => inferInstance
    multZero := fun _ => LinearIsometryEquiv.refl ℂ ℂ
    multTop := fun _ => LinearIsometryEquiv.refl ℂ ℂ
    io := fun _ _ => LinearMap.id
    Mtilde := fun _ => oneOLat _
    eOp := fun _ => eo • LinearMap.id
    eOp_idem := fun _ => smul_id_idem eo heo
    eOp_sa := fun _ => smul_id_sa eo heo
    Mu := fun _ => ℂ
    instMu := fun _ => inferInstance
    instMui := fun _ => inferInstance
    instMuf := fun _ => inferInstance
    perCol := fun _ _ φ F => (period2 Tau).PtilCol (fun _ _ => φ) F
    Bu := fun _ φ F => φ * F
    Mj := fun _ => ℂ
    instMj := fun _ => inferInstance
    instMji := fun _ => inferInstance
    instMjf := fun _ => inferInstance
    MjLat := fun _ => oneOLat _
    Mt := fun _ _ => ℂ
    instMt := fun _ _ => inferInstance
    instMti := fun _ _ => inferInstance
    instMtf := fun _ _ => inferInstance
    MtLat := fun _ _ => oneOLat _
    MtL := fun _ _ => LL
    instMtL := fun _ _ => inferInstance
    instMtLm := fun _ _ => inferInstance
    jMt := fun _ _ => slL LL embLL
    jMt_basis := fun _ _ b => slL_basis LL embLL b
    MtLat_sub := fun _ _ x hx => ⟨1, by
      rw [Finset.mem_singleton.mp hx]; exact map_one embLL⟩
    eMt := fun _ _ => eo • LinearMap.id
    eMt_idem := fun _ _ => smul_id_idem eo heo
    eMt_sa := fun _ _ => smul_id_sa eo heo
    eMt_LL := fun _ _ x => by rcases heo with rfl | rfl <;> [exact ⟨0, by simp⟩; exact ⟨x, by simp⟩]
    thetaP := fun _ _ => LinearMap.id
    isot := fun _ _ => ⊤
    lamP := fun _ _ _ => 1 }

end Rows

section Div

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def bk2 : (Fin 1 → K) →ₗ[K] Module.Dual K (Fin 1 → K) :=
  LinearMap.mk₂ K (fun φ x => φ 0 * x 0) (by intros; simp [add_mul]) (by intros; simp [mul_assoc])
    (by intros; simp [mul_add]) (by intros; simp; ring)

abbrev div2 : DivData K Unit :=
  { toyZeroLatticeDatum K with
    RR := oneHLat K
    Nu := fun _ => oneHLat K
    Bk := fun _ => bk2 K
    h := fun _ => 0
    HH := sFrame (fun _ : Unit => oneHLat K) (fun _ => 0) + (oneHLat K).muMax
    HH_ge := le_refl _
    Dall := 1 }

theorem unitDivisor_good : (div2 K).RR.Good ∧ ∀ u, ((div2 K).Nu u).Good :=
  ⟨oneHLat_good K, fun _ => oneHLat_good K⟩

end Div

section S

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (sig : E →ₐ[F] E) {Word Tau : Type} [Subsingleton Word] (hc : Word → Tau → HCParam R)

abbrev sData2 (Del : ℚ) (hDel : 0 < Del)
    (hgap : ∀ (w : Word) (τ : Tau) (l : ℕ) (h : l + 1 < R.k - 1),
      (hc w τ).v ⟨l, by omega⟩ - (hc w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (hlet : ∀ (w : Word) (τ : Tau) (l : ℕ) (h : l < R.k - 2),
      (hc w τ).u ⟨l + 1, by omega⟩ = (hc w τ).v ⟨l, by omega⟩ - 1 / 2)
    (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc :=
  { toySData sig hc Del hDel hgap hlet loc with
    HH := ℂ
    hhN := inferInstance
    hhI := inferInstance
    hhF := inferInstance
    Cu := fun _ => ℂ
    cuN := fun _ => inferInstance
    cuI := fun _ => inferInstance
    cuF := fun _ => inferInstance
    Pu := fun _ => ContinuousLinearMap.id ℂ ℂ
    aTerm := fun _ _ t => t.elim }

end S

def conjLI : ℂ →ₗᵢ⋆[ℂ] ℂ :=
  ⟨{ toFun := starRingEnd ℂ, map_add' := map_add _, map_smul' := fun c z => by simp }, fun z => by simp⟩

section Forms

variable (Tau : Type) [Fintype Tau] (T : ℕ) [hT : Fact T.Prime]
  {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (embLL : LL →+* ℂ)
  (Pl : Rows.Places LL) (hTau : Fintype.card Tau = R0.f) (Dst : ℝ) (hD : 0 < Dst)

def forms2 : MemberForms LL embLL Pl Tau (fun _ => hc0) (chain1 Tau) (baseColumnsAt Tau T Dst hD)
    (period2 Tau) :=
  { forms1 Tau T embLL Pl hTau Dst hD with }

theorem forms2_ipC (φ ψ : FU) :
    (forms2 Tau T embLL Pl hTau Dst hD).ipC 0 φ ψ = starRingEnd ℂ (φ () ()) * ψ () () :=
  forms1_ipC Tau T embLL Pl hTau Dst hD φ ψ

end Forms

open Polynomial in
theorem not_isGood_const {N g : ℕ} [Fact g.Prime] {PP J : Type} (f : (ZMod g)[X])
    (χ : PP → J → (ZMod g)ˣ) : ¬ Formalism.CyclotomicNorms.IsGood N g (fun _ : PP => f) χ := by
  rintro ⟨h1, -, -, -, h4, v, q, -, ⟨s, hs'⟩, -, hN, hN3⟩
  have hs : f = q * s := hs'
  have hf0 : f ≠ 0 := (h1 v).1.ne_zero
  have hfN : f.natDegree = N := (h1 v).2.1
  have hq0 : q ≠ 0 := fun h => hf0 (by rw [hs, h, zero_mul])
  have hs0 : s ≠ 0 := fun h => hf0 (by rw [hs, h, mul_zero])
  have hdeg : f.natDegree = q.natDegree + s.natDegree := by
    conv_lhs => rw [hs]
    exact natDegree_mul hq0 hs0
  obtain ⟨_, hv'⟩ := h4 s.natDegree (by omega) (by omega)
  exact hv' ⟨s, ⟨q, by rw [mul_comm]; exact hs⟩, rfl⟩

end Formalism.BasicNotions.Examples₂.ND
