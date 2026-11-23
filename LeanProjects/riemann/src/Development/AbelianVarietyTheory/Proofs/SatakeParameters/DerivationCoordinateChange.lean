import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.PolynomialIntegralityJets
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTieAlg
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne

open NumberField MvPowerSeries

noncomputable section

namespace GlobalTheory.Proof.DirectionalDerivative

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets

section Formal

variable {p : ℕ} [Fact p.Prime] {σ κ : Type}

def dirDer [Fintype σ] (v : σ → ℂ_[p]) : MvPowerSeries σ ℂ_[p] →ₗ[ℂ_[p]] MvPowerSeries σ ℂ_[p] :=
  ∑ k, v k • (pderiv ℂ_[p] k).toLinearMap

theorem dirDer_apply [Fintype σ] (v : σ → ℂ_[p]) (G : MvPowerSeries σ ℂ_[p]) :
    dirDer v G = ∑ k, v k • pderiv ℂ_[p] k G := by
  simp [dirDer, LinearMap.sum_apply]

theorem dirDer_add [Fintype σ] (v w : σ → ℂ_[p]) : dirDer (v + w) = dirDer v + dirDer w := by
  simp [dirDer, add_smul, Finset.sum_add_distrib]

theorem dirDer_smul [Fintype σ] (c : ℂ_[p]) (v : σ → ℂ_[p]) : dirDer (c • v) = c • dirDer v := by
  simp [dirDer, Finset.smul_sum, mul_smul]

theorem dirDer_zero [Fintype σ] : dirDer (0 : σ → ℂ_[p]) = 0 := by
  simp [dirDer]

theorem jetAt_zero (F : MvPowerSeries κ ℂ_[p]) : jetAt F 0 = constantCoeff F := by
  simp [jetAt]

theorem jetAt_add_single (F : MvPowerSeries κ ℂ_[p]) (β : κ →₀ ℕ) (x : κ) :
    jetAt F (β + Finsupp.single x 1) = jetAt (pderiv ℂ_[p] x F) β := by
  classical
  have key : ((β + Finsupp.single x 1).prod fun _ n => (n.factorial : ℂ_[p])) =
      (β.prod fun _ n => (n.factorial : ℂ_[p])) * ((β x : ℂ_[p]) + 1) := by
    have h1 := Finsupp.mul_prod_erase' (β + Finsupp.single x 1) x (fun _ n => (n.factorial : ℂ_[p])) (by simp)
    have h2 := Finsupp.mul_prod_erase' β x (fun _ n => (n.factorial : ℂ_[p])) (by simp)
    rw [← h1, ← h2, Finsupp.erase_add, Finsupp.erase_single, add_zero]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
    push_cast
    ring
  unfold jetAt
  rw [key, coeff_pderiv]
  ring

theorem linAt_const [Fintype κ] (c : σ → κ → ℂ_[p]) (k : σ) :
    constantCoeff (∑ x : κ, algebraMap ℂ_[p] (MvPowerSeries κ ℂ_[p]) (c k x) * X x) = 0 := by
  simp

theorem constantCoeff_linAt [Fintype σ] [Fintype κ] (c : σ → κ → ℂ_[p]) (G : MvPowerSeries σ ℂ_[p]) :
    constantCoeff (linAt c G) = constantCoeff G :=
  ModuliIntegralCharts.H1.ExpTieAlg.const_subst0 (linAt_const c) G

theorem pderiv_linAt [Fintype σ] [Fintype κ] (c : σ → κ → ℂ_[p]) (G : MvPowerSeries σ ℂ_[p]) (x : κ) :
    pderiv ℂ_[p] x (linAt c G) = linAt c (dirDer (fun k => c k x) G) := by
  classical
  have ha := ModuliIntegralCharts.H1.ExpTieAlg.hasSubst0 (linAt_const c)
  unfold linAt
  rw [ModuliIntegralCharts.H1.ExpTieAlg.pderiv_subst ha, dirDer_apply, ModuliIntegralCharts.H1.ExpTieAlg.subst_sum' ha]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : pderiv ℂ_[p] x (∑ y : κ, algebraMap ℂ_[p] (MvPowerSeries κ ℂ_[p]) (c k y) * X y) =
      algebraMap ℂ_[p] (MvPowerSeries κ ℂ_[p]) (c k x) := by
    simp only [← Algebra.smul_def, map_sum, Derivation.map_smul]
    rw [Finset.sum_eq_single x]
    · rw [pderiv_X_self, Algebra.algebraMap_eq_smul_one]
    · intro y _ hy
      rw [pderiv_X_of_ne hy, smul_zero]
    · simp
  rw [this, subst_smul ha, Algebra.smul_def, mul_comm]

theorem jetsIntegral_linAt [Fintype σ] [Fintype κ] (c : σ → κ → ℂ_[p]) (Good : MvPowerSeries σ ℂ_[p] → Prop)
    (h0 : ∀ G, Good G → ‖constantCoeff G‖ ≤ 1) (hc : ∀ x G, Good G → Good (dirDer (fun k => c k x) G))
    (G : MvPowerSeries σ ℂ_[p]) (hG : Good G) : JetsIntegral (linAt c G) := by
  classical
  intro α
  induction hn : α.degree generalizing α G with
  | zero =>
    rw [(Finsupp.degree_eq_zero_iff α).1 hn, jetAt_zero, constantCoeff_linAt]
    exact h0 G hG
  | succ n ih =>
    have hα : α ≠ 0 := by rintro rfl; simp at hn
    obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.2 hα
    have hle : Finsupp.single x 1 ≤ α := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hx)
    obtain ⟨β, rfl⟩ : ∃ β, α = β + Finsupp.single x 1 := ⟨α - Finsupp.single x 1, (tsub_add_cancel_of_le hle).symm⟩
    rw [jetAt_add_single, pderiv_linAt]
    refine ih _ (hc x G hG) β ?_
    rw [map_add, Finsupp.degree_single] at hn
    omega

end Formal

section Lattice

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}

theorem exists_lamHom {A : Type} [Field A] [NumberField A] (f : A →+* ℂ) :
    ∃ g : A →+* ℂ_[p], ∀ x, lamC lam (f x) = g x := by
  have hm : ∀ x, f x ∈ Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom f.toRatAlgHom)
  exact ⟨lam.comp (f.codRestrict Qbar hm), fun x => dif_pos (hm x)⟩

def vecY (y : Matrix (Fin N') (Fin N) D.host.E) : D.what₂.Tau × Fin N' × Fin N → ℂ_[p] :=
  fun k => tauEmb D lam k.1 (y k.2.1 k.2.2)

theorem der_eq (y : Matrix (Fin N') (Fin N) D.host.E) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    der D lam y G = dirDer (vecY D lam y) G := by
  rw [dirDer_apply, der]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def]
  congr 1
  ext n
  rw [coeff_pderiv, mul_comm]
  rfl

def derList (l : List (Matrix (Fin N') (Fin N) D.host.E)) :
    Module.End ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :=
  (l.map fun y => (dirDer (vecY D lam y) : Module.End ℂ_[p] _)).prod

theorem foldr_der (l : List (Matrix (Fin N') (Fin N) D.host.E))
    (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    l.foldr (fun y' G => der D lam y' G) G = derList D lam l G := by
  induction l with
  | nil => simp [derList]
  | cons y l ih => rw [List.foldr_cons, ih, der_eq]; simp [derList]

variable (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E))

theorem jetsInt_iff (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    JetsInt D lam Y G ↔ ∀ l : List (Matrix (Fin N') (Fin N) D.host.E), (∀ y ∈ l, y ∈ Y) →
      ‖constantCoeff (derList D lam l G)‖ ≤ 1 := by
  constructor
  · intro h l hl
    have := h l.length l.get fun i => hl _ (List.get_mem l i)
    rwa [List.ofFn_get, foldr_der] at this
  · intro h n y hy
    rw [foldr_der]
    refine h _ fun z hz => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
    exact hy i

def Keeps (v : D.what₂.Tau × Fin N' × Fin N → ℂ_[p]) : Prop :=
  ∀ G, JetsInt D lam Y G → JetsInt D lam Y (dirDer v G)

theorem jetsInt_const {G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]} (h : JetsInt D lam Y G) :
    ‖constantCoeff G‖ ≤ 1 := by
  simpa [derList] using (jetsInt_iff D lam Y G).1 h [] (by simp)

theorem keeps_vecY {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ Y) : Keeps D lam Y (vecY D lam y) := by
  intro G hG
  rw [jetsInt_iff] at hG ⊢
  intro l hl
  have := hG (l ++ [y]) (by
    intro z hz
    rcases List.mem_append.1 hz with h | h
    · exact hl z h
    · rw [List.mem_singleton.1 h]; exact hy)
  simpa [derList] using this

theorem keeps_zero : Keeps D lam Y 0 := by
  intro G _
  rw [jetsInt_iff]
  intro l _
  simp [dirDer_zero]

theorem keeps_add {v w : D.what₂.Tau × Fin N' × Fin N → ℂ_[p]} (hv : Keeps D lam Y v) (hw : Keeps D lam Y w) :
    Keeps D lam Y (v + w) := by
  intro G hG
  have h1 := hv G hG
  have h2 := hw G hG
  rw [jetsInt_iff] at h1 h2 ⊢
  intro l hl
  rw [dirDer_add, LinearMap.add_apply, map_add, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 l hl) (h2 l hl))

theorem keeps_smul {c : ℂ_[p]} (hc : ‖c‖ ≤ 1) {v : D.what₂.Tau × Fin N' × Fin N → ℂ_[p]} (hv : Keeps D lam Y v) :
    Keeps D lam Y (c • v) := by
  intro G hG
  have h1 := hv G hG
  rw [jetsInt_iff] at h1 ⊢
  intro l hl
  rw [dirDer_smul, LinearMap.smul_apply, map_smul, constantCoeff_smul, smul_eq_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (h1 l hl)

end Lattice

section Eigen

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
  {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}

theorem keeps_mmM (M : IntermediateField ℚ ℂ) [NumberField M] (hM : ∀ τ x, embT D τ x ∈ M)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ homL D L L') {m : D.what₂.Tau → M} (hm : m ∈ mmM D M) :
    Keeps D lam (YYl D L L') fun k => lamC lam (m k.1 : ℂ) * vecY D lam A k := by
  obtain ⟨g, hg⟩ := exists_lamHom lam (algebraMap M ℂ)
  have hg' : ∀ x : M, lamC lam (x : ℂ) = g x := hg
  simp only [hg']
  induction hm using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, rfl⟩ := hv
    have hy : a • A ∈ YYl D L L' := Submodule.subset_span ⟨a, ha, A, hA, rfl⟩
    convert keeps_vecY D lam _ hy using 2 with k
    obtain ⟨ρ, hρ⟩ := exists_lamHom lam (embT D k.1)
    have e : ((TaylorLogMetric.liftM M (embT D k.1 a) : M) : ℂ) = embT D k.1 a := by rw [TaylorLogMetric.liftM, dif_pos (hM _ _)]
    rw [← hg', e]
    simp only [vecY, tauEmb, hρ, Matrix.smul_apply, smul_eq_mul]
    rw [map_mul]
  | zero => convert keeps_zero D lam (YYl D L L') using 2; simp
  | add v w _ _ hv hw => convert keeps_add D lam _ hv hw using 2; simp [add_mul]
  | smul c v _ hv =>
    have hc : ‖g (c : M)‖ ≤ 1 :=
      GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int g c.isIntegral_coe)
    convert keeps_smul D lam _ hc hv using 2 with k
    have : (c • v) k.1 = (c : M) * v k.1 := rfl
    rw [this, map_mul, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem exists_smul_mem_homL (ρ : D.host.E →+* ℂ_[p]) (hL : L.FG) {P : Matrix (Fin N) (Fin N) D.host.E}
    {P' : Matrix (Fin N') (Fin N') D.host.E} (hP : LocBasisW D ρ L P) (hP' : LocBasisW D ρ L' P') (a : Fin N) (b : Fin N') :
    ∃ s : D.host.E, ‖ρ s‖ = 1 ∧ (Matrix.of fun i j => s * (P' i b * P⁻¹ a j)) ∈ homL D L L' := by
  classical
  obtain ⟨T, hT⟩ := hL
  obtain ⟨s', hs', hb⟩ := hP'.2.1 b
  have hx : ∀ x : T, ∃ s : 𝓞 D.host.E, ‖ρ (s : D.host.E)‖ = 1 ∧ ∃ c : 𝓞 D.host.E,
      (s : D.host.E) * (P⁻¹.mulVec x) a = c := by
    intro x
    obtain ⟨s, hs, c, hc⟩ := hP.2.2 x (hT ▸ Submodule.subset_span x.2)
    refine ⟨s, hs, c a, ?_⟩
    have h1 : (s : D.host.E) • (x : Fin N → D.host.E) = P.mulVec fun j => (c j : D.host.E) := by
      funext i
      have := congrFun hc i
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply] at this
      simp only [Pi.smul_apply, Matrix.mulVec, dotProduct]
      refine this.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [mul_comm]; rfl
    have h2 : P⁻¹.mulVec ((s : D.host.E) • (x : Fin N → D.host.E)) = fun j => (c j : D.host.E) := by
      rw [h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hP.1), Matrix.one_mulVec]
    rw [Matrix.mulVec_smul] at h2
    exact congrFun h2 a
  choose s hs c hc using hx
  have hall : ∀ x ∈ L, ∃ c : 𝓞 D.host.E, ((∏ t, s t : 𝓞 D.host.E) : D.host.E) * (P⁻¹.mulVec x) a = c := by
    intro x hxL
    rw [← hT] at hxL
    induction hxL using Submodule.span_induction with
    | mem x hx =>
      refine ⟨(∏ t ∈ Finset.univ.erase (⟨x, hx⟩ : T), s t) * c ⟨x, hx⟩, ?_⟩
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx⟩ : T))]
      have := hc ⟨x, hx⟩
      simp only [map_mul, RingOfIntegers.coe_eq_algebraMap] at this ⊢
      rw [mul_assoc, this]
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c1, h1⟩ := hx
      obtain ⟨c2, h2⟩ := hy
      refine ⟨c1 + c2, ?_⟩
      rw [Matrix.mulVec_add, Pi.add_apply, mul_add, h1, h2]
      simp
    | smul r x _ hx =>
      obtain ⟨c1, h1⟩ := hx
      refine ⟨r * c1, ?_⟩
      have : r • x = (r : D.host.E) • x := rfl
      rw [this, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm, h1]
      simp
  refine ⟨((∏ t, s t : 𝓞 D.host.E) : D.host.E) * s', ?_, Submodule.subset_span fun x hxL => ?_⟩
  · rw [map_mul, norm_mul, hs', mul_one]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_prod, norm_prod] at hs ⊢
    exact Finset.prod_eq_one fun t _ => hs t
  · obtain ⟨c1, h1⟩ := hall x hxL
    convert L'.smul_mem c1 hb using 1
    funext i
    have : (c1 • s' • P'.transpose b) i = (c1 : D.host.E) * ((s' : D.host.E) * P' i b) := rfl
    rw [this, ← h1]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem keeps_coordChange (M : IntermediateField ℚ ℂ) [NumberField M] (hM : ∀ τ x, embT D τ x ∈ M)
    (dg : D.what₂.Tau → ℂ) (hdg : ∀ τ, ∃ s : M, (s : ℂ) = dg τ ∧ ellT D M τ = Submodule.span (𝓞 M) {s})
    (c0 : D.what₂.Tau → ℂ_[p]) (hc0 : ∀ τ, ‖c0 τ‖ = 1) (hL : L.FG)
    {P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E} {P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E}
    (hP : ∀ τ, LocBasisW D (tauEmb D lam τ) L (P τ)) (hP' : ∀ τ, LocBasisW D (tauEmb D lam τ) L' (P' τ))
    (x : (Bool × G.HH D) × Fin N × Fin N') :
    Keeps D lam (YYl D L L') fun k => coordChange D lam (fun τ => c0 τ * lamC lam (dg τ)) P P' k x := by
  classical
  set τ := tauPl D x.1 with hτ
  obtain ⟨ρ, hρ⟩ := exists_lamHom lam (embT D τ)
  have hρ' : tauEmb D lam τ = ρ := funext hρ
  obtain ⟨s, hs, hA⟩ := exists_smul_mem_homL D ρ hL (hρ' ▸ hP τ) (hρ' ▸ hP' τ) x.2.1 x.2.2
  obtain ⟨g, hg, hell⟩ := hdg τ
  have hm : g ∈ ellT D M τ := hell ▸ Submodule.mem_span_singleton_self g
  have hk := keeps_mmM D lam M hM hA (Submodule.mem_comap.1 hm)
  have hs0 : ρ s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hs
    exact zero_ne_one hs
  have hn : ‖c0 τ * (ρ s)⁻¹‖ ≤ 1 := by rw [norm_mul, norm_inv, hs, hc0]; simp
  have hinv : ((P τ).map ρ)⁻¹ = ((P τ)⁻¹).map ρ := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit (hP τ).1), Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  convert keeps_smul D lam _ hn hk using 2 with k
  obtain ⟨τ', i, j⟩ := k
  simp only [coordChange, Pi.smul_apply, smul_eq_mul, LinearMap.single_apply, ← hτ]
  split_ifs with h
  · subst h
    simp only [Pi.single_eq_same, hg, vecY, hρ', hinv, Matrix.map_apply, Matrix.of_apply, map_mul]
    field_simp
  · rw [Pi.single_eq_of_ne' h]
    have : lamC lam 0 = 0 := by rw [lamC, dif_pos (zero_mem _)]; exact map_zero lam
    simp [this]

end Eigen

theorem jetInt_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ))
    (hInt : B.IntP χ) (hComb : GL3Theta.kerComb D cc δ (B.eNat χ)) :
    JetInt_at D Dx Tw E cc δ B χ O := by
  intro _ u μ hLev hKer w hw hd hSer i hi c c'
  have hj : JetsIntegral (E.Th u μ w i c c') := by
    obtain ⟨P, hP, hTh⟩ := hSer
    obtain ⟨c0, hc0, hE⟩ := hTh i hi c c'
    have hev : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add ((D.R.t_odd.add_one).mul_left j)
    have hAdm : admitted D _ _ ((O u μ).lat i c).1 ((O u μ).lat (i + 1) c').1 :=
      ⟨hev _, hev _, ((O u μ).lat i c).2, ((O u μ).lat (i + 1) c').2⟩
    have hC := hComb _ _ _ _ _ _ hAdm ((hKer i hi).1 c c') _ (E.lam w) ((not_mem_S hLev w).1 hw)
    have hJ := ((hInt _ (E.lam w) _ _ _ _ hAdm).1 hd _ hC).2.1
    obtain ⟨M, _, hM, hdg⟩ := (O u μ).dgen_gen
    rw [hE]
    exact jetsIntegral_linAt _ _ (fun _ h => jetsInt_const D _ _ h)
      (fun x => keeps_coordChange D (E.lam w) M hM _ hdg c0 hc0 ((O u μ).lat i c).2.1
        (hP i hi.le c) (hP (i + 1) hi c') x) _ hJ
  exact ⟨hj, fun P => polyIntegral_applyAt0 _ _ _ _ hj P, fun I => polyIntegral_applyAt0 _ _ _ _ hj _⟩

theorem jetInt_at_of_famTie (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ))
    (h : FamTie D cc δ χ → B.IntP χ ∧ GL3Theta.kerComb D cc δ (B.eNat χ)) :
    JetInt_at D Dx Tw E cc δ B χ O :=
  fun hF => jetInt_at D Dx Tw E cc δ B χ O (h hF).1 (h hF).2 hF

end GlobalTheory.Proof.DirectionalDerivative
