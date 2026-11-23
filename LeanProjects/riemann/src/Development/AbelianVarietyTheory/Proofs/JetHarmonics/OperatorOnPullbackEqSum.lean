import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisation
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedNormalisation
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenMul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowMulEqOne
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGenerators

open TorusExt

attribute [local instance] gtGroup

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem exists_lift (hG : GlobalFnsSt) (hB : D.TauBimult) (oa : D.OAct O) (a : O) (N k : ℕ)
    (haa : a * star a = (N : O)) (u v : O) (huv : u * N + v * k = 1) (p : QkPt D F k) :
    ∃ (p' : QkPt D F k) (p₁ : QkPt D F (k * N)), QkPt.Equiv D F p p' ∧ GtAct oa a p₁.g p'.g ∧
      p₁.y = star a • p'.y ∧ ∀ b : O, QkPt.Equiv D F (qkZero hB F k) (qkSmul hB hG oa b p) →
        QkPt.Equiv D F (qkZero hB F (k * N)) (qkSmul hB hG oa b p₁) := by
  letI := gtModule hG oa F
  have hs : ∀ (c : O) (g : GtPtF D F), gtSmul hG oa c g = c • g := fun _ _ => rfl
  have hι : ∀ (c : O) (y : D.X), iota hB F (c • y) = c • iota hB F y := iota_smul hG oa hB
  have hp : (k : O) • p.g = iota hB F p.y := by rw [Nat.cast_smul_eq_nsmul]; exact qk_nsmul hB p
  have e : u * N = 1 + k * -v := by linear_combination huv
  refine ⟨qkSmul hB hG oa (u * N) p, qkMk hB (star a • (u * N) • p.y) ((u * star a) • p.g) ?_, ?_, ?_, rfl, ?_⟩
  · rw [hι, hι, ← hp, ← Nat.cast_smul_eq_nsmul O, smul_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  · refine (equiv_iff hB _ _).2 ⟨(-v) • p.y, ?_, ?_⟩
    · show (u * N) • p.y = p.y + k • (-v) • p.y
      rw [e, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul]
    · show (u * N) • p.g = p.g + iota hB F ((-v) • p.y)
      rw [hι, ← hp, e, add_smul, one_smul, mul_comm, mul_smul]
  · refine (gtAct_iff_eq_gtSmul hG oa _ _ _).2 ?_
    show (u * N) • p.g = a • (u * star a) • p.g
    rw [smul_smul, ← haa]
    congr 1
    ring
  · intro b hb
    obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 hb
    have hy' : b • p.y = (k : O) • z := by
      rw [Nat.cast_smul_eq_nsmul]; exact hy.trans (zero_add _)
    have hg' : b • p.g = iota hB F z := hg.trans (zero_add _)
    refine (equiv_iff hB _ _).2 ⟨(u * star a) • z, ?_, ?_⟩
    · show b • star a • (u * N) • p.y = 0 + (k * N) • (u * star a) • z
      rw [zero_add, smul_comm b, smul_comm b, hy', ← Nat.cast_smul_eq_nsmul O, smul_smul, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    · show b • (u * star a) • p.g = 0 + iota hB F ((u * star a) • z)
      rw [zero_add, smul_comm b, hg', hι]

theorem killed_iff (hG : GlobalFnsSt) (hB : D.TauBimult) (oa : D.OAct O) {k : ℕ} {G : Type} [Group G]
    (f : QkPt D F k → G) (act : O → G → G) (h₁ : ∀ p p', f p = f p' ↔ QkPt.Equiv D F p p')
    (h₂ : ∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p')
    (h₃ : ∀ a p p', QkAct oa a p p' → f p' = act a (f p)) (b : O) (p : QkPt D F k) :
    act b (f p) = 1 ↔ QkPt.Equiv D F (qkZero hB F k) (qkSmul hB hG oa b p) := by
  have z : f (qkZero hB F k) = 1 := by
    have e : qkAdd hB (qkZero hB F k) (qkZero hB F k) = qkZero hB F k := qk_ext (add_zero _) (add_zero _)
    have := h₂ _ _ _ (qkAdd_qkAdd hB (qkZero hB F k) (qkZero hB F k))
    rw [e] at this
    exact left_eq_mul.1 this
  rw [← h₁, z, h₃ b p _ (qkAct_qkSmul hB hG oa b p), eq_comm]

end Points

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem exists_operator (hL : Laws) (oa : D.toPre.OAct O) (w0 : O) (hw0 : TraceFormTwistIso D.toPre oa w0) (a : O) (N k : ℕ)
    (hN : 1 ≤ N) (hk : 1 ≤ k) (haa : a * star a = (N : O))
    (π : Fam D.toPre F k →ₗ[F] Fam D.toPre F (k * N)) (hπ : Function.Injective π)
    (hπ' : ∀ s s', PullAl D F oa a k N s s' ↔ s' = π s) (θ : Fam D.toPre F k) (hθ : θ ≠ 0)
    (p p' : QkPt D.toPre F k) (p₀ p₁ p₂ : QkPt D.toPre F (k * N)) (he : QkPt.Equiv D.toPre F p p')
    (hg : GtAct oa a p₁.g p'.g) (hy : p₁.y = star a • p'.y) (hy₂ : p₂.y = p₀.y + p₁.y) (hg₂ : p₀.g.IsAdd p₁.g p₂.g)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (w₀ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₀.g.b) (DegPre.lineε (k * N)))) (hw₀ : w₀.IsGen)
    (ζ ζ₀ : F) (hζ : FinOrd D F k p w ζ) (hζ₀ : FinOrd D F (k * N) p₀ w₀ ζ₀) :
    ∃ w₂ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₂.g.b) (DegPre.lineε (k * N))), w₂.IsGen ∧
      FinOrd D F (k * N) p₂ w₂ (ζ₀ * ζ) ∧ ∀ s t t', PhiRel D.toPre F k p w s t →
        PhiRel D.toPre F (k * N) p₀ w₀ (π t) t' → PhiRel D.toPre F (k * N) p₂ w₂ (π s) t' := by
  have hkN : 1 ≤ k * N := Nat.mul_pos hk hN
  obtain ⟨w', hw', h'⟩ := phiRel_of_qkEquiv hL V D F k hk p p' he w hw
  obtain ⟨w₁, hw₁, h₁⟩ := ThetaPull.phiRel_pullAl hL V D F O oa w0 hw0 a N k hN hk haa p' p₁ hg hy w' hw'
  obtain ⟨w₂, hw₂, h₂⟩ := phi_mul hL V D F (k * N) hkN p₀ p₁ p₂ hy₂ hg₂ w₀ w₁ hw₀ hw₁
  have hc : ∀ s t, PhiRel D.toPre F k p w s t → PhiRel D.toPre F (k * N) p₁ w₁ (π s) (π t) := fun s t h =>
    h₁ s t _ _ ((h' s t).1 h) ((hπ' _ _).2 rfl) ((hπ' _ _).2 rfl)
  refine ⟨w₂, hw₂, ?_, fun s t t' h h₀ => h₂ _ _ _ (hc s t h) h₀⟩
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL V _ D F k hk p w hw
  obtain ⟨Φ₁, hΦ₁⟩ := phiFun_of hL V _ D F (k * N) hkN p₁ w₁ hw₁
  obtain ⟨M, hM, hU⟩ := (ThetaFinOrd.finOrd_iff p w ζ Φ hΦ).1 hζ
  have hn : ∀ (n : ℕ) (s : Fam D.toPre F k), ((ζ • Φ₁ : Module.End F (Fam D.toPre F (k * N))) ^ n) (π s) =
      π (((ζ • Φ : Module.End F (Fam D.toPre F k)) ^ n) s) := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih, LinearMap.smul_apply,
        LinearMap.smul_apply, map_smul π, (hΦ₁ _ _).1 (hc s _ ((hΦ _ _).2 rfl))]
  obtain ⟨c₁, c₂⟩ := finOrd_criteria hL V D F (k * N) hkN
  refine c₂ p₀ p₁ p₂ hy₂ hg₂ w₀ w₁ w₂ hw₀ hw₁ hw₂ h₂ ζ₀ ζ hζ₀
    (c₁ p₁ w₁ hw₁ ζ Φ₁ hΦ₁ (π θ) M (fun h => hθ (hπ (h.trans (map_zero π).symm))) hM ?_)
  exact (hn M θ).trans (by rw [hU]; rfl)

end GlobalTheory.ThetaGenerators

namespace GlobalTheory

open ThetaGenerators TorusExt in

theorem operator_on_pullback_eq_sum : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso → letI := H.starRing; ∀ (a a' : 𝓞 E) (N N' : ℕ), 1 ≤ N → 1 ≤ N' → Nat.Coprime N N' → a * star a = (N : 𝓞 E) → a' * star a' = (N' : 𝓞 E) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (θ' s : Fam P.D.toPre F (1 * N')) (θ₂ s₂ t₀ h : Fam P.D.toPre F (1 * N' * N)), θ' ≠ 0 → PullAl P.D F P.oD a (1 * N') N θ' θ₂ → PullAl P.D F P.oD a (1 * N') N s s₂ → ∀ (m : ℕ) (c : Fin m → F) (p : Fin m → QkPt P.D.toPre F (1 * N')) (x : Fin m → (TFK (R := V) F ⟶ P.A.A)) (w : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p i).g.b) (DegPre.lineε (1 * N')))) (ζ : Fin m → F) (tt : Fin m → Fam P.D.toPre F (1 * N')), ((∀ i, P.ToA F (1 * N') (p i) (x i)) ∧ (∀ i, x i ≫ P.oA.act (star (a')) = 1) ∧ (∀ i, (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd P.D F (1 * N') (p i) (w i) (ζ i)) ∧ (∀ i, ∃ t' : Fam P.D.toPre F (1 * N'), PhiRel P.D.toPre F (1 * N') (p i) (w i) θ' t' ∧ Fam.IsSmul P.D.toPre F (ζ i) t' (tt i)) ∧ s = ∑ i, c i • tt i) → ∀ (p₀ : QkPt P.D.toPre F (1 * N' * N)) (x₀ : TFK (R := V) F ⟶ P.A.A) (w₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₀.g.b) (DegPre.lineε (1 * N' * N)))) (ζ₀ : F), P.ToA F (1 * N' * N) p₀ x₀ → x₀ ≫ P.oA.act (star a) = 1 → w₀.IsGen → ζ₀ ≠ 0 → FinOrd P.D F (1 * N' * N) p₀ w₀ ζ₀ → PhiRel P.D.toPre F (1 * N' * N) p₀ w₀ s₂ t₀ → Fam.IsSmul P.D.toPre F ζ₀ t₀ h → ∃ (p₂ : Fin m → QkPt P.D.toPre F (1 * N' * N)) (x₂ : Fin m → (TFK (R := V) F ⟶ P.A.A)) (w₂ : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p₂ i).g.b) (DegPre.lineε (1 * N' * N)))) (ζ₂ : Fin m → F) (t₂ : Fin m → Fam P.D.toPre F (1 * N' * N)), (∀ i, P.ToA F (1 * N' * N) (p₂ i) (x₂ i)) ∧ (∀ i, x₂ i ≫ P.oA.act (star (a' * a)) = 1) ∧ (∀ i, (w₂ i).IsGen ∧ ζ₂ i ≠ 0 ∧ FinOrd P.D F (1 * N' * N) (p₂ i) (w₂ i) (ζ₂ i)) ∧ (∀ i, ∃ t' : Fam P.D.toPre F (1 * N' * N), PhiRel P.D.toPre F (1 * N' * N) (p₂ i) (w₂ i) θ₂ t' ∧ Fam.IsSmul P.D.toPre F (ζ₂ i) t' (t₂ i)) ∧ h = ∑ i, c i • t₂ i := by
  intro hL E _ _ _ H V _ _ _ t P hT
  letI := H.starRing
  intro a a' N N' hN hN' hco haa _ F _ _ _ θ' s θ₂ s₂ t₀ h hθ hθ₂ hs₂ m c p x w ζ tt ⟨hx, hxa, hw, htt, hs⟩
    p₀ x₀ w₀ ζ₀ hx₀ hxa₀ hw₀ hζ₀ hf₀ ht₀ hh
  have hG := hL.globalFns
  have hB := P.D.tau_bimult
  have hk : 1 ≤ 1 * N' := by omega
  have hkN : 1 ≤ 1 * N' * N := Nat.mul_pos hk hN
  obtain ⟨u, v, huv⟩ : IsCoprime (N : 𝓞 E) ((1 * N' : ℕ) : 𝓞 E) := by
    rw [_root_.one_mul]; exact hco.cast
  obtain ⟨π, hπ, hπ'⟩ := PullLin.exists_pull_linearMap hL V P.D F (𝓞 E) P.oD H.w0 P.w0 a N (1 * N') hN hk haa
  obtain rfl := (hπ' _ _).1 hθ₂
  obtain rfl := (hπ' _ _).1 hs₂
  obtain ⟨f, f₀, -, f₁, f₂, f₃, -⟩ := hT F (1 * N') hk
  obtain ⟨g, g₀, -, g₁, g₂, g₃, -⟩ := hT F (1 * N' * N) hkN
  obtain ⟨Φ₀, hΦ₀⟩ := phiFun_of hL V _ P.D F (1 * N' * N) hkN p₀ w₀ hw₀
  choose p' p₁ he hg hy hb using fun i => exists_lift hG hB P.oD a N (1 * N') haa u v huv (p i)
  choose w₂ hw₂ hf₂ hΦ₂ using fun i => exists_operator hL P.oD H.w0 P.w0 a N (1 * N') hN hk haa π hπ hπ' θ' hθ
    (p i) (p' i) p₀ (p₁ i) (qkAdd hB p₀ (p₁ i)) (he i) (hg i) (hy i) rfl ((isAdd_iff_eq _ _ _).2 rfl)
    (w i) (hw i).1 w₀ hw₀ (ζ i) ζ₀ (hw i).2.2 hf₀
  choose t' ht' htt' using htt
  refine ⟨fun i => qkAdd hB p₀ (p₁ i), fun i => g (qkAdd hB p₀ (p₁ i)), w₂, fun i => ζ₀ * ζ i,
    fun i => (ζ₀ * ζ i) • Φ₀ (π (t' i)), fun i => (g₀ _ _).2 rfl, fun i => ?_,
    fun i => ⟨hw₂ i, mul_ne_zero hζ₀ (hw i).2.1, hf₂ i⟩,
    fun i => ⟨_, hΦ₂ i _ _ _ (ht' i) ((hΦ₀ _ _).2 rfl), (DVR.isSmul_iff _ _ _).2 rfl⟩, ?_⟩
  · have k₁ : g (p₁ i) ≫ P.oA.act (star a') = 1 :=
      (killed_iff hG hB P.oD g (fun b y => y ≫ P.oA.act b) g₁ g₂ g₃ (star a') (p₁ i)).2 (hb i _
        ((killed_iff hG hB P.oD f (fun b y => y ≫ P.oA.act b) f₁ f₂ f₃ (star a') (p i)).1
          ((f₀ _ _).1 (hx i) ▸ hxa i)))
    have := P.oA.hom (star (a' * a))
    have := P.oA.hom (star a')
    have := P.oA.hom (star a)
    have e₀ : x₀ ≫ P.oA.act (star (a' * a)) = 1 := by
      rw [star_mul', P.oA.map_mul, ← Category.assoc, hxa₀, MonObj.one_comp]
    have e₁ : g (p₁ i) ≫ P.oA.act (star (a' * a)) = 1 := by
      rw [star_mul, P.oA.map_mul, ← Category.assoc, k₁, MonObj.one_comp]
    show g (qkAdd hB p₀ (p₁ i)) ≫ P.oA.act (star (a' * a)) = 1
    rw [g₂ _ _ _ (qkAdd_qkAdd hB p₀ (p₁ i)), ← (g₀ _ _).1 hx₀, MonObj.mul_comp, e₀, e₁, _root_.mul_one]
  · rw [(DVR.isSmul_iff _ _ _).1 hh, (hΦ₀ _ _).1 ht₀, hs, map_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(DVR.isSmul_iff _ _ _).1 (htt' i), map_smul, map_smul, map_smul, map_smul, smul_comm, smul_smul ζ₀]

end GlobalTheory
