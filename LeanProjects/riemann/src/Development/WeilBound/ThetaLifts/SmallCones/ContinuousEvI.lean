import Development.WeilBound.ThetaLifts.SmallCones.SliceSummable
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT.Ker

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)
open Matrix (vecMulVec)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem continuous_evI : Continuous (evI F) := by
  have : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    change Continuous fun x : InfiniteAdeleRing F =>
      ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  exact this.comp continuous_fst

theorem sz_le {κ : Type} [Fintype κ] (y : κ → AF F) :
    PositivityTheory.ThKCT.sz y ≤ (1 + Fintype.card κ * Fintype.card (InfinitePlace F)) * (1 + ‖fun j => evI F (y j)‖) := by
  have h : ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (y j)) ≤
      ∑ _j : κ, ∑ _w : InfinitePlace F, ‖fun j => evI F (y j)‖ :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun w _ => by
      refine le_trans ?_ (norm_le_pi_norm (fun j => evI F (y j)) j)
      rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
      exact Finset.le_sup' (fun w => mixedEmbedding.normAtPlace w (evI F (y j))) (Finset.mem_univ w)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have h0 := norm_nonneg fun j => evI F (y j)
  have h1 : (0 : ℝ) ≤ Fintype.card κ * Fintype.card (InfinitePlace F) := by positivity
  unfold PositivityTheory.ThKCT.sz
  nlinarith

theorem theta_unif {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    ∃ p : Seminorm ℂ (SInf F κ), Continuous p ∧ ∀ (f : SInf F κ) w, ‖thetaSum F (schr ψ w (pureA F f g))‖ ≤ p f := by
  obtain ⟨K, hK, hc⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  obtain ⟨G, hG⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hKp : IsCompact (Set.univ.pi fun _ : κ => K) := isCompact_univ_pi fun _ => hK
  obtain ⟨A, hA⟩ := hKp.exists_bound_of_continuousOn
    (f := fun k : κ → AF F => fun j => evI F (k j)) (continuous_pi fun j => continuous_evI.comp (continuous_apply j)).continuousOn
  have hC : IsCompact ((fun x : (κ → Af F) × (κ → AF F) => x.1 - fun j => (x.2 j).2) '' (tsupport g ×ˢ Set.univ.pi fun _ : κ => K)) :=
    (hg.2.isCompact.prod hKp).image (continuous_fst.sub (continuous_pi fun j => ((continuous_apply j).comp continuous_snd).snd))
  obtain ⟨N, hN⟩ := summable_wt hC
  set C := (fun x : (κ → Af F) × (κ → AF F) => x.1 - fun j => (x.2 j).2) '' (tsupport g ×ˢ Set.univ.pi fun _ : κ => K) with hCd
  set wt : (κ → F) → ℝ := fun ξ => if (fun j => (algebraMap F (AF F) (ξ j)).2) ∈ C then
    (PositivityTheory.ThKCT.sz (fun j => algebraMap F (AF F) (ξ j)) ^ N)⁻¹ else 0 with hwt
  have hw0 : ∀ ξ, 0 ≤ wt ξ := fun ξ => by
    rw [hwt]; dsimp only; split_ifs
    · exact inv_nonneg.2 (pow_pos (sz_pos _) _).le
    · exact le_rfl
  set c : ℝ := (1 + Fintype.card κ * Fintype.card (InfinitePlace F)) * (1 + |A|) with hcdef
  have hc0 : 0 < c := by positivity
  let q : Seminorm ℂ (SInf F κ) := (Finset.Iic (N, 0)).sup (schwartzSeminormFamily ℂ _ ℂ)
  have hq : Continuous q := Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm i
  let D : ℝ≥0 := ⟨2 ^ N * G * c ^ N * ∑' ξ, wt ξ, mul_nonneg (by positivity) (tsum_nonneg hw0)⟩
  refine ⟨D • q, hq.const_smul D, fun f w => ?_⟩
  choose a ha using fun j => hc (w.1 j)
  set k : κ → AF F := fun j => w.1 j - algebraMap F (AF F) (a j) with hk
  have hkK : k ∈ Set.univ.pi fun _ : κ => K := fun j _ => ha j
  have key : ∀ ξ : κ → F, ‖schr ψ w (pureA F f g) fun i => algebraMap F (AF F) (ξ i)‖ ≤ (2 ^ N * G * c ^ N * q f) * wt (ξ + a) := by
    intro ξ
    have e : (fun i => algebraMap F (AF F) (ξ i)) + w.1 = (fun i => algebraMap F (AF F) ((ξ + a) i)) + k := by
      funext i; simp [hk]
    rw [schr, norm_mul, std_norm hψ, one_mul, e]
    set η := ξ + a
    set y : κ → AF F := fun i => algebraMap F (AF F) (η i)
    change ‖f (fun i => evI F ((y + k) i)) * g (fun i => ((y + k) i).2)‖ ≤ _
    by_cases h0 : g (fun i => ((y + k) i).2) = 0
    · rw [h0, mul_zero, norm_zero]
      exact mul_nonneg (by positivity) (hw0 _)
    have hm : wt η = (PositivityTheory.ThKCT.sz y ^ N)⁻¹ := if_pos ⟨(_, k), ⟨subset_tsupport g h0, hkK⟩, by
      funext i
      change (y i).2 + (k i).2 - (k i).2 = _
      rw [add_sub_cancel_right]⟩
    set v : κ → mixedEmbedding.mixedSpace F := fun i => evI F ((y + k) i)
    have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl f v
    rw [norm_iteratedFDeriv_zero] at h1
    have h2 : PositivityTheory.ThKCT.sz y ≤ c * (1 + ‖v‖) := by
      refine (sz_le y).trans ?_
      rw [hcdef, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have e2 : (fun j => evI F (y j)) = v - fun j => evI F (k j) := funext fun j =>
        eq_sub_of_add_eq (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (y j).1 (k j).1).symm
      have := norm_sub_le v fun j => evI F (k j)
      have h3 := (hA k hkK).trans (le_abs_self A)
      rw [e2]
      nlinarith [norm_nonneg v, abs_nonneg A]
    rw [hm, ← div_eq_mul_inv, le_div_iff₀ (pow_pos (sz_pos _) _), norm_mul]
    calc _ ≤ ‖f v‖ * G * (c * (1 + ‖v‖)) ^ N :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hG _) (norm_nonneg _)) (pow_le_pow_left₀ (sz_pos _).le h2 N) (pow_pos (sz_pos _) _).le
            (by positivity)
      _ = G * c ^ N * ((1 + ‖v‖) ^ N * ‖f v‖) := by rw [mul_pow]; ring
      _ ≤ G * c ^ N * (2 ^ N * q f) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have hs : HasSum (fun ξ => wt (ξ + a)) (∑' ξ, wt ξ) := (Equiv.addRight a).hasSum_iff.2 hN.hasSum
  refine (tsum_of_norm_bounded (hs.mul_left _) key).trans_eq ?_
  change _ = (2 ^ N * G * c ^ N * ∑' ξ, wt ξ) * q f
  ring

variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
  {I : Set (Ten F E n d)} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {u z : Fin m → Matrix (Fin n) (Fin d) E}

theorem slice_unif (hS : Slice) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e)
    (hD : Dual σ X W I u z) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) : ∃ b : (Fin m → F) → ℝ, Summable b ∧ ∀ y w,
      ‖thetaSum F (M₁.co.rho B.ψ w (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ)))‖ ≤ b y := by
  obtain ⟨l, -, hl⟩ := (GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F (Fin n₁ × Fin d₁)).2.1
  have h := hB.std
  suffices ∃ b : (Fin m → F) → ℝ, Summable b ∧ ∀ y w,
      ‖l (rhoL B M₁ w (e (rhoL B M (lin u fun j => algebraMap F (AF F) (y j)) Φ)))‖ ≤ b y by
    obtain ⟨b, h1, h2⟩ := this
    exact ⟨b, h1, fun y w => by rw [← hl _ (rho_mem M₁ h _ (he.maps _ (rho_mem M h _ hΦ)))]; exact h2 y w⟩
  induction hΦ using Submodule.span_induction with
  | mem Φ h0 =>
    obtain ⟨f, φ, hφ, rfl⟩ := h0
    obtain ⟨r, φ₁, C, A, h1, hC, -, h2, h3, h4⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m u z hD φ hφ
    obtain ⟨N, hN⟩ := summable_wt hC
    choose q hq hb using fun i => theta_unif h (h1 i)
    choose p hp hpq using fun i => h4 (q i) N (hq i)
    refine ⟨_, hN.mul_left (∑ i, p i f), fun y w => ?_⟩
    rw [show e (rhoL B M _ _) = _ from h2 _ f, map_sum, map_sum]
    have hb' : ∀ i (f' : SInf F (Fin n₁ × Fin d₁)), ‖l (rhoL B M₁ w (pureA F f' (φ₁ i)))‖ ≤ q i f' := fun i f' =>
      (congrArg norm (hl _ (rho_mem M₁ h w (Submodule.subset_span ⟨f', _, h1 i, rfl⟩)))).trans_le (hb i f' _)
    split_ifs with hy
    · rw [Finset.sum_mul]
      refine norm_sum_le_of_le _ fun i _ => (hb' i _).trans ?_
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (sz_pos _) _)]
      exact hpq i i _ f
    · refine (norm_sum_le_of_le _ fun i _ => hb' i _).trans ?_
      simp [h3 _ _ hy]
  | zero => exact ⟨0, summable_zero, fun y w => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨a, a1, a2⟩ := h1
    obtain ⟨b, b1, b2⟩ := h2
    exact ⟨a + b, a1.add b1, fun y w => by
      simp only [map_add]; exact (norm_add_le _ _).trans (add_le_add (a2 y w) (b2 y w))⟩
  | smul c Φ _ h1 =>
    obtain ⟨a, a1, a2⟩ := h1
    exact ⟨fun y => ‖c‖ * a y, a1.mul_left _, fun y w => by
      simp only [map_smul, norm_smul]; exact mul_le_mul_of_nonneg_left (a2 y w) (norm_nonneg c)⟩

end PositivityTheory.ThKCT.Ker

end
