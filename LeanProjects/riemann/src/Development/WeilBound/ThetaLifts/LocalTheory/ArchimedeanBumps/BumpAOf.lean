import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.FormYx
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc.Cone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKCT PositivityTheory.ThKCT.Fr PositivityTheory.ThKF
open scoped ComplexConjugate RealInnerProductSpace

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}

theorem bA_l (J : Matrix (Fin n) (Fin n) E) (a : AE F E) (x y : Fin n → AE F E) : bA σ J (a • x) y = a * bA σ J x y := by
  simpa using bA_smul J a 1 x y

theorem bA_r (J : Matrix (Fin n) (Fin n) E) (a : AE F E) (x y : Fin n → AE F E) : bA σ J x (a • y) = cA σ a * bA σ J x y := by
  simpa using bA_smul J 1 a x y

theorem genA (hA : ArchOp) (hE : EiDense) (hS : ArchSlice) {M : Model σ X W} {M₁ : Model σ X₁ W₁} {χX χW om om₁ r s r' s' r₁ s₁ r₁' s₁'}
    (hP : IsPair B M χX χW om r s r' s') (hP₁ : IsPair B M₁ χX χW om₁ r₁ s₁ r₁' s₁') {H : Plane E n n₁} {H' : Plane E d d₁} {i j i' j'}
    (hH : H.IsAdapted σ B X X₁ i j) (hH' : H'.IsAdapted σ B W W₁ i' j') {e ei ev} (he : IsEv B M M₁ H.ι H'.ι (isoA H H') e)
    (hv : IsEvLoc M M₁ e ei ev) {rX rW} (hm : Mix2 H H' χX χW rX rW om om₁ e) {K : Subgroup (UA σ X.J)} {m : LocMeas K}
    (hK : IsStab B K) (hm' : m.Is) {ν : Chr F E} (hc : Continuous ν) {κ : InfinitePlace F → ℕ} (hν : HasExp B.emb ν fun w => κ w)
    {z : ℕ} (hχ : ∀ t, (χW t : ℂ) * ν t = 1)
    {L} (hL : IsConeI B M om m ei (shiftA H H') ν (z + 1) L) {l : SInf F _ →L[ℂ] ℂ} (hl0 : l ≠ 0)
    (hl : ∀ g ∈ UAt σ X₁ (evI F), ∀ f f₁ : SInf F _, Acts (evI F) (om₁ (g, 1)) f f₁ → l f₁ = l f) : ∃ f, l (L f) ≠ 0 := by
  by_contra hn
  push Not at hn
  have cfg : Cfg B M M₁ H H' e (shiftA H H') :=
    ⟨hP.base, ⟨_, _, hP.herm⟩, ⟨_, _, hP.skew⟩, ⟨_, _, hP₁.herm⟩, ⟨_, _, hP₁.skew⟩, hP.good, hP₁.good, ⟨_, _, hH⟩, ⟨_, _, hH'⟩, Or.inl ⟨he, rfl⟩⟩
  obtain ⟨lift, hlf⟩ := archDict_of F E σ B hP.base
  obtain ⟨hcp, hin, hsl⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e _ ei ev cfg hv lift hlf K m hK hm' _ _ om _ _ _ _ hP
  obtain ⟨f₀, hf₀⟩ := hE F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e _ ei ev cfg hv l hl0
  obtain ⟨-, i1, i2⟩ := PositivityTheory.ThKEst.lcsc_UA σ X.J
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : CompactSpace (kAt K (evI F)) := isCompact_iff_compactSpace.1 hcp
  haveI := hm'.ki
  obtain ⟨c₀, hc₀, hcv⟩ := conv hlf hν m.xi hm'.xi
  have hU : ∀ k ∈ kAt K (evI F), k ∈ UAt σ X (evI F) := fun k hk => (hin k hk).1
  have hG := hP.good
  have hG₁ := hP₁.good
  have sch := (archHeis_of F E σ B n d X W M hP.base).1
  have yx : form σ X.J H.y H.x = 1 := by simpa using form_yx hP.base (ε := 1) (by simpa using hP.herm.herm) hH.xy
  have yx' : form σ W.J H'.y H'.x = -1 := by simpa using form_yx hP.base (ε := -1) (by simpa using hP.skew.skew) hH'.xy
  have hprp := prp_pim (cont_xi hlf H.x (kAt K (evI F))) (xi_ne hlf hH.xy) 1
  have val : ∀ (u) (_ : At (evI F) u) (k : kAt K (evI F)) f, l (ei (opI (fun Φ => M.co.rho B.ψ u (om (k.1, 1) Φ)) f)) =
      unp M₁ l (e (M.co.rho B.ψ u (om (k.1, 1) (PV M f)))) := fun u hu k f => by
    rw [← pv_opI hA hP hu (hU _ k.2), un_e hG hG₁ hv]
  have omv : ∀ (k : kAt K (evI F)) f, ∃ g, om (k.1, 1) (PV M f) = PV M g := fun k f =>
    ⟨_, ((pv_opI hA hP (u := 0) (fun a _ => smul_zero a) (hU _ k.2) f).trans (rho_zero _ _ _)).symm⟩
  have om1 : ∀ Φ, om (((1 : kAt K (evI F)) : UA σ X.J), 1) Φ = Φ := fun Φ => by
    change om 1 Φ = Φ
    rw [map_one]; rfl
  have sh : ∀ c, lift c • shiftA H H' 1 = Matrix.vecMulVec (lift c • incV F H.x) (incV F H'.y) := fun c => by
    rw [shiftA, Units.val_one, one_smul, Matrix.smul_vecMulVec]
  let a : SInf F _ → kAt K (evI F) × (InfinitePlace F → ℂ) → ℂ := fun f p =>
    l (ei (opI (fun Φ => M.co.rho B.ψ (lift p.2 • shiftA H H' 1) (om (p.1.1, 1) Φ)) f))
  have ha : ∀ f k c, a f (k, c) = unp M₁ l (e (M.co.rho B.ψ (Matrix.vecMulVec (lift c • incV F H.x) (incV F H'.y)) (om (k.1, 1) (PV M f)))) :=
    fun f k c => by rw [← sh]; exact val _ (at_smul2 (hlf.supp c) _) k f
  have zero : ∀ f, ∫ k, ∫ c, a f (k, c) * r0 κ z c ∂volume ∂m.ki = 0 := fun f => by
    have h1 := (hsl f l).2.2 ν (z + 1) hc (by omega) L hL
    rw [hn] at h1
    have h2 : ∀ k : kAt K (evI F), _ = c₀ * ∫ c, a f (k, c) * r0 κ z c := fun k => hcv z (fun c => a f (k, c))
      (fun t => l (ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • shiftA H H' t) (om (k.1, 1) Φ)) f))) fun t => by
        simp only [a, shiftA, Units.val_one, one_smul]
        rw [← smul_assoc, hlf.eq (hlf.part t.1).1 (hlf.part t.1).2]
    simp only [h2] at h1
    rw [integral_const_mul] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left hc₀
  obtain ⟨f, hf⟩ := pv_rho hP.base hG (u := Matrix.vecMulVec ((-lift 1) • incV F H.x) (incV F H'.y))
    (at_vv (by rw [neg_smul, ← zero_sub]; exact at_sub (fun a _ => smul_zero a) (at_smul2 (hlf.supp 1) _)) _) f₀
  have h11 : a f (1, 1) ≠ 0 := by
    rw [ha, om1, ← hf, ← heisenberg_action_add_of_orthogonal M B.ψ (by rw [sy_vv, bA_smul, bA_inc, hH.xx]; simp), ← Matrix.add_vecMulVec, ← add_smul, add_neg_cancel,
      zero_smul, Matrix.zero_vecMulVec, rho_zero, un_e hG hG₁ hv]
    exact hf₀
  refine coreA m.ki hprp κ z (hsl f l).1 (hsl f l).2.1 (a f (1, 1))⁻¹ (fun p hp => ?_) fun η => ?_
  · obtain ⟨hne, t, ht, ht', hk⟩ := sig_pt hlf hH.xy hU p hp
    obtain ⟨e1, e2⟩ := nu_eq hlf hν ht
    simp only [ht'] at e1 e2
    have k1 : lift p.2 • incV F H.x = mat p.1.1 *ᵥ (lift 1 • incV F H.x) := by
      rw [Matrix.mulVec_smul, hk, smul_smul, ← hlf.eq (at_mul (hlf.supp 1) t.1) fun w => by rw [map_mul, hlf.pi, ht']; simp]
    have k2 : a f p = (χW t : ℂ) * (((absE F E t : ℝ) ^ rX : ℝ) : ℂ) * a f (1, 1) := by
      rw [ha f p.1 p.2, ha, k1, ← om_rho hP _ _ _ (pv_sch hG f), om1]
      exact (mix_un hA hP hP₁ hH hv hm hl (hU _ p.1.2) hk).1 _
        ((pv_rho hP.base hG (at_vv (at_smul2 (hlf.supp 1) _) _) f))
    have k3 : a f p * r0 κ z p.2 * (a f (1, 1))⁻¹ = (((nm p.2) ^ rX * nm p.2 ^ z : ℝ) : ℂ) := by
      rw [k2, rationalWeight_eq_mul_norm_pow, ← e1, e2]
      push_cast
      field_simp
      linear_combination ((((nm p.2) ^ rX : ℝ) : ℂ) * ((nm p.2 : ℝ) : ℂ) ^ z) * hχ t
    change 0 < (a f p * _ * _).re
    rw [k3, Complex.ofReal_re]
    have := nm_pos hne
    positivity
  · obtain ⟨g, hg⟩ := pv_rho hP.base hG (at_vv (at_Yv hlf (X := X) (-η)) (incV F H'.x)) f
    refine Eq.trans ?_ (zero g)
    congr 1; funext k; congr 1; funext c; congr 1
    obtain ⟨f₁, hf₁⟩ := omv k f
    change _ * a f (k, c) = _
    rw [ha, ha, ← hg, om_rho hP _ _ _ (pv_sch hG f), rho_comm, hf₁]
    obtain ⟨f₂, hf₂⟩ := pv_rho hP.base hG (at_vv (at_smul2 (hlf.supp c) (incV F H.x)) (incV F H'.y)) f₁
    rw [hf₂, un_e_smul hG hG₁ hv l _ (pv_rho hP.base hG (at_vv (at_mulVec (at_Yv hlf _)) _) f₂),
      he.inv _ (Or.inl ⟨_, rfl⟩) _ (pv_sch hG f₂)]
    congr 1
    rw [sy_vv, bA_l, bA_inc, yx', map_neg (inclR (F := F) (E := E) (AF F)), map_one, mul_neg_one, neg_neg,
      hlf.ch (hlf.supp c) (x := bet (xi B H.x) (k, -η)) (y := c) fun w => by rw [map_mul, hlf.pi, pi_beta hlf hP.herm, mul_comm],
      pr_bet, inner_neg_left, neg_neg]

set_option maxHeartbeats 400000 in
theorem genB (hA : ArchOp) (hE : EiDense) (hS : ArchSlice) {M : Model σ X W} {M₁ : Model σ X₁ W₁} {χX χW om om₁ r s r' s' r₁ s₁ r₁' s₁'}
    (hP : IsPair B M χX χW om r s r' s') (hP₁ : IsPair B M₁ χX χW om₁ r₁ s₁ r₁' s₁') {H : Plane E n n₁} {H' : Plane E d d₁} {i j i' j'}
    (hH : H.IsAdapted σ B X X₁ i j) (hH' : H'.IsAdapted σ B W W₁ i' j') {e ei ev} (he : IsEv B M M₁ H.ι H'.ι (isoB H H') e)
    (hv : IsEvLoc M M₁ e ei ev) {rX rW} (hm : Mix2 H H' χX χW rX rW om om₁ e) {K : Subgroup (UA σ X.J)} {m : LocMeas K}
    (hK : IsStab B K) (hm' : m.Is) {ν : Chr F E} (hc : Continuous ν) {κ : InfinitePlace F → ℕ} (hν : HasExp B.emb ν fun w => κ w)
    {z : ℕ} (hχ : ∀ t, χW t = ν t) (hκ : ∀ w, 2 * z < κ w)
    {L} (hL : IsConeI B M om m ei (shiftB σ H H') ν (z + 1) L) {l : SInf F _ →L[ℂ] ℂ} (hl0 : l ≠ 0)
    (hl : ∀ g ∈ UAt σ X₁ (evI F), ∀ f f₁ : SInf F _, Acts (evI F) (om₁ (g, 1)) f f₁ → l f₁ = l f) : ∃ f, l (L f) ≠ 0 := by
  by_contra hn
  push Not at hn
  have cfg : Cfg B M M₁ H H' e (shiftB σ H H') :=
    ⟨hP.base, ⟨_, _, hP.herm⟩, ⟨_, _, hP.skew⟩, ⟨_, _, hP₁.herm⟩, ⟨_, _, hP₁.skew⟩, hP.good, hP₁.good, ⟨_, _, hH⟩, ⟨_, _, hH'⟩, Or.inr ⟨he, rfl⟩⟩
  obtain ⟨lift, hlf⟩ := archDict_of F E σ B hP.base
  obtain ⟨hcp, hin, hsl⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e _ ei ev cfg hv lift hlf K m hK hm' _ _ om _ _ _ _ hP
  obtain ⟨f₀, hf₀⟩ := hE F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e _ ei ev cfg hv l hl0
  obtain ⟨-, i1, i2⟩ := PositivityTheory.ThKEst.lcsc_UA σ X.J
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : CompactSpace (kAt K (evI F)) := isCompact_iff_compactSpace.1 hcp
  haveI := hm'.ki
  obtain ⟨c₀, hc₀, hcv⟩ := conv hlf hν m.xi hm'.xi
  have hU : ∀ k ∈ kAt K (evI F), k ∈ UAt σ X (evI F) := fun k hk => (hin k hk).1
  have hG := hP.good
  have hG₁ := hP₁.good
  have sch := (archHeis_of F E σ B n d X W M hP.base).1
  have yx : form σ X.J H.y H.x = 1 := by simpa using form_yx hP.base (ε := 1) (by simpa using hP.herm.herm) hH.xy
  have yx' : form σ W.J H'.y H'.x = -1 := by simpa using form_yx hP.base (ε := -1) (by simpa using hP.skew.skew) hH'.xy
  have hprp := prp_pim (cont_xi hlf H.x (kAt K (evI F))) (xi_ne hlf hH.xy) 1
  have val : ∀ (u) (_ : At (evI F) u) (k : kAt K (evI F)) f, l (ei (opI (fun Φ => M.co.rho B.ψ u (om (k.1, 1) Φ)) f)) =
      unp M₁ l (e (M.co.rho B.ψ u (om (k.1, 1) (PV M f)))) := fun u hu k f => by
    rw [← pv_opI hA hP hu (hU _ k.2), un_e hG hG₁ hv]
  have omv : ∀ (k : kAt K (evI F)) f, ∃ g, om (k.1, 1) (PV M f) = PV M g := fun k f =>
    ⟨_, ((pv_opI hA hP (u := 0) (fun a _ => smul_zero a) (hU _ k.2) f).trans (rho_zero _ _ _)).symm⟩
  have om1 : ∀ Φ, om (((1 : kAt K (evI F)) : UA σ X.J), 1) Φ = Φ := fun Φ => by
    change om 1 Φ = Φ
    rw [map_one]; rfl
  have sh : ∀ c, lift c • shiftB σ H H' 1 = Matrix.vecMulVec (lift c • incV F H.y) (incV F H'.x) := fun c => by
    rw [shiftB, Units.val_one, map_one, one_smul, Matrix.smul_vecMulVec]
  have cj : Continuous fun p : kAt K (evI F) × (InfinitePlace F → ℂ) => (p.1, star p.2) := by fun_prop
  let a : SInf F _ → kAt K (evI F) × (InfinitePlace F → ℂ) → ℂ := fun f p =>
    l (ei (opI (fun Φ => M.co.rho B.ψ (lift (star p.2) • shiftB σ H H' 1) (om (p.1.1, 1) Φ)) f))
  have hac : ∀ f, Continuous (a f) := fun f => by
    have := (hsl f l).1.comp cj
    exact this
  have had : ∀ f, Dec (a f) := fun f N => let ⟨C, hC⟩ := (hsl f l).2.1 N; ⟨C, fun k c => by have := hC k (star c); rw [norm_star] at this; exact this⟩
  have ha : ∀ f k c, a f (k, c) =
      unp M₁ l (e (M.co.rho B.ψ (Matrix.vecMulVec (lift (star c) • incV F H.y) (incV F H'.x)) (om (k.1, 1) (PV M f)))) :=
    fun f k c => by rw [← sh]; exact val _ (at_smul2 (hlf.supp _) _) k f
  have zero : ∀ f, ∫ k, ∫ c, a f (k, c) * r0 κ z c ∂volume ∂m.ki = 0 := fun f => by
    have h1 := (hsl f l).2.2 ν (z + 1) hc (by omega) L hL
    rw [hn] at h1
    have h2 : ∀ k : kAt K (evI F), _ = c₀ * ∫ c, a f (k, c) * r0 κ z c := fun k => hcv z (fun c => a f (k, c))
      (fun t => l (ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • shiftB σ H H' t) (om (k.1, 1) Φ)) f))) fun t => by
        simp only [a, shiftB, Units.val_one, map_one, one_smul]
        rw [← smul_assoc, hlf.eq (hlf.part _).1 (c := star fun w => piInf (B.emb w) t.1) fun w => by
          rw [(hlf.part _).2, hlf.conj]; rfl]
    simp only [h2] at h1
    rw [integral_const_mul] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left hc₀
  clear_value a
  clear hsl val hcv
  have hac1 : ∀ f, Continuous fun c => a f (1, c) := fun f => (hac f).comp (Continuous.prodMk_right 1)
  have sy0 : ∀ x x' : Fin n → AE F E, sy σ X W (Matrix.vecMulVec x (incV F H'.x)) (Matrix.vecMulVec x' (incV F H'.x)) = 0 := fun x x' => by
    rw [sy_vv, bA_inc, hH'.xx]; simp
  have kill : ∀ U (b : AE F E) y, ∀ Φ ∈ schA F _, e (M.co.rho B.ψ (Matrix.vecMulVec (incM F H.ι *ᵥ U + b • incV F H.x + y) (incV F H'.x)) Φ) =
      e (M.co.rho B.ψ (Matrix.vecMulVec y (incV F H'.x)) Φ) := fun U b y Φ hΦ => by
    rw [Matrix.add_vecMulVec, Matrix.add_vecMulVec, add_assoc, ← Matrix.add_vecMulVec, heisenberg_action_add_of_orthogonal M B.ψ (sy0 _ _),
      he.inv _ (Or.inr ⟨_, rfl⟩) _ (sch _ _ hΦ), Matrix.add_vecMulVec, heisenberg_action_add_of_orthogonal M B.ψ (sy0 _ _),
      he.inv _ (Or.inl ⟨b • incV F H'.x, by rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]⟩) _ (sch _ _ hΦ)]
  have l0 : lift 0 = 0 := (hlf.eq (fun u _ => smul_zero u) fun w => map_zero _).symm
  obtain ⟨t₀, ht₀⟩ := exists_FT_ne (a := fun c => a f₀ (1, c)) (hac1 f₀)
    ((had f₀).integrable 1 (hac1 f₀)) (by
      rw [ha, om1, star_zero, l0, zero_smul, Matrix.zero_vecMulVec, rho_zero, un_e hG hG₁ hv]; exact hf₀)
  obtain ⟨f, hf⟩ := pv_rho hP.base hG (at_vv (at_smul2 (hlf.supp (1 - t₀)) (incV F H.x)) (incV F H'.y)) f₀
  have h11 : FT (fun c => a f (1, c)) 1 ≠ 0 := by
    refine fun h => ht₀ (Eq.trans ?_ h)
    rw [FT, FT]
    congr 1; funext c
    obtain ⟨f₂, hf₂⟩ := pv_rho hP.base hG (at_vv (at_smul2 (hlf.supp (star c)) (incV F H.y)) (incV F H'.x)) f₀
    rw [ha, ha, om1, om1, ← hf, rho_comm, hf₂, un_e_smul hG hG₁ hv l _ (pv_rho hP.base hG (at_vv (at_smul2 (hlf.supp _) _) _) f₂),
      he.inv _ (Or.inl ⟨lift (1 - t₀) • incV F H'.y, by rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]⟩) _ (pv_sch hG f₂),
      ← mul_assoc]
    congr 1
    rw [sy_vv, bA_smul, bA_inc, bA_inc, yx, hH'.xy, map_one, mul_one, mul_one, ← mul_neg,
      hlf.ch (hlf.supp _) (x := c) (y := t₀ - 1) fun w => by
        rw [map_mul, map_neg, hlf.conj, hlf.pi, hlf.pi]; simp <;> ring, ← ch_add]
    congr 1
    simp only [pr, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by simp; ring
  haveI : SecondCountableTopology (kAt K (evI F)) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : FirstCountableTopology (kAt K (evI F)) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  obtain ⟨D, hD⟩ := bet_le (cont_xi hlf H.x (kAt K (evI F)))
  refine coreB m.ki hprp κ z hκ (hac f) (had f) (FT (fun c => a f (1, c)) 1)⁻¹ _ (cont_bet (cont_xi hlf H.x _)) D hD (pr_bet _)
    (fun p hp => ?_) fun η => ?_
  · obtain ⟨hne, t, ht, ht', hk⟩ := sig_pt hlf hH.xy hU p hp
    obtain ⟨e1, e2⟩ := nu_eq hlf hν ht
    simp only [ht'] at e1 e2
    obtain ⟨hmx, U, b, hy⟩ := mix_un hA hP hP₁ hH hv hm hl (hU _ p.1.2) hk
    have k2 : ∀ c, a f (p.1, c) = (χW t : ℂ) * (((absE F E t : ℝ) ^ rX : ℝ) : ℂ) * a f (1, p.2 * c) := fun c => by
      rw [ha, ha, ← mat_cancel' p.1.1 (lift (star c) • incV F H.y), ← om_rho hP _ _ _ (pv_sch hG f), om1,
        hmx _ (pv_rho hP.base hG (at_vv (at_mulVec (at_smul2 (hlf.supp _) _)) _) f), Matrix.mulVec_smul, hy, smul_add, smul_add,
        ← Matrix.mulVec_smul, smul_smul, smul_smul, kill _ _ _ _ (pv_sch hG f),
        hlf.eq (at_mul (hlf.supp (star c)) (cA σ t.1)) (c := star (p.2 * c)) fun w => by
          rw [map_mul, hlf.pi, hlf.conj, ht']; simp [mul_comm]]
    have k4 : FT (fun c => a f (p.1, c)) p.2 =
        (χW t : ℂ) * (((absE F E t : ℝ) ^ rX : ℝ) : ℂ) * (((nm p.2 : ℝ) : ℂ)⁻¹ * FT (fun c => a f (1, c)) 1) := by
      have := FT_scale ((had f).integrable 1 (hac1 f)) hne p.2
      rw [show p.2 * p.2⁻¹ = 1 from funext fun w => mul_inv_cancel₀ (hne w)] at this
      rw [← this, FT, FT, ← integral_const_mul]
      congr 1; funext c; rw [k2]; ring
    have hp' := nm_pos hne
    have hp'' : ((nm p.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
    have hr := rationalWeight_ne_zero κ 0 hne
    have k3 : FT (fun c => a f (p.1, c)) p.2 * ((r0 κ z p.2)⁻¹ * ((nm p.2 : ℝ) : ℂ)⁻¹) * (FT (fun c => a f (1, c)) 1)⁻¹ =
        (((nm p.2) ^ rX * (nm p.2 ^ (z + 2))⁻¹ : ℝ) : ℂ) := by
      rw [k4, rationalWeight_eq_mul_norm_pow κ z p.2, hχ, e1, e2]
      change r0 κ 0 p.2 * (((nm p.2) ^ rX : ℝ) : ℂ) * _ * _ * _ = _
      rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
      have h11' : FT (fun c => a f (1, c)) 1 * (FT (fun c => a f (1, c)) 1)⁻¹ = 1 := mul_inv_cancel₀ h11
      have hr' : r0 κ 0 p.2 * (r0 κ 0 p.2)⁻¹ = 1 := mul_inv_cancel₀ hr
      generalize (((nm p.2) ^ rX : ℝ) : ℂ) = A
      generalize FT (fun c => a f (1, c)) 1 = T at h11'
      rw [mul_inv, pow_add, mul_inv, ← inv_pow _ 2]
      linear_combination (A * ((nm p.2 : ℝ) : ℂ)⁻¹ ^ 2 * (((nm p.2 : ℝ) : ℂ) ^ z)⁻¹) * (T * T⁻¹ * hr' + h11')
    rw [k3, Complex.ofReal_re]
    positivity
  · obtain ⟨g, hg⟩ := pv_rho hP.base hG (at_vv (at_Yv hlf (X := X) η) (incV F H'.x)) f
    refine Eq.trans ?_ (zero g)
    congr 1; funext k; congr 1; funext c; congr 1
    obtain ⟨U, b, hy⟩ := decomp hP.base hP.herm hH (mat k.1 *ᵥ Yv X B lift η)
    have hat : At (evI F) (cA σ (bA σ X.J (incV F H.x) (mat k.1 *ᵥ Yv X B lift η))) := by
      rw [← at_iff.1 (at_mulVec (g := mat k.1) (at_Yv hlf (X := X) η)), ← algebraMap_smul (AE F E), bA_r, map_mul,
        PositivityTheory.ThKG.Tow.Levi.cA_cA hP.base.cm, ← Algebra.smul_def]
      exact (hlf.part _).1
    rw [ha, ha, ← hg, om_rho hP _ _ _ (pv_sch hG f), ← heisenberg_action_add_of_orthogonal M B.ψ (sy0 _ _), ← Matrix.add_vecMulVec, hy, add_comm (lift _ • _),
      add_assoc, kill _ _ _ _ (om_sch hP _ (pv_sch hG f)), ← add_smul,
      ← hlf.eq (at_add hat (hlf.supp (star c))) (c := star (c + bet (xi B H.x) (k, η))) fun w => by
        rw [map_add, hlf.pi, hlf.conj, pi_beta hlf hP.herm]; simp [add_comm]]

theorem kap_ex {a a' : ℕ} {G : Geo σ a a'} {Y : Chars F E} {om om'} (t : IsTriple B G Y om om') :
    ∃ κ : InfinitePlace F → ℕ, (∀ w, a + a' < κ w) ∧ HasExp B.emb Y.ν fun w => κ w := by
  refine ⟨fun w => (B.mα w - B.mβ w).toNat, fun w => by have := t.geo.kappa w; beta_reduce; omega, fun z hz => ?_⟩
  obtain ⟨lift, h⟩ := archDict_of F E σ B t.base
  rw [Chars.ν, MonoidHom.div_apply, Circle.coe_div, t.chars.expα z hz, t.chars.expβ z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h0 : piInf (B.emb w) (z : AE F E) ≠ 0 := (z.isUnit.map _).ne_zero
  rw [← zpow_sub₀ (by simpa using h0)]
  congr 1
  have := t.geo.kappa w; beta_reduce; omega

theorem pcast {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' a b a' b' : ℕ} (h : IsPair B M χX χW om r s r' s')
    (h1 : r = a) (h2 : s = b) (h3 : r' = a') (h4 : s' = b') : IsPair B M χX χW om a b a' b' := by subst h1 h2 h3 h4; exact h

theorem bumpA_of (hA : ArchOp) (hE : EiDense) (hS : ArchSlice) (hM : MixAB) : BumpA := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' c e ei ev he hv K m hK hm X om om' om₁ om₁' t t₁ L hL l hl0 hl
  obtain ⟨κ, -, hκ⟩ := kap_ex t
  have h1 := t.geo.eBig; have h2 := t₁.geo.eBig; have h3 := c.ep; have h4 := c.q0; have h5 := c.q1
  obtain ⟨z, hz⟩ : ∃ z, (b + 2 - a') / 2 = z + 1 := ⟨(b + 2 - a') / 2 - 1, by omega⟩
  rw [hz] at hL
  refine genA hA hE hS (pairV t) (pairV t₁) c.hH c.hH' he hv ((hM F E σ B _ _ _ _ _ _ _ _ H H' _ _ _ _ _ _ _ _ _ _ c.hH c.hH' _ _ om om₁
    (pcast (pairV t) (by omega) (by omega) (by omega) (by omega)) (pairV t₁)).1 e he) hK hm
    (isHecke_div t.chars.heckeα t.chars.heckeβ).1 hκ (fun x => ?_) hL hl0 hl
  simp [Chars.ν]

theorem bumpB_of (hA : ArchOp) (hE : EiDense) (hS : ArchSlice) (hM : MixAB) : BumpB := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' c e ei ev he hv K m hK hm X om om' om₁ om₁' t t₁ L hL l hl0 hl
  obtain ⟨κ, hκ', hκ⟩ := kap_ex t
  have h1 := t.geo.aBig; have h2 := t₁.geo.aBig; have h3 := c.ep; have h4 := c.eq; have h5 := t.geo.lt
  exact genB hA hE hS (pairV' t) (pairV' t₁) c.hH c.hH' he hv ((hM F E σ B _ _ _ _ _ _ _ _ H H' _ _ _ _ _ _ _ _ _ _ c.hH c.hH' _ _ om' om₁'
    (pcast (pairV' t) (by omega) (by omega) (by omega) (by omega)) (pairV' t₁)).2 e he) hK hm
    (isHecke_div t.chars.heckeα t.chars.heckeβ).1 hκ (fun x => rfl) (fun w => by have := hκ' w; omega) hL hl0 hl

end PositivityTheory.ThKG.Loc.Bump

end
