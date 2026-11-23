import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.ArchHeisOf
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.RationalWeightSuccMulInvNorm
import Development.WeilBound.ThetaLifts.SmallCones.MatCancel
import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc.Cone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKCT PositivityTheory.ThKCT.Fr PositivityTheory.ThKF

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}

theorem rho_rho (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u u' : Matrix (Fin n) (Fin d) (AE F E)) (Φ : Fn F n d) :
    M.co.rho ψ u (M.co.rho ψ u' Φ) = ψ (⅟(2 : AF F) * sy σ X W u u') • M.co.rho ψ (u + u') Φ := by
  funext x
  have h2 : ⅟(2 : AF F) * 2 = 1 := invOf_mul_self _
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, map_add, Prod.fst_add, Prod.snd_add, sy, M.co.2 u u', ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-((M.co.e u).1 ⬝ᵥ (M.co.e u').2)) * h2

theorem rho_zero (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (Φ : Fn F n d) : M.co.rho ψ 0 Φ = Φ := by
  funext x; simp [Darboux.rho, schr]

theorem heisenberg_action_add_of_orthogonal (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {u u' : Matrix (Fin n) (Fin d) (AE F E)} (h : sy σ X W u u' = 0) (Φ : Fn F n d) :
    M.co.rho ψ (u + u') Φ = M.co.rho ψ u (M.co.rho ψ u' Φ) := by
  rw [rho_rho, h, mul_zero, AddChar.map_zero_eq_one, one_smul]

theorem rho_comm (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u u' : Matrix (Fin n) (Fin d) (AE F E)) (Φ : Fn F n d) :
    M.co.rho ψ u (M.co.rho ψ u' Φ) = ψ (sy σ X W u u') • M.co.rho ψ u' (M.co.rho ψ u Φ) := by
  have h2 : ⅟(2 : AF F) * 2 = 1 := invOf_mul_self _
  rw [rho_rho, rho_rho, smul_smul, ← AddChar.map_add_eq_mul, add_comm u' u]
  congr 2
  simp only [sy, M.co.2]
  linear_combination ((M.co.e u).1 ⬝ᵥ (M.co.e u').2 - (M.co.e u').1 ⬝ᵥ (M.co.e u).2) * h2

variable (σ) in

def bA (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → AE F E) : AE F E := x ⬝ᵥ incM F J *ᵥ fun i => cA σ (y i)

theorem sy_vv (x x' : Fin n → AE F E) (y y' : Fin d → AE F E) :
    sy σ X W (Matrix.vecMulVec x y) (Matrix.vecMulVec x' y') = Algebra.trace (AF F) (AE F E) (-(bA σ X.J x x' * bA σ W.J y y')) := by
  simp only [sy, symp, hTens, bA, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, map_mul, neg_one_mul]
  congr 2
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum _ _ (y j), Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem bA_inc (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : bA σ J (incV F x) (incV F y) = inclR (F := F) (AF F) (form σ J x y) := by
  simp only [bA, form, dotProduct, Matrix.mulVec, map_sum, map_mul]
  rfl

theorem bA_smul (J : Matrix (Fin n) (Fin n) E) (a b : AE F E) (x y : Fin n → AE F E) : bA σ J (a • x) (b • y) = a * cA σ b * bA σ J x y := by
  simp only [bA, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem bA_mat {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (x y : Fin n → AE F E) : bA σ J (mat g *ᵥ x) (mat g *ᵥ y) = bA σ J x y := by
  have h : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have e : (fun i => cA σ ((mat g *ᵥ y) i)) = (mat g).map (cA σ) *ᵥ fun i => cA σ (y i) :=
    funext fun i => RingHom.map_mulVec (cA σ : AE F E →+* AE F E) (mat g) y i
  simp only [bA]
  conv_rhs => rw [← h]
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]

theorem om_rho {M : Model σ X W} {χX χW om r s r' s'} (hP : IsPair B M χX χW om r s r' s') (g : UA σ X.J)
    (x : Fin n → AE F E) (y : Fin d → AE F E) {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) :
    om (g, 1) (M.co.rho B.ψ (Matrix.vecMulVec x y) Φ) = M.co.rho B.ψ (Matrix.vecMulVec (mat g *ᵥ x) y) (om (g, 1) Φ) := by
  rw [hP.weil.isUSplitting.impl (g, 1) _ Φ hΦ]
  congr 1
  change mat g * _ * (1 : Matrix _ _ _)ᵀ = _
  rw [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_vecMulVec]

theorem om_sch {M : Model σ X W} {χX χW om r s r' s'} (hP : IsPair B M χX χW om r s r' s') (g) {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) :
    om g Φ ∈ schA F (Fin n × Fin d) := hP.weil.isUSplitting.pres g Φ hΦ

abbrev PV (M : Model σ X W) (f : SInf F (Fin n × Fin d)) : Fn F n d := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac

theorem pv_sch {M : Model σ X W} (hM : M.IsGood B.ψ) (f) : PV M f ∈ schA F (Fin n × Fin d) :=
  (rest_pure f M.vac (fun v => (hM.vac v).1) hM.std).2

theorem pv_act {M : Model σ X W} (hM : M.IsGood B.ψ) {S} {f f₁ : SInf F (Fin n × Fin d)} (h : Acts (evI F) S f f₁) : S (PV M f) = PV M f₁ :=
  h _ (rest_pure f M.vac (fun v => (hM.vac v).1) hM.std)

theorem pv_smul (M : Model σ X W) (c : ℂ) (f) : PV M (c • f) = c • PV M f := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem pv_rho {M : Model σ X W} (hB : B.IsGood σ) (hM : M.IsGood B.ψ) {u} (hu : At (evI F) u) (f) :
    ∃ f₁, M.co.rho B.ψ u (PV M f) = PV M f₁ :=
  let ⟨f₁, h⟩ := (archHeis_of F E σ B n d X W M hB).2 u hu f; ⟨f₁, pv_act hM h⟩

theorem one_at {J : Matrix (Fin n) (Fin n) E} (Y : Spc F E n) : (1 : UA σ Y.J) ∈ UAt σ Y (evI F) := fun a _ => by
  rw [mat_one, sub_self, smul_zero]

theorem pv_opI (hA : ArchOp) {M : Model σ X W} {χX χW om r s r' s'} (hP : IsPair B M χX χW om r s r' s') {u} (hu : At (evI F) u)
    {k} (hk : k ∈ UAt σ X (evI F)) (f) :
    PV M (opI (fun Φ => M.co.rho B.ψ u (om (k, 1) Φ)) f) = M.co.rho B.ψ u (om (k, 1) (PV M f)) := by
  obtain ⟨T, hT, -⟩ := hA F E σ B n d X W M χX χW om r s r' s' hP k hk 1 (one_at (J := W.J) W)
  obtain ⟨f₂, h₂⟩ := (archHeis_of F E σ B n d X W M hP.base).2 u hu (T f)
  have h : ∃ f₁ : SInf F _, Acts (evI F) (fun Φ => M.co.rho B.ψ u (om (k, 1) Φ)) f f₁ := ⟨f₂, fun q hq => by
    have e := hT.2 f q hq
    beta_reduce
    rw [e]
    exact h₂ q ⟨hq.1, e ▸ om_sch hP _ hq.2⟩⟩
  rw [opI, dif_pos h]
  exact (pv_act hP.good h.choose_spec).symm

open Classical in

def unp (M : Model σ X W) (l : SInf F (Fin n × Fin d) →L[ℂ] ℂ) (Ψ : Fn F n d) : ℂ :=
  if h : ∃ g, Ψ = PV M g then l h.choose else 0

theorem un_pv {M : Model σ X W} (hM : M.IsGood B.ψ) (l) (g) : unp M l (PV M g) = l g := by
  have h : ∃ g', PV M g = PV M g' := ⟨g, rfl⟩
  rw [unp, dif_pos h, ← pure_inj M.vac (fun v => (hM.vac v).2.1) hM.std h.choose_spec]

theorem e_pv {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hM : M.IsGood B.ψ) {e ei ev} (h : IsEvLoc M M₁ e ei ev) (f) :
    e (PV M f) = PV M₁ (ei f) := by
  rw [h.pure f M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl)]
  congr 1
  exact funext fun v => (h.vac v).1

theorem un_e {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) {e ei ev} (h : IsEvLoc M M₁ e ei ev) (l) (f) :
    unp M₁ l (e (PV M f)) = l (ei f) := by rw [e_pv hM h, un_pv hM₁]

theorem un_e_smul {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) {e ei ev} (h : IsEvLoc M M₁ e ei ev) (l)
    (c : ℂ) {Ψ} (hΨ : ∃ f, Ψ = PV M f) : unp M₁ l (e (c • Ψ)) = c * unp M₁ l (e Ψ) := by
  obtain ⟨f, rfl⟩ := hΨ
  rw [← pv_smul, un_e hM hM₁ h, un_e hM hM₁ h, map_smul, map_smul, smul_eq_mul]

theorem at_mulVec {g : Matrix (Fin n) (Fin n) (AE F E)} {x : Fin n → AE F E} (h : At (evI F) x) : At (evI F) (g *ᵥ x) := fun a ha => by
  rw [← Matrix.mulVec_smul, h a ha, Matrix.mulVec_zero]

theorem at_vv {x : Fin n → AE F E} (h : At (evI F) x) (y : Fin d → AE F E) : At (evI F) (Matrix.vecMulVec x y) := fun a ha => by
  rw [← Matrix.smul_vecMulVec, h a ha, Matrix.zero_vecMulVec]

theorem at_smul2 {N : Type} [AddCommGroup N] [Module (AF F) N] [Module (AE F E) N] [IsScalarTower (AF F) (AE F E) N] {c : AE F E}
    (h : At (evI F) c) (x : N) : At (evI F) (c • x) := fun a ha => by rw [← smul_assoc, h a ha, zero_smul]

theorem mix_un (hA : ArchOp) {M : Model σ X W} {M₁ : Model σ X₁ W₁} {χX χW om om₁ r s r' s' r₁ s₁ r₁' s₁'}
    (hP : IsPair B M χX χW om r s r' s') (hP₁ : IsPair B M₁ χX χW om₁ r₁ s₁ r₁' s₁') {H : Plane E n n₁} {H' : Plane E d d₁} {i j}
    (hH : H.IsAdapted σ B X X₁ i j) {e ei ev} (h : IsEvLoc M M₁ e ei ev) {rX rW} (hm : Mix2 H H' χX χW rX rW om om₁ e)
    {l : SInf F _ →L[ℂ] ℂ} (hl : ∀ g ∈ UAt σ X₁ (evI F), ∀ f f₁ : SInf F _, Acts (evI F) (om₁ (g, 1)) f f₁ → l f₁ = l f)
    {k} (hk : k ∈ UAt σ X (evI F)) {t : (AE F E)ˣ} (ht : mat k *ᵥ incV F H.x = t.1 • incV F H.x) :
    (∀ Ψ, (∃ f, Ψ = PV M f) → unp M₁ l (e (om (k, 1) Ψ)) = (χW t : ℂ) * (((absE F E t : ℝ) ^ rX : ℝ) : ℂ) * unp M₁ l (e Ψ)) ∧
    ∃ (U : Fin n₁ → AE F E) (c : AE F E), mat k⁻¹ *ᵥ incV F H.y = incM F H.ι *ᵥ U + c • incV F H.x + cA σ t.1 • incV F H.y := by
  obtain ⟨ε, A', hF⟩ := isFr hP.base (Or.inl hP.herm) hH
  obtain ⟨u, hu, g₁, m, hL, rfl, hg⟩ := stab_dec hP.base.cm hF (det_ne (Or.inl hP.herm)) k t ht
  have hg₁ : g₁ ∈ UAt σ X₁ (evI F) := fun a ha => by
    have e1 : mat g₁ - 1 = (incM F A' * (mat (u * m) - 1) * fr (incM F H.ι) (incV F H.x) (incV F H.y)).toBlocks₁₁ := by
      rw [hg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, (IsFr.ad hF).inv2]
      ext a b; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
    have e2 : a • (incM F A' * (mat (u * m) - 1) * fr (incM F H.ι) (incV F H.x) (incV F H.y)) = 0 := by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, hk a ha, Matrix.mul_zero, Matrix.zero_mul]
    rw [e1]
    ext b c
    exact congrFun (congrFun e2 (Sum.inl b)) (Sum.inl c)
  constructor
  · rintro _ ⟨f, rfl⟩
    have := hm t g₁ m hL u hu 1 1 1 levi_one 1 (one_mem _) _ (pv_sch hP.good f)
    rw [mul_one] at this
    obtain ⟨T, hT, -⟩ := hA F E σ B n₁ d₁ X₁ W₁ M₁ χX χW om₁ _ _ _ _ hP₁ g₁ hg₁ 1 (one_at (J := W₁.J) W₁)
    rw [this, e_pv hP.good h, pv_act hP₁.good (hT.2 _), ← pv_smul, un_pv hP₁.good, un_pv hP₁.good, map_smul, hl g₁ hg₁ _ _ (hT.2 _)]
    simp
  · obtain ⟨U, c, hU⟩ := (IsFr.ad hF).fix_y (PositivityTheory.ThKG.Tow.Levi.cA_cA hP.base.cm) (u⁻¹).2 (mem_unip.1 (inv_mem hu)).1
    have h2 := levi_inv hL
    refine ⟨mat g₁⁻¹ *ᵥ U, c * (t⁻¹).1, ?_⟩
    rw [mul_inv_rev, mat_mul, ← Matrix.mulVec_mulVec]
    change mat m⁻¹ *ᵥ ((u⁻¹).1.1 *ᵥ _) = _
    rw [hU, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, h2.1, h2.2.1, levi_vec h2, inv_inv, smul_smul]
    abel

end PositivityTheory.ThKG.Loc.Bump

end
