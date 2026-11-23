import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesInsertZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

noncomputable section
namespace GlobalTheory.ThK.PlaneEv

namespace AdaptedJ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (e : E) :
    piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  have := congrFun (congrFun (incM_map_piInf_emb (F := F) (Matrix.of fun (_ : Unit) (_ : Unit) => e) τ) ()) ()
  simpa [incM] using this

theorem exists_plane_decomp {σ : E →ₐ[F] E} {B : Base F E} {d d₁ i₀ i₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁}
    {H' : Plane E d d₁} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (hL : W.L.IsLattice E) (v : Fin d → E) :
    ∃ (s t : E) (u : Fin d₁ → E), v = s • H'.x + H'.ι *ᵥ u + t • H'.y := by
  have hv : v ∈ Submodule.span E (W.L : Set (Fin d → E)) := by rw [hL.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, t, u, -, -, -, h⟩ := hH.split z hz
    exact ⟨s, t, u, h⟩
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨s, t, u, h⟩ := hp
    obtain ⟨s', t', u', h'⟩ := hq
    exact ⟨s + s', t + t', u + u', by rw [h, h', Matrix.mulVec_add, add_smul, add_smul]; abel⟩
  | smul c p _ hp =>
    obtain ⟨s, t, u, h⟩ := hp
    exact ⟨c * s, c * t, c • u, by rw [h, Matrix.mulVec_smul, smul_add, smul_add, smul_smul, smul_smul]⟩

theorem one_eq_plane_decomp {σ : E →ₐ[F] E} {B : Base F E} {d d₁ i₀ i₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁}
    {H' : Plane E d d₁} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (hL : W.L.IsLattice E) :
    ∃ (U : Matrix (Fin d) (Fin d₁) E) (s t : Fin d → E),
      (1 : Matrix (Fin d) (Fin d) E) = U * H'.ιᵀ + Matrix.vecMulVec s H'.x + Matrix.vecMulVec t H'.y := by
  choose s t U hU using fun k : Fin d => exists_plane_decomp hH hL (Pi.single k 1)
  refine ⟨Matrix.of U, s, t, ?_⟩
  ext k l
  have := congrFun (hU k) l
  simp [Matrix.one_apply, Pi.single_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply] at this ⊢
  have e : (if k = l then (1 : E) else 0) = if l = k then 1 else 0 := by
    by_cases h : k = l <;> simp [h, eq_comm]
  rw [e, this]
  simp_rw [mul_comm (H'.ι l _)]
  ring

theorem adelic_plane_decomp {n d d₁ : ℕ} {ι : Matrix (Fin d) (Fin d₁) E} {x y : Fin d → E}
    {U : Matrix (Fin d) (Fin d₁) E} {s t : Fin d → E}
    (h : (1 : Matrix (Fin d) (Fin d) E) = U * ιᵀ + Matrix.vecMulVec s x + Matrix.vecMulVec t y)
    (u : Matrix (Fin n) (Fin d) (AE F E)) :
    u = (u * incM F U) * (incM F ι)ᵀ + Matrix.vecMulVec (u *ᵥ incV F s) (incV F x) +
      Matrix.vecMulVec (u *ᵥ incV F t) (incV F y) := by
  have h1 : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hv : ∀ p q : Fin d → E, incM F (Matrix.vecMulVec p q) = Matrix.vecMulVec (incV F p) (incV F q) := fun p q => by
    ext i j; simp [incM, incV, Matrix.vecMulVec_apply]
  have hm : incM F (U * ιᵀ) = incM F U * (incM F ι)ᵀ := by
    simp only [incM]
    rw [Matrix.map_mul, Matrix.transpose_map]
  conv_lhs => rw [← Matrix.mul_one u, ← h1, h]
  simp only [incM] at hv hm ⊢
  rw [Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), hm, hv, hv, Matrix.mul_add, Matrix.mul_add, Matrix.mul_vecMulVec,
    Matrix.mul_vecMulVec, Matrix.mul_assoc]

theorem inl_symm_eq_zero {F : Type} [Field F] [NumberField F] (g : mixedEmbedding.mixedSpace F) (hg : g = 0) :
    LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm g) = 0 := by
  subst hg
  rw [map_zero, map_zero]

end AdaptedJ

open AdaptedJ in

theorem exists_plane_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M₁ : Model σ X W₁)
    (hd : d = d₁ + 2), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d),
    (∀ z : Matrix (Fin n) (Fin d₁) (AE F E), co.e (z * (incM F H'.ι)ᵀ) = (ins0 hd (M₁.co.e z).1, ins0 hd (M₁.co.e z).2)) →
    (∀ a : Fin n → AE F E, (co.e (Matrix.vecMulVec a (incV F H'.x))).1 = 0 ∧
        ∀ p, (co.e (Matrix.vecMulVec a (incV F H'.x))).2 ((idx hd).symm (Sum.inl p)) = 0) →
    (∀ b : Fin n → AE F E, (co.e (Matrix.vecMulVec b (incV F H'.y))).2 = 0 ∧
        ∀ p, (co.e (Matrix.vecMulVec b (incV F H'.y))).1 ((idx hd).symm (Sum.inl p)) = 0) →
    ∀ (ε : InfinitePlace F → ℤˣ) (γ : Fin n × Fin d → mixedEmbedding.mixedSpace F), IsPl hd γ →
    ∃ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u ∧ At (evI F) u' ∧
      (∀ w, u'.map (piInf (B.emb w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) ∧
      cw co u = (γ, 0) ∧ (cw co u').1 = 0 ∧ IsPl hd (cw co u').2 := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M₁ hd hB hX hW hH co h1 h2 h3 ε γ hγ
  have hcm := hB.cm
  haveI := hcm.1
  obtain ⟨ξ, hξ⟩ := GlobalTheory.RealLift.OneParam.exists_moved hcm
  have hξ' : ∀ w, ((B.emb w).1 ξ).im ≠ 0 := fun w => GlobalTheory.RealLift.OneParam.im_ne_zero hcm hξ (B.emb w).1
  obtain ⟨U, sv, tv, hone⟩ := one_eq_plane_decomp hH hW.lat
  set L : Fin n × Fin d → AF F := fun i =>
    LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (γ i)) with hLdef
  set u := co.e.symm (L, 0) with hudef
  have hu : co.e u = (L, 0) := co.e.apply_symm_apply _
  have hLat : ∀ t : AF F, evI F t = 0 → t • L = 0 := fun t ht => by
    funext i
    refine Prod.ext ?_ ?_
    · change t.1 * _ = 0
      rw [GlobalTheory.RealLift.OneParam.inf_eq_zero ht, zero_mul]
    · change t.2 * 0 = 0
      exact mul_zero _
  have huAt : At (evI F) u := fun t ht => by
    rw [hudef, ← map_smul, Prod.smul_mk, hLat t ht, smul_zero]
    exact map_zero _
  have hcwu : cw co u = (γ, 0) := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show evI F ((co.e u).1 i) = γ i
      rw [hu]
      show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (γ i)) = γ i
      exact RingEquiv.apply_symm_apply _ _
    · show evI F ((co.e u).2 i) = 0
      rw [hu]
      exact evI_zero_eq
  set z := u * incM F U with hzdef
  set a := u *ᵥ incV F sv with hadef
  set b := u *ᵥ incV F tv with hbdef
  have hdec : u = z * (incM F H'.ι)ᵀ + Matrix.vecMulVec a (incV F H'.x) + Matrix.vecMulVec b (incV F H'.y) :=
    adelic_plane_decomp hone u
  have hsum : co.e (z * (incM F H'.ι)ᵀ) + co.e (Matrix.vecMulVec a (incV F H'.x)) +
      co.e (Matrix.vecMulVec b (incV F H'.y)) = (L, 0) := by
    rw [← map_add, ← map_add, ← hdec, hu]
  obtain ⟨ha1, ha2⟩ := h2 a
  obtain ⟨hb2, hb1⟩ := h3 b
  have hz : M₁.co.e z = 0 := by
    refine Prod.ext (funext fun p => ?_) (funext fun p => ?_)
    · have e := congrArg (fun q => q.1 ((idx hd).symm (Sum.inl p))) hsum
      simp only [Prod.fst_add, Pi.add_apply, h1 z, ha1, hb1 p, planeZeroInsertion_apply_inl, Pi.zero_apply, add_zero] at e
      have key : L ((idx hd).symm (Sum.inl p)) = 0 := by
        rw [hLdef]
        exact inl_symm_eq_zero _ (hγ p)
      rw [key] at e
      exact e
    · have e := congrArg (fun q => q.2 ((idx hd).symm (Sum.inl p))) hsum
      simp only [Prod.snd_add, Pi.add_apply, h1 z, ha2 p, hb2, planeZeroInsertion_apply_inl, Pi.zero_apply, add_zero] at e
      exact e
  have hzi : co.e (z * (incM F H'.ι)ᵀ) = 0 := by
    rw [h1 z, hz]
    simp [ins0_zero]
  have hax : co.e (Matrix.vecMulVec a (incV F H'.x)) = 0 := by
    refine Prod.ext ha1 ?_
    have e := congrArg Prod.snd hsum
    simp only [Prod.snd_add, hzi, hb2] at e
    simpa using e
  have hu' : u = Matrix.vecMulVec b (incV F H'.y) := by
    rw [hdec, co.e.map_eq_zero_iff.1 hzi, co.e.map_eq_zero_iff.1 hax, zero_add, zero_add]
  choose c hc0 hcy using fun w => (hH.cartan w).2
  have hθ : ∀ w, W.θ w *ᵥ (fun i => (B.emb w).1 (H'.y i)) = c w • fun i => (B.emb w).1 (H'.x i) := fun w => by
    rw [hcy w, Matrix.mulVec_smul, Matrix.mulVec_mulVec, (hW.cartan w).1, Matrix.one_mulVec]
  set b' : Fin n → AE F E := fun i => GlobalTheory.RealLift.OneParam.liftC B.emb ξ
    (fun w => (((ε w : ℤ) : ℂ) * Complex.I * c w) * (X.θ w *ᵥ fun j => piInf (B.emb w) (b j)) i) with hb'def
  refine ⟨u, Matrix.vecMulVec b' (incV F H'.x), huAt, ?_, ?_, hcwu, ?_, ?_⟩
  · intro t ht
    have : t • b' = 0 := funext fun i => GlobalTheory.RealLift.OneParam.at_liftC B.emb ξ _ t ht
    rw [← Matrix.smul_vecMulVec, this]
    ext i j
    simp
  · intro w
    have hm : (Matrix.vecMulVec b (incV F H'.y)).map (piInf (B.emb w)) =
        Matrix.vecMulVec (fun j => piInf (B.emb w) (b j)) (fun l => (B.emb w).1 (H'.y l)) := by
      ext i l
      simp [Matrix.vecMulVec_apply, incV, piInf_inclR]
    have hm' : (Matrix.vecMulVec b' (incV F H'.x)).map (piInf (B.emb w)) =
        Matrix.vecMulVec (fun i => (((ε w : ℤ) : ℂ) * Complex.I * c w) * (X.θ w *ᵥ fun j => piInf (B.emb w) (b j)) i)
          (fun l => (B.emb w).1 (H'.x l)) := by
      ext i l
      simp only [Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, incV, piInf_inclR, hb'def,
        GlobalTheory.RealLift.OneParam.piInf_liftC B.emb hξ']
    rw [hu', hm, hm', Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hθ w,
      Matrix.vecMulVec_smul]
    ext i l
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · funext i
    show evI F ((co.e (Matrix.vecMulVec b' (incV F H'.x))).1 i) = 0
    rw [(h2 b').1]
    exact evI_zero_eq
  · intro p
    show evI F ((co.e (Matrix.vecMulVec b' (incV F H'.x))).2 ((idx hd).symm (Sum.inl p))) = 0
    rw [(h2 b').2 p]
    exact evI_zero_eq

end GlobalTheory.ThK.PlaneEv
