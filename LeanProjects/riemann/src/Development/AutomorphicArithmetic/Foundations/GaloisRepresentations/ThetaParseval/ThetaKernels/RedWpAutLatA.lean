import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutLatA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutDef
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GamQFEqOneIffK

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
namespace AutLatA
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
theorem sgsg_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
theorem mem_iff_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hR : RatSD σ JS JT ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ)) (y : Matrix (Fin nT) (Fin nS) E) :
    finRatF F y ∈ latF F E nS nT Λ ↔ y ∈ Λ :=
  ⟨fun h => (hR y).2 fun M' hM' => (_root_.PositivityTheory.ThKW.gamQF_eq_one_iff'_k C y M').1 ((hA _).1 h _ (finRatF_mem_of hM')),
    finRatF_mem_of⟩
theorem sdQ_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hR : RatSD σ JS JT ξ₀ Λ) : SelfDual (gamQF σ JS JT ξ₀ B.ψ) Λ := fun x =>
  (hR x).trans (forall₂_congr fun y _ => (_root_.PositivityTheory.ThKW.gamQF_eq_one_iff'_k C x y).symm)
theorem norm_emb_eq_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (φ : E →+* ℂ) (x : E) :
    ∃ v : InfinitePlace F, ‖φ x‖ = ‖tauB B v x‖ := by
  have hcm := hB.cm
  let ρ : F →+* ℂ := φ.comp (algebraMap F E)
  refine ⟨InfinitePlace.mk ρ, ?_⟩
  have hρ : ComplexEmbedding.IsReal ρ := by
    have := hcm.1.isReal (InfinitePlace.mk ρ)
    rwa [InfinitePlace.isReal_mk_iff] at this
  have he : (InfinitePlace.mk ρ).embedding = ρ := by
    rcases InfinitePlace.embedding_mk_eq ρ with h | h
    · exact h
    · rw [h]; exact hρ
  have hτ : (tauB B (InfinitePlace.mk ρ)).comp (algebraMap F E) = ρ := by
    exact (B.emb (InfinitePlace.mk ρ)).2.trans he
  obtain ⟨c, hc⟩ := PI.OmLocU.Red.fix_range σ hcm (y := x * σ x) (by rw [map_mul, _root_.PositivityTheory.ThKW.AutLatA.sgsg_k hB, mul_comm])
  have key : ∀ τ : E →+* ℂ, τ.comp (algebraMap F E) = ρ → Complex.normSq (τ x) = ρ c := fun τ hτ => by
    rw [← hτ, RingHom.comp_apply, hc, map_mul, hcm.2.2.2 τ]
    exact (Complex.mul_conj (τ x)).symm
  have h2 := (key φ rfl).trans (key _ hτ).symm
  rw [Complex.ofReal_inj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
theorem finLat_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hG : GoodLat Λ) (R : ℝ) : {y | y ∈ Λ ∧ ‖infRatF (tauB B) y‖ ≤ R}.Finite := by
  obtain ⟨d, hd, hdi⟩ := exists_denomM hG.fg
  have hS := GlobalTheory.CompletedLatticeFinite.finite_of_denom d hd R
  refine (Set.Finite.pi fun _ : Fin nT => Set.Finite.pi fun _ : Fin nS => hS).subset ?_
  rintro y ⟨hy, hR⟩ i - j -
  refine ⟨hdi y hy i j, fun φ => ?_⟩
  obtain ⟨v, hv⟩ := _root_.PositivityTheory.ThKW.AutLatA.norm_emb_eq_k hB φ (y i j)
  rw [hv]
  exact (norm_le_pi_norm (infRatF (tauB B) y) ((i, j), v)).trans hR
theorem isHeisQ_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (hw : w + sgOF σ w = 1) :
    IsHeis (sgOF σ) w (gamQF σ JS JT ξ₀ B.ψ) fun x => opFF hc w (finRatF F x) := by
  have H := isHeis_opFF (_root_.PositivityTheory.ThKW.AutLatA.sgsg_k C.good) C.hS C.hT C.hξ hc hw
  have e : ∀ x y, gamQF σ JS JT ξ₀ B.ψ x y = gamFF σ JS JT ξ₀ B.ψ (finRatF F x) (finRatF F y) := fun _ _ => rfl
  exact ⟨H.sg_sg, H.w_add, fun x y z => by rw [e, e, e, map_add, H.add_left],
    fun x y z => by rw [e, e, e, map_add, H.add_right], fun x => by rw [e, H.alt],
    fun r x y => by rw [e, e, map_smul, map_smul, H.adj], fun v => by rw [map_zero, H.zero],
    fun x y v => by rw [H.comp, e, map_smul, map_add]⟩
theorem idx_eq_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) =
      Λ.toAddSubgroup.relIndex (Λ.toAddSubgroup.comap (GlobalTheory.RatAut.sandw b a).toAddMonoidHom) := by
  have hmem := _root_.PositivityTheory.ThKW.AutLatA.mem_iff_k C hR hO.sd
  have hfin := hO.fin (g⁻¹, h⁻¹)
  have hmov : ∀ u ∈ latF F E nS nT Λ,
      idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • u ∈
        (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)) := fun u hu => by
    rw [mem_map_rho, map_nsmul]
    exact AddSubgroup.nsmul_relIndex_mem (latF F E nS nT Λ).toAddSubgroup (Submodule.mem_map_of_mem hu)
  rw [GlobalTheory.FinWeil.idx, ← GlobalTheory.RatLattice.relIndex_comap_comap (finRatF F (E := E) (nS := nS) (nT := nT)).toAddMonoidHom]
  · congr 1
    · ext x; exact hmem x
    · ext x
      show finRatF F x ∈ (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)) ↔ b * x * a ∈ Λ
      rw [mem_map_rho, rhoFF_finRatF ha hb, hmem]
  · intro z hz
    have hN := Nat.pos_of_ne_zero hfin
    obtain ⟨γ, hγ⟩ := lat_approx hG _ (incAF F E ((idx (latF F E nS nT Λ)
      ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) : ℕ) : E)⁻¹ • z).fin
    obtain ⟨u, hu, e⟩ : ∃ u ∈ latF F E nS nT Λ, z = finRatF F (idx (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • γ) +
        idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • u :=
      ⟨_, hγ, by rw [map_nsmul, ← nsmul_add, add_sub_cancel, nsmul_inv_smul' (F := F) (E := E) hN]⟩
    refine ⟨idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • γ, ?_, ?_⟩
    · show finRatF F _ ∈ (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))
      rw [eq_sub_of_add_eq e.symm]
      exact sub_mem hz (hmov u hu)
    · show z - finRatF F _ ∈ latF F E nS nT Λ
      rw [sub_eq_of_eq_add' e]
      exact nsmul_mem hu _
open GlobalTheory.RatAut in
theorem data_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hΔ : (b ⊗ₖ aᵀ).det ≠ 0) (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x) ∧
    ∃ (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (c N M : ℕ), n ≠ 0 ∧ c ≠ 0 ∧ N ≠ 0 ∧
      (∀ k, b * t k * a - t k ∈ Λ) ∧ (∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) ∧
      ∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k) = lam n ∧ lam n ^ 2 = n ∧
      ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ - 1).det)| ∧
      ((c * idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) : ℕ) : ℚ) =
        |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ).det)| := by
  have sd := _root_.PositivityTheory.ThKW.AutLatA.sdQ_k C hR
  obtain ⟨d, hd0, hdi⟩ := exists_denomM hG.fg
  have fg : Λ.toAddSubgroup.FG := GlobalTheory.RatLattice.fg_of_denom _ d hd0 hdi
  have full := hG.den
  rw [_root_.PositivityTheory.ThKW.AutLatA.idx_eq_k C hG hR hO ha hb]
  rw [← det_sandw] at hΔ ⊢
  rw [← det_sandw_sub_one] at hd ⊢
  have hbij : Function.Bijective ⇑(sandw b a - 1) :=
    (Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 hd.isUnit)
  refine ⟨hbij, ?_⟩
  set A := Λ.toAddSubgroup with hA
  obtain ⟨N, hN, hNA⟩ : ∃ N : ℕ, N ≠ 0 ∧ ∀ x ∈ A, N • sandw b a x ∈ A := by
    obtain ⟨s, hs⟩ := fg
    choose k hk hk' using full
    refine ⟨∏ y ∈ s, k (sandw b a y), Finset.prod_ne_zero_iff.2 fun y _ => (hk _).ne', fun x hx => ?_⟩
    rw [← hs] at hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun y => k (sandw b a y)) hx
      rw [hm, mul_comm, mul_smul]
      exact nsmul_mem (hk' _) m
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx
  have i1 := GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det _ _ A fg full (sandw b a - 1) N hN hd fun x hx => by
    rw [LinearMap.sub_apply, smul_sub]
    exact sub_mem (hNA x hx) (nsmul_mem hx N)
  have i2 := GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det _ _ A fg full (sandw b a) N hN hΔ hNA
  set B₁ := A.comap (sandw b a - 1).toAddMonoidHom with hB₁
  set B₂ := A.comap (sandw b a).toAddMonoidHom with hB₂
  set NA := A.map (N • AddMonoidHom.id _) with hNA'
  have e12 : A ⊓ B₁ = A ⊓ B₂ := by
    ext x
    refine and_congr_right fun hx => ?_
    show sandw b a x - x ∈ A ↔ sandw b a x ∈ A
    exact ⟨fun h => by simpa using add_mem h hx, fun h => sub_mem h hx⟩
  have hle : NA ≤ A ⊓ B₂ := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨nsmul_mem hx N, ?_⟩
    show sandw b a (N • x) ∈ A
    rw [map_nsmul]
    exact hNA x hx
  have m1 := AddSubgroup.relIndex_mul_relIndex NA (A ⊓ B₁) B₁ (e12 ▸ hle) inf_le_right
  have m2 := AddSubgroup.relIndex_mul_relIndex NA (A ⊓ B₂) B₂ hle inf_le_right
  rw [AddSubgroup.inf_relIndex_right] at m1 m2
  rw [e12] at m1
  have h0 : NA.relIndex (A ⊓ B₂) * A.relIndex B₁ ≠ 0 := by
    rw [m1, ← Nat.cast_ne_zero (R := ℚ), i1, abs_ne_zero, Algebra.norm_ne_zero_iff]
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hN)) hd
  obtain ⟨t, t1, t2⟩ := exists_transversal A B₁ (right_ne_zero_of_mul h0)
  obtain ⟨g1, g2⟩ := gauss_isometry (_root_.PositivityTheory.ThKW.AutLatA.isHeisQ_k C hc hO.hw) hO.good sd ((sandw b a).restrictScalars (𝓞 E))
    (fun x y => by
      show gamFF σ JS JT ξ₀ B.ψ (finRatF F (b * x * a)) (finRatF F (b * y * a)) =
        gamFF σ JS JT ξ₀ B.ψ (finRatF F x) (finRatF F y)
      rw [← rhoFF_finRatF ha hb, ← rhoFF_finRatF ha hb]
      unfold gamFF
      rw [coe_rhoFF, coe_rhoFF, _root_.PositivityTheory.ThKW.symplOF_actOF_k C]) hbij.2 _ t t1 t2
  exact ⟨_, t, _, N, _, right_ne_zero_of_mul h0, left_ne_zero_of_mul h0, hN, t1, t2, g1, g2, m1 ▸ i1, m2 ▸ i2⟩
end AutLatA
end PositivityTheory.ThKW
end
end
