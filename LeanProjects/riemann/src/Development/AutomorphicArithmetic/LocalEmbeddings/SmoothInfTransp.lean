import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedRepLocalFactorFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DopEqSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslationStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothContinuousConvolutionRealPointsUnitary

noncomputable section

namespace GlobalTheory.ThKCentreTransp

section Inst

open NumberField Matrix Formalism.MainNotions.S Formalism.REAL GlobalTheory.Dec
open scoped ContDiff

private theorem Eword_mul_left {n : ℕ} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (k : Matrix (Fin n) (Fin n) ℂ)
    (w : List (Fin n × Fin n)) : Eword ε w (fun y => f (k * y)) = fun y => Eword ε w f (k * y) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    funext y
    simp only [Eword, Eab, Ec, Rd, ih, Matrix.mul_assoc]

variable {I : AutInst}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private theorem smoothOnG_slice {f : I.GA → ℂ} (hf : ∀ xf, SmoothInf I fun y => f (y, xf)) (v : InfinitePlace I.F)
    (x : I.GA) : SmoothOnG (I.ε v) (slice I f x v) := by
  classical
  intro g₀ _
  obtain ⟨A, hA, hAa⟩ := GlobalTheory.SmoothConv.exists_contDiff_extension I (hf x.2)
  refine ⟨Set.univ, fun y => A (fun w i j => if w = v then ∑ k, uMat (x.1 v) i k * y k j else uMat (x.1 w) i j),
    isOpen_univ, trivial, ContDiff.contDiffOn (hA.comp ?_), fun y _ hy => ?_⟩
  · refine contDiff_pi.2 fun w => contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    split_ifs
    · refine ContDiff.sum fun k _ => contDiff_const.mul ?_
      exact (contDiff_apply_apply ℝ ℂ k j : ContDiff ℝ ∞ fun y : Fin I.n → Fin I.n → ℂ => y k j)
    · exact contDiff_const
  · have hu : Jm (I.ε v) * yᴴ * Jm (I.ε v) * y = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc yᴴ, hy, Jm_mul_self]
    let u : UJ (I.ε v) := ⟨⟨y, _, mul_eq_one_comm.1 hu, hu⟩, hy⟩
    refine (slice_apply I f x v u).trans ?_
    have e : x * (Pi.mulSingle v u, 1) = (x.1 * Pi.mulSingle v u, x.2) := by ext1 <;> simp
    rw [e, ← hAa]
    refine congrArg A ?_
    funext w i j
    by_cases hw : w = v
    · subst hw
      simp only [GlobalTheory.SmoothConv.emb, Pi.mul_apply, Pi.mulSingle_eq_same, if_true]
      rfl
    · simp [GlobalTheory.SmoothConv.emb, hw]

theorem zOp_mul_right {f : I.GA → ℂ} (hf : ∀ xf, SmoothInf I fun y => f (y, xf)) (v : InfinitePlace I.F) (m : ℕ)
    (x b : I.GA) : zOp I v m (fun y => f (y * b)) x = zOp I v m f (x * b) := by
  classical
  set x' : I.GA := x * b * (Pi.mulSingle v (b.1 v)⁻¹, 1) with hx'
  have h1 : zOp I v m (fun y => f (y * b)) x = gelf (I.ε v) m (fun y => slice I f x' v (y * uMat (b.1 v))) 1 := by
    refine zOp_eq_gelf I v m _ x _ fun g => ?_
    refine (slice_apply I f x' v (g * b.1 v)).trans (congrArg f ?_)
    rw [hx', mul_assoc, mul_assoc, mul_assoc]
    congr 1
    refine Prod.ext (funext fun w => ?_) (by simp)
    by_cases hw : w = v
    · subst hw; simp
    · simp [Pi.mulSingle_eq_of_ne hw]
  have h2 : zOp I v m f (x * b) = gelf (I.ε v) m (fun y => slice I f x' v (uMat (b.1 v) * y)) 1 := by
    refine zOp_eq_gelf I v m _ _ _ fun g => ?_
    refine (slice_apply I f x' v (b.1 v * g)).trans (congrArg f ?_)
    rw [hx', mul_assoc]
    congr 1
    refine Prod.ext (funext fun w => ?_) (by simp)
    by_cases hw : w = v
    · subst hw; simp
    · simp [Pi.mulSingle_eq_of_ne hw]
  rw [h1, h2, GlobalTheory.T.gelfandInvariant_comm_rightTranslation _ _ m _ _ 1 (smoothOnG_slice hf v x') (b.1 v).2 (show inUJ _ _ by simp [inUJ])]
  simp only [gelf, Eword_mul_left, Matrix.mul_one, Matrix.one_mul]

end Inst

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThKAdm GlobalTheory.ThK.SquareIntegrability GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.Dec GlobalTheory.ThKAdmAut
open Formalism.MainNotions.S (AutInst uMat)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}
  {B : Base F E} {W : Spc F E d} {L : Subgroup (UA σ W.J)} {I : AutInst} {g : ℕ} {e : I.GA →* UA σ W.J}

private theorem smoothInf_transp (hcm : IsCMExt F E σ) (hσ : ∀ x, σ (σ x) = x) {c : E} (hc : c ≠ 0)
    (he : IsTransp B W L I g e) {f : GAd σ (c • W.J.map σ) → ℂ} (hf : IsSm σ (c • W.J.map σ) f) (xf : I.Gf) :
    SmoothInf I fun y => f (toGAd hσ W.J hc (e (y, xf))) := by
  refine smoothInf_of_lines fun k γ hγ x => ?_
  have h1 := hf k _ (fun i => isRealLine_transp hcm hσ hc he (hγ i)) (toGAd hσ W.J hc (e (x, xf)))
  convert h1 using 3 with t
  have h2 : ((x * (List.ofFn fun i => γ i (t i)).prod, xf) : I.GA) =
      (x, xf) * MonoidHom.inl _ _ (List.ofFn fun i => γ i (t i)).prod := by simp
  simp only [h2, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, MonoidHom.inl_apply]

open Classical in

private theorem exists_line (hcm : IsCMExt F E σ) (hσ : ∀ x, σ (σ x) = x) {c : E} (hc : c ≠ 0)
    (he : IsTransp B W L I g e) (v : InfinitePlace I.F) {Z : Matrix (Fin I.n) (Fin I.n) ℂ} (hZ : Formalism.REAL.inG (I.ε v) Z) :
    ∃ γ, IsRealLine σ (c • W.J.map σ) γ ∧ ∀ (S : Matrix (Fin I.n) (Fin I.n) ℂ → ℂ) (ψ : GAd σ (c • W.J.map σ) → ℂ) (x : I.GA),
      (∀ u : Formalism.REAL.UJ (I.ε v), S (uMat u) = ψ (toGAd hσ W.J hc (e (x * (Pi.mulSingle v u, 1))))) →
      ∀ u : Formalism.REAL.UJ (I.ε v), Formalism.REAL.Rd Z S (uMat u) = lineDer γ ψ (toGAd hσ W.J hc (e (x * (Pi.mulSingle v u, 1)))) := by
  let p : ℝ → Formalism.REAL.UJ (I.ε v) := fun t =>
    ⟨(Matrix.isUnit_exp ((t : ℂ) • Z)).unit, Formalism.REAL.exp_indefinite_unitary_holds I.n (I.ε v) Z hZ t⟩
  have hp : ∀ t, uMat (p t) = NormedSpace.exp ((t : ℂ) • Z) := fun _ => rfl
  refine ⟨fun t => toGAd hσ W.J hc (e (Pi.mulSingle v (p t), 1)),
    isRealLine_transp hcm hσ hc he (γ := fun t => Pi.mulSingle v (p t))
      ⟨v, Z, fun t => ⟨by beta_reduce; rw [Pi.mulSingle_eq_same, hp]; exact congrArg _ (by ext; simp), fun u hu => Pi.mulSingle_eq_of_ne hu _⟩⟩,
    fun S ψ x h u => ?_⟩
  unfold Formalism.REAL.Rd lineDer
  congr 1
  funext t
  have e1 : ((Pi.mulSingle v u, 1) : I.GA) * (Pi.mulSingle v (p t), 1) = (Pi.mulSingle v (u * p t), 1) := by
    rw [Prod.mk_mul_mk, ← Pi.mulSingle_mul, mul_one]
  rw [← hp, ← map_mul, ← map_mul, mul_assoc, e1]
  exact h (u * p t)

open Classical in

private theorem exists_word (hcm : IsCMExt F E σ) (hσ : ∀ x, σ (σ x) = x) {c : E} (hc : c ≠ 0)
    (he : IsTransp B W L I g e) (v : InfinitePlace I.F) (w : List (Fin I.n × Fin I.n)) :
    ∃ z : List (ℝ → GAd σ (c • W.J.map σ)) →₀ ℂ, (∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ (c • W.J.map σ) γ) ∧
      ∀ f, IsSm σ (c • W.J.map σ) f → ∀ (x : I.GA) (u : Formalism.REAL.UJ (I.ε v)),
        Formalism.REAL.Eword (I.ε v) w (slice I (fun y => f (toGAd hσ W.J hc (e y))) x v) (uMat u) =
          dop z f (toGAd hσ W.J hc (e (x * (Pi.mulSingle v u, 1)))) := by
  induction w with
  | nil =>
    refine ⟨Finsupp.single [] 1, by simp, fun f _ x u => ?_⟩
    rw [dop_single]
    simp only [Formalism.REAL.Eword, id, List.foldr_nil, one_mul]
    exact slice_apply I _ x v u
  | cons p w ih =>
    obtain ⟨z, hz, ez⟩ := ih
    have hp := Formalism.REAL.complex_parts_mem_lie_algebra_holds I.n (I.ε v) (Matrix.single p.1 p.2 1)
    obtain ⟨γ, hγ, eγ⟩ := exists_line hcm hσ hc he v hp.1
    obtain ⟨δ, hδ, eδ⟩ := exists_line hcm hσ hc he v hp.2.1
    have hy : ∀ l ∈ (Finsupp.single [γ] (1 : ℂ) + Finsupp.single [δ] Complex.I).support, ∀ ε ∈ l,
        IsRealLine σ (c • W.J.map σ) ε := fun l hl ε hε => by
      rcases Finset.mem_union.1 (Finsupp.support_add hl) with hl | hl <;>
        obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hl) <;>
        obtain rfl := List.mem_singleton.1 hε
      exacts [hγ, hδ]
    refine ⟨wordMul (Finsupp.single [γ] 1 + Finsupp.single [δ] Complex.I) z, fun m hm ε hε => ?_, fun f hf x u => ?_⟩
    · obtain ⟨l, hl, l', hl', rfl⟩ := mem_support_wordMul hm
      rcases List.mem_append.1 hε with h | h
      exacts [hy l hl ε h, hz l' hl' ε h]
    · rw [← (GlobalTheory.UAut.DopComp.dop_dop σ _ f hf _ z hy hz).2, dop_add_comb, dop_single, dop_single]
      simp only [Formalism.REAL.Eword, Formalism.REAL.Eab, Formalism.REAL.Ec]
      rw [eγ _ _ x (ez f hf x) u, eδ _ _ x (ez f hf x) u]
      simp

theorem exists_central (hcm : IsCMExt F E σ) (hσ : ∀ x, σ (σ x) = x) {c : E} (hc : c ≠ 0)
    (he : IsTransp B W L I g e) (v : InfinitePlace I.F) (m : ℕ) :
    ∃ z : List (ℝ → GAd σ (c • W.J.map σ)) →₀ ℂ, IsCentral σ (c • W.J.map σ) z ∧
      ∀ (N : ℕ) (f : GAd σ (c • W.J.map σ) → ℂ), IsSm σ (c • W.J.map σ) f →
        (zOp I v m)^[N] (fun y => f (toGAd hσ W.J hc (e y))) = fun y => (dop z)^[N] f (toGAd hσ W.J hc (e y)) := by
  classical
  choose z hz ez using exists_word hcm hσ hc he v
  have hs : ∀ l ∈ (∑ a : Fin (m + 1) → Fin I.n, z (cycWord a)).support, ∀ γ ∈ l, IsRealLine σ (c • W.J.map σ) γ :=
    fun l hl => by
      obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hl)
      exact hz _ l ha
  have h1 : ∀ f, IsSm σ (c • W.J.map σ) f → zOp I v m (fun y => f (toGAd hσ W.J hc (e y))) =
      fun y => dop (∑ a : Fin (m + 1) → Fin I.n, z (cycWord a)) f (toGAd hσ W.J hc (e y)) := fun f hf => by
    funext x
    rw [dop_sum_comb, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h := ez (cycWord a) f hf x 1
    rw [Pi.mulSingle_one, Prod.mk_one_one, mul_one] at h
    exact h
  refine ⟨_, ⟨hs, fun f hf a _ y => ?_⟩, fun N => ?_⟩
  · obtain ⟨x, rfl⟩ := ((toGAd hσ W.J hc).surjective.comp he.surj) y
    obtain ⟨b, rfl⟩ := ((toGAd hσ W.J hc).surjective.comp he.surj) a
    have e1 := congrFun (h1 _ (GlobalTheory.EisCont.CentreFinite.isSm_mul_right hcm hf (toGAd hσ W.J hc (e b)))) x
    have e2 := congrFun (h1 f hf) (x * b)
    have e3 := zOp_mul_right (f := fun y => f (toGAd hσ W.J hc (e y))) (smoothInf_transp hcm hσ hc he hf) v m x b
    simp only [map_mul] at e2 e3
    exact e1.symm.trans (e3.trans e2)
  · induction N with
    | zero => exact fun f _ => rfl
    | succ N ih =>
      intro f hf
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h1 f hf]
      exact ih _ (GlobalTheory.UAut.DopComp.dop_dop σ _ f hf _ _ hs hs).1

end GlobalTheory.ThKCentreTransp

end
