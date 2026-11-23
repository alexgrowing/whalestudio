import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionFockDegreeFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingMulOfAdaptedPlaneStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.WtDisj

open Module

def qProd {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (B : ι → End ℂ V) (s : List (ι × ℂ)) : End ℂ V :=
  (s.map fun q => B q.1 - algebraMap ℂ (End ℂ V) q.2).prod

theorem qProd_commute {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (B : ι → End ℂ V)
    (hc : ∀ i j, Commute (B i) (B j)) (s t : List (ι × ℂ)) : Commute (qProd B s) (qProd B t) := by
  unfold qProd
  refine Commute.list_prod_left _ _ fun x hx => Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨q', -, rfl⟩ := List.mem_map.1 hy
  exact Commute.sub_left ((hc q.1 q'.1).sub_right (Algebra.commute_algebraMap_right q'.2 _))
    (Algebra.commute_algebraMap_left q.2 _)

theorem qProd_eigen {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (B : ι → End ℂ V) (lam : ι → ℂ)
    (v : V) (hv : ∀ i, B i v = lam i • v) (s : List (ι × ℂ)) :
    qProd B s v = (s.map fun q => lam q.1 - q.2).prod • v := by
  induction s with
  | nil => simp [qProd]
  | cons q s ih =>
    simp only [qProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, hv, Module.algebraMap_end_apply, ← sub_smul,
      smul_smul, mul_comm]

theorem prod_ne_zero_of {ι : Type} (lam : ι → ℂ) (s : List (ι × ℂ)) (hs : ∀ q ∈ s, q.2 ≠ lam q.1) :
    (s.map fun q => lam q.1 - q.2).prod ≠ 0 := by
  refine List.prod_ne_zero fun h => ?_
  obtain ⟨q, hq, e⟩ := List.mem_map.1 h
  exact hs q hq (sub_eq_zero.1 e).symm

theorem exists_qProd_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (B : ι → End ℂ V) (lam : ι → ℂ)
    (hc : ∀ i j, Commute (B i) (B j)) {v : V}
    (hv : v ∈ Submodule.span ℂ {x | ∃ i, ∃ c : ℂ, c ≠ lam i ∧ B i x = c • x}) :
    ∃ s : List (ι × ℂ), (∀ q ∈ s, q.2 ≠ lam q.1) ∧ qProd B s v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, c, hc', hx⟩ := hx
    refine ⟨[(i, c)], by simpa using hc', ?_⟩
    simp [qProd, hx]
  | zero => exact ⟨[], by simp, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s ++ t, fun q hq => ?_, ?_⟩
    · rcases List.mem_append.1 hq with h | h
      exacts [hs q h, ht q h]
    · have e : qProd B (s ++ t) = qProd B s * qProd B t := by
        simp [qProd, List.prod_append]
      rw [map_add, e, Module.End.mul_apply _ _ y, hty, map_zero, add_zero, (qProd_commute B hc s t).eq,
        Module.End.mul_apply, hsx, map_zero]
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    exact ⟨s, hs, by rw [map_smul, hsx, smul_zero]⟩

theorem disjoint_span_span {P : Type} [AddCommGroup P] [Module ℂ P] (V : Submodule ℂ P)
    {ι : Type} (A : ι → End ℂ P) (lam : ι → ℂ) (hmap : ∀ i, ∀ x ∈ V, A i x ∈ V)
    (hcomm : ∀ i j, ∀ x ∈ V, A i (A j x) = A j (A i x)) :
    Disjoint (Submodule.span ℂ {x | x ∈ V ∧ ∀ i, A i x = lam i • x})
      (Submodule.span ℂ {x | x ∈ V ∧ ∃ i, ∃ c : ℂ, c ≠ lam i ∧ A i x = c • x}) := by
  let B : ι → End ℂ V := fun i => (A i).restrict (hmap i)
  have hB : ∀ i (y : V), ((B i y : V) : P) = A i y := fun i y => rfl
  have hc : ∀ i j, Commute (B i) (B j) := fun i j =>
    LinearMap.ext fun y => Subtype.ext (hcomm i j y y.2)
  have hoff : Submodule.span ℂ {x | x ∈ V ∧ ∃ i, ∃ c : ℂ, c ≠ lam i ∧ A i x = c • x} =
      (Submodule.span ℂ {y : V | ∃ i, ∃ c : ℂ, c ≠ lam i ∧ B i y = c • y}).map V.subtype := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨hx, i, c, hc', he⟩
      exact ⟨⟨x, hx⟩, ⟨i, c, hc', Subtype.ext he⟩, rfl⟩
    · rintro ⟨y, ⟨i, c, hc', he⟩, rfl⟩
      exact ⟨y.2, i, c, hc', congrArg Subtype.val he⟩
  rw [Submodule.disjoint_def, hoff]
  rintro _ hz ⟨v, hv, rfl⟩
  have htw0 : ∀ z ∈ Submodule.span ℂ {x | x ∈ V ∧ ∀ i, A i x = lam i • x}, ∀ i, A i z = lam i • z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hx.2
    | zero => intro i; simp
    | add x y _ _ hx hy => intro i; rw [map_add, hx, hy, smul_add]
    | smul a x _ hx => intro i; rw [map_smul, hx, smul_comm]
  have hv' : ∀ i, B i v = lam i • v := fun i => Subtype.ext (htw0 _ hz i)
  obtain ⟨s, hs, hsv⟩ := exists_qProd_eq_zero B lam hc hv
  rw [qProd_eigen B lam v hv' s] at hsv
  have := (smul_eq_zero.1 hsv).resolve_left (prod_ne_zero_of lam s hs)
  simp [this]

end GlobalTheory.WtDisj

namespace GlobalTheory.WtDisj

section Tens

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem tens_inj {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0) (hR : ∀ f : SInf F κ, Rest (evI F) (⇑f) R)
    {f g : SInf F κ} (h : tens (evI F) (⇑f) R = tens (evI F) (⇑g) R) : f = g := by
  refine DFunLike.ext f g fun t => ?_
  let u : κ → AF F := fun i =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)
  have hev : ∀ i, evI F (u i) = t i := fun i =>
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i)) = t i from
      RingEquiv.apply_symm_apply _ _
  have hat : At (evI F) u := by
    intro u' hu'
    have h0 : u'.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu')
    funext i
    refine Prod.ext ?_ ?_
    · show u'.1 * (u i).1 = 0
      rw [h0, zero_mul]
    · show u'.2 * (u i).2 = 0
      simp [u]
  have h1 := congrFun h u
  have hR' : R u = R 0 := by
    have := (hR f).1 0 u hat
    rwa [zero_add] at this
  have hev' : (fun i => evI F (u i)) = t := funext hev
  simp only [tens, hev', hR'] at h1
  exact mul_right_cancel₀ hR0 h1

end Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem acts_comm' {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) {k k' : UA σ W.J} (hkk : k * k' = k' * k)
    {f f₁ f₂ g₁ g₂ : SInf F (Fin n × Fin d)} (h1 : Acts (evI F) (om (1, k')) (⇑f) (⇑f₁))
    (h2 : Acts (evI F) (om (1, k)) (⇑f₁) (⇑f₂)) (h3 : Acts (evI F) (om (1, k)) (⇑f) (⇑g₁))
    (h4 : Acts (evI F) (om (1, k')) (⇑g₁) (⇑g₂)) : f₂ = g₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  refine tens_inj hR0 hR ?_
  have e1 : tens (evI F) (⇑f₂) R = om (1, k * k') (tens (evI F) (⇑f) R) := by
    have : ((1 : UA σ Y.J), k * k') = (1, k) * (1, k') := by simp
    rw [this, map_mul, Module.End.mul_apply, h1 R (hR f), h2 R (hR f₁)]
  have e2 : tens (evI F) (⇑g₂) R = om (1, k' * k) (tens (evI F) (⇑f) R) := by
    have : ((1 : UA σ Y.J), k' * k) = (1, k') * (1, k) := by simp
    rw [this, map_mul, Module.End.mul_apply, h3 R (hR f), h4 R (hR g₁)]
  rw [e1, e2, hkk]

end GlobalTheory.WtDisj

namespace GlobalTheory.WtDisj

set_option maxHeartbeats 1000000 in

theorem twPart_disjoint_offPart_beta : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      Disjoint (twPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p)) (offPart B G.M om R.p G₁.W H' X.β ((a : ℝ) / 2) (lowPartInf B G.M R.p)) := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hm hm₁
  classical
  have hB := hm.triple.base
  have hg := hm.triple.geo

  have hop : ∀ k ∈ KInf σ G.W B.emb, ∃ A : SInf F (Fin a × Fin (a + (b + 2))) →ₗ[ℂ] SInf F (Fin a × Fin (a + (b + 2))),
      ∀ f : SInf F (Fin a × Fin (a + (b + 2))), Acts (evI F) (om (1, k)) (⇑f) (⇑(A f)) :=
    fun k hk => GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V G.W G.M om _ _ hB hg.hM hm.triple.weil k hk
  have hop' : ∀ k ∈ KInf σ G.W B.emb, ∃ A : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (a + (b + 2))),
      ∀ f : SInf F (Fin (b + 2) × Fin (a + (b + 2))), Acts (evI F) (om' (1, k)) (⇑f) (⇑(A f)) :=
    fun k hk => GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G.V' G.W G.M' om' _ _ hB hg.hM' hm.triple.weil' k hk

  have hdesc : ∀ k ∈ KInf σ G.W B.emb, ∃ T : R.Pi →ₗ[ℂ] R.Pi, ∀ f ∈ G.M.Pol B.ψ B.emb,
      ∀ f₁ : SInf F (Fin a × Fin (a + (b + 2))), Acts (evI F) (om (1, k)) (⇑f) (⇑f₁) → R.p f₁ = T (R.p f) := by
    intro k hk
    obtain ⟨A, hA⟩ := hop k hk
    obtain ⟨A', hA'⟩ := hop' k hk
    have onto : ∀ x, ∃ f ∈ G.M.Pol B.ψ B.emb, R.p f = x := by
      intro x
      have : x ∈ (G.M.Pol B.ψ B.emb).map R.p := by rw [hm.real.quot.onto]; trivial
      obtain ⟨f, hf, e⟩ := this
      exact ⟨f, hf, e⟩
    have onto' : ∀ x, ∃ f ∈ G.M'.Pol B.ψ B.emb, R.p' f = x := by
      intro x
      have : x ∈ (G.M'.Pol B.ψ B.emb).map R.p' := by rw [hm.real.quot'.onto]; trivial
      obtain ⟨f, hf, e⟩ := this
      exact ⟨f, hf, e⟩
    have key : ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) (⇑f) (⇑f₁) →
        ∀ f' ∈ G.M'.Pol B.ψ B.emb, R.p f = R.p' f' → R.p f₁ = R.p' (A' f') :=
      fun f hf f₁ h1 f' hf' he => hm.real.cpt k hk f hf f' hf' f₁ (A' f') h1 (hA' f') he
    have wd : ∀ f' ∈ G.M'.Pol B.ψ B.emb, ∀ g' ∈ G.M'.Pol B.ψ B.emb, R.p' f' = R.p' g' →
        R.p' (A' f') = R.p' (A' g') := by
      intro f' hf' g' hg' he
      obtain ⟨f, hf, hfx⟩ := onto (R.p' f')
      rw [← key f hf (A f) (hA f) f' hf' hfx, key f hf (A f) (hA f) g' hg' (hfx.trans he)]
    choose g hgP hgx using onto'
    refine ⟨{ toFun := fun x => R.p' (A' (g x)), map_add' := ?_, map_smul' := ?_ }, ?_⟩
    · intro x y
      rw [← map_add, ← map_add]
      exact wd _ (hgP _) _ (add_mem (hgP x) (hgP y)) (by rw [hgx, map_add, hgx, hgx])
    · intro c x
      rw [RingHom.id_apply, ← map_smul, ← map_smul]
      exact wd _ (hgP _) _ (Submodule.smul_mem _ c (hgP x)) (by rw [hgx, map_smul, hgx])
    · intro f hf f₁ h1
      exact key f hf f₁ h1 _ (hgP _) (hgx _).symm
  choose! A hA using hop
  choose! T hT using hdesc
  set j₀ := lowDegInf B G.M R.p
  have hstab := GlobalTheory.T.weil_action_fock_degree_formula F E σ B _ _ G.V G.W G.M om _ _ _ _ _ _ hB hg.hV hg.hW hg.hM hm.triple.weil
  have hcommG := GlobalTheory.T.levi_embedding_mul_of_adapted_plane F E σ B _ _ G.W G₁.W H' a (a + b + 1) _ _ _ _ hB hg.hW hm₁.triple.geo.hW hC.hH'
  have hPol : ∀ f ∈ fockDeg G.M B.ψ B.emb j₀, f ∈ G.M.Pol B.ψ B.emb := fun f hf => fockDeg_le_pol _ _ _ _ hf
  let ι := {q : UA σ G.W.J × (AE F E)ˣ // q.1 ∈ KInf σ G.W B.emb ∧ IsLevi H' q.2 (1 : UA σ G₁.W.J) q.1}
  let lam : ι → ℂ := fun i => (X.β i.1.2 : ℂ) * (((absE F E i.1.2 : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)
  have hTp : ∀ i : ι, ∀ f ∈ fockDeg G.M B.ψ B.emb j₀, T i.1.1 (R.p f) = R.p (A i.1.1 f) := fun i f hf =>
    (hT i.1.1 i.2.1 f (hPol f hf) _ (hA i.1.1 i.2.1 f)).symm
  have main := disjoint_span_span (lowPartInf B G.M R.p) (fun i : ι => (T i.1.1 : Module.End ℂ R.Pi)) lam ?_ ?_
  · refine main.mono (Submodule.span_mono ?_) (Submodule.span_mono ?_)
    · rintro x ⟨hx, hxe⟩
      refine ⟨hx, fun i => ?_⟩
      obtain ⟨f, hf, rfl⟩ := hx
      show T i.1.1 (R.p f) = lam i • R.p f
      exact (hT i.1.1 i.2.1 f (hPol f hf) _ (hA i.1.1 i.2.1 f)).symm.trans
        (hxe i.1.1 i.2.1 i.1.2 i.2.2 f (hPol f hf) _ (hA i.1.1 i.2.1 f) rfl)
    · rintro x ⟨hx, k, hk, t, hL, c, hc, hxe⟩
      refine ⟨hx, ⟨(k, t), hk, hL⟩, c, hc, ?_⟩
      obtain ⟨f, hf, rfl⟩ := hx
      show T k (R.p f) = c • R.p f
      exact (hT k hk f (hPol f hf) _ (hA k hk f)).symm.trans (hxe f (hPol f hf) _ (hA k hk f) rfl)
  · rintro i x ⟨f, hf, rfl⟩
    show T i.1.1 (R.p f) ∈ _
    rw [hTp i f hf]
    exact ⟨_, hstab i.1.1 i.2.1 j₀ f hf _ (hA i.1.1 i.2.1 f), rfl⟩
  · rintro i i' x ⟨f, hf, rfl⟩
    have hf1 := hstab i'.1.1 i'.2.1 j₀ f hf _ (hA i'.1.1 i'.2.1 f)
    have hf2 := hstab i.1.1 i.2.1 j₀ f hf _ (hA i.1.1 i.2.1 f)
    show T i.1.1 (T i'.1.1 (R.p f)) = T i'.1.1 (T i.1.1 (R.p f))
    rw [hTp i' f hf, hTp i _ hf1, hTp i f hf, hTp i' _ hf2]
    congr 1
    exact acts_comm' om (hcommG _ _ _ _ i.2.2 i'.2.2) (hA i'.1.1 i'.2.1 f) (hA i.1.1 i.2.1 _)
      (hA i.1.1 i.2.1 f) (hA i'.1.1 i'.2.1 _)

end GlobalTheory.WtDisj
