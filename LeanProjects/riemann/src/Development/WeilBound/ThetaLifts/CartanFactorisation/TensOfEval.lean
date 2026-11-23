import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem eval_basis {Y : Type} [Nonempty Y] {m : ℕ} (φ : Fin m → Y → ℂ) :
    ∃ (s : Finset Y) (e : Y → Y → ℂ), ∀ i, φ i = ∑ j ∈ s, φ i j • e j := by
  let w : Y → Fin m → ℂ := fun y i => φ i y
  have hfg : (Submodule.span ℂ (Set.range w)).FG := IsNoetherian.noetherian _
  obtain ⟨s', hs', hsp⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have hs'' : ∀ x, x ∈ s' → ∃ y, w y = x := fun x hx => hs' (Finset.mem_coe.2 hx)
  choose! p hp using hs''
  have h : ∀ y, ∃ c : (Fin m → ℂ) → ℂ, ∑ x ∈ s', c x • x = w y := fun y => by
    have : w y ∈ Submodule.span ℂ (s' : Set (Fin m → ℂ)) := hsp ▸ Submodule.subset_span ⟨y, rfl⟩
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 this
    exact ⟨c, hc⟩
  choose c hc using h
  refine ⟨s'.image p, fun j y => c y (w j), fun i => ?_⟩
  funext y
  rw [Finset.sum_image (fun a ha b hb hab => by rw [← hp a ha, ← hp b hb, hab])]
  have := congrFun (hc y) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  change w y i = _
  rw [← this]
  refine Finset.sum_congr rfl fun x hx => ?_
  change _ = w (p x) i * _
  rw [hp x hx, mul_comm]

theorem tens_of_eval {ι : Type} [Fintype ι] {Y : ι → Type} [∀ v, Nonempty (Y v)] {A : Type} [AddCommGroup A] [Module ℂ A] {m : ℕ}
    (c : Fin m → ℂ) (a : Fin m → A) (φ : Fin m → ∀ v, Y v → ℂ)
    (h : ∀ y : ∀ v, Y v, ∑ i, (c i * ∏ v, φ i v (y v)) • a i = 0) :
    ∑ i, c i • a i ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v => φ i v) = 0 := by
  choose s e he using fun v => eval_basis (fun i => φ i v)
  have h1 : ∀ i, (PiTensorProduct.tprod ℂ fun v => φ i v) =
      ∑ J ∈ Fintype.piFinset s, (∏ v, φ i v (J v)) • PiTensorProduct.tprod ℂ fun v => e v (J v) := fun i => by
    conv_lhs => rw [show (fun v => φ i v) = fun v => ∑ j ∈ s v, φ i v j • e v j from funext fun v => he v i]
    rw [MultilinearMap.map_sum_finset]
    exact Finset.sum_congr rfl fun J _ => MultilinearMap.map_smul_univ _ _ _
  simp only [h1, TensorProduct.tmul_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun J _ => ?_
  have := congrArg (· ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v => e v (J v))) (h J)
  simp only [TensorProduct.sum_tmul, TensorProduct.zero_tmul] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.tmul_smul, smul_smul, TensorProduct.smul_tmul']

theorem tensInj : TensInj := by
  intro F _ _ κ _ vac hne hstd T m c f φ hφ hsum
  choose b hb using fun v => Function.ne_iff.1 (hne v)
  let s : Finset (Pl F) := (Filter.eventually_cofinite.1 hstd).toFinset \ T
  refine tens_of_eval c f (fun i (v : T) => φ i v) fun y => ?_
  ext z
  let pt : ∀ v : Pl F, κ → Fv F v := fun v => if h : v ∈ T then y ⟨v, h⟩ else b v
  let x : κ → AF F := fun k => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z k), ∑ v ∈ T ∪ s, singleFin v (pt v k))
  have hx : ∀ u k, evFin F u (x k) = if u ∈ T ∪ s then pt u k else 0 := fun u k => by
    change evalV F u (∑ v ∈ T ∪ s, singleFin v (pt v k)) = _
    rw [map_sum]
    split_ifs with hu
    · rw [Finset.sum_eq_single u (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _) (fun h => absurd hu h),
        evalV_singleFin_self]
    · exact Finset.sum_eq_zero fun v hv => evalV_singleFin_ne (fun h : u = v => hu (h ▸ hv)) _
  have hI : (fun k => evI F (x k)) = z := funext fun k => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
  have hd : Disjoint T s := Finset.disjoint_sdiff
  have hp : ∀ i, (∏ᶠ v, φ i v fun k => evFin F v (x k)) = (∏ v : T, φ i v (y v)) * ∏ v ∈ s, vac v (b v) := fun i => by
    rw [finprod_eq_prod_of_mulSupport_subset (s := T ∪ s), Finset.prod_union hd, ← Finset.prod_coe_sort T]
    · congr 1
      · refine Finset.prod_congr rfl fun v _ => ?_
        congr 1; funext k
        rw [hx, if_pos (Finset.mem_union_left _ v.2)]
        simp only [pt, dif_pos v.2]
      · refine Finset.prod_congr rfl fun v hv => ?_
        have hT : v ∉ T := (Finset.mem_sdiff.1 hv).2
        rw [hφ i v hT]
        congr 1; funext k
        rw [hx, if_pos (Finset.mem_union_right _ hv)]
        simp only [pt, dif_neg hT]
    · intro v hv
      by_contra hn
      have hn' : v ∉ T ∪ s := fun h => hn (Finset.mem_coe.2 h)
      have hT : v ∉ T := fun h => hn' (Finset.mem_union_left _ h)
      have hs : vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
        by_contra h
        exact hn' (Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨(Set.Finite.mem_toFinset _).2 h, hT⟩))
      apply hv
      simp only [hφ i v hT, hs, hx, if_neg hn']
      rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
      rfl
  have h0 := congrFun hsum x
  have hC : ∏ v ∈ s, vac v (b v) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hb v
  simp only [Finset.sum_apply, Pi.smul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hI, hp, smul_eq_mul, Pi.zero_apply] at h0
  have e : (∑ i, (c i * ∏ v : T, φ i v (y v)) • f i) z = ∑ i, (c i * ∏ v : T, φ i v (y v)) * f i z := by
    rw [SchwartzMap.sum_apply]; rfl
  rw [e]
  apply mul_right_cancel₀ hC
  rw [Finset.sum_mul, SchwartzMap.zero_apply, zero_mul, ← h0]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem pureAct : PureAct := by
  intro F _ _ κ _ v S f φ hSB hstd
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  refine ⟨⟨fun y => ∏ᶠ v, φ v fun i => evalV F v (y i),
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩,
    fun _ => rfl⟩, fun φ₁ φ₂ a => ?_, fun φ₁ h => ?_⟩
  · rw [← hr', ← hr', ← hr']
    funext x
    simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have e : tens (evFin F v) (φ v) r = pure f φ := by rw [hr', Function.update_eq_self]
    rw [← hr', ← e]
    exact h r ⟨hr, e ▸ GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩

end PositivityTheory.ThKF

end
