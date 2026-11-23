import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem exists_section {A P : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P] (p : A →ₗ[ℂ] P)
    (S : Submodule ℂ A) : ∃ s : P →ₗ[ℂ] A, (∀ y, s y ∈ S) ∧ ∀ x ∈ S, p (s (p x)) = p x := by
  let g := p.domRestrict S
  obtain ⟨t, ht⟩ := g.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict g)
  obtain ⟨q, hq⟩ := (LinearMap.range g).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  refine ⟨S.subtype ∘ₗ t ∘ₗ q, fun y => (t (q y)).2, fun x hx => ?_⟩
  have e : q (p x) = ⟨p x, ⟨x, hx⟩, rfl⟩ := LinearMap.congr_fun hq ⟨p x, ⟨x, hx⟩, rfl⟩
  have := congrArg Subtype.val (LinearMap.congr_fun ht ⟨p x, ⟨x, hx⟩, rfl⟩)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, e]
  exact this

theorem ml_congr {ι : Type} [Fintype ι] {Y : ι → Type} [∀ v, AddCommGroup (Y v)] [∀ v, Module ℂ (Y v)] {Z : Type}
    [AddCommGroup Z] [Module ℂ Z] (l : MultilinearMap ℂ Y Z) (S K : ∀ v, Submodule ℂ (Y v))
    (h : ∀ ψ, (∀ v, ψ v ∈ S v) → (∃ v, ψ v ∈ K v) → l ψ = 0) (ψ ψ' : ∀ v, Y v) (hψ : ∀ v, ψ v ∈ S v) (hψ' : ∀ v, ψ' v ∈ S v)
    (hk : ∀ v, ψ v - ψ' v ∈ K v) : l ψ = l ψ' := by
  have e : ψ = (ψ - ψ') + ψ' := (sub_add_cancel _ _).symm
  rw [e, l.map_add_univ, Finset.sum_eq_single ∅, Finset.piecewise_empty]
  · intro s _ hs
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 hs
    refine h _ (fun u => ?_) ⟨v, by rw [Finset.piecewise_eq_of_mem _ _ _ hv]; exact hk v⟩
    by_cases hu : u ∈ s
    · rw [Finset.piecewise_eq_of_mem _ _ _ hu]; exact sub_mem (hψ u) (hψ' u)
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hu]; exact hψ' u
  · exact fun h => absurd (Finset.mem_univ _) h

theorem desc {ι : Type} [Fintype ι] {A P Z : Type} {Y Q : ι → Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Z] [Module ℂ Z] [∀ v, AddCommGroup (Y v)] [∀ v, Module ℂ (Y v)] [∀ v, AddCommGroup (Q v)]
    [∀ v, Module ℂ (Q v)] (l : A →ₗ[ℂ] MultilinearMap ℂ Y Z) (p : A →ₗ[ℂ] P) (q : ∀ v, Y v →ₗ[ℂ] Q v) (S₀ : Submodule ℂ A)
    (S : ∀ v, Submodule ℂ (Y v)) (h : ∀ f ∈ S₀, ∀ ψ, (∀ v, ψ v ∈ S v) → (p f = 0 ∨ ∃ v, q v (ψ v) = 0) → l f ψ = 0) :
    ∃ L : P ⊗[ℂ] (PiTensorProduct ℂ Q) →ₗ[ℂ] Z, ∀ f ∈ S₀, ∀ ψ, (∀ v, ψ v ∈ S v) →
      L (p f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v => q v (ψ v)) = l f ψ := by
  obtain ⟨s₀, hs₀, hs₀'⟩ := exists_section p S₀
  choose s hs hs' using fun v => exists_section (q v) (S v)
  refine ⟨TensorProduct.lift ((PiTensorProduct.lift (R := ℂ) (s := Q) (E := Z)).toLinearMap ∘ₗ
    (MultilinearMap.compLinearMapₗ s) ∘ₗ l ∘ₗ s₀), fun f hf ψ hψ => ?_⟩
  simp only [TensorProduct.lift.tmul, LinearMap.comp_apply, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMapₗ_apply, MultilinearMap.compLinearMap_apply]
  rw [ml_congr (l (s₀ (p f))) S (fun v => LinearMap.ker (q v)) (fun ψ h1 h2 => h _ (hs₀ _) ψ h1 (Or.inr h2)) _ ψ
    (fun v => hs v _) hψ (fun v => by rw [LinearMap.mem_ker, map_sub, hs' v _ (hψ v), sub_self])]
  have := h (s₀ (p f) - f) (sub_mem (hs₀ _) hf) ψ hψ (Or.inl (by rw [map_sub, hs₀' f hf, sub_self]))
  rwa [map_sub, MultilinearMap.sub_apply, sub_eq_zero] at this

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def Std (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : Prop :=
  ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

theorem Std.congr {φ w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hw : Std w) (h : ∀ᶠ v in cofinite, φ v = w v) : Std φ := by
  filter_upwards [hw, h] with v h1 h2 using h2.trans h1

theorem ev_of_off {φ w : ∀ v : Pl F, (κ → Fv F v) → ℂ} {T : Finset (Pl F)} (h : ∀ v ∉ T, φ v = w v) :
    ∀ᶠ v in cofinite, φ v = w v := by
  filter_upwards [T.eventually_cofinite_notMem] with v hv using h v hv

theorem tens_eq {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hne : ∀ v, w v ≠ 0) (hw : Std w) (T : Finset (Pl F)) {ι ι' : Type}
    [Fintype ι] [Fintype ι'] (f : ι → SInf F κ) (φ : ι → ∀ v : Pl F, (κ → Fv F v) → ℂ) (f' : ι' → SInf F κ)
    (φ' : ι' → ∀ v : Pl F, (κ → Fv F v) → ℂ) (h : ∀ i, ∀ v ∉ T, φ i v = w v) (h' : ∀ i, ∀ v ∉ T, φ' i v = w v)
    (e : ∑ i, pure (f i) (φ i) = ∑ i, pure (f' i) (φ' i)) :
    ∑ i, f i ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => φ i v) =
      ∑ i, f' i ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => φ' i v) := by
  let E := (Fintype.equivFin (ι ⊕ ι')).symm
  let c : ι ⊕ ι' → ℂ := Sum.elim (fun _ => 1) fun _ => -1
  have := tensInj F κ w hne hw T _ (fun i => c (E i)) (fun i => Sum.elim f f' (E i)) (fun i => Sum.elim φ φ' (E i))
    (fun i => by rcases E i with j | j; exacts [h j, h' j])
    (by rw [E.sum_comp (fun j => c j • pure (Sum.elim f f' j) (Sum.elim φ φ' j)), Fintype.sum_sum_type]
        simp [c, e])
  rw [E.sum_comp (fun j => c j • Sum.elim f f' j ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Sum.elim φ φ' j v)),
    Fintype.sum_sum_type] at this
  simpa [c, ← sub_eq_add_neg, sub_eq_zero] using this

theorem tens_eq_map {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hne : ∀ v, w v ≠ 0) (hw : Std w) (T : Finset (Pl F)) {ι ι' : Type}
    [Fintype ι] [Fintype ι'] (f : ι → SInf F κ) (φ : ι → ∀ v : Pl F, (κ → Fv F v) → ℂ) (f' : ι' → SInf F κ)
    (φ' : ι' → ∀ v : Pl F, (κ → Fv F v) → ℂ) (h : ∀ i, ∀ v ∉ T, φ i v = w v) (h' : ∀ i, ∀ v ∉ T, φ' i v = w v)
    (e : ∑ i, pure (f i) (φ i) = ∑ i, pure (f' i) (φ' i)) {P : Type} [AddCommGroup P] [Module ℂ P] {Q : Pl F → Type}
    [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (p : SInf F κ →ₗ[ℂ] P) (q : ∀ v, ((κ → Fv F v) → ℂ) →ₗ[ℂ] Q v) :
    ∑ i, p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => q v (φ i v)) =
      ∑ i, p (f' i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => q v (φ' i v)) := by
  have := congrArg (TensorProduct.map p (PiTensorProduct.map fun v : T => q v)) (tens_eq hne hw T f φ f' φ' h h' e)
  simpa only [map_sum, TensorProduct.map_tmul, PiTensorProduct.map_tprod] using this

def ext (w : ∀ v : Pl F, (κ → Fv F v) → ℂ) (T : Finset (Pl F)) (ψ : ∀ v : T, (κ → Fv F v) → ℂ) (v : Pl F) :
    (κ → Fv F v) → ℂ := if h : v ∈ T then ψ ⟨v, h⟩ else w v

theorem ext_of {w φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} {T : Finset (Pl F)} (h : ∀ v ∉ T, φ v = w v) :
    ext w T (fun v => φ v) = φ := funext fun v => by
  unfold ext; split_ifs with hv
  exacts [rfl, (h v hv).symm]

theorem ext_off (w : ∀ v : Pl F, (κ → Fv F v) → ℂ) (T : Finset (Pl F)) (ψ) : ∀ v ∉ T, ext w T ψ v = w v :=
  fun _ hv => dif_neg hv

theorem pure_ext {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hw : Std w) (T : Finset (Pl F)) (f : SInf F κ) (ψ) (x : κ → AF F) :
    pure f (ext w T ψ) x = f (fun i => evI F (x i)) * ((∏ v : T, ψ v fun i => evFin F v (x i)) *
      ∏ᶠ (v) (_ : v ∉ T), w v fun i => evFin F v (x i)) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  congr 1
  have hf := GlobalTheory.PureFactor.mulSupport_finite _ (hw.congr (ev_of_off (ext_off w T ψ))) x
  rw [← finprod_mem_univ, ← Set.union_compl_self (T : Set (Pl F)),
    finprod_mem_union' disjoint_compl_right (hf.inter_of_right _) (hf.inter_of_right _), finprod_mem_coe_finset,
    ← Finset.prod_coe_sort T]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => by unfold ext; rw [dif_pos v.2]
  · exact finprod_congr fun v => finprod_congr fun hv => by rw [ext_off w T ψ v hv]

theorem exists_pureML {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hw : Std w) (T : Finset (Pl F)) :
    ∃ l : SInf F κ →ₗ[ℂ] MultilinearMap ℂ (fun v : T => (κ → Fv F v) → ℂ) ((κ → AF F) → ℂ),
      ∀ f ψ, l f ψ = pure f (ext w T ψ) := by
  let m : (κ → AF F) → MultilinearMap ℂ (fun v : T => (κ → Fv F v) → ℂ) ℂ := fun x =>
    (MultilinearMap.mkPiAlgebra ℂ T ℂ).compLinearMap fun v => LinearMap.proj fun i => evFin F v (x i)
  refine ⟨{ toFun := fun f => MultilinearMap.pi fun x =>
              (f (fun i => evI F (x i)) * ∏ᶠ (v) (_ : v ∉ T), w v fun i => evFin F v (x i)) • m x
            map_add' := fun f g => ?_, map_smul' := fun a f => ?_ }, fun f ψ => ?_⟩
  · ext ψ x; simp [add_mul]
  · ext ψ x; simp [mul_assoc]
  · funext x
    rw [pure_ext hw]
    simp [m]; ring

theorem exists_factorOp (v : Pl F) (π : Module.End ℂ ((κ → Fv F v) → ℂ)) :
    ∃ O : Module.End ℂ ((κ → AF F) → ℂ), ∀ (f : SInf F κ) φ, Std φ → O (pure f φ) = pure f (Function.update φ v (π (φ v))) := by
  let sh : (κ → AF F) → (κ → Fv F v) → κ → AF F := fun x y i => x i + GlobalTheory.EmbChart.atPlace v (y i - evFin F v (x i))
  refine ⟨{ toFun := fun Φ x => π (fun y => Φ (sh x y)) fun i => evFin F v (x i)
            map_add' := fun Φ Ψ => funext fun x => ?_, map_smul' := fun a Φ => funext fun x => ?_ }, fun f φ hφ => ?_⟩
  · exact congrFun (π.map_add (fun y => Φ (sh x y)) fun y => Ψ (sh x y)) _
  · exact congrFun (π.map_smul a fun y => Φ (sh x y)) _
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hφ
  have e : pure f φ = tens (evFin F v) (φ v) r := by rw [hr', Function.update_eq_self]
  rw [← hr', e]
  funext x
  have e2 : (fun y => tens (evFin F v) (φ v) r (sh x y)) = r x • φ v := by
    funext y
    have h1 : (fun i => evFin F v (sh x y i)) = y := funext fun i => by
      simp only [sh, map_add, GlobalTheory.EmbChart.evFin_atPlace, add_sub_cancel]
    have h2 : r (sh x y) = r x := hr x (fun i => GlobalTheory.EmbChart.atPlace v (y i - evFin F v (x i))) fun u hu => by
      funext i
      show u * GlobalTheory.EmbChart.atPlace v (y i - evFin F v (x i)) = 0
      refine Prod.ext (mul_zero u.1) (af_ext fun w => ?_)
      show evalV F w (u.2 * singleFin v (y i - evFin F v (x i))) = evalV F w 0
      rw [map_mul, map_zero]
      by_cases h : w = v
      · subst h; rw [show evalV F w u.2 = 0 from hu, zero_mul]
      · rw [evalV_singleFin_ne h, mul_zero]
    simp only [tens, h1, h2, Pi.smul_apply, smul_eq_mul, mul_comm]
  change π (fun y => tens (evFin F v) (φ v) r (sh x y)) _ = _
  rw [e2, map_smul]
  simp only [tens, Pi.smul_apply, smul_eq_mul, mul_comm]

end PositivityTheory.ThKF

end
