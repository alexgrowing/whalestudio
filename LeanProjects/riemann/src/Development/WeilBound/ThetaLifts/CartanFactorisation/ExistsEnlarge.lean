import Development.WeilBound.ThetaLifts.CartanFactorisation.Factor

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG
open scoped Classical

theorem exists_enlarge {α : Type} {Q : α → Type} [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (z : ∀ v, Q v)
    {T T' : Finset α} (h : T ⊆ T') : ∃ L : PiTensorProduct ℂ (fun v : T => Q v) →ₗ[ℂ] PiTensorProduct ℂ (fun v : T' => Q v),
      ∀ y : ∀ v, Q v, (∀ v ∉ T, y v = z v) →
        L (PiTensorProduct.tprod ℂ fun v : T => y v) = PiTensorProduct.tprod ℂ fun v : T' => y v := by
  let e : (∀ v : T, Q v) → ∀ v : T', Q v := fun ψ v => if hv : v.1 ∈ T then ψ ⟨v, hv⟩ else z v
  have he : ∀ [DecidableEq T] (ψ : ∀ v : T, Q v) (i : T) (x : Q i),
      e (Function.update ψ i x) = Function.update (e ψ) ⟨i.1, h i.2⟩ x := by
    intro _ ψ i x
    funext v
    by_cases hv : v = ⟨i.1, h i.2⟩
    · subst hv; simp only [e, dif_pos i.2, Function.update_self]
    · rw [Function.update_of_ne hv]
      simp only [e]
      split_ifs with hT
      · exact Function.update_of_ne (f := ψ) (a := ⟨v.1, hT⟩) (a' := i) (fun k => hv (Subtype.ext (congrArg Subtype.val k :))) _
      · rfl
  refine ⟨PiTensorProduct.lift
    { toFun := fun ψ => PiTensorProduct.tprod ℂ (e ψ)
      map_update_add' := fun ψ i x y => by rw [he, he, he, MultilinearMap.map_update_add]
      map_update_smul' := fun ψ i c x => by rw [he, he, MultilinearMap.map_update_smul] }, fun y hy => ?_⟩
  rw [PiTensorProduct.lift.tprod]
  change PiTensorProduct.tprod ℂ (e fun v => y v) = _
  congr 1
  funext v
  simp only [e]
  split_ifs with hv
  exacts [rfl, (hy v hv).symm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem kill_aug (hI : ILeft) {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
    (hp : IsPair B M χX χW om r s r' s') (J : Fn F n d →ₗ[ℂ] (UA σ W.J → ℂ)) (hJ : ∀ Φ ∈ schA F _, J Φ = M.I om Φ)
    (v : Pl F) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (h1 : ∀ v, φ v ∈ SB _) (h2 : Std φ)
    (z : (Fin n × Fin d → Fv F v) → ℂ) (hz : z ∈ augAt om v) : J (pure f (Function.update φ v z)) = 0 := by
  obtain ⟨ρ, hρ, hρ'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ h2
  let t : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Fn F n d :=
    { toFun := fun z => tens (evFin F v) z ρ
      map_add' := fun x y => funext fun _ => add_mul _ _ _
      map_smul' := fun a x => funext fun _ => mul_assoc _ _ _ }
  have mem : ∀ y ∈ SB _, t y ∈ schA F _ := fun y hy => by
    change tens (evFin F v) y ρ ∈ _
    rw [hρ']
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun u => ?_) (GlobalTheory.PureFactor.update_eventually φ v y h2)
    by_cases hu : u = v
    · subst hu; rw [Function.update_self]; exact hy
    · rw [Function.update_of_ne hu]; exact h1 u
  rw [← hρ']
  change (J ∘ₗ t) z = 0
  refine (Submodule.span_le.2 ?_ : augAt om v ≤ LinearMap.ker (J ∘ₗ t)) hz
  rintro _ ⟨g, -, y, hy, y₁, hy₁, ha, rfl⟩
  have e : om (g, 1) (t y) = t y₁ := ha ρ ⟨hρ, mem y hy⟩
  change J (t (y₁ - y)) = 0
  rw [map_sub, map_sub, hJ _ (mem y₁ hy₁), hJ _ (mem y hy), ← e, hI F E σ B n d X W M χX χW om r s r' s' hp _ (mem y hy), sub_self]

theorem anAll_of (hW : WeilConv) (hC : KCoinv) (hI : ILeft) : AnAll := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm hq c hc Φ Φ' ⟨T, hT, m, m', f, φ, f', φ', h1, h2, e1, e2, e⟩ h
  have g := hm.triple.geo.hM
  have g' := hm.triple.geo.hM'
  have hp := pairV' hm.triple
  obtain ⟨J, hJ⟩ := exists_Ilin hm.triple.weil' (schA F _) le_rfl fun Φ hΦ =>
    ((hW F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hp (Or.inr (by rw [hq]; simp))).1 Φ hΦ).1
  obtain ⟨-, c2, c3, -⟩ := (hC F E σ B a a' G X om om' R Rf hm).1 B.v₁ hm.triple.chars.good
  choose y hy hy' using fun j => c3 B.τ₁ (Rf.p' B.v₁ (φ' j B.v₁))
  let φ₀ : Fin m' → ∀ v : Pl F, _ := fun j => Function.update (φ' j) B.v₁ (y j)
  have sb : ∀ j v, φ₀ j v ∈ SB _ := fun j v => by
    by_cases hv : v = B.v₁
    · subst hv; simp only [φ₀, Function.update_self]; exact (hy j).1
    · simp only [φ₀, Function.update_of_ne hv]; exact (h2 j).2.1 v
  have off : ∀ j, ∀ v ∉ insert B.v₁ T, φ₀ j v = G.M'.vac v := fun j v hv => by
    rw [Finset.mem_insert, not_or] at hv
    simp only [φ₀, Function.update_of_ne hv.1]; exact (h2 j).2.2 v hv.2
  have pe : ∀ j v, Rf.p' v (φ₀ j v) = Rf.p' v (φ' j v) := fun j v => by
    by_cases hv : v = B.v₁
    · subst hv; simp only [φ₀, Function.update_self]; exact hy' j
    · simp only [φ₀, Function.update_of_ne hv]
  have so : ∑ j, pure (f' j) (φ₀ j) ∈ G.M'.So B.ψ B.τ₁ := sum_mem fun j _ =>
    pure_mem_So g' _ _ _ (fun v _ => sb j v) (ev_of_off (off j))
      (by simp only [φ₀, Function.update_self]; exact Submodule.subset_span (hy j))
  obtain ⟨L, hL⟩ := exists_enlarge (fun v => Rf.p v (G.M.vac v)) (Finset.subset_insert B.v₁ T)
  have pm : PolMatch B G X R Rf Φ (∑ j, pure (f' j) (φ₀ j)) := by
    refine ⟨insert B.v₁ T, hT.trans (Finset.subset_insert _ _), m, m', f, φ, f', φ₀,
      fun i => ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v fun k => hv (Finset.mem_insert_of_mem k)⟩,
      fun j => ⟨(h2 j).1, sb j, off j⟩, e1, rfl, ?_⟩
    have := congrArg (TensorProduct.map LinearMap.id L) e
    simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply] at this
    simp only [pe]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (this.trans (Finset.sum_congr rfl fun j _ => ?_))
    · rw [hL (fun v => Rf.p v (φ i v)) fun v hv => by rw [(h1 i).2.2 v hv]]
    · rw [hL (fun v => Rf.p' v (φ' j v)) fun v hv => by
        rw [(h2 j).2.2 v hv, (hm.fin.sph v fun k => hv (hT k)).1]]
  rw [hc Φ _ so pm h]
  congr 1
  have st : ∀ j, Std (φ' j) := fun j => (good_std g').congr (ev_of_off (h2 j).2.2)
  have m1 : Φ' ∈ schA F _ := e2 ▸ sum_mem fun j _ => GlobalTheory.TensUniq.pure_mem_schA _ _ (h2 j).2.1 (st j)
  rw [← hJ _ (so_le g' _ so), ← hJ _ m1, e2, map_sum, map_sum]
  refine congrFun (Finset.sum_congr rfl fun j _ => ?_) h
  have k := kill_aug hI hp J hJ B.v₁ (f' j) (φ' j) (h2 j).2.1 (st j) (y j - φ' j B.v₁)
    ((c2 _ (sub_mem (hy j).1 ((h2 j).2.1 _))).1 (by rw [map_sub, hy', sub_self]))
  have a2 := (pureAct F _ B.v₁ id (f' j) (φ' j) (h2 j).2.1 (st j)).2.1 (φ' j B.v₁) (y j - φ' j B.v₁) 1
  rw [one_smul, one_smul, add_sub_cancel, Function.update_eq_self] at a2
  have k' : J (pure (f' j) (φ₀ j)) = J (pure (f' j) (φ' j)) := by
    have := congrArg J a2
    rw [map_add] at this
    exact this.trans (by rw [show J _ = 0 from k, add_zero])
  exact k'

end PositivityTheory.ThKF

end
