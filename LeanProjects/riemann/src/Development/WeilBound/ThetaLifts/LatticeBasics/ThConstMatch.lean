import Development.WeilBound.ThetaLifts.LatticeBasics.ThConstInv
import Development.WeilBound.ThetaLifts.LatticeBasics.NonZero

noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_ext {ι : Type} (M : ι → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module ℂ (M v)] {S T : Finset ι} (h : S ⊆ T)
    (z : ∀ v, M v) : ∃ e : (PiTensorProduct ℂ fun v : S => M v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T => M v,
      ∀ u : ∀ v, M v, (∀ v ∉ S, u v = z v) → e (PiTensorProduct.tprod ℂ fun v : S => u v) = PiTensorProduct.tprod ℂ fun v : T => u v := by
  let c : (∀ v : S, M v) → ∀ v : T, M v := fun x v => if hv : (v : ι) ∈ S then x ⟨v, hv⟩ else z v
  have key : ∀ [DecidableEq S] x (i : S) w, c (Function.update x i w) = Function.update (c x) ⟨i, h i.2⟩ w := fun x i w => by
    funext v
    by_cases hvi : v = ⟨i, h i.2⟩
    · subst hvi
      simp [c]
    · rw [Function.update_of_ne hvi]
      by_cases hv : (v : ι) ∈ S
      · simp only [c, dif_pos hv]
        exact Function.update_of_ne (fun e => hvi (Subtype.ext (by rw [← e]))) _ _
      · simp only [c, dif_neg hv]
  refine ⟨PiTensorProduct.lift
    { toFun := fun x => PiTensorProduct.tprod ℂ (c x)
      map_update_add' := fun x i y y' => by simp only [key]; exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
      map_update_smul' := fun x i a y => by simp only [key]; exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _ }, fun u hu => ?_⟩
  rw [PiTensorProduct.lift.tprod]
  refine congrArg (PiTensorProduct.tprod ℂ) (funext fun v => ?_)
  by_cases hv : (v : ι) ∈ S
  · simp only [c, dif_pos hv]
  · simp only [c, dif_neg hv, hu v hv]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d a a' : ℕ}
  {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

variable (B G R Rf) in

def On (T : Finset (Pl F)) (Φ : Fn F a (a + a')) (Φ' : Fn F a' (a + a')) : Prop :=
  ∃ (m m' : ℕ) (f : Fin m → SInf F _) (φ : Fin m → ∀ v : Pl F, (_ → Fv F v) → ℂ)
    (f' : Fin m' → SInf F _) (φ' : Fin m' → ∀ v : Pl F, (_ → Fv F v) → ℂ),
    (∀ i, f i ∈ G.M.Pol B.ψ B.emb ∧ (∀ v, φ i v ∈ SB _) ∧ ∀ v ∉ T, φ i v = G.M.vac v) ∧
    (∀ j, f' j ∈ G.M'.Pol B.ψ B.emb ∧ (∀ v, φ' j v ∈ SB _) ∧ ∀ v ∉ T, φ' j v = G.M'.vac v) ∧
    Φ = ∑ i, pure (f i) (φ i) ∧ Φ' = ∑ j, pure (f' j) (φ' j) ∧
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v))

theorem On.mono (hm : IsMatched B G X om om' R Rf) {S T : Finset (Pl F)} (h0 : X.T ⊆ S) (h : S ⊆ T) {Φ Φ'}
    (H : On B G R Rf S Φ Φ') : On B G R Rf T Φ Φ' := by
  obtain ⟨m, m', f, φ, f', φ', h1, h2, e1, e2, e3⟩ := H
  obtain ⟨e, he⟩ := exists_ext Rf.Pi h fun v => Rf.p v (G.M.vac v)
  refine ⟨m, m', f, φ, f', φ', fun i => ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v fun k => hv (h k)⟩,
    fun i => ⟨(h2 i).1, (h2 i).2.1, fun v hv => (h2 i).2.2 v fun k => hv (h k)⟩, e1, e2, ?_⟩
  have := congrArg (e.lTensor R.Pi) e3
  simp only [map_sum, LinearMap.lTensor_tmul] at this
  refine (Finset.sum_congr rfl fun i _ => ?_).trans (this.trans (Finset.sum_congr rfl fun i _ => ?_))
  · rw [he (fun v => Rf.p v (φ i v)) fun v hv => by rw [(h1 i).2.2 v hv]]
  · rw [he (fun v => Rf.p' v (φ' i v)) fun v hv => by rw [(h2 i).2.2 v hv, (hm.fin.sph v fun k => hv (h0 k)).1]]

theorem pm_zero : PolMatch B G X R Rf 0 0 :=
  ⟨_, le_rfl, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp, by simp, by simp⟩

theorem pm_add (hm : IsMatched B G X om om' R Rf) {Φ Φ' Ψ Ψ'} (c : ℂ) (h1 : PolMatch B G X R Rf Φ Φ')
    (h2 : PolMatch B G X R Rf Ψ Ψ') : PolMatch B G X R Rf (c • Φ + Ψ) (c • Φ' + Ψ') := by
  obtain ⟨T₁, hT₁, H₁⟩ := h1
  obtain ⟨T₂, hT₂, H₂⟩ := h2
  obtain ⟨m, m', f, φ, f', φ', hf, hf', rfl, rfl, e1⟩ := On.mono hm hT₁ (Finset.subset_union_left (s₂ := T₂)) H₁
  obtain ⟨k, k', g, ψ, g', ψ', hg, hg', rfl, rfl, e2⟩ := On.mono hm hT₂ (Finset.subset_union_right (s₁ := T₁)) H₂
  refine ⟨T₁ ∪ T₂, hT₁.trans Finset.subset_union_left, m + k, m' + k', Fin.append (c • f) g, Fin.append φ ψ, Fin.append (c • f') g',
    Fin.append φ' ψ', fun i => ?_, fun i => ?_, funext fun x => ?_, funext fun x => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply]
      exact ⟨Submodule.smul_mem _ _ (hf i).1, (hf i).2⟩
    · simp only [Fin.append_right]
      exact hg i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.smul_apply]
      exact ⟨Submodule.smul_mem _ _ (hf' i).1, (hf' i).2⟩
    · simp only [Fin.append_right]
      exact hg' i
  · simp [Fin.sum_univ_add, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum, mul_assoc]
  · simp [Fin.sum_univ_add, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum, mul_assoc]
  · rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, map_smul, ← TensorProduct.smul_tmul']
    rw [← Finset.smul_sum, ← Finset.smul_sum, e1, e2]

theorem loc_op (hS : SplitModel) {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {o : Rep σ Y W} {χ χ' : Chr F E} {r s r' s' : ℕ}
    (p : IsPair B M χ χ' o r s r' s') {v : Pl F} (t : E →ₐ[F] Fv F v) {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) :
    ∃ O : Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ), (∀ φ ∈ SB _, O φ ∈ SB _ ∧ Acts (evFin F v) (o (1, h)) φ (O φ)) ∧
      ∀ f (φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ), (∀ u, φ u ∈ SB _) → (∀ᶠ u in cofinite, φ u = M.vac u) →
        o (1, h) (pure f φ) = pure f (Function.update φ v (O (φ v))) := by
  obtain ⟨-, ι, b, -, r1⟩ := hS F E σ B n d Y W M _ _ o _ _ _ _ p v t
  obtain ⟨j, -, j2⟩ := exists_inv' b
  let h₀ := Matrix.GeneralLinearGroup.map (piW t) h.1
  have k := fun φ hφ => acts_of_reads (r1 h hh h₀ rfl) j2 (φ := φ) hφ
  refine ⟨j ∘ₗ GlobalTheory.SplitFlip.repB (chrW χ' t) (chrW χ t) (1, h₀) ∘ₗ ι, k, fun f φ p1 p2 => ?_⟩
  obtain ⟨T, t1, -, t3⟩ := intersection_update_fsHerm_neg_one v f p1 ((p2.and p.good.std).mono fun _ h => h.1.trans h.2)
  have := t3 _ _ (p1 v) _ (k _ (p1 v)).2
  rwa [t1, t1, Function.update_eq_self] at this

theorem pm_fin (hS : SplitModel) (hm : IsMatched B G X om om' R Rf) {v : Pl F} (t : E →ₐ[F] Fv F v) {h : UA σ G.W.J}
    (hh : h ∈ UAt σ G.W (evFin F v)) {Φ Φ'} (H : PolMatch B G X R Rf Φ Φ') :
    PolMatch B G X R Rf (om (1, h) Φ) (om' (1, h) Φ') := by
  obtain ⟨T, hT, H⟩ := H
  obtain ⟨m, m', f, φ, f', φ', h1, h2, rfl, rfl, e⟩ := On.mono hm hT (Finset.subset_insert v T) H
  obtain ⟨O, o1, o2⟩ := loc_op hS (pairV hm.triple) t hh
  obtain ⟨O', o1', o2'⟩ := loc_op hS (pairV' hm.triple) t hh
  obtain ⟨s, hs⟩ := ((Rf.p v).domRestrict (SB _)).exists_rightInverse_of_surjective
    ((LinearMap.range_domRestrict _ _).trans (hm.fin.onto v))
  let A : Module.End ℂ (Rf.Pi v) := Rf.p v ∘ₗ O ∘ₗ (SB _).subtype ∘ₗ s
  have q : ∀ x ∈ SB _, ∀ x' ∈ SB _, Rf.p v x = Rf.p' v x' → Rf.p v (O x) = Rf.p' v (O' x') := fun x hx x' hx' =>
    hm.fin.equiv v h hh x hx x' hx' _ (o1 x hx).1 _ (o1' x' hx').1 (o1 x hx).2 (o1' x' hx').2
  have A' : ∀ x' ∈ SB _, A (Rf.p' v x') = Rf.p' v (O' x') := fun x' hx' =>
    q _ (s _).2 x' hx' (LinearMap.congr_fun hs _)
  have A1 : ∀ x ∈ SB _, A (Rf.p v x) = Rf.p v (O x) := fun x hx => by
    obtain ⟨x', hx', k⟩ : Rf.p v x ∈ (SB _).map (Rf.p' v) := hm.fin.onto' v ▸ Submodule.mem_top
    rw [q x hx x' hx' k.symm, ← k, A' x' hx']
  have up : ∀ {P : ∀ u : Pl F, Type} (Q : ∀ u, P u → Prop) (x : ∀ u, P u) (y : P v), Q v y → (∀ u ≠ v, Q u (x u)) →
      ∀ u, Q u (Function.update x v y u) := fun Q x y a b u => by
    by_cases hu : u = v
    · subst hu; rwa [Function.update_self]
    · rw [Function.update_of_ne hu]; exact b u hu
  have ne : ∀ u ∉ insert v T, u ≠ v := fun u hu k => hu (k ▸ Finset.mem_insert_self _ _)
  refine ⟨_, hT.trans (Finset.subset_insert v T), m, m', f, fun i => Function.update (φ i) v (O (φ i v)), f',
    fun i => Function.update (φ' i) v (O' (φ' i v)), fun i => ⟨(h1 i).1,
      up (fun u x => x ∈ SB _) _ _ (o1 _ ((h1 i).2.1 v)).1 fun u _ => (h1 i).2.1 u,
      fun u hu => (Function.update_of_ne (ne u hu) _ _).trans ((h1 i).2.2 u hu)⟩, fun i => ⟨(h2 i).1,
      up (fun u x => x ∈ SB _) _ _ (o1' _ ((h2 i).2.1 v)).1 fun u _ => (h2 i).2.1 u,
      fun u hu => (Function.update_of_ne (ne u hu) _ _).trans ((h2 i).2.2 u hu)⟩, ?_, ?_, ?_⟩
  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => o2 _ _ (h1 i).2.1 ((insert v T).eventually_cofinite_notMem.mono (h1 i).2.2)
  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => o2' _ _ (h2 i).2.1 ((insert v T).eventually_cofinite_notMem.mono (h2 i).2.2)
  let D : ∀ u, Module.End ℂ (Rf.Pi u) := Function.update (fun _ => LinearMap.id) v A
  have := congrArg ((PiTensorProduct.map fun u : (insert v T : Finset _) => D u).lTensor R.Pi) e
  simp only [map_sum, LinearMap.lTensor_tmul, PiTensorProduct.map_tprod] at this
  refine (Finset.sum_congr rfl fun i _ => ?_).trans (this.trans (Finset.sum_congr rfl fun i _ => ?_)) <;> congr 2 <;> funext ⟨u, _⟩ <;>
    by_cases hu : u = v
  · subst hu; simp only [D, Function.update_self, A1 _ ((h1 i).2.1 _)]
  · simp only [D, Function.update_of_ne hu, LinearMap.id_apply]
  · subst hu; simp only [D, Function.update_self, A' _ ((h2 i).2.1 _)]
  · simp only [D, Function.update_of_ne hu, LinearMap.id_apply]

end GlobalTheory.ThK.Dbl.TC

end
