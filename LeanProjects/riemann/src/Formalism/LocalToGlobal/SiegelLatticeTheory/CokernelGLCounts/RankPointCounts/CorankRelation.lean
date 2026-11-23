import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.DensInertDisplayHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PairCorankPositivity.FinrankOrthAddLe

noncomputable section

open scoped Classical
open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Matrix

namespace Formalism.L2.SG.NGCut.CorankRelation

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem span_pair_orth_eq_zero {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0)
    (x : S.V) (hx : x ∈ Submodule.span E (Set.range (Sum.elim F.fvec F'.fvec)))
    (ho : ∀ i, S.hT (Sum.elim F.fvec F'.fvec i) x = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
  have hdet : (Formalism.L2.SG.GramJoint.gramFF F F').det ≠ 0 := by
    rw [Formalism.L2.SG.Closed.GramDetFlag_holds E S r T T' F F']
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hG
  have hc : Formalism.L2.SG.GramJoint.gramFF F F' *ᵥ c = 0 := by
    funext i
    have h := ho i
    rw [map_sum] at h
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Formalism.L2.SG.GramJoint.gramFF, Formalism.L2.SG.GramJoint.pairVec, brS, map_smul, smul_eq_mul]
    ring
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hc
  simp [h0]

theorem Xsp_le_span {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') :
    F.X ≤ Submodule.span E (Set.range (Sum.elim F.fvec F'.fvec)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨Sum.inl (Fin.castSucc a), by simp [FlagG.fvec]⟩

theorem hT_eq_zero_of_mem_Hp {T T' : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    {x y : S.V} (hx : x ∈ Hp Λ F F') (hy : y ∈ UUE Λ F F') : S.hT y x = 0 := by
  have hx' : x ∈ orth S (UUE Λ F F') := hx
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx'
  exact hx' y hy

theorem Xsp_Hp_eq_zero {T T' : E} (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') (hG : Gval F F' ≠ 0)
    {x : S.V} (hx : x ∈ Xsp F) (hH : x ∈ Hp Λ F F') : x = 0 := by
  refine span_pair_orth_eq_zero F.fl F'.fl hG x (Xsp_le_span F.fl F'.fl hx) fun i => ?_
  exact hT_eq_zero_of_mem_Hp Λ F F' hH (PI.PairCorankPos.W.frame_mem_UUE Λ hΛ F F' hL hL' i)

theorem mem_Hp_of_orth {T T' : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    (hL : IsLift Λ F) (hL' : IsLift Λ F') (v : S.V) (hv : ∀ i, S.hT (Sum.elim F.fl.fvec F'.fl.fvec i) v = 0) :
    v ∈ Hp Λ F F' := by
  let K : Submodule E S.V := LinearMap.ker (S.hT.flip v)
  have hK : ∀ y, y ∈ K ↔ S.hT y v = 0 := fun y => by simp [K]
  have hXK : ∀ {T₀ : E} (G : LFlag S r T₀), (∀ a, S.hT (G.fl.e a) v = 0) → Xsp G ≤ K := by
    intro T₀ G hG
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact (hK _).2 (hG a)
  have he : ∀ a, S.hT (F.fl.e a) v = 0 := fun a => by
    have := hv (Sum.inl (Fin.castSucc a)); simpa [FlagG.fvec] using this
  have he' : ∀ a, S.hT (F'.fl.e a) v = 0 := fun a => by
    have := hv (Sum.inr (Fin.castSucc a)); simpa [FlagG.fvec] using this
  have hz : S.hT F.zt v = 0 := by
    have := hv (Sum.inl (Fin.last r)); rw [hL.2]; simpa [FlagG.fvec] using this
  have hz' : S.hT F'.zt v = 0 := by
    have := hv (Sum.inr (Fin.last r)); rw [hL'.2]; simpa [FlagG.fvec] using this
  have hUU : UU Λ F F' ≤ K.restrictScalars (𝓞 E) := by
    unfold UU
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact inf_le_right.trans (Submodule.restrictScalars_mono _ (hXK F he))
    · exact Submodule.span_le.2 (by rintro _ rfl; exact (hK _).2 hz)
    · exact inf_le_right.trans (Submodule.restrictScalars_mono _ (hXK F' he'))
    · exact Submodule.span_le.2 (by rintro _ rfl; exact (hK _).2 hz')
  have hUUE : UUE Λ F F' ≤ K := Submodule.span_le.2 fun y hy => hUU hy
  show v ∈ orth S (UUE Λ F F')
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro y hy
  exact (hK y).1 (hUUE hy)

theorem finrank_Hp {T T' : E} (k : ℕ) (hdim : finrank E S.V = k + 2 * r + 1) (Λ : Submodule (𝓞 E) S.V)
    (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F')
    (hG : Gval F F' ≠ 0) : finrank E (Hp Λ F F') = k - 1 ∧ 1 ≤ k := by
  have hu := PI.PairCorankPos.W.linIndep F.fl F'.fl hG
  have h1 := PI.PairCorankPos.W.finrank_orth_add_le S _ hu (UUE Λ F F')
    (PI.PairCorankPos.W.frame_mem_UUE Λ hΛ F F' hL hL')
  rw [Fintype.card_sum, Fintype.card_fin] at h1
  have h3 : finrank E (Hp Λ F F') = finrank E (orth S (UUE Λ F F')) := rfl
  let Φ : S.V →ₗ[E] (Fin (r + 1) ⊕ Fin (r + 1) → E) :=
    LinearMap.pi (fun i => S.hT (Sum.elim F.fl.fvec F'.fl.fvec i))
  have hker : LinearMap.ker Φ ≤ Hp Λ F F' := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    exact mem_Hp_of_orth Λ F F' hL hL' v fun i => congrFun hv i
  have h4 := LinearMap.finrank_range_add_finrank_ker Φ
  have h5 : finrank E (LinearMap.range Φ) ≤ 2 * r + 2 := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at this
    omega
  have h6 := Submodule.finrank_mono hker
  omega

theorem s0_eq_one_iff_Th_eq_Hp {T T' : E} (k : ℕ) (hdim : finrank E S.V = k + 2 * r + 1) (Λ : Submodule (𝓞 E) S.V)
    (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hL : IsLift Λ F) (hL' : IsLift Λ F') (hG : Gval F F' ≠ 0) :
    s0 Λ F F' F'' β k = 1 ↔ Th Λ F F' F'' β = Hp Λ F F' := by
  obtain ⟨h1, hk⟩ := finrank_Hp k hdim Λ hΛ F F' hL hL' hG
  have hle := PI.PairCorankPos.W.Th_le_Hp Λ F F' F'' β
  have h2 := Submodule.finrank_mono hle
  unfold s0
  constructor
  · intro h
    exact Submodule.eq_of_le_of_finrank_le hle (by omega)
  · intro h
    rw [h]; omega

theorem mem_ThPairs {T T' : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' F'' : LFlag S r T')
    (β : S.V ≃ₗ[E] S.V) (p : S.V × S.V) :
    p ∈ ThPairs Λ F F' F'' β ↔ p.1 ∈ Hp Λ F F' ∧ p.2 ∈ Hp Λ F F'' ∧ p.1 - p.2 ∈ Xsp F ∧
      β p.1 - p.2 ∈ Xsp F'' := by
  simp only [ThPairs, Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_comap, LinearMap.sub_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  tauto

theorem Th_one {T T' : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Th Λ F F' F' 1 = Hp Λ F F' := by
  refine le_antisymm (PI.PairCorankPos.W.Th_le_Hp Λ F F' F' 1) fun x hx => ?_
  refine Submodule.mem_map.2 ⟨(x, x), (mem_ThPairs Λ F F' F' 1 (x, x)).2 ⟨hx, hx, ?_, ?_⟩, rfl⟩
  · simp
  · show (1 : S.V ≃ₗ[E] S.V) x - x ∈ Xsp F'
    simp

theorem Th_symm {T T' : E} (k : ℕ) (hdim : finrank E S.V = k + 2 * r + 1) (Λ : Submodule (𝓞 E) S.V)
    (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F₁ F₂ : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hL : IsLift Λ F) (hL₁ : IsLift Λ F₁) (hL₂ : IsLift Λ F₂) (hG₁ : Gval F F₁ ≠ 0) (hG₂ : Gval F F₂ ≠ 0)
    (hβ : ∀ x, x ∈ Xsp F₁ ↔ β x ∈ Xsp F₂) (h : Th Λ F F₁ F₂ β = Hp Λ F F₁) :
    Th Λ F F₂ F₁ β⁻¹ = Hp Λ F F₂ := by
  let P := ThPairs Λ F F₁ F₂ β
  have hd₁ := (finrank_Hp k hdim Λ hΛ F F₁ hL hL₁ hG₁).1
  have hd₂ := (finrank_Hp k hdim Λ hΛ F F₂ hL hL₂ hG₂).1

  let f : P →ₗ[E] S.V := (LinearMap.snd E S.V S.V).domRestrict P
  have hf : Function.Injective f := by
    intro a b hab
    have hsub := (mem_ThPairs Λ F F₁ F₂ β ((a : S.V × S.V) - b)).1 (P.sub_mem a.2 b.2)
    have h2 : ((a : S.V × S.V) - b).2 = 0 := by
      have : (a : S.V × S.V).2 = (b : S.V × S.V).2 := hab
      simp [this]
    rw [h2, sub_zero] at hsub
    have h1 := Xsp_Hp_eq_zero Λ hΛ F F₁ hL hL₁ hG₁ hsub.2.2.1 hsub.1
    apply Subtype.ext
    exact Prod.ext (sub_eq_zero.1 (by simpa using h1)) hab
  have hrange : LinearMap.range f = P.map (LinearMap.snd E S.V S.V) := LinearMap.range_domRestrict _ _
  have hTh2 : finrank E P ≤ finrank E (P.map (LinearMap.snd E S.V S.V)) := by
    rw [← hrange, LinearMap.finrank_range_of_inj hf]
  have hTh1 : finrank E (Th Λ F F₁ F₂ β) ≤ finrank E P := Submodule.finrank_map_le _ _
  have hle2 : P.map (LinearMap.snd E S.V S.V) ≤ Hp Λ F F₂ := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hy
    exact ((mem_ThPairs Λ F F₁ F₂ β p).1 hp).2.1
  have hTh' : P.map (LinearMap.snd E S.V S.V) = Hp Λ F F₂ := by
    refine Submodule.eq_of_le_of_finrank_le hle2 ?_
    rw [h] at hTh1
    omega
  refine le_antisymm (PI.PairCorankPos.W.Th_le_Hp Λ F F₂ F₁ β⁻¹) ?_
  rw [← hTh']
  intro y hy
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨hp1, hp2, hp3, hp4⟩ := (mem_ThPairs Λ F F₁ F₂ β p).1 hp
  refine Submodule.mem_map.2 ⟨(p.2, p.1), (mem_ThPairs Λ F F₂ F₁ β⁻¹ _).2 ⟨hp2, hp1, ?_, ?_⟩, rfl⟩
  · have := (Xsp F).neg_mem hp3
    simpa using this
  · show β.symm p.2 - p.1 ∈ Xsp F₁
    rw [hβ]
    have : β (β.symm p.2 - p.1) = -(β p.1 - p.2) := by
      rw [map_sub, LinearEquiv.apply_symm_apply]; abel
    rw [this]
    exact (Xsp F₂).neg_mem hp4

theorem Th_trans {T T' : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F₁ F₂ F₃ : LFlag S r T')
    (β β' : S.V ≃ₗ[E] S.V) (hβ' : ∀ x, x ∈ Xsp F₂ → β' x ∈ Xsp F₃)
    (h : Th Λ F F₁ F₂ β = Hp Λ F F₁) (h' : Th Λ F F₂ F₃ β' = Hp Λ F F₂) :
    Th Λ F F₁ F₃ (β' * β) = Hp Λ F F₁ := by
  refine le_antisymm (PI.PairCorankPos.W.Th_le_Hp Λ F F₁ F₃ (β' * β)) fun x hx => ?_
  rw [← h] at hx
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hx
  obtain ⟨hp1, hp2, hp3, hp4⟩ := (mem_ThPairs Λ F F₁ F₂ β p).1 hp
  have hy : p.2 ∈ Th Λ F F₂ F₃ β' := by rw [h']; exact hp2
  obtain ⟨q, hq, hq1⟩ := Submodule.mem_map.1 hy
  obtain ⟨hq1', hq2, hq3, hq4⟩ := (mem_ThPairs Λ F F₂ F₃ β' q).1 hq
  have hq1e : q.1 = p.2 := hq1
  rw [hq1e] at hq3 hq4
  refine Submodule.mem_map.2 ⟨(p.1, q.2), (mem_ThPairs Λ F F₁ F₃ (β' * β) _).2 ⟨hp1, hq2, ?_, ?_⟩, rfl⟩
  · have := (Xsp F).add_mem hp3 hq3
    simpa using this
  · show β' (β p.1) - q.2 ∈ Xsp F₃
    have := (Xsp F₃).add_mem (hβ' _ hp4) hq4
    simpa [map_sub] using this

theorem mem_Xsp_mapLF {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (x : S.V) :
    x ∈ Xsp (Formalism.L2.SG.TermOp.mapLF γ F) ↔ γ.symm x ∈ Xsp F := by
  have h1 : Xsp (Formalism.L2.SG.TermOp.mapLF γ F) = (Xsp F).map (γ : S.V →ₗ[E] S.V) := by
    unfold Formalism.L2.SG.TermOp.mapLF
    rw [dif_pos hγ]
    show Submodule.span E (Set.range fun a => γ (F.fl.e a)) =
      (Submodule.span E (Set.range F.fl.e)).map (γ : S.V →ₗ[E] S.V)
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [h1]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨γ.symm x, h, by simp⟩

end Gen

section Terms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem frame_mem_iff (t t' : GTerm X u u' F0 F0' what₂ rows') (x : (VS D).V) :
    x ∈ Xsp t.frame ↔ (t'.lin * t.lin⁻¹) x ∈ Xsp t'.frame := by
  unfold GTerm.frame
  rw [mem_Xsp_mapLF (γ := t.lin) t.rep.2.2.1, mem_Xsp_mapLF (γ := t'.lin) t'.rep.2.2.1]
  have h : t'.lin.symm ((t'.lin * t.lin⁻¹) x) = t.lin.symm x := by
    show t'.lin.symm (t'.lin (t.lin.symm x)) = t.lin.symm x
    simp
  rw [h]

end Terms

theorem corankOne_equivalence_holds : CorankOneEquivalence := by
  intro D X Y u u' _hT
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ t ∈ (Y.tO u u').ngSet, Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    intro t ht h
    apply ht.1
    show Formalism.L2.SG.TermOp.Gt t = 0
    unfold Formalism.L2.SG.TermOp.Gt
    rw [if_pos ((Formalism.L2.SG.Pf.SatGram.gterm_G Y t).trans h)]
  have hlat : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
      Submodule.IsLattice D.host.E t.lam := fun t => ((Y.rowsOK u).1 t.lam t.mem).2.1.1
  have hLF : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
      IsLift t.lam (lf D (X.Fu u)) := fun t => ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), IsLift t.lam t.frame :=
    fun t => t.rep.2.2.2.2.1
  refine ⟨fun t ht => ?_, fun t ht t' ht' hr h1 => ?_, fun t ht t' ht' t'' ht'' hr1 hr2 h1 h2 => ?_⟩
  · show Formalism.L2.SG.TermOp.s0T t t = 1
    unfold Formalism.L2.SG.TermOp.s0T
    rw [if_pos ⟨rfl, rfl⟩, mul_inv_cancel]
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t.frame 1 (hLF t) (hLt t) (hGv t ht)).2
      (Th_one _ _ _)
  · have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
    have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
    have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := h1
    show Formalism.L2.SG.TermOp.s0T t' t = 1
    unfold Formalism.L2.SG.TermOp.s0T at h1' ⊢
    rw [if_pos ⟨hlam, hlam'⟩] at h1'
    rw [if_pos ⟨hlam.symm, hlam'.symm⟩, ← hlam]
    have hth := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
      (hGv t ht)).1 h1'
    have hL' : IsLift t.lam t'.frame := by rw [hlam]; exact hLt t'
    have hsym := Th_symm D.R.k hdim t.lam (hlat t) _ t.frame t'.frame (t'.lin * t.lin⁻¹) (hLF t) (hLt t) hL'
      (hGv t ht) (hGv t' ht') (frame_mem_iff t t') hth
    have hinv : (t'.lin * t.lin⁻¹)⁻¹ = t.lin * t'.lin⁻¹ := by group
    rw [hinv] at hsym
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t.frame _ (hLF t) hL' (hGv t' ht')).2 hsym
  · have hl1 : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1
    have hl1' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1
    have hl2 : t'.lam = t''.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2
    have hl2' : t'.lam' = t''.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2
    have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := h1
    have h2' : Formalism.L2.SG.TermOp.s0T t' t'' = 1 := h2
    show Formalism.L2.SG.TermOp.s0T t t'' = 1
    unfold Formalism.L2.SG.TermOp.s0T at h1' h2' ⊢
    rw [if_pos ⟨hl1, hl1'⟩] at h1'
    rw [if_pos ⟨hl2, hl2'⟩, ← hl1] at h2'
    rw [if_pos ⟨hl1.trans hl2, hl1'.trans hl2'⟩]
    have hL' : IsLift t.lam t'.frame := by rw [hl1]; exact hLt t'
    have hth1 := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
      (hGv t ht)).1 h1'
    have hth2 := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t''.frame _ (hLF t) hL'
      (hGv t' ht')).1 h2'
    have htr := Th_trans t.lam _ t.frame t'.frame t''.frame (t'.lin * t.lin⁻¹) (t''.lin * t'.lin⁻¹)
      (fun x hx => (frame_mem_iff t' t'' x).1 hx) hth1 hth2
    have hmul : (t''.lin * t'.lin⁻¹) * (t'.lin * t.lin⁻¹) = t''.lin * t.lin⁻¹ := by group
    rw [hmul] at htr
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t''.frame _ (hLF t) (hLt t) (hGv t ht)).2 htr

end Formalism.L2.SG.NGCut.CorankRelation
