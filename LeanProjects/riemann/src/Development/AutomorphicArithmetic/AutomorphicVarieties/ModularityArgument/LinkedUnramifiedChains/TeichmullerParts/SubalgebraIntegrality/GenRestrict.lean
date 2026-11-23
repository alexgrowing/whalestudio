import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.MemOrdC
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge

open UpperTheory.V.Z.J.D UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.SmGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D

section Abs

variable {M : Type} [AddCommGroup M] [Module ℂ M]

private theorem gen_mul {A B : Module.End ℂ M} (h : Commute A B) {a b : ℂ} {x : M}
    (ha : x ∈ A.maxGenEigenspace a) (hb : x ∈ B.maxGenEigenspace b) : x ∈ (A * B).maxGenEigenspace (a * b) := by
  rw [Module.End.mem_maxGenEigenspace] at ha hb ⊢
  obtain ⟨k1, hk1⟩ := ha
  obtain ⟨k2, hk2⟩ := hb
  have hA : Commute (A - a • 1) B := h.sub_left ((Commute.one_left B).smul_left a)
  have hB : Commute B (B - b • 1) := (Commute.refl B).sub_right ((Commute.one_right B).smul_right b)
  have hAB : Commute (A - a • 1) (B - b • 1) := hA.sub_right ((Commute.one_right _).smul_right b)
  have hXY : Commute ((A - a • 1) * B) (a • (B - b • 1)) := (hAB.mul_left hB).smul_right a
  have hsum : A * B - (a * b) • (1 : Module.End ℂ M) = (A - a • 1) * B + a • (B - b • 1) := by
    rw [sub_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul]
    abel
  have hX : ∀ m, ((A - a • 1) * B) ^ m = B ^ m * (A - a • 1) ^ m := fun m => by
    rw [hA.eq, hA.symm.mul_pow]
  refine ⟨k1 + k2, ?_⟩
  rw [hsum, hXY.add_pow, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul]
  suffices hz : ((((A - a • 1) * B) ^ m) * (a • (B - b • 1)) ^ (k1 + k2 - m)) x = 0 by
    rw [hz, smul_zero]
  rcases le_or_gt k1 m with h1 | h1
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' h1
    rw [(hXY.pow_pow _ _).eq, hX, pow_add (A - a • 1)]
    simp only [Module.End.mul_apply, hk1, map_zero]
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' (show k2 ≤ k1 + k2 - m by omega)
    rw [hd, smul_pow, pow_add (B - b • 1)]
    simp only [Module.End.mul_apply, LinearMap.smul_apply, hk2, map_zero, smul_zero]

private theorem gen_restrict (p : Submodule ℂ M) (U : Module.End ℂ M) (hU : ∀ y ∈ p, U y ∈ p) (c : ℂ) (y : p) :
    y ∈ Module.End.maxGenEigenspace (U.restrict hU) c ↔ (y : M) ∈ U.maxGenEigenspace c := by
  show y ∈ Module.End.genEigenspace (U.restrict hU) c ⊤ ↔ (y : M) ∈ U.genEigenspace c ⊤
  rw [Module.End.genEigenspace_restrict]
  exact Iff.rfl

private theorem gen_smul (T : Module.End ℂ M) {c : ℂ} (hc : c ≠ 0) (e : ℂ) (y : M) :
    y ∈ (c⁻¹ • T).maxGenEigenspace e ↔ y ∈ T.maxGenEigenspace (c * e) := by
  have hrw : c⁻¹ • T - e • (1 : Module.End ℂ M) = c⁻¹ • (T - (c * e) • 1) := by
    rw [smul_sub, smul_smul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  simp only [Module.End.mem_maxGenEigenspace, hrw, smul_pow, LinearMap.smul_apply, smul_eq_zero,
    pow_eq_zero_iff', inv_eq_zero, hc, false_and, false_or]

variable {G : Type} [Group G] (I : Iwa G) (π : Representation ℂ G M)

private theorem gen_two {a b : G} (ha : a ∈ I.P) (hb : b ∈ I.P) {F : M} (hF : F ∈ fixd π I.N) {s t : ℂ}
    (h1 : F ∈ (I.uOp π a).maxGenEigenspace s) (h2 : F ∈ (I.uOp π b).maxGenEigenspace t) :
    F ∈ (I.uOp π (a * b)).maxGenEigenspace (s * t) := by
  have hmap : ∀ g ∈ I.P, ∀ y ∈ fixd π I.N, I.uOp π g y ∈ fixd π I.N := fun g hg y hy =>
    (uOpMul G I ℂ M π g 1 hg (one_mem _) y hy).1
  let A' := (I.uOp π a).restrict (hmap a ha)
  let B' := (I.uOp π b).restrict (hmap b hb)
  let C' := (I.uOp π (a * b)).restrict (hmap (a * b) (mul_mem ha hb))
  have hAB : A' * B' = C' := LinearMap.ext fun y => Subtype.ext (by
    simp only [A', B', C', Module.End.mul_apply, LinearMap.restrict_coe_apply]
    exact (uOpMul G I ℂ M π a b ha hb y y.2).2.1)
  have hba : b * a = a * b := I.comm b (I.P_le b hb) a (I.P_le a ha)
  have hBA : B' * A' = C' := LinearMap.ext fun y => Subtype.ext (by
    simp only [A', B', C', Module.End.mul_apply, LinearMap.restrict_coe_apply]
    rw [← hba]
    exact (uOpMul G I ℂ M π b a hb ha y y.2).2.1)
  have hcomm : Commute A' B' := hAB.trans hBA.symm
  have key := gen_mul hcomm ((gen_restrict _ _ (hmap a ha) s ⟨F, hF⟩).2 h1)
    ((gen_restrict _ _ (hmap b hb) t ⟨F, hF⟩).2 h2)
  rw [hAB] at key
  exact (gen_restrict _ _ (hmap (a * b) (mul_mem ha hb)) _ ⟨F, hF⟩).1 key

private theorem gen_list {F : M} (hF : F ∈ fixd π I.N) {κ : Type} (a : κ → G) (μ : κ → ℂ) (s : List κ)
    (h : ∀ k ∈ s, a k ∈ I.P ∧ F ∈ (I.uOp π (a k)).maxGenEigenspace (μ k)) :
    (s.map a).prod ∈ I.P ∧ F ∈ (I.uOp π (s.map a).prod).maxGenEigenspace (s.map μ).prod := by
  induction s with
  | nil =>
    refine ⟨one_mem _, ?_⟩
    rw [List.map_nil, List.map_nil, List.prod_nil, List.prod_nil, Module.End.mem_maxGenEigenspace]
    refine ⟨1, ?_⟩
    rw [pow_one, LinearMap.sub_apply, one_smul, Module.End.one_apply,
      (uOpMul G I ℂ M π 1 1 (one_mem _) (one_mem _) F hF).2.2.1, sub_self]
  | cons k t ih =>
    have hk := h k List.mem_cons_self
    have ht := ih fun k' hk' => h k' (List.mem_cons_of_mem _ hk')
    simp only [List.map_cons, List.prod_cons]
    exact ⟨mul_mem hk.1 ht.1, gen_two I π hk.1 ht.1 hF hk.2 ht.2⟩

end Abs

private theorem prod_single {σ : Type} [DecidableEq σ] {G : σ → Type} [∀ v, Group (G v)] (g : ∀ v, G v) (w : σ) (s : List σ)
    (hs : s.Nodup) (hw : w ∈ s) : (s.map fun v => (Pi.mulSingle v (g v) : ∀ v, G v)).prod w = g w := by
  rw [Pi.list_prod_apply, List.map_map]
  induction s with
  | nil => simp at hw
  | cons v t ih =>
    rw [List.nodup_cons] at hs
    simp only [List.map_cons, List.prod_cons, Function.comp_apply]
    by_cases hvw : v = w
    · subst hvw
      rw [Pi.mulSingle_eq_same, List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
      exact Pi.mulSingle_eq_of_ne (fun h => hs.1 (by rw [h]; exact hu)) _
    · rw [Pi.mulSingle_eq_of_ne (Ne.symm hvw), one_mul]
      exact ih hs.2 ((List.mem_cons.1 hw).resolve_left (Ne.symm hvw))

private theorem al_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    al k n 0 = 1 := by
  simp only [al, upow, Nat.not_lt_zero, ite_false, zpow_zero]
  exact map_one _

section Set

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ)

private theorem lowVal_ne (lam : Wt L l n) (v : H.V) (j : ℕ) : H.lowVal ι lam v j ≠ 0 := by
  refine (map_ne_zero ι).2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
  refine finprod_induction (p := fun y : Qbar l => y ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun e => ?_
  exact zpow_ne_zero _ ((map_ne_zero e.1).2 (Units.ne_zero _))

end Set

end UpperTheory.V.Z.J.D

private theorem list_range_map_prod_eq_finset_prod (n : ℕ) (f : ℕ → ℂ) : ((List.range n).map f).prod = ∏ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]
    simp

theorem UpperTheory.V.Z.J.D.zEq :
    ZEq := by
  intro L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ hθ ι x lam d ξ c0 sp hsp K ev hev
  classical
  have hinr : ∀ (F : Fin H.m → H.X.Fn ℂ d) (v : H.V) (j : Fin n),
      F ∈ (H.opC ι lam d (Sum.inr (v, j))).maxGenEigenspace (ev (Sum.inr (v, j))) ↔
      F ∈ (H.X.I.uOp (H.X.rpF ℂ d H.m) (alV n H.Sl v (↑j + 1))).maxGenEigenspace
        (H.lowVal ι lam v (↑j + 1) * ev (Sum.inr (v, j))) := fun F v j =>
    gen_smul _ (lowVal_ne H ι lam v _) _ F
  let e : H.V → ℕ → ℂ := fun v j =>
    if h : 0 < j ∧ j ≤ n then ev (Sum.inr (v, ⟨j - 1, by omega⟩)) else 1
  have hnorm : ‖ι.symm (∏ v, ∏ j ∈ Finset.range n, e v j)‖ = 1 := by
    simp only [map_prod, norm_prod]
    refine Finset.prod_eq_one fun v _ => Finset.prod_eq_one fun j _ => ?_
    simp only [e]
    split_ifs with h
    · exact hev _ _
    · simp
  have hz : H.X.I.z = (Finset.univ.toList.map fun v => ((List.range n).map (alV n H.Sl v)).prod).prod := by
    funext w
    have h1 : ∀ v, ((List.range n).map (alV n H.Sl v)).prod =
        Pi.mulSingle v ((List.range n).map
          (al (IsDedekindDomain.HeightOneSpectrum.adicCompletion L (H.Sl v)) n)).prod := by
      intro v
      rw [← MonoidHom.mulSingle_apply, map_list_prod, List.map_map]
      rfl
    simp only [h1]
    rw [prod_single _ w _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ w))]
    exact (glBridge _ n ℂ 1).2.2.2.2.2.2.2.2.1
  have hlev : ∀ F ∈ fixd (H.X.rpF ℂ d H.m) H.X.I.N,
      (∀ (v : H.V) (j : Fin n), F ∈ (H.X.I.uOp (H.X.rpF ℂ d H.m) (alV n H.Sl v (↑j + 1))).maxGenEigenspace
        (H.lowVal ι lam v (↑j + 1) * ev (Sum.inr (v, j)))) →
      F ∈ (H.uzC ι lam d).maxGenEigenspace (∏ v, ∏ j ∈ Finset.range n, e v j) := by
    intro F hF hU
    have h1 : ∀ v, ∀ j ∈ List.range n, alV n H.Sl v j ∈ H.X.I.P ∧
        F ∈ (H.X.I.uOp (H.X.rpF ℂ d H.m) (alV n H.Sl v j)).maxGenEigenspace
          (H.lowVal ι lam v j * e v j) := by
      intro v j hj
      rw [List.mem_range] at hj
      refine ⟨Up.singleP (fun v => glIwa (IsDedekindDomain.HeightOneSpectrum.adicCompletion L (H.Sl v)) n)
        v _ (al_mem _ n j), ?_⟩
      rcases j with _ | j
      · have h0 : alV n H.Sl v 0 = 1 := by
          rw [alV, al_zero]
          exact Pi.mulSingle_one v
        have hl : H.lowVal ι lam v 0 = 1 := by simp [HSet.lowVal]
        have he : e v 0 = 1 := dif_neg (by omega)
        rw [h0, hl, he, one_mul, Module.End.mem_maxGenEigenspace]
        refine ⟨1, ?_⟩
        rw [pow_one, LinearMap.sub_apply, one_smul, Module.End.one_apply,
          (uOpMul _ H.X.I ℂ _ (H.X.rpF ℂ d H.m) 1 1 (one_mem _) (one_mem _) F hF).2.2.1, sub_self]
      · have hj' : j < n := by omega
        have he : e v (j + 1) = ev (Sum.inr (v, ⟨j, hj'⟩)) := dif_pos ⟨Nat.succ_pos j, by omega⟩
        rw [he]
        exact hU v ⟨j, hj'⟩
    have h2 : ∀ v ∈ Finset.univ.toList, ((List.range n).map (alV n H.Sl v)).prod ∈ H.X.I.P ∧
        F ∈ (H.X.I.uOp (H.X.rpF ℂ d H.m) ((List.range n).map (alV n H.Sl v)).prod).maxGenEigenspace
          ((List.range n).map fun j => H.lowVal ι lam v j * e v j).prod := fun v _ =>
      gen_list H.X.I (H.X.rpF ℂ d H.m) hF (alV n H.Sl v) (fun j => H.lowVal ι lam v j * e v j)
        (List.range n) (h1 v)
    have h3 := (gen_list H.X.I (H.X.rpF ℂ d H.m) hF
      (fun v => ((List.range n).map (alV n H.Sl v)).prod)
      (fun v => ((List.range n).map fun j => H.lowVal ι lam v j * e v j).prod)
      Finset.univ.toList h2).2
    rw [← hz] at h3
    have hc : (∏ v, ∏ j ∈ Finset.range n, H.lowVal ι lam v j) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun v _ => Finset.prod_ne_zero_iff.2 fun j _ => lowVal_ne H ι lam v j
    refine (gen_smul (H.X.I.uOp (H.X.rpF ℂ d H.m) H.X.I.z) hc _ F).2 ?_
    have hμ : (∏ v, ∏ j ∈ Finset.range n, H.lowVal ι lam v j) * (∏ v, ∏ j ∈ Finset.range n, e v j) =
        (Finset.univ.toList.map fun v => ((List.range n).map fun j => H.lowVal ι lam v j * e v j).prod).prod := by
      rw [Finset.prod_map_toList, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [list_range_map_prod_eq_finset_prod, ← Finset.prod_mul_distrib]
    rw [hμ]
    exact h3
  apply le_antisymm
  · intro F hF
    rw [zPart, Submodule.mem_inf, Submodule.mem_iInf] at hF
    obtain ⟨hO, hE⟩ := hF
    have hle : H.OrdAt θ ι x.toRingHom lam ξ K c0 ≤ H.ClAt θ ι x.toRingHom lam ξ K c0 := by
      unfold HSet.OrdAt
      exact iSup_le fun μ => inf_le_left
    have hC := hle hO
    simp only [HSet.ClAt, Submodule.mem_inf, Submodule.mem_iInf] at hC
    obtain ⟨⟨⟨⟨hB, hK⟩, hN⟩, hNm⟩, hEig⟩ := hC
    simp only [zL, eigL, Submodule.mem_inf, Submodule.mem_iInf]
    exact ⟨⟨⟨hB, hK⟩, ⟨⟨hN, hNm⟩, hEig⟩, fun v j => (hinr F v j).1 (hE _)⟩, fun p => hE _⟩
  · intro F hF
    simp only [zL, eigL, Submodule.mem_inf, Submodule.mem_iInf] at hF
    obtain ⟨⟨⟨hB, hK⟩, ⟨⟨hN, hNm⟩, hEig⟩, hU⟩, hP⟩ := hF
    have hC : F ∈ H.ClAt θ ι x.toRingHom lam ξ K c0 := by
      simp only [HSet.ClAt, Submodule.mem_inf, Submodule.mem_iInf]
      exact ⟨⟨⟨⟨hB, hK⟩, hN⟩, hNm⟩, hEig⟩
    have hE : ∀ i, F ∈ (H.opC ι lam d i).maxGenEigenspace (ev i) := by
      rintro (p | ⟨v, j⟩)
      · exact hP p
      · exact (hinr F v j).2 (hU v j)
    rw [zPart, Submodule.mem_inf, Submodule.mem_iInf]
    refine ⟨?_, hE⟩
    unfold HSet.OrdAt
    exact Submodule.mem_iSup_of_mem (⟨_, hnorm⟩ : { μ : ℂ // ‖ι.symm μ‖ = 1 })
      (Submodule.mem_inf.2 ⟨hC, hlev F hN hU⟩)
