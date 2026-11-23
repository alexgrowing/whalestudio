import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.TransgressionA

namespace ReciprocityTheory.Coh.InflationTransgression

open ReciprocityTheory.Gal ReciprocityTheory.Coh Cx Function InflationRestrictionInvariants

universe u

noncomputable section

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def ev1 (M : TRep R G) (N : Subgroup G) (f0 : (M.resSub N).coch.X 1) (n : N) : M.V := f0.1 (e1 n)

def conjN (M : TRep R G) (N : Subgroup G) [N.Normal] (s : G) : Pair (M.resSub N) (M.resSub N) where
  φ := { toFun := cj N s
         map_one' := Subtype.ext (by simp)
         map_mul' := fun a b => Subtype.ext (by simp only [cj_coe, Subgroup.coe_mul]; group) }
  u := M.rho s
  φ_cont := Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  u_cont := by
    have h := M.cont.comp (Continuous.prodMk (continuous_const (y := s)) (continuous_id (X := M.V)))
    exact h
  equiv g m := by
    have key : ∀ (g : G) (m : M.V), M.rho s (M.rho (s⁻¹ * g * s) m) = M.rho g (M.rho s m) := by
      intro g m
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2; group
    exact key g m

theorem conj_fix_iff (M : TRep R G) (N : Subgroup G) [N.Normal] (s : G) (f0 : (M.resSub N).coch.X 1)
    (hf : (M.resSub N).coch.d 1 f0 = 0) :
    (conjN M N s).hom.H 1 ((M.resSub N).coch.cls 1 f0 hf) = (M.resSub N).coch.cls 1 f0 hf ↔
      ∃ m : M.V, ∀ n : N, M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m := by
  rw [Cx.Hom.H_cls, Cx.cls_eq_iff, mem_oneCoboundaries_iff]
  rfl

theorem pair_fix (M : TRep R G) (N : Subgroup G) [N.Normal] (s : G) (c : Pair (M.resSub N) (M.resSub N))
    (hφ : ∀ g, (c.φ g : G) = s⁻¹ * g * s) (hu : ∀ m, c.u m = M.rho s m) (f0 : (M.resSub N).coch.X 1)
    (hf : (M.resSub N).coch.d 1 f0 = 0) (m : M.V)
    (hm : ∀ n : N, M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m) :
    c.hom.H 1 ((M.resSub N).coch.cls 1 f0 hf) = (M.resSub N).coch.cls 1 f0 hf := by
  rw [Cx.Hom.H_cls, Cx.cls_eq_iff, mem_oneCoboundaries_iff]
  refine ⟨m, fun n => ?_⟩
  have he : (fun i => c.φ (e1 n i)) = e1 (cj N s n) := by
    funext i
    exact Subtype.ext (hφ _)
  show c.u (f0.1 fun i => c.φ (e1 n i)) - f0.1 (e1 n) = _
  rw [he, hu]
  exact hm n

section
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
  (hP : IsInvRep M N Q P)
include hP

theorem phi_apply (a : G) : P.φ a = (a : G ⧸ N) := by
  rw [hP.1]
  rfl

theorem hom_f_injective (n : ℕ) : Injective (P.hom.f n) := by
  intro f f' h
  apply Subtype.ext
  funext x
  obtain ⟨g, rfl⟩ : ∃ g : Fin n → G, (fun i => (g i : G ⧸ N)) = x :=
    ⟨fun i => (x i).out, funext fun i => QuotientGroup.out_eq' (x i)⟩
  have h1 : P.u (f.1 fun i => P.φ (g i)) = P.u (f'.1 fun i => P.φ (g i)) := congrArg (fun F => F.1 g) h
  have h2 := hP.2.1.injective h1
  simpa [phi_apply M N Q P hP] using h2

theorem inflation_hom_degree_two_apply (z : Q.coch.X 2) (a b : G) :
    (P.hom.f 2 z).1 ![a, b] = P.u (z.1 ![(a : G ⧸ N), b]) := by
  show P.u (z.1 fun i => P.φ (![a, b] i)) = _
  have e : (fun i => P.φ (![a, b] i)) = ![(a : G ⧸ N), (b : G ⧸ N)] := by
    funext i
    fin_cases i <;> simp [phi_apply M N Q P hP]
  rw [e]

theorem inflation_hom_degree_one_apply (v : Q.coch.X 1) (a : G) :
    (P.hom.f 1 v).1 (e1 a) = P.u (v.1 (e1 (a : G ⧸ N))) := by
  show P.u (v.1 fun i => P.φ (e1 a i)) = _
  have e : (fun i => P.φ (e1 a i)) = e1 (a : G ⧸ N) := by
    funext i
    simp [e1, phi_apply M N Q P hP]
  rw [e]

theorem inflD_of_d (y : M.coch.X 1) (z : Q.coch.X 2) (h : M.coch.d 1 y = P.hom.f 2 z) :
    InflD M N (D1 M fun g => y.1 (e1 g)) := by
  have key : ∀ a b, D1 M (fun g => y.1 (e1 g)) a b = P.u (z.1 ![(a : G ⧸ N), b]) := by
    intro a b
    show M.rho a (y.1 (e1 b)) - y.1 (e1 (a * b)) + y.1 (e1 a) = _
    rw [← oneDifferential_val, h, inflation_hom_degree_two_apply M N Q P hP z a b]
  refine ⟨fun a b n => ?_, fun a b n => ?_, fun a b n => ?_⟩
  · rw [key, key, QuotientGroup.mk_mul_of_mem b n.2]
  · rw [key, key, QuotientGroup.mk_mul_of_mem a n.2]
  · rw [key]
    exact (hP.2.2 _).1 ⟨_, rfl⟩ n n.2

theorem descend1 (w : G → M.V) (hw : Continuous w) (hr : ∀ a (n : N), w (a * n) = w a)
    (hi : ∀ a (n : N), M.rho n (w a) = w a) :
    ∃ v : Q.coch.X 1, ∀ a : G, P.u (v.1 (e1 (a : G ⧸ N))) = w a := by
  letI : Setoid G := QuotientGroup.leftRel N
  have hw' : ∀ a b : G, a ≈ b → w a = w b := by
    intro a b hab
    have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.mp hab
    have e := hr a ⟨a⁻¹ * b, hab'⟩
    simp only [mul_inv_cancel_left] at e
    exact e.symm
  let wq : G ⧸ N → M.V := Quotient.lift w hw'
  have hwq : Continuous wq := hw.quotient_lift hw'
  have hmem : ∀ x : G ⧸ N, wq x ∈ LinearMap.range P.u := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a => exact (hP.2.2 (w a)).2 fun g hg => hi a ⟨g, hg⟩
  let v0 : G ⧸ N → Q.V := fun x => (LinearEquiv.ofInjective P.u hP.2.1.injective).symm ⟨wq x, hmem x⟩
  have hv0u : ∀ x, P.u (v0 x) = wq x := by
    intro x
    have := (LinearEquiv.ofInjective P.u hP.2.1.injective).apply_symm_apply ⟨wq x, hmem x⟩
    exact congrArg Subtype.val this
  have hv0 : Continuous v0 := by
    rw [hP.2.1.continuous_iff]
    have e : (P.u ∘ v0) = wq := funext hv0u
    rw [e]
    exact hwq
  refine ⟨⟨fun g => v0 (g 0), hv0.comp (continuous_apply 0)⟩, fun a => ?_⟩
  exact hv0u _

theorem descend2 (D : G → G → M.V) (hD : Continuous fun p : G × G => D p.1 p.2) (hI : InflD M N D) :
    ∃ z : Q.coch.X 2, ∀ a b : G, P.u (z.1 ![(a : G ⧸ N), b]) = D a b := by
  have hout : ∀ a b : G, D (Quotient.out (a : G ⧸ N)) (Quotient.out (b : G ⧸ N)) = D a b := by
    intro a b
    obtain ⟨h1, e1'⟩ := QuotientGroup.mk_out_eq_mul N a
    obtain ⟨h2, e2'⟩ := QuotientGroup.mk_out_eq_mul N b
    rw [e1', e2', hI.left, hI.right]
  let Dq : (G ⧸ N) × (G ⧸ N) → M.V := fun x => D x.1.out x.2.out
  have hq : Topology.IsQuotientMap (Prod.map (QuotientGroup.mk : G → G ⧸ N) (QuotientGroup.mk : G → G ⧸ N)) :=
    (QuotientGroup.isOpenMap_coe.prodMap QuotientGroup.isOpenMap_coe).isQuotientMap
      (continuous_quot_mk.prodMap continuous_quot_mk)
      (QuotientGroup.mk_surjective.prodMap QuotientGroup.mk_surjective)
  have hDq : Continuous Dq := by
    rw [hq.continuous_iff]
    have e : Dq ∘ Prod.map (QuotientGroup.mk : G → G ⧸ N) (QuotientGroup.mk : G → G ⧸ N) =
        fun p : G × G => D p.1 p.2 := funext fun p => hout p.1 p.2
    rw [e]
    exact hD
  have hmem : ∀ x, Dq x ∈ LinearMap.range P.u := fun x =>
    (hP.2.2 (Dq x)).2 fun g hg => hI.inv _ _ ⟨g, hg⟩
  let z0 : (G ⧸ N) × (G ⧸ N) → Q.V := fun x =>
    (LinearEquiv.ofInjective P.u hP.2.1.injective).symm ⟨Dq x, hmem x⟩
  have hz0u : ∀ x, P.u (z0 x) = Dq x := by
    intro x
    have := (LinearEquiv.ofInjective P.u hP.2.1.injective).apply_symm_apply ⟨Dq x, hmem x⟩
    exact congrArg Subtype.val this
  have hz0 : Continuous z0 := by
    rw [hP.2.1.continuous_iff]
    have e : (P.u ∘ z0) = Dq := funext hz0u
    rw [e]
    exact hDq
  refine ⟨⟨fun g => z0 (g 0, g 1), hz0.comp ((continuous_apply 0).prodMk (continuous_apply 1))⟩, fun a b => ?_⟩
  show P.u (z0 ((a : G ⧸ N), (b : G ⧸ N))) = D a b
  rw [hz0u]
  exact hout a b

theorem exists_lift [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [DiscreteTopology M.V]
    (hNc : IsClosed (N : Set G)) (f0 : (M.resSub N).coch.X 1) (hf : (M.resSub N).coch.d 1 f0 = 0)
    (hinv : ∀ s : G, ∃ m : M.V, ∀ n : N, M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m) :
    ∃ (y : M.coch.X 1) (z : Q.coch.X 2) (_ : Q.coch.d 2 z = 0), M.coch.d 1 y = P.hom.f 2 z ∧
      (Pair.res M N.subtype continuous_subtype_val).hom.f 1 y = f0 := by
  have hfc := (wach_d1_eq_zero_iff (M.resSub N) f0).1 hf
  obtain ⟨y0, hy0c, hy0N, h2, h3⟩ := exists_ext_cochain M N hNc (ev1 M N f0)
    ((show Continuous f0.1 from f0.2).comp (continuous_pi fun _ => continuous_id)) (fun a b => hfc a b) hinv
  have hDc : Continuous fun p : G × G => D1 M y0 p.1 p.2 :=
    ((M.cont.comp (continuous_fst.prodMk (hy0c.comp continuous_snd))).sub
      (hy0c.comp (continuous_fst.mul continuous_snd))).add (hy0c.comp continuous_fst)
  obtain ⟨z, hz⟩ := descend2 M N Q P hP (D1 M y0) hDc (inflD_of_ext M N _ y0 h2 h3)
  let y : M.coch.X 1 := ⟨fun g => y0 (g 0), hy0c.comp (continuous_apply 0)⟩
  have hd : M.coch.d 1 y = P.hom.f 2 z := Subtype.ext (funext fun g => by
    have hg : g = ![g 0, g 1] := by funext i; fin_cases i <;> rfl
    rw [hg, oneDifferential_val, inflation_hom_degree_two_apply M N Q P hP, hz]; rfl)
  have hzc : Q.coch.d 2 z = 0 := hom_f_injective M N Q P hP 3 (by
    rw [map_zero, P.hom.comm, ← hd]; exact M.coch.dd 1 y)
  refine ⟨y, z, hzc, hd, Subtype.ext (funext fun g => ?_)⟩
  show y0 (g 0 : G) = f0.1 g
  rw [hy0N]
  exact (oneCochain_apply_fin_one _ f0 g).symm

theorem cls_unique (y y' : M.coch.X 1) (z z' : Q.coch.X 2) (hz : Q.coch.d 2 z = 0)
    (hz' : Q.coch.d 2 z' = 0) (hd : M.coch.d 1 y = P.hom.f 2 z) (hd' : M.coch.d 1 y' = P.hom.f 2 z')
    (hr : (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (y - y') ∈ (M.resSub N).coch.B 1) :
    Q.coch.cls 2 z hz = Q.coch.cls 2 z' hz' := by
  obtain ⟨m, hm⟩ : ∃ m : M.V, ∀ n : N, y.1 (e1 (n : G)) - y'.1 (e1 (n : G)) = M.rho n m - m :=
    (mem_oneCoboundaries_iff _ _).1 hr
  obtain ⟨w, hw⟩ : ∃ w : M.coch.X 1, w = y - y' - M.coch.d 0 (const0 M m) := ⟨_, rfl⟩
  have hwv : ∀ a, w.1 (e1 a) = y.1 (e1 a) - y'.1 (e1 a) - (M.rho a m - m) := fun a => by
    rw [hw]
    show y.1 (e1 a) - y'.1 (e1 a) - (M.coch.d 0 (const0 M m)).1 (e1 a) = _
    rw [zeroDifferential_val]; rfl
  have hwN : ∀ n : N, w.1 (e1 n) = 0 := fun n => by
    rw [hwv, hm n, sub_self]
  have hdw : M.coch.d 1 w = P.hom.f 2 (z - z') := by
    rw [hw, map_sub, map_sub, M.coch.dd, sub_zero, hd, hd', map_sub]
  have hI := inflD_of_d M N Q P hP w (z - z') hdw
  have h1 : (fun g => w.1 (e1 g)) 1 = 0 := by
    have e := hwN 1
    rwa [OneMemClass.coe_one] at e
  obtain ⟨hr1, hr2⟩ := inflD_of_zero M N (fun g => w.1 (e1 g)) h1 hI hwN
  obtain ⟨v, hv⟩ := descend1 M N Q P hP (fun g => w.1 (e1 g))
    ((show Continuous w.1 from w.2).comp (continuous_pi fun _ => continuous_id)) hr1 hr2
  have hvw : P.hom.f 1 v = w := Subtype.ext (funext fun g => by
    rw [oneCochain_apply_fin_one M _ g, oneCochain_apply_fin_one M w g, inflation_hom_degree_one_apply M N Q P hP, hv])
  have hdv : Q.coch.d 1 v = z - z' := hom_f_injective M N Q P hP 2 (by rw [P.hom.comm, hvw, hdw])
  rw [cls_eq_iff]
  exact ⟨v, hdv⟩

end

end

end ReciprocityTheory.Coh.InflationTransgression
